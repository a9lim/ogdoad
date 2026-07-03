//! Kneser `p`-neighbors for explicit integral lattices.
//!
//! For a lattice `L` and a prime `p ∤ det(L)`, an isotropic line
//! `ell = <v> <= L/pL` gives the neighbor
//!
//! ```text
//! M   = { x in L : <x,v> = 0 mod p }
//! L'  = M + Z*(v/p).
//! ```
//!
//! The implementation keeps the denominator visible: it builds the integer row
//! lattice `pM + Zv`, Hermite-reduces it, and divides the resulting Gram matrix
//! by `p^2`. If the line is not isotropic, the lift cannot be made integral, or
//! any checked arithmetic boundary fails, the constructor returns `None`.
//!
//! The mass reports here are deliberately bounded. Rank 8 and rank 16 have
//! explicit representatives in this crate (`E8`, `E8+E8`, `D16+`), so the
//! neighbor surface can be paired with the already-shipped mass formula. Rank 24
//! still routes through the Niemeier catalogue rather than generated glued Gram
//! representatives; see [`super::niemeier`].

use super::{
    are_in_same_genus, e_8, is_root_lattice, mass_even_unimodular,
    root_lattices::E8_WEYL_GROUP_ORDER, IntegralForm, D16_PLUS_AUT_ORDER,
};
use crate::linalg::integer::normalize_relation_rows;
use crate::scalar::{is_prime_u128, Rational};
use std::collections::BTreeSet;
use std::fmt;

/// One explicit Kneser neighbor, recording the projective line that generated it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KneserNeighbor {
    pub prime: u128,
    pub line: Vec<u128>,
    pub lattice: IntegralForm,
}

/// One class used in a bounded mass-closure report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KneserMassRecord {
    pub label: &'static str,
    pub automorphism_group_order: u128,
}

impl KneserMassRecord {
    /// `display()` alias kept for Python callers.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for KneserMassRecord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "KneserMassRecord(label={:?}, automorphism_group_order={})",
            self.label, self.automorphism_group_order
        )
    }
}

/// A bounded Kneser/mass certificate for an explicit even-unimodular genus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KneserMassInvariants {
    pub rank: usize,
    pub prime: u128,
    pub seed_label: &'static str,
    pub generated_neighbor_count: usize,
    /// The sorted, de-duplicated set of class labels the Kneser neighbor search
    /// actually classified (via `generated_rank_labels`), independent of
    /// [`classes`](Self::classes) (the static catalogue). If neighbor generation
    /// ever stopped finding one of the classes, this set would shrink even
    /// though `classes` would not — that asymmetry is the point: it is what lets
    /// a test cross-check "generation actually found it" against "the catalogue
    /// says it exists" instead of comparing the catalogue to itself.
    pub generated_labels: Vec<&'static str>,
    pub classes: Vec<KneserMassRecord>,
    pub mass: (i128, i128),
    pub mass_sum: (i128, i128),
    pub mass_closed: bool,
}

impl KneserMassInvariants {
    /// The class labels the neighbor search actually generated. Equal to
    /// [`generated_labels`](Self::generated_labels); kept as a method for
    /// backward-compatible call sites (incl. the Python binding).
    pub fn generated_class_labels(&self) -> Vec<&'static str> {
        self.generated_labels.clone()
    }

    /// `display()` alias kept for Python callers.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for KneserMassInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "KneserMassInvariants(rank={}, prime={}, seed={:?}, mass={}/{}, mass_closed={}, classes={:?})",
            self.rank,
            self.prime,
            self.seed_label,
            self.mass.0,
            self.mass.1,
            self.mass_closed,
            self.generated_class_labels(),
        )
    }
}

fn mod_i128(x: i128, p: i128) -> i128 {
    x.rem_euclid(p)
}

fn inv_mod(a: i128, p: i128) -> Option<i128> {
    let (mut t, mut new_t) = (0i128, 1i128);
    let (mut r, mut new_r) = (p, mod_i128(a, p));
    while new_r != 0 {
        let q = r / new_r;
        (t, new_t) = (new_t, t - q * new_t);
        (r, new_r) = (new_r, r - q * new_r);
    }
    if r == 1 {
        Some(mod_i128(t, p))
    } else {
        None
    }
}

fn matvec_mod(lattice: &IntegralForm, v: &[i128], p: i128) -> Vec<i128> {
    let n = lattice.dim();
    let mut out = vec![0i128; n];
    for (i, out_i) in out.iter_mut().enumerate() {
        let mut acc = 0i128;
        for (j, &vj) in v.iter().enumerate() {
            acc = mod_i128(acc + mod_i128(lattice.gram()[i][j], p) * mod_i128(vj, p), p);
        }
        *out_i = acc;
    }
    out
}

fn projective_line_is_normalized(v: &[u128], p: u128) -> bool {
    let Some(first) = v.iter().position(|&x| x != 0) else {
        return false;
    };
    v[first] == 1 && v.iter().all(|&x| x < p)
}

fn is_isotropic_line(lattice: &IntegralForm, p: u128, v: &[i128]) -> bool {
    if p == 2 && lattice.is_even() {
        lattice.norm(v).rem_euclid(4) == 0
    } else {
        lattice.norm(v).rem_euclid(p as i128) == 0
    }
}

fn checked_scale_row(row: &[i128], scale: i128) -> Option<Vec<i128>> {
    row.iter().map(|&x| x.checked_mul(scale)).collect()
}

fn m_basis_for_line(lattice: &IntegralForm, p: i128, lift: &[i128]) -> Option<Vec<Vec<i128>>> {
    let n = lattice.dim();
    let h = matvec_mod(lattice, lift, p);
    let pivot = h.iter().position(|&x| x != 0)?;
    let inv = inv_mod(h[pivot], p)?;
    let mut rows = Vec::with_capacity(n);
    for i in 0..n {
        if i == pivot {
            continue;
        }
        let mut row = vec![0i128; n];
        row[i] = 1;
        row[pivot] = mod_i128(-h[i] * inv, p);
        rows.push(row);
    }
    let mut p_row = vec![0i128; n];
    p_row[pivot] = p;
    rows.push(p_row);
    Some(rows)
}

fn odd_prime_lift(lattice: &IntegralForm, p: i128, lift: &mut [i128]) -> Option<()> {
    debug_assert!(p > 2);
    let norm = lattice.norm(lift);
    if norm.rem_euclid(p) != 0 {
        return None;
    }
    if norm.rem_euclid(p * p) == 0 {
        return Some(());
    }
    let h = matvec_mod(lattice, lift, p);
    let pivot = h.iter().position(|&x| x != 0)?;
    let m = (norm / p).rem_euclid(p);
    let denom = mod_i128(2 * h[pivot], p);
    let t = mod_i128(-m * inv_mod(denom, p)?, p);
    lift[pivot] = lift[pivot].checked_add(p.checked_mul(t)?)?;
    if lattice.norm(lift).rem_euclid(p * p) == 0 {
        Some(())
    } else {
        None
    }
}

fn even_two_lift(lattice: &IntegralForm, lift: &mut [i128]) -> Option<()> {
    let norm = lattice.norm(lift);
    if norm.rem_euclid(4) != 0 {
        return None;
    }
    if norm.rem_euclid(8) == 0 {
        return Some(());
    }
    let h = matvec_mod(lattice, lift, 2);
    let pivot = h.iter().position(|&x| x != 0)?;
    lift[pivot] = lift[pivot].checked_add(2)?;
    if lattice.norm(lift).rem_euclid(8) == 0 {
        Some(())
    } else {
        None
    }
}

/// The Kneser `p`-neighbor attached to an isotropic projective line in `L/pL`.
///
/// `line` must be a canonical projective representative: entries in `0..p`, not
/// all zero, with first nonzero entry equal to `1`. For `p=2`, this constructor
/// uses the even-lattice quadratic refinement `Q(x)/2 mod 2`, so it requires an
/// even lattice. For odd `p`, the bilinear isotropy condition is `Q(x)=0 mod p`,
/// and the lift is adjusted so `Q(v)` is divisible by `p^2`.
pub fn kneser_neighbor(lattice: &IntegralForm, p: u128, line: &[u128]) -> Option<IntegralForm> {
    if !is_prime_u128(p) || p > i128::MAX as u128 || line.len() != lattice.dim() {
        return None;
    }
    if p == 2 && !lattice.is_even() {
        return None;
    }
    if lattice.determinant().rem_euclid(p as i128) == 0 {
        return None;
    }
    if !projective_line_is_normalized(line, p) {
        return None;
    }

    let p_i = p as i128;
    let mut lift: Vec<i128> = line
        .iter()
        .map(|&x| i128::try_from(x).ok())
        .collect::<Option<_>>()?;
    if !is_isotropic_line(lattice, p, &lift) {
        return None;
    }
    if p == 2 {
        even_two_lift(lattice, &mut lift)?;
    } else {
        odd_prime_lift(lattice, p_i, &mut lift)?;
    }

    let m_basis = m_basis_for_line(lattice, p_i, &lift)?;
    let mut scaled_rows = Vec::with_capacity(m_basis.len() + 1);
    for row in &m_basis {
        scaled_rows.push(checked_scale_row(row, p_i)?);
    }
    scaled_rows.push(lift);
    let basis = normalize_relation_rows(scaled_rows);
    if basis.len() != lattice.dim() {
        return None;
    }

    let denom = p_i.checked_mul(p_i)?;
    let n = basis.len();
    let mut gram = vec![vec![0i128; n]; n];
    for i in 0..n {
        for j in 0..n {
            let inner = lattice.inner(&basis[i], &basis[j]);
            if inner % denom != 0 {
                return None;
            }
            gram[i][j] = inner / denom;
        }
    }
    IntegralForm::new(gram)
}

fn enumerate_projective_lines_rec(
    lattice: &IntegralForm,
    p: u128,
    first: usize,
    idx: usize,
    max_lines: u128,
    cur: &mut [u128],
    out: &mut Vec<Vec<u128>>,
) {
    if out.len() as u128 >= max_lines {
        return;
    }
    if idx == cur.len() {
        let v: Vec<i128> = cur.iter().map(|&x| x as i128).collect();
        if is_isotropic_line(lattice, p, &v) {
            out.push(cur.to_vec());
        }
        return;
    }
    if idx < first {
        cur[idx] = 0;
        enumerate_projective_lines_rec(lattice, p, first, idx + 1, max_lines, cur, out);
    } else if idx == first {
        cur[idx] = 1;
        enumerate_projective_lines_rec(lattice, p, first, idx + 1, max_lines, cur, out);
    } else {
        for x in 0..p {
            cur[idx] = x;
            enumerate_projective_lines_rec(lattice, p, first, idx + 1, max_lines, cur, out);
            if out.len() as u128 >= max_lines {
                break;
            }
        }
    }
}

/// Isotropic projective lines in `L/pL`, in canonical representatives.
///
/// The enumeration stops after `max_lines` isotropic lines; pass a large bound
/// for small finite searches. Returns `None` when `p` is unsupported, divides the
/// determinant, or `p=2` is requested for an odd lattice.
pub fn isotropic_lines_mod_p(
    lattice: &IntegralForm,
    p: u128,
    max_lines: u128,
) -> Option<Vec<Vec<u128>>> {
    if !is_prime_u128(p)
        || p > i128::MAX as u128
        || lattice.determinant().rem_euclid(p as i128) == 0
    {
        return None;
    }
    if p == 2 && !lattice.is_even() {
        return None;
    }
    if max_lines == 0 {
        return Some(Vec::new());
    }
    let n = lattice.dim();
    let mut cur = vec![0u128; n];
    let mut out = Vec::new();
    for first in 0..n {
        enumerate_projective_lines_rec(lattice, p, first, 0, max_lines, &mut cur, &mut out);
        if out.len() as u128 >= max_lines {
            break;
        }
    }
    Some(out)
}

/// Kneser neighbors from the first `max_lines` isotropic projective lines.
pub fn kneser_neighbors(
    lattice: &IntegralForm,
    p: u128,
    max_lines: u128,
) -> Option<Vec<KneserNeighbor>> {
    let lines = isotropic_lines_mod_p(lattice, p, max_lines)?;
    let mut out = Vec::new();
    for line in lines {
        let neighbor = kneser_neighbor(lattice, p, &line)?;
        out.push(KneserNeighbor {
            prime: p,
            line,
            lattice: neighbor,
        });
    }
    Some(out)
}

fn add_frac((a, b): (i128, i128), (c, d): (i128, i128)) -> Option<(i128, i128)> {
    let r = Rational::try_new(a, b)?.checked_add(&Rational::try_new(c, d)?)?;
    Some((r.numer(), r.denom()))
}

fn reciprocal_u128(x: u128) -> Option<(i128, i128)> {
    Some((1, i128::try_from(x).ok()?))
}

fn mass_sum(classes: &[KneserMassRecord]) -> Option<(i128, i128)> {
    let mut out = (0i128, 1i128);
    for class in classes {
        out = add_frac(out, reciprocal_u128(class.automorphism_group_order)?)?;
    }
    Some(out)
}

fn aut_e8_e8() -> Option<u128> {
    2u128
        .checked_mul(E8_WEYL_GROUP_ORDER)?
        .checked_mul(E8_WEYL_GROUP_ORDER)
}

fn rank16_neighbor_label(neighbor: &IntegralForm, seed: &IntegralForm) -> Option<&'static str> {
    if neighbor.dim() != 16 || !neighbor.is_even() || !neighbor.is_unimodular() {
        return None;
    }
    if !are_in_same_genus(seed, neighbor) {
        return None;
    }
    if is_root_lattice(neighbor) {
        Some("E8+E8")
    } else {
        Some("D16+")
    }
}

fn generated_rank_labels(
    seed: &IntegralForm,
    rank: usize,
    prime: u128,
    max_lines: u128,
) -> Option<(usize, Vec<&'static str>)> {
    let lines = isotropic_lines_mod_p(seed, prime, max_lines)?;
    let mut labels = BTreeSet::new();
    for line in &lines {
        let neighbor = kneser_neighbor(seed, prime, line)?;
        let label = match rank {
            8 => {
                if neighbor.is_even()
                    && neighbor.is_unimodular()
                    && are_in_same_genus(seed, &neighbor)
                {
                    "E8"
                } else {
                    return None;
                }
            }
            16 => rank16_neighbor_label(&neighbor, seed)?,
            _ => return None,
        };
        labels.insert(label);
        if (rank == 8 && labels.len() == 1) || (rank == 16 && labels.len() == 2) {
            break;
        }
    }
    Some((lines.len(), labels.into_iter().collect()))
}

/// Bounded mass-closed Kneser reports for explicit even-unimodular genera.
///
/// Supported ranks:
///
/// * `8`: the unique class `E8`;
/// * `16`: the two explicit classes `E8+E8` and `D16+`.
///
/// Rank 24 is intentionally not included here: the crate carries the Niemeier
/// catalogue and the Leech Gram, not explicit glued Gram representatives for the
/// other 23 classes.
pub fn even_unimodular_kneser_report(rank: usize) -> Option<KneserMassInvariants> {
    let prime = 2;
    let (seed_label, seed, classes) = match rank {
        8 => (
            "E8",
            e_8(),
            vec![KneserMassRecord {
                label: "E8",
                automorphism_group_order: E8_WEYL_GROUP_ORDER,
            }],
        ),
        16 => (
            "E8+E8",
            e_8().direct_sum(&e_8()),
            vec![
                KneserMassRecord {
                    label: "E8+E8",
                    automorphism_group_order: aut_e8_e8()?,
                },
                KneserMassRecord {
                    label: "D16+",
                    automorphism_group_order: D16_PLUS_AUT_ORDER,
                },
            ],
        ),
        _ => return None,
    };
    let max_lines = if rank == 8 { 1_000 } else { 100_000 };
    // The neighbor generation is a load-bearing verification step (it classifies
    // every generated neighbor and bails with `None` if one falls outside the
    // genus); `generated_labels` is the actual set it found, kept distinct from
    // `classes` (the static catalogue) so tests can cross-check one against the
    // other instead of the catalogue against itself.
    let (generated_neighbor_count, generated_labels) =
        generated_rank_labels(&seed, rank, prime, max_lines)?;
    let mass = mass_even_unimodular(rank as u128)?;
    let mass_sum = mass_sum(&classes)?;
    Some(KneserMassInvariants {
        rank,
        prime,
        seed_label,
        generated_neighbor_count,
        generated_labels,
        classes,
        mass,
        mass_sum,
        mass_closed: mass == mass_sum,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forms::{are_in_same_genus, d16_plus};

    #[test]
    fn e8_two_neighbor_stays_in_the_even_unimodular_genus() {
        let e8 = e_8();
        let line = isotropic_lines_mod_p(&e8, 2, 1).unwrap().pop().unwrap();
        let n = kneser_neighbor(&e8, 2, &line).unwrap();
        assert!(n.is_even());
        assert!(n.is_unimodular());
        assert!(are_in_same_genus(&e8, &n));
        assert_eq!(n.dim(), 8);
    }

    #[test]
    fn bad_lines_are_rejected() {
        let e8 = e_8();
        assert!(kneser_neighbor(&e8, 2, &[1, 0, 0, 0, 0, 0, 0, 0]).is_none());
        assert!(kneser_neighbor(&e8, 4, &[0, 1, 1, 0, 0, 0, 0, 0]).is_none());
        assert!(kneser_neighbor(&IntegralForm::diagonal(&[1, 1]), 2, &[1, 1]).is_none());
    }

    /// The static catalogue's label set, independent of anything neighbor
    /// generation found — the thing [`KneserMassInvariants::generated_labels`]
    /// must be cross-checked against so a broken generator (that silently found
    /// nothing, or found the wrong classes) cannot hide behind the catalogue.
    fn static_class_labels(report: &KneserMassInvariants) -> Vec<&'static str> {
        let labels: BTreeSet<&'static str> = report.classes.iter().map(|c| c.label).collect();
        labels.into_iter().collect()
    }

    #[test]
    fn rank16_report_finds_both_neighbor_classes_and_closes_mass() {
        let report = even_unimodular_kneser_report(16).unwrap();
        assert_eq!(report.prime, 2);
        assert!(report.generated_neighbor_count > 0);
        assert_eq!(report.generated_class_labels(), vec!["D16+", "E8+E8"]);
        // Cross-check the *generated* set against the static catalogue, not the
        // catalogue against itself: this is the assertion that would fail if
        // neighbor generation stopped finding D16+ (or E8+E8) even though the
        // hand-entered `classes` list still names it.
        assert_eq!(
            report.generated_class_labels(),
            static_class_labels(&report)
        );
        assert_eq!(report.classes.len(), 2);
        assert_eq!(report.mass, mass_even_unimodular(16).unwrap());
        assert_eq!(report.mass, report.mass_sum);
        assert!(report.mass_closed);
        assert!(are_in_same_genus(&e_8().direct_sum(&e_8()), &d16_plus()));
    }

    #[test]
    fn rank8_report_is_the_unique_mass_class() {
        let report = even_unimodular_kneser_report(8).unwrap();
        assert_eq!(report.generated_class_labels(), vec!["E8"]);
        assert_eq!(
            report.generated_class_labels(),
            static_class_labels(&report)
        );
        assert_eq!(
            report.classes[0].automorphism_group_order,
            E8_WEYL_GROUP_ORDER
        );
        assert_eq!(report.mass, (1, E8_WEYL_GROUP_ORDER as i128));
        assert!(report.mass_closed);
        assert!(even_unimodular_kneser_report(24).is_none());
    }

    #[test]
    fn kneser_mass_record_and_invariants_display_render_the_mass_report() {
        let report = even_unimodular_kneser_report(8).unwrap();
        assert_eq!(
            report.classes[0].to_string(),
            "KneserMassRecord(label=\"E8\", automorphism_group_order=696729600)"
        );
        assert_eq!(report.classes[0].display(), report.classes[0].to_string());
        assert_eq!(
            report.to_string(),
            "KneserMassInvariants(rank=8, prime=2, seed=\"E8\", mass=1/696729600, mass_closed=true, classes=[\"E8\"])"
        );
        assert_eq!(report.display(), report.to_string());
    }
}
