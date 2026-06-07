//! The characteristic-0 Clifford classifier — the symmetry-completing companion
//! to [`char2`](crate::forms::char2). Where the Arf invariant returns the
//! isomorphism class of a char-2 (nimber) Clifford algebra, this returns the
//! isomorphism class of a char-0 one as a concrete matrix algebra over ℝ, ℂ, or ℍ.
//!
//! ## The two tables
//!
//! Over a **real-closed** field every nonzero square can be rescaled to ±1
//! (positive elements have square roots). The crate's `Surreal` backend is only
//! a finite-support Hahn/CNF model with rational coefficients, so the real table
//! is returned only when the actual represented coefficients can be rescaled by
//! exact square roots in this implementation. For example `ω` is accepted
//! (`√ω = ω^{1/2}` is represented), while the rational coefficient `2` is not.
//! On that checked subdomain, a metric is classified by its signature
//! `(p, q, r)` = (#positive, #negative, #null) squares, and the nondegenerate
//! `Cl(p,q)` follows the 8-fold Bott table indexed by `s = (q − p) mod 8`
//! (with `n = p+q`):
//!
//! | s | algebra            |   | s | algebra            |
//! |---|--------------------|---|---|--------------------|
//! | 0 | ℝ(2^{n/2})         |   | 4 | ℍ(2^{(n−2)/2})     |
//! | 1 | ℂ(2^{(n−1)/2})     |   | 5 | ℂ(2^{(n−1)/2})     |
//! | 2 | ℍ(2^{(n−2)/2})     |   | 6 | ℝ(2^{n/2})         |
//! | 3 | ℍ(2^{(n−3)/2})²    |   | 7 | ℝ(2^{(n−1)/2})²    |
//!
//! Over an **algebraically closed** field all nonzero squares are equivalent, so
//! only `(n, r)` matter and the classification is 2-fold:
//! `Cl(n,ℂ) ≅ ℂ(2^{n/2})` for n even, `ℂ(2^{(n−1)/2})²` for n odd. As above,
//! `Surcomplex<Surreal>` exposes that table only for diagonal entries whose
//! square roots are actually represented by the finite-support backend.
//!
//! The null directions (radical of dim `r`) contribute an exterior factor:
//! `Cl(p,q,r) ≅ Cl(p,q) ⊗ Λ(F^r)` over the ground field `F ∈ {ℝ, ℂ}`.
//!
//! The rational backend is **not** treated as real-closed. `classify_rational`
//! reports the genuine Hasse--Minkowski invariant package: dimension, radical,
//! discriminant square-class, real signature, and the local Hasse invariants at
//! the real place and the finitely many relevant `Q_p` places.

use crate::clifford::Metric;
use crate::forms::{disc_class, hasse_at_place, relevant_primes, square_free, Place};
use crate::scalar::Surcomplex;
use crate::scalar::Surreal;
use crate::scalar::{Rational, Scalar};
use std::cmp::Ordering;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BaseField {
    R,
    C,
    H,
}

impl BaseField {
    fn symbol(self) -> &'static str {
        match self {
            BaseField::R => "R",
            BaseField::C => "C",
            BaseField::H => "H",
        }
    }
}

/// The isomorphism class of a char-0 Clifford algebra: a matrix algebra (or a
/// direct sum of two of them) over ℝ/ℂ/ℍ, optionally tensored with the exterior
/// algebra of the metric's radical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CliffordType {
    /// The division ring underlying the matrix algebra.
    pub base: BaseField,
    /// `m` such that the (semisimple) core is `M_m(base)` (or two copies of it).
    pub matrix_dim: usize,
    /// Whether the core is a direct sum of two equal matrix algebras (`⊕`).
    pub doubled: bool,
    /// Dimension of the metric radical (null directions): an `Λ(ground^r)` factor.
    pub radical_dim: usize,
    /// The ground field of the classification (ℝ for real, ℂ for surcomplex);
    /// the field over which the radical's exterior factor is taken.
    pub ground: BaseField,
    /// The nondegenerate signature `(p, q)` (positive, negative squares). For the
    /// complex case `q` is 0 and `p` is the nondegenerate dimension.
    pub signature: (usize, usize),
}

impl CliffordType {
    /// Human-readable name, e.g. `M_2(H)`, `M_4(R) ⊕ M_4(R)`, `C ⊗ Λ(R^1)`.
    pub fn display(&self) -> String {
        let unit = if self.matrix_dim == 1 {
            self.base.symbol().to_string()
        } else {
            format!("M_{}({})", self.matrix_dim, self.base.symbol())
        };
        let core = if self.doubled {
            format!("{unit} ⊕ {unit}")
        } else {
            unit
        };
        if self.radical_dim > 0 {
            format!("{core} ⊗ Λ({}^{})", self.ground.symbol(), self.radical_dim)
        } else {
            core
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalPlaceInvariant {
    pub place: Place,
    /// Hasse invariant at this place: `+1` or `-1`.
    pub hasse: i8,
}

/// Complete rational quadratic-form invariants for the metric underlying a
/// rational Clifford algebra.
///
/// The nondegenerate part is classified over `Q` by `(dim, discriminant,
/// Hasse_v for all places v)`; only the real place and primes dividing
/// `2·disc` can be nontrivial, so the finite list here is complete. The
/// `real_closure` field records what the algebra becomes after scalar extension
/// to `R`, but it is not used as a substitute for the rational invariant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalCliffordType {
    pub dim: usize,
    pub radical_dim: usize,
    /// Canonical representative of the discriminant in `Q*/Q*²`.
    pub discriminant: i128,
    pub signature: (usize, usize),
    pub local_hasse: Vec<RationalPlaceInvariant>,
    pub real_closure: CliffordType,
}

impl RationalCliffordType {
    pub fn display(&self) -> String {
        let locals = self
            .local_hasse
            .iter()
            .map(|h| match h.place {
                Place::Real => format!("R:{:+}", h.hasse),
                Place::Prime(p) => format!("Q_{}:{:+}", p, h.hasse),
            })
            .collect::<Vec<_>>()
            .join(", ");
        let rad = if self.radical_dim > 0 {
            format!(" radical {}", self.radical_dim)
        } else {
            String::new()
        };
        format!(
            "Q: dim {} disc {} sig ({},{}) hasse [{}]{}; over R: {}",
            self.dim,
            self.discriminant,
            self.signature.0,
            self.signature.1,
            locals,
            rad,
            self.real_closure.display()
        )
    }
}

/// `2^k`.
fn p2(k: usize) -> usize {
    1usize << k
}

/// Classify the nondegenerate real Clifford algebra `Cl(p,q)` (no radical) by
/// the 8-fold Bott table. `radical_dim`/`ground` are filled in by the callers.
fn real_core(p: usize, q: usize) -> (BaseField, usize, bool) {
    let n = p + q;
    let s = (q as isize - p as isize).rem_euclid(8) as usize;
    match s {
        0 | 6 => (BaseField::R, p2(n / 2), false),
        1 | 5 => (BaseField::C, p2((n - 1) / 2), false),
        2 | 4 => (BaseField::H, p2((n - 2) / 2), false),
        3 => (BaseField::H, p2((n - 3) / 2), true),
        7 => (BaseField::R, p2((n - 1) / 2), true),
        _ => unreachable!(),
    }
}

/// Classify a real Clifford algebra from its signature `(p, q, r)`.
pub fn classify_real(p: usize, q: usize, r: usize) -> CliffordType {
    let (base, matrix_dim, doubled) = real_core(p, q);
    CliffordType {
        base,
        matrix_dim,
        doubled,
        radical_dim: r,
        ground: BaseField::R,
        signature: (p, q),
    }
}

/// Classify a complex Clifford algebra from `(n, r)` (nondegenerate dim, radical).
pub fn classify_complex(n: usize, r: usize) -> CliffordType {
    let (matrix_dim, doubled) = if n % 2 == 0 {
        (p2(n / 2), false)
    } else {
        (p2((n - 1) / 2), true)
    };
    CliffordType {
        base: BaseField::C,
        matrix_dim,
        doubled,
        radical_dim: r,
        ground: BaseField::C,
        signature: (n, 0),
    }
}

fn exact_surreal_sqrt_nonnegative(x: &Surreal) -> Option<Surreal> {
    if x.is_zero() {
        return Some(Surreal::zero());
    }
    if x.sign() != Ordering::Greater {
        return None;
    }
    let base = x.terms().len().max(1);
    for n in 1..=(8 * base + 32) {
        let root = x.sqrt(n)?;
        if root.mul(&root) == *x {
            return Some(root);
        }
    }
    None
}

fn exact_surcomplex_sqrt(z: &Surcomplex<Surreal>) -> Option<Surcomplex<Surreal>> {
    if z.is_zero() {
        return Some(Surcomplex::zero());
    }
    let root = if z.im.is_zero() {
        match z.re.sign() {
            Ordering::Greater => {
                let root = exact_surreal_sqrt_nonnegative(&z.re)?;
                Surcomplex::new(root, Surreal::zero())
            }
            Ordering::Less => {
                let root = exact_surreal_sqrt_nonnegative(&z.re.neg())?;
                Surcomplex::new(Surreal::zero(), root)
            }
            Ordering::Equal => Surcomplex::zero(),
        }
    } else {
        let norm_sq = z.re.mul(&z.re).add(&z.im.mul(&z.im));
        let norm = exact_surreal_sqrt_nonnegative(&norm_sq)?;
        let half = Surreal::from_rational(Rational::new(1, 2));
        let a2 = norm.add(&z.re).mul(&half);
        let b2 = norm.sub(&z.re).mul(&half);
        let a = exact_surreal_sqrt_nonnegative(&a2)?;
        let mut b = exact_surreal_sqrt_nonnegative(&b2)?;
        if z.im.sign() == Ordering::Less {
            b = b.neg();
        }
        Surcomplex::new(a, b)
    };
    if root.mul(&root) == *z {
        Some(root)
    } else {
        None
    }
}

/// Signature over the implemented `Surreal` subdomain where every nonzero
/// diagonal entry is exactly square-equivalent to ±1.
pub(crate) fn surreal_signature(metric: &Metric<Surreal>) -> Option<(usize, usize, usize)> {
    let diag = crate::forms::as_diagonal(metric)?;
    let (mut p, mut q, mut r) = (0, 0, 0);
    for x in &diag.q {
        match x.sign() {
            Ordering::Greater => {
                exact_surreal_sqrt_nonnegative(x)?;
                p += 1;
            }
            Ordering::Less => {
                exact_surreal_sqrt_nonnegative(&x.neg())?;
                q += 1;
            }
            Ordering::Equal => r += 1,
        }
    }
    Some((p, q, r))
}

/// Rank/radical over the implemented `Surcomplex<Surreal>` subdomain where each
/// nonzero diagonal entry has an exact represented square root.
pub(crate) fn surcomplex_rank(metric: &Metric<Surcomplex<Surreal>>) -> Option<(usize, usize)> {
    let diag = crate::forms::as_diagonal(metric)?;
    let mut nonzero = 0usize;
    let mut radical = 0usize;
    for z in &diag.q {
        if z.is_zero() {
            radical += 1;
        } else {
            exact_surcomplex_sqrt(z)?;
            nonzero += 1;
        }
    }
    Some((nonzero, radical))
}

fn rational_square_class(x: &Rational) -> i128 {
    square_free(x.numer() * x.denom())
}

/// Classify a rational-scalar quadratic form by the genuine rational invariants:
/// nondegenerate dimension, radical, discriminant square-class, real signature,
/// and the Hasse invariant at every relevant place.
pub fn classify_rational(metric: &Metric<Rational>) -> Option<RationalCliffordType> {
    let diag = crate::forms::as_diagonal(metric)?;
    let mut entries = Vec::new();
    let mut radical_dim = 0usize;
    let mut signature = (0usize, 0usize);
    for x in &diag.q {
        if x.is_zero() {
            radical_dim += 1;
            continue;
        }
        match x.sign() {
            Ordering::Greater => signature.0 += 1,
            Ordering::Less => signature.1 += 1,
            Ordering::Equal => unreachable!("zero handled above"),
        }
        entries.push(rational_square_class(x));
    }
    let discriminant = if entries.is_empty() {
        1
    } else {
        disc_class(&entries)
    };
    let mut local_hasse = vec![RationalPlaceInvariant {
        place: Place::Real,
        hasse: hasse_at_place(&entries, Place::Real),
    }];
    for p in relevant_primes(&entries) {
        local_hasse.push(RationalPlaceInvariant {
            place: Place::Prime(p),
            hasse: hasse_at_place(&entries, Place::Prime(p)),
        });
    }
    Some(RationalCliffordType {
        dim: entries.len(),
        radical_dim,
        discriminant,
        signature,
        local_hasse,
        real_closure: classify_real(signature.0, signature.1, radical_dim),
    })
}

/// Classify a surreal-scalar Clifford algebra when the represented coefficients
/// can be exactly rescaled to ±1. Returns `None` for forms such as `⟨2⟩`, which
/// would need `√2` outside the finite-support rational-coefficient backend.
pub fn classify_surreal(metric: &Metric<Surreal>) -> Option<CliffordType> {
    let (p, q, r) = surreal_signature(metric)?;
    Some(classify_real(p, q, r))
}

/// Classify a surcomplex-scalar Clifford algebra on the exact-square subdomain.
/// Returns `None` when a diagonal entry has no represented square root.
pub fn classify_surcomplex(metric: &Metric<Surcomplex<Surreal>>) -> Option<CliffordType> {
    let (nonzero, r) = surcomplex_rank(metric)?;
    Some(classify_complex(nonzero, r))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::{CliffordAlgebra, Metric};
    use crate::scalar::Scalar;

    fn rat(n: i128) -> Rational {
        Rational::int(n)
    }
    fn surreal_diag(qs: &[i128]) -> Metric<Surreal> {
        Metric::diagonal(qs.iter().map(|&x| Surreal::from_int(x)).collect())
    }
    fn cl_real(qs: &[i128]) -> Option<CliffordType> {
        classify_surreal(&surreal_diag(qs))
    }
    fn name(qs: &[i128]) -> String {
        cl_real(qs).unwrap().display()
    }

    #[test]
    fn low_dimensional_real_clifford_table() {
        assert_eq!(name(&[]), "R"); // Cl(0,0) = ℝ
        assert_eq!(name(&[1]), "R ⊕ R"); // Cl(1,0) = ℝ⊕ℝ
        assert_eq!(name(&[-1]), "C"); // Cl(0,1) = ℂ
        assert_eq!(name(&[1, 1]), "M_2(R)"); // Cl(2,0) = M₂(ℝ)
        assert_eq!(name(&[1, -1]), "M_2(R)"); // Cl(1,1) = M₂(ℝ)
        assert_eq!(name(&[-1, -1]), "H"); // Cl(0,2) = ℍ
        assert_eq!(name(&[1, 1, 1]), "M_2(C)"); // Cl(3,0) = M₂(ℂ)
        assert_eq!(name(&[-1, -1, -1]), "H ⊕ H"); // Cl(0,3) = ℍ⊕ℍ
        assert_eq!(name(&[-1, -1, -1, -1]), "M_2(H)"); // Cl(0,4) = M₂(ℍ)
    }

    #[test]
    fn physics_signatures() {
        // Spacetime algebra Cl(1,3) ≅ M₂(ℍ); Cl(3,1) ≅ M₄(ℝ) (the two conventions
        // are genuinely different algebras — a classic subtlety the table shows).
        assert_eq!(name(&[1, -1, -1, -1]), "M_2(H)"); // Cl(1,3)
        assert_eq!(name(&[1, 1, 1, -1]), "M_4(R)"); // Cl(3,1)
                                                    // Conformal geometric algebra Cl(4,1) ≅ M₄(ℂ).
        assert_eq!(name(&[1, 1, 1, 1, -1]), "M_4(C)"); // Cl(4,1)
    }

    #[test]
    fn dimension_is_consistent() {
        // real-dim of the algebra must equal 2^n for every nondegenerate signature.
        for p in 0..=5usize {
            for q in 0..=5usize {
                let t = classify_real(p, q, 0);
                let unit = match t.base {
                    BaseField::R => 1,
                    BaseField::C => 2,
                    BaseField::H => 4,
                };
                let copies = if t.doubled { 2 } else { 1 };
                let real_dim = copies * unit * t.matrix_dim * t.matrix_dim;
                assert_eq!(real_dim, 1usize << (p + q), "Cl({p},{q})");
            }
        }
    }

    #[test]
    fn radical_gives_exterior_factor() {
        // Cl(0,1,2): ℂ tensor an exterior algebra on the 2 null directions.
        assert_eq!(name(&[-1, 0, 0]), "C ⊗ Λ(R^2)");
        // pure Grassmann Λ(R^3) = Cl(0,0,3): trivial core ⊗ Λ.
        assert_eq!(name(&[0, 0, 0]), "R ⊗ Λ(R^3)");
    }

    #[test]
    fn rational_classification_keeps_square_classes_and_local_hasse_data() {
        let one = classify_rational(&Metric::diagonal(vec![rat(1)])).unwrap();
        let two = classify_rational(&Metric::diagonal(vec![rat(2)])).unwrap();
        assert_eq!(one.signature, two.signature);
        assert_ne!(one.discriminant, two.discriminant);

        let h = classify_rational(&Metric::diagonal(vec![rat(-1), rat(-1)])).unwrap();
        assert_eq!(h.discriminant, 1);
        assert_eq!(h.signature, (0, 2));
        assert!(h
            .local_hasse
            .iter()
            .any(|x| x.place == Place::Real && x.hasse == -1));
        assert!(h
            .local_hasse
            .iter()
            .any(|x| x.place == Place::Prime(2) && x.hasse == -1));
    }

    #[test]
    fn surreal_accepts_represented_exact_square_classes() {
        // Infinite/infinitesimal square classes are represented exactly here:
        // sqrt(ω)=ω^(1/2), sqrt(ε)=ω^(-1/2), so the signature is (1,1).
        let m = Metric::diagonal(vec![Surreal::omega(), Surreal::epsilon().neg()]);
        assert_eq!(classify_surreal(&m).unwrap().display(), "M_2(R)");
        assert_eq!(
            classify_surreal(&surreal_diag(&[4])).unwrap().display(),
            "R ⊕ R"
        );
    }

    #[test]
    fn surreal_declines_unrepresented_square_classes() {
        // The implemented Surreal model has rational coefficients, not all real
        // coefficients, so sqrt(2) is absent and ⟨2⟩ must not be collapsed to ⟨1⟩.
        assert_eq!(classify_surreal(&surreal_diag(&[2])), None);
    }

    #[test]
    fn surcomplex_is_two_fold_on_exact_square_subdomain() {
        let even =
            Metric::<Surcomplex<Surreal>>::diagonal(vec![Surcomplex::one(), Surcomplex::one()]);
        assert_eq!(classify_surcomplex(&even).unwrap().display(), "M_2(C)"); // n=2
        let odd = Metric::<Surcomplex<Surreal>>::diagonal(vec![Surcomplex::one()]);
        assert_eq!(classify_surcomplex(&odd).unwrap().display(), "C ⊕ C"); // n=1
        let minus_one = Metric::<Surcomplex<Surreal>>::diagonal(vec![Surcomplex::new(
            Surreal::from_int(-1),
            Surreal::zero(),
        )]);
        assert_eq!(classify_surcomplex(&minus_one).unwrap().display(), "C ⊕ C");
        let square_of_two_plus_i = Metric::<Surcomplex<Surreal>>::diagonal(vec![Surcomplex::new(
            Surreal::from_int(3),
            Surreal::from_int(4),
        )]);
        assert_eq!(
            classify_surcomplex(&square_of_two_plus_i)
                .unwrap()
                .display(),
            "C ⊕ C"
        );
    }

    #[test]
    fn surcomplex_declines_unrepresented_square_classes() {
        let two = Metric::<Surcomplex<Surreal>>::diagonal(vec![Surcomplex::new(
            Surreal::from_int(2),
            Surreal::zero(),
        )]);
        assert_eq!(classify_surcomplex(&two), None);
    }

    #[test]
    fn even_subalgebra_classification_drops_one_dimension() {
        // Cl(3,0)⁰ ≅ Cl(0,2) = ℍ — ties the classifier to even_subalgebra.
        let alg = CliffordAlgebra::new(3, Metric::diagonal(vec![rat(1), rat(1), rat(1)]));
        let even = alg.even_subalgebra().unwrap();
        assert_eq!(
            classify_rational(&even.metric)
                .unwrap()
                .real_closure
                .display(),
            "H"
        );
        // Cl(1,3)⁰ ≅ Cl(1,2) ... check it matches a direct signature classification.
        let st = CliffordAlgebra::new(4, Metric::diagonal(vec![rat(1), rat(-1), rat(-1), rat(-1)]));
        let st_even = st.even_subalgebra().unwrap();
        // pivot is the last non-null (a −1 direction): f_i² = −q_i·(−1) = q_i.
        // signature of the even part here is (1,2) ⇒ same class as Cl(1,2).
        assert_eq!(
            classify_rational(&st_even.metric)
                .unwrap()
                .real_closure
                .display(),
            classify_real(1, 2, 0).display()
        );
    }
}
