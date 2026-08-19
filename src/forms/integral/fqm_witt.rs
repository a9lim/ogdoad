//! Witt classes of finite quadratic modules.
//!
//! This is the Wall/Nikulin finite-module side of the integral pillar: a
//! nonsingular finite quadratic module is reduced, prime by prime, by quotienting
//! isotropic cyclic subgroups until an anisotropic core remains. The terminal core
//! is canonicalised as a finite table, so the output is a full Witt normal form,
//! not just the Milgram/Brown phase.

use crate::forms::integral::diagonal::{odd_unit_residue, rat_val, rational_mod_int, unit_mod8};
use crate::forms::integral::discriminant::{
    phase_mod8_from_q_values, DiscriminantForm, IsoTables, SquareTable,
};
use crate::forms::integral::is_prime_power;
use crate::forms::try_is_square_qp;
use crate::linalg::integer::prime_factors;
use crate::scalar::{Rational, Scalar};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

const FQM_WITT_GROUP_CAP: usize = 512;
const FQM_WITT_TUPLE_CAP: u128 = 2_000_000;

#[derive(Clone, Debug)]
struct IndexSet {
    present: Vec<bool>,
    len: usize,
}

impl IndexSet {
    fn new(size: usize) -> Self {
        IndexSet {
            present: vec![false; size],
            len: 0,
        }
    }

    fn insert(&mut self, index: usize) -> bool {
        if self.present[index] {
            false
        } else {
            self.present[index] = true;
            self.len += 1;
            true
        }
    }

    fn contains(&self, index: usize) -> bool {
        self.present[index]
    }

    fn len(&self) -> usize {
        self.len
    }

    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.present
            .iter()
            .enumerate()
            .filter_map(|(index, &present)| present.then_some(index))
    }

    fn is_subset(&self, other: &IndexSet) -> bool {
        self.iter().all(|index| other.contains(index))
    }
}

/// A value-count entry in a finite quadratic module normal form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FqmValueCount {
    /// Numerator of the canonical rational representative.
    pub numer: i128,
    /// Denominator of the canonical rational representative.
    pub denom: i128,
    /// Number of elements carrying this value.
    pub count: u128,
}

/// One p-primary summand of the finite-quadratic-module Witt class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FqmPrimaryWittClass {
    /// The prime `p`.
    pub prime: u128,
    /// The order of the original p-primary summand.
    pub order: u128,
    /// The order of the anisotropic Witt core.
    pub core_order: u128,
    /// Invariant factors of the anisotropic core.
    pub core_group: Vec<u128>,
    /// Exponent of the anisotropic core.
    pub core_exponent: u128,
    /// The Milgram/Brown phase of this p-primary Witt class.
    pub phase_mod8: i128,
    /// Value counts on the anisotropic core, useful as readable diagnostics.
    pub q_value_counts: Vec<FqmValueCount>,
    /// Opaque exact normal form of the anisotropic core.
    ///
    /// The label is canonical under finite-module isomorphism; equality of these
    /// labels is the equality test for the p-primary Witt class.
    pub normal_form: Vec<i128>,
}

impl FqmPrimaryWittClass {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for FqmPrimaryWittClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FqmPrimaryWittClass(prime={}, order={}, core_order={}, core_group={:?}, core_exponent={}, phase_mod8={})",
            self.prime, self.order, self.core_order, self.core_group, self.core_exponent, self.phase_mod8,
        )
    }
}

/// The Witt class of a nonsingular finite quadratic module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FqmWittClass {
    /// Order of the original finite module.
    pub order: u128,
    /// Total Milgram/Brown phase, i.e. the sum of the p-primary phases in `Z/8`.
    pub phase_mod8: i128,
    /// Prime-local Witt normal forms.
    pub primary: Vec<FqmPrimaryWittClass>,
}

impl FqmWittClass {
    /// Whether the class is Witt-trivial, i.e. every p-primary anisotropic core is
    /// the zero module.
    pub fn is_trivial(&self) -> bool {
        self.primary.iter().all(|p| p.core_order == 1)
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for FqmWittClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FqmWittClass(order={}, phase_mod8={}, primary=[",
            self.order, self.phase_mod8
        )?;
        for (i, p) in self.primary.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{p}")?;
        }
        write!(f, "])")
    }
}

/// A local condition in Nikulin's even-lattice existence criterion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NikulinPrimaryExistenceInvariants {
    /// The prime `p`.
    pub prime: u128,
    /// The order of the p-primary summand.
    pub order: u128,
    /// The minimal number of generators `l(A_p)`.
    pub length: usize,
    /// Whether the requested rank is exactly `l(A_p)`, so Nikulin's determinant
    /// side condition is active at this prime.
    pub equality_case: bool,
    /// For `p = 2`, whether the 2-primary quadratic form is even in Nikulin's
    /// sense, i.e. it has no order-2 cyclic summand with q-value odd/2.
    pub even_two_primary: bool,
    /// The p-adic determinant square class `discr K(q_p)` represented by an exact
    /// rational. Present only in equality cases where a determinant check is
    /// required.
    pub p_adic_discriminant: Option<Rational>,
    /// Result of the equality-case determinant check, when one is required.
    pub determinant_condition_holds: Option<bool>,
}

impl NikulinPrimaryExistenceInvariants {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for NikulinPrimaryExistenceInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let discr = self
            .p_adic_discriminant
            .as_ref()
            .map_or_else(|| "none".to_string(), |r| r.to_string());
        let holds = self
            .determinant_condition_holds
            .map_or_else(|| "none".to_string(), |b| b.to_string());
        write!(
            f,
            "NikulinPrimaryExistenceInvariants(prime={}, order={}, length={}, equality_case={}, even_two_primary={}, p_adic_discriminant={}, determinant_condition_holds={})",
            self.prime, self.order, self.length, self.equality_case, self.even_two_primary, discr, holds,
        )
    }
}

/// The first failed condition in Nikulin's theorem 1.10.1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NikulinExistenceObstruction {
    /// `sign(q) != t_+ - t_- (mod 8)`.
    SignatureCongruence {
        /// Signature required by the requested lattice.
        required_mod8: i128,
        /// Phase of the finite quadratic module.
        module_phase_mod8: i128,
    },
    /// `rank < l(A_p)` at one prime.
    RankTooSmall {
        /// Prime at which the length bound fails.
        prime: u128,
        /// Requested lattice rank.
        rank: usize,
        /// Length of the primary module.
        length: usize,
    },
    /// The odd-prime equality case failed:
    /// `(-1)^{t_-}|A_p| != discr K(q_p)` in `Q_p^*/Q_p^{*2}`.
    OddPrimeDeterminant {
        /// Odd prime at which the determinant condition fails.
        prime: u128,
        /// Signed order entering Nikulin's condition.
        signed_order: i128,
        /// Computed p-adic discriminant.
        p_adic_discriminant: Rational,
    },
    /// The 2-adic even equality case failed:
    /// `|A_2| != +/- discr K(q_2)` in `Q_2^*/Q_2^{*2}`.
    TwoAdicDeterminant {
        /// Order of the two-primary module.
        order: u128,
        /// Computed two-adic discriminant.
        p_adic_discriminant: Rational,
    },
}

impl NikulinExistenceObstruction {
    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for NikulinExistenceObstruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NikulinExistenceObstruction::SignatureCongruence {
                required_mod8,
                module_phase_mod8,
            } => write!(
                f,
                "SignatureCongruence(required_mod8={required_mod8}, module_phase_mod8={module_phase_mod8})"
            ),
            NikulinExistenceObstruction::RankTooSmall {
                prime,
                rank,
                length,
            } => write!(f, "RankTooSmall(prime={prime}, rank={rank}, length={length})"),
            NikulinExistenceObstruction::OddPrimeDeterminant {
                prime,
                signed_order,
                p_adic_discriminant,
            } => write!(
                f,
                "OddPrimeDeterminant(prime={prime}, signed_order={signed_order}, p_adic_discriminant={p_adic_discriminant})"
            ),
            NikulinExistenceObstruction::TwoAdicDeterminant {
                order,
                p_adic_discriminant,
            } => write!(
                f,
                "TwoAdicDeterminant(order={order}, p_adic_discriminant={p_adic_discriminant})"
            ),
        }
    }
}

/// Full bounded report for Nikulin's even-lattice existence criterion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NikulinExistenceInvariants {
    /// Requested signature `(t_+, t_-)`.
    pub signature: (usize, usize),
    /// Requested rank `t_+ + t_-`.
    pub rank: usize,
    /// The finite quadratic module's Gauss/Milgram phase, `sign(q) mod 8`.
    pub module_phase_mod8: i128,
    /// Prime-local rank and determinant checks.
    pub primary: Vec<NikulinPrimaryExistenceInvariants>,
    /// The first failed condition, or `None` when the lattice exists.
    pub obstruction: Option<NikulinExistenceObstruction>,
}

impl NikulinExistenceInvariants {
    /// Whether Nikulin's theorem decides that an even lattice with the requested
    /// signature and discriminant form exists.
    pub fn exists(&self) -> bool {
        self.obstruction.is_none()
    }

    /// Return the canonical display representation.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for NikulinExistenceInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let obstruction = self
            .obstruction
            .as_ref()
            .map_or_else(|| "none".to_string(), |o| o.to_string());
        write!(
            f,
            "NikulinExistenceInvariants(signature={:?}, rank={}, module_phase_mod8={}, exists={}, obstruction={})",
            self.signature, self.rank, self.module_phase_mod8, self.exists(), obstruction,
        )
    }
}

/// A native finite quadratic module in a cyclic product presentation.
///
/// The `q_values_mod2` slice is ordered lexicographically over the cyclic factors:
/// for factors `[d0, d1, ...]`, index `((x0*d1 + x1)*d2 + ...)` stores
/// `q(x0, x1, ...)` as a rational in `Q/2Z`. The constructor validates
/// nonsingularity and the quadratic law up to `FQM_WITT_GROUP_CAP`.
#[derive(Clone, Debug, PartialEq)]
pub struct FiniteQuadraticModule {
    cyclic_factors: Vec<u128>,
    q_values_mod2: Vec<Rational>,
}

impl FiniteQuadraticModule {
    /// Build a nonsingular finite quadratic module from a cyclic presentation and
    /// all of its quadratic values in lexicographic coordinate order.
    pub fn new(cyclic_factors: Vec<u128>, q_values_mod2: Vec<Rational>) -> Option<Self> {
        if cyclic_factors.iter().any(|&d| d <= 1) {
            return None;
        }
        let order = cyclic_factors
            .iter()
            .try_fold(1usize, |acc, &d| acc.checked_mul(usize::try_from(d).ok()?))?;
        if order == 0 || order > FQM_WITT_GROUP_CAP || q_values_mod2.len() != order {
            return None;
        }
        let q_values_mod2 = q_values_mod2
            .into_iter()
            .map(|q| rational_mod_int(q, 2))
            .collect::<Vec<_>>();
        let module = FiniteQuadraticModule {
            cyclic_factors,
            q_values_mod2,
        };
        let table = FqmTable::from_native(&module)?;
        if table.q[table.zero] != Rational::zero()
            || !table.quadratic_values_are_even()
            || !table.bilinear_form_is_biadditive()
            || !table.is_nondegenerate()
        {
            return None;
        }
        Some(module)
    }

    /// The cyclic module generated by `g` with `q(g) = generator_q`.
    pub fn cyclic(order: u128, generator_q: Rational) -> Option<Self> {
        if order <= 1 || usize::try_from(order).ok()? > FQM_WITT_GROUP_CAP {
            return None;
        }
        let qg = rational_mod_int(generator_q, 2);
        let mut q_values = Vec::with_capacity(usize::try_from(order).ok()?);
        for k in 0..order {
            let kk = i128::try_from(k.checked_mul(k)?).ok()?;
            q_values.push(rational_mod_int(Rational::from_int(kk).mul(&qg), 2));
        }
        Self::new(vec![order], q_values)
    }

    /// Orthogonal direct sum.
    pub fn direct_sum(&self, other: &Self) -> Option<Self> {
        let left = FqmTable::from_native(self)?;
        let right = FqmTable::from_native(other)?;
        let mut factors = self.cyclic_factors.clone();
        factors.extend(other.cyclic_factors.iter().copied());
        let mut q_values = Vec::with_capacity(left.q.len().checked_mul(right.q.len())?);
        for ql in &left.q {
            for qr in &right.q {
                q_values.push(rational_mod_int(ql.add(qr), 2));
            }
        }
        Self::new(factors, q_values)
    }

    /// Order of the finite module.
    pub fn order(&self) -> u128 {
        self.q_values_mod2.len() as u128
    }

    /// Cyclic factors of this presentation.
    pub fn cyclic_factors(&self) -> &[u128] {
        &self.cyclic_factors
    }

    /// Quadratic values in lexicographic coordinate order.
    pub fn q_values_mod2(&self) -> &[Rational] {
        &self.q_values_mod2
    }

    /// The Wall/Nikulin Witt normal form.
    pub fn witt_class(&self) -> Option<FqmWittClass> {
        FqmTable::from_native(self)?.witt_class()
    }

    /// Nikulin's even-lattice existence criterion for this finite quadratic
    /// module and the requested signature `(t_+, t_-)`.
    ///
    /// This implements Nikulin, *Integral symmetric bilinear forms and some of
    /// their applications*, Math. USSR Izv. **14** (1980), Theorem 1.10.1, in the
    /// bounded finite-table model used by [`witt_class`](Self::witt_class).
    /// `None` means the table/determinant computation exceeded that bounded exact
    /// surface, not that the theorem failed.
    pub fn nikulin_existence_report(
        &self,
        signature: (usize, usize),
    ) -> Option<NikulinExistenceInvariants> {
        FqmTable::from_native(self)?.nikulin_existence_report(signature)
    }

    /// Boolean convenience wrapper around [`nikulin_existence_report`](Self::nikulin_existence_report).
    pub fn nikulin_even_lattice_exists(&self, signature: (usize, usize)) -> Option<bool> {
        Some(self.nikulin_existence_report(signature)?.exists())
    }
}

impl DiscriminantForm {
    /// The full Wall/Nikulin finite-quadratic-module Witt class of `(A_L, q_L)`.
    ///
    /// This refines [`fqm_gauss_phase`](Self::fqm_gauss_phase): the phase is kept as
    /// a projection, but equality is decided by the p-primary anisotropic normal
    /// forms. The implementation is exact up to the finite enumeration budget; it
    /// returns `None` instead of truncating when `|A_L| > 512`.
    pub fn fqm_witt_class(&self) -> Option<FqmWittClass> {
        FqmTable::from_iso_tables(self.tables_bounded(FQM_WITT_GROUP_CAP)?).witt_class()
    }

    /// Whether two discriminant forms are Witt-equivalent as finite quadratic
    /// modules.
    pub fn is_fqm_witt_equivalent(&self, other: &Self) -> Option<bool> {
        Some(self.fqm_witt_class()? == other.fqm_witt_class()?)
    }

    /// Nikulin's even-lattice existence criterion for this discriminant form and
    /// the requested signature `(t_+, t_-)`.
    ///
    /// This is the existence companion to [`is_isomorphic`](Self::is_isomorphic):
    /// instead of comparing two already-built lattices, it decides whether the
    /// pair `(signature, q)` is realized by some even lattice. The implementation
    /// follows Nikulin theorem 1.10.1 and returns `None` only past the bounded
    /// finite-table surface (`|A| <= 512` here).
    pub fn nikulin_existence_report(
        &self,
        signature: (usize, usize),
    ) -> Option<NikulinExistenceInvariants> {
        FqmTable::from_iso_tables(self.tables_bounded(FQM_WITT_GROUP_CAP)?)
            .nikulin_existence_report(signature)
    }

    /// Boolean convenience wrapper around [`nikulin_existence_report`](Self::nikulin_existence_report).
    pub fn nikulin_even_lattice_exists(&self, signature: (usize, usize)) -> Option<bool> {
        Some(self.nikulin_existence_report(signature)?.exists())
    }
}

#[derive(Clone, Debug)]
struct FqmTable {
    zero: usize,
    q: Vec<Rational>,
    order: Vec<usize>,
    add: SquareTable<usize>,
}

impl FqmTable {
    fn from_iso_tables(t: IsoTables) -> Self {
        FqmTable {
            zero: t.zero,
            q: t.q,
            order: t.order,
            add: t.add,
        }
    }

    fn from_native(module: &FiniteQuadraticModule) -> Option<Self> {
        let n = module.q_values_mod2.len();
        let mut add = SquareTable::filled(n, 0usize);
        let coords = (0..n)
            .map(|index| coords_from_index(index, &module.cyclic_factors))
            .collect::<Option<Vec<_>>>()?;
        for i in 0..n {
            for j in 0..n {
                let mut sum_index = 0usize;
                for ((&a, &b), &d) in coords[i].iter().zip(&coords[j]).zip(&module.cyclic_factors) {
                    let digit = a.checked_add(b)? % d;
                    sum_index = sum_index
                        .checked_mul(usize::try_from(d).ok()?)?
                        .checked_add(usize::try_from(digit).ok()?)?;
                }
                add[i][j] = sum_index;
            }
        }
        let zero = 0;
        let mut out = FqmTable {
            zero,
            q: module.q_values_mod2.clone(),
            order: vec![1; n],
            add,
        };
        out.compute_orders();
        Some(out)
    }

    fn compute_orders(&mut self) {
        let n = self.q.len();
        self.order = vec![1usize; n];
        for i in 0..n {
            let mut cur = i;
            let mut k = 1usize;
            while cur != self.zero {
                cur = self.add[cur][i];
                k += 1;
            }
            self.order[i] = k;
        }
    }

    fn witt_class(&self) -> Option<FqmWittClass> {
        if self.q.len() > FQM_WITT_GROUP_CAP {
            return None;
        }
        let mut primes = BTreeSet::new();
        for &ord in &self.order {
            for p in prime_factors(ord as u128) {
                primes.insert(p);
            }
        }
        let mut primary = Vec::new();
        for p in primes {
            let part = self.primary_subtable(p)?;
            let phase = phase_mod8_from_q_values(part.q.iter(), part.q.len())?;
            let mut memo = BTreeMap::new();
            let core = part.anisotropic_core(&mut memo)?;
            let core_phase = phase_mod8_from_q_values(core.q.iter(), core.q.len())?;
            if core_phase != phase {
                return None;
            }
            primary.push(FqmPrimaryWittClass {
                prime: p,
                order: part.q.len() as u128,
                core_order: core.q.len() as u128,
                core_group: core.primary_invariant_factors(p)?,
                core_exponent: core.order.iter().copied().max().unwrap_or(1) as u128,
                phase_mod8: phase,
                q_value_counts: core.q_value_counts(),
                normal_form: core.canonical_label()?,
            });
        }
        let phase_mod8 = primary
            .iter()
            .map(|p| p.phase_mod8)
            .sum::<i128>()
            .rem_euclid(8);
        Some(FqmWittClass {
            order: self.q.len() as u128,
            phase_mod8,
            primary,
        })
    }

    fn nikulin_existence_report(
        &self,
        signature: (usize, usize),
    ) -> Option<NikulinExistenceInvariants> {
        if self.q.len() > FQM_WITT_GROUP_CAP {
            return None;
        }
        let rank = signature.0.checked_add(signature.1)?;
        let sig_plus = i128::try_from(signature.0).ok()?;
        let sig_minus = i128::try_from(signature.1).ok()?;
        let required_mod8 = (sig_plus - sig_minus).rem_euclid(8);
        let module_phase_mod8 = phase_mod8_from_q_values(self.q.iter(), self.q.len())?;
        let mut obstruction = (required_mod8 != module_phase_mod8).then_some(
            NikulinExistenceObstruction::SignatureCongruence {
                required_mod8,
                module_phase_mod8,
            },
        );

        let mut primes = BTreeSet::new();
        for &ord in &self.order {
            for p in prime_factors(ord as u128) {
                primes.insert(p);
            }
        }

        let mut primary = Vec::new();
        for p in primes {
            let part = self.primary_subtable(p)?;
            let length = part.direct_product_generators()?.len();
            let order = part.q.len() as u128;
            let equality_case = rank == length;
            let even_two_primary = p == 2 && !part.has_odd_two_adic_summand();
            let mut p_adic_discriminant = None;
            let mut determinant_condition_holds = None;

            if rank < length && obstruction.is_none() {
                obstruction = Some(NikulinExistenceObstruction::RankTooSmall {
                    prime: p,
                    rank,
                    length,
                });
            }

            if equality_case && p != 2 {
                let discr = part.p_adic_discriminant()?;
                let signed_order = signed_order_for_odd_prime(order, signature.1)?;
                let signed_order_q = Rational::from_int(signed_order);
                let ok = same_square_class_odd(&signed_order_q, &discr, p)?;
                if !ok && obstruction.is_none() {
                    obstruction = Some(NikulinExistenceObstruction::OddPrimeDeterminant {
                        prime: p,
                        signed_order,
                        p_adic_discriminant: discr.clone(),
                    });
                }
                p_adic_discriminant = Some(discr);
                determinant_condition_holds = Some(ok);
            } else if equality_case && even_two_primary {
                let discr = part.p_adic_discriminant()?;
                let order_q = rational_from_u128(order)?;
                let ok = same_square_class_2_up_to_sign(&order_q, &discr)?;
                if !ok && obstruction.is_none() {
                    obstruction = Some(NikulinExistenceObstruction::TwoAdicDeterminant {
                        order,
                        p_adic_discriminant: discr.clone(),
                    });
                }
                p_adic_discriminant = Some(discr);
                determinant_condition_holds = Some(ok);
            }

            primary.push(NikulinPrimaryExistenceInvariants {
                prime: p,
                order,
                length,
                equality_case,
                even_two_primary,
                p_adic_discriminant,
                determinant_condition_holds,
            });
        }

        Some(NikulinExistenceInvariants {
            signature,
            rank,
            module_phase_mod8,
            primary,
            obstruction,
        })
    }

    fn primary_subtable(&self, p: u128) -> Option<Self> {
        let indices = self
            .order
            .iter()
            .enumerate()
            .filter_map(|(i, &ord)| is_prime_power(ord as u128, p).then_some(i))
            .collect::<Vec<_>>();
        self.induced_subtable(&indices)
    }

    fn induced_subtable(&self, indices: &[usize]) -> Option<Self> {
        let mut map = vec![usize::MAX; self.q.len()];
        for (new, &old) in indices.iter().enumerate() {
            map[old] = new;
        }
        let zero = map[self.zero];
        if zero == usize::MAX {
            return None;
        }
        let mut add = SquareTable::filled(indices.len(), 0usize);
        for (i, &old_i) in indices.iter().enumerate() {
            for (j, &old_j) in indices.iter().enumerate() {
                let s = self.add[old_i][old_j];
                let mapped = map[s];
                if mapped == usize::MAX {
                    return None;
                }
                add[i][j] = mapped;
            }
        }
        let mut out = FqmTable {
            zero,
            q: indices.iter().map(|&i| self.q[i].clone()).collect(),
            order: vec![1; indices.len()],
            add,
        };
        out.compute_orders();
        Some(out)
    }

    fn anisotropic_core(&self, memo: &mut BTreeMap<Vec<i128>, FqmTable>) -> Option<Self> {
        let raw = self.raw_label()?;
        if let Some(hit) = memo.get(&raw) {
            return Some(hit.clone());
        }
        let isotropic = (0..self.q.len())
            .filter(|&i| i != self.zero && self.q[i] == Rational::zero())
            .collect::<Vec<_>>();
        if isotropic.is_empty() {
            memo.insert(raw, self.clone());
            return Some(self.clone());
        }

        let mut best: Option<(Vec<i128>, FqmTable)> = None;
        for x in isotropic {
            let h = self.subgroup_generated(&[x]);
            if h.len() <= 1 {
                continue;
            }
            let quotient = self.quotient_by_isotropic_subgroup(&h)?;
            if quotient.q.len() >= self.q.len() {
                return None;
            }
            let core = quotient.anisotropic_core(memo)?;
            let label = core.canonical_label()?;
            if best.as_ref().is_none_or(|(b, _)| label < *b) {
                best = Some((label, core));
            }
        }
        let core = best?.1;
        memo.insert(raw, core.clone());
        Some(core)
    }

    fn quotient_by_isotropic_subgroup(&self, subgroup: &IndexSet) -> Option<Self> {
        if !subgroup.contains(self.zero) || !subgroup.iter().all(|h| self.q[h] == Rational::zero())
        {
            return None;
        }
        let mut orthogonal = IndexSet::new(self.q.len());
        for x in 0..self.q.len() {
            if subgroup
                .iter()
                .all(|h| self.bilinear_value(x, h) == Rational::zero())
            {
                orthogonal.insert(x);
            }
        }
        if !subgroup.is_subset(&orthogonal) {
            return None;
        }

        let mut coset_of = vec![usize::MAX; self.q.len()];
        let mut reps = Vec::new();
        for x in orthogonal.iter() {
            if coset_of[x] != usize::MAX {
                continue;
            }
            let id = reps.len();
            reps.push(x);
            for h in subgroup.iter() {
                let y = self.add[x][h];
                if !orthogonal.contains(y) {
                    return None;
                }
                coset_of[y] = id;
            }
        }
        let zero = coset_of[self.zero];
        if zero == usize::MAX {
            return None;
        }
        let mut add = SquareTable::filled(reps.len(), 0usize);
        for (i, &x) in reps.iter().enumerate() {
            for (j, &y) in reps.iter().enumerate() {
                let s = self.add[x][y];
                let mapped = coset_of[s];
                if mapped == usize::MAX {
                    return None;
                }
                add[i][j] = mapped;
            }
        }
        let mut out = FqmTable {
            zero,
            q: reps.iter().map(|&i| self.q[i].clone()).collect(),
            order: vec![1; reps.len()],
            add,
        };
        out.compute_orders();
        Some(out)
    }

    fn subgroup_generated(&self, gens: &[usize]) -> IndexSet {
        let mut set = IndexSet::new(self.q.len());
        let mut queue = Vec::new();
        set.insert(self.zero);
        queue.push(self.zero);
        while let Some(x) = queue.pop() {
            for &g in gens {
                let nx = self.add[x][g];
                if set.insert(nx) {
                    queue.push(nx);
                }
            }
        }
        set
    }

    fn generator_rank(&self) -> usize {
        let mut gens = Vec::new();
        let mut covered = self.subgroup_generated(&gens);
        while covered.len() < self.q.len() {
            let g = (0..self.q.len())
                .filter(|&i| !covered.contains(i))
                .max_by_key(|&i| self.order[i])
                .expect("uncovered finite-module element exists");
            gens.push(g);
            covered = self.subgroup_generated(&gens);
        }
        gens.len()
    }

    fn direct_product_generators(&self) -> Option<Vec<usize>> {
        if self.q.len() == 1 {
            return Some(Vec::new());
        }
        let mut candidates = (0..self.q.len())
            .filter(|&i| i != self.zero)
            .collect::<Vec<_>>();
        candidates.sort_by(|&a, &b| self.order[b].cmp(&self.order[a]).then_with(|| a.cmp(&b)));
        let mut gens = Vec::new();
        let covered = self.subgroup_generated(&gens);
        self.direct_product_generators_rec(&candidates, &mut gens, covered)
    }

    fn direct_product_generators_rec(
        &self,
        candidates: &[usize],
        gens: &mut Vec<usize>,
        covered: IndexSet,
    ) -> Option<Vec<usize>> {
        if covered.len() == self.q.len() {
            return Some(gens.clone());
        }
        for &g in candidates {
            if covered.contains(g) || gens.contains(&g) {
                continue;
            }
            let mut trial = gens.clone();
            trial.push(g);
            let trial_covered = self.subgroup_generated(&trial);
            let expected = covered.len().checked_mul(self.order[g])?;
            if trial_covered.len() != expected {
                continue;
            }
            gens.push(g);
            if let Some(out) = self.direct_product_generators_rec(candidates, gens, trial_covered) {
                return Some(out);
            }
            gens.pop();
        }
        None
    }

    fn p_adic_discriminant(&self) -> Option<Rational> {
        let gens = self.direct_product_generators()?;
        if gens.is_empty() {
            return Some(Rational::one());
        }
        let mut matrix = vec![vec![Rational::zero(); gens.len()]; gens.len()];
        for (i, &x) in gens.iter().enumerate() {
            for (j, &y) in gens.iter().enumerate() {
                matrix[i][j] = self.bilinear_value(x, y);
            }
        }
        let det_pairing = rational_det(matrix)?;
        det_pairing.inv()
    }

    fn has_odd_two_adic_summand(&self) -> bool {
        (0..self.q.len()).any(|i| {
            self.order[i] == 2 && self.q[i].denom() == 2 && self.q[i].numer().rem_euclid(2) == 1
        })
    }

    fn canonical_label(&self) -> Option<Vec<i128>> {
        if self.q.len() == 1 {
            return Some(vec![1, 0]);
        }
        let rank = self.generator_rank();
        let candidates = (0..self.q.len())
            .filter(|&i| i != self.zero)
            .collect::<Vec<_>>();
        let mut tuple = Vec::with_capacity(rank);
        let mut best: Option<Vec<i128>> = None;
        let mut seen = 0u128;
        self.canonical_label_rec(rank, &candidates, &mut tuple, &mut best, &mut seen)?;
        best
    }

    fn canonical_label_rec(
        &self,
        rank: usize,
        candidates: &[usize],
        tuple: &mut Vec<usize>,
        best: &mut Option<Vec<i128>>,
        seen: &mut u128,
    ) -> Option<()> {
        if tuple.len() == rank {
            *seen = seen.checked_add(1)?;
            if *seen > FQM_WITT_TUPLE_CAP {
                return None;
            }
            if let Some(order) = self.ordered_elements_from_generators(tuple) {
                let label = self.label_for_order(&order)?;
                if best.as_ref().is_none_or(|b| label < *b) {
                    *best = Some(label);
                }
            }
            return Some(());
        }
        for &cand in candidates {
            if tuple.contains(&cand) {
                continue;
            }
            tuple.push(cand);
            self.canonical_label_rec(rank, candidates, tuple, best, seen)?;
            tuple.pop();
        }
        Some(())
    }

    fn ordered_elements_from_generators(&self, gens: &[usize]) -> Option<Vec<usize>> {
        let mut order = vec![self.zero];
        let mut seen = vec![false; self.q.len()];
        seen[self.zero] = true;
        let mut cursor = 0usize;
        while cursor < order.len() {
            let x = order[cursor];
            for &g in gens {
                let nx = self.add[x][g];
                if !seen[nx] {
                    seen[nx] = true;
                    order.push(nx);
                }
            }
            cursor += 1;
        }
        (order.len() == self.q.len()).then_some(order)
    }

    fn label_for_order(&self, order: &[usize]) -> Option<Vec<i128>> {
        let mut pos = vec![usize::MAX; self.q.len()];
        for (i, &old) in order.iter().enumerate() {
            pos[old] = i;
        }
        let mut out = Vec::with_capacity(2 + 2 * order.len() + order.len() * order.len());
        out.push(i128::try_from(order.len()).ok()?);
        for &old in order {
            out.push(self.q[old].numer());
            out.push(self.q[old].denom());
        }
        for &x in order {
            for &y in order {
                out.push(i128::try_from(pos[self.add[x][y]]).ok()?);
            }
        }
        Some(out)
    }

    fn raw_label(&self) -> Option<Vec<i128>> {
        let order = (0..self.q.len()).collect::<Vec<_>>();
        self.label_for_order(&order)
    }

    fn q_value_counts(&self) -> Vec<FqmValueCount> {
        let mut counts: BTreeMap<(i128, i128), u128> = BTreeMap::new();
        for q in &self.q {
            *counts.entry((q.numer(), q.denom())).or_default() += 1;
        }
        counts
            .into_iter()
            .map(|((numer, denom), count)| FqmValueCount {
                numer,
                denom,
                count,
            })
            .collect()
    }

    fn primary_invariant_factors(&self, p: u128) -> Option<Vec<u128>> {
        let exponent = self.order.iter().copied().max().unwrap_or(1) as u128;
        let max_power = exact_prime_power_exponent(exponent, p)?;
        let mut killed_log = vec![0u128; usize::try_from(max_power + 1).ok()?];
        killed_log[0] = 0;
        let mut p_to_j = 1u128;
        for j in 1..=max_power {
            p_to_j = p_to_j.checked_mul(p)?;
            let count = self
                .order
                .iter()
                .filter(|&&ord| p_to_j.is_multiple_of(ord as u128))
                .count() as u128;
            killed_log[usize::try_from(j).ok()?] = exact_prime_power_exponent(count, p)?;
        }

        let mut ge = vec![0u128; usize::try_from(max_power + 2).ok()?];
        for j in 1..=max_power {
            let ji = usize::try_from(j).ok()?;
            ge[ji] = killed_log[ji].checked_sub(killed_log[ji - 1])?;
        }
        let mut factors = Vec::new();
        for j in 1..=max_power {
            let ji = usize::try_from(j).ok()?;
            let exact = ge[ji].checked_sub(ge[ji + 1])?;
            let factor = pow_u128(p, j)?;
            for _ in 0..exact {
                factors.push(factor);
            }
        }
        Some(factors)
    }

    fn bilinear_value(&self, x: usize, y: usize) -> Rational {
        let diff = self.q[self.add[x][y]].sub(&self.q[x]).sub(&self.q[y]);
        rational_half_mod1(diff)
    }

    fn quadratic_values_are_even(&self) -> bool {
        (0..self.q.len()).all(|x| {
            let nx = self.neg(x);
            self.q[nx] == self.q[x]
        })
    }

    fn bilinear_form_is_biadditive(&self) -> bool {
        for x in 0..self.q.len() {
            for y in 0..self.q.len() {
                for z in 0..self.q.len() {
                    let yz = self.add[y][z];
                    let lhs = self.bilinear_value(x, yz);
                    let rhs = rational_mod_int(
                        self.bilinear_value(x, y).add(&self.bilinear_value(x, z)),
                        1,
                    );
                    if lhs != rhs {
                        return false;
                    }
                    let xy = self.add[x][y];
                    let lhs = self.bilinear_value(xy, z);
                    let rhs = rational_mod_int(
                        self.bilinear_value(x, z).add(&self.bilinear_value(y, z)),
                        1,
                    );
                    if lhs != rhs {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn is_nondegenerate(&self) -> bool {
        (0..self.q.len()).all(|x| {
            x == self.zero
                || (0..self.q.len()).any(|y| self.bilinear_value(x, y) != Rational::zero())
        })
    }

    fn neg(&self, x: usize) -> usize {
        (0..self.q.len())
            .find(|&y| self.add[x][y] == self.zero)
            .expect("finite abelian group element has an inverse")
    }
}

fn coords_from_index(mut index: usize, factors: &[u128]) -> Option<Vec<u128>> {
    let mut out = vec![0u128; factors.len()];
    for (i, &d) in factors.iter().enumerate().rev() {
        let du = usize::try_from(d).ok()?;
        out[i] = (index % du) as u128;
        index /= du;
    }
    Some(out)
}

fn rational_half_mod1(x: Rational) -> Rational {
    let den = x
        .denom()
        .checked_mul(2)
        .expect("rational denominator exceeds i128");
    rational_mod_int(Rational::new(x.numer(), den), 1)
}

fn rational_from_u128(n: u128) -> Option<Rational> {
    Some(Rational::from_int(i128::try_from(n).ok()?))
}

fn signed_order_for_odd_prime(order: u128, t_minus: usize) -> Option<i128> {
    let order = i128::try_from(order).ok()?;
    Some(if t_minus.is_multiple_of(2) {
        order
    } else {
        order.checked_neg()?
    })
}

fn same_square_class_odd(a: &Rational, b: &Rational, p: u128) -> Option<bool> {
    if a.is_zero() || b.is_zero() || p == 2 {
        return None;
    }
    let p_i = i128::try_from(p).ok()?;
    let ratio = a.mul(&b.inv()?);
    if rat_val(&ratio, p_i) % 2 != 0 {
        return Some(false);
    }
    try_is_square_qp(odd_unit_residue(&ratio, p_i), p)
}

fn same_square_class_2_up_to_sign(a: &Rational, b: &Rational) -> Option<bool> {
    if a.is_zero() || b.is_zero() {
        return None;
    }
    let ratio = a.mul(&b.inv()?);
    if rat_val(&ratio, 2) % 2 != 0 {
        return Some(false);
    }
    Some(matches!(unit_mod8(&ratio), 1 | 7))
}

fn rational_det(mut a: Vec<Vec<Rational>>) -> Option<Rational> {
    let n = a.len();
    if a.iter().any(|row| row.len() != n) {
        return None;
    }
    let mut det = Rational::one();
    for i in 0..n {
        let pivot = (i..n).find(|&r| !a[r][i].is_zero())?;
        if pivot != i {
            a.swap(i, pivot);
            det = det.neg();
        }
        let pivot_value = a[i][i].clone();
        det = det.mul(&pivot_value);
        let pivot_inv = pivot_value.inv()?;
        for r in (i + 1)..n {
            if a[r][i].is_zero() {
                continue;
            }
            let factor = a[r][i].mul(&pivot_inv);
            for c in i..n {
                let correction = factor.mul(&a[i][c]);
                a[r][c] = a[r][c].sub(&correction);
            }
        }
    }
    Some(det)
}

fn exact_prime_power_exponent(mut n: u128, p: u128) -> Option<u128> {
    if n == 1 {
        return Some(0);
    }
    let mut k = 0u128;
    while n > 1 && n.is_multiple_of(p) {
        n /= p;
        k += 1;
    }
    (n == 1).then_some(k)
}

fn pow_u128(base: u128, exp: u128) -> Option<u128> {
    let mut out = 1u128;
    for _ in 0..exp {
        out = out.checked_mul(base)?;
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::forms::{e_6, e_7, DiscriminantForm, IntegralForm};

    // `root_lattices::a_n`/`d_n` are `Option`-checked on out-of-domain rank; every
    // call site below passes an in-domain rank, so these thin local wrappers keep
    // the test bodies unchanged.
    fn a_n(n: usize) -> IntegralForm {
        crate::forms::a_n(n).unwrap()
    }
    fn d_n(n: usize) -> IntegralForm {
        crate::forms::d_n(n).unwrap()
    }

    #[test]
    fn native_cyclic_module_matches_lattice_a1() {
        let native = FiniteQuadraticModule::cyclic(2, Rational::new(1, 2)).unwrap();
        let from_lattice = DiscriminantForm::from_lattice(&a_n(1))
            .unwrap()
            .fqm_witt_class()
            .unwrap();
        assert_eq!(native.witt_class().unwrap(), from_lattice);
    }

    #[test]
    fn fqm_witt_reduces_hyperbolic_two_primary_pair() {
        let a1 = DiscriminantForm::from_lattice(&a_n(1)).unwrap();
        let e7 = DiscriminantForm::from_lattice(&e_7()).unwrap();
        assert_ne!(a1.fqm_witt_class().unwrap(), e7.fqm_witt_class().unwrap());

        let hyperbolic = FiniteQuadraticModule::cyclic(2, Rational::new(1, 2))
            .unwrap()
            .direct_sum(&FiniteQuadraticModule::cyclic(2, Rational::new(3, 2)).unwrap())
            .unwrap();
        let class = hyperbolic.witt_class().unwrap();
        assert!(class.is_trivial());
        assert_eq!(class.phase_mod8, 0);
    }

    #[test]
    fn fqm_witt_reduces_hyperbolic_odd_primary_pair() {
        let a2 = DiscriminantForm::from_lattice(&a_n(2)).unwrap();
        let e6 = DiscriminantForm::from_lattice(&e_6()).unwrap();
        assert_eq!(a2.is_fqm_witt_equivalent(&e6), Some(false));
        assert!(DiscriminantForm::from_lattice(&a_n(2).direct_sum(&e_6()))
            .unwrap()
            .fqm_witt_class()
            .unwrap()
            .is_trivial());

        let sum = FiniteQuadraticModule::cyclic(3, Rational::new(2, 3))
            .unwrap()
            .direct_sum(&FiniteQuadraticModule::cyclic(3, Rational::new(4, 3)).unwrap())
            .unwrap();
        let class = sum.witt_class().unwrap();
        assert!(class.is_trivial());
        assert_eq!(class.phase_mod8, 0);
    }

    #[test]
    fn fqm_witt_refines_phase_projection() {
        let a1 = DiscriminantForm::from_lattice(&a_n(1)).unwrap();
        let class = a1.fqm_witt_class().unwrap();
        let phase = a1.fqm_gauss_phase().unwrap();
        assert_eq!(class.order, phase.order as u128);
        assert_eq!(class.phase_mod8, phase.phase_mod8);
        assert_eq!(class.primary[0].phase_mod8, phase.primary[0].phase_mod8);
        assert_eq!(class.primary[0].core_group, vec![2]);
        assert_eq!(class.primary[0].q_value_counts.len(), 2);
    }

    #[test]
    fn fqm_witt_class_can_leave_a_noncyclic_anisotropic_core() {
        // Every case above (A_1, the A_1(+)E_7/A_2(+)E_6 hyperbolic pairs) reduces
        // to a CYCLIC core (`core_group` of length <= 1), because a single isotropic
        // generator is always enough to Witt-cancel a rank-2 hyperbolic summand. A_1
        // (+) A_1 has discriminant group (Z/2)^2 with q-values {0, 1/2, 1/2, 1} on
        // its four elements (q(x,y) = q_{A1}(x) + q_{A1}(y), q_{A1}(1) = 1/2): the
        // only element with q = 0 is the identity itself, so `anisotropic_core` can
        // never find a nonzero isotropic generator to quotient by, and the ENTIRE
        // rank-2 group survives as the core, unreduced.
        let a1a1 = a_n(1).direct_sum(&a_n(1));
        let disc = DiscriminantForm::from_lattice(&a1a1).unwrap();
        assert_eq!(disc.group(), vec![2, 2]);
        let class = disc.fqm_witt_class().unwrap();
        assert_eq!(class.primary.len(), 1);
        let p2 = &class.primary[0];
        assert_eq!(p2.prime, 2);
        assert_eq!(p2.order, 4, "no reduction: the core is the whole group");
        assert_eq!(p2.core_order, 4);
        assert_eq!(
            p2.core_group,
            vec![2, 2],
            "noncyclic: two invariant factors"
        );
        assert_eq!(p2.core_exponent, 2);
        assert_eq!(p2.phase_mod8, 2, "1/2+1/2 doubled A_1 phase (1+1 mod 8)");
        assert!(!class.is_trivial());
    }

    #[test]
    fn fqm_witt_class_reduces_an_exponent_eight_two_primary_block() {
        // Every prior 2-primary case tops out at exponent 4 (A_3's Z/4). A_7 has
        // discriminant group Z/8 (A_n always has Z/(n+1)) — genuinely exponent 8,
        // exercising the `k=3` rung of the reduction the smaller cases never reach.
        //
        // Hand derivation, independent of this file (cross-checked with an exact
        // `Fraction` Python port of the same reduction algorithm before writing
        // this assertion): A_n's canonical discriminant generator has q(1) = n/(n+1)
        // mod 2Z, so A_7 has q(1) = 7/8. On the cyclic group Z/8 this is
        // `q(k) = k^2 * 7/8 mod 2`, giving q = [0, 7/8, 3/2, 15/8, 0, 15/8, 3/2,
        // 7/8]. Every element x of EXACT order 8 in ANY nonsingular finite
        // quadratic module has q(4x) = 16*q(x) mod 2 = 4*(4*q(x)) mod 2 (an integer
        // multiple of 4, since evenness forces q(x) to have denominator dividing 4
        // when x has order 8), hence q(4x) = 0 always — so the order-4 element
        // (index 4 here) is ALWAYS isotropic. This is why no anisotropic 2-adic
        // block can have exponent 8: the order-4 subtree always Witt-cancels first.
        //
        // Quotienting by the isotropic subgroup {0, 4} restricted to its own
        // orthogonal complement {0, 2, 4, 6} (b(k,4) = 0 only for even k) leaves the
        // 2-element quotient {[0,4], [2,6]}, represented by q(2) = 3/2: a Z/2
        // anisotropic core (3/2 != 0), NOT the trivial module.
        let a7 = a_n(7);
        let disc = DiscriminantForm::from_lattice(&a7).unwrap();
        assert_eq!(disc.group(), vec![8], "exponent 8 going in");
        assert_eq!(disc.quadratic_value_mod2(&[1]), Rational::new(7, 8));
        let class = disc.fqm_witt_class().unwrap();
        assert_eq!(class.primary.len(), 1);
        let p2 = &class.primary[0];
        assert_eq!(p2.prime, 2);
        assert_eq!(p2.order, 8, "the input 2-primary block is exponent 8");
        assert_eq!(
            p2.core_order, 2,
            "reduces away, as the theorem above forces"
        );
        assert_eq!(p2.core_group, vec![2]);
        assert_eq!(
            p2.core_exponent, 2,
            "the surviving core is exponent 2, not 8"
        );
        assert_eq!(
            p2.q_value_counts,
            vec![
                FqmValueCount {
                    numer: 0,
                    denom: 1,
                    count: 1
                },
                FqmValueCount {
                    numer: 3,
                    denom: 2,
                    count: 1
                },
            ],
            "the surviving generator carries q = 3/2, matching the hand trace"
        );
        assert_eq!(p2.phase_mod8, 7);
        assert_eq!(disc.milgram_signature_mod8_fqm(), Some(7));
    }

    #[test]
    fn fqm_witt_class_of_d4_matches_brown_invariant() {
        // D_4's discriminant form is a standard textbook example (Conway-Sloane
        // SPLAG): the "Arf invariant 1" quadratic form on (Z/2)^2, whose
        // three nonzero vectors ALL carry q = 1 (no isotropic vector at all, unlike
        // a hyperbolic plane's single nonzero isotropic vector). Rather than lean on
        // an external citation I can't source-pin precisely, this pins the D_4 Witt
        // class two independent ways within this crate:
        //
        // (1) direct hand trace of the reduction algorithm: since every nonzero
        //     element has q = 1 != 0, `anisotropic_core` can never find an isotropic
        //     generator, so the FULL (Z/2)^2 group survives unreduced as the core —
        //     same shape argument as the A_1 (+) A_1 test above, but with D_4's
        //     different q-value multiset ({0: 1, 1: 3} instead of {0: 1, 1/2: 2,
        //     1: 1}), giving a genuinely different p-primary Witt class.
        // (2) cross-check against `DiscriminantForm::brown_invariant`
        //     (`forms/integral/discriminant/form.rs`), a COMPLETELY separate
        //     exact-integer code path (radical splitting + line/plane reduction,
        //     no cyclotomic arithmetic) tested independently
        //     (`brown_invariant_recovers_signature_mod8_on_2_elementary_forms`) to
        //     beta(D_4) = 4. The Milgram/Brown identity beta = sign(L) mod 8
        //     forces the FQM phase to equal that same 4 — an independently-derived
        //     pin on `class.phase_mod8`, not just a self-consistency check of this
        //     file's own cyclotomic machinery.
        let d4 = d_n(4);
        let disc = DiscriminantForm::from_lattice(&d4).unwrap();
        assert_eq!(disc.group(), vec![2, 2]);
        let brown = disc.brown_invariant().expect("D_4 is 2-elementary");
        assert_eq!(brown.beta, 4, "independently pinned elsewhere in the suite");

        let class = disc.fqm_witt_class().unwrap();
        assert_eq!(class.primary.len(), 1);
        let p2 = &class.primary[0];
        assert_eq!(p2.prime, 2);
        assert_eq!(p2.order, 4);
        assert_eq!(
            p2.core_order, 4,
            "anisotropic: no isotropic vector to cancel"
        );
        assert_eq!(p2.core_group, vec![2, 2]);
        assert_eq!(
            p2.q_value_counts,
            vec![
                FqmValueCount {
                    numer: 0,
                    denom: 1,
                    count: 1
                },
                FqmValueCount {
                    numer: 1,
                    denom: 1,
                    count: 3
                },
            ]
        );
        assert_eq!(
            p2.phase_mod8, brown.beta as i128,
            "FQM phase must match the independently computed Brown invariant"
        );
        assert_eq!(class.phase_mod8, brown.beta as i128);
        assert!(!class.is_trivial());
    }

    #[test]
    fn nikulin_existence_accepts_realized_lattice_discriminant_forms() {
        for lattice in [a_n(1), a_n(2), e_6(), e_7()] {
            let signature = lattice.signature();
            let q = DiscriminantForm::from_lattice(&lattice).unwrap();
            let report = q.nikulin_existence_report(signature).unwrap();
            assert!(
                report.exists(),
                "realized lattice should pass Nikulin 1.10.1"
            );
            assert_eq!(q.nikulin_even_lattice_exists(signature), Some(true));
        }
    }

    #[test]
    fn nikulin_existence_keeps_odd_two_primary_boundary() {
        let q = DiscriminantForm::from_lattice(&a_n(1)).unwrap();
        let report = q.nikulin_existence_report((1, 0)).unwrap();
        assert!(report.exists());
        assert_eq!(report.primary.len(), 1);
        assert_eq!(report.primary[0].prime, 2);
        assert_eq!(report.primary[0].length, 1);
        assert!(report.primary[0].equality_case);
        assert!(!report.primary[0].even_two_primary);
        assert_eq!(report.primary[0].determinant_condition_holds, None);

        let blocked = q.nikulin_existence_report((0, 1)).unwrap();
        assert_eq!(
            blocked.obstruction,
            Some(NikulinExistenceObstruction::SignatureCongruence {
                required_mod8: 7,
                module_phase_mod8: 1,
            })
        );
    }

    #[test]
    fn nikulin_existence_checks_odd_primary_borderline() {
        let hyperbolic_three = FiniteQuadraticModule::cyclic(3, Rational::new(2, 3))
            .unwrap()
            .direct_sum(&FiniteQuadraticModule::cyclic(3, Rational::new(4, 3)).unwrap())
            .unwrap();

        let report = hyperbolic_three.nikulin_existence_report((1, 1)).unwrap();
        assert!(report.exists());
        assert_eq!(report.primary.len(), 1);
        assert_eq!(report.primary[0].prime, 3);
        assert_eq!(report.primary[0].length, 2);
        assert!(report.primary[0].equality_case);
        assert_eq!(report.primary[0].determinant_condition_holds, Some(true));

        let too_small = hyperbolic_three.nikulin_existence_report((0, 0)).unwrap();
        assert_eq!(
            too_small.obstruction,
            Some(NikulinExistenceObstruction::RankTooSmall {
                prime: 3,
                rank: 0,
                length: 2,
            })
        );
    }

    #[test]
    fn nikulin_existence_checks_even_two_primary_borderline() {
        let u2 = IntegralForm::new(vec![vec![0, 2], vec![2, 0]]).unwrap();
        let q = DiscriminantForm::from_lattice(&u2).unwrap();
        let report = q.nikulin_existence_report((1, 1)).unwrap();
        assert!(report.exists());
        assert_eq!(report.primary.len(), 1);
        assert_eq!(report.primary[0].prime, 2);
        assert_eq!(report.primary[0].length, 2);
        assert!(report.primary[0].equality_case);
        assert!(report.primary[0].even_two_primary);
        assert_eq!(report.primary[0].determinant_condition_holds, Some(true));
    }

    #[test]
    fn nikulin_existence_forces_odd_prime_determinant_obstruction() {
        // Hand derivation (cross-checked independently with an exact-`Fraction`
        // Python port of this file's algorithm, not by reading this code's output):
        // build the 3-primary module A_3 = Z/3 x Z/9 as the orthogonal sum of two
        // cyclic pieces. Evenness (q(-x) = q(x)) forces an odd-order cyclic
        // generator_q = c/order to have c an EVEN multiple of 1/order — i.e.
        // generator_q = 2j/order for an integer j — so cyclic(3, 2/3) (j=1) and
        // cyclic(9, 4/9) (j=2) are the smallest nontrivial even choices on each
        // factor. Both are individually nonsingular, and the constructor confirms
        // the orthogonal sum stays nonsingular.
        //
        // A_3 = Z/3 x Z/9 is not cyclic (gcd(3,9) = 3), so l(A_3) = 2: a rank-2
        // signature puts Nikulin's equality case in play. The greedy generator
        // search picks the two natural cyclic generators; their pairing matrix is
        // diagonal, `b(order-9 gen) = (q(2)-2q(1))/2 mod 1 = (16/9 - 8/9)/2 = 4/9`
        // and `b(order-3 gen) = (2/3-4/3)/2 mod 1 = 2/3`, so
        // `discr K(q_3) = 1/det = 1/(4/9 * 2/3) = 27/8`.
        //
        // The module's total Milgram phase is 2 mod 8 (an exact quadratic Gauss sum
        // over 27 elements), which matches `t+ - t- = 2` at signature (2,0) — so the
        // *signature* congruence holds and the equality-case determinant condition
        // is the one Nikulin's theorem tests. `(-1)^{t-}|A_3| = 27` (t- = 0, even),
        // and `27 / (27/8) = 8`, a 3-adic unit (val_3(8) = 0) with residue `8 mod 3 =
        // 2` — a non-residue mod 3 (the only nonzero square mod 3 is 1, since
        // `(Z/3)^* = {1,2}` squares to `{1,1}`). So `(-1)^{t-}|A_3|` and
        // `discr K(q_3)` land in different square classes of `Q_3^*/Q_3^{*2}`: the
        // theorem's equality-case necessary condition genuinely fails, and no even
        // lattice of signature (2,0) can realize this discriminant form.
        let a3 = FiniteQuadraticModule::cyclic(3, Rational::new(2, 3)).unwrap();
        let a9 = FiniteQuadraticModule::cyclic(9, Rational::new(4, 9)).unwrap();
        let module = a3.direct_sum(&a9).unwrap();
        assert_eq!(module.order(), 27);

        let report = module.nikulin_existence_report((2, 0)).unwrap();
        assert_eq!(report.module_phase_mod8, 2);
        assert!(!report.exists());
        assert_eq!(report.primary.len(), 1);
        assert_eq!(report.primary[0].prime, 3);
        assert_eq!(report.primary[0].length, 2);
        assert!(report.primary[0].equality_case);
        assert_eq!(
            report.primary[0].p_adic_discriminant,
            Some(Rational::new(27, 8))
        );
        assert_eq!(report.primary[0].determinant_condition_holds, Some(false));
        assert_eq!(
            report.obstruction,
            Some(NikulinExistenceObstruction::OddPrimeDeterminant {
                prime: 3,
                signed_order: 27,
                p_adic_discriminant: Rational::new(27, 8),
            })
        );
        assert_eq!(module.nikulin_even_lattice_exists((2, 0)), Some(false));
    }

    #[test]
    fn nikulin_existence_forces_two_adic_determinant_obstruction() {
        // Hand derivation (same independent Python cross-check as the odd-prime
        // witness above): build A_2 = Z/4 x Z/4 as cyclic(4, 1/4) (+) cyclic(4,
        // 7/4). Every order-2 element (the three nonzero elements of the
        // `{0,2}x{0,2}` subgroup) carries an INTEGER q-value (1, 1, and 0
        // respectively, denominator 1) rather than an odd multiple of 1/2 — so this
        // is Nikulin's "even" 2-primary type (`even_two_primary`), not the "odd"
        // type the (existing) `nikulin_existence_checks_even_two_primary_borderline`
        // hyperbolic-plane test also covers.
        //
        // Z/4 x Z/4 is not cyclic, so l(A_2) = 2: rank-2 puts the equality case in
        // play. The pairing matrix on the two natural generators is diagonal:
        // `b(gen of cyclic(4,1/4)) = (q(2)-2q(1))/2 mod 1 = (1 - 1/2)/2 = 1/4` and
        // `b(gen of cyclic(4,7/4)) = (1 - 7/2)/2 mod 1 = 3/4`, so
        // `discr K(q_2) = 1/det = 1/(1/4 * 3/4) = 16/3`.
        //
        // The module's total Milgram phase is 0 mod 8, matching `t+ - t- = 0` at
        // signature (1,1) — so signature congruence holds and the equality-case
        // determinant condition is live. `|A_2| = 16`, and `16 / (16/3) = 3`: a
        // 2-adic unit (val_2(3) = 0) with `3 mod 8 = 3`, which is neither 1 nor 7 —
        // not a 2-adic square up to sign. So `|A_2|` and `discr K(q_2)` fail
        // Nikulin's 2-adic equality-case condition, and no even lattice of
        // signature (1,1) can realize this discriminant form.
        let g1 = FiniteQuadraticModule::cyclic(4, Rational::new(1, 4)).unwrap();
        let g2 = FiniteQuadraticModule::cyclic(4, Rational::new(7, 4)).unwrap();
        let module = g1.direct_sum(&g2).unwrap();
        assert_eq!(module.order(), 16);

        let report = module.nikulin_existence_report((1, 1)).unwrap();
        assert_eq!(report.module_phase_mod8, 0);
        assert!(!report.exists());
        assert_eq!(report.primary.len(), 1);
        assert_eq!(report.primary[0].prime, 2);
        assert_eq!(report.primary[0].length, 2);
        assert!(report.primary[0].equality_case);
        assert!(report.primary[0].even_two_primary);
        assert_eq!(
            report.primary[0].p_adic_discriminant,
            Some(Rational::new(16, 3))
        );
        assert_eq!(report.primary[0].determinant_condition_holds, Some(false));
        assert_eq!(
            report.obstruction,
            Some(NikulinExistenceObstruction::TwoAdicDeterminant {
                order: 16,
                p_adic_discriminant: Rational::new(16, 3),
            })
        );
        assert_eq!(module.nikulin_even_lattice_exists((1, 1)), Some(false));
    }

    #[test]
    fn fqm_witt_class_display_renders_order_phase_and_primary_summands() {
        let a1 = DiscriminantForm::from_lattice(&a_n(1)).unwrap();
        let class = a1.fqm_witt_class().unwrap();
        assert_eq!(
            class.primary[0].to_string(),
            "FqmPrimaryWittClass(prime=2, order=2, core_order=2, core_group=[2], core_exponent=2, phase_mod8=1)"
        );
        assert_eq!(class.primary[0].display(), class.primary[0].to_string());
        assert_eq!(
            class.to_string(),
            "FqmWittClass(order=2, phase_mod8=1, primary=[FqmPrimaryWittClass(prime=2, order=2, core_order=2, core_group=[2], core_exponent=2, phase_mod8=1)])"
        );
        assert_eq!(class.display(), class.to_string());
    }

    #[test]
    fn nikulin_existence_obstruction_display_covers_every_variant() {
        let sig = NikulinExistenceObstruction::SignatureCongruence {
            required_mod8: 7,
            module_phase_mod8: 1,
        };
        assert_eq!(
            sig.to_string(),
            "SignatureCongruence(required_mod8=7, module_phase_mod8=1)"
        );
        assert_eq!(sig.display(), sig.to_string());

        let rank = NikulinExistenceObstruction::RankTooSmall {
            prime: 3,
            rank: 0,
            length: 2,
        };
        assert_eq!(rank.to_string(), "RankTooSmall(prime=3, rank=0, length=2)");

        let odd = NikulinExistenceObstruction::OddPrimeDeterminant {
            prime: 3,
            signed_order: 27,
            p_adic_discriminant: Rational::new(27, 8),
        };
        assert_eq!(
            odd.to_string(),
            "OddPrimeDeterminant(prime=3, signed_order=27, p_adic_discriminant=27/8)"
        );

        let two_adic = NikulinExistenceObstruction::TwoAdicDeterminant {
            order: 16,
            p_adic_discriminant: Rational::new(16, 3),
        };
        assert_eq!(
            two_adic.to_string(),
            "TwoAdicDeterminant(order=16, p_adic_discriminant=16/3)"
        );
    }

    #[test]
    fn nikulin_existence_invariants_display_renders_the_verdict() {
        let a3 = FiniteQuadraticModule::cyclic(3, Rational::new(2, 3)).unwrap();
        let a9 = FiniteQuadraticModule::cyclic(9, Rational::new(4, 9)).unwrap();
        let module = a3.direct_sum(&a9).unwrap();
        let report = module.nikulin_existence_report((2, 0)).unwrap();
        assert_eq!(
            report.primary[0].to_string(),
            "NikulinPrimaryExistenceInvariants(prime=3, order=27, length=2, equality_case=true, even_two_primary=false, p_adic_discriminant=27/8, determinant_condition_holds=false)"
        );
        assert_eq!(report.primary[0].display(), report.primary[0].to_string());
        assert_eq!(
            report.to_string(),
            "NikulinExistenceInvariants(signature=(2, 0), rank=2, module_phase_mod8=2, exists=false, obstruction=OddPrimeDeterminant(prime=3, signed_order=27, p_adic_discriminant=27/8))"
        );
        assert_eq!(report.display(), report.to_string());

        let d4 = d_n(4);
        let disc = DiscriminantForm::from_lattice(&d4).unwrap();
        let clean = disc.nikulin_existence_report((4, 0)).unwrap();
        assert_eq!(
            clean.to_string(),
            "NikulinExistenceInvariants(signature=(4, 0), rank=4, module_phase_mod8=4, exists=true, obstruction=none)"
        );
    }
}
