//! The Witt group of quadratic forms over a nim-field — the abstraction that
//! sits behind the `A ⊕ A ≅ H ⊕ H` fact `arf.rs` checks pointwise.
//!
//! Two nonsingular quadratic forms are **Witt-equivalent** if they become
//! isomorphic after adding hyperbolic planes; the equivalence classes form an
//! abelian group `W_q(F)` under orthogonal sum `⊥`, with the hyperbolic plane as
//! identity. Over a *finite* field of characteristic 2 the anisotropic forms are
//! just two — the zero form (Arf 0) and the unique anisotropic plane (Arf 1) —
//! so `W_q(F_{2^m}) ≅ ℤ/2`, **classified completely by the Arf invariant**, and
//! the group law is XOR of Arf invariants. (Over the full algebraically-closed
//! On₂, or other fields, `W_q` can be richer; for the finite nim-subfields this
//! engine targets, Arf is the whole story.)
//!
//! So `WittClass` makes the additivity executable as a group: `w(A) + w(A) = 0`
//! is the same statement as `A ⊕ A ≅ H ⊕ H`, now a one-liner.

use crate::arf::arf_invariant;
use crate::clifford::Metric;
use crate::nimber::Nimber;

/// A class in the Witt group `W_q(F) ≅ ℤ/2` of a finite nim-field: the Arf
/// invariant of a form's anisotropic core (hyperbolic planes are the identity).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WittClass {
    /// The class, 0 or 1 — equivalently the Arf invariant of the nonsingular core.
    pub arf: u8,
}

impl WittClass {
    /// The identity: the class of the hyperbolic plane (and of the zero form).
    pub fn zero() -> Self {
        WittClass { arf: 0 }
    }

    /// The Witt class of a nimber Clifford metric — the Arf invariant of its
    /// nonsingular core. (Arf is a Witt invariant: it ignores hyperbolic summands
    /// and the polar-form radical, so this is well defined on the class.)
    pub fn from_metric(metric: &Metric<Nimber>) -> Self {
        WittClass {
            arf: arf_invariant(metric).arf,
        }
    }

    /// The group operation: the class of the orthogonal sum `⊥` of two forms.
    /// Arf is additive, hyperbolics vanish, so this is XOR of the Arf invariants.
    pub fn add(&self, other: &WittClass) -> WittClass {
        WittClass {
            arf: self.arf ^ other.arf,
        }
    }

    /// In `ℤ/2` every element is its own inverse (`w + w = 0`).
    pub fn neg(&self) -> WittClass {
        *self
    }

    /// Whether this is the identity class — i.e. the form is hyperbolic (its
    /// anisotropic core is zero).
    pub fn is_hyperbolic(&self) -> bool {
        self.arf == 0
    }

    /// Dimension of the anisotropic core: 0 (hyperbolic) or 2 (the plane).
    pub fn anisotropic_dim(&self) -> usize {
        if self.arf == 0 {
            0
        } else {
            2
        }
    }

    pub fn display(&self) -> String {
        if self.arf == 0 {
            "0 (hyperbolic class)".to_string()
        } else {
            "[anisotropic plane] (Arf 1)".to_string()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn metric(qs: &[u64], bs: &[((usize, usize), u64)]) -> Metric<Nimber> {
        let q = qs.iter().map(|&x| Nimber(x)).collect();
        let mut b = BTreeMap::new();
        for &((i, j), v) in bs {
            b.insert((i, j), Nimber(v));
        }
        Metric::new(q, b)
    }

    #[test]
    fn hyperbolic_is_identity_anisotropic_is_order_two() {
        let h = WittClass::from_metric(&metric(&[0, 0], &[((0, 1), 1)])); // Arf 0
        let a = WittClass::from_metric(&metric(&[1, 1], &[((0, 1), 1)])); // Arf 1
        assert!(h.is_hyperbolic());
        assert!(!a.is_hyperbolic());
        assert_eq!(h, WittClass::zero());
        assert_eq!(a.anisotropic_dim(), 2);
        // self-inverse: a + a = 0  ⟺  A ⊕ A ≅ H ⊕ H
        assert_eq!(a.add(&a), WittClass::zero());
        assert_eq!(a.add(&h), a); // identity
    }

    #[test]
    fn group_law_is_xor_of_arf() {
        let h = WittClass { arf: 0 };
        let a = WittClass { arf: 1 };
        assert_eq!(a.add(&a), h);
        assert_eq!(a.add(&h), a);
        assert_eq!(h.add(&h), h);
        // direct_sum of the underlying forms agrees with the abstract group law.
        let am = metric(&[1, 1], &[((0, 1), 1)]);
        let combined = WittClass::from_metric(&am.direct_sum(&am));
        assert_eq!(combined, a.add(&a)); // both are 0
    }

    #[test]
    fn witt_class_over_f4() {
        // From arf.rs's F₄ facts: q=[2,2],b=1 is anisotropic (Arf 1); q=[2,3],b=1
        // is hyperbolic-class (Arf 0). Their Witt classes add to the nonzero class.
        let aniso = WittClass::from_metric(&metric(&[2, 2], &[((0, 1), 1)]));
        let split = WittClass::from_metric(&metric(&[2, 3], &[((0, 1), 1)]));
        assert_eq!(aniso.arf, 1);
        assert_eq!(split.arf, 0);
        assert_eq!(aniso.add(&split), aniso);
    }
}
