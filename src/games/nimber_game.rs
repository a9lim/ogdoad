//! Represented transfinite Nim heaps carried by ordinal Grundy values.
//!
//! [`NimberGame`] is the impartial analogue of
//! [`NumberGame`](crate::games::NumberGame): it stores the value of `⋆α`
//! instead of materializing its transfinite option set. Disjunctive sum is
//! ordinal nim-addition, negation is the identity, and Turning Corners is
//! ordinal nim-multiplication.
//!
//! The [`Ordinal`] backend represents a checked initial region of Conway's
//! nimbers, not the full algebraically closed class `On₂`. Addition is total on
//! represented values; multiplication returns `None` when it leaves the
//! supported Kummer tower.

use crate::games::Game;
use crate::scalar::Ordinal;
use std::cmp::Ordering;
use std::fmt;

/// A represented transfinite Nim heap `⋆α`, carried by its ordinal Grundy
/// value rather than an infinite option set.
#[derive(Clone, Debug, PartialEq)]
pub struct NimberGame {
    grundy: Ordinal,
}

impl NimberGame {
    /// Construct `⋆α` from its represented ordinal Grundy value. No option
    /// tree is built.
    pub fn from_ordinal(o: &Ordinal) -> NimberGame {
        NimberGame { grundy: o.clone() }
    }

    /// The finite Nim heap `⋆n`.
    pub fn nim_heap(n: u128) -> NimberGame {
        NimberGame {
            grundy: Ordinal::from_u128(n),
        }
    }

    /// The represented ordinal Grundy value. The game is a P-position iff this
    /// value is zero.
    pub fn grundy(&self) -> &Ordinal {
        &self.grundy
    }

    /// Disjunctive sum, computed by ordinal nim-addition. It is total on the
    /// represented CNF values (`⋆α + ⋆α = 0`, `⋆ω + ⋆1 = ⋆(ω+1)`).
    pub fn add(&self, other: &NimberGame) -> NimberGame {
        NimberGame {
            grundy: self.grundy.nim_add(&other.grundy),
        }
    }

    /// Negation, which is the identity for impartial games.
    pub fn neg(&self) -> NimberGame {
        self.clone()
    }

    /// Conway's Turning-Corners product, computed by ordinal nim-multiplication.
    /// Returns `None` when a Kummer carry lies outside the supported table or
    /// the result reaches the `ω^(ω^ω)` representation boundary. This is a
    /// separate game operation from disjunctive sum.
    pub fn turning_corners(&self, other: &NimberGame) -> Option<NimberGame> {
        self.grundy
            .nim_mul(&other.grundy)
            .map(|grundy| NimberGame { grundy })
    }

    /// The heap-size order: ordinal order on the stored Grundy values. This is
    /// not a field order on nimbers.
    // Inherent value-order, kept off `std::cmp::Ord` to mirror `Ordinal::cmp` and
    // the partial `Game` order (see AGENTS.md).
    #[allow(clippy::should_implement_trait)]
    pub fn cmp(&self, other: &NimberGame) -> Ordering {
        self.grundy.cmp(&other.grundy)
    }

    /// Convert a finite heap to the short-game engine. Returns `None` for a
    /// genuinely transfinite heap.
    pub fn to_finite_game(&self) -> Option<Game> {
        self.grundy.as_finite().map(Game::nim_heap)
    }
}

impl fmt::Display for NimberGame {
    /// Renders as the Ordinal's star-wrapped display (e.g. `*5`, `*(ω + 1)`).
    /// Delegates to [`Ordinal`]'s Display which already star-wraps ordinals.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.grundy)
    }
}

impl std::ops::Add for NimberGame {
    type Output = NimberGame;

    fn add(self, rhs: NimberGame) -> NimberGame {
        NimberGame::add(&self, &rhs)
    }
}

impl std::ops::Neg for NimberGame {
    type Output = NimberGame;

    fn neg(self) -> NimberGame {
        NimberGame::neg(&self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transfinite_bridge() {
        // ⋆ω: Grundy value ω, no finite option tree (mirror of the ω number game).
        let w = Ordinal::omega();
        let g = NimberGame::from_ordinal(&w);
        assert_eq!(g.grundy(), &w);
        assert!(g.to_finite_game().is_none());

        // disjunctive sum = nim-add; ⋆ω + ⋆ω = 0 (a P-position); neg is identity.
        assert!(g.add(&g).grundy().is_zero());
        assert_eq!(g.neg(), g);
        let one = NimberGame::nim_heap(1);
        assert_eq!(g.add(&one).grundy(), &w.nim_add(&Ordinal::from_u128(1))); // ω+1

        // the heap-size (ordinal) order: ⋆ω dominates every finite heap.
        assert_eq!(g.cmp(&NimberGame::nim_heap(1_000_000)), Ordering::Greater);

        // a finite heap bridges to the finite engine, value-for-value.
        let fin = NimberGame::nim_heap(2);
        assert!(fin.to_finite_game().unwrap().eq(&Game::nim_heap(2)));
    }

    #[test]
    fn turning_corners_is_nim_multiplication() {
        // Below ω^ω the product is the genuine On₂ nim-product. ⋆2 ⊗ ⋆3:
        let two = NimberGame::nim_heap(2);
        let three = NimberGame::nim_heap(3);
        let prod = two.turning_corners(&three).unwrap();
        assert_eq!(
            prod.grundy().as_finite(),
            Ordinal::from_u128(2)
                .nim_mul(&Ordinal::from_u128(3))
                .unwrap()
                .as_finite()
        );

        // Conway's ω³ = 2: ⋆ω ⊗ ⋆ω ⊗ ⋆ω = ⋆2, built from coin games.
        let w = NimberGame::from_ordinal(&Ordinal::omega());
        let w3 = w
            .turning_corners(&w)
            .and_then(|w2| w2.turning_corners(&w))
            .unwrap();
        assert_eq!(w3.grundy(), &Ordinal::from_u128(2));

        // The supported degree-5 generator satisfies
        // ⋆ω^ω ⊗ ⋆ω^ω = ⋆ω^(ω·2).
        let ww = NimberGame::from_ordinal(&Ordinal::omega_pow(Ordinal::omega()));
        assert_eq!(
            ww.turning_corners(&ww).unwrap().grundy(),
            &Ordinal::omega_pow(Ordinal::monomial(Ordinal::from_u128(1), 2))
        );
        // The non-scalar Kummer carry at ⋆ω^(ω^ω) is outside the representation.
        let www =
            NimberGame::from_ordinal(&Ordinal::omega_pow(Ordinal::omega_pow(Ordinal::omega())));
        assert!(www.turning_corners(&www).is_none());
    }

    #[test]
    fn additive_operator_traits_delegate_to_nim_arithmetic() {
        let two = NimberGame::nim_heap(2);
        let three = NimberGame::nim_heap(3);

        assert_eq!(
            (two.clone() + three.clone()).grundy(),
            &Ordinal::from_u128(2).nim_add(&Ordinal::from_u128(3))
        );
        assert_eq!(-two.clone(), two);
        assert_eq!(two.turning_corners(&three), Some(NimberGame::nim_heap(1)));
    }

    #[test]
    fn mirrors_the_number_game_on_the_shared_cnf() {
        // The structural point: NimberGame is to On₂ what NumberGame is to No, and
        // both read the same CNF tower. ω+1 here (XOR-merge) vs. there (+-merge):
        // the heaps add by nim-addition, never collapsing equal ω-powers the way
        // ordinary ordinal addition would (ω + ω = ω·2, but ⋆ω + ⋆ω = 0).
        let w = NimberGame::from_ordinal(&Ordinal::omega());
        assert!(w.add(&w).grundy().is_zero(), "⋆ω + ⋆ω = 0 (XOR, not ω·2)");
        let wp1 = w.add(&NimberGame::nim_heap(1));
        assert_eq!(format!("{:?}", wp1.grundy()), "*(ω + 1)");
    }
}
