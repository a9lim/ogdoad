//! Relation and certificate record types: [`GameRelation`],
//! [`GameRelationCertificate`], and [`RelationSearchCertificate`].

use crate::games::partizan::Game;
use crate::linalg::integer::reduce_integer_vector;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
/// An integer relation among a fixed ordered tuple of game generators.
pub struct GameRelation {
    /// Coefficients in generator order.
    pub coeffs: Vec<i128>,
}

impl GameRelation {
    /// Construct a nonzero relation vector.
    ///
    /// # Panics
    ///
    /// Panics when every coefficient is zero.
    pub fn new(coeffs: Vec<i128>) -> Self {
        assert!(
            coeffs.iter().any(|&c| c != 0),
            "game relation must be nonzero"
        );
        GameRelation { coeffs }
    }
}

/// A stored witness for an accepted game-group relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GameRelationCertificate {
    /// The relation vector `Σ coeffs[i]·g_i = 0`.
    pub coeffs: Vec<i128>,
    /// Canonical value key of the evaluated relation. Accepted relations have
    /// the same value key as [`Game::zero`].
    pub value_key: String,
    /// Whether this row added new information modulo earlier accepted rows.
    pub independent: bool,
}

impl GameRelationCertificate {
    /// Python-visible rendering alias.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for GameRelationCertificate {
    /// Render the coefficient vector and its canonical zero-value certificate.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "GameRelationCertificate(coeffs={:?}, value_key={:?}, independent={})",
            self.coeffs, self.value_key, self.independent
        )
    }
}

/// Audit trail for bounded automatic relation discovery.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationSearchCertificate {
    /// Coefficient box `[-bound, bound]` used for automatic discovery (`0` for
    /// explicitly supplied relations).
    pub bound: i128,
    /// `true` iff the whole coefficient box was searched.
    pub exhaustive: bool,
    /// Number of nonzero candidates in the coefficient box, if it fit in `usize`.
    pub candidate_count: Option<usize>,
    /// Accepted relation rows, in the order they were imposed.
    pub relations: Vec<GameRelationCertificate>,
}

impl RelationSearchCertificate {
    /// Python-visible rendering alias.
    pub fn display(&self) -> String {
        self.to_string()
    }
}

impl fmt::Display for RelationSearchCertificate {
    /// One-line summary beginning with the completeness verdict.
    /// `exhaustive = false` means only singleton-coefficient candidates were
    /// tried and the full cross-generator coefficient box (`candidate_count`,
    /// when its size is known) went unexplored — the case
    /// `game_exterior_new_default_bound_is_incomplete_at_three_generators`
    /// pins this behavior for [`GameExterior::new`](super::GameExterior::new).
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = self.relations.len();
        match (self.exhaustive, self.candidate_count) {
            (true, Some(c)) => write!(
                f,
                "RelationSearchCertificate(exhaustive, bound={}, {c} candidate(s) searched, \
                 {n} relation(s) accepted)",
                self.bound
            ),
            (true, None) => write!(
                f,
                "RelationSearchCertificate(exhaustive, bound={}, {n} relation(s) accepted)",
                self.bound
            ),
            (false, Some(c)) => write!(
                f,
                "RelationSearchCertificate(INCOMPLETE — singleton-only search, bound={}, \
                 {c} candidate(s) unexplored, {n} relation(s) accepted)",
                self.bound
            ),
            (false, None) => write!(
                f,
                "RelationSearchCertificate(INCOMPLETE — box too large to count, bound={}, \
                 {n} relation(s) accepted)",
                self.bound
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Certificate helpers (pub(super) — only the lambda/clifford constructors call them)
// ---------------------------------------------------------------------------

pub(super) fn relation_search_certificate(
    gens: &[Game],
    bound: i128,
    exhaustive: bool,
    candidate_count: Option<usize>,
    relations: &[GameRelation],
    independent: bool,
) -> RelationSearchCertificate {
    RelationSearchCertificate {
        bound,
        exhaustive,
        candidate_count,
        relations: relation_certificates(gens, relations, independent),
    }
}

pub(super) fn relation_certificates(
    gens: &[Game],
    relations: &[GameRelation],
    trust_independent: bool,
) -> Vec<GameRelationCertificate> {
    let mut previous = Vec::new();
    relations
        .iter()
        .map(|rel| {
            let mut reduced = rel.coeffs.clone();
            reduce_integer_vector(&mut reduced, previous.clone());
            let independent = trust_independent || reduced.iter().any(|&c| c != 0);
            previous.push(rel.coeffs.clone());
            GameRelationCertificate {
                coeffs: rel.coeffs.clone(),
                value_key: eval_relation(gens, &rel.coeffs).canonical_string(),
                independent,
            }
        })
        .collect()
}

pub(super) fn eval_relation(gens: &[Game], coeffs: &[i128]) -> Game {
    let mut acc = Game::zero();
    for (g, &c) in gens.iter().zip(coeffs) {
        acc = acc.add(&g.times_int(c));
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn game_relation_certificate_render_byte_matches_py_repr() {
        // Keep the Rust and Python renderings byte-identical.
        let cert = GameRelationCertificate {
            coeffs: vec![1, -1],
            value_key: "0".to_string(),
            independent: true,
        };
        assert_eq!(
            cert.to_string(),
            "GameRelationCertificate(coeffs=[1, -1], value_key=\"0\", independent=true)"
        );
        assert_eq!(cert.display(), cert.to_string());
    }

    #[test]
    fn relation_search_certificate_incomplete_render_is_visibly_incomplete() {
        // Mirrors the shape of `game_exterior_new_default_bound_is_incomplete_at_three_generators`
        // (game_exterior/mod.rs): `GameExterior::new` on 3 generators falls back
        // to a singleton-only search at bound 3, candidate_count = 342.
        let cert = RelationSearchCertificate {
            bound: 3,
            exhaustive: false,
            candidate_count: Some(342),
            relations: vec![],
        };
        assert_eq!(
            cert.to_string(),
            "RelationSearchCertificate(INCOMPLETE — singleton-only search, bound=3, \
             342 candidate(s) unexplored, 0 relation(s) accepted)"
        );
        assert!(cert.to_string().contains("INCOMPLETE"));
        assert_eq!(cert.display(), cert.to_string());
    }

    #[test]
    fn relation_search_certificate_exhaustive_render_says_exhaustive() {
        let rel = GameRelationCertificate {
            coeffs: vec![1, 1, -1],
            value_key: "0".to_string(),
            independent: true,
        };
        let cert = RelationSearchCertificate {
            bound: 1,
            exhaustive: true,
            candidate_count: Some(8),
            relations: vec![rel],
        };
        assert_eq!(
            cert.to_string(),
            "RelationSearchCertificate(exhaustive, bound=1, 8 candidate(s) searched, \
             1 relation(s) accepted)"
        );
    }
}
