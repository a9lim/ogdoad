//! Normal-play Hackenbush.
//!
//! A Hackenbush position is a graph of coloured edges standing on the *ground*
//! (vertex `0`). Players alternately delete an edge of their colour (Left:
//! **blue**, Right: **red**, either player: **green**); any edge no longer
//! connected to the ground falls off. Last player to move wins (normal play).
//!
//! [`Hackenbush::to_game`] evaluates a position by move-and-prune recursion.
//! Restricted colour classes admit more specific interpretations:
//!
//! | position             | value class        | API                          |
//! |----------------------|--------------------|------------------------------|
//! | blue / red only      | surreal **number** | [`Hackenbush::value`]        |
//! | blue–red string      | dyadic surreal     | = its **sign expansion**     |
//! | green only           | **nimber** (Nim)   | [`Hackenbush::grundy`]       |
//! | mixed                | general partizan   | [`Hackenbush::to_game`]      |
//!
//! A blue–red *string* is exactly an [ordinal sum](crate::games::Game::ordinal_sum)
//! of single edges, and Berlekamp's rule says its value's
//! [sign expansion](crate::scalar::Surreal::sign_expansion) is the colour
//! sequence read from the ground up (blue `+`, red `−`). A green *string* of `n`
//! edges is the Nim heap `*n`.

use crate::games::Game;
use crate::scalar::Surreal;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

/// An edge colour: who may remove it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Color {
    /// Left's edge.
    Blue,
    /// Right's edge.
    Red,
    /// Either player's edge (impartial).
    Green,
}

/// A Hackenbush position: undirected coloured edges over the ground vertex `0`.
#[derive(Clone, Debug)]
pub struct Hackenbush {
    edges: Vec<(usize, usize, Color)>,
}

impl Hackenbush {
    /// A position from an explicit edge list `(u, v, colour)`. Vertex `0` is the
    /// ground. Edges not connected to the ground (directly or through other edges)
    /// are pruned immediately, as they fall off before play begins.
    pub fn new(edges: Vec<(usize, usize, Color)>) -> Hackenbush {
        let raw = Hackenbush { edges };
        let grounded = raw.grounded();
        Hackenbush {
            edges: raw
                .edges
                .into_iter()
                .filter(|&(u, v, _)| grounded.contains(&u) && grounded.contains(&v))
                .collect(),
        }
    }

    /// A **stalk** rooted at the ground: `0 — 1 — 2 — …`, edge `i` joining
    /// vertices `i` and `i+1` with colour `colors[i]`.
    pub fn string(colors: &[Color]) -> Hackenbush {
        let edges = colors
            .iter()
            .enumerate()
            .map(|(i, &c)| (i, i + 1, c))
            .collect();
        Hackenbush { edges }
    }

    /// The edges `(u, v, colour)`.
    pub fn edges(&self) -> &[(usize, usize, Color)] {
        &self.edges
    }

    /// The vertices connected to the ground (`0`) through the current edges.
    fn grounded(&self) -> HashSet<usize> {
        let mut adjacency: HashMap<usize, Vec<usize>> = HashMap::new();
        for &(u, v, _) in &self.edges {
            adjacency.entry(u).or_default().push(v);
            adjacency.entry(v).or_default().push(u);
        }
        let mut reach = HashSet::new();
        reach.insert(0usize);
        let mut queue = VecDeque::from([0usize]);
        while let Some(vertex) = queue.pop_front() {
            if let Some(neighbors) = adjacency.get(&vertex) {
                for &neighbor in neighbors {
                    if reach.insert(neighbor) {
                        queue.push_back(neighbor);
                    }
                }
            }
        }
        reach
    }

    /// Remove edge `i`, then drop every edge that has fallen off the ground.
    fn remove_edge(&self, i: usize) -> Hackenbush {
        let mut edges = self.edges.clone();
        edges.remove(i);
        let pruned = Hackenbush { edges };
        let grounded = pruned.grounded();
        Hackenbush {
            edges: pruned
                .edges
                .into_iter()
                .filter(|&(u, v, _)| grounded.contains(&u) && grounded.contains(&v))
                .collect(),
        }
    }

    /// The partizan game value, as a [`Game`] — the universal evaluator. Left
    /// options are the blue/green deletions, Right options the red/green ones,
    /// each followed by pruning.
    pub fn to_game(&self) -> Game {
        fn visit(
            position: &Hackenbush,
            memo: &mut HashMap<Vec<(usize, usize, Color)>, Game>,
        ) -> Game {
            if let Some(game) = memo.get(&position.edges) {
                return game.clone();
            }
            let mut left = Vec::new();
            let mut right = Vec::new();
            for (i, &(_, _, color)) in position.edges.iter().enumerate() {
                let sub = visit(&position.remove_edge(i), memo);
                match color {
                    Color::Blue => left.push(sub),
                    Color::Red => right.push(sub),
                    Color::Green => {
                        left.push(sub.clone());
                        right.push(sub);
                    }
                }
            }
            let game = Game::new(left, right);
            memo.insert(position.edges.clone(), game.clone());
            game
        }
        visit(self, &mut HashMap::new())
    }

    /// The **surreal number** value — `Some` exactly when the position's value is
    /// a number (every blue/red position is). `None` for values carrying an
    /// infinitesimal or switch (green edges, `↑`, `⋆`, …).
    pub fn value(&self) -> Option<Surreal> {
        self.to_game().number_value()
    }

    /// The **Sprague–Grundy (nim) value** — `Some` only for an all-green
    /// (impartial) position, where Hackenbush *is* Nim. `None` if any edge is
    /// blue or red.
    pub fn grundy(&self) -> Option<u128> {
        if self.edges.iter().any(|&(_, _, c)| c != Color::Green) {
            return None;
        }
        Some(self.grundy_green())
    }

    fn grundy_green(&self) -> u128 {
        fn visit(
            position: &Hackenbush,
            memo: &mut HashMap<Vec<(usize, usize, Color)>, u128>,
        ) -> u128 {
            if let Some(&value) = memo.get(&position.edges) {
                return value;
            }
            let reachable: BTreeSet<u128> = (0..position.edges.len())
                .map(|i| visit(&position.remove_edge(i), memo))
                .collect();
            let mut value = 0u128;
            while reachable.contains(&value) {
                value += 1;
            }
            memo.insert(position.edges.clone(), value);
            value
        }
        visit(self, &mut HashMap::new())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{Rational, Surreal};

    fn blue_red(colors: &[Color]) -> Hackenbush {
        Hackenbush::string(colors)
    }

    #[test]
    fn blue_and_red_strings_are_integers() {
        use Color::*;
        for n in 0u128..5 {
            let blue = Hackenbush::string(&vec![Blue; n as usize]);
            assert_eq!(blue.value(), Some(Surreal::from_int(n as i128)));
            assert!(blue.to_game().eq(&Game::integer(n as i128)));

            let red = Hackenbush::string(&vec![Red; n as usize]);
            assert_eq!(red.value(), Some(Surreal::from_int(-(n as i128))));
        }
    }

    #[test]
    fn green_strings_are_nim_heaps() {
        use Color::*;
        for n in 0u128..6 {
            let g = Hackenbush::string(&vec![Green; n as usize]);
            assert_eq!(g.grundy(), Some(n)); // mex recursion = Nim heap n

            // The edge-removal recursion lands on the canonical Nim-heap value.
            assert!(g.to_game().eq(&Game::nim_heap(n)));
            if n >= 1 {
                assert_eq!(g.value(), None); // *n (n≥1) is not a number
            }
        }
    }

    #[test]
    fn blue_red_strings_are_their_sign_expansion() {
        use Color::*;
        // Berlekamp's rule: value's sign expansion = colours ground→top (B=+, R=−).
        let cases: [&[Color]; 6] = [
            &[Blue, Red],            // +−  = 1/2
            &[Blue, Red, Blue],      // +−+ = 3/4
            &[Red, Blue],            // −+  = −1/2
            &[Blue, Blue, Red],      // ++− = 3/2
            &[Blue, Red, Red],       // +−− = 1/4
            &[Red, Blue, Red, Blue], // −+−+ = −5/8
        ];
        for colors in cases {
            let signs: Vec<bool> = colors.iter().map(|&c| c == Blue).collect();
            let expected = Surreal::from_sign_expansion(&signs);
            assert_eq!(
                blue_red(colors).value(),
                Some(expected),
                "colors {:?}",
                colors
            );
        }
    }

    #[test]
    fn one_position_model_exposes_three_value_classes() {
        use Color::*;
        // surreal integer
        assert_eq!(
            Hackenbush::string(&[Blue, Blue, Blue]).value(),
            Some(Surreal::from_int(3))
        );
        // nimber
        assert_eq!(Hackenbush::string(&[Green, Green]).grundy(), Some(2));
        // dyadic surreal via sign expansion
        assert_eq!(
            Hackenbush::string(&[Blue, Red]).value(),
            Some(Surreal::from_rational(Rational::new(1, 2)))
        );
    }

    #[test]
    fn green_cycle_and_mixed() {
        use Color::*;
        // a green triangle hung from the ground by vertex 0. Removing a rim edge
        // leaves a 2-edge path (*2); removing the far edge leaves two separate
        // stalks (*1 ⊕ *1 = *0). So options are {*0, *2} and the triangle is
        // mex{0,2} = *1 — exactly the fusion principle (a green cycle = one edge).
        let triangle = Hackenbush::new(vec![(0, 1, Green), (1, 2, Green), (2, 0, Green)]);
        assert_eq!(triangle.grundy(), Some(1));

        // a blue edge atop a green edge is a partizan infinitesimal: not a number.
        let mixed = Hackenbush::new(vec![(0, 1, Green), (1, 2, Blue)]);
        assert_eq!(mixed.value(), None);
        assert!(mixed.grundy().is_none()); // has a coloured edge
    }

    #[test]
    fn branched_blue_red_position_matches_an_independent_ordinal_sum_reconstruction() {
        use Color::*;
        // A genuinely BRANCHED (non-string) blue/red position: a single base edge
        // ground--Blue-->1, then two independent branches fork off vertex 1:
        // 1--Red-->2 and 1--Blue-->3. All existing blue/red oracle tests are single
        // *strings* (`blue_and_red_strings_are_integers`,
        // `blue_red_strings_are_their_sign_expansion`); this is the one branched
        // case, with a value derivable *without going through `to_game()`/`value()`
        // at all*.
        //
        // Ground truth: while the base edge survives, the two branches never
        // interact (an edge deletion in one cannot affect the other or the base),
        // so together they are the DISJUNCTIVE SUM of two lone edges evaluated as
        // if vertex 1 were its own ground: value(1--Red-->2 alone) +
        // value(1--Blue-->3 alone) = (-1) + 1 = 0. The instant the base edge is cut,
        // both branches fall off together — exactly the ORDINAL SUM `base : branches`
        // (the module doc's "Hackenbush strings are ordinal sums of single edges"
        // generalizes to any grounded branch point, not just a bare string). So the
        // predicted value is `Game::integer(1).ordinal_sum(&(branch_a + branch_b))`,
        // built entirely from `Game::integer`/`ordinal_sum`/`add`, never touching
        // `Hackenbush::to_game()`.
        let branched = Hackenbush::new(vec![(0, 1, Blue), (1, 2, Red), (1, 3, Blue)]);
        let branch_a = Hackenbush::string(&[Red]).to_game(); // 1--Red-->2, evaluated alone
        let branch_b = Hackenbush::string(&[Blue]).to_game(); // 1--Blue-->3, evaluated alone
        let predicted = Game::integer(1).ordinal_sum(&branch_a.add(&branch_b));

        assert!(
            branched.to_game().eq(&predicted),
            "branched Hackenbush value {} should match the independent ordinal-sum \
             reconstruction {}",
            branched.to_game().display(),
            predicted.display()
        );

        // Asserted via the surreal round-trip: value() -> Surreal -> from_surreal
        // should land back on (a value equal to) the same independently derived
        // canonical game.
        let value = branched
            .value()
            .expect("blue/red-only position is a number");
        assert_eq!(value, Surreal::from_int(1));
        let rebuilt = Game::from_surreal(&value).expect("integer values are dyadic");
        assert!(rebuilt.canonical().structural_eq(&predicted.canonical()));
    }

    #[test]
    fn floating_edges_are_pruned_at_construction() {
        use Color::*;
        // A floating blue edge (vertices 1-2) with no path to the ground (vertex 0).
        // It must fall off at construction; value should be 0 (no legal moves), not 1.
        let h = Hackenbush::new(vec![(1, 2, Blue)]);
        assert!(
            h.edges().is_empty(),
            "floating edge should be pruned from the position"
        );
        assert_eq!(
            h.value(),
            Some(Surreal::from_int(0)),
            "position with no grounded edges is the empty game, value 0"
        );
    }

    #[test]
    fn partially_floating_edges_are_pruned() {
        use Color::*;
        // Ground — vertex1 (blue); vertex1 — vertex2 — vertex3 (blue chain).
        // Also a floating red edge vertex4 — vertex5.
        // After pruning: the chain from the ground survives; the floating red edge does not.
        let h = Hackenbush::new(vec![
            (0, 1, Blue),
            (1, 2, Blue),
            (2, 3, Blue),
            (4, 5, Red), // floating
        ]);
        assert_eq!(
            h.edges().len(),
            3,
            "only the 3 grounded edges should survive"
        );
        // A 3-edge blue stalk = value 3.
        assert_eq!(h.value(), Some(Surreal::from_int(3)));
    }
}
