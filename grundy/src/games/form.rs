//! `Form`: presented games — finite trees as built, and finite cyclic
//! graphs from guarded equations — with the loopy machinery: graph
//! materialization, retrograde classification, product-graph sums, stopper
//! gates, multiset bisimilarity, and self-contained equation-system display.

#![allow(clippy::too_many_lines)]

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::sync::Arc;

use ogdoad::games::{
    Game, LoopyMover, LoopyPartizanGraph, LoopyPartizanGraphError, LoopyPartizanOutcome,
    LoopyStopperStatus, LoopyWinner,
};

use super::super::error::{GrundyError, GrundyErrorKind, GrundyResult, Span};
use super::super::syntax::ast::{Mover, OutcomeCell, RelOp};

#[derive(Clone)]
pub enum GameElement {
    Finite(Game),
    Graph(GraphRef),
}

#[derive(Clone)]
pub struct GraphRef {
    graph: Arc<RegularGameGraph>,
    node: usize,
}

pub struct RegularGameGraph {
    name: String,
    equation_names: BTreeMap<usize, String>,
    nodes: Vec<RegularGameNode>,
    has_draw: Vec<bool>,
}

pub type GraphKey = (usize, usize);
pub type GraphPair = (GraphKey, GraphKey);

#[derive(Clone)]
pub struct RegularGameNode {
    left: Vec<RegularGameEdge>,
    right: Vec<RegularGameEdge>,
}

#[derive(Clone)]
pub enum RegularGameEdge {
    Finite(Game),
    Local(usize),
    External(GraphRef),
}

#[derive(Clone)]
pub enum SymbolicGame {
    Value(GameElement),
    Form {
        left: Vec<SymbolicGame>,
        right: Vec<SymbolicGame>,
    },
    SystemRef(usize),
}

/// A presented game value.
#[derive(Clone)]
pub struct FormV(pub GameElement);

impl FormV {
    /// A finite form as built.
    pub fn finite(game: Game) -> FormV {
        FormV(GameElement::Finite(game))
    }

    /// Multiset bisimilarity (`≡`).
    pub fn structural_eq(&self, other: &FormV) -> bool {
        game_element_regular_eq(&self.0, &other.0)
    }

    /// A deterministic display used to order distinct Forms inside keys.
    pub fn display_key(&self) -> String {
        display_game_element(&self.0)
    }
}

/// Names in scope when a Form is displayed: each global name with the Form
/// graph it binds, if it binds one. Display reuses source names only when
/// they cannot change meaning.
pub type FormNames = BTreeMap<String, Option<GraphRef>>;

fn graph_budget_error(budget: u128) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::GraphBudget,
        Span::point(0),
        format!("materialized game graph exceeds the node budget of {budget}"),
    )
    .with_hint("raise it with `:graph n`")
}

pub fn build_game_form(
    left: Vec<GameElement>,
    right: Vec<GameElement>,
    node_budget: u128,
) -> GrundyResult<GameElement> {
    if left
        .iter()
        .chain(&right)
        .all(|value| matches!(value, GameElement::Finite(_)))
    {
        let finite = |values: Vec<GameElement>| {
            values
                .into_iter()
                .map(|value| match value {
                    GameElement::Finite(game) => game,
                    GameElement::Graph(_) => unreachable!("checked above"),
                })
                .collect()
        };
        return Ok(GameElement::Finite(Game::new(finite(left), finite(right))));
    }
    materialize_regular_game(
        "",
        SymbolicGame::Form {
            left: left.into_iter().map(SymbolicGame::Value).collect(),
            right: right.into_iter().map(SymbolicGame::Value).collect(),
        },
        node_budget,
    )
}

pub fn materialize_regular_game(
    name: &str,
    root: SymbolicGame,
    node_budget: u128,
) -> GrundyResult<GameElement> {
    if matches!(root, SymbolicGame::SystemRef(_)) {
        return Err(unfounded_error(name));
    }
    if let SymbolicGame::Value(value) = root {
        return Ok(value);
    }
    let mut nodes = Vec::new();
    materialize_symbolic_node(&root, &mut nodes, node_budget)?;
    let finite = finite_regular_nodes(&nodes);
    if let Some(game) = finite[0].clone() {
        return Ok(GameElement::Finite(game));
    }
    for node in &mut nodes {
        for edge in node.left.iter_mut().chain(&mut node.right) {
            if let RegularGameEdge::Local(target) = edge {
                if let Some(game) = &finite[*target] {
                    *edge = RegularGameEdge::Finite(game.clone());
                }
            }
        }
    }
    let has_draw = classify_regular_nodes(&nodes, node_budget)?;
    Ok(GameElement::Graph(GraphRef {
        graph: Arc::new(RegularGameGraph {
            name: name.to_string(),
            equation_names: if name.is_empty() {
                BTreeMap::new()
            } else {
                BTreeMap::from([(0, name.to_string())])
            },
            nodes,
            has_draw,
        }),
        node: 0,
    }))
}

pub fn materialize_symbolic_node(
    value: &SymbolicGame,
    nodes: &mut Vec<RegularGameNode>,
    node_budget: u128,
) -> GrundyResult<usize> {
    let SymbolicGame::Form { left, right } = value else {
        return Err(GrundyError::new(
            GrundyErrorKind::Unfounded,
            Span::point(0),
            "an Element fixpoint must reduce to a brace constructor",
        ));
    };
    if nodes.len() as u128 >= node_budget {
        return Err(graph_budget_error(node_budget));
    }
    let index = nodes.len();
    nodes.push(RegularGameNode {
        left: Vec::new(),
        right: Vec::new(),
    });
    let left = left
        .iter()
        .map(|item| materialize_symbolic_edge(item, nodes, node_budget))
        .collect::<GrundyResult<_>>()?;
    let right = right
        .iter()
        .map(|item| materialize_symbolic_edge(item, nodes, node_budget))
        .collect::<GrundyResult<_>>()?;
    nodes[index] = RegularGameNode { left, right };
    Ok(index)
}

pub fn materialize_symbolic_edge(
    value: &SymbolicGame,
    nodes: &mut Vec<RegularGameNode>,
    node_budget: u128,
) -> GrundyResult<RegularGameEdge> {
    match value {
        SymbolicGame::SystemRef(node) => Ok(RegularGameEdge::Local(*node)),
        SymbolicGame::Value(GameElement::Finite(game)) => Ok(RegularGameEdge::Finite(game.clone())),
        SymbolicGame::Value(GameElement::Graph(reference)) => {
            Ok(RegularGameEdge::External(reference.clone()))
        }
        SymbolicGame::Form { .. } => {
            materialize_symbolic_node(value, nodes, node_budget).map(RegularGameEdge::Local)
        }
    }
}

pub fn materialize_regular_system(
    names: &[String],
    roots: Vec<SymbolicGame>,
    node_budget: u128,
) -> GrundyResult<Vec<GameElement>> {
    let mut nodes = Vec::new();
    let mut root_nodes = vec![None; roots.len()];
    for (equation, root) in roots.iter().enumerate() {
        match root {
            SymbolicGame::Form { .. } => {
                if nodes.len() as u128 >= node_budget {
                    return Err(graph_budget_error(node_budget));
                }
                root_nodes[equation] = Some(nodes.len());
                nodes.push(RegularGameNode {
                    left: Vec::new(),
                    right: Vec::new(),
                });
            }
            SymbolicGame::SystemRef(target) => {
                return Err(unfounded_system_error(&names[equation], &names[*target]));
            }
            SymbolicGame::Value(_) => {}
        }
    }

    for (equation, root) in roots.iter().enumerate() {
        let Some(node) = root_nodes[equation] else {
            continue;
        };
        let SymbolicGame::Form { left, right } = root else {
            unreachable!("root node was reserved only for a symbolic form")
        };
        let left = left
            .iter()
            .map(|item| materialize_system_edge(item, &roots, &root_nodes, &mut nodes, node_budget))
            .collect::<GrundyResult<_>>()?;
        let right = right
            .iter()
            .map(|item| materialize_system_edge(item, &roots, &root_nodes, &mut nodes, node_budget))
            .collect::<GrundyResult<_>>()?;
        nodes[node] = RegularGameNode { left, right };
    }

    if nodes.is_empty() {
        return Ok(roots
            .into_iter()
            .map(|root| match root {
                SymbolicGame::Value(value) => value,
                _ => unreachable!("node-bearing roots handled above"),
            })
            .collect());
    }

    let has_draw = classify_regular_nodes(&nodes, node_budget)?;
    let finite = finite_regular_nodes(&nodes);
    for node in &mut nodes {
        for edge in node.left.iter_mut().chain(&mut node.right) {
            if let RegularGameEdge::Local(target) = edge {
                if let Some(game) = &finite[*target] {
                    *edge = RegularGameEdge::Finite(game.clone());
                }
            }
        }
    }
    let equation_names = root_nodes
        .iter()
        .enumerate()
        .filter_map(|(equation, node)| node.map(|node| (node, names[equation].clone())))
        .collect();
    let graph = Arc::new(RegularGameGraph {
        name: names.first().cloned().unwrap_or_default(),
        equation_names,
        nodes,
        has_draw,
    });
    Ok(roots
        .into_iter()
        .enumerate()
        .map(|(equation, root)| match root {
            SymbolicGame::Value(value) => value,
            SymbolicGame::Form { .. } => {
                let node = root_nodes[equation].expect("form root node");
                finite[node].clone().map_or_else(
                    || {
                        GameElement::Graph(GraphRef {
                            graph: graph.clone(),
                            node,
                        })
                    },
                    GameElement::Finite,
                )
            }
            SymbolicGame::SystemRef(_) => unreachable!("rejected above"),
        })
        .collect())
}

fn materialize_system_edge(
    value: &SymbolicGame,
    roots: &[SymbolicGame],
    root_nodes: &[Option<usize>],
    nodes: &mut Vec<RegularGameNode>,
    node_budget: u128,
) -> GrundyResult<RegularGameEdge> {
    match value {
        SymbolicGame::SystemRef(equation) => match &roots[*equation] {
            SymbolicGame::Value(GameElement::Finite(game)) => {
                Ok(RegularGameEdge::Finite(game.clone()))
            }
            SymbolicGame::Value(GameElement::Graph(reference)) => {
                Ok(RegularGameEdge::External(reference.clone()))
            }
            SymbolicGame::Form { .. } => Ok(RegularGameEdge::Local(
                root_nodes[*equation].expect("form equation root"),
            )),
            SymbolicGame::SystemRef(_) => unreachable!("bare equation rejected above"),
        },
        SymbolicGame::Value(GameElement::Finite(game)) => Ok(RegularGameEdge::Finite(game.clone())),
        SymbolicGame::Value(GameElement::Graph(reference)) => {
            Ok(RegularGameEdge::External(reference.clone()))
        }
        SymbolicGame::Form { left, right } => {
            if nodes.len() as u128 >= node_budget {
                return Err(graph_budget_error(node_budget));
            }
            let node = nodes.len();
            nodes.push(RegularGameNode {
                left: Vec::new(),
                right: Vec::new(),
            });
            let left = left
                .iter()
                .map(|item| materialize_system_edge(item, roots, root_nodes, nodes, node_budget))
                .collect::<GrundyResult<_>>()?;
            let right = right
                .iter()
                .map(|item| materialize_system_edge(item, roots, root_nodes, nodes, node_budget))
                .collect::<GrundyResult<_>>()?;
            nodes[node] = RegularGameNode { left, right };
            Ok(RegularGameEdge::Local(node))
        }
    }
}

fn finite_regular_nodes(nodes: &[RegularGameNode]) -> Vec<Option<Game>> {
    let mut finite = vec![None; nodes.len()];
    let mut remaining = vec![0_usize; nodes.len()];
    let mut predecessors = vec![Vec::new(); nodes.len()];
    for (node, value) in nodes.iter().enumerate() {
        remaining[node] = value
            .left
            .iter()
            .chain(&value.right)
            .filter(|edge| matches!(edge, RegularGameEdge::Local(_)))
            .count();
        for target in value
            .left
            .iter()
            .chain(&value.right)
            .filter_map(|edge| match edge {
                RegularGameEdge::Local(target) => Some(*target),
                _ => None,
            })
        {
            predecessors[target].push(node);
        }
    }
    let mut ready = (0..nodes.len())
        .filter(|node| remaining[*node] == 0)
        .collect::<VecDeque<_>>();
    while let Some(node) = ready.pop_front() {
        let convert = |edges: &[RegularGameEdge]| {
            edges
                .iter()
                .map(|edge| match edge {
                    RegularGameEdge::Finite(game) => Some(game.clone()),
                    RegularGameEdge::Local(target) => finite[*target].clone(),
                    RegularGameEdge::External(_) => None,
                })
                .collect::<Option<Vec<_>>>()
        };
        if let (Some(left), Some(right)) = (convert(&nodes[node].left), convert(&nodes[node].right))
        {
            finite[node] = Some(Game::new(left, right));
        }
        for &source in &predecessors[node] {
            remaining[source] -= 1;
            if remaining[source] == 0 {
                ready.push_back(source);
            }
        }
    }
    finite
}

#[derive(Clone)]
pub enum ClassificationPosition {
    Current(usize),
    External(GraphRef),
    Finite(Game),
}

pub fn classify_regular_nodes(
    nodes: &[RegularGameNode],
    node_budget: u128,
) -> GrundyResult<Vec<bool>> {
    let mut positions = (0..nodes.len())
        .map(ClassificationPosition::Current)
        .collect::<Vec<_>>();
    let mut external = HashMap::new();
    let mut left = vec![Vec::new(); positions.len()];
    let mut right = vec![Vec::new(); positions.len()];
    let mut cursor = 0;
    while cursor < positions.len() {
        let (left_edges, right_edges) = match positions[cursor].clone() {
            ClassificationPosition::Current(node) => {
                (nodes[node].left.clone(), nodes[node].right.clone())
            }
            ClassificationPosition::External(reference) => {
                let node = &reference.graph.nodes[reference.node];
                let adapt = |edge: &RegularGameEdge| match edge {
                    RegularGameEdge::Local(node) => RegularGameEdge::External(GraphRef {
                        graph: reference.graph.clone(),
                        node: *node,
                    }),
                    edge => edge.clone(),
                };
                (
                    node.left.iter().map(adapt).collect(),
                    node.right.iter().map(adapt).collect(),
                )
            }
            ClassificationPosition::Finite(game) => (
                game.left()
                    .iter()
                    .cloned()
                    .map(RegularGameEdge::Finite)
                    .collect(),
                game.right()
                    .iter()
                    .cloned()
                    .map(RegularGameEdge::Finite)
                    .collect(),
            ),
        };
        left[cursor] = classification_edges(
            left_edges,
            node_budget,
            &mut positions,
            &mut left,
            &mut right,
            &mut external,
        )?;
        right[cursor] = classification_edges(
            right_edges,
            node_budget,
            &mut positions,
            &mut left,
            &mut right,
            &mut external,
        )?;
        cursor += 1;
    }
    let draw_set = LoopyPartizanGraph::new(left, right)
        .map_err(partizan_graph_error)?
        .draw_set()
        .into_iter()
        .collect::<HashSet<_>>();
    Ok((0..nodes.len())
        .map(|node| draw_set.contains(&node))
        .collect())
}

pub fn classification_edges(
    edges: Vec<RegularGameEdge>,
    node_budget: u128,
    positions: &mut Vec<ClassificationPosition>,
    left: &mut Vec<Vec<usize>>,
    right: &mut Vec<Vec<usize>>,
    external: &mut HashMap<GraphKey, usize>,
) -> GrundyResult<Vec<usize>> {
    edges
        .into_iter()
        .map(|edge| match edge {
            RegularGameEdge::Local(node) => Ok(node),
            RegularGameEdge::Finite(game) => {
                if positions.len() as u128 >= node_budget {
                    return Err(graph_budget_error(node_budget));
                }
                let index = positions.len();
                positions.push(ClassificationPosition::Finite(game));
                left.push(Vec::new());
                right.push(Vec::new());
                Ok(index)
            }
            RegularGameEdge::External(reference) => {
                let key = graph_key(&reference);
                if let Some(&index) = external.get(&key) {
                    return Ok(index);
                }
                if positions.len() as u128 >= node_budget {
                    return Err(graph_budget_error(node_budget));
                }
                let index = positions.len();
                external.insert(key, index);
                positions.push(ClassificationPosition::External(reference));
                left.push(Vec::new());
                right.push(Vec::new());
                Ok(index)
            }
        })
        .collect()
}

pub fn operational_partizan_graph(
    element: &GameElement,
    node_budget: u128,
) -> GrundyResult<LoopyPartizanGraph> {
    if let GameElement::Finite(game) = element {
        return LoopyPartizanGraph::from_game(game, node_budget).map_err(partizan_graph_error);
    }
    let GameElement::Graph(root) = element else {
        unreachable!()
    };
    if node_budget == 0 {
        return Err(graph_budget_error(node_budget));
    }

    let mut positions = vec![ClassificationPosition::External(root.clone())];
    let mut external = HashMap::from([(graph_key(root), 0_usize)]);
    let mut left = vec![Vec::new()];
    let mut right = vec![Vec::new()];
    let mut cursor = 0;
    while cursor < positions.len() {
        let (left_edges, right_edges) = match positions[cursor].clone() {
            ClassificationPosition::Current(_) => {
                unreachable!("operational flattening starts from an external graph reference")
            }
            ClassificationPosition::External(reference) => {
                let node = &reference.graph.nodes[reference.node];
                let adapt = |edge: &RegularGameEdge| match edge {
                    RegularGameEdge::Local(node) => RegularGameEdge::External(GraphRef {
                        graph: reference.graph.clone(),
                        node: *node,
                    }),
                    edge => edge.clone(),
                };
                (
                    node.left.iter().map(adapt).collect(),
                    node.right.iter().map(adapt).collect(),
                )
            }
            ClassificationPosition::Finite(game) => (
                game.left()
                    .iter()
                    .cloned()
                    .map(RegularGameEdge::Finite)
                    .collect(),
                game.right()
                    .iter()
                    .cloned()
                    .map(RegularGameEdge::Finite)
                    .collect(),
            ),
        };
        left[cursor] = operational_classification_edges(
            left_edges,
            node_budget,
            &mut positions,
            &mut left,
            &mut right,
            &mut external,
        )?;
        right[cursor] = operational_classification_edges(
            right_edges,
            node_budget,
            &mut positions,
            &mut left,
            &mut right,
            &mut external,
        )?;
        cursor += 1;
    }
    LoopyPartizanGraph::new(left, right).map_err(partizan_graph_error)
}

pub fn operational_classification_edges(
    edges: Vec<RegularGameEdge>,
    node_budget: u128,
    positions: &mut Vec<ClassificationPosition>,
    left: &mut Vec<Vec<usize>>,
    right: &mut Vec<Vec<usize>>,
    external: &mut HashMap<GraphKey, usize>,
) -> GrundyResult<Vec<usize>> {
    edges
        .into_iter()
        .map(|edge| match edge {
            RegularGameEdge::Local(_) => {
                unreachable!("external graph edges are adapted before flattening")
            }
            RegularGameEdge::Finite(game) => push_operational_position(
                ClassificationPosition::Finite(game),
                node_budget,
                positions,
                left,
                right,
            ),
            RegularGameEdge::External(reference) => {
                let key = graph_key(&reference);
                if let Some(&index) = external.get(&key) {
                    Ok(index)
                } else {
                    let index = push_operational_position(
                        ClassificationPosition::External(reference),
                        node_budget,
                        positions,
                        left,
                        right,
                    )?;
                    external.insert(key, index);
                    Ok(index)
                }
            }
        })
        .collect()
}

pub fn push_operational_position(
    position: ClassificationPosition,
    node_budget: u128,
    positions: &mut Vec<ClassificationPosition>,
    left: &mut Vec<Vec<usize>>,
    right: &mut Vec<Vec<usize>>,
) -> GrundyResult<usize> {
    if positions.len() as u128 >= node_budget {
        return Err(graph_budget_error(node_budget));
    }
    let index = positions.len();
    positions.push(position);
    left.push(Vec::new());
    right.push(Vec::new());
    Ok(index)
}

pub fn partizan_game_element(graph: LoopyPartizanGraph) -> GameElement {
    // Recover every well-founded subgraph as a finite `Game`. Besides keeping
    // finite results finite, this preserves literal recognition at exits from a
    // cyclic component (`-ones` should contain `-1`, not its expanded node DAG).
    let mut finite = vec![None; graph.node_count()];
    let mut remaining = vec![0_usize; graph.node_count()];
    let mut predecessors = vec![Vec::new(); graph.node_count()];
    // Index-parallel walk over three per-node arrays (`remaining`,
    // `predecessors`, and the graph's option lists); the range loop reads clearer.
    #[allow(clippy::needless_range_loop)]
    for node in 0..graph.node_count() {
        remaining[node] = graph.left()[node].len() + graph.right()[node].len();
        for &target in graph.left()[node].iter().chain(&graph.right()[node]) {
            predecessors[target].push(node);
        }
    }
    let mut ready = (0..graph.node_count())
        .filter(|node| remaining[*node] == 0)
        .collect::<VecDeque<_>>();
    while let Some(node) = ready.pop_front() {
        finite[node] = Some(Game::new(
            graph.left()[node]
                .iter()
                .map(|target| {
                    finite[*target]
                        .clone()
                        .expect("retrograde finite left target")
                })
                .collect(),
            graph.right()[node]
                .iter()
                .map(|target| {
                    finite[*target]
                        .clone()
                        .expect("retrograde finite right target")
                })
                .collect(),
        ));
        for &source in &predecessors[node] {
            remaining[source] -= 1;
            if remaining[source] == 0 {
                ready.push_back(source);
            }
        }
    }
    if let Some(root) = finite[0].clone() {
        return GameElement::Finite(root);
    }

    let has_draw = graph
        .outcomes()
        .iter()
        .map(|outcome| outcome.has_draw())
        .collect();
    let nodes = graph
        .left()
        .iter()
        .zip(graph.right())
        .map(|(left, right)| RegularGameNode {
            left: left
                .iter()
                .map(|target| {
                    finite[*target]
                        .clone()
                        .map_or_else(|| RegularGameEdge::Local(*target), RegularGameEdge::Finite)
                })
                .collect(),
            right: right
                .iter()
                .map(|target| {
                    finite[*target]
                        .clone()
                        .map_or_else(|| RegularGameEdge::Local(*target), RegularGameEdge::Finite)
                })
                .collect(),
        })
        .collect();
    GameElement::Graph(GraphRef {
        graph: Arc::new(RegularGameGraph {
            name: String::new(),
            equation_names: BTreeMap::new(),
            nodes,
            has_draw,
        }),
        node: 0,
    })
}

pub fn negate_game_element(element: GameElement, node_budget: u128) -> GrundyResult<GameElement> {
    match element {
        GameElement::Finite(game) => {
            LoopyPartizanGraph::from_game(&game, node_budget).map_err(partizan_graph_error)?;
            Ok(GameElement::Finite(game.neg()))
        }
        graph @ GameElement::Graph(_) => Ok(partizan_game_element(
            operational_partizan_graph(&graph, node_budget)?.neg(),
        )),
    }
}

pub fn add_game_elements(
    lhs: GameElement,
    rhs: GameElement,
    subtract: bool,
    node_budget: u128,
) -> GrundyResult<GameElement> {
    if let (GameElement::Finite(lhs), GameElement::Finite(rhs)) = (&lhs, &rhs) {
        return Ok(GameElement::Finite(if subtract {
            lhs.add(&rhs.neg())
        } else {
            lhs.add(rhs)
        }));
    }
    let lhs = operational_partizan_graph(&lhs, node_budget)?;
    let mut rhs = operational_partizan_graph(&rhs, node_budget)?;
    if subtract {
        rhs = rhs.neg();
    }
    lhs.sum(0, &rhs, 0, node_budget)
        .map(partizan_game_element)
        .map_err(partizan_graph_error)
}

pub fn game_difference_outcome(
    lhs: &GameElement,
    rhs: &GameElement,
    node_budget: u128,
) -> GrundyResult<LoopyPartizanOutcome> {
    let lhs = operational_partizan_graph(lhs, node_budget)?;
    let rhs = operational_partizan_graph(rhs, node_budget)?.neg();
    lhs.sum(0, &rhs, 0, node_budget)
        .and_then(|difference| difference.outcome_pair(0))
        .map_err(partizan_graph_error)
}

pub fn outcome_cell(outcome: LoopyPartizanOutcome) -> OutcomeCell {
    let mover = |winner: LoopyWinner| match winner {
        LoopyWinner::Left => Mover::Left,
        LoopyWinner::Right => Mover::Right,
        LoopyWinner::Draw => Mover::Draw,
    };
    OutcomeCell {
        left_first: mover(outcome.left_to_move),
        right_first: mover(outcome.right_to_move),
    }
}

pub fn project_stopper_outcome(outcome: LoopyPartizanOutcome) -> RelOp {
    // Standard stopper-order projection: Siegel, Combinatorial Game Theory,
    // GSM 146, Def. VI.1.8 p. 284 (survival) and Thm. VI.2.1 p. 290.
    let cell = outcome_cell(outcome);
    match (cell.left_first, cell.right_first) {
        (Mover::Left, Mover::Left | Mover::Draw) => RelOp::Gt,
        (Mover::Left, Mover::Right) => RelOp::Fuzzy,
        (Mover::Right | Mover::Draw, Mover::Left) | (Mover::Right | Mover::Draw, Mover::Draw) => {
            RelOp::Eq
        }
        (Mover::Draw | Mover::Right, Mover::Right) => RelOp::Lt,
    }
}

pub fn ensure_game_stopper(
    operand: &str,
    element: &GameElement,
    node_budget: u128,
) -> GrundyResult<()> {
    let graph = operational_partizan_graph(element, node_budget)?;
    match graph.stopper_status(0).map_err(partizan_graph_error)? {
        LoopyStopperStatus::Stopper => Ok(()),
        LoopyStopperStatus::NonStopper { witness } => Err(loopy_error(&format!(
            "value relation requires stopper operands; {operand} operand has alternating cycle {}",
            render_stopper_witness(&witness.cycle)
        ))),
    }
}

pub fn game_element_is_stopper(element: &GameElement, node_budget: u128) -> GrundyResult<bool> {
    operational_partizan_graph(element, node_budget)?
        .is_stopper(0)
        .map_err(partizan_graph_error)
}

pub fn render_stopper_witness(cycle: &[ogdoad::games::LoopyTurnState]) -> String {
    cycle
        .iter()
        .map(|state| {
            let mover = match state.mover {
                LoopyMover::Left => 'L',
                LoopyMover::Right => 'R',
            };
            format!("{}:{mover}", state.node)
        })
        .collect::<Vec<_>>()
        .join("→")
}

pub fn partizan_graph_error(error: LoopyPartizanGraphError) -> GrundyError {
    match error {
        LoopyPartizanGraphError::NodeBudgetExceeded { budget } => graph_budget_error(budget),
        other => GrundyError::new(
            GrundyErrorKind::Domain,
            Span::point(0),
            format!("invalid materialized game graph: {other}"),
        ),
    }
}

pub fn game_options(element: &GameElement, left: bool) -> Vec<GameElement> {
    match element {
        GameElement::Finite(game) => {
            let options = if left { game.left() } else { game.right() };
            options.iter().cloned().map(GameElement::Finite).collect()
        }
        GameElement::Graph(reference) => {
            let node = &reference.graph.nodes[reference.node];
            let edges = if left { &node.left } else { &node.right };
            edges
                .iter()
                .map(|edge| match edge {
                    RegularGameEdge::Finite(game) => GameElement::Finite(game.clone()),
                    RegularGameEdge::Local(node) => GameElement::Graph(GraphRef {
                        graph: reference.graph.clone(),
                        node: *node,
                    }),
                    RegularGameEdge::External(reference) => GameElement::Graph(reference.clone()),
                })
                .collect()
        }
    }
}

pub fn unfounded_error(name: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Unfounded,
        Span::point(0),
        format!("Element fixpoint `{name}` is not guarded by a brace constructor"),
    )
}

pub fn unfounded_system_error(equation: &str, name: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Unfounded,
        Span::point(0),
        format!(
            "Element equation `{equation}` has unguarded system name `{name}` outside a brace constructor"
        ),
    )
}

pub fn loopy_error(message: &str) -> GrundyError {
    GrundyError::new(GrundyErrorKind::Loopy, Span::point(0), message)
}

type DisplayReachability = (
    Vec<GraphKey>,
    HashMap<GraphKey, Vec<GraphKey>>,
    HashMap<GraphKey, GraphRef>,
);

pub fn display_game_element(element: &GameElement) -> String {
    display_game_element_in_env(element, &BTreeMap::new())
}

pub fn display_game_element_in_env(element: &GameElement, env: &FormNames) -> String {
    match element {
        GameElement::Finite(game) => display_game(game),
        GameElement::Graph(reference) => display_composite_graph(reference, env),
    }
}

pub fn display_composite_graph(reference: &GraphRef, env: &FormNames) -> String {
    let (discovery, successors, references) = reachable_display_graph(reference);
    let (components, component_of) = display_components(&discovery, &successors);
    let cyclic_components = components
        .iter()
        .enumerate()
        .filter_map(|(component, nodes)| {
            (nodes.len() > 1
                || successors
                    .get(&nodes[0])
                    .is_some_and(|targets| targets.contains(&nodes[0])))
            .then_some(component)
        })
        .collect::<HashSet<_>>();
    let anchor_keys = collect_display_anchor_keys(reference);
    let anchored = discovery
        .iter()
        .filter(|key| anchor_keys.contains(key))
        .filter(|key| cyclic_components.contains(&component_of[key]))
        .map(|key| references[key].clone())
        .collect::<Vec<_>>();
    if anchored.is_empty() {
        return display_graph_node(reference, &HashMap::new(), true, &mut HashSet::new());
    }

    let mut collision = env.keys().cloned().collect::<HashSet<_>>();
    let mut preferred = vec![None; anchored.len()];
    let mut exact = HashMap::new();
    for (name, value) in env {
        if let Some(bound) = value {
            exact
                .entry(graph_key(bound))
                .or_insert_with(|| name.clone());
        }
    }
    for (index, anchor) in anchored.iter().enumerate() {
        if let Some(name) = exact.get(&graph_key(anchor)) {
            preferred[index] = Some(name.clone());
        } else {
            preferred[index] = validated_anchor_name(anchor, env, false);
        }
    }
    if let Some(index) = anchored
        .iter()
        .position(|anchor| graph_key(anchor) == graph_key(reference))
    {
        if preferred[index].is_none() {
            preferred[index] = validated_anchor_name(reference, env, true);
        }
    }
    for name in preferred.iter().flatten() {
        collision.insert(name.clone());
    }

    let mut anchors = HashMap::new();
    let mut generated = 1_u128;
    for (index, anchor) in anchored.iter().enumerate() {
        let name = preferred[index].clone().unwrap_or_else(|| loop {
            let candidate = format!("g{generated}");
            generated += 1;
            if collision.insert(candidate.clone()) {
                break candidate;
            }
        });
        anchors.insert(graph_key(anchor), name);
    }

    let component_order =
        display_component_order(&discovery, &successors, &component_of, &cyclic_components);
    let groups = component_order
        .iter()
        .map(|component| {
            anchored
                .iter()
                .filter(|anchor| component_of[&graph_key(anchor)] == *component)
                .cloned()
                .collect::<Vec<_>>()
        })
        .filter(|group| !group.is_empty())
        .collect::<Vec<_>>();
    let parts = groups
        .iter()
        .flat_map(|group| group.iter())
        .map(|anchor| {
            format!(
                "{} =: {}",
                anchors[&graph_key(anchor)],
                display_graph_node(anchor, &anchors, true, &mut HashSet::new())
            )
        })
        .collect::<Vec<_>>();
    let root_key = graph_key(reference);
    let root_name = anchors.get(&root_key).cloned();
    if parts.len() == 1 && root_name.is_some() {
        return parts[0].clone();
    }
    if let Some(root_name) = root_name {
        let root_component = component_of[&root_key];
        // A system of several equations names its root explicitly.
        let _ = root_component;
        let mut body = parts;
        body.push(root_name);
        return format!("({})", body.join("; "));
    }
    let mut body = parts;
    body.push(display_graph_node(
        reference,
        &anchors,
        true,
        &mut HashSet::new(),
    ));
    format!("({})", body.join("; "))
}

fn validated_anchor_name(
    root: &GraphRef,
    env: &FormNames,
    allow_graph_name: bool,
) -> Option<String> {
    let provenance = root
        .graph
        .equation_names
        .get(&root.node)
        .filter(|name| !name.is_empty())
        .or_else(|| {
            (allow_graph_name && !root.graph.name.is_empty()).then_some(&root.graph.name)
        })?;
    match env.get(provenance) {
        None => Some(provenance.clone()),
        Some(Some(bound)) if Arc::ptr_eq(&bound.graph, &root.graph) => Some(provenance.clone()),
        _ => None,
    }
}

fn reachable_display_graph(root: &GraphRef) -> DisplayReachability {
    let mut discovery = Vec::new();
    let mut successors = HashMap::new();
    let mut references = HashMap::new();
    let mut seen = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(reference) = stack.pop() {
        let key = graph_key(&reference);
        if !seen.insert(key) {
            continue;
        }
        discovery.push(key);
        references.insert(key, reference.clone());
        let targets = graph_reference_successors(&reference);
        successors.insert(key, targets.iter().map(graph_key).collect());
        stack.extend(targets.into_iter().rev());
    }
    (discovery, successors, references)
}

fn collect_display_anchor_keys(root: &GraphRef) -> HashSet<GraphKey> {
    let root_key = graph_key(root);
    let mut colors = HashMap::from([(root_key, 1_u8)]);
    let mut anchors = HashSet::new();
    let mut stack = vec![(
        root.clone(),
        graph_reference_successors_marked(root),
        0_usize,
    )];
    while !stack.is_empty() {
        let top = stack.len() - 1;
        if stack[top].2 == stack[top].1.len() {
            colors.insert(graph_key(&stack[top].0), 2);
            stack.pop();
            continue;
        }
        let (target, external) = stack[top].1[stack[top].2].clone();
        stack[top].2 += 1;
        let key = graph_key(&target);
        if external {
            anchors.insert(key);
        }
        match colors.get(&key).copied().unwrap_or(0) {
            0 => {
                colors.insert(key, 1);
                let successors = graph_reference_successors_marked(&target);
                stack.push((target, successors, 0));
            }
            1 => {
                anchors.insert(key);
            }
            _ => {}
        }
    }

    let mut seen = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(reference) = stack.pop() {
        let key = graph_key(&reference);
        if !seen.insert(key) {
            continue;
        }
        if reference.graph.equation_names.len() > 1
            && reference.graph.equation_names.contains_key(&reference.node)
        {
            anchors.insert(key);
        }
        stack.extend(graph_reference_successors(&reference).into_iter().rev());
    }
    anchors
}

fn display_components(
    discovery: &[GraphKey],
    successors: &HashMap<GraphKey, Vec<GraphKey>>,
) -> (Vec<Vec<GraphKey>>, HashMap<GraphKey, usize>) {
    let mut seen = HashSet::new();
    let mut finish = Vec::new();
    for &start in discovery {
        if !seen.insert(start) {
            continue;
        }
        let mut stack = vec![(start, 0_usize)];
        while let Some((node, next)) = stack.last_mut() {
            let targets = &successors[node];
            if *next == targets.len() {
                finish.push(*node);
                stack.pop();
            } else {
                let target = targets[*next];
                *next += 1;
                if seen.insert(target) {
                    stack.push((target, 0));
                }
            }
        }
    }
    let mut reverse = HashMap::<GraphKey, Vec<GraphKey>>::new();
    for (&source, targets) in successors {
        reverse.entry(source).or_default();
        for &target in targets {
            reverse.entry(target).or_default().push(source);
        }
    }
    let mut component_of = HashMap::new();
    let mut components = Vec::new();
    for start in finish.into_iter().rev() {
        if component_of.contains_key(&start) {
            continue;
        }
        let component = components.len();
        let mut nodes = Vec::new();
        let mut stack = vec![start];
        component_of.insert(start, component);
        while let Some(node) = stack.pop() {
            nodes.push(node);
            for &target in &reverse[&node] {
                if let std::collections::hash_map::Entry::Vacant(entry) = component_of.entry(target)
                {
                    entry.insert(component);
                    stack.push(target);
                }
            }
        }
        components.push(nodes);
    }
    (components, component_of)
}

fn display_component_order(
    discovery: &[GraphKey],
    successors: &HashMap<GraphKey, Vec<GraphKey>>,
    component_of: &HashMap<GraphKey, usize>,
    cyclic: &HashSet<usize>,
) -> Vec<usize> {
    let mut dependencies = cyclic
        .iter()
        .map(|component| (*component, HashSet::new()))
        .collect::<HashMap<_, _>>();
    for &source in discovery {
        let source_component = component_of[&source];
        if !cyclic.contains(&source_component) {
            continue;
        }
        let mut seen = HashSet::new();
        let mut stack = successors[&source].clone();
        while let Some(target) = stack.pop() {
            let target_component = component_of[&target];
            if cyclic.contains(&target_component) {
                if target_component != source_component {
                    dependencies
                        .get_mut(&source_component)
                        .expect("cyclic source component")
                        .insert(target_component);
                }
            } else if seen.insert(target) {
                stack.extend(successors[&target].iter().copied());
            }
        }
    }
    let mut consumers = HashMap::<usize, Vec<usize>>::new();
    for (&consumer, deps) in &dependencies {
        for &dependency in deps {
            consumers.entry(dependency).or_default().push(consumer);
        }
    }
    let rank = discovery
        .iter()
        .enumerate()
        .fold(HashMap::new(), |mut rank, (index, node)| {
            rank.entry(component_of[node]).or_insert(index);
            rank
        });
    let mut remaining = dependencies
        .iter()
        .map(|(&component, deps)| (component, deps.len()))
        .collect::<HashMap<_, _>>();
    let mut order = Vec::new();
    while order.len() < cyclic.len() {
        let next = remaining
            .iter()
            .filter(|(component, count)| **count == 0 && !order.contains(*component))
            .min_by_key(|(component, _)| rank[*component])
            .map(|(component, _)| *component);
        let Some(component) = next else {
            break;
        };
        order.push(component);
        for &consumer in consumers.get(&component).into_iter().flatten() {
            remaining.entry(consumer).and_modify(|count| *count -= 1);
        }
    }
    order
}

pub fn graph_reference_successors(reference: &GraphRef) -> Vec<GraphRef> {
    graph_reference_successors_marked(reference)
        .into_iter()
        .map(|(target, _)| target)
        .collect()
}

fn graph_reference_successors_marked(reference: &GraphRef) -> Vec<(GraphRef, bool)> {
    let node = &reference.graph.nodes[reference.node];
    node.left
        .iter()
        .chain(&node.right)
        .filter_map(|edge| match edge {
            RegularGameEdge::Finite(_) => None,
            RegularGameEdge::Local(node) => Some((
                GraphRef {
                    graph: reference.graph.clone(),
                    node: *node,
                },
                false,
            )),
            RegularGameEdge::External(reference) => Some((reference.clone(), true)),
        })
        .collect()
}

pub fn display_graph_node(
    reference: &GraphRef,
    anchors: &HashMap<GraphKey, String>,
    expand_root: bool,
    active: &mut HashSet<GraphKey>,
) -> String {
    let key = graph_key(reference);
    if !expand_root {
        if let Some(name) = anchors.get(&key) {
            return name.clone();
        }
    }
    if !active.insert(key) {
        return anchors
            .get(&key)
            .cloned()
            .unwrap_or_else(|| format!("g{}", reference.node + 1));
    }
    let node = &reference.graph.nodes[reference.node];
    let left = node
        .left
        .iter()
        .map(|edge| display_regular_edge(reference, edge, anchors, active))
        .collect::<Vec<_>>()
        .join(", ");
    let right = node
        .right
        .iter()
        .map(|edge| display_regular_edge(reference, edge, anchors, active))
        .collect::<Vec<_>>()
        .join(", ");
    active.remove(&key);
    display_raw_game_form(&left, &right)
}

pub fn display_regular_edge(
    owner: &GraphRef,
    edge: &RegularGameEdge,
    anchors: &HashMap<GraphKey, String>,
    active: &mut HashSet<GraphKey>,
) -> String {
    match edge {
        RegularGameEdge::Finite(game) => display_game(game),
        RegularGameEdge::Local(node) => display_graph_node(
            &GraphRef {
                graph: owner.graph.clone(),
                node: *node,
            },
            anchors,
            false,
            active,
        ),
        RegularGameEdge::External(reference) => {
            display_graph_node(reference, anchors, false, active)
        }
    }
}

pub fn display_raw_game_form(left: &str, right: &str) -> String {
    match (left.is_empty(), right.is_empty()) {
        (true, true) => "{|}".to_string(),
        (false, true) => format!("{{{left} |}}"),
        (true, false) => format!("{{| {right}}}"),
        (false, false) => format!("{{{left} | {right}}}"),
    }
}

pub fn display_game(game: &Game) -> String {
    if let Some(integer) = structural_game_integer(game) {
        return integer.to_string();
    }
    if let Some(dyadic) = structural_game_dyadic(game) {
        return dyadic;
    }
    if let Some(nimber) = structural_game_nimber(game) {
        return format!("*{nimber}");
    }
    let up = Game::up();
    if game_structural_eq_multiset(game, &up) {
        return "up".to_string();
    }
    let down = up.neg();
    if game_structural_eq_multiset(game, &down) {
        return "down".to_string();
    }
    let left = game
        .left()
        .iter()
        .map(display_game)
        .collect::<Vec<_>>()
        .join(", ");
    let right = game
        .right()
        .iter()
        .map(display_game)
        .collect::<Vec<_>>()
        .join(", ");
    match (left.is_empty(), right.is_empty()) {
        (true, true) => "0".to_string(),
        (false, true) => format!("{{{left} |}}"),
        (true, false) => format!("{{| {right}}}"),
        (false, false) => format!("{{{left} | {right}}}"),
    }
}

pub fn structural_game_dyadic(game: &Game) -> Option<String> {
    let value = game.number_value()?;
    let (numerator, exponent) = value.as_dyadic()?;
    if exponent == 0 {
        return None;
    }
    let canonical = Game::from_surreal(&value)?;
    if !game_structural_eq_multiset(game, &canonical) {
        return None;
    }
    let shift = u32::try_from(exponent).ok()?;
    let denominator = 1_i128.checked_shl(shift)?;
    Some(format!("{numerator}/{denominator}"))
}

pub fn structural_game_integer(game: &Game) -> Option<i128> {
    if game.left().is_empty() && game.right().is_empty() {
        return Some(0);
    }
    if game.left().len() == 1 && game.right().is_empty() {
        let value = structural_game_integer(&game.left()[0])?;
        return (value >= 0).then(|| value.checked_add(1)).flatten();
    }
    if game.left().is_empty() && game.right().len() == 1 {
        let value = structural_game_integer(&game.right()[0])?;
        return (value <= 0).then(|| value.checked_sub(1)).flatten();
    }
    None
}

/// `n` when the form is presented exactly as `*n`: both sides list
/// `*0, …, *(n-1)` in that order. Order matters because `lefts` and `rights`
/// expose it.
pub fn structural_game_nimber(game: &Game) -> Option<u128> {
    fn visit(game: &Game, memo: &mut HashMap<usize, Option<u128>>) -> Option<u128> {
        if let Some(&known) = memo.get(&game.ptr_id()) {
            return known;
        }
        let n = game.left().len();
        let result = (game.right().len() == n
            && (0..n).all(|k| {
                visit(&game.left()[k], memo) == Some(k as u128)
                    && visit(&game.right()[k], memo) == Some(k as u128)
            }))
        .then_some(n as u128);
        memo.insert(game.ptr_id(), result);
        result
    }
    visit(game, &mut HashMap::new())
}

pub fn game_structural_eq_multiset(lhs: &Game, rhs: &Game) -> bool {
    game_structural_eq_multiset_inner(lhs, rhs, &mut HashMap::new())
}

pub fn game_structural_eq_multiset_inner(
    lhs: &Game,
    rhs: &Game,
    memo: &mut HashMap<(usize, usize), bool>,
) -> bool {
    if lhs.ptr_eq(rhs) {
        return true;
    }
    let key = (lhs.ptr_id(), rhs.ptr_id());
    if let Some(&equal) = memo.get(&key) {
        return equal;
    }
    let equal = lhs.left().len() == rhs.left().len()
        && lhs.right().len() == rhs.right().len()
        && perfect_matching(lhs.left().len(), |left, right| {
            game_structural_eq_multiset_inner(&lhs.left()[left], &rhs.left()[right], memo)
        })
        && perfect_matching(lhs.right().len(), |left, right| {
            game_structural_eq_multiset_inner(&lhs.right()[left], &rhs.right()[right], memo)
        });
    memo.insert(key, equal);
    memo.insert((key.1, key.0), equal);
    equal
}

pub fn perfect_matching(size: usize, mut compatible: impl FnMut(usize, usize) -> bool) -> bool {
    // Sides are multisets: equality is an existential bijection, not a sorted
    // presentation walk. The compatibility matrix preserves multiplicity, and
    // the augmenting-path matcher finds a bijection without canonicalizing.
    let edges = (0..size)
        .map(|left| {
            (0..size)
                .map(|right| compatible(left, right))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut matched_right = vec![None; size];
    (0..size).all(|left| augment_matching(left, &edges, &mut vec![false; size], &mut matched_right))
}

pub fn augment_matching(
    left: usize,
    edges: &[Vec<bool>],
    seen_right: &mut [bool],
    matched_right: &mut [Option<usize>],
) -> bool {
    for right in 0..edges.len() {
        if !edges[left][right] || seen_right[right] {
            continue;
        }
        seen_right[right] = true;
        if matched_right[right]
            .is_none_or(|previous| augment_matching(previous, edges, seen_right, matched_right))
        {
            matched_right[right] = Some(left);
            return true;
        }
    }
    false
}

pub fn game_element_has_draw(element: &GameElement) -> bool {
    match element {
        GameElement::Finite(_) => false,
        GameElement::Graph(reference) => reference.graph.has_draw[reference.node],
    }
}

#[derive(Clone, Default)]
pub struct RegularEqState {
    // Graph pairs are coinductive assumptions. A repeated pair closes one
    // synchronized descent path; the finite product of node sets bounds all
    // paths. Mixed graph/tree paths instead reject a repeated graph node,
    // because a genuinely cyclic unfolding cannot equal a finite tree.
    visited_pairs: HashSet<GraphPair>,
    mixed_path: HashSet<GraphKey>,
}

pub fn game_element_regular_eq(lhs: &GameElement, rhs: &GameElement) -> bool {
    regular_eq_inner(lhs, rhs, &mut RegularEqState::default())
}

pub fn regular_eq_inner(lhs: &GameElement, rhs: &GameElement, state: &mut RegularEqState) -> bool {
    match (lhs, rhs) {
        (GameElement::Finite(lhs), GameElement::Finite(rhs)) => {
            game_structural_eq_multiset(lhs, rhs)
        }
        (GameElement::Graph(lhs), GameElement::Graph(rhs)) => {
            if !state.visited_pairs.insert((graph_key(lhs), graph_key(rhs))) {
                return true;
            }
            regular_options_eq(lhs, rhs, true, state) && regular_options_eq(lhs, rhs, false, state)
        }
        (GameElement::Graph(graph), GameElement::Finite(finite))
        | (GameElement::Finite(finite), GameElement::Graph(graph)) => {
            if !state.mixed_path.insert(graph_key(graph)) {
                return false;
            }
            let graph_value = GameElement::Graph(graph.clone());
            let finite_value = GameElement::Finite(finite.clone());
            let result = [true, false].into_iter().all(|left| {
                let graph_options = game_options(&graph_value, left);
                let finite_options = game_options(&finite_value, left);
                graph_options.len() == finite_options.len()
                    && regular_element_options_eq(&graph_options, &finite_options, state)
            });
            state.mixed_path.remove(&graph_key(graph));
            result
        }
    }
}

pub fn regular_options_eq(
    lhs: &GraphRef,
    rhs: &GraphRef,
    left: bool,
    state: &RegularEqState,
) -> bool {
    let lhs = game_options(&GameElement::Graph(lhs.clone()), left);
    let rhs = game_options(&GameElement::Graph(rhs.clone()), left);
    lhs.len() == rhs.len() && regular_element_options_eq(&lhs, &rhs, state)
}

pub fn regular_element_options_eq(
    lhs: &[GameElement],
    rhs: &[GameElement],
    state: &RegularEqState,
) -> bool {
    // Every matrix edge gets branch-local assumptions. A failed candidate
    // cannot leak an optimistic cycle into another candidate's matching proof.
    perfect_matching(lhs.len(), |left, right| {
        let mut branch = state.clone();
        regular_eq_inner(&lhs[left], &rhs[right], &mut branch)
    })
}

pub fn graph_key(reference: &GraphRef) -> GraphKey {
    (Arc::as_ptr(&reference.graph) as usize, reference.node)
}

/// A value relation between presented games: exact on finite forms; on
/// cyclic forms, gated on both operands being stoppers and computed by
/// projecting the outcome of the conjugate sum.
pub fn form_value_relation(
    op: RelOp,
    lhs: &GameElement,
    rhs: &GameElement,
    node_budget: u128,
) -> GrundyResult<bool> {
    let cmp = |less: bool, equal: bool, greater: bool| match op {
        RelOp::Eq => equal,
        RelOp::Lt => less,
        RelOp::Gt => greater,
        RelOp::Le => less || equal,
        RelOp::Ge => greater || equal,
        RelOp::Fuzzy => !less && !equal && !greater,
        RelOp::Equiv | RelOp::Outcome(_) => unreachable!("not a value relation"),
    };
    if let (GameElement::Finite(lhs), GameElement::Finite(rhs)) = (lhs, rhs) {
        LoopyPartizanGraph::from_game(lhs, node_budget).map_err(partizan_graph_error)?;
        LoopyPartizanGraph::from_game(rhs, node_budget).map_err(partizan_graph_error)?;
        let le = lhs.le(rhs);
        let ge = rhs.le(lhs);
        return Ok(cmp(le && !ge, le && ge, ge && !le));
    }
    ensure_game_stopper("left", lhs, node_budget)?;
    ensure_game_stopper("right", rhs, node_budget)?;
    let projected = project_stopper_outcome(game_difference_outcome(lhs, rhs, node_budget)?);
    Ok(cmp(
        projected == RelOp::Lt,
        projected == RelOp::Eq,
        projected == RelOp::Gt,
    ))
}

/// The outcome cell of the conjugate sum `lhs + (-rhs)`.
pub fn form_outcome_cell(
    lhs: &GameElement,
    rhs: &GameElement,
    node_budget: u128,
) -> GrundyResult<OutcomeCell> {
    Ok(outcome_cell(game_difference_outcome(
        lhs,
        rhs,
        node_budget,
    )?))
}

/// The outcome of a presented game against zero.
pub fn form_outcome(element: &GameElement, node_budget: u128) -> GrundyResult<OutcomeCell> {
    form_outcome_cell(element, &GameElement::Finite(Game::zero()), node_budget)
}
