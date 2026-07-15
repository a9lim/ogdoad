//! Guarded game fixpoints, graph closure, and operational graph lowering.

use super::*;

pub(crate) enum SpineWalk {
    ReachesNil(Vec<GameElement>),
    Cycles,
}

pub(crate) fn walk_game_spine(spine: &GameElement) -> GrundyResult<SpineWalk> {
    let mut current = spine.clone();
    let mut heads = Vec::new();
    let mut visited = HashSet::new();
    loop {
        if let GameElement::Graph(reference) = &current {
            if !visited.insert(graph_key(reference)) {
                return Ok(SpineWalk::Cycles);
            }
        }
        let left = game_options(&current, true);
        let right = game_options(&current, false);
        match (left.len(), right.len()) {
            (0, 0) => return Ok(SpineWalk::ReachesNil(heads)),
            (1, 1) => {
                heads.push(left.into_iter().next().expect("singleton left option"));
                current = right.into_iter().next().expect("singleton right option");
            }
            _ => return Err(improper_spine_error()),
        }
    }
}

pub(crate) fn improper_spine_error() -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Improper,
        Span::point(0),
        "left operand of `⧺` is improper: its right-spine reaches a node that is neither cons nor nil",
    )
}

pub(crate) fn build_game_form(
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

pub(crate) fn graft_game_spine(
    heads: Vec<GameElement>,
    tail: GameElement,
    node_budget: u128,
) -> GrundyResult<GameElement> {
    if heads
        .iter()
        .chain(std::iter::once(&tail))
        .all(|value| matches!(value, GameElement::Finite(_)))
    {
        let GameElement::Finite(mut result) = tail else {
            unreachable!("checked above")
        };
        for head in heads.into_iter().rev() {
            let GameElement::Finite(head) = head else {
                unreachable!("checked above")
            };
            result = Game::new(vec![head], vec![result]);
        }
        return Ok(GameElement::Finite(result));
    }
    materialize_regular_game(
        "",
        symbolic_spine(heads, SymbolicGame::Value(tail)),
        node_budget,
    )
}

pub(crate) fn symbolic_spine(heads: Vec<GameElement>, tail: SymbolicGame) -> SymbolicGame {
    symbolic_spine_parts(heads.into_iter().map(SymbolicGame::Value).collect(), tail)
}

pub(crate) fn symbolic_spine_parts(heads: Vec<SymbolicGame>, tail: SymbolicGame) -> SymbolicGame {
    heads
        .into_iter()
        .rev()
        .fold(tail, |tail, head| SymbolicGame::Form {
            left: vec![head],
            right: vec![tail],
        })
}

pub(crate) fn materialize_regular_game(
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

pub(crate) fn materialize_symbolic_node(
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

pub(crate) fn materialize_symbolic_edge(
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

pub(crate) fn materialize_regular_system(
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
pub(crate) enum ClassificationPosition {
    Current(usize),
    External(GraphRef),
    Finite(Game),
}

pub(crate) fn classify_regular_nodes(
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

pub(crate) fn classification_edges(
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

pub(crate) fn operational_partizan_graph(
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

pub(crate) fn operational_classification_edges(
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

pub(crate) fn push_operational_position(
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

pub(crate) fn partizan_game_element(graph: LoopyPartizanGraph) -> GameElement {
    // Recover every well-founded subgraph as a finite `Game`. Besides keeping
    // finite results finite, this preserves literal recognition at exits from a
    // cyclic component (`-ones` should contain `-1`, not its expanded node DAG).
    let mut finite = vec![None; graph.node_count()];
    let mut remaining = vec![0_usize; graph.node_count()];
    let mut predecessors = vec![Vec::new(); graph.node_count()];
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
        .into_iter()
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

pub(crate) fn negate_game_element(
    element: GameElement,
    node_budget: u128,
) -> GrundyResult<GameElement> {
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

pub(crate) fn add_game_elements(
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

pub(crate) fn game_difference_outcome(
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

pub(crate) fn outcome_cell(outcome: LoopyPartizanOutcome) -> OutcomeCell {
    match (outcome.left_to_move, outcome.right_to_move) {
        (LoopyWinner::Left, LoopyWinner::Left) => OutcomeCell::LeftLeft,
        (LoopyWinner::Left, LoopyWinner::Draw) => OutcomeCell::LeftDraw,
        (LoopyWinner::Left, LoopyWinner::Right) => OutcomeCell::LeftRight,
        (LoopyWinner::Draw, LoopyWinner::Left) => OutcomeCell::DrawLeft,
        (LoopyWinner::Draw, LoopyWinner::Draw) => OutcomeCell::DrawDraw,
        (LoopyWinner::Draw, LoopyWinner::Right) => OutcomeCell::DrawRight,
        (LoopyWinner::Right, LoopyWinner::Left) => OutcomeCell::RightLeft,
        (LoopyWinner::Right, LoopyWinner::Draw) => OutcomeCell::RightDraw,
        (LoopyWinner::Right, LoopyWinner::Right) => OutcomeCell::RightRight,
    }
}

pub(crate) fn project_stopper_outcome(outcome: LoopyPartizanOutcome) -> RelOp {
    // Standard stopper-order projection: Siegel, Combinatorial Game Theory,
    // GSM 146, Def. VI.1.8 p. 284 (survival) and Thm. VI.2.1 p. 290.
    match outcome_cell(outcome) {
        OutcomeCell::LeftLeft | OutcomeCell::LeftDraw => RelOp::Gt,
        OutcomeCell::LeftRight => RelOp::Fuzzy,
        OutcomeCell::RightLeft
        | OutcomeCell::RightDraw
        | OutcomeCell::DrawLeft
        | OutcomeCell::DrawDraw => RelOp::Eq,
        OutcomeCell::DrawRight | OutcomeCell::RightRight => RelOp::Lt,
    }
}

pub(crate) fn ensure_game_stopper(
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

pub(crate) fn game_element_is_stopper(
    element: &GameElement,
    node_budget: u128,
) -> GrundyResult<bool> {
    operational_partizan_graph(element, node_budget)?
        .is_stopper(0)
        .map_err(partizan_graph_error)
}

pub(crate) fn render_stopper_witness(cycle: &[crate::games::LoopyTurnState]) -> String {
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

pub(crate) fn partizan_graph_error(error: LoopyPartizanGraphError) -> GrundyError {
    match error {
        LoopyPartizanGraphError::NodeBudgetExceeded { budget } => graph_budget_error(budget),
        other => GrundyError::new(
            GrundyErrorKind::Domain,
            Span::point(0),
            format!("invalid materialized game graph: {other}"),
        ),
    }
}

pub(crate) fn game_options(element: &GameElement, left: bool) -> Vec<GameElement> {
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

pub(crate) fn unfounded_error(name: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Unfounded,
        Span::point(0),
        format!("Element fixpoint `{name}` is not guarded by a brace constructor"),
    )
}

pub(crate) fn unfounded_system_error(equation: &str, name: &str) -> GrundyError {
    GrundyError::new(
        GrundyErrorKind::Unfounded,
        Span::point(0),
        format!(
            "Element equation `{equation}` has unguarded system name `{name}` outside a brace constructor"
        ),
    )
}

pub(crate) fn loopy_error(message: &str) -> GrundyError {
    GrundyError::new(GrundyErrorKind::Loopy, Span::point(0), message)
}

pub(crate) fn game_option_index(name: &str, index: i128) -> GrundyResult<usize> {
    usize::try_from(index).map_err(|_| domain(format!("{name} option index must be non-negative")))
}

pub(crate) fn game_wrong_world(message: &str) -> GrundyError {
    GrundyError::new(GrundyErrorKind::WrongWorld, Span::point(0), message)
}

pub(crate) fn game_wrong_world_hint(message: &str, hint: &str) -> GrundyError {
    game_wrong_world(message).with_hint(hint)
}

pub(crate) fn refine_game_binder_sorts(
    expr: &Expr,
    binders: &[String],
    sorts: &mut [DataSort],
    env: &BTreeMap<String, Value<GameElement>>,
) {
    match expr {
        Expr::Relation { lhs, rhs, .. } => {
            if game_known_sort(lhs, env) == Some(DataSort::Index) {
                mark_game_expr_sort(rhs, DataSort::Index, binders, sorts);
            }
            if game_known_sort(rhs, env) == Some(DataSort::Index) {
                mark_game_expr_sort(lhs, DataSort::Index, binders, sorts);
            }
            refine_game_binder_sorts(lhs, binders, sorts, env);
            refine_game_binder_sorts(rhs, binders, sorts, env);
        }
        Expr::Apply { callee, args } => {
            if let Expr::Ident(name) = &**callee {
                if let Some(Value::Function(function)) = env.get(name) {
                    for (arg, binder) in args.iter().zip(&function.binders) {
                        mark_game_expr_sort(arg, binder.sort, binders, sorts);
                    }
                }
            }
            refine_game_binder_sorts(callee, binders, sorts, env);
            for arg in args {
                refine_game_binder_sorts(arg, binders, sorts, env);
            }
        }
        Expr::Block { bindings, body } => {
            for binding in bindings {
                refine_game_binder_sorts(&binding.expr, binders, sorts, env);
            }
            refine_game_binder_sorts(body, binders, sorts, env);
        }
        Expr::Container(items) => {
            for item in items {
                refine_game_binder_sorts(item, binders, sorts, env);
            }
        }
        Expr::GameForm { left, right } => {
            for item in left.iter().chain(right) {
                refine_game_binder_sorts(item, binders, sorts, env);
            }
        }
        Expr::Lambda { body, .. } | Expr::Index(body) | Expr::Unary { expr: body, .. } => {
            refine_game_binder_sorts(body, binders, sorts, env);
        }
        Expr::Call { args, .. } => {
            for arg in args {
                refine_game_binder_sorts(arg, binders, sorts, env);
            }
        }
        Expr::Binary { lhs, rhs, .. } => {
            refine_game_binder_sorts(lhs, binders, sorts, env);
            refine_game_binder_sorts(rhs, binders, sorts, env);
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            refine_game_binder_sorts(cond, binders, sorts, env);
            refine_game_binder_sorts(then_expr, binders, sorts, env);
            refine_game_binder_sorts(else_expr, binders, sorts, env);
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Up
        | Expr::Down
        | Expr::Dim
        | Expr::Ident(_) => {}
    }
}

pub(crate) fn mark_game_expr_sort(
    expr: &Expr,
    sort: DataSort,
    binders: &[String],
    sorts: &mut [DataSort],
) {
    match expr {
        Expr::Ident(name) => {
            if let Some(index) = binders.iter().position(|binder| binder == name) {
                sorts[index] = sort;
            }
        }
        Expr::Unary { expr, .. } => mark_game_expr_sort(expr, sort, binders, sorts),
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Pow,
            lhs,
            rhs,
        } => {
            mark_game_expr_sort(lhs, sort, binders, sorts);
            mark_game_expr_sort(rhs, sort, binders, sorts);
        }
        _ => {}
    }
}

pub(crate) fn game_known_sort(
    expr: &Expr,
    env: &BTreeMap<String, Value<GameElement>>,
) -> Option<DataSort> {
    match expr {
        Expr::Index(_) | Expr::Dim => Some(DataSort::Index),
        Expr::Call { name, .. }
            if matches!(
                name.as_str(),
                "nleft" | "nright" | "dim" | "deg" | "birthday"
            ) =>
        {
            Some(DataSort::Index)
        }
        Expr::Call { name, .. } if matches!(name.as_str(), "hasdraw" | "stopper" | "integral") => {
            Some(DataSort::Bool)
        }
        Expr::Apply { callee, .. } => game_function_expr_return_sort(callee, env),
        Expr::Bool(_)
        | Expr::Relation { .. }
        | Expr::Unary {
            op: UnaryOp::Not, ..
        }
        | Expr::Binary {
            op: BinaryOp::And | BinaryOp::Or,
            ..
        } => Some(DataSort::Bool),
        _ => None,
    }
}

pub(crate) fn game_function_expr_return_sort(
    expr: &Expr,
    env: &BTreeMap<String, Value<GameElement>>,
) -> Option<DataSort> {
    match expr {
        Expr::Ident(name) => match env.get(name) {
            Some(Value::Function(function)) => Some(function.ret),
            _ => None,
        },
        Expr::Block { bindings, body } => {
            let Expr::Ident(name) = &**body else {
                return None;
            };
            let binding = bindings
                .iter()
                .rev()
                .find(|binding| &binding.name == name)?;
            let Expr::Lambda { body, .. } = &binding.expr else {
                return None;
            };
            game_return_sort_hint(
                body,
                env,
                binding.recursive.then_some(binding.name.as_str()),
            )
        }
        _ => None,
    }
}

pub(crate) fn game_return_sort_hint(
    body: &Expr,
    env: &BTreeMap<String, Value<GameElement>>,
    mu_name: Option<&str>,
) -> Option<DataSort> {
    if bool_shaped(body) {
        return Some(DataSort::Bool);
    }
    if let Some(name) = mu_name {
        if is_game_index_counter(name, body) {
            return Some(DataSort::Index);
        }
    }
    match body {
        Expr::Apply { callee, .. } => game_function_expr_return_sort(callee, env),
        Expr::Call { name, .. }
            if matches!(
                name.as_str(),
                "nleft" | "nright" | "dim" | "deg" | "birthday"
            ) =>
        {
            Some(DataSort::Index)
        }
        Expr::Block { bindings, body } => {
            let mut local_returns = BTreeMap::new();
            for binding in bindings {
                if let Expr::Lambda { body, .. } = &binding.expr {
                    let hint = if bool_shaped(body) {
                        Some(DataSort::Bool)
                    } else if binding.recursive && is_game_index_counter(&binding.name, body) {
                        Some(DataSort::Index)
                    } else {
                        game_return_sort_hint(body, env, None)
                    };
                    if let Some(sort) = hint {
                        local_returns.insert(binding.name.as_str(), sort);
                    }
                }
            }
            if let Expr::Apply { callee, .. } = &**body {
                if let Expr::Ident(name) = &**callee {
                    return local_returns.get(name.as_str()).copied();
                }
            }
            game_return_sort_hint(body, env, None)
        }
        Expr::If {
            then_expr,
            else_expr,
            ..
        } => {
            let lhs = game_return_sort_hint(then_expr, env, mu_name);
            let rhs = game_return_sort_hint(else_expr, env, mu_name);
            (lhs == rhs).then_some(lhs).flatten()
        }
        _ => game_known_sort(body, env),
    }
}

pub(crate) fn is_game_index_counter(name: &str, expr: &Expr) -> bool {
    contains_game_self_call(name, expr) && contains_game_unit_step(expr)
}

pub(crate) fn contains_game_self_call(name: &str, expr: &Expr) -> bool {
    match expr {
        Expr::Apply { callee, args } => {
            matches!(&**callee, Expr::Ident(candidate) if candidate == name)
                || contains_game_self_call(name, callee)
                || args.iter().any(|arg| contains_game_self_call(name, arg))
        }
        Expr::Block { bindings, body } => {
            bindings
                .iter()
                .any(|binding| contains_game_self_call(name, &binding.expr))
                || contains_game_self_call(name, body)
        }
        Expr::Container(items) => items.iter().any(|item| contains_game_self_call(name, item)),
        Expr::GameForm { left, right } => left
            .iter()
            .chain(right)
            .any(|item| contains_game_self_call(name, item)),
        Expr::Lambda { body, .. } | Expr::Index(body) | Expr::Unary { expr: body, .. } => {
            contains_game_self_call(name, body)
        }
        Expr::Call { args, .. } => args.iter().any(|arg| contains_game_self_call(name, arg)),
        Expr::Binary { lhs, rhs, .. } | Expr::Relation { lhs, rhs, .. } => {
            contains_game_self_call(name, lhs) || contains_game_self_call(name, rhs)
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            contains_game_self_call(name, cond)
                || contains_game_self_call(name, then_expr)
                || contains_game_self_call(name, else_expr)
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Up
        | Expr::Down
        | Expr::Dim
        | Expr::Ident(_) => false,
    }
}

pub(crate) fn contains_game_unit_step(expr: &Expr) -> bool {
    match expr {
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub,
            lhs,
            rhs,
        } if (matches!(&**lhs, Expr::Ident(_)) && matches!(&**rhs, Expr::Int(1)))
            || matches!(&**lhs, Expr::Int(1)) =>
        {
            true
        }
        Expr::Block { bindings, body } => {
            bindings
                .iter()
                .any(|binding| contains_game_unit_step(&binding.expr))
                || contains_game_unit_step(body)
        }
        Expr::Container(items) => items.iter().any(contains_game_unit_step),
        Expr::Apply { callee, args } => {
            contains_game_unit_step(callee) || args.iter().any(contains_game_unit_step)
        }
        Expr::GameForm { left, right } => left.iter().chain(right).any(contains_game_unit_step),
        Expr::Lambda { body, .. } | Expr::Index(body) | Expr::Unary { expr: body, .. } => {
            contains_game_unit_step(body)
        }
        Expr::Call { args, .. } => args.iter().any(contains_game_unit_step),
        Expr::Binary { lhs, rhs, .. } | Expr::Relation { lhs, rhs, .. } => {
            contains_game_unit_step(lhs) || contains_game_unit_step(rhs)
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            contains_game_unit_step(cond)
                || contains_game_unit_step(then_expr)
                || contains_game_unit_step(else_expr)
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Up
        | Expr::Down
        | Expr::Dim
        | Expr::Ident(_) => false,
    }
}

pub(crate) fn contains_game_binder_unit_step(binder: &str, expr: &Expr) -> bool {
    match expr {
        Expr::Binary {
            op: BinaryOp::Add | BinaryOp::Sub,
            lhs,
            rhs,
        } if matches!(&**lhs, Expr::Ident(name) if name == binder)
            && matches!(&**rhs, Expr::Int(1)) =>
        {
            true
        }
        Expr::Block { bindings, body } => {
            bindings
                .iter()
                .any(|binding| contains_game_binder_unit_step(binder, &binding.expr))
                || contains_game_binder_unit_step(binder, body)
        }
        Expr::Container(items) => items
            .iter()
            .any(|item| contains_game_binder_unit_step(binder, item)),
        Expr::Apply { callee, args } => {
            contains_game_binder_unit_step(binder, callee)
                || args
                    .iter()
                    .any(|arg| contains_game_binder_unit_step(binder, arg))
        }
        Expr::GameForm { left, right } => left
            .iter()
            .chain(right)
            .any(|item| contains_game_binder_unit_step(binder, item)),
        Expr::Lambda { body, .. } | Expr::Index(body) | Expr::Unary { expr: body, .. } => {
            contains_game_binder_unit_step(binder, body)
        }
        Expr::Call { args, .. } => args
            .iter()
            .any(|arg| contains_game_binder_unit_step(binder, arg)),
        Expr::Binary { lhs, rhs, .. } | Expr::Relation { lhs, rhs, .. } => {
            contains_game_binder_unit_step(binder, lhs)
                || contains_game_binder_unit_step(binder, rhs)
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            contains_game_binder_unit_step(binder, cond)
                || contains_game_binder_unit_step(binder, then_expr)
                || contains_game_binder_unit_step(binder, else_expr)
        }
        Expr::Int(_)
        | Expr::Bool(_)
        | Expr::Star(_)
        | Expr::Omega
        | Expr::Blade(_)
        | Expr::Up
        | Expr::Down
        | Expr::Dim
        | Expr::Ident(_) => false,
    }
}
