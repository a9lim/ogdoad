//! Game-form recognition and finite/loopy display.

use super::*;

pub(crate) fn display_game_value(value: &Value<GameElement>) -> String {
    match value {
        Value::Element(game) => display_game_element(game),
        Value::Index(value) => display_index(*value),
        Value::Bool(value) => value.to_string(),
        Value::Function(function) => {
            let lambda = crate::ogham::unparse::unparse_expr(&function.lambda_expr());
            function
                .mu_name
                .as_ref()
                .map_or(lambda.clone(), |name| format!("{name} =: {lambda}"))
        }
    }
}

pub(crate) fn display_game_element(element: &GameElement) -> String {
    match element {
        GameElement::Finite(game) => display_game(game),
        GameElement::Graph(reference) if !reference.graph.name.is_empty() => {
            let mut anchors = HashMap::new();
            anchors.insert(graph_key(reference), reference.graph.name.clone());
            format!(
                "{} =: {}",
                reference.graph.name,
                display_graph_node(reference, &anchors, true, &mut HashSet::new())
            )
        }
        GameElement::Graph(reference) => display_composite_graph(reference),
    }
}

pub(crate) fn display_composite_graph(reference: &GraphRef) -> String {
    let anchored = collect_display_anchors(reference);
    if anchored.is_empty() {
        return display_graph_node(reference, &HashMap::new(), true, &mut HashSet::new());
    }
    let mut anchors = HashMap::new();
    let mut generated = 1_u128;
    for anchor in &anchored {
        let name = if anchor.graph.name.is_empty() {
            let name = format!("g{generated}");
            generated += 1;
            name
        } else {
            anchor.graph.name.clone()
        };
        anchors.insert(graph_key(anchor), name);
    }
    // Inner first-reach cycles are definitions used by their enclosing cycle,
    // so emit the flat block from inner to outer while retaining g1, g2, ... in
    // first-reach naming order.
    let mut parts = anchored
        .iter()
        .rev()
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
        return parts.pop().expect("single synthesized root equation");
    }
    parts.push(
        root_name
            .unwrap_or_else(|| display_graph_node(reference, &anchors, true, &mut HashSet::new())),
    );
    format!("({})", parts.join("; "))
}

pub(crate) fn collect_display_anchors(root: &GraphRef) -> Vec<GraphRef> {
    let root_key = graph_key(root);
    let mut colors = HashMap::from([(root_key, 1_u8)]);
    let mut discovery = vec![root.clone()];
    let mut back_targets = HashSet::new();
    let mut named_entries = HashSet::new();
    let mut stack = vec![(root.clone(), graph_reference_successors(root), 0_usize)];

    while !stack.is_empty() {
        let top = stack.len() - 1;
        if stack[top].2 == stack[top].1.len() {
            colors.insert(graph_key(&stack[top].0), 2);
            stack.pop();
            continue;
        }
        let (target, named_entry) = stack[top].1[stack[top].2].clone();
        stack[top].2 += 1;
        let key = graph_key(&target);
        if named_entry {
            named_entries.insert(key);
        }
        match colors.get(&key).copied().unwrap_or(0) {
            0 => {
                colors.insert(key, 1);
                discovery.push(target.clone());
                let successors = graph_reference_successors(&target);
                stack.push((target, successors, 0));
            }
            1 => {
                back_targets.insert(key);
            }
            _ => {}
        }
    }

    discovery
        .into_iter()
        .filter(|reference| {
            let key = graph_key(reference);
            named_entries.contains(&key) || back_targets.contains(&key)
        })
        .collect()
}

pub(crate) fn graph_reference_successors(reference: &GraphRef) -> Vec<(GraphRef, bool)> {
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
            RegularGameEdge::External(reference) => {
                Some((reference.clone(), !reference.graph.name.is_empty()))
            }
        })
        .collect()
}

pub(crate) fn display_graph_node(
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
            .unwrap_or_else(|| reference.graph.name.clone());
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

pub(crate) fn display_regular_edge(
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

pub(crate) fn display_raw_game_form(left: &str, right: &str) -> String {
    match (left.is_empty(), right.is_empty()) {
        (true, true) => "{|}".to_string(),
        (false, true) => format!("{{{left} |}}"),
        (true, false) => format!("{{| {right}}}"),
        (false, false) => format!("{{{left} | {right}}}"),
    }
}

pub(crate) fn display_game(game: &Game) -> String {
    if let Some(integer) = structural_game_integer(game) {
        return integer.to_string();
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
    if let Some(items) = structural_game_list(game) {
        return format!(
            "[{}]",
            items
                .iter()
                .map(|item| display_game(item))
                .collect::<Vec<_>>()
                .join(", ")
        );
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

pub(crate) fn structural_game_list(mut game: &Game) -> Option<Vec<&Game>> {
    let mut items = Vec::new();
    loop {
        if game.left().is_empty() && game.right().is_empty() {
            return Some(items);
        }
        if game.left().len() != 1 || game.right().len() != 1 {
            return None;
        }
        items.push(&game.left()[0]);
        game = &game.right()[0];
    }
}

pub(crate) fn structural_game_integer(game: &Game) -> Option<i128> {
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

pub(crate) fn structural_game_nimber(game: &Game) -> Option<u128> {
    if game.left().is_empty() && game.right().is_empty() {
        return Some(0);
    }
    if game.left().len() != game.right().len() {
        return None;
    }
    let nimber = u128::try_from(game.left().len()).ok()?;
    game_structural_eq_multiset(game, &Game::nim_heap(nimber)).then_some(nimber)
}
