//! Game-form recognition and finite/loopy display.

use super::*;

type DisplayReachability = (
    Vec<GraphKey>,
    HashMap<GraphKey, Vec<GraphKey>>,
    HashMap<GraphKey, GraphRef>,
);

pub(crate) fn display_game_value(
    value: &Value<GameElement>,
    env: &BTreeMap<String, Value<GameElement>>,
) -> String {
    match value {
        Value::Element(game) => display_game_element_in_env(game, env),
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
    display_game_element_in_env(element, &BTreeMap::new())
}

pub(crate) fn display_game_element_in_env(
    element: &GameElement,
    env: &BTreeMap<String, Value<GameElement>>,
) -> String {
    match element {
        GameElement::Finite(game) => display_game(game),
        GameElement::Graph(reference) => display_composite_graph(reference, env),
    }
}

pub(crate) fn display_composite_graph(
    reference: &GraphRef,
    env: &BTreeMap<String, Value<GameElement>>,
) -> String {
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
        if let Value::Element(GameElement::Graph(bound)) = value {
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
        if groups.len() == 1
            && groups[0]
                .iter()
                .all(|anchor| component_of[&graph_key(anchor)] == root_component)
        {
            return parts.join("; ");
        }
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
    env: &BTreeMap<String, Value<GameElement>>,
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
        Some(Value::Element(GameElement::Graph(bound)))
            if Arc::ptr_eq(&bound.graph, &root.graph) =>
        {
            Some(provenance.clone())
        }
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

pub(crate) fn graph_reference_successors(reference: &GraphRef) -> Vec<GraphRef> {
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
