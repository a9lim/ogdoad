//! Rulesets: component positions with move generators, explored into game
//! values, Grundy numbers, and presented graphs.
//!
//! An option is a list of components — a disjunctive sum — so splitting games
//! are first-class. `[]` means no options; `[[]]` is one option that removes
//! the component. Exploration is iterative and budgeted: the node budget
//! bounds distinct positions, fuel bounds the work of move generation.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::rc::Rc;

use ogdoad::games::{octal_moves, LoopyPartizanGraph, OctalCode};

use super::super::builtins::Builtin;
use super::super::core::CtorRef;
use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult};
use super::super::eval::interp::Interp;
use super::super::eval::value::{key_cmp, Value};
use super::form::{partizan_game_element, partizan_graph_error, FormV};
use super::game::GameV;

/// How a ruleset generates moves.
pub enum RulesKind {
    /// One move function for both players.
    Impartial(Value),
    /// Left and Right move functions.
    Partizan(Value, Value),
    /// A finite octal code over single heaps.
    Octal(OctalCode),
}

/// A ruleset with its memo tables.
pub struct RulesV {
    /// The move generator.
    pub kind: RulesKind,
    values: RefCell<HashMap<PosKey, GameV>>,
    grundy: RefCell<HashMap<PosKey, i128>>,
}

impl RulesV {
    /// Wrap a generator.
    pub fn new(kind: RulesKind) -> RulesV {
        RulesV {
            kind,
            values: RefCell::new(HashMap::new()),
            grundy: RefCell::new(HashMap::new()),
        }
    }

    /// Whether both players share one move function.
    pub fn impartial(&self) -> bool {
        matches!(self.kind, RulesKind::Impartial(_) | RulesKind::Octal(_))
    }
}

/// A hashable structural key for a `Key` value.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PosKey {
    /// An integer.
    Int(i128),
    /// A Boolean.
    Bool(bool),
    /// A winner.
    Winner(u8),
    /// A tuple.
    Tuple(Vec<PosKey>),
    /// A list.
    List(Vec<PosKey>),
    /// An option.
    Option(Option<Box<PosKey>>),
    /// A data value: constructor rank and fields.
    Data((u8, u32, u32), Vec<PosKey>),
    /// A game value by interned id.
    Game(u32),
    /// A scalar by canonical display.
    Scalar(String),
}

/// The structural key of a position.
pub fn pos_key(value: &Value) -> PosKey {
    match value {
        Value::Int(n) => PosKey::Int(*n),
        Value::Bool(b) => PosKey::Bool(*b),
        Value::Winner(w) => PosKey::Winner(*w),
        Value::Tuple(items) => PosKey::Tuple(items.iter().map(pos_key).collect()),
        Value::List(items) => PosKey::List(items.iter().map(pos_key).collect()),
        Value::Option(inner) => PosKey::Option(inner.as_ref().map(|v| Box::new(pos_key(v)))),
        Value::Data(data) => {
            let rank = match &data.ctor {
                CtorRef::Data(id, index) => (0, *id, *index),
                CtorRef::Winner(w) => (1, u32::from(*w), 0),
                CtorRef::None => (2, 0, 0),
                CtorRef::Some => (2, 1, 0),
            };
            PosKey::Data(rank, data.fields.iter().map(pos_key).collect())
        }
        Value::Game(g) => PosKey::Game(g.id()),
        Value::Scalar(s) => PosKey::Scalar(s.to_string()),
        other => PosKey::Scalar(format!("<{}>", other.kind_name())),
    }
}

/// The players.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Player {
    /// Left.
    Left,
    /// Right.
    Right,
}

fn player(value: &Value) -> GrundyResult<Player> {
    match value {
        Value::Winner(0) => Ok(Player::Left),
        Value::Winner(1) => Ok(Player::Right),
        _ => Err(err(
            GrundyErrorKind::Domain,
            "a player is `Left` or `Right`",
        )),
    }
}

fn rules_of(value: &Value) -> &Rc<RulesV> {
    match value {
        Value::Rules(rules) => rules,
        other => panic!("expected Rules, found {}", other.kind_name()),
    }
}

/// The options of one component for one player.
pub fn component_moves(
    interp: &mut Interp<'_>,
    rules: &RulesV,
    position: &Value,
    who: Player,
) -> GrundyResult<Vec<Vec<Value>>> {
    let raw = match &rules.kind {
        RulesKind::Impartial(f) => interp.apply(f, vec![position.clone()])?,
        RulesKind::Partizan(left, right) => {
            let f = if who == Player::Left { left } else { right };
            interp.apply(f, vec![position.clone()])?
        }
        RulesKind::Octal(code) => {
            let heap = position.as_int();
            if heap < 0 {
                return Err(err(
                    GrundyErrorKind::Domain,
                    "octal heaps are natural numbers",
                ));
            }
            if heap == 0 {
                return Ok(Vec::new());
            }
            let moves = octal_moves(
                &code
                    .digits()
                    .iter()
                    .map(|d| u128::from(*d))
                    .collect::<Vec<_>>(),
                &[heap as u128],
            );
            interp.spend(moves.len() as u128)?;
            return Ok(moves
                .into_iter()
                .map(|option| option.into_iter().map(|h| Value::Int(h as i128)).collect())
                .collect());
        }
    };
    let mut out = Vec::new();
    for option in raw.as_list().iter() {
        let components = option.as_list().to_vec();
        interp.spend(1 + components.len() as u128)?;
        out.push(components);
    }
    Ok(out)
}

/// The component graph reachable from a root: positions in discovery order,
/// and each position's options (as indices) for both players.
struct ComponentGraph {
    positions: Vec<Value>,
    left: Vec<Vec<Vec<usize>>>,
    right: Vec<Vec<Vec<usize>>>,
}

fn explore_components(
    interp: &mut Interp<'_>,
    rules: &RulesV,
    root: &Value,
    known: &dyn Fn(&PosKey) -> bool,
) -> GrundyResult<(ComponentGraph, HashMap<PosKey, usize>)> {
    let mut index: HashMap<PosKey, usize> = HashMap::new();
    let mut graph = ComponentGraph {
        positions: Vec::new(),
        left: Vec::new(),
        right: Vec::new(),
    };
    let mut queue = VecDeque::new();
    let mut intern = |value: &Value,
                      graph: &mut ComponentGraph,
                      queue: &mut VecDeque<usize>,
                      budget: u128|
     -> GrundyResult<usize> {
        let key = pos_key(value);
        if let Some(&id) = index.get(&key) {
            return Ok(id);
        }
        if graph.positions.len() as u128 >= budget {
            return Err(budget_error(budget));
        }
        let id = graph.positions.len();
        graph.positions.push(value.clone());
        graph.left.push(Vec::new());
        graph.right.push(Vec::new());
        if !known(&key) {
            queue.push_back(id);
        }
        index.insert(key, id);
        Ok(id)
    };
    let budget = interp.graph_budget;
    intern(root, &mut graph, &mut queue, budget)?;
    while let Some(id) = queue.pop_front() {
        let position = graph.positions[id].clone();
        let left = component_moves(interp, rules, &position, Player::Left)?;
        let right = if rules.impartial() {
            left.clone()
        } else {
            component_moves(interp, rules, &position, Player::Right)?
        };
        let mut side = |options: Vec<Vec<Value>>,
                        graph: &mut ComponentGraph,
                        queue: &mut VecDeque<usize>|
         -> GrundyResult<Vec<Vec<usize>>> {
            let mut out = Vec::new();
            for option in options {
                let mut ids = Vec::new();
                for component in &option {
                    ids.push(intern(component, graph, queue, budget)?);
                }
                out.push(ids);
            }
            Ok(out)
        };
        let left = side(left, &mut graph, &mut queue)?;
        let right = side(right, &mut graph, &mut queue)?;
        graph.left[id] = left;
        graph.right[id] = right;
    }
    Ok((graph, index))
}

/// Children-first order of the explored positions, or a component cycle.
fn topological(
    graph: &ComponentGraph,
    done: &dyn Fn(usize) -> bool,
) -> Result<Vec<usize>, Vec<usize>> {
    let n = graph.positions.len();
    let mut state = vec![0u8; n]; // 0 new, 1 on stack, 2 finished
    let mut order = Vec::new();
    for start in 0..n {
        if state[start] != 0 || done(start) {
            continue;
        }
        let mut stack: Vec<(usize, Vec<usize>, usize)> = Vec::new();
        let children = |id: usize| -> Vec<usize> {
            let mut out: Vec<usize> = graph.left[id]
                .iter()
                .chain(&graph.right[id])
                .flatten()
                .copied()
                .collect();
            out.sort_unstable();
            out.dedup();
            out
        };
        state[start] = 1;
        stack.push((start, children(start), 0));
        while let Some((node, kids, next)) = stack.last_mut() {
            if *next < kids.len() {
                let child = kids[*next];
                *next += 1;
                if done(child) || state[child] == 2 {
                    continue;
                }
                if state[child] == 1 {
                    let mut cycle: Vec<usize> = stack.iter().map(|(id, _, _)| *id).collect();
                    let from = cycle.iter().position(|id| *id == child).unwrap_or(0);
                    cycle.drain(..from);
                    cycle.push(child);
                    return Err(cycle);
                }
                state[child] = 1;
                let grandchildren = children(child);
                stack.push((child, grandchildren, 0));
            } else {
                let node = *node;
                state[node] = 2;
                order.push(node);
                stack.pop();
            }
        }
    }
    Ok(order)
}

fn cycle_error(
    data: &super::super::types::DataRegistry,
    graph: &ComponentGraph,
    cycle: &[usize],
) -> GrundyError {
    let shown: Vec<String> = cycle
        .iter()
        .map(|id| super::super::display::show_plain(&graph.positions[*id], data))
        .collect();
    err(
        GrundyErrorKind::Loopy,
        format!("the component positions cycle: {}", shown.join(" → ")),
    )
    .with_hint("a cyclic ruleset has no short value; `graph(R, p)` presents it as a Form")
}

/// `value(R, p)`.
pub fn value(interp: &mut Interp<'_>, rules: &RulesV, root: &Value) -> GrundyResult<GameV> {
    if let Some(game) = rules.values.borrow().get(&pos_key(root)) {
        return Ok(game.clone());
    }
    let memo = rules.values.borrow().clone();
    let (graph, _) = explore_components(interp, rules, root, &|key| memo.contains_key(key))?;
    let known = |id: usize| memo.contains_key(&pos_key(&graph.positions[id]));
    let order =
        topological(&graph, &known).map_err(|cycle| cycle_error(interp.data, &graph, &cycle))?;
    let mut values: Vec<Option<GameV>> = graph
        .positions
        .iter()
        .map(|p| memo.get(&pos_key(p)).cloned())
        .collect();
    for id in order {
        let sum = |option: &[usize], values: &[Option<GameV>]| {
            option.iter().fold(GameV::integer(0), |acc, c| {
                acc.add(values[*c].as_ref().expect("children first"))
            })
        };
        let left: Vec<GameV> = graph.left[id].iter().map(|o| sum(o, &values)).collect();
        let right: Vec<GameV> = graph.right[id].iter().map(|o| sum(o, &values)).collect();
        interp.spend(1 + (left.len() + right.len()) as u128)?;
        values[id] = Some(GameV::form(&left, &right));
    }
    let mut memo = rules.values.borrow_mut();
    for (position, value) in graph.positions.iter().zip(&values) {
        if let Some(value) = value {
            memo.insert(pos_key(position), value.clone());
        }
    }
    Ok(values[0].clone().expect("root valued"))
}

/// `sg(R, p)`: the Grundy number of a component.
pub fn grundy(interp: &mut Interp<'_>, rules: &RulesV, root: &Value) -> GrundyResult<i128> {
    if !rules.impartial() {
        return Err(
            err(GrundyErrorKind::Domain, "`sg` needs an impartial ruleset")
                .with_hint("partizan positions have values: `value(R, p)`"),
        );
    }
    if let Some(n) = rules.grundy.borrow().get(&pos_key(root)) {
        return Ok(*n);
    }
    let memo = rules.grundy.borrow().clone();
    let (graph, _) = explore_components(interp, rules, root, &|key| memo.contains_key(key))?;
    let known = |id: usize| memo.contains_key(&pos_key(&graph.positions[id]));
    let order =
        topological(&graph, &known).map_err(|cycle| cycle_error(interp.data, &graph, &cycle))?;
    let mut values: Vec<Option<i128>> = graph
        .positions
        .iter()
        .map(|p| memo.get(&pos_key(p)).copied())
        .collect();
    for id in order {
        let mut reachable: Vec<i128> = graph.left[id]
            .iter()
            .map(|option| {
                option
                    .iter()
                    .fold(0, |acc, c| acc ^ values[*c].expect("children first"))
            })
            .collect();
        reachable.sort_unstable();
        reachable.dedup();
        let mut mex = 0;
        for value in reachable {
            if value == mex {
                mex += 1;
            } else if value > mex {
                break;
            }
        }
        values[id] = Some(mex);
    }
    let mut memo = rules.grundy.borrow_mut();
    for (position, value) in graph.positions.iter().zip(&values) {
        if let Some(value) = value {
            memo.insert(pos_key(position), *value);
        }
    }
    Ok(values[0].expect("root valued"))
}

/// A sum-state: components sorted by the structural order.
fn normalize(mut components: Vec<Value>) -> Vec<Value> {
    components.sort_by(key_cmp);
    components
}

fn state_key(components: &[Value]) -> Vec<PosKey> {
    components.iter().map(pos_key).collect()
}

/// The successors of a sum for one player: moving in one component replaces
/// it by the option's components. Equal components contribute once.
pub fn sum_moves(
    interp: &mut Interp<'_>,
    rules: &RulesV,
    components: &[Value],
    who: Player,
) -> GrundyResult<Vec<Vec<Value>>> {
    let mut out = Vec::new();
    for (index, component) in components.iter().enumerate() {
        if index > 0 && key_cmp(&components[index - 1], component) == Ordering::Equal {
            continue;
        }
        for option in component_moves(interp, rules, component, who)? {
            let mut next: Vec<Value> = components
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != index)
                .map(|(_, c)| c.clone())
                .collect();
            next.extend(option);
            out.push(normalize(next));
        }
    }
    Ok(out)
}

/// `graph(R, p)`: the presented sum-state graph, cycles allowed.
pub fn graph(interp: &mut Interp<'_>, rules: &RulesV, root: &Value) -> GrundyResult<FormV> {
    let budget = interp.graph_budget;
    let mut index: BTreeMap<Vec<PosKey>, usize> = BTreeMap::new();
    let mut states: Vec<Vec<Value>> = Vec::new();
    let mut left: Vec<Vec<usize>> = Vec::new();
    let mut right: Vec<Vec<usize>> = Vec::new();
    let root_state = normalize(vec![root.clone()]);
    index.insert(state_key(&root_state), 0);
    states.push(root_state);
    left.push(Vec::new());
    right.push(Vec::new());
    let mut cursor = 0;
    while cursor < states.len() {
        let state = states[cursor].clone();
        for (who, edges) in [(Player::Left, true), (Player::Right, false)] {
            if !edges && rules.impartial() {
                right[cursor] = left[cursor].clone();
                continue;
            }
            let mut targets = Vec::new();
            for next in sum_moves(interp, rules, &state, who)? {
                let key = state_key(&next);
                let id = match index.get(&key) {
                    Some(&id) => id,
                    None => {
                        if states.len() as u128 >= budget {
                            return Err(budget_error(budget));
                        }
                        let id = states.len();
                        index.insert(key, id);
                        states.push(next);
                        left.push(Vec::new());
                        right.push(Vec::new());
                        id
                    }
                };
                targets.push(id);
            }
            if edges {
                left[cursor] = targets;
            } else {
                right[cursor] = targets;
            }
        }
        cursor += 1;
    }
    let graph = LoopyPartizanGraph::new(left, right).map_err(partizan_graph_error)?;
    Ok(FormV(partizan_game_element(graph)))
}

fn budget_error(budget: u128) -> GrundyError {
    err(
        GrundyErrorKind::GraphBudget,
        format!("the exploration exceeds the node budget of {budget} positions"),
    )
    .with_hint(
        "raise it with `:graph n`; finitely many components can still have infinitely many sums",
    )
}

/// Ruleset builtins.
pub fn call(interp: &mut Interp<'_>, builtin: Builtin, args: Vec<Value>) -> GrundyResult<Value> {
    use Builtin as B;
    match builtin {
        B::Impartial => Ok(Value::Rules(Rc::new(RulesV::new(RulesKind::Impartial(
            args[0].clone(),
        ))))),
        B::Partizan => Ok(Value::Rules(Rc::new(RulesV::new(RulesKind::Partizan(
            args[0].clone(),
            args[1].clone(),
        ))))),
        B::Octal => {
            let digits: Vec<u128> = args[0]
                .as_list()
                .iter()
                .map(|d| u128::try_from(d.as_int()).unwrap_or(u128::MAX))
                .collect();
            let code = OctalCode::try_new(&digits)
                .map_err(|e| err(GrundyErrorKind::Domain, e.to_string()))?;
            if code.digits().is_empty() {
                return Err(err(GrundyErrorKind::Domain, "the octal code has no moves"));
            }
            Ok(Value::Rules(Rc::new(RulesV::new(RulesKind::Octal(code)))))
        }
        B::Value => Ok(Value::Game(value(interp, rules_of(&args[0]), &args[1])?)),
        B::Graph => Ok(Value::Form(graph(interp, rules_of(&args[0]), &args[1])?)),
        B::Sg => Ok(Value::Int(grundy(interp, rules_of(&args[0]), &args[1])?)),
        B::Moves | B::Winning => {
            let rules = rules_of(&args[0]).clone();
            let components = normalize(args[1].as_list().to_vec());
            let who = player(&args[2])?;
            let moves = sum_moves(interp, &rules, &components, who)?;
            if builtin == B::Moves {
                return Ok(Value::list(moves.into_iter().map(Value::list).collect()));
            }
            let mut out = Vec::new();
            for next in moves {
                let wins = if rules.impartial() {
                    let mut x = 0;
                    for c in &next {
                        x ^= grundy(interp, &rules, c)?;
                    }
                    x == 0
                } else {
                    let total = next.iter().try_fold(GameV::integer(0), |acc, c| {
                        value(interp, &rules, c).map(|v| acc.add(&v))
                    })?;
                    let zero = GameV::integer(0);
                    match who {
                        Player::Left => zero.le(&total),
                        Player::Right => total.le(&zero),
                    }
                };
                if wins {
                    out.push(Value::list(next));
                }
            }
            Ok(Value::list(out))
        }
        _ => unreachable!("not a ruleset builtin"),
    }
}
