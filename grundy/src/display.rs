//! Canonical display: every value renders as a program that rebuilds it.
//!
//! Closures render as a sequence binding their captured free variables, then
//! the lambda; recursive groups render as their `=:` system. Claims render as
//! `verify(<witness>)`, so re-evaluating the text re-checks the evidence.
//!
//! A value is a graph, not a tree: a subvalue reached twice is bound once,
//! `(v1 := B(Z, Z); B(v1, v1))`, and a deep spine is cut into bindings, so a
//! display is linear in the value and nests within the parser's limit.
//! Bindings and captures carry a type annotation exactly when their text alone
//! would re-read at a different type.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use ogdoad::games::{Game, PlayConvention, StateVerdict};

use super::algebra::AlgebraV;
use super::core::CtorRef;
use super::eval::value::{Closure, Env, GenericV, Globals, PolyBody, Value};
use super::games::claims::{BoundedV, QuotientV, Statement, WitnessV};
use super::games::form::{
    display_game_element_in_env, game_structural_eq_multiset, structural_game_dyadic,
    structural_game_integer, structural_game_nimber, FormNames, FormV, GameElement,
};
use super::games::game::GameV;
use super::games::rules::{RulesKind, RulesV};
use super::syntax::ast::*;
use super::syntax::unparse::unparse_expr;
use super::types::{show_ty, DataRegistry, Ty, TyCon, VarNames};

/// Text nesting past which a subvalue is bound instead of inlined.
const SPLIT_DEPTH: usize = 256;

/// A repeated subvalue is bound only when its text is longer than this.
const SHARE_MIN_LEN: usize = 40;

/// Re-reads a display at a type: `true` when the text alone has that type.
pub type Reads<'a> = &'a dyn Fn(&str, &Ty) -> bool;

/// The identity of a composite subvalue in memory.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Data(usize),
    Tuple(usize),
    List(usize),
    Some(usize),
    Opaque(usize),
    Game(usize),
    Form(usize),
}

/// A part of a structural shape: a composite's structural id, or an atom's
/// text.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Part {
    Sid(usize),
    Atom(String),
}

/// The structure of a composite subvalue. Equal values have equal shapes, so
/// the bindings a display introduces depend on the value, not on how it was
/// built. Functions and evidence are compared by identity.
#[derive(PartialEq, Eq, Hash)]
enum Shape {
    Data(String, Vec<Part>),
    Tuple(Vec<Part>),
    List(Vec<Part>),
    Some(Part),
    Game(usize),
    Form(Vec<Part>, Vec<Part>),
    Opaque(usize),
}

/// One thing to render: a value, a canonical game, or a finite form.
#[derive(Clone)]
enum Item {
    Value(Value),
    Game(GameV),
    Form(Game),
}

#[derive(Default)]
struct Sharing {
    /// Structural ids of composites met in memory.
    sid_of: HashMap<Node, usize>,
    shapes: HashMap<Shape, usize>,
    /// Each structural id's children, with multiplicity.
    children: Vec<Vec<usize>>,
    /// How often each structural id occurs in the value read as a tree.
    occurrences: Vec<u128>,
    bound: HashMap<usize, String>,
    rendered: HashMap<usize, (String, usize)>,
    lets: Vec<String>,
    reserved: BTreeSet<String>,
    next: usize,
}

/// Display context: data declarations, the names in scope, and the budget.
pub struct Show<'a> {
    /// Data declarations, for constructor names.
    pub data: &'a DataRegistry,
    /// Global names, so Form displays never capture a different binding.
    pub names: FormNames,
    /// Atoms the display may still write.
    pub budget: Cell<u128>,
    /// Whether the display ran out of budget.
    pub exhausted: Cell<bool>,
    reads: Option<Reads<'a>>,
    sharing: RefCell<Sharing>,
}

/// Display a value with no names in scope and no annotations, for messages.
pub fn show_plain(value: &Value, data: &DataRegistry) -> String {
    Show::new(data, FormNames::new(), u128::MAX, None).top(value)
}

fn join<T>(items: impl IntoIterator<Item = T>, f: impl FnMut(T) -> String) -> String {
    items.into_iter().map(f).collect::<Vec<_>>().join(", ")
}

fn is_game_atom(game: &GameV) -> bool {
    game.number().is_some_and(|s| s.as_dyadic().is_some())
        || game.as_nimber().is_some()
        || game.same(&GameV::up(false))
        || game.same(&GameV::up(true))
}

fn form_atom(game: &Game) -> Option<String> {
    if let Some(integer) = structural_game_integer(game) {
        return Some(integer.to_string());
    }
    if let Some(dyadic) = structural_game_dyadic(game) {
        return Some(dyadic);
    }
    if let Some(nimber) = structural_game_nimber(game) {
        return Some(format!("*{nimber}"));
    }
    let up = Game::up();
    if game_structural_eq_multiset(game, &up) {
        return Some("up".to_string());
    }
    if game_structural_eq_multiset(game, &up.neg()) {
        return Some("down".to_string());
    }
    None
}

impl Item {
    /// The item for a value: games and finite forms are their own items.
    fn of(value: &Value) -> Item {
        match value {
            Value::Game(g) => Item::Game(g.clone()),
            Value::Form(FormV(GameElement::Finite(game))) => Item::Form(game.clone()),
            other => Item::Value(other.clone()),
        }
    }

    fn node(&self) -> Option<Node> {
        Some(match self {
            Item::Value(Value::Data(d)) if !d.fields.is_empty() => {
                Node::Data(Rc::as_ptr(d) as *const () as usize)
            }
            Item::Value(Value::Tuple(items)) if !items.is_empty() => {
                Node::Tuple(Rc::as_ptr(items) as usize)
            }
            Item::Value(Value::List(items)) if !items.is_empty() => {
                Node::List(Rc::as_ptr(items) as usize)
            }
            Item::Value(Value::Option(Some(inner))) => Node::Some(Rc::as_ptr(inner) as usize),
            Item::Value(Value::Closure(c)) => Node::Opaque(Rc::as_ptr(c) as *const () as usize),
            Item::Value(Value::Generic(g)) => Node::Opaque(Rc::as_ptr(g) as *const () as usize),
            Item::Value(Value::Rules(r)) => Node::Opaque(Rc::as_ptr(r) as *const () as usize),
            Item::Value(Value::Witness(w)) => Node::Opaque(Rc::as_ptr(w) as *const () as usize),
            Item::Value(Value::Claim(c)) => Node::Opaque(Rc::as_ptr(c) as *const () as usize),
            Item::Value(Value::Bounded(b)) => Node::Opaque(Rc::as_ptr(b) as *const () as usize),
            Item::Value(Value::Quotient(q)) => Node::Opaque(Rc::as_ptr(q) as *const () as usize),
            Item::Game(g) if !is_game_atom(g) => Node::Game(g.id()),
            Item::Form(game) if form_atom(game).is_none() => Node::Form(game.ptr_id()),
            _ => return None,
        })
    }
}

/// The type a value has on its own, when its shape determines it.
pub fn value_type(value: &Value) -> Option<Ty> {
    let con = Ty::con;
    let over = |c: TyCon, arg: TyCon| Ty::Con(c, vec![Ty::con(arg)]);
    Some(match value {
        Value::Int(_) => Ty::int(),
        Value::Bool(_) => Ty::bool(),
        Value::Winner(_) => con(TyCon::Winner),
        Value::Game(_) => con(TyCon::Game),
        Value::Form(_) => con(TyCon::Form),
        Value::Scalar(s) => con(s.con()),
        Value::Poly(p) => over(TyCon::Poly, p.coefficient_con()),
        Value::RatFunc(f) => over(TyCon::RatFunc, f.coefficient_con()),
        Value::Algebra(a) => over(TyCon::Algebra, a.con()),
        Value::Mv(v) => over(TyCon::Mv, v.con()),
        Value::Tuple(items) => Ty::tuple(items.iter().map(value_type).collect::<Option<_>>()?),
        Value::List(items) => Ty::list(value_type(items.first()?)?),
        Value::Option(Some(inner)) => Ty::Con(TyCon::Option, vec![value_type(inner)?]),
        Value::Data(d) => match d.ctor {
            CtorRef::Data(id, _) => con(TyCon::Data(id)),
            CtorRef::Winner(_) => con(TyCon::Winner),
            _ => return None,
        },
        Value::Witness(_) => con(TyCon::Witness),
        Value::Claim(_) => con(TyCon::Claim),
        Value::Bounded(b) => Ty::Con(TyCon::Bounded, vec![value_type(&b.value)?]),
        _ => return None,
    })
}

/// Whether every display of a value of this type re-reads at the type.
fn self_typed(ty: &Ty) -> bool {
    match ty {
        Ty::Con(
            TyCon::Int
            | TyCon::Bool
            | TyCon::Winner
            | TyCon::Data(_)
            | TyCon::Witness
            | TyCon::Claim,
            _,
        ) => true,
        Ty::Con(TyCon::List | TyCon::Tuple(_) | TyCon::Option | TyCon::Bounded, args) => {
            args.iter().all(self_typed)
        }
        _ => false,
    }
}

/// Whether `text` mentions `name` as an identifier.
fn mentions(text: &str, name: &str) -> bool {
    let is_ident = |c: char| c.is_alphanumeric() || c == '_' || c == '\'';
    text.match_indices(name).any(|(at, _)| {
        let before = text[..at].chars().next_back();
        let after = text[at + name.len()..].chars().next();
        !before.is_some_and(is_ident) && !after.is_some_and(is_ident)
    })
}

/// The generator a coefficient type names, if any.
fn generator_of(con: TyCon) -> Option<&'static str> {
    match con {
        TyCon::Fpn(..) => Some("x"),
        _ => None,
    }
}

impl<'a> Show<'a> {
    /// A display context writing at most `budget` atoms; `reads` decides
    /// annotations of bindings and captures.
    pub fn new(
        data: &'a DataRegistry,
        names: FormNames,
        budget: u128,
        reads: Option<Reads<'a>>,
    ) -> Show<'a> {
        Show {
            data,
            names,
            budget: Cell::new(budget),
            exhausted: Cell::new(false),
            reads,
            sharing: RefCell::new(Sharing::default()),
        }
    }

    /// Render a value at statement level. A single game equation stays a
    /// bare `g =: …` statement; a bare field element or polynomial is left
    /// for the caller to annotate.
    pub fn top(&self, value: &Value) -> String {
        if let Value::Form(f @ FormV(GameElement::Graph(_))) = value {
            return display_game_element_in_env(&f.0, &self.names);
        }
        self.analyze(value);
        let text = match value {
            Value::Scalar(_) | Value::Poly(_) | Value::RatFunc(_) => self.atom_text(value),
            other => self.render(&Item::of(other)).0,
        };
        let lets = std::mem::take(&mut self.sharing.borrow_mut().lets);
        if lets.is_empty() {
            text
        } else {
            format!("({}; {text})", lets.join("; "))
        }
    }

    fn spend(&self) -> bool {
        if self.exhausted.get() {
            return false;
        }
        match self.budget.get().checked_sub(1) {
            Some(left) => {
                self.budget.set(left);
                true
            }
            None => {
                self.exhausted.set(true);
                false
            }
        }
    }

    // ------------------------------------------------------------ sharing

    /// Give every composite subvalue a structural id, count how often each
    /// occurs in the value read as a tree, and reserve the names closures
    /// bind, so fresh binding names never collide with them.
    fn analyze(&self, root: &Value) {
        enum Step {
            Enter(Item),
            Exit(Item, Node),
        }
        // Atom texts render through `self`, so the state is held outside it.
        let mut sharing = std::mem::take(&mut *self.sharing.borrow_mut());
        sharing.reserved.extend(self.names.keys().cloned());
        let mut stack = vec![Step::Enter(Item::of(root))];
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(item) => {
                    let Some(node) = item.node() else {
                        continue;
                    };
                    if sharing.sid_of.contains_key(&node) {
                        continue;
                    }
                    let mut kids = Vec::new();
                    self.children(&item, &mut sharing.reserved, &mut |child| kids.push(child));
                    stack.push(Step::Exit(item, node));
                    stack.extend(kids.into_iter().map(Step::Enter));
                }
                Step::Exit(item, node) => {
                    if sharing.sid_of.contains_key(&node) {
                        continue;
                    }
                    let mut kids = Vec::new();
                    self.children(&item, &mut BTreeSet::new(), &mut |child| kids.push(child));
                    let parts: Vec<Part> = kids
                        .iter()
                        .map(|kid| match kid.node() {
                            Some(n) => Part::Sid(sharing.sid_of[&n]),
                            None => Part::Atom(self.render_body(kid).0),
                        })
                        .collect();
                    let shape = self.shape(&item, &node, parts.clone());
                    let next = sharing.shapes.len();
                    let sid = *sharing.shapes.entry(shape).or_insert(next);
                    if sid == next {
                        sharing.children.push(
                            parts
                                .iter()
                                .filter_map(|part| match part {
                                    Part::Sid(sid) => Some(*sid),
                                    Part::Atom(_) => None,
                                })
                                .collect(),
                        );
                    }
                    sharing.sid_of.insert(node, sid);
                }
            }
        }
        // Ids are assigned children first, so parents come later.
        let mut occurrences = vec![0u128; sharing.children.len()];
        if let Some(root) = Item::of(root).node() {
            occurrences[sharing.sid_of[&root]] = 1;
        }
        for sid in (0..occurrences.len()).rev() {
            for &child in &sharing.children[sid] {
                occurrences[child] = occurrences[child].saturating_add(occurrences[sid]);
            }
        }
        sharing.occurrences = occurrences;
        *self.sharing.borrow_mut() = sharing;
    }

    fn shape(&self, item: &Item, node: &Node, parts: Vec<Part>) -> Shape {
        match item {
            Item::Game(g) => Shape::Game(g.id()),
            Item::Form(game) => {
                let split = game.left().len();
                let mut parts = parts;
                let right = parts.split_off(split);
                Shape::Form(parts, right)
            }
            Item::Value(Value::Data(d)) => Shape::Data(ctor_name(&d.ctor, self.data), parts),
            Item::Value(Value::Tuple(_)) => Shape::Tuple(parts),
            Item::Value(Value::List(_)) => Shape::List(parts),
            Item::Value(Value::Option(_)) => {
                Shape::Some(parts.into_iter().next().expect("one inner value"))
            }
            _ => match node {
                Node::Opaque(ptr) => Shape::Opaque(*ptr),
                _ => unreachable!("composite shapes are listed"),
            },
        }
    }

    /// The subitems a rendering visits, mirroring `render_body`.
    fn children(&self, item: &Item, reserved: &mut BTreeSet<String>, push: &mut dyn FnMut(Item)) {
        let mut values = |values: &mut dyn Iterator<Item = &Value>| {
            for v in values {
                push(Item::of(v));
            }
        };
        match item {
            Item::Game(g) => {
                if !is_game_atom(g) {
                    for option in g.lefts().into_iter().chain(g.rights()) {
                        push(Item::Game(option));
                    }
                }
            }
            Item::Form(game) => {
                if form_atom(game).is_none() {
                    for option in game.left().iter().chain(game.right()) {
                        push(Item::Form(option.clone()));
                    }
                }
            }
            Item::Value(value) => match value {
                Value::Tuple(items) | Value::List(items) => values(&mut items.iter()),
                Value::Data(d) => values(&mut d.fields.iter()),
                Value::Option(Some(inner)) => values(&mut std::iter::once(&**inner)),
                Value::Closure(_) | Value::Generic(_) => {
                    let (captures, bound) = self.captures(value);
                    reserved.extend(captures.iter().map(|(name, _)| name.clone()));
                    reserved.extend(bound);
                    values(&mut captures.iter().map(|(_, v)| v));
                }
                Value::Rules(rules) => match &rules.kind {
                    RulesKind::Impartial(f) => values(&mut std::iter::once(f)),
                    RulesKind::Partizan(l, r) => values(&mut [l, r].into_iter()),
                    RulesKind::Octal(_) => {}
                },
                Value::Witness(w) => self.witness_values(w, &mut |v| push(Item::of(&v))),
                Value::Claim(c) => self.witness_values(&c.witness, &mut |v| push(Item::of(&v))),
                Value::Bounded(b) => values(&mut std::iter::once(&b.value)),
                Value::Quotient(q) => {
                    values(&mut q.classes.iter().flatten().flatten());
                }
                Value::Algebra(a) => self.metric_values(a, &mut |v| push(Item::of(&v))),
                Value::Mv(v) => {
                    if let Some(alg) = v.algebra() {
                        self.metric_values(&alg, &mut |v| push(Item::of(&v)));
                    }
                }
                _ => {}
            },
        }
    }

    fn witness_values(&self, witness: &WitnessV, push: &mut dyn FnMut(Value)) {
        match witness {
            WitnessV::Outcome { .. } => {}
            WitnessV::Grundy { rules, root, table } => {
                push(rules.clone());
                push(root.clone());
                for (p, _, _) in table {
                    push(p.clone());
                }
            }
            WitnessV::Periodic { rules, .. } => push(rules.clone()),
            WitnessV::Separation {
                rules,
                p,
                q,
                context,
            } => {
                push(rules.clone());
                for v in p.iter().chain(q).chain(context) {
                    push(v.clone());
                }
            }
        }
    }

    fn metric_values(&self, alg: &AlgebraV, push: &mut dyn FnMut(Value)) {
        let (q, b, a) = alg.metric_values();
        for v in q {
            push(v);
        }
        for (_, v) in b.into_iter().chain(a) {
            push(v);
        }
    }

    fn fresh(&self) -> String {
        let mut sharing = self.sharing.borrow_mut();
        loop {
            sharing.next += 1;
            let name = format!("v{}", sharing.next);
            if !sharing.reserved.contains(&name) {
                return name;
            }
        }
    }

    /// `text`, annotated with the value's type when the text alone would
    /// re-read at a different type, in the scope of the bindings so far.
    fn annotated(&self, text: String, value: Option<&Value>) -> String {
        let (Some(reads), Some(ty)) = (self.reads, value.and_then(value_type)) else {
            return text;
        };
        if self_typed(&ty) {
            return text;
        }
        let lets = self.sharing.borrow().lets.join("; ");
        let probe = if lets.is_empty() {
            text.clone()
        } else {
            format!("({lets}; {text})")
        };
        if reads(&probe, &ty) {
            return text;
        }
        let ty = show_ty(&ty, self.data, &mut VarNames::default());
        if starts_open(&text) {
            format!("({text}) : {ty}")
        } else {
            format!("{text} : {ty}")
        }
    }

    // ---------------------------------------------------------- rendering

    /// Render an item: a bound name if a long text of it repeats or it is
    /// deep, else its text. Returns the text and its nesting depth.
    fn render(&self, item: &Item) -> (String, usize) {
        if !self.spend() {
            return (String::new(), 0);
        }
        let Some(sid) = item
            .node()
            .and_then(|node| self.sharing.borrow().sid_of.get(&node).copied())
        else {
            return self.render_body(item);
        };
        {
            let sharing = self.sharing.borrow();
            if let Some(name) = sharing.bound.get(&sid) {
                return (name.clone(), 0);
            }
            if let Some(done) = sharing.rendered.get(&sid) {
                return done.clone();
            }
        }
        let (text, depth) = self.render_body(item);
        let repeated = self
            .sharing
            .borrow()
            .occurrences
            .get(sid)
            .copied()
            .unwrap_or(0)
            > 1;
        if !(repeated && text.len() > SHARE_MIN_LEN) && depth <= SPLIT_DEPTH {
            self.sharing
                .borrow_mut()
                .rendered
                .insert(sid, (text.clone(), depth));
            return (text, depth);
        }
        let value = match item {
            Item::Value(v) => v.clone(),
            Item::Game(g) => Value::Game(g.clone()),
            Item::Form(game) => Value::Form(FormV::finite(game.clone())),
        };
        let rhs = self.annotated(text, Some(&value));
        let name = self.fresh();
        let mut sharing = self.sharing.borrow_mut();
        sharing.lets.push(format!("{name} := {rhs}"));
        sharing.bound.insert(sid, name.clone());
        (name, 0)
    }

    fn nested(&self, value: &Value) -> (String, usize) {
        self.render(&Item::of(value))
    }

    fn many<'v>(&self, values: impl IntoIterator<Item = &'v Value>) -> (String, usize) {
        let mut depth = 0;
        let text = join(values, |v| {
            let (text, d) = self.nested(v);
            depth = depth.max(d);
            text
        });
        (text, depth)
    }

    fn render_body(&self, item: &Item) -> (String, usize) {
        match item {
            Item::Game(g) => self.game(g),
            Item::Form(game) => self.form(game),
            Item::Value(value) => self.value_body(value),
        }
    }

    fn game(&self, g: &GameV) -> (String, usize) {
        if let Some(surreal) = g.number() {
            if let Some((num, k)) = surreal.as_dyadic() {
                let text = if k == 0 {
                    num.to_string()
                } else {
                    format!("{num}/{}", 1u128 << k)
                };
                return (text, 0);
            }
        }
        if let Some(n) = g.as_nimber() {
            return (format!("*{n}"), 0);
        }
        if g.same(&GameV::up(false)) {
            return ("up".to_string(), 0);
        }
        if g.same(&GameV::up(true)) {
            return ("down".to_string(), 0);
        }
        let side = |options: Vec<GameV>| {
            let mut depth = 0;
            let text = join(options, |o| {
                let (text, d) = self.render(&Item::Game(o));
                depth = depth.max(d);
                text
            });
            (text, depth)
        };
        let (left, dl) = side(g.lefts());
        let (right, dr) = side(g.rights());
        (braces(&left, &right, "{|}"), 1 + dl.max(dr))
    }

    fn form(&self, game: &Game) -> (String, usize) {
        if let Some(atom) = form_atom(game) {
            return (atom, 0);
        }
        let side = |options: &[Game]| {
            let mut depth = 0;
            let text = join(options, |o| {
                let (text, d) = self.render(&Item::Form(o.clone()));
                depth = depth.max(d);
                text
            });
            (text, depth)
        };
        let (left, dl) = side(game.left());
        let (right, dr) = side(game.right());
        (braces(&left, &right, "0"), 1 + dl.max(dr))
    }

    /// A field element or polynomial; nested ones that mention their
    /// generator bind it with their own annotation.
    fn atom_text(&self, value: &Value) -> String {
        match value {
            Value::Scalar(s) => s.to_string(),
            Value::Poly(p) => p.to_string(),
            Value::RatFunc(f) => f.to_string(),
            _ => unreachable!("an algebra atom"),
        }
    }

    fn self_annotated(&self, value: &Value) -> String {
        let text = self.atom_text(value);
        let generator = match value {
            Value::Scalar(s) => generator_of(s.con()),
            _ => Some("t"),
        };
        match (generator, value_type(value)) {
            (Some(name), Some(ty)) if mentions(&text, name) => format!(
                "({text} : {})",
                show_ty(&ty, self.data, &mut VarNames::default())
            ),
            _ => text,
        }
    }

    fn value_body(&self, value: &Value) -> (String, usize) {
        match value {
            Value::Int(n) => (n.to_string(), 0),
            Value::Bool(b) => (b.to_string(), 0),
            Value::Tuple(items) => {
                let (text, depth) = self.many(items.iter());
                (format!("({text})"), depth + 1)
            }
            Value::List(items) => {
                let (text, depth) = self.many(items.iter());
                (format!("[{text}]"), depth + 1)
            }
            Value::Data(value) => {
                let name = ctor_name(&value.ctor, self.data);
                if value.fields.is_empty() {
                    (name, 0)
                } else {
                    let (text, depth) = self.many(&value.fields);
                    (format!("{name}({text})"), depth + 1)
                }
            }
            Value::Winner(w) => (["Left", "Right", "Draw"][*w as usize].to_string(), 0),
            Value::Option(None) => ("None".to_string(), 0),
            Value::Option(Some(inner)) => {
                let (text, depth) = self.nested(inner);
                (format!("Some({text})"), depth + 1)
            }
            Value::Game(g) => self.game(g),
            Value::Form(FormV(GameElement::Finite(game))) => self.form(game),
            Value::Form(f) => {
                let text = display_game_element_in_env(&f.0, &self.names);
                // A bare single equation is a statement; nested, it names its root.
                let text = match text.split_once(" =: ") {
                    Some((root, _)) if !text.starts_with('(') => format!("({text}; {root})"),
                    _ => text,
                };
                (text, 1)
            }
            Value::Scalar(_) | Value::Poly(_) | Value::RatFunc(_) => {
                (self.self_annotated(value), 0)
            }
            Value::Algebra(a) => (self.algebra(a), 1),
            Value::Mv(v) => (self.multivector(v), 1),
            Value::Closure(_) | Value::Generic(_) => self.function(value),
            Value::Builtin(builtin, _) => (builtin.name().to_string(), 0),
            Value::CtorFn(ctor) => (ctor_name(ctor, self.data), 0),
            Value::Rules(rules) => self.rules(rules),
            Value::Witness(w) => (self.witness(w), 1),
            Value::Claim(c) => (
                format!(
                    "verify({}) /* claim: {} */",
                    self.witness(&c.witness),
                    self.statement(&c.statement)
                ),
                1,
            ),
            Value::Bounded(b) => (self.bounded(b), 1),
            Value::Quotient(q) => (self.quotient(q), 1),
        }
    }

    fn algebra(&self, alg: &AlgebraV) -> String {
        let (q, b, a) = alg.metric_values();
        let q = format!("[{}]", self.many(&q).0);
        if b.is_empty() && a.is_empty() {
            return format!("clifford({q})");
        }
        let pairs = |pairs: &[((usize, usize), Value)]| {
            format!(
                "[{}]",
                join(pairs, |((i, j), v)| format!(
                    "(({i}, {j}), {})",
                    self.nested(v).0
                ))
            )
        };
        format!("clifford_metric({q}, {}, {})", pairs(&b), pairs(&a))
    }

    /// A multivector that has met an algebra keeps it: grade-zero values are
    /// written `s + (e0 - e0)` so that re-reading attaches the same algebra.
    fn multivector(&self, v: &super::algebra::MvV) -> String {
        let Some(alg) = v.algebra() else {
            return v.to_string();
        };
        let dim = alg.dim();
        let basis = join(0..dim, |i| format!("e{i}"));
        let body = if v.has_blades() {
            v.to_string()
        } else {
            // `e0 - e0` is zero in the algebra for every coefficient type.
            let attach = if dim == 0 {
                "vector(alg, [])"
            } else {
                "e0 - e0"
            };
            if v.is_zero() {
                attach.to_string()
            } else {
                format!("{v} + ({attach})")
            }
        };
        let generator = generator_of(v.con())
            .filter(|name| mentions(&body, name))
            .map(|name| {
                format!(
                    "{name} := ({name} : {}); ",
                    show_ty(&Ty::con(v.con()), self.data, &mut VarNames::default())
                )
            })
            .unwrap_or_default();
        format!(
            "({generator}alg := {}; [{basis}] := basis(alg); {body})",
            self.algebra(&alg)
        )
    }

    fn rules(&self, rules: &RulesV) -> (String, usize) {
        match &rules.kind {
            RulesKind::Impartial(f) => {
                let (f, depth) = self.nested(f);
                (format!("impartial({f})"), depth + 1)
            }
            RulesKind::Partizan(l, r) => {
                let ((l, dl), (r, dr)) = (self.nested(l), self.nested(r));
                (format!("partizan({l}, {r})"), dl.max(dr) + 1)
            }
            RulesKind::Octal(code) => (
                format!("octal([{}])", join(code.digits(), |d| d.to_string())),
                1,
            ),
        }
    }

    fn witness(&self, witness: &WitnessV) -> String {
        match witness {
            WitnessV::Outcome {
                left,
                right,
                convention,
                labels,
            } => {
                let adjacency = |rows: &[Vec<usize>]| {
                    format!(
                        "[{}]",
                        join(rows, |row| format!("[{}]", join(row, |n| n.to_string())))
                    )
                };
                let labels = join(labels, |label| {
                    let verdict = match label.verdict {
                        StateVerdict::Loss => 0,
                        StateVerdict::Win => 1,
                        StateVerdict::Draw => 2,
                    };
                    let chosen = label.chosen.map_or("-1".to_string(), |c| c.to_string());
                    format!("({verdict}, {}, {chosen})", label.rank)
                });
                format!(
                    "outcome_witness({}, {}, {}, [{labels}])",
                    adjacency(left),
                    adjacency(right),
                    *convention == PlayConvention::Misere
                )
            }
            WitnessV::Grundy { rules, root, table } => format!(
                "sg_witness({}, {}, [{}])",
                self.nested(rules).0,
                self.nested(root).0,
                join(table, |(p, g, r)| format!(
                    "({}, {g}, {r})",
                    self.nested(p).0
                ))
            ),
            WitnessV::Periodic {
                rules,
                preperiod,
                period,
            } => format!(
                "periodic_witness({}, {preperiod}, {period})",
                self.nested(rules).0
            ),
            WitnessV::Separation {
                rules,
                p,
                q,
                context,
            } => format!(
                "separation_witness({}, [{}], [{}], [{}])",
                self.nested(rules).0,
                self.many(p).0,
                self.many(q).0,
                self.many(context).0
            ),
        }
    }

    fn statement(&self, statement: &Statement) -> String {
        match statement {
            Statement::Outcome(cell) => {
                let name = |m: Mover| match m {
                    Mover::Left => "Left",
                    Mover::Right => "Right",
                    Mover::Draw => "Draw",
                };
                format!(
                    "outcome ({}, {})",
                    name(cell.left_first),
                    name(cell.right_first)
                )
            }
            Statement::Grundy(g) => format!("sg = {g}"),
            Statement::Periodic { preperiod, period } => {
                format!("every heap from {preperiod} on repeats with period {period}")
            }
            Statement::Separated => "misère-distinguishable".to_string(),
        }
    }

    fn bounded(&self, bounded: &BoundedV) -> String {
        format!(
            "bounded({}, {})",
            self.nested(&bounded.value).0,
            bounded.samples
        )
    }

    fn quotient(&self, q: &QuotientV) -> String {
        let classes = format!(
            "[{}]",
            join(&q.classes, |class| format!(
                "[{}]",
                join(class, |member| format!("[{}]", self.many(member).0))
            ))
        );
        let p = format!("[{}]", join(&q.p, |c| c.to_string()));
        let table = match &q.table {
            None => "None".to_string(),
            Some(rows) => format!(
                "Some([{}])",
                join(rows, |row| format!("[{}]", join(row, |c| c.to_string())))
            ),
        };
        format!("quotient({classes}, {p}, {table})")
    }

    // ---------------------------------------------------------- functions

    /// The sources, bound names, captured environment, and body of a
    /// closure or generic function.
    fn function_parts<'v>(&self, value: &'v Value) -> Option<FunctionParts<'v>> {
        match value {
            Value::Closure(closure) => Some(self.closure_parts(closure)),
            Value::Generic(generic) => self.generic_parts(generic),
            _ => None,
        }
    }

    fn closure_parts<'v>(&self, closure: &'v Closure) -> FunctionParts<'v> {
        match &closure.rec {
            None => {
                let lambda = &closure.lam.source;
                FunctionParts {
                    sources: vec![lambda],
                    bound: Vec::new(),
                    env: &closure.env,
                    globals: &closure.globals,
                    body: unparse_expr(lambda),
                }
            }
            Some((group, index)) => {
                let sources: Vec<&Expr> = group.lams.iter().map(|lam| &lam.source).collect();
                let body = equations(&group.names, &sources, *index);
                FunctionParts {
                    sources,
                    bound: group.names.clone(),
                    env: &group.env,
                    globals: &group.globals,
                    body,
                }
            }
        }
    }

    fn generic_parts<'v>(&self, generic: &'v GenericV) -> Option<FunctionParts<'v>> {
        match &generic.body {
            PolyBody::Expr(super::core::Core::Lambda(lam)) => Some(FunctionParts {
                sources: vec![&lam.source],
                bound: Vec::new(),
                env: &generic.env,
                globals: &generic.globals,
                body: unparse_expr(&lam.source),
            }),
            PolyBody::Expr(_) => None,
            PolyBody::Group { names, lams, index } => {
                let sources: Vec<&Expr> = lams.iter().map(|lam| &lam.source).collect();
                let body = equations(names, &sources, *index);
                Some(FunctionParts {
                    sources,
                    bound: names.clone(),
                    env: &generic.env,
                    globals: &generic.globals,
                    body,
                })
            }
        }
    }

    /// The captured free variables of a function, by name, and the names
    /// it binds itself.
    fn captures(&self, value: &Value) -> (Vec<(String, Value)>, Vec<String>) {
        let Some(FunctionParts {
            sources,
            bound,
            env,
            globals,
            ..
        }) = self.function_parts(value)
        else {
            return (Vec::new(), Vec::new());
        };
        let mut free = BTreeSet::new();
        for source in &sources {
            free_vars(source, &mut Vec::new(), &mut free);
        }
        for name in &bound {
            free.remove(name);
        }
        let captures = free
            .into_iter()
            .filter_map(|name| {
                let value = env.get(&name).or_else(|| globals.get(&name))?.clone();
                Some((name, value))
            })
            .collect();
        (captures, bound)
    }

    fn function(&self, value: &Value) -> (String, usize) {
        let Some(FunctionParts { bound, body, .. }) = self.function_parts(value) else {
            return ("<generic>".to_string(), 0);
        };
        let (captures, _) = self.captures(value);
        let (lets, depth) = self.capture_lets(captures);
        if lets.is_empty() && bound.is_empty() {
            return (body, 1);
        }
        let mut parts = lets;
        parts.push(body);
        (format!("({})", parts.join("; ")), depth + 1)
    }

    /// Capture bindings in an order where every builtin a capture names is
    /// read before another capture shadows it. A cycle of such shadowings
    /// reads the builtin into a fresh name first.
    fn capture_lets(&self, captures: Vec<(String, Value)>) -> (Vec<String>, usize) {
        let builtin_name = |value: &Value| match value {
            Value::Builtin(b, _) => Some(b.name()),
            _ => None,
        };
        let mut pending: Vec<(String, Value, Option<String>)> =
            captures.into_iter().map(|(n, v)| (n, v, None)).collect();
        let mut lets = Vec::new();
        let mut depth = 0;
        while !pending.is_empty() {
            // A capture may be bound once no pending capture still needs
            // the builtin its name shadows.
            let ready = (0..pending.len()).find(|&i| {
                let name = pending[i].0.as_str();
                !pending.iter().enumerate().any(|(j, (_, v, alias))| {
                    j != i && alias.is_none() && builtin_name(v) == Some(name)
                })
            });
            let index = match ready {
                Some(index) => index,
                None => {
                    // Break the cycle: read the shadowed builtin into a
                    // fresh name, and let its readers use that name.
                    let name = pending[0].0.clone();
                    let alias = self.fresh();
                    lets.push(format!("{alias} := {name}"));
                    for entry in pending.iter_mut() {
                        if entry.2.is_none() && builtin_name(&entry.1) == Some(name.as_str()) {
                            entry.2 = Some(alias.clone());
                        }
                    }
                    continue;
                }
            };
            let (name, value, alias) = pending.remove(index);
            let text = match alias {
                Some(alias) => alias,
                None => {
                    let (text, d) = self.nested(&value);
                    depth = depth.max(d);
                    self.annotated_in(text, &value, &lets)
                }
            };
            lets.push(format!("{name} := {text}"));
        }
        (lets, depth)
    }

    /// Annotate a capture, reading it after the captures bound before it.
    fn annotated_in(&self, text: String, value: &Value, before: &[String]) -> String {
        if before.is_empty() {
            return self.annotated(text, Some(value));
        }
        let (Some(reads), Some(ty)) = (self.reads, value_type(value)) else {
            return text;
        };
        if self_typed(&ty) {
            return text;
        }
        let mut scope = self.sharing.borrow().lets.clone();
        scope.extend(before.iter().cloned());
        if reads(&format!("({}; {text})", scope.join("; ")), &ty) {
            return text;
        }
        let ty = show_ty(&ty, self.data, &mut VarNames::default());
        if starts_open(&text) {
            format!("({text}) : {ty}")
        } else {
            format!("{text} : {ty}")
        }
    }
}

/// What a function's display is built from.
struct FunctionParts<'v> {
    sources: Vec<&'v Expr>,
    bound: Vec<String>,
    env: &'v Env,
    globals: &'v Globals,
    body: String,
}

fn braces(left: &str, right: &str, empty: &str) -> String {
    match (left.is_empty(), right.is_empty()) {
        (true, true) => empty.to_string(),
        (false, true) => format!("{{{left} |}}"),
        (true, false) => format!("{{| {right}}}"),
        (false, false) => format!("{{{left} | {right}}}"),
    }
}

fn equations(names: &[String], sources: &[&Expr], index: usize) -> String {
    let equations = names
        .iter()
        .zip(sources)
        .map(|(name, source)| format!("{name} =: {}", unparse_expr(source)))
        .collect::<Vec<_>>()
        .join("; ");
    format!("{equations}; {}", names[index])
}

/// Whether an annotation after this text would attach to its trailing part:
/// a lambda body or an `else` branch.
pub fn starts_open(text: &str) -> bool {
    matches!(
        super::syntax::parse::parse_expr(text).map(|e| e.kind),
        Ok(ExprKind::Lambda(..) | ExprKind::If(..))
    )
}

/// The surface name of a constructor.
pub fn ctor_name(ctor: &CtorRef, data: &DataRegistry) -> String {
    match ctor {
        CtorRef::Data(id, index) => data.get(*id).ctors[*index as usize].0.clone(),
        CtorRef::Winner(w) => ["Left", "Right", "Draw"][*w as usize].to_string(),
        CtorRef::Some => "Some".to_string(),
        CtorRef::None => "None".to_string(),
    }
}

/// Collect the free variables of an expression.
pub fn free_vars(expr: &Expr, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    let with =
        |names: Vec<String>, bound: &mut Vec<String>, f: &mut dyn FnMut(&mut Vec<String>)| {
            let depth = bound.len();
            bound.extend(names);
            f(bound);
            bound.truncate(depth);
        };
    match &expr.kind {
        ExprKind::Var(name) => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        ExprKind::Int(_)
        | ExprKind::Frac(..)
        | ExprKind::Star(_)
        | ExprKind::Omega
        | ExprKind::Bool(_)
        | ExprKind::Up
        | ExprKind::Down
        | ExprKind::Con(_) => {}
        ExprKind::Tuple(items) => items.iter().for_each(|e| free_vars(e, bound, out)),
        ExprKind::List(items) => items.iter().for_each(|item| free_item(item, bound, out)),
        ExprKind::Form { left, right } => left
            .iter()
            .chain(right)
            .for_each(|item| free_item(item, bound, out)),
        ExprKind::Comprehension(head, clauses) => {
            let depth = bound.len();
            for clause in clauses {
                match clause {
                    Clause::For(pat, source) => {
                        free_vars(source, bound, out);
                        bound.extend(pat.binders().into_iter().map(String::from));
                    }
                    Clause::If(guard) => free_vars(guard, bound, out),
                }
            }
            free_vars(head, bound, out);
            bound.truncate(depth);
        }
        ExprKind::Range { lo, hi, .. } => {
            free_vars(lo, bound, out);
            free_vars(hi, bound, out);
        }
        ExprKind::Call(callee, args) => {
            free_vars(callee, bound, out);
            args.iter().for_each(|a| free_vars(a, bound, out));
        }
        ExprKind::Index(a, b) | ExprKind::Binary(_, a, b) | ExprKind::Relation(_, a, b) => {
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
        ExprKind::Lambda(params, body) => {
            let names = params
                .iter()
                .flat_map(|p| p.pat.binders().into_iter().map(String::from))
                .collect();
            with(names, bound, &mut |bound| free_vars(body, bound, out));
        }
        ExprKind::Unary(_, a) => free_vars(a, bound, out),
        ExprKind::If(c, a, b) => {
            free_vars(c, bound, out);
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
        ExprKind::Match(scrutinee, arms) => {
            free_vars(scrutinee, bound, out);
            for (pat, body) in arms {
                let names = pat.binders().into_iter().map(String::from).collect();
                with(names, bound, &mut |bound| free_vars(body, bound, out));
            }
        }
        ExprKind::Block(bindings, body) => {
            let depth = bound.len();
            let mut index = 0;
            while index < bindings.len() {
                if bindings[index].kind == BindKind::Rec {
                    let mut end = index;
                    while end < bindings.len() && bindings[end].kind == BindKind::Rec {
                        bound.extend(bindings[end].pat.binders().into_iter().map(String::from));
                        end += 1;
                    }
                    for binding in &bindings[index..end] {
                        free_vars(&binding.expr, bound, out);
                    }
                    index = end;
                } else {
                    free_vars(&bindings[index].expr, bound, out);
                    bound.extend(bindings[index].pat.binders().into_iter().map(String::from));
                    index += 1;
                }
            }
            free_vars(body, bound, out);
            bound.truncate(depth);
        }
        ExprKind::Annot(inner, ty) => {
            let generator = match &ty.kind {
                TypeKind::PolyRing(_) | TypeKind::RatField(_) => Some("t"),
                TypeKind::Named(name, args)
                    if args.is_empty()
                        && matches!(name.as_str(), "F4" | "F8" | "F16" | "F9" | "F27" | "F25") =>
                {
                    Some("x")
                }
                _ => None,
            };
            match generator {
                Some(name) => with(vec![name.to_string()], bound, &mut |bound| {
                    free_vars(inner, bound, out)
                }),
                None => free_vars(inner, bound, out),
            }
        }
    }
}

fn free_item(item: &Item_, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    match item {
        Item_::One(expr) | Item_::Splice(expr) => free_vars(expr, bound, out),
    }
}

use super::syntax::ast::Item as Item_;
