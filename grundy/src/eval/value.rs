//! Runtime values, environments, and closures.

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;

use super::super::algebra::{AlgebraV, MvV, PolyV, RatFuncV, ScalarV};
use super::super::builtins::Builtin;
use super::super::core::{Core, CtorRef, Lam};
use super::super::games::claims::{BoundedV, ClaimV, QuotientV, WitnessV};
use super::super::games::form::FormV;
use super::super::games::game::GameV;
use super::super::games::rules::RulesV;
use super::super::types::{Ty, TyVar};

/// A runtime type environment: the instantiation of enclosing type
/// parameters.
pub type TEnv = Rc<BTreeMap<TyVar, Ty>>;

/// Values.
#[derive(Clone)]
pub enum Value {
    /// An integer.
    Int(i128),
    /// A Boolean.
    Bool(bool),
    /// A tuple.
    Tuple(Rc<Seq>),
    /// A list.
    List(Rc<Seq>),
    /// A user data value.
    Data(Rc<DataV>),
    /// `Left` (0), `Right` (1), or `Draw` (2).
    Winner(u8),
    /// `Some(v)` or `None`.
    Option(Option<Rc<Value>>),
    /// A closure.
    Closure(Rc<Closure>),
    /// A generalized binding awaiting instantiation.
    Generic(Rc<GenericV>),
    /// A builtin at an instantiation.
    Builtin(Builtin, Rc<[Ty]>),
    /// A constructor used as a function.
    CtorFn(CtorRef),
    /// A short game value.
    Game(GameV),
    /// A presented game.
    Form(FormV),
    /// A ruleset.
    Rules(Rc<RulesV>),
    /// A scalar: nimber, ordinal, surreal, omnific, or finite-field element.
    Scalar(ScalarV),
    /// A polynomial.
    Poly(PolyV),
    /// A rational function.
    RatFunc(RatFuncV),
    /// A Clifford algebra.
    Algebra(AlgebraV),
    /// A multivector.
    Mv(MvV),
    /// Evidence awaiting verification.
    Witness(Rc<WitnessV>),
    /// A verified claim.
    Claim(Rc<ClaimV>),
    /// A bounded answer.
    Bounded(Rc<BoundedV>),
    /// A sampled quotient.
    Quotient(Rc<QuotientV>),
}

/// How deeply data, closures, and recursive groups may nest: every walk
/// over a value recurses on this depth.
pub const MAX_VALUE_DEPTH: u32 = 1 << 14;

/// The elements of a tuple or list, with their nesting depth.
pub struct Seq {
    items: Box<[Value]>,
    depth: u32,
}

impl Seq {
    fn new(items: Vec<Value>) -> Seq {
        let depth = items
            .iter()
            .map(Value::depth)
            .max()
            .unwrap_or(0)
            .saturating_add(1);
        Seq {
            items: items.into_boxed_slice(),
            depth,
        }
    }
}

impl std::ops::Deref for Seq {
    type Target = [Value];

    fn deref(&self) -> &[Value] {
        &self.items
    }
}

/// A constructed user data value.
pub struct DataV {
    /// Its constructor.
    pub ctor: CtorRef,
    /// Its fields.
    pub fields: Vec<Value>,
    /// Its nesting depth.
    pub depth: u32,
}

/// A closure: a lambda with its captured environment.
pub struct Closure {
    /// The lambda.
    pub lam: Rc<Lam>,
    /// Captured local bindings.
    pub env: Env,
    /// Captured globals.
    pub globals: Globals,
    /// Captured type instantiation.
    pub tenv: TEnv,
    /// For a member of a recursive group: the group and the member index.
    pub rec: Option<(Rc<RecGroup>, usize)>,
    /// Its nesting depth through captured values.
    pub depth: u32,
}

/// A recursive function group, holding its environment but never itself.
pub struct RecGroup {
    /// Member names.
    pub names: Vec<String>,
    /// Member lambdas.
    pub lams: Vec<Rc<Lam>>,
    /// The environment the group was defined in.
    pub env: Env,
    /// The globals it captured.
    pub globals: Globals,
    /// The instantiation of its type parameters.
    pub tenv: TEnv,
    /// Its nesting depth through captured values.
    pub depth: u32,
}

/// A generalized binding: its right-hand side is re-evaluated at each
/// instantiation of its type parameters.
pub struct GenericV {
    /// Type parameters.
    pub tparams: Vec<TyVar>,
    /// What to instantiate.
    pub body: PolyBody,
    /// The defining environment.
    pub env: Env,
    /// The globals it captured.
    pub globals: Globals,
    /// The enclosing instantiation.
    pub tenv: TEnv,
    /// Its nesting depth through captured values.
    pub depth: u32,
}

/// The two generalized forms.
pub enum PolyBody {
    /// A non-recursive right-hand side (a lambda, possibly wrapped).
    Expr(Rc<Core>),
    /// A member of a recursive function group.
    Group {
        /// Member names.
        names: Vec<String>,
        /// Member lambdas.
        lams: Vec<Rc<Lam>>,
        /// This member's index.
        index: usize,
    },
}

/// Global bindings, captured by closures at definition time.
pub type Globals = Rc<BTreeMap<String, Value>>;

/// A persistent environment of local bindings.
#[derive(Clone, Default)]
pub struct Env(Option<Rc<Frame>>);

struct Frame {
    name: String,
    value: Value,
    next: Env,
}

impl Env {
    /// The empty environment.
    pub fn new() -> Env {
        Env(None)
    }

    /// Extend with one binding.
    pub fn bind(&self, name: impl Into<String>, value: Value) -> Env {
        Env(Some(Rc::new(Frame {
            name: name.into(),
            value,
            next: self.clone(),
        })))
    }

    /// Look a name up.
    pub fn get(&self, name: &str) -> Option<&Value> {
        let mut current = &self.0;
        while let Some(frame) = current {
            if frame.name == name {
                return Some(&frame.value);
            }
            current = &frame.next.0;
        }
        None
    }
}

impl Drop for Env {
    fn drop(&mut self) {
        // Unlink long chains iteratively so dropping never recurses deeply.
        let mut current = self.0.take();
        while let Some(frame) = current {
            match Rc::try_unwrap(frame) {
                Ok(mut frame) => current = frame.next.0.take(),
                Err(_) => break,
            }
        }
    }
}

impl Value {
    /// A short tag for diagnostics.
    pub fn kind_name(&self) -> &'static str {
        match self {
            Value::Int(_) => "Int",
            Value::Bool(_) => "Bool",
            Value::Tuple(_) => "tuple",
            Value::List(_) => "list",
            Value::Data(_) => "data",
            Value::Winner(_) => "Winner",
            Value::Option(_) => "Option",
            Value::Closure(_) | Value::Generic(_) | Value::Builtin(..) | Value::CtorFn(..) => {
                "function"
            }
            Value::Game(_) => "Game",
            Value::Form(_) => "Form",
            Value::Rules(_) => "Rules",
            Value::Scalar(_) => "scalar",
            Value::Poly(_) => "polynomial",
            Value::RatFunc(_) => "rational function",
            Value::Algebra(_) => "Algebra",
            Value::Mv(_) => "multivector",
            Value::Witness(_) => "Witness",
            Value::Claim(_) => "Claim",
            Value::Bounded(_) => "Bounded",
            Value::Quotient(_) => "Quotient",
        }
    }

    /// A list from a vector.
    pub fn list(items: Vec<Value>) -> Value {
        Value::List(Rc::new(Seq::new(items)))
    }

    /// A tuple from a vector.
    pub fn tuple(items: Vec<Value>) -> Value {
        Value::Tuple(Rc::new(Seq::new(items)))
    }

    /// How deeply the value nests: data, closures, and containers record
    /// theirs when built, so this is constant time for them.
    pub fn depth(&self) -> u32 {
        match self {
            Value::Data(d) => d.depth,
            Value::Closure(c) => c.depth,
            Value::Generic(g) => g.depth,
            Value::Tuple(s) | Value::List(s) => s.depth,
            Value::Option(Some(inner)) => inner.depth().saturating_add(1),
            Value::Rules(rules) => rules.depth(),
            Value::Bounded(b) => b.value.depth().saturating_add(1),
            Value::Witness(w) => w.depth(),
            Value::Claim(c) => c.witness.depth().saturating_add(1),
            Value::Quotient(q) => q
                .classes
                .iter()
                .flatten()
                .flatten()
                .map(Value::depth)
                .max()
                .unwrap_or(0)
                .saturating_add(1),
            _ => 0,
        }
    }

    /// The elements of a list value.
    pub fn as_list(&self) -> &[Value] {
        match self {
            Value::List(items) => items,
            other => panic!("expected a list, found {}", other.kind_name()),
        }
    }

    /// The shared elements of a list value.
    pub fn into_list(self) -> Rc<Seq> {
        match self {
            Value::List(items) => items,
            other => panic!("expected a list, found {}", other.kind_name()),
        }
    }

    /// An Int value.
    pub fn as_int(&self) -> i128 {
        match self {
            Value::Int(n) => *n,
            other => panic!("expected an Int, found {}", other.kind_name()),
        }
    }

    /// A Bool value.
    pub fn as_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            other => panic!("expected a Bool, found {}", other.kind_name()),
        }
    }
}

/// Structural equality on `Eq` values. Functions never reach here: the type
/// checker rejects `=` on them.
pub fn values_equal(a: &Value, b: &Value) -> bool {
    key_cmp(a, b) == Ordering::Equal
}

/// The structural total order on `Key` values: deterministic, independent of
/// allocation and discovery order. Used to normalize multisets of positions.
pub fn key_cmp(a: &Value, b: &Value) -> Ordering {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => x.cmp(y),
        (Value::Bool(x), Value::Bool(y)) => x.cmp(y),
        (Value::Winner(x), Value::Winner(y)) => x.cmp(y),
        (Value::Tuple(x), Value::Tuple(y)) | (Value::List(x), Value::List(y)) => {
            for (p, q) in x.iter().zip(y.iter()) {
                match key_cmp(p, q) {
                    Ordering::Equal => continue,
                    other => return other,
                }
            }
            x.len().cmp(&y.len())
        }
        (Value::Option(x), Value::Option(y)) => match (x, y) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(p), Some(q)) => key_cmp(p, q),
        },
        (Value::Data(x), Value::Data(y)) => {
            ctor_rank(&x.ctor).cmp(&ctor_rank(&y.ctor)).then_with(|| {
                for (p, q) in x.fields.iter().zip(&y.fields) {
                    match key_cmp(p, q) {
                        Ordering::Equal => continue,
                        other => return other,
                    }
                }
                Ordering::Equal
            })
        }
        (Value::Game(x), Value::Game(y)) => x.structural_cmp(y),
        (Value::Form(x), Value::Form(y)) => {
            if x.structural_eq(y) {
                Ordering::Equal
            } else {
                x.display_key().cmp(&y.display_key())
            }
        }
        (Value::Scalar(x), Value::Scalar(y)) => x.key_cmp(y),
        (Value::Poly(x), Value::Poly(y)) => x.key_cmp(y),
        (Value::RatFunc(x), Value::RatFunc(y)) => x.key_cmp(y),
        (Value::Mv(x), Value::Mv(y)) => x.key_cmp(y),
        _ => a.kind_name().cmp(b.kind_name()),
    }
}

fn ctor_rank(ctor: &CtorRef) -> (u8, u32, u32) {
    match ctor {
        CtorRef::Data(id, index) => (0, *id, *index),
        CtorRef::Winner(w) => (1, u32::from(*w), 0),
        CtorRef::None => (2, 0, 0),
        CtorRef::Some => (2, 1, 0),
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}>", self.kind_name())
    }
}
