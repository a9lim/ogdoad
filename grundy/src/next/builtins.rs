//! The builtin function table: names, signatures, and constraints.
//!
//! Signatures are written in surface type syntax and parsed once; lowercase
//! names are the scheme's quantified variables.

use std::collections::BTreeMap;
use std::sync::OnceLock;

use super::syntax::parse::parse_type;
use super::types::{infer::type_from_expr_closed, Class, DataRegistry, Pred, Scheme};

macro_rules! builtins {
    ($($variant:ident => $name:literal : $sig:literal $(where $($class:ident $var:ident),+)?;)*) => {
        /// Builtin functions.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub enum Builtin {
            $(
                #[doc = concat!("`", $name, " : ", $sig, "`")]
                $variant,
            )*
        }

        impl Builtin {
            /// Every builtin.
            pub const ALL: &'static [Builtin] = &[$(Builtin::$variant),*];

            /// The surface name.
            pub fn name(self) -> &'static str {
                match self {
                    $(Builtin::$variant => $name,)*
                }
            }

            fn signature(self) -> (&'static str, &'static [(&'static str, &'static str)]) {
                match self {
                    $(Builtin::$variant => ($sig, &[$($((stringify!($class), stringify!($var))),+)?]),)*
                }
            }
        }
    };
}

builtins! {
    // ------------------------------------------------------------ lists and Int
    Len => "len": "List(a) → Int";
    Map => "map": "(a → b, List(a)) → List(b)";
    Filter => "filter": "(a → Bool, List(a)) → List(a)";
    Fold => "fold": "((b, a) → b, b, List(a)) → b";
    Sum => "sum": "List(a) → a" where Add a;
    Any => "any": "(a → Bool, List(a)) → Bool";
    All => "all": "(a → Bool, List(a)) → Bool";
    Contains => "contains": "(List(a), a) → Bool" where Eq a;
    Reverse => "reverse": "List(a) → List(a)";
    Sort => "sort": "List(a) → List(a)" where Key a;
    Unique => "unique": "List(a) → List(a)" where Key a;
    Flatten => "flatten": "List(List(a)) → List(a)";
    Zip => "zip": "(List(a), List(b)) → List((a, b))";
    Sums => "sums": "(List(a), Int) → List(List(a))" where Key a;
    Div => "div": "(Int, Int) → Int";
    Abs => "abs": "Int → Int";
    Min => "min": "(Int, Int) → Int";
    Max => "max": "(Int, Int) → Int";
    Xor => "xor": "(Int, Int) → Int";
    Mex => "mex": "List(Int) → Int";
    // ------------------------------------------------------------------ games
    GameOf => "game": "a → Game" where IntoGame a;
    FormOf => "form": "Game → Form";
    Canon => "canon": "Form → Game";
    Number => "number": "Game → Surreal";
    NimberOf => "nimber": "Game → Nimber";
    IsNumber => "is_number": "Game → Bool";
    Lefts => "lefts": "g → List(g)" where GameLike g;
    Rights => "rights": "g → List(g)" where GameLike g;
    Birthday => "birthday": "g → Int" where GameLike g;
    Outcome => "outcome": "g → (Winner, Winner)" where GameLike g;
    Stopper => "stopper": "Form → Bool";
    HasDraw => "hasdraw": "Form → Bool";
    Temperature => "temperature": "Game → Surreal";
    Mean => "mean": "Game → Surreal";
    LeftStop => "left_stop": "Game → Surreal";
    RightStop => "right_stop": "Game → Surreal";
    AtomicWeight => "atomic_weight": "Game → Game";
    // --------------------------------------------------------------- rulesets
    Impartial => "impartial": "(s → List(List(s))) → Rules(s)" where Key s;
    Partizan => "partizan": "(s → List(List(s)), s → List(List(s))) → Rules(s)" where Key s;
    Octal => "octal": "List(Int) → Rules(Int)";
    Value => "value": "(Rules(s), s) → Game";
    Graph => "graph": "(Rules(s), s) → Form";
    Sg => "sg": "(Rules(s), s) → Int";
    Moves => "moves": "(Rules(s), List(s), Winner) → List(List(s))";
    Winning => "winning": "(Rules(s), List(s), Winner) → List(List(s))";
    // ----------------------------------------------------------------- misère
    Misere => "misere": "(Rules(s), List(s)) → (Winner, Winner)";
    MisereQuotient => "misere_quotient": "(Rules(s), List(s), Int, Int) → Bounded(Quotient)";
    MisereEqual => "misere_equal": "(Rules(s), List(s), List(s), List(List(s))) → Bounded(Bool)";
    Separate => "separate": "(Rules(s), List(s), List(s), List(List(s))) → Option(Claim)";
    Sampled => "sampled": "Bounded(a) → a";
    Classes => "classes": "Quotient → List(List(Int))";
    PClasses => "p_classes": "Quotient → List(Int)";
    Table => "table": "Quotient → Option(List(List(Int)))";
    // ----------------------------------------------------------------- claims
    Certify => "certify": "Form → Claim";
    CertifySg => "certify_sg": "(Rules(s), s) → Claim";
    Periodic => "periodic": "(Rules(Int), Int, Int) → Claim";
    Verify => "verify": "Witness → Claim";
    Evidence => "evidence": "Claim → Witness";
}

/// A builtin's type scheme.
pub fn scheme(builtin: Builtin) -> &'static Scheme {
    static SCHEMES: OnceLock<BTreeMap<Builtin, Scheme>> = OnceLock::new();
    &SCHEMES.get_or_init(|| {
        Builtin::ALL
            .iter()
            .map(|&builtin| (builtin, build_scheme(builtin)))
            .collect()
    })[&builtin]
}

fn build_scheme(builtin: Builtin) -> Scheme {
    let (sig, preds) = builtin.signature();
    let expr = parse_type(sig).unwrap_or_else(|err| panic!("builtin `{}`: {err}", builtin.name()));
    let (ty, vars) = type_from_expr_closed(&expr, &DataRegistry::default())
        .unwrap_or_else(|err| panic!("builtin `{}`: {err}", builtin.name()));
    let preds = preds
        .iter()
        .map(|(class, var)| {
            let class = match *class {
                "Add" => Class::Add,
                "Eq" => Class::Eq,
                "Key" => Class::Key,
                "GameLike" => Class::GameLike,
                "IntoGame" => Class::IntoGame,
                other => panic!("builtin `{}`: unknown class {other}", builtin.name()),
            };
            Pred::Is(class, vars[*var].clone())
        })
        .collect();
    let mut quantified: Vec<_> = vars
        .values()
        .filter_map(|ty| match ty {
            super::types::Ty::Var(v) => Some(*v),
            _ => None,
        })
        .collect();
    quantified.sort_unstable();
    Scheme {
        vars: quantified,
        preds,
        ty,
    }
}

/// Look a builtin up by name.
pub fn lookup(name: &str) -> Option<Builtin> {
    static BY_NAME: OnceLock<BTreeMap<&'static str, Builtin>> = OnceLock::new();
    BY_NAME
        .get_or_init(|| {
            Builtin::ALL
                .iter()
                .map(|&builtin| (builtin.name(), builtin))
                .collect()
        })
        .get(name)
        .copied()
}
