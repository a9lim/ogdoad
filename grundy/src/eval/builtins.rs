//! Builtin implementations. Signatures live in [`super::super::builtins`].

use std::cmp::Ordering;

use ogdoad::games::{atomic_weight, left_stop, mean_value, right_stop, temperature, Game};
use ogdoad::scalar::{Nimber, Rational, Surreal};

use super::super::algebra::scalar::ScalarV;
use super::super::builtins::Builtin;
use super::super::error::{err, GrundyErrorKind, GrundyResult};
use super::super::games::form::{
    form_outcome, game_element_has_draw, game_element_is_stopper, game_options, FormV, GameElement,
};
use super::super::games::game::GameV;
use super::super::games::{claims, rules};
use super::super::syntax::ast::Mover;
use super::super::types::{Ty, TyCon};
use super::interp::{game_cell, Interp};
use super::value::{key_cmp, values_equal, Value};

/// Call a builtin.
pub fn call_builtin(
    interp: &mut Interp<'_>,
    builtin: Builtin,
    tys: &[Ty],
    args: Vec<Value>,
) -> GrundyResult<Value> {
    use Builtin as B;
    let arg = |i: usize| &args[i];
    match builtin {
        // ------------------------------------------------------------- lists
        B::Len => Ok(Value::Int(arg(0).as_list().len() as i128)),
        B::Map => {
            let f = arg(0).clone();
            let mut out = Vec::new();
            for item in arg(1).as_list().iter() {
                interp.spend(1)?;
                out.push(interp.apply(&f, vec![item.clone()])?);
            }
            Ok(Value::list(out))
        }
        B::Filter => {
            let f = arg(0).clone();
            let mut out = Vec::new();
            for item in arg(1).as_list().iter() {
                if interp.apply(&f, vec![item.clone()])?.as_bool() {
                    interp.spend(1)?;
                    out.push(item.clone());
                }
            }
            Ok(Value::list(out))
        }
        B::Fold => {
            let f = arg(0).clone();
            let mut acc = arg(1).clone();
            for item in arg(2).as_list().iter() {
                acc = interp.apply(&f, vec![acc, item.clone()])?;
            }
            Ok(acc)
        }
        B::Sum => {
            let mut acc = zero_of(&tys[0])?;
            for item in arg(0).as_list().iter() {
                acc = interp.binary(super::super::syntax::ast::BinaryOp::Add, acc, item.clone())?;
            }
            Ok(acc)
        }
        B::Any | B::All => {
            let f = arg(0).clone();
            let want = builtin == B::Any;
            for item in arg(1).as_list().iter() {
                if interp.apply(&f, vec![item.clone()])?.as_bool() == want {
                    return Ok(Value::Bool(want));
                }
            }
            Ok(Value::Bool(!want))
        }
        B::Contains => Ok(Value::Bool(
            arg(0)
                .as_list()
                .iter()
                .any(|item| values_equal(item, arg(1))),
        )),
        B::Reverse => Ok(Value::list(
            arg(0).as_list().iter().rev().cloned().collect(),
        )),
        B::Sort => {
            let mut items = arg(0).as_list().to_vec();
            items.sort_by(key_cmp);
            Ok(Value::list(items))
        }
        B::Unique => {
            let items = arg(0).as_list();
            let mut order: Vec<usize> = (0..items.len()).collect();
            order.sort_by(|a, b| key_cmp(&items[*a], &items[*b]).then(a.cmp(b)));
            let mut keep = vec![false; items.len()];
            let mut previous: Option<usize> = None;
            for index in order {
                if previous.is_none_or(|p| key_cmp(&items[p], &items[index]) != Ordering::Equal) {
                    keep[index] = true;
                    previous = Some(index);
                }
            }
            Ok(Value::list(
                items
                    .iter()
                    .zip(keep)
                    .filter(|(_, keep)| *keep)
                    .map(|(item, _)| item.clone())
                    .collect(),
            ))
        }
        B::Flatten => {
            let mut out = Vec::new();
            for inner in arg(0).as_list().iter() {
                interp.spend(inner.as_list().len() as u128)?;
                out.extend(inner.as_list().iter().cloned());
            }
            Ok(Value::list(out))
        }
        B::Zip => Ok(Value::list(
            arg(0)
                .as_list()
                .iter()
                .zip(arg(1).as_list().iter())
                .map(|(a, b)| Value::tuple(vec![a.clone(), b.clone()]))
                .collect(),
        )),
        B::Sums => {
            let mut atoms = arg(0).as_list().to_vec();
            atoms.sort_by(key_cmp);
            atoms.dedup_by(|a, b| key_cmp(a, b) == Ordering::Equal);
            let k = arg(1).as_int();
            if k < 0 {
                return Err(err(GrundyErrorKind::Domain, "a sum size is non-negative"));
            }
            let mut out = vec![Value::list(Vec::new())];
            let mut frontier: Vec<(usize, Vec<Value>)> = vec![(0, Vec::new())];
            for _ in 0..k {
                let mut next = Vec::new();
                for (start, prefix) in &frontier {
                    for (index, atom) in atoms.iter().enumerate().skip(*start) {
                        interp.spend(1)?;
                        let mut sum = prefix.clone();
                        sum.push(atom.clone());
                        out.push(Value::list(sum.clone()));
                        next.push((index, sum));
                    }
                }
                frontier = next;
            }
            Ok(Value::list(out))
        }
        B::Div => {
            let (a, b) = (arg(0).as_int(), arg(1).as_int());
            if b == 0 {
                return Err(err(GrundyErrorKind::DivisionByZero, "division by zero"));
            }
            a.checked_div_euclid(b)
                .map(Value::Int)
                .ok_or_else(|| err(GrundyErrorKind::Overflow, "division overflows i128"))
        }
        B::Abs => arg(0)
            .as_int()
            .checked_abs()
            .map(Value::Int)
            .ok_or_else(|| err(GrundyErrorKind::Overflow, "abs overflows i128")),
        B::Min => Ok(Value::Int(arg(0).as_int().min(arg(1).as_int()))),
        B::Max => Ok(Value::Int(arg(0).as_int().max(arg(1).as_int()))),
        B::Xor => {
            let (a, b) = (arg(0).as_int(), arg(1).as_int());
            if a < 0 || b < 0 {
                return Err(err(
                    GrundyErrorKind::Domain,
                    "nim-sum takes natural numbers",
                ));
            }
            Ok(Value::Int(a ^ b))
        }
        B::Mex => {
            let mut values: Vec<i128> = arg(0).as_list().iter().map(Value::as_int).collect();
            values.sort_unstable();
            values.dedup();
            let mut mex = 0;
            for value in values {
                if value == mex {
                    mex += 1;
                } else if value > mex {
                    break;
                }
            }
            Ok(Value::Int(mex))
        }
        // ------------------------------------------------------------- games
        B::GameOf => match arg(0) {
            Value::Int(n) => Ok(Value::Game(GameV::integer(*n, interp)?)),
            Value::Scalar(ScalarV::Nimber(Nimber(n))) => {
                Ok(Value::Game(GameV::nimber(*n, interp)?))
            }
            Value::Scalar(ScalarV::Surreal(s)) => GameV::of_surreal(s, interp)?
                .map(Value::Game)
                .ok_or_else(|| {
                    err(
                        GrundyErrorKind::Domain,
                        format!("{s} is not a dyadic rational"),
                    )
                    .with_hint("only dyadics are short games")
                }),
            Value::Game(g) => Ok(Value::Game(g.clone())),
            other => Err(err(
                GrundyErrorKind::Domain,
                format!("game() of a {}", other.kind_name()),
            )),
        },
        B::FormOf => Ok(Value::Form(FormV::finite(game_of(arg(0)).game()))),
        B::Canon => match &form_of(arg(0)).0 {
            GameElement::Finite(game) => Ok(Value::Game(GameV::seal(game, interp)?)),
            GameElement::Graph(_) => Err(err(
                GrundyErrorKind::Loopy,
                "a cyclic Form has no short canonical value",
            )
            .with_hint("`canon` reads finite forms; compare loopy values with relations")),
        },
        B::Number => game_of(arg(0))
            .number()
            .map(|s| Value::Scalar(ScalarV::Surreal(s)))
            .ok_or_else(|| err(GrundyErrorKind::Domain, "the game is not a number")),
        B::NimberOf => game_of(arg(0))
            .as_nimber()
            .map(|n| Value::Scalar(ScalarV::Nimber(Nimber(n))))
            .ok_or_else(|| err(GrundyErrorKind::Domain, "the game is not a nimber")),
        B::IsNumber => Ok(Value::Bool(game_of(arg(0)).is_number())),
        B::Lefts | B::Rights => {
            let left = builtin == B::Lefts;
            match arg(0) {
                Value::Game(g) => Ok(Value::list(
                    if left { g.lefts() } else { g.rights() }
                        .into_iter()
                        .map(Value::Game)
                        .collect(),
                )),
                Value::Form(f) => Ok(Value::list(
                    game_options(&f.0, left)
                        .into_iter()
                        .map(|option| Value::Form(FormV(option)))
                        .collect(),
                )),
                other => Err(err(
                    GrundyErrorKind::Domain,
                    format!("options of a {}", other.kind_name()),
                )),
            }
        }
        B::Birthday => match arg(0) {
            Value::Game(g) => Ok(Value::Int(g.birthday() as i128)),
            Value::Form(FormV(GameElement::Finite(game))) => Ok(Value::Int(
                i128::try_from(game.birthday())
                    .map_err(|_| err(GrundyErrorKind::Overflow, "birthday exceeds i128"))?,
            )),
            Value::Form(_) => Err(err(
                GrundyErrorKind::Loopy,
                "a cyclic Form has no finite formation day",
            )),
            other => Err(err(
                GrundyErrorKind::Domain,
                format!("birthday of a {}", other.kind_name()),
            )),
        },
        B::Outcome => {
            let cell = match arg(0) {
                Value::Game(g) => game_cell(g, &GameV::zero(), interp)?,
                Value::Form(f) => form_outcome(&f.0, interp.graph_budget)?,
                other => {
                    return Err(err(
                        GrundyErrorKind::Domain,
                        format!("outcome of a {}", other.kind_name()),
                    ))
                }
            };
            Ok(Value::tuple(vec![
                winner(cell.left_first),
                winner(cell.right_first),
            ]))
        }
        B::Stopper => Ok(Value::Bool(game_element_is_stopper(
            &form_of(arg(0)).0,
            interp.graph_budget,
        )?)),
        B::HasDraw => Ok(Value::Bool(game_element_has_draw(&form_of(arg(0)).0))),
        B::Temperature | B::Mean | B::LeftStop | B::RightStop => {
            let game = game_of(arg(0)).game();
            let value = match builtin {
                B::Temperature => temperature(&game),
                B::Mean => mean_value(&game),
                B::LeftStop => left_stop(&game),
                _ => right_stop(&game),
            };
            value
                .map(|q| Value::Scalar(ScalarV::Surreal(Surreal::from_rational(q))))
                .ok_or_else(|| err(GrundyErrorKind::Domain, "the game has no thermograph"))
        }
        B::AtomicWeight => atomic_weight(&game_of(arg(0)).game())
            .ok_or_else(|| {
                err(
                    GrundyErrorKind::Domain,
                    "atomic weight needs an all-small game",
                )
            })
            .and_then(|g| GameV::seal(&g, interp).map(Value::Game)),
        // ---------------------------------------------------------- algebra
        B::Deg
        | B::Coef
        | B::Gcd
        | B::Integral
        | B::Frob
        | B::Tr
        | B::NimTr
        | B::Clifford
        | B::CliffordMetric
        | B::Grassmann
        | B::Basis
        | B::Vector
        | B::Dim
        | B::Rev
        | B::Even
        | B::Dual
        | B::Grade
        | B::Component
        | B::ScalarPart => super::super::algebra::call(interp, builtin, tys, args),
        // ---------------------------------------------- rulesets and evidence
        B::Impartial
        | B::Partizan
        | B::Octal
        | B::Value
        | B::Graph
        | B::Sg
        | B::Moves
        | B::Winning => rules::call(interp, builtin, args),
        B::Misere
        | B::MisereQuotient
        | B::MisereEqual
        | B::Separate
        | B::Bounded
        | B::Sampled
        | B::Samples
        | B::QuotientOf
        | B::Classes
        | B::PClasses
        | B::Table
        | B::Consistent
        | B::ClassOf
        | B::Certify
        | B::CertifySg
        | B::Periodic
        | B::Verify
        | B::Evidence
        | B::OutcomeWitness
        | B::SgWitness
        | B::PeriodicWitness
        | B::SeparationWitness => claims::call(interp, builtin, args),
    }
}

/// The additive identity at a type.
pub fn zero_of(ty: &Ty) -> GrundyResult<Value> {
    match ty {
        Ty::Con(TyCon::Int, _) => Ok(Value::Int(0)),
        Ty::Con(TyCon::Game, _) => Ok(Value::Game(GameV::zero())),
        Ty::Con(TyCon::Form, _) => Ok(Value::Form(FormV::finite(Game::zero()))),
        Ty::Con(con, _) => ScalarV::zero(*con)
            .map(Value::Scalar)
            .ok_or_else(|| err(GrundyErrorKind::Domain, "internal: no zero for this type")),
        _ => Err(err(
            GrundyErrorKind::Domain,
            "internal: unresolved type for zero",
        )),
    }
}

fn game_of(value: &Value) -> GameV {
    match value {
        Value::Game(g) => g.clone(),
        other => panic!("expected a Game, found {}", other.kind_name()),
    }
}

fn form_of(value: &Value) -> &FormV {
    match value {
        Value::Form(f) => f,
        other => panic!("expected a Form, found {}", other.kind_name()),
    }
}

/// A mover result as a `Winner`.
pub fn winner(mover: Mover) -> Value {
    Value::Winner(match mover {
        Mover::Left => 0,
        Mover::Right => 1,
        Mover::Draw => 2,
    })
}

#[allow(dead_code)]
fn rational(q: Rational) -> Value {
    Value::Scalar(ScalarV::Surreal(Surreal::from_rational(q)))
}
