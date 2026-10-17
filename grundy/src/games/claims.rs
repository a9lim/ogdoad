//! Evidence: witnesses, verified claims, bounded answers, and misère.
//!
//! A [`WitnessV`] is freely constructible data. [`verify`] runs only an
//! independent checker and either seals a [`ClaimV`] or fails with
//! `E_Refuted`, naming the failed condition. A claim displays as
//! `verify(<witness>)`, so re-evaluating its text re-verifies it.
//!
//! A [`BoundedV`] is an answer computed on an explicit finite sample. It is a
//! different type from its payload; the only projection is `sampled`.

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use ogdoad::games::{
    GuySmithCertificate, LoopyPartizanGraph, OutcomeCertificate, PlayConvention, StateLabel,
    StateVerdict,
};

use super::super::builtins::Builtin;
use super::super::error::{err, GrundyError, GrundyErrorKind, GrundyResult};
use super::super::eval::builtins::winner;
use super::super::eval::interp::Interp;
use super::super::eval::value::{key_cmp, values_equal, Value};
use super::super::syntax::ast::OutcomeCell;
use super::form::{operational_partizan_graph, outcome_cell, FormV};
use super::rules::{
    budget_error, component_moves, explore_components, grundy, normalize, pos_key, rules_of,
    state_key, sum_moves, topological, Player, PosKey, RulesKind, RulesV,
};

/// Evidence awaiting verification.
pub enum WitnessV {
    /// A labeling of an explicit graph's turn-states (root: node 0).
    Outcome {
        /// Left successor lists.
        left: Vec<Vec<usize>>,
        /// Right successor lists.
        right: Vec<Vec<usize>>,
        /// Normal or misère play.
        convention: PlayConvention,
        /// One label per turn-state.
        labels: Vec<StateLabel>,
    },
    /// A Grundy labeling of a ruleset's components below a root.
    Grundy {
        /// The ruleset (impartial).
        rules: Value,
        /// The root component.
        root: Value,
        /// Each component with its Grundy number and rank.
        table: Vec<(Value, i128, u128)>,
    },
    /// Guy–Smith eventual periodicity of an octal ruleset.
    Periodic {
        /// The ruleset (built by `octal`).
        rules: Value,
        /// The preperiod.
        preperiod: u128,
        /// The period.
        period: u128,
    },
    /// A misère separating context.
    Separation {
        /// The ruleset (impartial).
        rules: Value,
        /// One sum.
        p: Vec<Value>,
        /// The other sum.
        q: Vec<Value>,
        /// The separating context.
        context: Vec<Value>,
    },
}

/// What a verified claim states.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    /// The root's outcome cell.
    Outcome(OutcomeCell),
    /// The root component's Grundy number.
    Grundy(i128),
    /// Eventual periodicity of single-heap Grundy numbers, for all heaps.
    Periodic {
        /// The preperiod.
        preperiod: u128,
        /// The period.
        period: u128,
    },
    /// The two sums are misère-distinguishable in the ruleset's universe.
    Separated,
}

/// A verified claim.
pub struct ClaimV {
    /// The evidence it was verified from.
    pub witness: Rc<WitnessV>,
    /// What it states.
    pub statement: Statement,
}

/// An answer computed on a finite sample.
pub struct BoundedV {
    /// The sampled answer.
    pub value: Value,
    /// How many test contexts the sample used.
    pub samples: u128,
}

/// A sampled misère quotient: classes of sampled sums with identical
/// sampled outcome signatures. It offers no monoid operations, because
/// agreement on finitely many tests need not be a congruence.
pub struct QuotientV {
    /// Each class's sampled member sums.
    pub classes: Vec<Vec<Vec<Value>>>,
    /// Classes of misère P-positions.
    pub p: Vec<usize>,
    /// A candidate multiplication table, when every class product was sampled.
    pub table: Option<Vec<Vec<usize>>>,
    /// Whether every sampled member product agrees with the table.
    pub consistent: bool,
}

fn refuted(message: impl Into<String>) -> GrundyError {
    err(GrundyErrorKind::Refuted, message)
}

fn witness_of(value: &Value) -> &Rc<WitnessV> {
    match value {
        Value::Witness(w) => w,
        other => panic!("expected a Witness, found {}", other.kind_name()),
    }
}

// ---------------------------------------------------------------- verification

/// Run the independent checker for a witness.
pub fn verify(interp: &mut Interp<'_>, witness: &Rc<WitnessV>) -> GrundyResult<ClaimV> {
    let statement = match &**witness {
        WitnessV::Outcome {
            left,
            right,
            convention,
            labels,
        } => {
            if left.is_empty() {
                return Err(refuted("an outcome witness needs a root node"));
            }
            let graph = LoopyPartizanGraph::new(left.clone(), right.clone())
                .map_err(|e| refuted(format!("the witness graph is invalid: {e}")))?;
            let outcomes = graph
                .verify_outcome_certificate(&OutcomeCertificate {
                    convention: *convention,
                    labels: labels.clone(),
                })
                .map_err(|e| refuted(e.to_string()))?;
            Statement::Outcome(outcome_cell(outcomes[0]))
        }
        WitnessV::Grundy { rules, root, table } => {
            let rules = rules_of(rules).clone();
            if !rules.impartial() {
                return Err(refuted("a Grundy witness needs an impartial ruleset"));
            }
            let mut entries: HashMap<PosKey, (i128, u128)> = HashMap::new();
            for (position, value, rank) in table {
                if entries.insert(pos_key(position), (*value, *rank)).is_some() {
                    return Err(refuted("a position appears twice in the Grundy table"));
                }
            }
            let Some(&(root_value, _)) = entries.get(&pos_key(root)) else {
                return Err(refuted("the root is not in the Grundy table"));
            };
            for (position, value, rank) in table {
                let options = component_moves(interp, &rules, position, Player::Left)?;
                if *value < 0 || *value as usize > options.len() {
                    return Err(refuted(format!(
                        "Grundy value {value} exceeds the option count {}",
                        options.len()
                    )));
                }
                let mut reachable = Vec::new();
                for option in &options {
                    let mut x = 0;
                    for component in option {
                        let Some(&(g, r)) = entries.get(&pos_key(component)) else {
                            return Err(refuted("an option's component is missing from the table"));
                        };
                        if r >= *rank {
                            return Err(refuted("ranks must decrease along options"));
                        }
                        x ^= g;
                    }
                    reachable.push(x);
                }
                reachable.sort_unstable();
                reachable.dedup();
                let mut mex = 0;
                for x in reachable {
                    if x == mex {
                        mex += 1;
                    } else if x > mex {
                        break;
                    }
                }
                if mex != *value {
                    return Err(refuted(format!(
                        "a table entry claims {value} but its options' mex is {mex}"
                    )));
                }
            }
            Statement::Grundy(root_value)
        }
        WitnessV::Periodic {
            rules,
            preperiod,
            period,
        } => {
            let RulesKind::Octal(code) = &rules_of(rules).kind else {
                return Err(refuted(
                    "Guy–Smith periodicity applies only to rules built by `octal`",
                ));
            };
            let budget = usize::try_from(interp.graph_budget).unwrap_or(usize::MAX);
            GuySmithCertificate::compute(code.clone(), *preperiod, *period, budget)
                .map_err(|e| refuted(e.to_string()))?;
            Statement::Periodic {
                preperiod: *preperiod,
                period: *period,
            }
        }
        WitnessV::Separation {
            rules,
            p,
            q,
            context,
        } => {
            let rules = rules_of(rules).clone();
            if !rules.impartial() {
                return Err(refuted("misère quotients are impartial"));
            }
            let mut solver = MisereSolver::default();
            let with = |sum: &[Value]| {
                let mut out = sum.to_vec();
                out.extend(context.iter().cloned());
                out
            };
            let a = solver.next_wins(interp, &rules, with(p))?;
            let b = solver.next_wins(interp, &rules, with(q))?;
            if a == b {
                return Err(refuted(
                    "the context gives both sums the same misère outcome",
                ));
            }
            Statement::Separated
        }
    };
    Ok(ClaimV {
        witness: witness.clone(),
        statement,
    })
}

// ---------------------------------------------------------------- misère

/// Memoized misère solver for impartial sums (`true`: the next player wins).
#[derive(Default)]
pub struct MisereSolver {
    memo: HashMap<Vec<PosKey>, bool>,
}

impl MisereSolver {
    /// The misère outcome of a sum of components.
    pub fn next_wins(
        &mut self,
        interp: &mut Interp<'_>,
        rules: &RulesV,
        sum: Vec<Value>,
    ) -> GrundyResult<bool> {
        let root = normalize(sum);
        let root_key = state_key(&root);
        if let Some(&known) = self.memo.get(&root_key) {
            return Ok(known);
        }
        // Iterative depth-first search; a revisited unsolved state is a cycle.
        struct Frame {
            key: Vec<PosKey>,
            children: Vec<(Vec<PosKey>, Vec<Value>)>,
            next: usize,
            wins: bool,
        }
        let mut on_stack: HashMap<Vec<PosKey>, ()> = HashMap::new();
        let expand = |interp: &mut Interp<'_>,
                      state: &[Value]|
         -> GrundyResult<Vec<(Vec<PosKey>, Vec<Value>)>> {
            Ok(sum_moves(interp, rules, state, Player::Left)?
                .into_iter()
                .map(|next| (state_key(&next), next))
                .collect())
        };
        let mut stack = vec![Frame {
            key: root_key.clone(),
            children: expand(interp, &root)?,
            next: 0,
            wins: false,
        }];
        on_stack.insert(root_key.clone(), ());
        while let Some(frame) = stack.last_mut() {
            if frame.children.is_empty() {
                // A player with no move wins in misère play.
                frame.wins = true;
                frame.next = usize::MAX;
            }
            if frame.wins || frame.next >= frame.children.len() {
                let done = stack.pop().expect("frame");
                on_stack.remove(&done.key);
                if self.memo.len() as u128 >= interp.graph_budget {
                    return Err(budget_error(interp.graph_budget));
                }
                self.memo.insert(done.key.clone(), done.wins);
                if let Some(parent) = stack.last_mut() {
                    if !done.wins {
                        parent.wins = true;
                    }
                }
                continue;
            }
            let (key, state) = frame.children[frame.next].clone();
            frame.next += 1;
            if let Some(&child) = self.memo.get(&key) {
                if !child {
                    frame.wins = true;
                }
                continue;
            }
            if on_stack.contains_key(&key) {
                return Err(err(
                    GrundyErrorKind::Loopy,
                    "the misère sum-state graph has a cycle",
                )
                .with_hint("misère analysis here covers terminating rulesets"));
            }
            let children = expand(interp, &state)?;
            on_stack.insert(key.clone(), ());
            stack.push(Frame {
                key,
                children,
                next: 0,
                wins: false,
            });
        }
        Ok(self.memo[&root_key])
    }
}

/// The misère outcome pair of a sum, impartial or partizan.
fn misere_outcome(interp: &mut Interp<'_>, rules: &RulesV, sum: Vec<Value>) -> GrundyResult<Value> {
    let (_, graph) = super::rules::sum_graph(interp, rules, sum)?;
    let certificate = graph.certify_outcomes(PlayConvention::Misere);
    let outcomes = graph
        .verify_outcome_certificate(&certificate)
        .map_err(|e| err(GrundyErrorKind::Domain, format!("internal: {e}")))?;
    let cell = outcome_cell(outcomes[0]);
    Ok(Value::tuple(vec![
        winner(cell.left_first),
        winner(cell.right_first),
    ]))
}

fn quotient(
    interp: &mut Interp<'_>,
    rules: &RulesV,
    atoms: &[Value],
    elem_bound: i128,
    test_bound: i128,
) -> GrundyResult<(QuotientV, u128)> {
    let multisets = |k: i128| -> Vec<Vec<Value>> {
        let mut atoms = atoms.to_vec();
        atoms.sort_by(key_cmp);
        atoms.dedup_by(|a, b| key_cmp(a, b).is_eq());
        let mut out = vec![Vec::new()];
        let mut frontier: Vec<(usize, Vec<Value>)> = vec![(0, Vec::new())];
        for _ in 0..k.max(0) {
            let mut next = Vec::new();
            for (start, prefix) in &frontier {
                for (index, atom) in atoms.iter().enumerate().skip(*start) {
                    let mut sum = prefix.clone();
                    sum.push(atom.clone());
                    out.push(sum.clone());
                    next.push((index, sum));
                }
            }
            frontier = next;
        }
        out
    };
    let elements = multisets(elem_bound);
    let tests = multisets(test_bound);
    interp.spend((elements.len() * tests.len()) as u128)?;
    let mut solver = MisereSolver::default();
    let mut signatures = Vec::new();
    for element in &elements {
        let mut signature = Vec::new();
        for test in &tests {
            let mut sum = element.clone();
            sum.extend(test.iter().cloned());
            signature.push(solver.next_wins(interp, rules, sum)?);
        }
        signatures.push(signature);
    }
    let mut class_of = Vec::new();
    let mut by_signature: BTreeMap<Vec<bool>, usize> = BTreeMap::new();
    let mut classes: Vec<Vec<Vec<Value>>> = Vec::new();
    for (element, signature) in elements.iter().zip(&signatures) {
        let next = classes.len();
        let class = *by_signature.entry(signature.clone()).or_insert(next);
        if class == next {
            classes.push(Vec::new());
        }
        classes[class].push(element.clone());
        class_of.push(class);
    }
    // The empty test is first: its column is each element's own outcome.
    let p: Vec<usize> = (0..classes.len())
        .filter(|&class| {
            let member = class_of.iter().position(|&c| c == class).expect("member");
            !signatures[member][0]
        })
        .collect();
    let index_of: HashMap<Vec<PosKey>, usize> = elements
        .iter()
        .enumerate()
        .map(|(i, e)| (state_key(&normalize(e.clone())), i))
        .collect();
    let class_of_sum = |a: &[Value], b: &[Value]| -> Option<usize> {
        let mut sum = a.to_vec();
        sum.extend(b.iter().cloned());
        index_of
            .get(&state_key(&normalize(sum)))
            .map(|&i| class_of[i])
    };
    let mut table = Some(vec![vec![0; classes.len()]; classes.len()]);
    for a in 0..classes.len() {
        for b in 0..classes.len() {
            match class_of_sum(&classes[a][0], &classes[b][0]) {
                Some(c) => {
                    if let Some(t) = &mut table {
                        t[a][b] = c;
                    }
                }
                None => table = None,
            }
        }
    }
    let mut consistent = true;
    if let Some(t) = &table {
        for (i, x) in elements.iter().enumerate() {
            for (j, y) in elements.iter().enumerate() {
                if let Some(c) = class_of_sum(x, y) {
                    if t[class_of[i]][class_of[j]] != c {
                        consistent = false;
                    }
                }
            }
        }
    }
    Ok((
        QuotientV {
            classes,
            p,
            table,
            consistent,
        },
        tests.len() as u128,
    ))
}

fn quotient_of(value: &Value) -> &Rc<QuotientV> {
    match value {
        Value::Quotient(q) => q,
        other => panic!("expected a Quotient, found {}", other.kind_name()),
    }
}

fn int_list(value: &Value) -> Vec<i128> {
    value.as_list().iter().map(Value::as_int).collect()
}

fn to_index(n: i128, what: &str) -> GrundyResult<usize> {
    usize::try_from(n).map_err(|_| err(GrundyErrorKind::Domain, format!("{what} must be natural")))
}

fn to_u128(n: i128, what: &str) -> GrundyResult<u128> {
    u128::try_from(n).map_err(|_| err(GrundyErrorKind::Domain, format!("{what} must be natural")))
}

// ---------------------------------------------------------------- builtins

/// Evidence and misère builtins.
pub fn call(interp: &mut Interp<'_>, builtin: Builtin, args: Vec<Value>) -> GrundyResult<Value> {
    use Builtin as B;
    match builtin {
        B::Verify => Ok(Value::Claim(Rc::new(verify(interp, witness_of(&args[0]))?))),
        B::Evidence => match &args[0] {
            Value::Claim(claim) => Ok(Value::Witness(claim.witness.clone())),
            other => panic!("expected a Claim, found {}", other.kind_name()),
        },
        B::OutcomeWitness => {
            let left: Vec<Vec<usize>> = args[0]
                .as_list()
                .iter()
                .map(|row| {
                    int_list(row)
                        .into_iter()
                        .map(|n| to_index(n, "a node"))
                        .collect()
                })
                .collect::<GrundyResult<_>>()?;
            let right: Vec<Vec<usize>> = args[1]
                .as_list()
                .iter()
                .map(|row| {
                    int_list(row)
                        .into_iter()
                        .map(|n| to_index(n, "a node"))
                        .collect()
                })
                .collect::<GrundyResult<_>>()?;
            let convention = if args[2].as_bool() {
                PlayConvention::Misere
            } else {
                PlayConvention::Normal
            };
            let mut labels = Vec::new();
            for label in args[3].as_list().iter() {
                let Value::Tuple(parts) = label else {
                    unreachable!("typed as a triple")
                };
                let verdict = match parts[0].as_int() {
                    0 => StateVerdict::Loss,
                    1 => StateVerdict::Win,
                    2 => StateVerdict::Draw,
                    _ => {
                        return Err(err(
                            GrundyErrorKind::Domain,
                            "verdicts are 0 loss, 1 win, 2 draw",
                        ))
                    }
                };
                let rank = to_u128(parts[1].as_int(), "a rank")?;
                let chosen = match parts[2].as_int() {
                    -1 => None,
                    n => Some(to_index(n, "a chosen state")?),
                };
                labels.push(StateLabel {
                    verdict,
                    rank,
                    chosen,
                });
            }
            Ok(Value::Witness(Rc::new(WitnessV::Outcome {
                left,
                right,
                convention,
                labels,
            })))
        }
        B::SgWitness => {
            let mut table = Vec::new();
            for entry in args[2].as_list().iter() {
                let Value::Tuple(parts) = entry else {
                    unreachable!("typed as a triple")
                };
                table.push((
                    parts[0].clone(),
                    parts[1].as_int(),
                    to_u128(parts[2].as_int(), "a rank")?,
                ));
            }
            Ok(Value::Witness(Rc::new(WitnessV::Grundy {
                rules: args[0].clone(),
                root: args[1].clone(),
                table,
            })))
        }
        B::PeriodicWitness => Ok(Value::Witness(Rc::new(WitnessV::Periodic {
            rules: args[0].clone(),
            preperiod: to_u128(args[1].as_int(), "a preperiod")?,
            period: to_u128(args[2].as_int(), "a period")?,
        }))),
        B::SeparationWitness => Ok(Value::Witness(Rc::new(WitnessV::Separation {
            rules: args[0].clone(),
            p: args[1].as_list().to_vec(),
            q: args[2].as_list().to_vec(),
            context: args[3].as_list().to_vec(),
        }))),
        B::Certify => {
            let FormV(element) = match &args[0] {
                Value::Form(f) => f.clone(),
                other => panic!("expected a Form, found {}", other.kind_name()),
            };
            let graph = operational_partizan_graph(&element, interp.graph_budget)?;
            let certificate = graph.certify_outcomes(PlayConvention::Normal);
            let witness = Rc::new(WitnessV::Outcome {
                left: graph.left().to_vec(),
                right: graph.right().to_vec(),
                convention: PlayConvention::Normal,
                labels: certificate.labels,
            });
            Ok(Value::Claim(Rc::new(verify(interp, &witness)?)))
        }
        B::CertifySg => {
            let rules = rules_of(&args[0]).clone();
            let root = args[1].clone();
            grundy(interp, &rules, &root)?;
            let (graph, _) = explore_components(interp, &rules, &root, &|_| false)?;
            let order = topological(&graph, &|_| false)
                .map_err(|cycle| super::rules::cycle_error(interp.data, &graph, &cycle))?;
            let mut ranks = vec![0u128; graph.positions.len()];
            for id in order {
                ranks[id] = graph.left[id]
                    .iter()
                    .flatten()
                    .map(|c| ranks[*c] + 1)
                    .max()
                    .unwrap_or(0);
            }
            let mut table = Vec::new();
            for (id, position) in graph.positions.iter().enumerate() {
                table.push((
                    position.clone(),
                    grundy(interp, &rules, position)?,
                    ranks[id],
                ));
            }
            let witness = Rc::new(WitnessV::Grundy {
                rules: args[0].clone(),
                root,
                table,
            });
            Ok(Value::Claim(Rc::new(verify(interp, &witness)?)))
        }
        B::Periodic => {
            let witness = Rc::new(WitnessV::Periodic {
                rules: args[0].clone(),
                preperiod: to_u128(args[1].as_int(), "a preperiod")?,
                period: to_u128(args[2].as_int(), "a period")?,
            });
            Ok(Value::Claim(Rc::new(verify(interp, &witness)?)))
        }
        B::Separate => {
            let rules = rules_of(&args[0]).clone();
            if !rules.impartial() {
                return Err(err(
                    GrundyErrorKind::Domain,
                    "misère quotients are impartial",
                ));
            }
            let p = args[1].as_list().to_vec();
            let q = args[2].as_list().to_vec();
            let mut solver = MisereSolver::default();
            for context in args[3].as_list().iter() {
                let context = context.as_list().to_vec();
                let mut a = p.clone();
                a.extend(context.iter().cloned());
                let mut b = q.clone();
                b.extend(context.iter().cloned());
                if solver.next_wins(interp, &rules, a)? != solver.next_wins(interp, &rules, b)? {
                    let witness = Rc::new(WitnessV::Separation {
                        rules: args[0].clone(),
                        p,
                        q,
                        context,
                    });
                    let claim = verify(interp, &witness)?;
                    return Ok(Value::Option(Some(Rc::new(Value::Claim(Rc::new(claim))))));
                }
            }
            Ok(Value::Option(None))
        }
        B::Misere => {
            let rules = rules_of(&args[0]).clone();
            misere_outcome(interp, &rules, args[1].as_list().to_vec())
        }
        B::MisereEqual => {
            let rules = rules_of(&args[0]).clone();
            if !rules.impartial() {
                return Err(err(
                    GrundyErrorKind::Domain,
                    "misère quotients are impartial",
                ));
            }
            let p = args[1].as_list().to_vec();
            let q = args[2].as_list().to_vec();
            let contexts = args[3].as_list();
            let mut solver = MisereSolver::default();
            let mut equal = true;
            for context in contexts.iter() {
                let context = context.as_list();
                let mut a = p.clone();
                a.extend(context.iter().cloned());
                let mut b = q.clone();
                b.extend(context.iter().cloned());
                if solver.next_wins(interp, &rules, a)? != solver.next_wins(interp, &rules, b)? {
                    equal = false;
                    break;
                }
            }
            Ok(Value::Bounded(Rc::new(BoundedV {
                value: Value::Bool(equal),
                samples: contexts.len() as u128,
            })))
        }
        B::MisereQuotient => {
            let rules = rules_of(&args[0]).clone();
            if !rules.impartial() {
                return Err(err(
                    GrundyErrorKind::Domain,
                    "misère quotients are impartial",
                ));
            }
            let (q, samples) = quotient(
                interp,
                &rules,
                args[1].as_list(),
                args[2].as_int(),
                args[3].as_int(),
            )?;
            Ok(Value::Bounded(Rc::new(BoundedV {
                value: Value::Quotient(Rc::new(q)),
                samples,
            })))
        }
        B::Bounded => Ok(Value::Bounded(Rc::new(BoundedV {
            value: args[0].clone(),
            samples: to_u128(args[1].as_int(), "a sample count")?,
        }))),
        B::Sampled => match &args[0] {
            Value::Bounded(b) => Ok(b.value.clone()),
            other => panic!("expected Bounded, found {}", other.kind_name()),
        },
        B::Samples => match &args[0] {
            Value::Bounded(b) => Ok(Value::Int(b.samples as i128)),
            other => panic!("expected Bounded, found {}", other.kind_name()),
        },
        B::QuotientOf => {
            let classes: Vec<Vec<Vec<Value>>> = args[0]
                .as_list()
                .iter()
                .map(|class| {
                    class
                        .as_list()
                        .iter()
                        .map(|member| normalize(member.as_list().to_vec()))
                        .collect()
                })
                .collect();
            let n = classes.len();
            let p = int_list(&args[1])
                .into_iter()
                .map(|c| to_index(c, "a class"))
                .collect::<GrundyResult<Vec<_>>>()?;
            if classes.iter().any(Vec::is_empty) || p.iter().any(|&c| c >= n) {
                return Err(err(
                    GrundyErrorKind::Domain,
                    "a quotient's classes are non-empty and its P-classes exist",
                ));
            }
            let table = match &args[2] {
                Value::Option(None) => None,
                Value::Option(Some(rows)) => {
                    let rows: Vec<Vec<usize>> = rows
                        .as_list()
                        .iter()
                        .map(|row| {
                            int_list(row)
                                .into_iter()
                                .map(|c| to_index(c, "a class"))
                                .collect()
                        })
                        .collect::<GrundyResult<_>>()?;
                    if rows.len() != n
                        || rows
                            .iter()
                            .any(|row| row.len() != n || row.iter().any(|&c| c >= n))
                    {
                        return Err(err(
                            GrundyErrorKind::Domain,
                            "the table is square over the classes",
                        ));
                    }
                    Some(rows)
                }
                _ => unreachable!("typed as an Option"),
            };
            let consistent = table_consistent(&classes, table.as_deref());
            Ok(Value::Quotient(Rc::new(QuotientV {
                classes,
                p,
                table,
                consistent,
            })))
        }
        B::Classes => Ok(Value::list(
            quotient_of(&args[0])
                .classes
                .iter()
                .map(|class| Value::list(class.iter().map(|m| Value::list(m.clone())).collect()))
                .collect(),
        )),
        B::PClasses => Ok(Value::list(
            quotient_of(&args[0])
                .p
                .iter()
                .map(|c| Value::Int(*c as i128))
                .collect(),
        )),
        B::Table => Ok(Value::Option(quotient_of(&args[0]).table.as_ref().map(
            |t| {
                Rc::new(Value::list(
                    t.iter()
                        .map(|row| {
                            Value::list(row.iter().map(|c| Value::Int(*c as i128)).collect())
                        })
                        .collect(),
                ))
            },
        ))),
        B::Consistent => Ok(Value::Bool(quotient_of(&args[0]).consistent)),
        B::ClassOf => {
            let q = quotient_of(&args[0]);
            let target = normalize(args[1].as_list().to_vec());
            let found = q.classes.iter().position(|class| {
                class.iter().any(|member| {
                    member.len() == target.len()
                        && member.iter().zip(&target).all(|(a, b)| values_equal(a, b))
                })
            });
            Ok(Value::Option(found.map(|c| Rc::new(Value::Int(c as i128)))))
        }
        _ => unreachable!("not an evidence builtin"),
    }
}

fn table_consistent(classes: &[Vec<Vec<Value>>], table: Option<&[Vec<usize>]>) -> bool {
    let Some(table) = table else {
        return true;
    };
    let mut class_of: HashMap<Vec<PosKey>, usize> = HashMap::new();
    for (c, class) in classes.iter().enumerate() {
        for member in class {
            class_of.insert(state_key(member), c);
        }
    }
    for (a, xs) in classes.iter().enumerate() {
        for (b, ys) in classes.iter().enumerate() {
            for x in xs {
                for y in ys {
                    let mut sum = x.clone();
                    sum.extend(y.iter().cloned());
                    if let Some(&c) = class_of.get(&state_key(&normalize(sum))) {
                        if table[a][b] != c {
                            return false;
                        }
                    }
                }
            }
        }
    }
    true
}
