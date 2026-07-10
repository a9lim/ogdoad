//! Shared environment, resource budgets, and call bookkeeping.

use super::*;

pub(crate) struct RuntimeState<E> {
    pub(crate) env: BTreeMap<String, Value<E>>,
    pub(crate) fuel_budget: u128,
    pub(crate) fuel_remaining: u128,
    pub(crate) graph_budget: u128,
    pub(crate) recursion_depth: u128,
    pub(crate) validation_sample_function_names: BTreeSet<String>,
    pub(crate) active_call_keys: HashSet<String>,
}

impl<E> RuntimeState<E> {
    pub(crate) fn new() -> Self {
        Self {
            env: BTreeMap::new(),
            fuel_budget: DEFAULT_FUEL,
            fuel_remaining: DEFAULT_FUEL,
            graph_budget: DEFAULT_GRAPH_BUDGET,
            recursion_depth: 0,
            validation_sample_function_names: BTreeSet::new(),
            active_call_keys: HashSet::new(),
        }
    }
}
