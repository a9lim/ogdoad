//! PyO3 bindings, split along the same pillars as the math core.
//!
//! A fixed catalog of exact and represented-precision scalar backends is
//! exposed as separate Python types. Registered scalar backends also receive
//! monomorphic algebra, multivector, and linear-map classes. Operands from
//! different backends cannot mix, and there is no runtime-tagged any-scalar
//! escape hatch.
//!
//!   - [`scalars`] — scalar types, arithmetic, extensions, and valuation APIs.
//!   - [`engine`] — algebra/MV pairs, linear maps, divided powers, and CGA.
//!   - [`forms`] — quadratic, bilinear, Hermitian, symplectic, and integral forms.
//!   - [`games`] — short/transfinite games, graph kernels, and game invariants.
//!
//! Each submodule registers its own classes and functions through a
//! `pub(crate) fn register`, which the `#[pymodule]` entry point chains
//! together.

use pyo3::prelude::*;

#[macro_use]
mod catalog;
mod engine;
mod forms;
mod games;
mod scalars;

#[pyfunction]
fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[pymodule]
fn ogdoad(m: &Bound<'_, PyModule>) -> PyResult<()> {
    scalars::register(m)?;
    engine::register(m)?;
    forms::register(m)?;
    games::register(m)?;
    m.add_function(wrap_pyfunction!(version, m)?)?;
    Ok(())
}
