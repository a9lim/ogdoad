//! Function arity, recursion-frame, and fuel bookkeeping.

use super::*;

pub(crate) fn function_arity_error(expected: usize, actual: usize) -> OghamError {
    OghamError::new(
        OghamErrorKind::Arity,
        Span::point(0),
        format!("function expects {expected} argument(s), got {actual}"),
    )
}

pub(crate) fn consume_fuel(
    function: &FunctionValue,
    remaining: &mut u128,
    budget: u128,
) -> OghamResult<()> {
    let Some(name) = &function.mu_name else {
        return Ok(());
    };
    if *remaining == 0 {
        return Err(OghamError::new(
            OghamErrorKind::Fuel,
            Span::point(0),
            format!("recursive definition `{name}` exhausted its fuel budget of {budget}"),
        ));
    }
    *remaining -= 1;
    Ok(())
}

pub(crate) fn enter_recursion_frame(
    function: &FunctionValue,
    depth: &mut u128,
    remaining: u128,
    budget: u128,
) -> OghamResult<bool> {
    let Some(name) = &function.mu_name else {
        return Ok(false);
    };
    if *depth >= RECURSION_DEPTH_GUARD {
        return Err(OghamError::new(
            OghamErrorKind::Fuel,
            Span::point(0),
            format!(
                "recursive definition `{name}` reached the recursion depth safety guard ({RECURSION_DEPTH_GUARD} frames); fuel budget {budget} has {remaining} step(s) remaining, but the host stack is not unbounded"
            ),
        ));
    }
    *depth += 1;
    Ok(true)
}

pub(crate) fn leave_recursion_frame(entered: bool, depth: &mut u128) {
    if entered {
        *depth -= 1;
    }
}
