# Security policy

## Threat model

ogdoad is a pure computational library: a Rust crate and an abi3 Python
extension built from it. Its attack surface is deliberately small.

- **No network, daemon, or persistence.** It computes in-process and returns;
  there is no listener or IPC.
- **No file, credential, or environment access.** It reads no configuration
  and writes no files.
- **No untrusted deserialization.** serde is not a dependency; the
  invariant-carrying types would need custom deserialization rather than a
  derive, so there is no parser to feed a hostile blob to.
- **No `unsafe`.** The crate contains no `unsafe` code, core and bindings
  alike; the only FFI is what the PyO3 proc-macros generate.
- **No world-mixing.** The Python layer monomorphizes each backend: arithmetic
  across scalar worlds raises `TypeError`, and cross-world equality compares
  unequal.

## The realistic surface: panics on out-of-domain input

Most out-of-domain requests return a domain error or `None`: singular or
general-bilinear metrics passed to a Witt, Brauer--Wall, or classification
API, budget exhaustion, and checked arithmetic at a representation boundary.
A few operations panic by design instead of returning a wrong answer:

- `Integer` and `Rational` arithmetic panics on `i128` overflow.
- `Ordinal`'s `Scalar` multiplication panics when the checked nim product
  would leave the represented Kummer rows; `Ordinal::nim_mul` itself returns
  `None`.
- Unchecked convenience constructors and accessors panic on malformed
  dimensions or out-of-range indices (checked APIs return errors), as do a few
  documented preconditions such as `Cga::new` and `reverse` on a
  characteristic-two general-bilinear metric.

In Python, validated arguments raise `ValueError`, panics at a guarded scalar
boundary are converted to `ValueError`, and any other panic surfaces as
`pyo3_runtime.PanicException`, which derives from `BaseException`.

A panic unwinds; it is not memory corruption. If you wrap ogdoad in a
**service that accepts untrusted input**, an adversarial parameter can still
abort that request or process. Validate inputs and catch panics at your own
trust boundary rather than exposing raw constructors to the open internet.

## Reporting a vulnerability

Email `mx@a9l.im`, or use GitHub's private vulnerability reporting on this
repository. Reports are acknowledged within a few days, followed by a fix and
an advisory.

For anything non-urgent — say, a panic on bad input that should be a clean
error — a public issue is fine.
