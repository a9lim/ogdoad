# Security policy

## Threat model

ogdoad is a pure computational library — a Rust crate and an abi3 Python extension
built from it. It has a deliberately small attack surface:

- **No network, no daemon, no persistent state.** It computes in-process and
  returns. There is no listener, no IPC, no background thread.
- **No file, credential, or environment access.** It reads no config and writes no
  files. The Python layer monomorphises the engine to one concrete scalar per
  backend and raises `TypeError` on world-mixing by construction.
- **No untrusted deserialization.** serde is intentionally **not** shipped — the
  invariant-carrying types would need custom deserialization, not a derive — so
  there is no parser to feed a hostile blob to.
- **Memory-safe by construction.** The crate contains **zero** `unsafe` — core and
  bindings alike. The only FFI is what the PyO3 proc-macros generate.

## The realistic surface: panics on out-of-domain input

Several operations panic by design rather than return a wrong answer:

- `Ordinal` nim-multiplication panics past the source-verified Kummer boundary
  (`ω^(ω^ω)`) instead of guessing.
- Singular polar forms and general-bilinear metrics are rejected where a
  nonsingular Witt/Brauer-Wall class is required.
- Malformed dimensions / out-of-range indices panic.

A panic is a controlled abort, not memory corruption. But if you wrap ogdoad in a
**service that accepts untrusted input** and feed it adversarial parameters, a
panic becomes a denial-of-service for that process. Validate and/or catch at your
own trust boundary; don't expose the raw constructors to the open internet.

## Reporting a vulnerability

Email `mx@a9l.im`, or use GitHub's private vulnerability reporting on this repo.
I'll acknowledge within a few days and publish a fix plus an advisory.

For anything non-urgent (a panic on bad input you think should be a clean error,
say), a public issue is fine.
