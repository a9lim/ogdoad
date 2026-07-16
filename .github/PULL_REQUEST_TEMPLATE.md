## What

<!-- One or two sentences on what changed -->

## Why

<!-- What problem does this solve? Link issues with "Fixes #N" if applicable -->

## Test plan

- [ ] `cargo test` passes
- [ ] `cargo clippy --all-targets` is warning-clean
- [ ] `cargo fmt --check` is clean
- [ ] If this touched `src/py/` or any core API the bindings call: `cargo check --features python` **and** `cargo clippy --features python --all-targets`
- [ ] If this touched `clifford/` or `scalar/big/surreal/`: rebuilt (`maturin develop`) and ran `demo.py` — Display changes don't surface in `cargo test`
- [ ] If this touched any doc comment (`//!` / `///`): ran `cargo doc --no-deps` **cold** (`RUSTDOCFLAGS="-D warnings"`) and it's link-clean
- [ ] If this added a new operation: there's a test pinning it to an independent oracle (the `associativity_*` / `general_product_reproduces_*` style)

## Claim level

<!-- If this changes prose / comments / examples, label the claims per AGENTS.md:
     standard math · implemented and tested · interpretation · open. New "X is
     true" math statements should be backed by a test or cited, not asserted. -->

## Notes

<!-- Anything reviewers should know. If this touches the metric/product, confirm
     q and b stay independent and signs go through the scalar's neg() — the two
     load-bearing char-2 invariants (see Hard rules in AGENTS.md). -->
