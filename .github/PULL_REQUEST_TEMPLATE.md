## What

<!-- One or two sentences on what changed -->

## Why

<!-- What problem does this solve? Link issues with "Fixes #N" if applicable -->

## Test plan

- [ ] `cargo fmt --all --check`
- [ ] `cargo test --workspace`
- [ ] `cargo clippy --workspace --all-targets -- -D warnings`
- [ ] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --workspace`
- [ ] If this touched `src/py/` or a core API used by Python: `cargo check -p ogdoad --features python`, the matching Clippy gate, and `python scripts/generate_stubs.py --check`
- [ ] If this touched Lean or a load-bearing proof claim: `(cd formal && lake build --wfail)`
- [ ] If this touched a paper or bibliography: `npm ci` and `python scripts/check_writeups.py`
- [ ] If this added a generic operation: a focused test pins it to an independent oracle

## Claim level

<!-- If this changes prose / comments / examples, label the claims per AGENTS.md:
     standard/cited · implemented and tested · proved here · open. -->

## Notes

<!-- Anything reviewers should know. For metric/product changes, confirm that q,
     b, and optional a stay distinct and generic signs use Scalar::neg. -->
