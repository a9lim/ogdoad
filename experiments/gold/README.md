# Exploratory Gold-form probes

This directory contains non-authoritative exploratory variants and independent
toy implementations. It is not imported by the package or run by CI. The live
Gold--Arf theorem is in `writeups/goldarf.tex`; its maintained executable
surfaces are the top-level experiments and the Rust/Lean modules named there.

Do not rely on filenames such as `final`, `check`, or `verify` as evidence.
Inspect the implementation and mathematical contract before reuse. Promote a
valuable oracle to the maintained top-level `experiments/` directory with
resource guards, tests, and a current paper or `docs/VERIFY.md` reference.
