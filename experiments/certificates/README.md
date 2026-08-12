# Exact finite certificates

`ordinary_359_hilbert_root_v1.bin` is the compact root-coordinate certificate
for the selected ordinary-spine row `p=359`.

- Size: 438,103 bytes.
- SHA-256:
  `c62433e428e6b0942c210b2df2543fcff6a9e444b835ceb5390db1c9e433bd9e`.
- Encoding: raw little-endian bitstream. Bit `179*i+j` is the coefficient of
  `z^j` in the `A^i` coefficient of `y`, for `0 <= i < 19580` and
  `0 <= j < 179`. The final four padding bits are zero.
- Ambient fields:
  `k=F_2[z]/(z^179+z^4+z^2+z+1)` and
  `E=k[A]/(F_179(A))`.

The authoritative verifier is
`../ordinary_359_hilbert_certificate.py --full`. It checks `y^179=A`,
recomputes `theta=Norm_(E/k)(1+y)` as a degree-19,580 resultant, and verifies
that `theta^((2^179-1)/359) != 1`. Default quick mode does not recompute the
norm and is therefore only an integrity smoke test, not the full certificate.

The four `ordinary_719_crossed_*_v1.bin` files form the compact exact
certificate for the row `p=719`.

- Size: 438,103 bytes.
- SHA-256:
  `c7385164fedcbb971ff2bb239ef9e0a0d1ccb81b16edd81eee2a139030ba8758`.
- Encoding: the same raw little-endian 179-by-19,580 coefficient bitstream as
  the `p=359` artifact, now encoding `a in F_(2^179)[A]/(F_179(A))`.
- Exact identity: `a^359=(1+x)/c`, where `x` is the checked `p=359` root and
  `c` is derived canonically from its certified nontrivial 359-phase.

- `ordinary_719_crossed_minpoly_v1.bin` stores the 19,580 non-leading
  coefficients of the monic minimal polynomial `f_a`.  Size: 438,103 bytes.
  SHA-256:
  `66a4aaa3a406d67bc9aba4ae56c9bc218f65d296d7c68725da6b1417854b92de`.
- `ordinary_719_crossed_norm_v1.bin` stores
  `W=v^19580*f_a(v^(-1))` in the fixed `V`-basis.  Size: 8,033 bytes.
  SHA-256:
  `fc00d40eabdba738d950bf17317e68418d0b8813ba3325c1ce35b1975f9569c6`.
- `ordinary_719_crossed_phase_v1.bin` stores the resulting nonidentity
  719-torsion Euler phase.  Size: 8,033 bytes.  SHA-256:
  `da5858b2e53bfce7e83944a41e264a0fa01a3f0a1b030b889239afd383708a81`.

For the two 438,103-byte payloads, bit `179*i+j` is the coefficient of
`z^j A^i` (or `z^j T^i`); the final four padding bits are zero.  For the two
8,033-byte payloads, bit `179*i+j` is the coefficient of `z^j V^i`; the
final three padding bits are zero.

The maintained verifier is `../ordinary_719_crossed_certificate.py`.  Default
mode is an integrity replay: it reconstructs the inherited `p=359` data and
`a`, recomputes `W` and the full Euler phase, and treats the stored `W` and
phase only as checkpoints, but does not establish `f_a(a)=0`.
Authoritative `--full` mode additionally verifies `f_a(a)=0` by dense modular
composition.  `--full-upstream` also recomputes the inherited `p=359`
resultant norm.  The finite computation plus the paper's crossed-tower
deduction proves `m_719=1`; it is not kernel-checked in Lean.
