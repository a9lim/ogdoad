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

`ordinary_719_crossed_359th_root_v1.bin` is the first compact payload in the
paper's crossed-tower reduction of the next row `p=719`.

- Size: 438,103 bytes.
- SHA-256:
  `c7385164fedcbb971ff2bb239ef9e0a0d1ccb81b16edd81eee2a139030ba8758`.
- Encoding: the same raw little-endian 179-by-19,580 coefficient bitstream as
  the `p=359` artifact, now encoding `a in F_(2^179)[A]/(F_179(A))`.
- Exact identity: `a^359=(1+x)/c`, where `x` is the checked `p=359` root and
  `c` is derived canonically from its certified nontrivial 359-phase.

The maintained verifier is
`../ordinary_719_crossed_root_certificate.py`. It reconstructs both artifacts,
checks their hashes and padding, and verifies the crossed root equation. Its
`--full-upstream` mode additionally recomputes the inherited `p=359` resultant
norm before checking this payload. This is an exact half-certificate, not the
`p=719` row: the second payload `f_a`, the inner norm `W`, and the final
719-phase have not been computed.
