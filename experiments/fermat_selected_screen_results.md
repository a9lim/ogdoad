# Conway–Fermat selected screens

Exact FQ_NMOD runs of
[fermat_selected_screen.py](fermat_selected_screen.py). Each row evaluates the selected Fibonacci residue
`S_(F_n / ell)(X)` modulo `A_(n-1)(X)` in the literal selected Conway
polynomial basis. The degree and SHA-256 columns fingerprint the nonzero
residue encoded as the minimal big-endian byte string of its coefficient
bitset. The stdlib and FLINT backends agree bit-for-bit at the F_5 / 641
orientation gate; a four-thread F_14 rerun reproduced its recorded hash, and
the F_17 smaller-factor hash also reproduced an independent FLINT run.

The large runs used the reproducible command shape

```sh
uv run --no-project --with python-flint python \
  experiments/fermat_selected_screen.py --backend flint --flint-threads 4 \
  --level N --factor P
```

| n | degree of A_(n-1) | weight | published prime factor ell | residue degree | residue SHA-256 |
|---:|---:|---:|---:|---:|:---|
| 12 | 4096 | 2093 | 114689 | 4095 | 45c962aba17a4607beb105e8a83107fa29c4c6ed67f0df28992fb87add07fc5b |
| 12 | 4096 | 2093 | 26017793 | 4095 | 5797da1fc4d049195b519e3a6a0f5c6b5f42b65b45fbad996f91d11cb2cde93b |
| 12 | 4096 | 2093 | 63766529 | 4095 | bcf9b8a67bee0e7615d3ad5fd2e5661b5f49aa746ed29a1e07978d91d971242f |
| 12 | 4096 | 2093 | 190274191361 | 4093 | 6e29ca2d247a32dfc08f274013504bf3ad77ea89096c835ea194ec11fee9b011 |
| 12 | 4096 | 2093 | 1256132134125569 | 4095 | 06edb91d42cef75fd82edf1a83443d09f7971c73c05de0fddefca32eb559dfb0 |
| 12 | 4096 | 2093 | 568630647535356955169033410940867804839360742060818433 | 4094 | a645dff3d25b7b8481210f6d01c66bee24e4e420b15e8074cf8f81c0a2ebcb35 |
| 13 | 8192 | 4119 | 2710954639361 | 8190 | cec4b19c0d495312028a87ee287fb8f25f6aadb8a53e9955a5399885ff7661fc |
| 13 | 8192 | 4119 | 2663848877152141313 | 8191 | 3bcde5dd0d596ea273db6c20587617d16c9398579c75e4705a3a84f93cc796ac |
| 13 | 8192 | 4119 | 3603109844542291969 | 8191 | 41834f10d02eb475cfe1c3ab529f50ce071cdecf198b31b00b6d7ce6fc516993 |
| 13 | 8192 | 4119 | 319546020820551643220672513 | 8184 | f938a1c671bbb9d87190a8839106732027a085e2e33b1a67c6ffd3fd96d75823 |
| 14 | 16384 | 8179 | 116928085873074369829035993834596371340386703423373313 | 16382 | 45e69ddeea1d7b32db48ddf26683a85909b59c1c351565d089a4480a76102e0f |
| 15 | 32768 | 16369 | 1214251009 | 32764 | 8948df1a005c37ac313f3498d7f846a5a2c419977e49d02d723d1af68fd66af6 |
| 15 | 32768 | 16369 | 2327042503868417 | 32767 | d8674cdf25809f7af5be1027583163ab8112b5657416d2952aaed68f733fdd12 |
| 15 | 32768 | 16369 | 168768817029516972383024127016961 | 32767 | d34d662c1281bce7d58711c71700ca9eb9b2dc707f3095f8489ebf4c64942047 |
| 16 | 65536 | 32809 | 825753601 | 65535 | bcc1e0f8f563382f62860ccec2291a0125a713940680774e7372379bedea7c81 |
| 16 | 65536 | 32809 | 188981757975021318420037633 | 65534 | 905c7e8cf6b2148c69549a8021409099f6b4423f9045398cf57ed960a70e233c |
| 17 | 131072 | 65521 | 31065037602817 | 131069 | 172e671f4a403fa5ac50b35787543e84f6567254535ac317cc37649cdf2c5e0e |
| 17 | 131072 | 65521 | 7751061099802522589358967058392886922693580423169 | 131069 | 51d4c1aa1939ae6992f16ba743f9da7a44c6a6bc0f255247a44dbc6f4c19221a |
| 18 | 262144 | 131087 | 13631489 | 262141 | 24e4063e1b929aea357b957a29b0490312fbd57e73b19dfba28d16bdb7c074d4 |
| 18 | 262144 | 131087 | 81274690703860512587777 | 262143 | 068c5f4db4a49df0029f47b40876db6afc69ca056c69954e733a3ac1d4246c7c |

Every displayed residue is nonzero. This certifies only the listed primary
coordinates. [FermatSearch's factor list](https://www.fermatsearch.org/factors/faclist.php)
and [compositeness table](https://www.fermatsearch.org/factors/composite.php)
list exact composite residual cofactors `C1133`,
`C2391`, `C4880`, `C9808`, `C19694`, `C39395`, and `C78884` at levels 12 through 18,
respectively, so none of these levels is fully certified. The database
supplies primality of the displayed factors; the script checks their exact
divisibility but does not vendor primality certificates. Hashes are
reproducibility fingerprints, not standalone formal proof certificates.

The same exact computation was also applied to each complete residual
cofactor from `F_15` through `F_18`, formed as the exact quotient of `F_n` by
the product of the published factors above:

| n | residual block | residue degree | residue SHA-256 |
|---:|:---|---:|:---|
| 15 | `C9808` | 32765 | 67de3b858a5f2373bb687e36bf539fc51925403da0825b0469c321d8c40ce69a |
| 16 | `C19694` | 65534 | 112b3411586c9466974e2de94379efb23bc66e2262f7aa577bde9dfcc9a515ae |
| 17 | `C39395` | 131071 | c851b53bdd40ae1dfb4d71707c019b492216add315fdd148b165eeae1e9e6d6c |
| 18 | `C78884` | 262143 | 2b4cbf133c1716b0be03b08cf9b3afdba283ece90483eba93b894f1db19e05af |

All four residues are nonzero. Together with the individual published-factor
tests, this excludes every proper divisor assembled as a product of the
available pairwise-coprime blocks: 14 products at level 15 and six at each of
levels 16--18. It proves that the selected logarithm is not divisible by any
complete displayed residual cofactor. A proper unknown divisor of a residual
cofactor can still divide the selected logarithm, so this does not certify an
unknown prime coordinate or any complete level.

The script's dependency-free `--jet-only` mode also computes the exact
factor-sensitive arithmetic obstruction
`Gamma_(n,ell)=gcd(F_n/ell, 3*2^v2(ell-1)+1)` in the odd half-index branch
(and the corresponding coefficient-one expression in the even branch).
Every factor in the table above has arithmetic gcd one. Conditional on a
hypothetical selected failure, this proves the first Hasse jet not already
forced by the quotient residue is nonzero at all displayed coordinates. It
does not prove the selected residue nonzero, maximal order, or any unlisted
factor.
