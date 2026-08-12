"""Diagnostic for the polar obstruction behind a quadratic P-set.

Normal-play disjunctive sums have XOR-linear outcomes: their P-positions are
subspaces. The proved weighted-source Witt--FIFO arena instead uses interactive
coupling to realize the zero set {v : Q_a(v)=0} of a game-built Gold form. This
probe isolates the obstruction that makes such coupling necessary.

This probe pins down the precise obstruction via the polar form. In char 2,

    Q(u ⊕ v) = Q(u) ⊕ Q(v) ⊕ B(u, v),

so for u, v already in the zero set (Q(u)=Q(v)=0):

    u ⊕ v ∈ {Q=0}   ⟺   B(u, v) = 0.

Therefore {Q=0} fails to be a subspace EXACTLY by the polar form B — and B is the
coin-turning / nim-product bilinear form, which *is* game-realizable (the Product
Theorem / Tartan games). The picture explains the construction's ingredients:

  • the linear part is Grundy/XOR                — game-realizable (Sprague–Grundy);
  • the obstruction to {Q=0} being XOR-closed is exactly B — game-realizable
    (coin-turning products);
  • the play rule must turn the bilinear coupling B into the quadratic outcome Q.

The shipped theorem supplies such an interactive rule through a public Witt
frame, weighted sources, and a pass-free tail. This script independently
confirms that the obstruction is exactly B and measures how far {Q=0} is from
a subspace for the game-built Gold forms.
"""

from common import gold, polar


if __name__ == "__main__":
    hdr = (f"{'field':>7} {'a':>2} {'|Q=0|':>6} {'closed':>7} {'open':>7} "
           f"{'subspace?':>10} {'obstruction=B?':>15}")
    print(hdr)
    print("-" * len(hdr))
    all_obstruction_is_B = True
    for k in (2, 3):                      # F2^4, F2^8 (pairwise scan stays cheap)
        m = 1 << k
        for a in range(1, k + 1):
            zeros = [v for v in range(1 << m) if gold(v, a, m) == 0]
            closed = opened = 0
            obstruction_is_B = True
            for u in zeros:
                for v in zeros:
                    uv_in = gold(u ^ v, a, m) == 0
                    b_zero = polar(u, v, a, m) == 0
                    # the claim: u⊕v ∈ {Q=0}  ⟺  B(u,v)=0
                    if uv_in != b_zero:
                        obstruction_is_B = False
                    if uv_in:
                        closed += 1
                    else:
                        opened += 1
            is_subspace = opened == 0
            all_obstruction_is_B = all_obstruction_is_B and obstruction_is_B
            print(f"  F2^{m:<3} {a:>2} {len(zeros):>6} {closed:>7} {opened:>7} "
                  f"{str(is_subspace):>10} {str(obstruction_is_B):>15}")
    print("-" * len(hdr))
    print("Reading: {Q=0} is NOT a subspace (normal-play disjunctive sums are ruled out),")
    print("and its failure to be closed under ⊕ is governed EXACTLY by the polar form B")
    print(f"(the game-realizable coin-turning form): {all_obstruction_is_B}")
    print()
    print("The realized rule must be interactive: ordinary disjunctive sums give")
    print("only the ruled-out XOR-linear, subspace P-sets.")
