import Ogdoad.FifoOuterFan

/-!
# The protected dummy fan

After the root prefix `O_x,O_d,O_z`, the complete defender fan consisting
of `C_x` and every still-available real `OPEN` has odd cardinality, while its
entire universal live-star prefix is zero.  Thus the protected `B'` branch
can be rewritten as a prefix-free odd continuation cap.

This is an exact prefix identity, not a contraction of those continuations.
The residual affine class is the same protected dummy class isolated by
`FifoOuterFan.lean`.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- After `O_x,O_d,O_z`, the prefix of the complete odd defender fan
`C_x` plus every remaining real `OPEN` is zero in the universal edge space. -/
theorem protected_dummy_complete_fan_prefix_zero
    (R : Finset V) (d x z : V)
    (hdR : d ∉ R) (hxR : x ∈ R) (hzR : z ∈ R) (hxz : x ≠ z) :
    liveStarVector (insert d R) x +
        liveStarVector (insert d R) d +
        liveStarVector (insert d R) z +
        ∑ w ∈ (R.erase x).erase z, liveStarVector (insert d R) w = 0 := by
  have hzErase : z ∈ R.erase x := by simp [hzR, Ne.symm hxz]
  have hRsplit :
      liveStarVector (insert d R) x +
          liveStarVector (insert d R) z +
          ∑ w ∈ (R.erase x).erase z, liveStarVector (insert d R) w =
        ∑ w ∈ R, liveStarVector (insert d R) w := by
    rw [← Finset.sum_erase_add _ _ hxR]
    rw [← Finset.sum_erase_add _ _ hzErase]
    abel
  calc
    liveStarVector (insert d R) x +
          liveStarVector (insert d R) d +
          liveStarVector (insert d R) z +
          ∑ w ∈ (R.erase x).erase z, liveStarVector (insert d R) w =
        liveStarVector (insert d R) d +
          (liveStarVector (insert d R) x +
            liveStarVector (insert d R) z +
            ∑ w ∈ (R.erase x).erase z,
              liveStarVector (insert d R) w) := by abel
    _ = liveStarVector (insert d R) d +
          ∑ w ∈ R, liveStarVector (insert d R) w := by rw [hRsplit]
    _ = 0 := by
      have htotal := sum_liveStarVector_eq_zero (insert d R)
      rw [Finset.sum_insert hdR] at htotal
      exact htotal

omit [Fintype V] in
/-- On an even real board, the complete fan after the protected dummy branch
has odd cardinality: one `CLOSE` plus one `OPEN` for every real vertex other
than the already opened `x,z`. -/
theorem protected_dummy_complete_fan_card_odd
    (R : Finset V) (x z : V)
    (hxR : x ∈ R) (hzR : z ∈ R) (hxz : x ≠ z)
    (hR : R.card % 2 = 0) :
    (1 + ((R.erase x).erase z).card) % 2 = 1 := by
  have hzErase : z ∈ R.erase x := by simp [hzR, Ne.symm hxz]
  have hxcard := Finset.card_erase_add_one hxR
  have hzcard := Finset.card_erase_add_one hzErase
  omega

end

end Ogdoad.Fifo
