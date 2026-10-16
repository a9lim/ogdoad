import Ogdoad.MisereOctalCertificate
import Ogdoad.MisereSaturation
import Ogdoad.MisereOctalTerminal

/-!
# Compression of periodic octal witnesses

These declarations operate on the actual whole-, one-, and two-remainder
masks. Persistent offsets are retained through `3 * N + 2 * p` and copied
into the congruent place in `[N, N+p)`. Added moves are translated original
moves, and every late compressed record contains an original tail record.
-/

namespace Ogdoad.MisereOctalCompression

open Set Ogdoad.MisereTransition Ogdoad.MisereOctalCertificate

variable {Q : Type*} [CommMonoid Q]

/-- The uniform maximum offset in the compressed code. -/
def bound (N p : Nat) : Nat := 3 * N + 2 * p

/-- Whole-heap bits are only truncated. -/
def compressedWhole (N p : Nat) (whole : Set Nat) : Set Nat :=
  {k | k ∈ whole ∧ k ≤ bound N p}

/-- Keep small persistent bits and add every congruent representative in the
first period of the asserted periodic tail. -/
def compressedPersistent (N p : Nat) (mask : Set Nat) : Set Nat :=
  {k | (k ∈ mask ∧ k ≤ bound N p) ∨
    (N ≤ k ∧ k < N + p ∧ ∃ t, k + t * p ∈ mask)}

/-- The complete option image of the actual compressed masks. -/
def compressedOptions (x : Nat → Q) (whole one two : Set Nat)
    (N p n : Nat) : Set Q :=
  octalOptions x (compressedWhole N p whole)
    (compressedPersistent N p one) (compressedPersistent N p two) n

omit [CommMonoid Q] in
/-- Iterate a tail period by an arbitrary nonnegative multiple. -/
theorem value_add_period_mul (x : Nat → Q) {N p n : Nat}
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m) (hn : N ≤ n) (t : Nat) :
    x (n + t * p) = x n := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, hperiod (n + t * p) (by omega), ih]

/-- Every compressed bit is at most the advertised bound. -/
theorem compressed_masks_bounded (N p : Nat) (whole one two : Set Nat) :
    MasksBounded (compressedWhole N p whole)
      (compressedPersistent N p one) (compressedPersistent N p two) (bound N p) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ hk => hk.2
  · intro k hk
    rcases hk with hk | hk
    · exact hk.2
    · unfold bound
      omega
  · intro k hk
    rcases hk with hk | hk
    · exact hk.2
    · unfold bound
      omega

/-- Every original prefix option survives truncation. -/
theorem prefix_options_subset (x : Nat → Q) (whole one two : Set Nat)
    {N p n : Nat} (hn : n ≤ bound N p) :
    octalOptions x whole one two n ⊆ compressedOptions x whole one two N p n := by
  rintro q ((hq | hq) | hq)
  · exact Or.inl (Or.inl ⟨hq.1, hq.2, hn⟩)
  · rcases hq with ⟨k, hk, hkn, heq⟩
    exact Or.inl (Or.inr ⟨k, Or.inl ⟨hk, by omega⟩, hkn, heq⟩)
  · rcases hq with ⟨k, hk, hkn, hsplit⟩
    exact Or.inr ⟨k, Or.inl ⟨hk, by omega⟩, hkn, hsplit⟩

/-- Added one-remainder moves have exactly the remainders of translated
original moves, and the source heap values agree by periodicity. -/
theorem copied_one_option_safe (x : Nat → Q) (whole one two : Set Nat)
    {P : Set Q} {N p n k t : Nat}
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hsafe : ∀ m, octalOptions x whole one two m ⊆ Meximal P (x m))
    (hNk : N ≤ k) (hkn : k < n) (hk : k + t * p ∈ one) :
    x (n - k) ∈ Meximal P (x n) := by
  have hsource : x (n + t * p) = x n :=
    value_add_period_mul x hperiod (by omega) t
  rw [← hsource]
  apply hsafe (n + t * p)
  have hidx : n + t * p - (k + t * p) = n - k := by omega
  exact Or.inl (Or.inr ⟨k + t * p, hk, by omega, by rw [hidx]⟩)

/-- Added split moves likewise retain the exact same two remainder heaps. -/
theorem copied_two_option_safe (x : Nat → Q) (whole one two : Set Nat)
    {P : Set Q} {N p n k t : Nat} {q : Q}
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hsafe : ∀ m, octalOptions x whole one two m ⊆ Meximal P (x m))
    (hNk : N ≤ k) (hkn : k + 2 ≤ n) (hk : k + t * p ∈ two)
    (hq : q ∈ splitSet x (n - k)) : q ∈ Meximal P (x n) := by
  have hsource : x (n + t * p) = x n :=
    value_add_period_mul x hperiod (by omega) t
  rw [← hsource]
  apply hsafe (n + t * p)
  have hidx : n + t * p - (k + t * p) = n - k := by omega
  exact Or.inr ⟨k + t * p, hk, by omega, by simpa only [hidx] using hq⟩

/-- All retained and copied moves in the actual compressed masks are safe. -/
theorem compressed_options_subset_meximal (x : Nat → Q) (whole one two : Set Nat)
    {P : Set Q} {N p : Nat}
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hsafe : ∀ m, octalOptions x whole one two m ⊆ Meximal P (x m)) (n : Nat) :
    compressedOptions x whole one two N p n ⊆ Meximal P (x n) := by
  rintro q ((hq | hq) | hq)
  · exact hsafe n (Or.inl (Or.inl ⟨hq.1, hq.2.1⟩))
  · rcases hq with ⟨k, hk, hkn, rfl⟩
    rcases hk with hk | ⟨hNk, _, t, hk⟩
    · exact hsafe n (Or.inl (Or.inr ⟨k, hk.1, hkn, rfl⟩))
    · exact copied_one_option_safe x whole one two hperiod hsafe hNk hkn hk
  · rcases hq with ⟨k, hk, hkn, hsplit⟩
    rcases hk with hk | ⟨hNk, _, t, hk⟩
    · exact hsafe n (Or.inr ⟨k, hk.1, hkn, hsplit⟩)
    · exact copied_two_option_safe x whole one two hperiod hsafe hNk hkn hk hsplit

/-- Every original persistent offset has a retained or copied representative
before the end of the first tail period. -/
theorem persistent_has_representative {mask : Set Nat} {N p k : Nat}
    (hp : 1 ≤ p) (hk : k ∈ mask) :
    ∃ r t, r < N + p ∧ r ≤ k ∧ k = r + t * p ∧
      r ∈ compressedPersistent N p mask := by
  by_cases hsmall : k < N + p
  · refine ⟨k, 0, hsmall, le_rfl, by simp, Or.inl ⟨hk, ?_⟩⟩
    unfold bound
    omega
  · have hNk : N ≤ k := by omega
    have hmod : (k - N) % p < p := Nat.mod_lt _ (by omega)
    have hdiv := Nat.mod_add_div (k - N) p
    rw [Nat.mul_comm p ((k - N) / p)] at hdiv
    have hdecomp : k = (N + (k - N) % p) + ((k - N) / p) * p := by omega
    refine ⟨N + (k - N) % p, (k - N) / p, by omega, by omega,
      hdecomp, Or.inr ⟨by omega, by omega, (k - N) / p, ?_⟩⟩
    rwa [← hdecomp]

/-- A represented residual in a compressed tail heap is beyond the exact
split-convolution stability threshold. -/
theorem represented_residual_stable {N p n r : Nat}
    (hn : bound N p < n) (hr : r < N + p) :
    2 * N + p ≤ n - r := by
  unfold bound at hn
  omega

/-- Shifting the source farther than the removed offset turns residual
congruence into a nonnegative multiple of the period. -/
theorem residual_shift {n r k t L p : Nat}
    (hrn : r ≤ n) (hkr : k = r + t * p) (ht : t ≤ L) :
    n + L * p - k = (n - r) + (L - t) * p := by
  have hmul : t * p ≤ L * p := Nat.mul_le_mul_right p ht
  rw [Nat.sub_mul]
  omega

/-- Every late compressed option set contains an exact original tail option
set of the same source value. The original source is chosen explicitly and
all contributions are compared on the actual masks. -/
theorem tail_options_contain_original (x : Nat → Q) (whole one two : Set Nat)
    {N p d n : Nat} (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hbounded : MasksBounded whole one two d)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (hn : bound N p < n) :
    ∃ m, n ≤ m ∧ x m = x n ∧ 2 * N + p + d ≤ m ∧ d < m ∧
      octalOptions x whole one two m ⊆ compressedOptions x whole one two N p n := by
  let L := d + 2 * N + p
  let m := n + L * p
  have hL : d + 2 * N + p ≤ L * p := by dsimp [L]; nlinarith
  have hnN : N ≤ n := by unfold bound at hn; omega
  have hdm : d < m := by dsimp [m]; omega
  refine ⟨m, by dsimp [m]; omega, value_add_period_mul x hperiod hnN L,
    by dsimp [m]; omega, hdm, ?_⟩
  rintro q ((hq | hq) | hq)
  · have hd : m ≤ d := hbounded.1 m hq.2
    omega
  · rcases hq with ⟨k, hk, _, hq⟩
    obtain ⟨r, t, hr, _, hkr, hrep⟩ := persistent_has_representative (N := N) hp hk
    have hkd : k ≤ d := hbounded.2.1 k hk
    have ht : t ≤ L := by dsimp [L]; nlinarith
    have hres : 2 * N + p ≤ n - r := represented_residual_stable hn hr
    have hrn : r < n := by unfold bound at hn; omega
    have hidx : m - k = (n - r) + (L - t) * p :=
      residual_shift (by omega) hkr ht
    have heq : x (m - k) = x (n - r) := by
      rw [hidx]
      exact value_add_period_mul x hperiod (by omega) (L - t)
    exact Or.inl (Or.inr ⟨r, hrep, hrn, hq.trans heq⟩)
  · rcases hq with ⟨k, hk, _, hq⟩
    obtain ⟨r, t, hr, _, hkr, hrep⟩ := persistent_has_representative (N := N) hp hk
    have hkd : k ≤ d := hbounded.2.2 k hk
    have ht : t ≤ L := by dsimp [L]; nlinarith
    have hres : 2 * N + p ≤ n - r := represented_residual_stable hn hr
    have hrn : r + 2 ≤ n := by unfold bound at hn; omega
    have hidx : m - k = (n - r) + (L - t) * p :=
      residual_shift (by omega) hkr ht
    have heq : splitSet x (m - k) = splitSet x (n - r) := by
      rw [hidx]
      exact value_add_period_mul (splitSet x)
        (fun j hj => splitSet_add_period x hN hp hperiod hj) hres (L - t)
    exact Or.inr ⟨r, hrep, hrn, by simpa only [heq] using hq⟩

/-- **All-heap compression certificate.** Every heap record of the
actual compressed masks belongs to the valid safe saturation of the original
table. The result covers empty baselines, including tails of pure whole-heap
codes, by the terminal-prefix theorem. -/
theorem compressed_records_mem_saturation
    (x : Nat → Q) (whole one two : Set Nat)
    {P : Set Q} {T : Set (Transition Q)} {R : Q → Nat} {a : Q}
    {N p d : Nat}
    (hterminal : Transition.mk 1 ∅ ∈ T)
    (hreduced : Reduced P) (hclosed : Closed T)
    (hparity : ParityTable P T) (hranked : Ranked T R)
    (hstar : Transition.mk a ({1} : Set Q) ∈ T)
    (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hbounded : MasksBounded whole one two d)
    (hone : ∀ k ∈ one, 0 < k)
    (hperiod : ∀ m, N ≤ m → x (m + p) = x m)
    (htrace : ∀ n, octalRecord x whole one two n ∈ T) :
    ∀ n,
      Transition.mk (x n) (compressedOptions x whole one two N p n) ∈ Saturation P T := by
  intro n
  have horigsafe : ∀ m, octalOptions x whole one two m ⊆ Meximal P (x m) :=
    fun m => options_subset_meximal hclosed hparity hranked (htrace m)
  have hsafe := compressed_options_subset_meximal x whole one two hperiod horigsafe n
  have hone' : ∀ k ∈ compressedPersistent N p one, 0 < k := by
    intro k hk
    rcases hk with hk | hk
    · exact hone k hk.1
    · omega
  obtain ⟨m, hnm, hxm, hsub⟩ : ∃ m, n ≤ m ∧ x m = x n ∧
      octalOptions x whole one two m ⊆ compressedOptions x whole one two N p n := by
    by_cases hsmall : n ≤ bound N p
    · exact ⟨n, le_rfl, rfl, prefix_options_subset x whole one two hsmall⟩
    · obtain ⟨m, hnm, hxm, _, _, hsub⟩ :=
        tail_options_contain_original x whole one two (n := n) hN hp hbounded hperiod (by omega)
      exact ⟨m, hnm, hxm, hsub⟩
  by_cases hE : (octalOptions x whole one two m).Nonempty
  · have hbase : Transition.mk (x n) (octalOptions x whole one two m) ∈ T := by
      simpa only [octalRecord, hxm] using htrace m
    exact nonempty_sandwich_mem_saturation hparity hbase hE hsub hsafe
  · have hempty := not_nonempty_iff_eq_empty.mp hE
    have hxm1 : x m = 1 := value_eq_of_options_eq hreduced hclosed hparity hranked
      (htrace m) hterminal hempty
    have hxn1 : x n = 1 := hxm.symm.trans hxm1
    have hprefix : ∀ j, 0 < j → j < n → x j = 1 ∨ x j = a := by
      intro j hj hjn
      exact Ogdoad.MisereOctalTerminal.value_before_terminal_eq_one_or_star
        hterminal hreduced hclosed hparity hranked hstar
        (fun k _ _ => htrace k) hempty hj (by omega)
    have ha2 := Ogdoad.MisereParityTrace.star_square_eq_one
      hterminal hreduced hclosed hparity hranked hstar
    have hpair := Ogdoad.MisereOctalTerminal.options_mem_pair_of_prefix ha2 hone' hprefix
      (whole := compressedWhole N p whole) (two := compressedPersistent N p two)
    have hmem : Transition.mk (x n) (compressedOptions x whole one two N p n) ∈ T := by
      rw [hxn1]
      exact Ogdoad.MisereOctalTerminal.safe_pair_record_mem_table
        hterminal hreduced hclosed hparity hranked hstar hpair (by simpa [hxn1] using hsafe)
    exact subset_saturation hclosed hparity hranked hmem

end Ogdoad.MisereOctalCompression
