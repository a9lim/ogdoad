import Ogdoad.FifoRootGadgetBoundary
import Ogdoad.FifoSingletonForkBoundary

/-!
# The private-leaf poison boundary

Attaching one private leaf `z` to a prospective first opener `x` is the most
natural attempt to poison the isolated-dummy reply below `OPEN x`.  Exact
minimax data suggest a strong exchange law: the replies `OPEN d` and `OPEN z`
have complementary nonmover outcomes.  This file separates the elementary
part of that phenomenon from the still nontrivial strategy transport.

The two CLOSE children differ by exactly one score unit.  The reason is
graph-theoretic and universal: replacing the untouched private leaf by the
isolated dummy removes precisely the edge `x--z`.  A complete reply-duality
would therefore rule out the leaf-poison construction immediately.  The
three-label edge-plus-isolate board proves the exchange law exactly in the
smallest instance.

The general strategy-level exchange is deliberately exposed as a predicate,
not asserted as a theorem.  Its missing step is the active singleton-ko wall:
after closing `x`, swapping the untouched dummy with the queued private leaf
also changes which physical seat sees the unit score translation.  Bridging
that seat change is equivalent to proving coldness for a queued isolate with
a second isolate still untouched.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- `z` has the single neighbour `x`.  In particular, it is a leaf and its
attachment is disjoint from every other part of a proposed poison gadget. -/
def IsPrivateLeaf (G : SimpleGraph V) (z x : V) : Prop :=
  ∀ v, G.Adj z v ↔ v = x

omit [Fintype V] [DecidableEq V] in
theorem IsPrivateLeaf.adj (h : IsPrivateLeaf G z x) : G.Adj z x :=
  (h x).2 rfl

omit [Fintype V] [DecidableEq V] in
theorem IsPrivateLeaf.ne (h : IsPrivateLeaf G z x) : z ≠ x := by
  intro hzx
  subst x
  exact (G.loopless.irrefl z) h.adj

omit [Fintype V] [DecidableEq V] in
theorem IsPrivateLeaf.adj_iff (h : IsPrivateLeaf G z x) (v : V) :
    G.Adj v z ↔ v = x := by
  rw [G.adj_comm]
  exact h v

/-- The carrier remaining after deleting the opener, dummy, and private
leaf. -/
def privateLeafResidual (x d z : V) : Finset V :=
  ((Finset.univ.erase x).erase d).erase z

theorem privateLeafResidual_not_mem_x (x d z : V) :
    x ∉ privateLeafResidual x d z := by
  simp [privateLeafResidual]

theorem privateLeafResidual_not_mem_d (x d z : V) :
    d ∉ privateLeafResidual x d z := by
  simp [privateLeafResidual]

theorem privateLeafResidual_not_mem_z (x d z : V) :
    z ∉ privateLeafResidual x d z := by
  simp [privateLeafResidual]

/-- Replacing the private leaf in the untouched carrier by an isolated dummy
changes the charge of `x` by exactly one.  This is the universal algebraic
core of the private-leaf exchange. -/
theorem privateLeaf_dummy_charge_dual
    {G : SimpleGraph V} {x d z : V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d) :
    flip G (insert z (privateLeafResidual x d z)) x =
      flip G (insert d (privateLeafResidual x d z)) x + 1 := by
  rw [flip_insert_of_not_mem (privateLeafResidual_not_mem_z x d z),
    flip_insert_of_not_mem (privateLeafResidual_not_mem_d x d z)]
  have hxz : adjacencyBit G x z = 1 := by
    simp [adjacencyBit, (hleaf.adj_iff x).2 rfl]
  have hxd : adjacencyBit G x d = 0 := by
    have hnot : ¬G.Adj x d := fun hxd ↦ hd x ((G.adj_comm x d).mp hxd)
    simp [adjacencyBit, hnot]
  rw [hxz, hxd, add_zero]

omit [Fintype V] in
/-- Arbitrary-carrier version of the same charge identity.  The common
carrier need only omit the dummy and private leaf. -/
theorem privateLeaf_dummy_charge_dual_of_disjoint
    {G : SimpleGraph V} {x d z : V} {U : Finset V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d)
    (hzU : z ∉ U) (hdU : d ∉ U) :
    flip G (insert z U) x = flip G (insert d U) x + 1 := by
  rw [flip_insert_of_not_mem hzU, flip_insert_of_not_mem hdU]
  have hxz : adjacencyBit G x z = 1 := by
    simp [adjacencyBit, (hleaf.adj_iff x).2 rfl]
  have hxd : adjacencyBit G x d = 0 := by
    have hnot : ¬G.Adj x d := fun h ↦ hd x ((G.adj_comm x d).mp h)
    simp [adjacencyBit, hnot]
  rw [hxz, hxd, add_zero]

/-- Canonical CLOSE child of the reply which opened the isolated dummy. -/
def privateLeafDummyCloseState
    (G : SimpleGraph V) (x d z : V) : State V where
  untouched := insert z (privateLeafResidual x d z)
  queue := [d]
  ko := false
  toMove := true
  score := flip G (insert z (privateLeafResidual x d z)) x

/-- Canonical CLOSE child of the reply which opened the private leaf. -/
def privateLeafRealCloseState
    (G : SimpleGraph V) (x d z : V) : State V where
  untouched := insert d (privateLeafResidual x d z)
  queue := [z]
  ko := false
  toMove := true
  score := flip G (insert d (privateLeafResidual x d z)) x

/-- The two displayed CLOSE-child scores are unit translates. -/
theorem privateLeaf_closeState_scores_dual
    {G : SimpleGraph V} {x d z : V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d) :
    (privateLeafDummyCloseState G x d z).score =
      (privateLeafRealCloseState G x d z).score + 1 := by
  exact privateLeaf_dummy_charge_dual hleaf hd

omit [Fintype V] [DecidableEq V] in
theorem privateLeaf_dummy_ne_opener
    {G : SimpleGraph V} {x d z : V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d) : d ≠ x := by
  intro hdx
  subst d
  exact hd z ((G.adj_comm z x).mp hleaf.adj)

omit [Fintype V] [DecidableEq V] in
theorem privateLeaf_dummy_ne_leaf
    {G : SimpleGraph V} {x d z : V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d) : d ≠ z := by
  intro hdz
  subst d
  exact hd x hleaf.adj

/-- The two graph-independent reply states have canonical CLOSE children,
and their scores differ by one.  This theorem packages the exact local
calculation without any minimax assumption. -/
theorem privateLeaf_reply_close_children
    {G : SimpleGraph V} {x d z : V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d) :
    step G (afterInitialTwoOpens x d) .close =
        some (privateLeafDummyCloseState G x d z) ∧
      step G (afterInitialTwoOpens x z) .close =
        some (privateLeafRealCloseState G x d z) ∧
      (privateLeafDummyCloseState G x d z).score =
        (privateLeafRealCloseState G x d z).score + 1 := by
  have hdx : d ≠ x := privateLeaf_dummy_ne_opener hleaf hd
  have hdz : d ≠ z := privateLeaf_dummy_ne_leaf hleaf hd
  have hzx : z ≠ x := hleaf.ne
  have hxd : x ≠ d := hdx.symm
  have hzd : z ≠ d := hdz.symm
  have hxz : x ≠ z := hzx.symm
  have hUd : ((Finset.univ.erase x).erase d : Finset V) =
      insert z (privateLeafResidual x d z) := by
    ext v
    by_cases hvx : v = x <;> by_cases hvd : v = d <;>
      by_cases hvz : v = z <;>
      simp [privateLeafResidual, hvx, hvd, hvz, hdx, hdz, hzx,
        hxd, hzd, hxz] at *
  have hUz : ((Finset.univ.erase x).erase z : Finset V) =
      insert d (privateLeafResidual x d z) := by
    ext v
    by_cases hvx : v = x <;> by_cases hvd : v = d <;>
      by_cases hvz : v = z <;>
      simp [privateLeafResidual, hvx, hvd, hvz, hdx, hdz, hzx,
        hxd, hzd, hxz] at *
  refine ⟨?_, ?_, privateLeaf_closeState_scores_dual hleaf hd⟩
  · simp [step, afterInitialTwoOpens, privateLeafDummyCloseState, hUd]
  · simp [step, afterInitialTwoOpens, privateLeafRealCloseState, hUz]

/-- The conjectured strategy-level exchange at the two replies below one
first opener.  This definition is an explicit proof obligation, not an
assumption made elsewhere. -/
def PrivateLeafReplyDual (G : SimpleGraph V) (x d z : V) : Prop :=
  EvenWins G true (afterInitialTwoOpens x d) ↔
    OddWins G true (afterInitialTwoOpens x z)

/-! ## Simultaneous A/N/C induction interface -/

/-- Active left state: `x` is followed by the dummy, while the private leaf
is still untouched. -/
def privateLeafActiveLeft (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) : State V where
  untouched := insert z U
  queue := x :: d :: q
  ko := false
  toMove := turn
  score := score

/-- Active right state with the roles of the dummy and private leaf swapped. -/
def privateLeafActiveRight (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) : State V where
  untouched := insert d U
  queue := x :: z :: q
  ko := false
  toMove := turn
  score := score

/-- Resolved left state after opening the private leaf from the active left
state. -/
def privateLeafResolvedLeft (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) : State V where
  untouched := U
  queue := x :: d :: (q ++ [z])
  ko := false
  toMove := turn
  score := score

/-- Resolved right state after opening the dummy from the active right
state. -/
def privateLeafResolvedRight (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) : State V where
  untouched := U
  queue := x :: z :: (q ++ [d])
  ko := false
  toMove := turn
  score := score

/-- Left CLOSE state.  Its displayed score includes the charge of `x`. -/
def privateLeafClosedLeft (G : SimpleGraph V) (x d z : V)
    (U : Finset V) (q : List V) (turn : Bool) (score : ZMod 2) : State V where
  untouched := insert z U
  queue := d :: q
  ko := false
  toMove := turn
  score := score + flip G (insert z U) x

/-- Right CLOSE state.  The isolated dummy replaces the private leaf in the
untouched carrier. -/
def privateLeafClosedRight (G : SimpleGraph V) (x d z : V)
    (U : Finset V) (q : List V) (turn : Bool) (score : ZMod 2) : State V where
  untouched := insert d U
  queue := z :: q
  ko := false
  toMove := turn
  score := score + flip G (insert d U) x

omit [Fintype V] in
/-- The arbitrary C-pair carries exactly one unit of relative score debt. -/
theorem privateLeafClosed_scores_dual
    {G : SimpleGraph V} {x d z : V} {U : Finset V} {q : List V}
    {turn : Bool} {score : ZMod 2}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d)
    (hzU : z ∉ U) (hdU : d ∉ U) :
    (privateLeafClosedLeft G x d z U q turn score).score =
      (privateLeafClosedRight G x d z U q turn score).score + 1 := by
  simp only [privateLeafClosedLeft, privateLeafClosedRight]
  rw [privateLeaf_dummy_charge_dual_of_disjoint hleaf hd hzU hdU]
  abel

/-- The two canonical root replies are the active A-pair at empty common
queue and zero score. -/
theorem privateLeaf_replies_eq_active
    {G : SimpleGraph V} {x d z : V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d) :
    afterInitialTwoOpens x d =
        privateLeafActiveLeft x d z (privateLeafResidual x d z) [] false 0 ∧
      afterInitialTwoOpens x z =
        privateLeafActiveRight x d z (privateLeafResidual x d z) [] false 0 := by
  have hdx : d ≠ x := privateLeaf_dummy_ne_opener hleaf hd
  have hdz : d ≠ z := privateLeaf_dummy_ne_leaf hleaf hd
  have hzx : z ≠ x := hleaf.ne
  have hxd : x ≠ d := hdx.symm
  have hzd : z ≠ d := hdz.symm
  have hxz : x ≠ z := hzx.symm
  have hUd : ((Finset.univ.erase x).erase d : Finset V) =
      insert z (privateLeafResidual x d z) := by
    ext v
    by_cases hvx : v = x <;> by_cases hvd : v = d <;>
      by_cases hvz : v = z <;>
      simp [privateLeafResidual, hvx, hvd, hvz, hdx, hdz, hzx,
        hxd, hzd, hxz] at *
  have hUz : ((Finset.univ.erase x).erase z : Finset V) =
      insert d (privateLeafResidual x d z) := by
    ext v
    by_cases hvx : v = x <;> by_cases hvd : v = d <;>
      by_cases hvz : v = z <;>
      simp [privateLeafResidual, hvx, hvd, hvz, hdx, hdz, hzx,
        hxd, hzd, hxz] at *
  constructor
  · simp [afterInitialTwoOpens, privateLeafActiveLeft, hUd]
  · simp [afterInitialTwoOpens, privateLeafActiveRight, hUz]

/-- Exact simultaneous target observed for active pairs: both current movers
win the zero target, while the two nonmover coordinates are complementary. -/
def PrivateLeafActiveInvariant (G : SimpleGraph V) (left right : State V) : Prop :=
  MoverEvenWins G left ∧ MoverEvenWins G right ∧
    (NonmoverEvenWins G left ↔ ¬NonmoverEvenWins G right)

/-- Target for the special-OPEN pair: the sheets agree and their mover
coordinate is even. -/
def PrivateLeafResolvedInvariant
    (G : SimpleGraph V) (left right : State V) : Prop :=
  MoverEvenWins G left ∧ MoverEvenWins G right ∧
    (NonmoverEvenWins G left ↔ NonmoverEvenWins G right)

/-- Target for the CLOSE pair: each endpoint is cold, and the two cold
outcomes are complementary. -/
def PrivateLeafClosedInvariant
    (G : SimpleGraph V) (left right : State V) : Prop :=
  (MoverEvenWins G left ↔ NonmoverEvenWins G left) ∧
    (MoverEvenWins G right ↔ NonmoverEvenWins G right) ∧
    (MoverEvenWins G left ↔ ¬MoverEvenWins G right)

omit [Fintype V] in
/-- The three elementary edges out of an active left state.  The last edge
is the common base OPEN which the Bellman obstruction below shows cannot be
discarded. -/
theorem privateLeafActiveLeft_steps
    (G : SimpleGraph V) (x d z r : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2)
    (hzU : z ∉ U) (hr : r ∈ U) :
    step G (privateLeafActiveLeft x d z U q turn score) (.open z) =
        some (privateLeafResolvedLeft x d z U q (!turn) score) ∧
      step G (privateLeafActiveLeft x d z U q turn score) .close =
        some (privateLeafClosedLeft G x d z U q (!turn) score) ∧
      step G (privateLeafActiveLeft x d z U q turn score) (.open r) =
        some (privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
          (!turn) score) := by
  have hzr : z ≠ r := by
    intro h
    subst r
    exact hzU hr
  constructor
  · simp [step, privateLeafActiveLeft, privateLeafResolvedLeft, hzU]
  constructor
  · simp [step, privateLeafActiveLeft, privateLeafClosedLeft]
  · have hr' : r ∈ insert z U := Finset.mem_insert_of_mem hr
    have hErase : (insert z U).erase r = insert z (U.erase r) := by
      ext v
      simp only [Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro ⟨hvr, hvz | hvU⟩
        · exact Or.inl hvz
        · exact Or.inr ⟨hvr, hvU⟩
      · rintro (rfl | ⟨hvr, hvU⟩)
        · exact ⟨hzr, Or.inl rfl⟩
        · exact ⟨hvr, Or.inr hvU⟩
    simp [step, privateLeafActiveLeft, hr', hErase]

omit [Fintype V] in
/-- Exact Bellman equations for an active left state.  They expose the
polarity that a mutual A/N/C proof must satisfy.  The current mover needs a
nonmover win in at least one child; the current nonmover needs mover wins in
all children.  In particular, the special OPEN reaches `N` on its nonmover
coordinate, not its mover coordinate. -/
theorem privateLeafActiveLeft_bellman
    (G : SimpleGraph V) (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) (hzU : z ∉ U) :
    (EvenWins G turn (privateLeafActiveLeft x d z U q turn score) ↔
      EvenWins G turn (privateLeafResolvedLeft x d z U q (!turn) score) ∨
      EvenWins G turn
        (privateLeafClosedLeft G x d z U q (!turn) score) ∨
      ∃ r ∈ U, EvenWins G turn
        (privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
          (!turn) score)) ∧
    (EvenWins G (!turn) (privateLeafActiveLeft x d z U q turn score) ↔
      EvenWins G (!turn)
          (privateLeafResolvedLeft x d z U q (!turn) score) ∧
      EvenWins G (!turn)
          (privateLeafClosedLeft G x d z U q (!turn) score) ∧
      ∀ r ∈ U, EvenWins G (!turn)
        (privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
          (!turn) score)) := by
  let A := privateLeafActiveLeft x d z U q turn score
  let N := privateLeafResolvedLeft x d z U q (!turn) score
  let C := privateLeafClosedLeft G x d z U q (!turn) score
  let R := fun r ↦ privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
    (!turn) score
  have hspecial : step G A (.open z) = some N := by
    simp [A, N, step, privateLeafActiveLeft, privateLeafResolvedLeft, hzU]
  have hclose : step G A .close = some C := by
    simp [A, C, step, privateLeafActiveLeft, privateLeafClosedLeft]
  have hcommon : ∀ r ∈ U, step G A (.open r) = some (R r) := by
    intro r hr
    have hall := privateLeafActiveLeft_steps G x d z r U q turn score hzU hr
    simpa [A, R] using hall.2.2
  constructor
  · constructor
    · intro hwin
      cases hwin with
      | terminal _ hterminal _ =>
          simp [Terminal, privateLeafActiveLeft] at hterminal
      | answer _ hseat _ _ =>
          exact False.elim (hseat (by simp [privateLeafActiveLeft]))
      | choose _ _ m t hstep tail =>
          cases m with
          | «open» v =>
              have hv : v ∈ insert z U := by
                simp only [step, privateLeafActiveLeft] at hstep
                split at hstep
                · assumption
                · contradiction
              rcases Finset.mem_insert.mp hv with rfl | hvU
              · rw [hspecial] at hstep
                have ht : t = N := Option.some.inj hstep.symm
                subst t
                exact Or.inl tail
              · have hr := hcommon v hvU
                rw [hr] at hstep
                have ht : t = R v := Option.some.inj hstep.symm
                subst t
                exact Or.inr (Or.inr ⟨v, hvU, tail⟩)
          | close =>
              rw [hclose] at hstep
              have ht : t = C := Option.some.inj hstep.symm
              subst t
              exact Or.inr (Or.inl tail)
          | pass => simp [step, privateLeafActiveLeft] at hstep
    · rintro (hN | hC | ⟨r, hr, hR⟩)
      · exact EvenWins.choose A (by simp [A, privateLeafActiveLeft])
          (.open z) N hspecial hN
      · exact EvenWins.choose A (by simp [A, privateLeafActiveLeft])
          .close C hclose hC
      · exact EvenWins.choose A (by simp [A, privateLeafActiveLeft])
          (.open r) (R r) (hcommon r hr) hR
  · constructor
    · intro hwin
      cases hwin with
      | terminal _ hterminal _ =>
          simp [Terminal, privateLeafActiveLeft] at hterminal
      | choose _ hseat _ _ _ _ =>
          simp [privateLeafActiveLeft] at hseat
      | answer _ _ _ children =>
          refine ⟨children (.open z) N hspecial,
            children .close C hclose, ?_⟩
          intro r hr
          exact children (.open r) (R r) (hcommon r hr)
    · rintro ⟨hN, hC, hR⟩
      refine EvenWins.answer A (by simp [A, privateLeafActiveLeft])
        ⟨.open z, N, hspecial⟩ ?_
      intro m t hstep
      cases m with
      | «open» v =>
          have hv : v ∈ insert z U := by
            simp only [step, A, privateLeafActiveLeft] at hstep
            split at hstep
            · assumption
            · contradiction
          rcases Finset.mem_insert.mp hv with rfl | hvU
          · rw [hspecial] at hstep
            have ht : t = N := Option.some.inj hstep.symm
            subst t
            exact hN
          · have hr := hcommon v hvU
            rw [hr] at hstep
            have ht : t = R v := Option.some.inj hstep.symm
            subst t
            exact hR v hvU
      | close =>
          rw [hclose] at hstep
          have ht : t = C := Option.some.inj hstep.symm
          subst t
          exact hC
      | pass => simp [step, A, privateLeafActiveLeft] at hstep

omit [Fintype V] in
/-- The symmetric Bellman equations for the active right state. -/
theorem privateLeafActiveRight_bellman
    (G : SimpleGraph V) (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) (hdU : d ∉ U) :
    (EvenWins G turn (privateLeafActiveRight x d z U q turn score) ↔
      EvenWins G turn (privateLeafResolvedRight x d z U q (!turn) score) ∨
      EvenWins G turn
        (privateLeafClosedRight G x d z U q (!turn) score) ∨
      ∃ r ∈ U, EvenWins G turn
        (privateLeafActiveRight x d z (U.erase r) (q ++ [r])
          (!turn) score)) ∧
    (EvenWins G (!turn) (privateLeafActiveRight x d z U q turn score) ↔
      EvenWins G (!turn)
          (privateLeafResolvedRight x d z U q (!turn) score) ∧
      EvenWins G (!turn)
          (privateLeafClosedRight G x d z U q (!turn) score) ∧
      ∀ r ∈ U, EvenWins G (!turn)
        (privateLeafActiveRight x d z (U.erase r) (q ++ [r])
          (!turn) score)) := by
  simpa [privateLeafActiveRight, privateLeafResolvedRight,
    privateLeafClosedRight, privateLeafActiveLeft,
    privateLeafResolvedLeft, privateLeafClosedLeft] using
    (privateLeafActiveLeft_bellman G x z d U q turn score hdU)

omit [Fintype V] in
/-- One exact mutual-induction step for the active pair.  The resolved and
CLOSE invariants imply nonmover complementarity, but do not by themselves
give both mover wins.  The remaining selector says: if the common resolved
nonmover loses, some smaller common-OPEN child has nonmover polarity opposite
to the left CLOSE state.  That one child repairs whichever side is not
already repaired by CLOSE. -/
theorem privateLeafActiveInvariant_of_resolved_closed
    (G : SimpleGraph V) (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) (hzU : z ∉ U) (hdU : d ∉ U)
    (hN : PrivateLeafResolvedInvariant G
      (privateLeafResolvedLeft x d z U q (!turn) score)
      (privateLeafResolvedRight x d z U q (!turn) score))
    (hC : PrivateLeafClosedInvariant G
      (privateLeafClosedLeft G x d z U q (!turn) score)
      (privateLeafClosedRight G x d z U q (!turn) score))
    (hrepair :
      ¬NonmoverEvenWins G
          (privateLeafResolvedLeft x d z U q (!turn) score) →
        ∃ r ∈ U,
          NonmoverEvenWins G
              (privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
                (!turn) score) ↔
            ¬NonmoverEvenWins G
              (privateLeafClosedLeft G x d z U q (!turn) score))
    (hchildren : ∀ r ∈ U, PrivateLeafActiveInvariant G
      (privateLeafActiveLeft x d z (U.erase r) (q ++ [r]) (!turn) score)
      (privateLeafActiveRight x d z (U.erase r) (q ++ [r]) (!turn) score)) :
    PrivateLeafActiveInvariant G
      (privateLeafActiveLeft x d z U q turn score)
      (privateLeafActiveRight x d z U q turn score) := by
  let AL := privateLeafActiveLeft x d z U q turn score
  let AR := privateLeafActiveRight x d z U q turn score
  let NL := privateLeafResolvedLeft x d z U q (!turn) score
  let NR := privateLeafResolvedRight x d z U q (!turn) score
  let CL := privateLeafClosedLeft G x d z U q (!turn) score
  let CR := privateLeafClosedRight G x d z U q (!turn) score
  let RL := fun r ↦ privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
    (!turn) score
  let RR := fun r ↦ privateLeafActiveRight x d z (U.erase r) (q ++ [r])
    (!turn) score
  have bL := privateLeafActiveLeft_bellman G x d z U q turn score hzU
  have bR := privateLeafActiveRight_bellman G x d z U q turn score hdU
  have bLM : MoverEvenWins G AL ↔
      NonmoverEvenWins G NL ∨ NonmoverEvenWins G CL ∨
        ∃ r ∈ U, NonmoverEvenWins G (RL r) := by
    simpa [MoverEvenWins, NonmoverEvenWins, AL, NL, CL, RL,
      privateLeafActiveLeft, privateLeafResolvedLeft,
      privateLeafClosedLeft] using bL.1
  have bLN : NonmoverEvenWins G AL ↔
      MoverEvenWins G NL ∧ MoverEvenWins G CL ∧
        ∀ r ∈ U, MoverEvenWins G (RL r) := by
    simpa [MoverEvenWins, NonmoverEvenWins, AL, NL, CL, RL,
      privateLeafActiveLeft, privateLeafResolvedLeft,
      privateLeafClosedLeft] using bL.2
  have bRM : MoverEvenWins G AR ↔
      NonmoverEvenWins G NR ∨ NonmoverEvenWins G CR ∨
        ∃ r ∈ U, NonmoverEvenWins G (RR r) := by
    simpa [MoverEvenWins, NonmoverEvenWins, AR, NR, CR, RR,
      privateLeafActiveRight, privateLeafResolvedRight,
      privateLeafClosedRight] using bR.1
  have bRN : NonmoverEvenWins G AR ↔
      MoverEvenWins G NR ∧ MoverEvenWins G CR ∧
        ∀ r ∈ U, MoverEvenWins G (RR r) := by
    simpa [MoverEvenWins, NonmoverEvenWins, AR, NR, CR, RR,
      privateLeafActiveRight, privateLeafResolvedRight,
      privateLeafClosedRight] using bR.2
  have hN' : PrivateLeafResolvedInvariant G NL NR := by
    simpa [NL, NR] using hN
  have hC' : PrivateLeafClosedInvariant G CL CR := by
    simpa [CL, CR] using hC
  have hrepair' : ¬NonmoverEvenWins G NL →
      ∃ r ∈ U, NonmoverEvenWins G (RL r) ↔
        ¬NonmoverEvenWins G CL := by
    simpa [NL, CL, RL] using hrepair
  have hchild : ∀ r ∈ U, PrivateLeafActiveInvariant G (RL r) (RR r) := by
    intro r hr
    simpa [RL, RR] using hchildren r hr
  have hALM : MoverEvenWins G AL := by
    apply bLM.mpr
    by_cases hNL : NonmoverEvenWins G NL
    · exact Or.inl hNL
    · obtain ⟨r, hr, hpol⟩ := hrepair' hNL
      by_cases hCL : NonmoverEvenWins G CL
      · exact Or.inr (Or.inl hCL)
      · exact Or.inr (Or.inr ⟨r, hr, hpol.mpr hCL⟩)
  have hCNonComp : NonmoverEvenWins G CL ↔
      ¬NonmoverEvenWins G CR := by
    constructor
    · intro hCL hCR
      have hmCL : MoverEvenWins G CL := hC'.1.mpr hCL
      have hmCR : MoverEvenWins G CR := hC'.2.1.mpr hCR
      exact (hC'.2.2.mp hmCL) hmCR
    · intro hnCR
      have hnMCR : ¬MoverEvenWins G CR := by
        intro hmCR
        exact hnCR (hC'.2.1.mp hmCR)
      have hmCL : MoverEvenWins G CL := hC'.2.2.mpr hnMCR
      exact hC'.1.mp hmCL
  have hARM : MoverEvenWins G AR := by
    apply bRM.mpr
    by_cases hNL : NonmoverEvenWins G NL
    · exact Or.inl (hN'.2.2.mp hNL)
    · obtain ⟨r, hr, hpol⟩ := hrepair' hNL
      by_cases hCL : NonmoverEvenWins G CL
      · right
        right
        refine ⟨r, hr, ?_⟩
        by_contra hnRR
        have hRL : NonmoverEvenWins G (RL r) :=
          (hchild r hr).2.2.mpr hnRR
        exact (hpol.mp hRL) hCL
      · right
        left
        by_contra hnCR
        exact hCL (hCNonComp.mpr hnCR)
  have hALN : NonmoverEvenWins G AL ↔ MoverEvenWins G CL := by
    constructor
    · exact fun h ↦ (bLN.mp h).2.1
    · intro hCL
      refine bLN.mpr ⟨hN'.1, hCL, ?_⟩
      intro r hr
      exact (hchild r hr).1
  have hARN : NonmoverEvenWins G AR ↔ MoverEvenWins G CR := by
    constructor
    · exact fun h ↦ (bRN.mp h).2.1
    · intro hCR
      refine bRN.mpr ⟨hN'.2.1, hCR, ?_⟩
      intro r hr
      exact (hchild r hr).2.1
  refine ⟨hALM, hARM, ?_⟩
  constructor
  · intro hAL
    have hCL : MoverEvenWins G CL := hALN.mp hAL
    have hnotCR : ¬MoverEvenWins G CR := hC'.2.2.mp hCL
    exact fun hAR ↦ hnotCR (hARN.mp hAR)
  · intro hnotAR
    have hnotCR : ¬MoverEvenWins G CR := by
      intro hCR
      exact hnotAR (hARN.mpr hCR)
    have hCL : MoverEvenWins G CL := hC'.2.2.mpr hnotCR
    exact hALN.mpr hCL

omit [Fintype V] in
/-- Converse Bellman extraction: assuming the N and C invariants and the
smaller active invariants, any active-pair invariant supplies exactly the
repair selector used above.  Hence the selector is not an artefact of the
proof; it is the precise remaining obligation. -/
theorem privateLeaf_repair_of_activeInvariant
    (G : SimpleGraph V) (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) (hzU : z ∉ U) (hdU : d ∉ U)
    (hN : PrivateLeafResolvedInvariant G
      (privateLeafResolvedLeft x d z U q (!turn) score)
      (privateLeafResolvedRight x d z U q (!turn) score))
    (hC : PrivateLeafClosedInvariant G
      (privateLeafClosedLeft G x d z U q (!turn) score)
      (privateLeafClosedRight G x d z U q (!turn) score))
    (hchildren : ∀ r ∈ U, PrivateLeafActiveInvariant G
      (privateLeafActiveLeft x d z (U.erase r) (q ++ [r]) (!turn) score)
      (privateLeafActiveRight x d z (U.erase r) (q ++ [r]) (!turn) score))
    (hactive : PrivateLeafActiveInvariant G
      (privateLeafActiveLeft x d z U q turn score)
      (privateLeafActiveRight x d z U q turn score))
    (hNL : ¬NonmoverEvenWins G
      (privateLeafResolvedLeft x d z U q (!turn) score)) :
    ∃ r ∈ U,
      NonmoverEvenWins G
          (privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
            (!turn) score) ↔
        ¬NonmoverEvenWins G
          (privateLeafClosedLeft G x d z U q (!turn) score) := by
  let AL := privateLeafActiveLeft x d z U q turn score
  let AR := privateLeafActiveRight x d z U q turn score
  let NL := privateLeafResolvedLeft x d z U q (!turn) score
  let NR := privateLeafResolvedRight x d z U q (!turn) score
  let CL := privateLeafClosedLeft G x d z U q (!turn) score
  let CR := privateLeafClosedRight G x d z U q (!turn) score
  let RL := fun r ↦ privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
    (!turn) score
  let RR := fun r ↦ privateLeafActiveRight x d z (U.erase r) (q ++ [r])
    (!turn) score
  have hN' : PrivateLeafResolvedInvariant G NL NR := by
    simpa [NL, NR] using hN
  have hC' : PrivateLeafClosedInvariant G CL CR := by
    simpa [CL, CR] using hC
  have hchild : ∀ r ∈ U, PrivateLeafActiveInvariant G (RL r) (RR r) := by
    intro r hr
    simpa [RL, RR] using hchildren r hr
  have hNL' : ¬NonmoverEvenWins G NL := by simpa [NL] using hNL
  have hNR' : ¬NonmoverEvenWins G NR := by
    intro hNR
    exact hNL' (hN'.2.2.mpr hNR)
  have hCNonComp : NonmoverEvenWins G CL ↔
      ¬NonmoverEvenWins G CR := by
    constructor
    · intro hCL hCR
      exact (hC'.2.2.mp (hC'.1.mpr hCL)) (hC'.2.1.mpr hCR)
    · intro hnCR
      apply hC'.1.mp
      apply hC'.2.2.mpr
      intro hmCR
      exact hnCR (hC'.2.1.mp hmCR)
  have bLM : MoverEvenWins G AL ↔
      NonmoverEvenWins G NL ∨ NonmoverEvenWins G CL ∨
        ∃ r ∈ U, NonmoverEvenWins G (RL r) := by
    simpa [MoverEvenWins, NonmoverEvenWins, AL, NL, CL, RL,
      privateLeafActiveLeft, privateLeafResolvedLeft,
      privateLeafClosedLeft] using
      (privateLeafActiveLeft_bellman G x d z U q turn score hzU).1
  have bRM : MoverEvenWins G AR ↔
      NonmoverEvenWins G NR ∨ NonmoverEvenWins G CR ∨
        ∃ r ∈ U, NonmoverEvenWins G (RR r) := by
    simpa [MoverEvenWins, NonmoverEvenWins, AR, NR, CR, RR,
      privateLeafActiveRight, privateLeafResolvedRight,
      privateLeafClosedRight] using
      (privateLeafActiveRight_bellman G x d z U q turn score hdU).1
  by_cases hCL : NonmoverEvenWins G CL
  · have hnCR : ¬NonmoverEvenWins G CR := hCNonComp.mp hCL
    rcases bRM.mp hactive.2.1 with hNR | hCR | ⟨r, hr, hRR⟩
    · exact False.elim (hNR' hNR)
    · exact False.elim (hnCR hCR)
    · refine ⟨r, hr, ?_⟩
      constructor
      · intro hRL
        exact False.elim ((hchild r hr).2.2.mp hRL hRR)
      · intro hnCL
        exact False.elim (hnCL hCL)
  · rcases bLM.mp hactive.1 with hN | hC | ⟨r, hr, hRL⟩
    · exact False.elim (hNL' hN)
    · exact False.elim (hCL hC)
    · refine ⟨r, hr, ?_⟩
      exact ⟨fun _ ↦ hCL, fun _ ↦ hRL⟩

omit [Fintype V] in
/-- Exact Bellman boundary: once N, C, and all smaller A invariants are in
place, the current active invariant is equivalent to the single repair
selector. -/
theorem privateLeafActiveInvariant_iff_repair
    (G : SimpleGraph V) (x d z : V) (U : Finset V) (q : List V)
    (turn : Bool) (score : ZMod 2) (hzU : z ∉ U) (hdU : d ∉ U)
    (hN : PrivateLeafResolvedInvariant G
      (privateLeafResolvedLeft x d z U q (!turn) score)
      (privateLeafResolvedRight x d z U q (!turn) score))
    (hC : PrivateLeafClosedInvariant G
      (privateLeafClosedLeft G x d z U q (!turn) score)
      (privateLeafClosedRight G x d z U q (!turn) score))
    (hchildren : ∀ r ∈ U, PrivateLeafActiveInvariant G
      (privateLeafActiveLeft x d z (U.erase r) (q ++ [r]) (!turn) score)
      (privateLeafActiveRight x d z (U.erase r) (q ++ [r]) (!turn) score)) :
    PrivateLeafActiveInvariant G
        (privateLeafActiveLeft x d z U q turn score)
        (privateLeafActiveRight x d z U q turn score) ↔
      (¬NonmoverEvenWins G
          (privateLeafResolvedLeft x d z U q (!turn) score) →
        ∃ r ∈ U,
          NonmoverEvenWins G
              (privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
                (!turn) score) ↔
            ¬NonmoverEvenWins G
              (privateLeafClosedLeft G x d z U q (!turn) score)) := by
  constructor
  · intro hactive hNL
    exact privateLeaf_repair_of_activeInvariant G x d z U q turn score
      hzU hdU hN hC hchildren hactive hNL
  · intro hrepair
    exact privateLeafActiveInvariant_of_resolved_closed G x d z U q
      turn score hzU hdU hN hC hrepair hchildren

/-- The active simultaneous invariant at the canonical empty-common-queue
pair is exactly the private-leaf reply duality needed by the gadget no-go. -/
theorem privateLeafReplyDual_of_activeInvariant
    {G : SimpleGraph V} {x d z : V}
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d)
    (hactive : PrivateLeafActiveInvariant G
      (privateLeafActiveLeft x d z (privateLeafResidual x d z) [] false 0)
      (privateLeafActiveRight x d z (privateLeafResidual x d z) [] false 0)) :
    PrivateLeafReplyDual G x d z := by
  obtain ⟨hleft, hright⟩ := privateLeaf_replies_eq_active hleaf hd
  have hcomp := hactive.2.2
  have hcomp' : EvenWins G true (afterInitialTwoOpens x d) ↔
      ¬EvenWins G true (afterInitialTwoOpens x z) := by
    simpa [NonmoverEvenWins, hleft, hright,
      privateLeafActiveLeft, privateLeafActiveRight] using hcomp
  rw [PrivateLeafReplyDual, oddWins_iff_not_evenWins]
  exact hcomp'

/-! ## The unresolved repair selector -/

/-- The graph-symmetry part of the unresolved transport: equality of the
resolved sheets and cold complementarity of the CLOSE sheets. -/
def PrivateLeafResolvedClosedBridge
    (G : SimpleGraph V) (NL NR CL CR : State V) : Prop :=
  PrivateLeafResolvedInvariant G NL NR ∧
    PrivateLeafClosedInvariant G CL CR

/-- A resolved/CLOSE bridge plus the exact repair selector at every common
carrier suffices to finish private-leaf reply duality.  The selector is
vacuous only when the resolved nonmover already wins; otherwise it must name
one smaller common OPEN whose left nonmover polarity opposes the left CLOSE
state. -/
theorem privateLeafReplyDual_of_resolvedClosedBridge
    (G : SimpleGraph V) (x d z : V)
    (hleaf : IsPrivateLeaf G z x) (hd : IsDummy G d)
    (hbridge : ∀ (U : Finset V) (q : List V) (turn : Bool)
      (score : ZMod 2), z ∉ U → d ∉ U →
      PrivateLeafResolvedClosedBridge G
        (privateLeafResolvedLeft x d z U q (!turn) score)
        (privateLeafResolvedRight x d z U q (!turn) score)
        (privateLeafClosedLeft G x d z U q (!turn) score)
        (privateLeafClosedRight G x d z U q (!turn) score))
    (hrepair : ∀ (U : Finset V) (q : List V) (turn : Bool)
      (score : ZMod 2), z ∉ U → d ∉ U →
      ¬NonmoverEvenWins G
          (privateLeafResolvedLeft x d z U q (!turn) score) →
        ∃ r ∈ U,
          NonmoverEvenWins G
              (privateLeafActiveLeft x d z (U.erase r) (q ++ [r])
                (!turn) score) ↔
            ¬NonmoverEvenWins G
              (privateLeafClosedLeft G x d z U q (!turn) score)) :
    PrivateLeafReplyDual G x d z := by
  have active : ∀ (U : Finset V) (q : List V) (turn : Bool)
      (score : ZMod 2), z ∉ U → d ∉ U →
      PrivateLeafActiveInvariant G
        (privateLeafActiveLeft x d z U q turn score)
        (privateLeafActiveRight x d z U q turn score) := by
    intro U
    induction hcard : U.card using Nat.strong_induction_on generalizing U with
    | h n ih =>
        intro q turn score hzU hdU
        obtain ⟨hN, hC⟩ := hbridge U q turn score hzU hdU
        apply privateLeafActiveInvariant_of_resolved_closed G x d z U q
          turn score hzU hdU hN hC (hrepair U q turn score hzU hdU)
        intro r hr
        have hlt : (U.erase r).card < n := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hr
        apply ih (U.erase r).card hlt (U.erase r) rfl
        · exact Finset.not_mem_subset (Finset.erase_subset r U) hzU
        · exact Finset.not_mem_subset (Finset.erase_subset r U) hdU
  have hzR : z ∉ privateLeafResidual x d z :=
    privateLeafResidual_not_mem_z x d z
  have hdR : d ∉ privateLeafResidual x d z :=
    privateLeafResidual_not_mem_d x d z
  exact privateLeafReplyDual_of_activeInvariant hleaf hd
    (active (privateLeafResidual x d z) [] false 0 hzR hdR)

/-- A private-leaf reply duality makes a complete bad reply fan impossible:
if the dummy reply is poisoned, the private-leaf reply is safe, and vice
versa. -/
theorem privateLeafReplyDual_blocks_secondSeatReplyFan
    {G : SimpleGraph V} {x d z : V}
    (hdual : PrivateLeafReplyDual G x d z)
    (hdummy : OddWins G true (afterInitialTwoOpens x d)) :
    ¬OddWins G true (afterInitialTwoOpens x z) := by
  intro hleaf
  exact (hdual.mpr hleaf).not_oddWins hdummy

/-- Structure-level form of the same obstruction.  A complete selected bad
reply fan at `x` cannot coexist with a dummy/private-leaf dual pair among its
replies. -/
theorem privateLeafReplyDual_no_secondSeatReplyFan
    {G : SimpleGraph V} {x d z : V}
    (hdx : d ≠ x) (hzx : z ≠ x)
    (hdual : PrivateLeafReplyDual G x d z) :
    IsEmpty (SecondSeatReplyFan G x) := by
  refine ⟨fun fan ↦ ?_⟩
  have hdummy : OddWins G true (afterInitialTwoOpens x d) :=
    (fan.child d (by simp [hdx])).toOddWins
  have hleaf : OddWins G true (afterInitialTwoOpens x z) :=
    (fan.child z (by simp [hzx])).toOddWins
  exact (privateLeafReplyDual_blocks_secondSeatReplyFan hdual hdummy) hleaf

/-! ## The smallest exact private-leaf transfer -/

theorem activeNeutralIntervalGraph_privateLeafTwo :
    IsPrivateLeaf activeNeutralIntervalGraph (2 : Fin 3) 0 := by
  intro v
  fin_cases v <;>
    simp [activeNeutralIntervalGraph, SimpleGraph.fromRel_adj]

/-- The tempting within-side N/C complement used in the first attempted
mutual induction is genuinely false, already with no common untouched
vertex.  On the three-label board the resolved right state and the right
CLOSE state are both nonmover-even.  Thus the universal proof must use the
repair selector above rather than an N/C dichotomy on each side. -/
theorem activeNeutral_not_resolvedClosed_right_polarity :
    ¬(NonmoverEvenWins activeNeutralIntervalGraph
          (privateLeafResolvedRight (0 : Fin 3) 1 2 ∅ [] true 0) ↔
       ¬NonmoverEvenWins activeNeutralIntervalGraph
          (privateLeafClosedRight activeNeutralIntervalGraph
            (0 : Fin 3) 1 2 ∅ [] true 0)) := by
  let N := privateLeafResolvedRight (0 : Fin 3) 1 2 ∅ [] true 0
  let C := privateLeafClosedRight activeNeutralIntervalGraph
    (0 : Fin 3) 1 2 ∅ [] true 0
  have hN : NonmoverEvenWins activeNeutralIntervalGraph N := by
    show EvenWins activeNeutralIntervalGraph false N
    apply evenWins_of_untouched_empty false N
    · rfl
    · rfl
  have hflip : flip activeNeutralIntervalGraph ({1} : Finset (Fin 3)) 0 = 0 := by
    rw [flip_singleton_eq_adjacencyBit]
    have hnot : ¬activeNeutralIntervalGraph.Adj 0 1 := by
      exact fun h ↦ activeNeutralIntervalGraph_dummy 0
        ((activeNeutralIntervalGraph.adj_comm 0 1).mp h)
    simp [adjacencyBit, hnot]
  have hCboth : BothEven activeNeutralIntervalGraph C := by
    apply isolated_singletonWall_bothEven_of_score_zero
      (s := C) (d := (1 : Fin 3)) (f := (2 : Fin 3))
      activeNeutralIntervalGraph_dummy
    · simp [C, privateLeafClosedRight]
    · simp [C, privateLeafClosedRight]
    · rfl
    · simp [C, privateLeafClosedRight, hflip]
  have hC : NonmoverEvenWins activeNeutralIntervalGraph C := hCboth.2
  intro hpol
  exact (hpol.mp hN) hC

/-- On the three-label edge-plus-isolate graph, the private-leaf reply
`[0,2]` is even-winning for the physical second seat.  The opponent can only
open the dummy or close `0`; after the latter, Even opens the dummy before
the leaf front can matter. -/
theorem evenWins_activeNeutral_privateLeafReply :
    EvenWins activeNeutralIntervalGraph true
      (afterInitialTwoOpens (0 : Fin 3) 2) := by
  let so : State (Fin 3) := {
    untouched := ∅
    queue := [0, 2, 1]
    ko := false
    toMove := true
    score := 0 }
  have hopen : step activeNeutralIntervalGraph
      (afterInitialTwoOpens (0 : Fin 3) 2) (.open 1) = some so := by
    have hU : (((Finset.univ.erase 0).erase 2).erase 1 :
        Finset (Fin 3)) = ∅ := by decide
    simp [step, afterInitialTwoOpens, so, hU]
  have hasMove : ∃ m t, step activeNeutralIntervalGraph
      (afterInitialTwoOpens (0 : Fin 3) 2) m = some t :=
    ⟨.open 1, so, hopen⟩
  refine EvenWins.answer (afterInitialTwoOpens (0 : Fin 3) 2)
    (by simp [afterInitialTwoOpens]) hasMove ?_
  intro m t hstep
  cases m with
  | «open» v =>
      have hv : v = 1 := by
        simp only [step, afterInitialTwoOpens] at hstep
        split at hstep
        · rename_i hmem
          fin_cases v <;> simp at hmem ⊢
        · contradiction
      subst v
      rw [hopen] at hstep
      have ht : t = so := Option.some.inj hstep.symm
      subst t
      exact evenWins_of_untouched_empty true so (by simp [so]) (by simp [so])
  | close =>
      let sc : State (Fin 3) := {
        untouched := {1}
        queue := [2]
        ko := false
        toMove := true
        score := 0 }
      have hclose : step activeNeutralIntervalGraph
          (afterInitialTwoOpens (0 : Fin 3) 2) .close = some sc := by
        have hU : ((Finset.univ.erase 0).erase 2 : Finset (Fin 3)) =
            {1} := by decide
        have hflip : flip activeNeutralIntervalGraph {1} 0 = 0 := by
          rw [flip_singleton_eq_adjacencyBit]
          have hnot : ¬activeNeutralIntervalGraph.Adj 0 1 := by
            simpa [activeNeutralIntervalGraph.adj_comm] using
              activeNeutralIntervalGraph_dummy 0
          simp [adjacencyBit, hnot]
        simp [step, afterInitialTwoOpens, sc, hU, hflip]
      rw [hclose] at hstep
      have ht : t = sc := Option.some.inj hstep.symm
      subst t
      let sco : State (Fin 3) := {
        untouched := ∅
        queue := [2, 1]
        ko := false
        toMove := false
        score := 0 }
      have hopen' : step activeNeutralIntervalGraph sc (.open 1) =
          some sco := by simp [step, sc, sco]
      refine EvenWins.choose sc rfl (.open 1) sco hopen' ?_
      exact evenWins_of_untouched_empty true sco (by simp [sco])
        (by simp [sco])
  | pass => simp [step, afterInitialTwoOpens] at hstep

/-- The private-leaf exchange is exact on the least nontrivial board.  The
dummy reply is `activeNeutralIntervalState`, already proved odd-winning;
the leaf reply is the preceding even-winning state. -/
theorem activeNeutral_privateLeafReplyDual :
    PrivateLeafReplyDual activeNeutralIntervalGraph (0 : Fin 3) 1 2 := by
  constructor
  · intro heven
    exact False.elim
      (heven.not_oddWins oddWins_activeNeutralInterval)
  · intro hodd
    exact False.elim
      (evenWins_activeNeutral_privateLeafReply.not_oddWins hodd)

/-- Consequently even the smallest private-leaf attachment cannot make both
the isolated-dummy reply and the new real reply odd-winning. -/
theorem activeNeutral_privateLeaf_cannot_poison_both :
    IsDummy activeNeutralIntervalGraph (1 : Fin 3) ∧
      IsPrivateLeaf activeNeutralIntervalGraph (2 : Fin 3) 0 ∧
      ¬(OddWins activeNeutralIntervalGraph true activeNeutralIntervalState ∧
      OddWins activeNeutralIntervalGraph true
        (afterInitialTwoOpens (0 : Fin 3) 2)) := by
  refine ⟨activeNeutralIntervalGraph_dummy,
    activeNeutralIntervalGraph_privateLeafTwo, ?_⟩
  rintro ⟨hdummy, hleaf⟩
  exact (privateLeafReplyDual_blocks_secondSeatReplyFan
    activeNeutral_privateLeafReplyDual hdummy) hleaf

end

end Ogdoad.Fifo
