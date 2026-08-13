import Ogdoad.FifoPublicPolicyAffine

/-!
# The topology of an attacker-pruned public policy tree

A fixed deterministic public policy is a tree of *history occurrences*:
reconvergent public states remain distinct vertices because the policy may
select different continuations after their different histories.  This file
formalizes the resulting elementary but decisive chain-level boundary.

Over `F₂`, a terminal chain determines exactly one edge flow whose boundary
is its terminal support together with its augmentation at the root.  The
coefficient of a stem edge is forced to be the augmentation of the terminal
chain below that stem.  In particular the degree-one boundary map is
injective, so the pruned history tree has no nonzero one-cycles on which a
boundary-of-boundary argument could operate.

Edge labels may take values in any `F₂`-module.  The label pairing of the
unique edge flow is exactly the coefficient-weighted sum of root-to-terminal
path labels.  For a FIFO policy these labels are the universal live-star move
vectors, and the path labels are its terminal affine moments.  Thus the
universal public-policy target remains a labelled cokernel condition; it does
not follow from the unlabelled topology of the pruned tree.
-/

namespace Ogdoad.Fifo

noncomputable section

universe u

/-- A finite rooted tree, retaining history occurrences rather than
identifying reconvergent public states. -/
inductive FiniteHistoryTree where
  | leaf : FiniteHistoryTree
  | branch (n : Nat) (child : Fin n → FiniteHistoryTree) : FiniteHistoryTree

namespace FiniteHistoryTree

/-- A zero-chain, represented recursively by the root coefficient and the
zero-chains in the child subtrees. -/
def VertexChain : FiniteHistoryTree → Type
  | .leaf => ZMod 2
  | .branch n child => ZMod 2 × ((i : Fin n) → VertexChain (child i))

/-- A one-chain, represented by the stem coefficients and the one-chains in
the child subtrees.  A leaf has no edges. -/
def EdgeChain : FiniteHistoryTree → Type
  | .leaf => PUnit
  | .branch n child =>
      ((i : Fin n) → ZMod 2) × ((i : Fin n) → EdgeChain (child i))

/-- A chain supported on terminal vertices. -/
def TerminalChain : FiniteHistoryTree → Type
  | .leaf => ZMod 2
  | .branch n child => (i : Fin n) → TerminalChain (child i)

/-- The zero zero-chain. -/
def zeroVertexChain : (tree : FiniteHistoryTree) → VertexChain tree
  | .leaf => (0 : ZMod 2)
  | .branch _ child => (0, fun i ↦ zeroVertexChain (child i))

/-- The zero one-chain. -/
def zeroEdgeChain : (tree : FiniteHistoryTree) → EdgeChain tree
  | .leaf => PUnit.unit
  | .branch _ child =>
      (fun _ ↦ 0, fun i ↦ zeroEdgeChain (child i))

/-- Add a coefficient at the root vertex. -/
def addRoot : (tree : FiniteHistoryTree) →
    ZMod 2 → VertexChain tree → VertexChain tree
  | .leaf, c, x => c + (show ZMod 2 from x)
  | .branch _ _, c, x => (c + x.1, x.2)

/-- Sum all coefficients of a zero-chain. -/
def vertexAugmentation : (tree : FiniteHistoryTree) →
    VertexChain tree → ZMod 2
  | .leaf, x => x
  | .branch n child, x =>
      x.1 + ∑ i : Fin n, vertexAugmentation (child i) (x.2 i)

/-- Sum all terminal coefficients. -/
def terminalAugmentation : (tree : FiniteHistoryTree) →
    TerminalChain tree → ZMod 2
  | .leaf, c => c
  | .branch n child, c =>
      ∑ i : Fin n, terminalAugmentation (child i) (c i)

/-- Include a terminal chain into the zero-chains. -/
def terminalVertexChain : (tree : FiniteHistoryTree) →
    TerminalChain tree → VertexChain tree
  | .leaf, c => c
  | .branch _ child, c =>
      (0, fun i ↦ terminalVertexChain (child i) (c i))

/-- The boundary target consisting of the terminal chain plus its
augmentation at the root. -/
def rootPlusTerminal (tree : FiniteHistoryTree) (c : TerminalChain tree) :
    VertexChain tree :=
  addRoot tree (terminalAugmentation tree c) (terminalVertexChain tree c)

/-- The degree-one boundary map over `F₂`.  Every stem contributes at the
parent root and at the child root. -/
def boundary : (tree : FiniteHistoryTree) → EdgeChain tree → VertexChain tree
  | .leaf, _ => (0 : ZMod 2)
  | .branch n child, x =>
      let rootCoefficient : ZMod 2 :=
        Finset.univ.sum fun i : Fin n ↦ x.1 i
      (rootCoefficient,
        fun i ↦ addRoot (child i) (x.1 i) (boundary (child i) (x.2 i)))

/-- The canonical edge flow below a terminal chain.  Each stem coefficient
is the augmentation of the selected terminals below it. -/
def terminalFlow : (tree : FiniteHistoryTree) →
    TerminalChain tree → EdgeChain tree
  | .leaf, _ => PUnit.unit
  | .branch _ child, c =>
      (fun i ↦ terminalAugmentation (child i) (c i),
        fun i ↦ terminalFlow (child i) (c i))

theorem vertexAugmentation_addRoot (tree : FiniteHistoryTree)
    (c : ZMod 2) (x : VertexChain tree) :
    vertexAugmentation tree (addRoot tree c x) =
      c + vertexAugmentation tree x := by
  cases tree <;> simp [addRoot, vertexAugmentation, add_assoc]

theorem addRoot_addRoot (tree : FiniteHistoryTree)
    (a b : ZMod 2) (x : VertexChain tree) :
    addRoot tree a (addRoot tree b x) = addRoot tree (a + b) x := by
  cases tree <;> simp [addRoot, add_assoc]

theorem addRoot_self (tree : FiniteHistoryTree)
    (c : ZMod 2) (x : VertexChain tree) :
    addRoot tree c (addRoot tree c x) = x := by
  rw [addRoot_addRoot, CharTwo.add_self_eq_zero]
  cases tree <;> simp [addRoot]

theorem addRoot_injective (tree : FiniteHistoryTree) (c : ZMod 2) :
    Function.Injective (addRoot tree c) := by
  intro x y h
  have h' := congrArg (addRoot tree c) h
  simpa [addRoot_self] using h'

/-- Every edge boundary has even total augmentation. -/
theorem vertexAugmentation_boundary (tree : FiniteHistoryTree)
    (x : EdgeChain tree) :
    vertexAugmentation tree (boundary tree x) = 0 := by
  induction tree with
  | leaf => cases x; rfl
  | branch n child ih =>
      rcases x with ⟨stem, tail⟩
      simp only [boundary, vertexAugmentation]
      simp_rw [vertexAugmentation_addRoot, ih]
      simp only [add_zero]
      exact CharTwo.add_self_eq_zero _

/-- The tree boundary map is injective.  This is the exact `H₁ = 0`
statement for history occurrences in the representation used here. -/
theorem boundary_injective (tree : FiniteHistoryTree) :
    Function.Injective (boundary tree) := by
  induction tree with
  | leaf =>
      intro x y _
      cases x
      cases y
      rfl
  | branch n child ih =>
      intro x y hxy
      rcases x with ⟨stemX, tailX⟩
      rcases y with ⟨stemY, tailY⟩
      have hsub : ∀ i : Fin n,
          addRoot (child i) (stemX i) (boundary (child i) (tailX i)) =
            addRoot (child i) (stemY i)
              (boundary (child i) (tailY i)) := by
        intro i
        exact congrFun (congrArg Prod.snd hxy) i
      have hstem : stemX = stemY := by
        funext i
        have htotal := congrArg (vertexAugmentation (child i)) (hsub i)
        simp only [vertexAugmentation_addRoot,
          vertexAugmentation_boundary, add_zero] at htotal
        exact htotal
      subst stemY
      have htail : tailX = tailY := by
        funext i
        apply ih i
        apply addRoot_injective (child i) (stemX i)
        exact hsub i
      subst tailY
      rfl

theorem boundary_zeroEdgeChain (tree : FiniteHistoryTree) :
    boundary tree (zeroEdgeChain tree) = zeroVertexChain tree := by
  induction tree with
  | leaf => rfl
  | branch n child ih =>
      change
        ((∑ _ : Fin n, (0 : ZMod 2)),
          fun i ↦ addRoot (child i) 0
            (boundary (child i) (zeroEdgeChain (child i)))) =
        ((0 : ZMod 2), fun i ↦ zeroVertexChain (child i))
      apply Prod.ext
      · simp
      · funext i
        change addRoot (child i) 0
            (boundary (child i) (zeroEdgeChain (child i))) =
          zeroVertexChain (child i)
        rw [ih i]
        cases child i <;> simp [addRoot, zeroVertexChain]

/-- There are no nonzero one-cycles in a pruned history tree. -/
theorem eq_zeroEdgeChain_of_boundary_eq_zero (tree : FiniteHistoryTree)
    (x : EdgeChain tree)
    (hx : boundary tree x = zeroVertexChain tree) :
    x = zeroEdgeChain tree := by
  apply boundary_injective tree
  rw [hx, boundary_zeroEdgeChain]

/-- The canonical terminal flow has exactly the terminal chain plus its
augmentation at the root as boundary. -/
theorem boundary_terminalFlow (tree : FiniteHistoryTree)
    (c : TerminalChain tree) :
    boundary tree (terminalFlow tree c) = rootPlusTerminal tree c := by
  induction tree with
  | leaf =>
      change (0 : ZMod 2) =
        (show ZMod 2 from c) + (show ZMod 2 from c)
      exact (CharTwo.add_self_eq_zero (show ZMod 2 from c)).symm
  | branch n child ih =>
      change
        ((∑ i : Fin n, terminalAugmentation (child i) (c i)),
          fun i ↦ addRoot (child i)
            (terminalAugmentation (child i) (c i))
            (boundary (child i) (terminalFlow (child i) (c i)))) =
        ((∑ i : Fin n, terminalAugmentation (child i) (c i)) + 0,
          fun i ↦ terminalVertexChain (child i) (c i))
      apply Prod.ext
      · simp
      · funext i
        change addRoot (child i)
            (terminalAugmentation (child i) (c i))
            (boundary (child i) (terminalFlow (child i) (c i))) =
          terminalVertexChain (child i) (c i)
        rw [ih i]
        simpa only [rootPlusTerminal] using
          addRoot_self (child i) (terminalAugmentation (child i) (c i))
            (terminalVertexChain (child i) (c i))

/-- A terminal chain determines the unique one-chain with the prescribed
root-plus-terminal boundary. -/
theorem terminalFlow_unique (tree : FiniteHistoryTree)
    (c : TerminalChain tree) (x : EdgeChain tree)
    (hx : boundary tree x = rootPlusTerminal tree c) :
    x = terminalFlow tree c := by
  apply boundary_injective tree
  rw [hx, boundary_terminalFlow]

/-! ## Label pairing -/

/-- One module-valued label for every oriented tree edge. -/
def EdgeLabelling (W : Type u) : (tree : FiniteHistoryTree) → Type u
  | .leaf => PUnit
  | .branch n child =>
      ((i : Fin n) → W) × ((i : Fin n) → EdgeLabelling W (child i))

/-- Pair an edge chain with an edge labelling. -/
def edgeLabelSum {W : Type u} [AddCommMonoid W] [Module (ZMod 2) W] :
    (tree : FiniteHistoryTree) → EdgeLabelling W tree → EdgeChain tree → W
  | .leaf, _, _ => 0
  | .branch n child, labels, x =>
      ∑ i : Fin n, (x.1 i • labels.1 i +
        edgeLabelSum (child i) (labels.2 i) (x.2 i))

/-- The coefficient-weighted sum of the root-to-terminal path labels. -/
def terminalPathLabelSum {W : Type u} [AddCommMonoid W] [Module (ZMod 2) W] :
    (tree : FiniteHistoryTree) →
      EdgeLabelling W tree → TerminalChain tree → W
  | .leaf, _, _ => 0
  | .branch n child, labels, c =>
      ∑ i : Fin n, (terminalAugmentation (child i) (c i) • labels.1 i +
        terminalPathLabelSum (child i) (labels.2 i) (c i))

/-- Interchanging the terminal-path sum and the edge sum gives the same
labelled moment. -/
theorem edgeLabelSum_terminalFlow {W : Type u}
    [AddCommMonoid W] [Module (ZMod 2) W]
    (tree : FiniteHistoryTree) (labels : EdgeLabelling W tree)
    (c : TerminalChain tree) :
    edgeLabelSum tree labels (terminalFlow tree c) =
      terminalPathLabelSum tree labels c := by
  induction tree with
  | leaf => rfl
  | branch n child ih =>
      simp only [edgeLabelSum, terminalFlow, terminalPathLabelSum]
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i]

/-- Complete chain-level form of the history-tree obstruction.  The unique
filling edge chain carries exactly its terminal path moment.  When the tree
is nontrivial and the terminal chain is odd, the root coefficient in
`rootPlusTerminal` is one. -/
theorem terminalChain_unique_filling {W : Type u}
    [AddCommMonoid W] [Module (ZMod 2) W]
    (tree : FiniteHistoryTree) (labels : EdgeLabelling W tree)
    (c : TerminalChain tree) :
    ∃! x : EdgeChain tree,
      boundary tree x = rootPlusTerminal tree c ∧
        edgeLabelSum tree labels x = terminalPathLabelSum tree labels c := by
  refine ⟨terminalFlow tree c, ⟨boundary_terminalFlow tree c,
    edgeLabelSum_terminalFlow tree labels c⟩, ?_⟩
  intro x hx
  exact terminalFlow_unique tree c x hx.1

/-! ## Minimal label obstruction -/

/-- The smallest nontrivial history-occurrence tree. -/
def unaryHistoryTree : FiniteHistoryTree :=
  .branch 1 (fun _ ↦ .leaf)

/-- Select its unique terminal with odd coefficient. -/
def unaryOddTerminalChain : TerminalChain unaryHistoryTree :=
  show (Fin 1 → ZMod 2) from fun _ ↦ 1

/-- Put one scalar label on the unique tree edge. -/
def unaryEdgeLabelling (a : ZMod 2) :
    EdgeLabelling (ZMod 2) unaryHistoryTree :=
  show (Fin 1 → ZMod 2) × (Fin 1 → PUnit) from
    (fun _ ↦ a, fun _ ↦ PUnit.unit)

theorem unaryOddTerminalChain_augmentation :
    terminalAugmentation unaryHistoryTree unaryOddTerminalChain = 1 := by
  simp [unaryHistoryTree, unaryOddTerminalChain, terminalAugmentation]

/-- The same unlabelled tree and the same odd terminal chain have zero or
unit path moment according only to the edge labelling.  Therefore no
invariant of the pruned tree topology alone can decide the affine target;
the FIFO live-star labels and their continuation cosets must be used. -/
theorem unary_zero_and_unit_labels_separate :
    terminalPathLabelSum unaryHistoryTree (unaryEdgeLabelling 0)
        unaryOddTerminalChain = 0 ∧
      terminalPathLabelSum unaryHistoryTree (unaryEdgeLabelling 1)
        unaryOddTerminalChain = 1 := by
  simp [unaryHistoryTree, unaryEdgeLabelling, unaryOddTerminalChain,
    terminalPathLabelSum, terminalAugmentation]

end FiniteHistoryTree

end

end Ogdoad.Fifo
