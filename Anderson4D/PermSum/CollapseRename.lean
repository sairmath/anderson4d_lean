import Anderson4D.PermSum.CollapseAlphabet
import Anderson4D.PermSum.Statements

/-!
# Renaming invariance of the Proposition 5.9 summand

The collapse induction replaces the Hepp-leaf alphabet by the canonical
inside/outside sum alphabet.  This file records that both word restrictions
and the positional chain statistic are invariant under that replacement.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

variable {α β : Type*} {m : ℕ}

/-! ## Word predicates -/

/-- Unequal neighbours are invariant under an alphabet equivalence. -/
theorem noAdjacentEqual_wordRename_iff
    (e : α ≃ β) (w : Fin m → α) :
    NoAdjacentEqual (wordRenameEquiv e m w) ↔ NoAdjacentEqual w := by
  constructor
  · intro h j hj heq
    exact h j hj (congrArg e heq)
  · intro h j hj heq
    exact h j hj (e.injective heq)

/-- A finite set of letters and its image under an equivalence occupy the
same positions in a renamed word. -/
theorem letterPositions_wordRename_map
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (w : Fin m → α) (S : Finset α) :
    letterPositions (wordRenameEquiv e m w) (S.map e.toEmbedding) =
      letterPositions w S := by
  ext i
  simp [letterPositions]

/-- The paper's proper-leaf-block restriction is invariant under renaming
the alphabet. -/
theorem noProperLeafBlock_wordRename
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (w : Fin m → α)
    (hw : NoProperLeafBlock w) :
    NoProperLeafBlock (wordRenameEquiv e m w) := by
  intro T hTnonempty hTproper a b hab hpositions
  let S : Finset α := T.map e.symm.toEmbedding
  have hSnonempty : S.Nonempty := by
    exact Finset.map_nonempty.mpr hTnonempty
  have hSproper : S ⊂ Finset.univ := by
    have h :=
      (Finset.map_ssubset_map (f := e.symm.toEmbedding)).mpr hTproper
    simpa only [Finset.map_univ_equiv] using h
  have hrename :
      letterPositions
          (wordRenameEquiv e.symm m (wordRenameEquiv e m w))
          (T.map e.symm.toEmbedding) =
        letterPositions (wordRenameEquiv e m w) T :=
    letterPositions_wordRename_map e.symm
      (wordRenameEquiv e m w) T
  have hword :
      wordRenameEquiv e.symm m (wordRenameEquiv e m w) = w := by
    exact (wordRenameEquiv e m).symm_apply_apply w
  apply hw S hSnonempty hSproper a b hab
  rw [← hword, hrename]
  exact hpositions

/-- Iff form used to rewrite the indicator in the P-5.9 summand. -/
theorem noProperLeafBlock_wordRename_iff
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (w : Fin m → α) :
    NoProperLeafBlock (wordRenameEquiv e m w) ↔
      NoProperLeafBlock w := by
  constructor
  · intro hw
    have h :=
      noProperLeafBlock_wordRename e.symm
        (wordRenameEquiv e m w) hw
    have hword :
        wordRenameEquiv e.symm m (wordRenameEquiv e m w) = w := by
      funext i
      simp
    rw [hword] at h
    exact h
  · exact noProperLeafBlock_wordRename e w

/-! ## Position-chain statistic -/

/-- The Hepp chain formula on an arbitrary finite alphabet equipped with
lattice positions.  On the actual Hepp-leaf alphabet this is definitionally
`heppChainWeight`. -/
def alphabetChainWeight
    (z : α → Fin 4 → ℤ) (w : Fin m → α) : ℝ :=
  ∏ j : AdjacentIndex m,
    latticeEdgeWeight (z (w j.1)) (z (w (adjacentSucc j)))

@[simp] theorem alphabetChainWeight_heppLeaf
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    alphabetChainWeight z w = heppChainWeight z w :=
  rfl

/-- Pulling positions back by the inverse equivalence makes the chain
product exactly invariant under word renaming. -/
@[simp] theorem alphabetChainWeight_wordRename
    (e : α ≃ β) (z : α → Fin 4 → ℤ) (w : Fin m → α) :
    alphabetChainWeight (fun b => z (e.symm b))
        (wordRenameEquiv e m w) =
      alphabetChainWeight z w := by
  simp [alphabetChainWeight]

/-- Direct Hepp-leaf form when both alphabets happen to be leaf types. -/
@[simp] theorem heppChainWeight_wordRename
    {t u : PlaneTree} (e : HeppLeaf t ≃ HeppLeaf u)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    heppChainWeight (fun l => z (e.symm l))
        (wordRenameEquiv e m w) =
      heppChainWeight z w := by
  exact alphabetChainWeight_wordRename e z w

/-- `heppChainWeight` expressed without loss on an arbitrary renamed
alphabet. -/
theorem heppChainWeight_eq_renamed
    {t : PlaneTree} {γ : Type*}
    (e : HeppLeaf t ≃ γ)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    heppChainWeight z w =
      alphabetChainWeight (fun c => z (e.symm c))
        (wordRenameEquiv e m w) := by
  symm
  simpa only [alphabetChainWeight_heppLeaf] using
    alphabetChainWeight_wordRename e z w

/-- The P-5.9 pointwise statistic on an arbitrary finite alphabet with
lattice positions. -/
def primitiveSeparatedAlphabetChainWeight
    [Fintype α] [DecidableEq α]
    (z : α → Fin 4 → ℤ) (w : Fin m → α) : ℝ :=
  if NoProperLeafBlock w ∧ NoAdjacentEqual w then
    alphabetChainWeight z w
  else
    0

@[simp] theorem primitiveSeparatedAlphabetChainWeight_heppLeaf
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    primitiveSeparatedAlphabetChainWeight z w =
      primitiveSeparatedChainWeight z w :=
  rfl

/-- The complete primitive-and-separated chain statistic is exactly
invariant under alphabet renaming. -/
@[simp] theorem primitiveSeparatedAlphabetChainWeight_wordRename
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (z : α → Fin 4 → ℤ) (w : Fin m → α) :
    primitiveSeparatedAlphabetChainWeight
        (fun b => z (e.symm b)) (wordRenameEquiv e m w) =
      primitiveSeparatedAlphabetChainWeight z w := by
  unfold primitiveSeparatedAlphabetChainWeight
  have hp :=
    noProperLeafBlock_wordRename_iff e w
  have ha :=
    noAdjacentEqual_wordRename_iff e w
  by_cases hw : NoProperLeafBlock w ∧ NoAdjacentEqual w
  · have hrenamed :
        NoProperLeafBlock (wordRenameEquiv e m w) ∧
          NoAdjacentEqual (wordRenameEquiv e m w) :=
      ⟨hp.mpr hw.1, ha.mpr hw.2⟩
    rw [if_pos hrenamed, if_pos hw,
      alphabetChainWeight_wordRename]
  · have hrenamed :
        ¬(NoProperLeafBlock (wordRenameEquiv e m w) ∧
          NoAdjacentEqual (wordRenameEquiv e m w)) := by
      intro h
      exact hw ⟨hp.mp h.1, ha.mp h.2⟩
    rw [if_neg hrenamed, if_neg hw]

/-- Direct Hepp-leaf form of invariance for the complete P-5.9 summand. -/
@[simp] theorem primitiveSeparatedChainWeight_wordRename
    {t u : PlaneTree} (e : HeppLeaf t ≃ HeppLeaf u)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    primitiveSeparatedChainWeight (fun l => z (e.symm l))
        (wordRenameEquiv e m w) =
      primitiveSeparatedChainWeight z w := by
  exact primitiveSeparatedAlphabetChainWeight_wordRename e z w

/-- `primitiveSeparatedChainWeight` expressed without loss on any renamed
finite alphabet. -/
theorem primitiveSeparatedChainWeight_eq_renamed
    {t : PlaneTree} {γ : Type*}
    [Fintype γ] [DecidableEq γ]
    (e : HeppLeaf t ≃ γ)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    primitiveSeparatedChainWeight z w =
      primitiveSeparatedAlphabetChainWeight
        (fun c => z (e.symm c)) (wordRenameEquiv e m w) := by
  symm
  simpa only [primitiveSeparatedAlphabetChainWeight_heppLeaf] using
    primitiveSeparatedAlphabetChainWeight_wordRename e z w

/-! ## The canonical inside/outside leaf split -/

open PlaneTree

/-- The original Hepp embedding pulled back to the inside/outside alphabet. -/
def splitLeafPosition {t : PlaneTree} (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ) :
    InsideLeaf r ⊕ OutsideLeaf r → Fin 4 → ℤ :=
  fun l => z ((leafInsideOutsideEquiv r).symm l)

/-- Forward tree-facing form: renaming a Hepp-leaf word to the split alphabet
does not alter its P-5.9 summand. -/
theorem primitiveSeparatedChainWeight_eq_splitLeafWord
    {t : PlaneTree} (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → HeppLeaf t) :
    primitiveSeparatedChainWeight z w =
      primitiveSeparatedAlphabetChainWeight
        (splitLeafPosition r z) (splitLeafWordEquiv r m w) := by
  exact primitiveSeparatedChainWeight_eq_renamed
    (leafInsideOutsideEquiv r) z w

/-- Inverse orientation used after `paperSum_eq_splitLeafAlphabet`: the
pulled-back original summand is directly the same statistic on a split word. -/
@[simp] theorem primitiveSeparatedChainWeight_splitLeafWord_symm
    {t : PlaneTree} (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin m → InsideLeaf r ⊕ OutsideLeaf r) :
    primitiveSeparatedChainWeight z
        ((splitLeafWordEquiv r m).symm w) =
      primitiveSeparatedAlphabetChainWeight
        (splitLeafPosition r z) w := by
  have h :=
    primitiveSeparatedChainWeight_eq_splitLeafWord r z
      ((splitLeafWordEquiv r m).symm w)
  have hword :
      splitLeafWordEquiv r m ((splitLeafWordEquiv r m).symm w) = w :=
    (splitLeafWordEquiv r m).apply_symm_apply w
  rw [hword] at h
  exact h

/-- Sum-level tree-facing corollary: after splitting the leaf alphabet, the
P-5.9 summand is literally the same primitive-and-separated chain statistic
with the pulled-back positions. -/
theorem paperSum_primitiveSeparated_eq_splitLeafAlphabet
    {t : PlaneTree} {n : ℕ}
    (mu : Multiplicities t) (r : VPos t)
    (z : HeppLeaf t → Fin 4 → ℤ) :
    paperSum (M := n) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) =
      paperSum (M := n) (splitLeafMultiplicity mu r)
        (primitiveSeparatedAlphabetChainWeight
          (splitLeafPosition r z)) := by
  simpa only [primitiveSeparatedChainWeight_splitLeafWord_symm] using
    paperSum_eq_splitLeafAlphabet
      (n := n) mu r (primitiveSeparatedChainWeight z)

end

end Anderson4D
