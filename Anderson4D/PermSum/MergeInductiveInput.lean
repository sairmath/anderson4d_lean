import Anderson4D.PermSum.AdmissibleDiameter
import Anderson4D.PermSum.MergeExpansionCount

/-!
# Run-compressed inputs for Proposition 5.9

This module turns a primitive valid word before run compression into the
tree, multiplicity, word, and embedding data expected by the inductive
estimate of Proposition 5.9.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-! ## Every compressed leaf multiplicity is at least two -/

/-- A primitive valid Hepp-leaf word cannot contain only one maximal run of
any leaf.  The branching-root hypothesis supplies a second leaf, and the
original multiplicities ensure that this second leaf occurs. -/
theorem two_le_mergedMultiplicity_of_valid_of_noProperLeafBlock
    {t : PlaneTree} {M : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w)
    (l : HeppLeaf t) :
    2 ≤ mergedMultiplicity w l := by
  have hleafCard :
      1 < Fintype.card (HeppLeaf t) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    exact two_le_leafCount_of_root_mem_BranchNodes t hroot
  obtain ⟨l', hl'⟩ :=
    Fintype.exists_ne_of_one_lt_card hleafCard l
  have hlPositive :
      0 < leafMultiplicity mu l := by
    exact lt_of_lt_of_le (by omega)
      (mu.two_le l.1 l.2)
  obtain ⟨i, hi⟩ :=
    exists_eq_of_mem_validWords_of_pos
      (leafMultiplicity mu) w hvalid l hlPositive
  have hmergedPositive :
      0 < mergedMultiplicity w l :=
    (mergedMultiplicity_pos_iff w l).mpr ⟨i, hi⟩
  by_contra hnotTwo
  have hmergedOne :
      mergedMultiplicity w l = 1 := by
    omega
  have hmergedValid :
      mergedWord w ∈ validWords (mergedMultiplicity w) :=
    mergedWord_mem_validWords w
  have hmergedPrimitive :
      NoProperLeafBlock (mergedWord w) :=
    mergedWord_noProperLeafBlock w hprimitive
  have hpositionCard :
      (letterPositions (mergedWord w) {l}).card = 1 := by
    have hcount :=
      (Finset.mem_filter.mp hmergedValid).2 l
    rw [letterPositions]
    simpa [hmergedOne] using hcount
  obtain ⟨j, hpositionsSingleton⟩ :=
    Finset.card_eq_one.mp hpositionCard
  have hsingletonProper :
      ({l} : Finset (HeppLeaf t)) ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hl'mem :
        l' ∈ ({l} : Finset (HeppLeaf t)) := by
      rw [heq]
      exact Finset.mem_univ l'
    exact hl' (by simpa using hl'mem)
  have hpositionsInterval :
      letterPositions (mergedWord w) {l} =
        Finset.Icc j j :=
    hpositionsSingleton.trans (Finset.Icc_self j).symm
  have hintervalFull :
      Finset.Icc j j =
        (Finset.univ :
          Finset (Fin (mergedWordList w).length)) :=
    hmergedPrimitive {l} (by simp) hsingletonProper
      j j le_rfl hpositionsInterval
  have hl'Positive :
      0 < leafMultiplicity mu l' := by
    exact lt_of_lt_of_le (by omega)
      (mu.two_le l'.1 l'.2)
  obtain ⟨i', hi'⟩ :=
    exists_eq_of_mem_validWords_of_pos
      (leafMultiplicity mu) w hvalid l' hl'Positive
  have hmergedPositive' :
      0 < mergedMultiplicity w l' :=
    (mergedMultiplicity_pos_iff w l').mpr ⟨i', hi'⟩
  obtain ⟨j', hj'⟩ :=
    exists_eq_of_mem_validWords_of_pos
      (mergedMultiplicity w) (mergedWord w)
      hmergedValid l' hmergedPositive'
  have hj'mem :
      j' ∈ letterPositions (mergedWord w) {l} := by
    rw [hpositionsInterval, hintervalFull]
    exact Finset.mem_univ j'
  have hj'eq :
      mergedWord w j' = l := by
    simpa using (mem_letterPositions.mp hj'mem)
  exact hl' (hj'.symm.trans hj'eq)

/-! ## The compressed multiplicity structure -/

/-- Extend the compressed leaf multiplicity by junk zero values away from
the leaf carrier. -/
def mergedMultiplicities
    {t : PlaneTree} {M : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w) :
    Multiplicities t where
  m v :=
    if hv : v ∈ Leaves t then
      mergedMultiplicity w ⟨v, hv⟩
    else
      0
  two_le v hv := by
    simp only [dif_pos hv]
    exact
      two_le_mergedMultiplicity_of_valid_of_noProperLeafBlock
        hroot mu w hvalid hprimitive ⟨v, hv⟩

@[simp]
theorem leafMultiplicity_mergedMultiplicities
    {t : PlaneTree} {M : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w)
    (l : HeppLeaf t) :
    leafMultiplicity
        (mergedMultiplicities
          hroot mu w hvalid hprimitive) l =
      mergedMultiplicity w l := by
  change
    (if hv : l.1 ∈ Leaves t then
      mergedMultiplicity w ⟨l.1, hv⟩
    else
      0) =
    mergedMultiplicity w l
  rw [dif_pos l.2]

/-- The total multiplicity of the compressed structure is exactly the
compressed word length. -/
theorem totalMultiplicity_mergedMultiplicities
    {t : PlaneTree} {M : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w) :
    totalMultiplicity
        (mergedMultiplicities
          hroot mu w hvalid hprimitive) =
      (mergedWordList w).length := by
  unfold totalMultiplicity
  simp_rw [leafMultiplicity_mergedMultiplicities]
  exact sum_mergedMultiplicity w

/-- The compressed word is valid for the constructed Hepp multiplicities. -/
theorem mergedWord_mem_validWords_mergedMultiplicities
    {t : PlaneTree} {M : ℕ}
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w) :
    mergedWord w ∈
      validWords
        (leafMultiplicity
          (mergedMultiplicities
            hroot mu w hvalid hprimitive)) := by
  have hmult :
      leafMultiplicity
          (mergedMultiplicities
            hroot mu w hvalid hprimitive) =
        mergedMultiplicity w := by
    funext l
    exact leafMultiplicity_mergedMultiplicities
      hroot mu w hvalid hprimitive l
  rw [hmult]
  exact mergedWord_mem_validWords w

/-! ## Geometric inputs -/

/-- Admissibility contains the separated-embedding hypothesis of
Proposition 5.9 literally. -/
theorem IsAdmissible.isSeparatedEmbedding
    {t : PlaneTree} {Nm : HeppMarking t} {R : ℕ}
    {z : HeppLeaf t → Fin 4 → ℤ}
    (hadmissible : IsAdmissible Nm R z) :
    IsSeparatedEmbedding Nm z :=
  ⟨hadmissible.inj, hadmissible.sep⟩

/-! ## Packaged induction input -/

/-- All data needed to invoke Proposition 5.9 on the run-compressed word. -/
structure MergeInductiveInput
    {t : PlaneTree} {M : ℕ}
    (Nm : HeppMarking t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (w : Fin M → HeppLeaf t) : Type where
  multiplicities : Multiplicities t
  treeValid : t.isValid = true
  rootBranch : rootV t ∈ BranchNodes t
  leafMultiplicity_eq :
    leafMultiplicity multiplicities =
      mergedMultiplicity w
  total_eq :
    totalMultiplicity multiplicities =
      (mergedWordList w).length
  wordValid :
    mergedWord w ∈ validWords
      (leafMultiplicity multiplicities)
  wordNoAdjacent :
    NoAdjacentEqual (mergedWord w)
  wordPrimitive :
    NoProperLeafBlock (mergedWord w)
  separated :
    IsSeparatedEmbedding Nm z
  subtreeDiameter :
    SatisfiesSubtreeDiameter Nm multiplicities z

/-- Construct the complete Proposition 5.9 input from an admissible
embedding and a primitive valid original word. -/
def mergeInductiveInput
    {t : PlaneTree} {M R : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hadmissible : IsAdmissible Nm R z)
    (w : Fin M → HeppLeaf t)
    (hvalid : w ∈ validWords (leafMultiplicity mu))
    (hprimitive : NoProperLeafBlock w) :
    MergeInductiveInput Nm z w where
  multiplicities :=
    mergedMultiplicities hroot mu w hvalid hprimitive
  treeValid := ht
  rootBranch := hroot
  leafMultiplicity_eq := by
    funext l
    exact leafMultiplicity_mergedMultiplicities
      hroot mu w hvalid hprimitive l
  total_eq :=
    totalMultiplicity_mergedMultiplicities
      hroot mu w hvalid hprimitive
  wordValid :=
    mergedWord_mem_validWords_mergedMultiplicities
      hroot mu w hvalid hprimitive
  wordNoAdjacent := mergedWord_noAdjacentEqual w
  wordPrimitive := mergedWord_noProperLeafBlock w hprimitive
  separated := hadmissible.isSeparatedEmbedding
  subtreeDiameter :=
    hadmissible.satisfiesSubtreeDiameter
      (mergedMultiplicities hroot mu w hvalid hprimitive)

end

end Anderson4D
