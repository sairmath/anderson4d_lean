import Anderson4D.PermSum.CollapseAlphabet
import Anderson4D.PermSum.CollapseCoordinates
import Anderson4D.PermSum.CollapseData

/-!
# Tree-facing collapse coordinates

This module connects the pure `(π₁, O, π₂)` collapse coordinates to the
actual leaf alphabets of the restricted and contracted Hepp trees.
-/

namespace Anderson4D

open PlaneTree

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-! ## Named alphabet and word equivalences -/

/-- Rename inside letters as leaves of the actual restricted subtree. -/
def restrictInsideAlphabetEquiv {t : PlaneTree} (r : VPos t) :
    InsideLeaf r ≃ HeppLeaf (subtreeAt t r.1) :=
  (restrictLeafEquiv r).symm

/-- Rename the marker/outside alphabet as leaves of the contracted tree. -/
def contractCollapsedAlphabetEquiv {t : PlaneTree} (r : VPos t) :
    Unit ⊕ OutsideLeaf r ≃ HeppLeaf (contractAt t r.1) :=
  (contractLeafSumEquiv r).symm

/-- Word equivalence used for the Proposition 5.10 call on the subtree. -/
def restrictInsideWordEquiv {t : PlaneTree} (r : VPos t) (n : ℕ) :
    (Fin n → InsideLeaf r) ≃
      (Fin n → HeppLeaf (subtreeAt t r.1)) :=
  wordRenameEquiv (restrictInsideAlphabetEquiv r) n

/-- Word equivalence used for the induction call on the contracted tree. -/
def contractCollapsedWordEquiv {t : PlaneTree} (r : VPos t) (n : ℕ) :
    (Fin n → Unit ⊕ OutsideLeaf r) ≃
      (Fin n → HeppLeaf (contractAt t r.1)) :=
  wordRenameEquiv (contractCollapsedAlphabetEquiv r) n

/-! ## Multiplicity identities -/

/-- Inside coordinate multiplicity transported to the restricted tree. -/
def restrictedCoordinateMultiplicity {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) :
    HeppLeaf (subtreeAt t r.1) → ℕ :=
  renameMultiplicity (restrictInsideAlphabetEquiv r)
    (insideMultiplicity (splitLeafMultiplicity mu r))

/-- The transported inside multiplicity is exactly the restricted tree's
leaf multiplicity. -/
theorem restrictedCoordinateMultiplicity_eq {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) :
    restrictedCoordinateMultiplicity mu r =
      leafMultiplicity (restrictMultiplicities mu r) := by
  funext l
  obtain ⟨lin, rfl⟩ :=
    (restrictInsideAlphabetEquiv r).surjective l
  rw [restrictedCoordinateMultiplicity, renameMultiplicity_apply]
  change
    insideMultiplicity (splitLeafMultiplicity mu r) lin =
      leafMultiplicity (restrictMultiplicities mu r)
        (restrictInsideLeaf r lin)
  rw [restrictMultiplicities_inside]
  rfl

/-- The paper cut count `s`, read from the number `s+1` of inside blocks. -/
def collapseCutCount {A B : Type*} (d : RawCollapseData A B) : ℕ :=
  d.blocks.length - 1

theorem collapseCutCount_add_one {A B : Type*}
    (d : RawCollapseData A B) (hblocks : 2 ≤ d.blocks.length) :
    collapseCutCount d + 1 = d.blocks.length := by
  unfold collapseCutCount
  omega

theorem one_le_collapseCutCount {A B : Type*}
    (d : RawCollapseData A B) (hblocks : 2 ≤ d.blocks.length) :
    1 ≤ collapseCutCount d := by
  unfold collapseCutCount
  omega

/-- Collapsed coordinate multiplicity transported to the contracted tree. -/
def contractedCoordinateMultiplicity {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    HeppLeaf (contractAt t r.1) → ℕ :=
  renameMultiplicity (contractCollapsedAlphabetEquiv r)
    (collapsedMultiplicity (splitLeafMultiplicity mu r) d)

/-- Marker branch of the contracted multiplicity identity. -/
theorem collapsedMultiplicity_marker_eq_contract {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hblocks : 2 ≤ d.blocks.length) :
    collapsedMultiplicity (splitLeafMultiplicity mu r) d (.inl ()) =
      leafMultiplicity
        (contractMultiplicities mu r (collapseCutCount d)
          (one_le_collapseCutCount d hblocks))
        (contractMarkerLeaf r) := by
  rw [contractMultiplicities_marker]
  change d.blocks.length = collapseCutCount d + 1
  exact (collapseCutCount_add_one d hblocks).symm

/-- Outside branch of the contracted multiplicity identity. -/
theorem collapsedMultiplicity_outside_eq_contract {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hblocks : 2 ≤ d.blocks.length) (l : OutsideLeaf r) :
    collapsedMultiplicity (splitLeafMultiplicity mu r) d (.inr l) =
      leafMultiplicity
        (contractMultiplicities mu r (collapseCutCount d)
          (one_le_collapseCutCount d hblocks))
        (contractOutsideLeaf r l) := by
  rw [contractMultiplicities_outside]
  rfl

/-- The transported collapsed multiplicity is exactly the contracted tree's
leaf multiplicity, including the new marker multiplicity `s+1`. -/
theorem contractedCoordinateMultiplicity_eq {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hblocks : 2 ≤ d.blocks.length) :
    contractedCoordinateMultiplicity mu r d =
      leafMultiplicity
        (contractMultiplicities mu r (collapseCutCount d)
          (one_le_collapseCutCount d hblocks)) := by
  funext l
  obtain ⟨x, rfl⟩ :=
    (contractCollapsedAlphabetEquiv r).surjective l
  rw [contractedCoordinateMultiplicity, renameMultiplicity_apply]
  cases x with
  | inl u =>
      cases u
      change
        collapsedMultiplicity (splitLeafMultiplicity mu r) d (.inl ()) =
          leafMultiplicity
            (contractMultiplicities mu r (collapseCutCount d)
              (one_le_collapseCutCount d hblocks))
            ((contractLeafSumEquiv r).symm (.inl ()))
      have hmarker :
          (contractLeafSumEquiv r).symm (.inl ()) =
            contractMarkerLeaf r := by
        apply (contractLeafSumEquiv r).injective
        simp
      rw [hmarker]
      exact collapsedMultiplicity_marker_eq_contract mu r d hblocks
  | inr l =>
      change
        collapsedMultiplicity (splitLeafMultiplicity mu r) d (.inr l) =
          leafMultiplicity
            (contractMultiplicities mu r (collapseCutCount d)
              (one_le_collapseCutCount d hblocks))
            (contractOutsideLeaf r l)
      exact collapsedMultiplicity_outside_eq_contract mu r d hblocks l

/-! ## Coordinate words on the actual tree alphabets -/

/-- The inside coordinate word, renamed as a word of restricted-tree leaves. -/
def restrictedInsideWord {t : PlaneTree} (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    Fin d.insideLength → HeppLeaf (subtreeAt t r.1) :=
  restrictInsideWordEquiv r d.insideLength d.insideWord

/-- The collapsed coordinate word, renamed as a word of contracted-tree
leaves. -/
def contractedCollapsedWord {t : PlaneTree} (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    Fin d.collapsed.length → HeppLeaf (contractAt t r.1) :=
  contractCollapsedWordEquiv r d.collapsed.length d.collapsedWord

@[simp]
theorem restrictedInsideWord_apply {t : PlaneTree} (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (i : Fin d.insideLength) :
    restrictedInsideWord r d i =
      (restrictLeafEquiv r).symm (d.insideWord i) :=
  rfl

@[simp]
theorem contractedCollapsedWord_apply {t : PlaneTree} (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (i : Fin d.collapsed.length) :
    contractedCollapsedWord r d i =
      (contractLeafSumEquiv r).symm (d.collapsedWord i) :=
  rfl

/-- Multiplicity specification on raw coordinates gives a valid word on the
actual restricted-tree leaf alphabet. -/
theorem restrictedInsideWord_mem_validWords {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d) :
    restrictedInsideWord r d ∈
      validWords (leafMultiplicity (restrictMultiplicities mu r)) := by
  have hrenamed :
      restrictedInsideWord r d ∈
        validWords (restrictedCoordinateMultiplicity mu r) := by
    exact
      (wordRename_mem_validWords_iff
        (restrictInsideAlphabetEquiv r)
        (insideMultiplicity (splitLeafMultiplicity mu r))
        d.insideWord).mpr
          (d.insideWord_mem_validWords hSpec)
  rw [restrictedCoordinateMultiplicity_eq] at hrenamed
  exact hrenamed

/-- Multiplicity specification on raw coordinates gives a valid word on the
actual contracted-tree leaf alphabet. -/
theorem contractedCollapsedWord_mem_validWords {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d)
    (hblocks : 2 ≤ d.blocks.length) :
    contractedCollapsedWord r d ∈
      validWords
        (leafMultiplicity
          (contractMultiplicities mu r (collapseCutCount d)
            (one_le_collapseCutCount d hblocks))) := by
  have hrenamed :
      contractedCollapsedWord r d ∈
        validWords (contractedCoordinateMultiplicity mu r d) := by
    exact
      (wordRename_mem_validWords_iff
        (contractCollapsedAlphabetEquiv r)
        (collapsedMultiplicity (splitLeafMultiplicity mu r) d)
        d.collapsedWord).mpr
          (d.collapsedWord_mem_validWords hSpec)
  rw [contractedCoordinateMultiplicity_eq mu r d hblocks] at hrenamed
  exact hrenamed

/-! ## Length and total-multiplicity interfaces -/

/-- A valid word's prescribed multiplicities sum to its word length. -/
theorem sum_multiplicity_eq_wordLength
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {mult : α → ℕ} {w : Fin n → α}
    (hw : w ∈ validWords mult) :
    ∑ a : α, mult a = n := by
  rw [validWords, Finset.mem_filter] at hw
  calc
    ∑ a : α, mult a =
        ∑ a : α,
          (Finset.univ.filter fun i => w i = a).card := by
      exact Finset.sum_congr rfl fun a _ => (hw.2 a).symm
    _ = n := by
      simpa using
        (Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin n))
          (Finset.univ : Finset α) w)

/-- The inside coordinate length is exactly the total multiplicity of the
restricted tree. -/
theorem totalMultiplicity_restrict_eq_insideLength {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d) :
    totalMultiplicity (restrictMultiplicities mu r) = d.insideLength := by
  unfold totalMultiplicity
  exact sum_multiplicity_eq_wordLength
    (restrictedInsideWord_mem_validWords mu r d hSpec)

/-- The collapsed coordinate length is exactly the total multiplicity of the
contracted tree. -/
theorem totalMultiplicity_contract_eq_collapsedLength {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d)
    (hblocks : 2 ≤ d.blocks.length) :
    totalMultiplicity
        (contractMultiplicities mu r (collapseCutCount d)
          (one_le_collapseCutCount d hblocks)) =
      d.collapsed.length := by
  unfold totalMultiplicity
  exact sum_multiplicity_eq_wordLength
    (contractedCollapsedWord_mem_validWords mu r d hSpec hblocks)

/-- Original-length form of the contracted total-multiplicity ledger. -/
theorem totalMultiplicity_contract_eq_lengthLedger {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec : CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d)
    (hblocks : 2 ≤ d.blocks.length) :
    totalMultiplicity
        (contractMultiplicities mu r (collapseCutCount d)
          (one_le_collapseCutCount d hblocks)) =
      d.expandedLength - d.insideLength + d.blocks.length := by
  rw [totalMultiplicity_contract_eq_collapsedLength
    mu r d hSpec hblocks, d.collapsed_length]

end

end Anderson4D
