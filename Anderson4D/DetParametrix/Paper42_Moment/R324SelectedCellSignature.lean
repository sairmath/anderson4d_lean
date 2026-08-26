import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedBlockOccupiedLabels

/-!
# Exact signature fibres of the selected R-324 cells

The finite physical cell index is regrouped by the data that remain
constant when the marked primitive word is sent to Proposition 5.7:

* its finite occupied support;
* its literal multiset of labels (equivalently, every raw count); and
* the two selected endpoint labels.

The decomposition in this file is an exact equality.  The overlapping
Hepp-tree cover is applied separately as the first nonnegative enlargement.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## A decidable raw word signature -/

/-- The multiset of values of a finite word. -/
def rawWordBag {q : ℕ} (w : Fin q → Z4) : Multiset Z4 :=
  (Finset.univ : Finset (Fin q)).1.map w

/-- Support, raw occurrence profile, and the two open-edge endpoint
labels.  The support is retained explicitly because it indexes the
occupied-label realization. -/
structure OpenEdgeCellWordSignature (q : ℕ) where
  support : Finset Z4
  rawBag : Multiset Z4
  leftLabel : Z4
  rightLabel : Z4
deriving DecidableEq

/-- Signature carried by one open-edge lattice word. -/
def openEdgeCellWordSignature
    {q : ℕ} (a b : Fin q) (w : Fin q → Z4) :
    OpenEdgeCellWordSignature q where
  support := tupleSupport w
  rawBag := rawWordBag w
  leftLabel := w a
  rightLabel := w b

/-- Raw occurrence count is the multiplicity in `rawWordBag`. -/
theorem rawWordBag_count
    {q : ℕ} (w : Fin q → Z4) (x : Z4) :
    (rawWordBag w).count x = wordFiberCount w x := by
  unfold rawWordBag wordFiberCount
  rw [Multiset.count_map]
  apply congrArg Multiset.card
  ext i
  simp [eq_comm]

/-- Equality of signatures gives equality of occupied supports. -/
theorem tupleSupport_eq_of_openEdgeCellWordSignature_eq
    {q : ℕ} (a b : Fin q)
    {reference w : Fin q → Z4}
    (h :
      openEdgeCellWordSignature a b w =
        openEdgeCellWordSignature a b reference) :
    tupleSupport w = tupleSupport reference := by
  exact congrArg OpenEdgeCellWordSignature.support h

/-- Equality of signatures gives equality of every literal raw count. -/
theorem wordFiberCount_eq_of_openEdgeCellWordSignature_eq
    {q : ℕ} (a b : Fin q)
    {reference w : Fin q → Z4}
    (h :
      openEdgeCellWordSignature a b w =
        openEdgeCellWordSignature a b reference) :
    ∀ x : Z4,
      wordFiberCount w x =
        wordFiberCount reference x := by
  intro x
  have hbag :
      rawWordBag w = rawWordBag reference :=
    congrArg OpenEdgeCellWordSignature.rawBag h
  rw [← rawWordBag_count, ← rawWordBag_count, hbag]

/-- Equality of signatures fixes the selected lower endpoint label. -/
theorem leftLabel_eq_of_openEdgeCellWordSignature_eq
    {q : ℕ} (a b : Fin q)
    {reference w : Fin q → Z4}
    (h :
      openEdgeCellWordSignature a b w =
        openEdgeCellWordSignature a b reference) :
    w a = reference a :=
  congrArg OpenEdgeCellWordSignature.leftLabel h

/-- Equality of signatures fixes the selected upper endpoint label. -/
theorem rightLabel_eq_of_openEdgeCellWordSignature_eq
    {q : ℕ} (a b : Fin q)
    {reference w : Fin q → Z4}
    (h :
      openEdgeCellWordSignature a b w =
        openEdgeCellWordSignature a b reference) :
    w b = reference b :=
  congrArg OpenEdgeCellWordSignature.rightLabel h

/-! ## Generic exact finite regrouping -/

/-- Any finite sum splits exactly into the fibres of an open-word
signature. -/
theorem sum_eq_sum_openEdgeCellWordSignature_fibers
    {ι R : Type*} [AddCommMonoid R]
    {q : ℕ} (s : Finset ι)
    (word : ι → Fin q → Z4)
    (a b : Fin q) (F : ι → R) :
    (∑ i ∈ s, F i) =
      ∑ sig ∈
          s.image
            (fun i =>
              openEdgeCellWordSignature
                a b (word i)),
        ∑ i ∈
            s.filter
              (fun i =>
                openEdgeCellWordSignature
                    a b (word i) = sig),
          F i := by
  classical
  symm
  calc
    (∑ sig ∈
        s.image
          (fun i =>
            openEdgeCellWordSignature
              a b (word i)),
      ∑ i ∈
          s.filter
            (fun i =>
              openEdgeCellWordSignature
                  a b (word i) = sig),
        F i) =
        ∑ sig ∈
            s.image
              (fun i =>
                openEdgeCellWordSignature
                  a b (word i)),
          ∑ i ∈ s,
            if openEdgeCellWordSignature
                a b (word i) = sig then
              F i
            else 0 := by
      simp_rw [Finset.sum_filter]
    _ =
        ∑ i ∈ s,
          ∑ sig ∈
              s.image
                (fun j =>
                  openEdgeCellWordSignature
                    a b (word j)),
            if openEdgeCellWordSignature
                a b (word i) = sig then
              F i
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ s, F i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_image.mpr ⟨i, hi, rfl⟩]

/-! ## The genuine selected physical cell carrier -/

/-- Restrict one ambient cell index to the canonical marked block. -/
def r324SelectedMarkedCellWord
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (y : Fin (2 * m) → Z4) :
    Fin
      (2 * residualBlockOrder
        (r324MarkedResidualBlock
          κp κm π selected)) → Z4 :=
  r324MarkedResidualBlockWord
    κp κm π selected y

/-- Signature of the marked-block word carried by one genuine ambient
cell index. -/
def r324SelectedMarkedCellSignature
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (y : Fin (2 * m) → Z4) :
    OpenEdgeCellWordSignature
      (2 * residualBlockOrder
        (r324MarkedResidualBlock
          κp κm π selected)) :=
  openEdgeCellWordSignature
    (r324MarkedResidualLowerPosition
      κp κm π selected)
    (r324MarkedResidualUpperPosition
      κp κm π selected)
    (r324SelectedMarkedCellWord
      κp κm π selected y)

/-- The finite set of signatures that actually occur in the selected
physical cell partition. -/
def r324SelectedPhysicalCellSignatures
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε) :
    Finset
      (OpenEdgeCellWordSignature
        (2 * residualBlockOrder
          (r324MarkedResidualBlock
            κp κm π selected))) :=
  (SmoothCutoff.r324SelectedPhysicalOpenEdgeCells
      κp κm π selected ε hε).indices.image
    (r324SelectedMarkedCellSignature
      κp κm π selected)

/-- Actual ambient physical cell indices in one marked-word signature
fibre. -/
def r324SelectedPhysicalCellSignatureFiber
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (sig :
      OpenEdgeCellWordSignature
        (2 * residualBlockOrder
          (r324MarkedResidualBlock
            κp κm π selected))) :
    Finset (Fin (2 * m) → Z4) :=
  (SmoothCutoff.r324SelectedPhysicalOpenEdgeCells
      κp κm π selected ε hε).indices.filter
    (fun y =>
      r324SelectedMarkedCellSignature
        κp κm π selected y = sig)

/-- Exact decomposition of the genuine selected physical cell-index sum
by support/raw-profile/endpoint signatures. -/
theorem sum_selectedPhysicalCells_eq_signatureFibers
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    {R : Type*} [AddCommMonoid R]
    (F : (Fin (2 * m) → Z4) → R) :
    (∑ y ∈
        (SmoothCutoff.r324SelectedPhysicalOpenEdgeCells
          κp κm π selected ε hε).indices,
      F y) =
      ∑ sig ∈
          r324SelectedPhysicalCellSignatures
            κp κm π selected ε hε,
        ∑ y ∈
            r324SelectedPhysicalCellSignatureFiber
              κp κm π selected ε hε sig,
          F y := by
  exact
    sum_eq_sum_openEdgeCellWordSignature_fibers
      (SmoothCutoff.r324SelectedPhysicalOpenEdgeCells
        κp κm π selected ε hε).indices
      (r324SelectedMarkedCellWord
        κp κm π selected)
      (r324MarkedResidualLowerPosition
        κp κm π selected)
      (r324MarkedResidualUpperPosition
        κp κm π selected)
      F

/-- Every actual selected physical cell index satisfies the ambient
one-open-edge constraint. -/
theorem respectsExcept_of_mem_r324SelectedPhysicalOpenEdgeCells
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    {y : Fin (2 * m) → Z4}
    (hy :
      y ∈
        (SmoothCutoff.r324SelectedPhysicalOpenEdgeCells
          κp κm π selected ε hε).indices) :
    RespectsPairingExcept
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (r324ResidualMarkedUpperEndpoint π selected)
      y := by
  change
    y ∈
      (r324MarkedResidualOpenEdgeCells
        κp κm π selected ε hε).indices at hy
  exact (Finset.mem_filter.mp hy).2

/-- Consequently, every word in an actual signature fibre obeys the
local unmarked pairing constraint on the unique marked block. -/
theorem selectedMarkedCellWord_respectsExcept_of_mem
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (sig :
      OpenEdgeCellWordSignature
        (2 * residualBlockOrder
          (r324MarkedResidualBlock
            κp κm π selected)))
    {y : Fin (2 * m) → Z4}
    (hy :
      y ∈
        r324SelectedPhysicalCellSignatureFiber
          κp κm π selected ε hε sig) :
    RespectsPairingExcept
      (residualPrimitiveBlockPairing
        (momentCombinedPairing κp κm π)
        (r324MarkedResidualBlock κp κm π selected)
        (r324MarkedResidualBlock_isFullyPairedOn
          κp κm π selected))
      (r324MarkedResidualLowerPosition
        κp κm π selected)
      (r324MarkedResidualUpperPosition
        κp κm π selected)
      (r324SelectedMarkedCellWord
        κp κm π selected y) := by
  have hyIndex :
      y ∈
        (SmoothCutoff.r324SelectedPhysicalOpenEdgeCells
          κp κm π selected ε hε).indices :=
    (Finset.mem_filter.mp hy).1
  exact
    r324MarkedResidualBlockWord_respectsExcept
      κp κm π selected y
      (respectsExcept_of_mem_r324SelectedPhysicalOpenEdgeCells
        κp κm π selected ε hε hyIndex)

end

end Anderson4D
