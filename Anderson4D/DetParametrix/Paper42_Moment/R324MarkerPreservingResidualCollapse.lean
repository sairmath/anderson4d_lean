import Anderson4D.DetParametrix.Paper42_Moment.R324SingleProjectedSlotClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324CrossSlotFrequencyConservation
import Anderson4D.DetParametrix.Paper42_Moment.R324CovarianceBlocks

/-!
# Marker-preserving residual collapse for R-324

After the signed within-copy collapses, a selected cross-copy covariance
must remain visible while the residual primitive blocks are collapsed.
This file records that visibility directly on the genuine residual block
schedule.

The marked covariance product below differs from the physical covariance
product at exactly one lower endpoint.  The residual blocks partition the
post-phase-A carrier and are closed under the combined pairing, so:

* the two endpoints of the marked cross slot lie in one unique nonempty
  residual block;
* every other block contains neither endpoint and retains its complete
  `etaEpsT4` covariance product;
* collapsing an unmarked head block leaves the marked product on the
  tail; and
* collapsing the marked head block leaves a completely unmarked tail.

These are exact finite-product identities.  No equality with the final
R-324 moment, no analytic estimate, and no abstract output predicate is
asserted here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## A single marked lower endpoint -/

/-- Covariance product on an ambient block with exactly one distinguished
lower endpoint replaced by the R-324 high-frequency projection. -/
def SmoothCutoff.r324MarkedPairingCovarianceProductOn
    {n : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κ : PartialPairing (Fin n)) (marked : Fin n)
    (B : Finset (Fin n)) (v : Fin n → T4) : ℂ :=
  ∏ i ∈ B.filter (fun i => i < κ i),
    if i = marked then
      ρ.r324ProjectedCovarianceC ε L (v i - v (κ i))
    else
      (ρ.etaEpsT4 ε (v i - v (κ i)) : ℂ)

/-- An unmarked block is literally the existing complete physical
covariance product (coerced to `ℂ`). -/
theorem SmoothCutoff.r324MarkedPairingCovarianceProductOn_eq_complete
    {n : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κ : PartialPairing (Fin n)) (marked : Fin n)
    (B : Finset (Fin n)) (v : Fin n → T4)
    (hmarked : marked ∉ B) :
    ρ.r324MarkedPairingCovarianceProductOn
        ε L κ marked B v =
      (pairingCovarianceProductOn ρ ε κ B v : ℂ) := by
  unfold SmoothCutoff.r324MarkedPairingCovarianceProductOn
    pairingCovarianceProductOn
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  have hiB : i ∈ B := (Finset.mem_filter.mp hi).1
  have himarked : i ≠ marked := by
    intro h
    exact hmarked (h ▸ hiB)
  simp only [himarked, ↓reduceIte]

/-- Marked covariance products multiply over disjoint blocks without
creating another projected factor. -/
theorem SmoothCutoff.r324MarkedPairingCovarianceProductOn_union
    {n : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κ : PartialPairing (Fin n)) (marked : Fin n)
    (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (v : Fin n → T4) :
    ρ.r324MarkedPairingCovarianceProductOn
        ε L κ marked (A ∪ B) v =
      ρ.r324MarkedPairingCovarianceProductOn
          ε L κ marked A v *
        ρ.r324MarkedPairingCovarianceProductOn
          ε L κ marked B v := by
  have hfilter :
      (A ∪ B).filter (fun i => i < κ i) =
        A.filter (fun i => i < κ i) ∪
          B.filter (fun i => i < κ i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdisjoint :
      Disjoint
        (A.filter (fun i => i < κ i))
        (B.filter (fun i => i < κ i)) := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact
      (Finset.disjoint_left.mp hAB)
        (Finset.mem_filter.mp hiA).1
        (Finset.mem_filter.mp hiB).1
  unfold SmoothCutoff.r324MarkedPairingCovarianceProductOn
  rw [hfilter, Finset.prod_union hdisjoint]

/-! ## The genuine marked residual block -/

/-- The lower endpoint of a selected residual cross covariance. -/
def r324ResidualMarkedLowerEndpoint
    {m : ℕ} {κp : PartialPairing (Fin m)}
    (selected : R324ResidualCovarianceSlot κp) :
    Fin (2 * m) :=
  leftMomentIndex selected.1

/-- The upper endpoint of a selected residual cross covariance. -/
def r324ResidualMarkedUpperEndpoint
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Fin (2 * m) :=
  rightMomentIndex (π selected).1

theorem r324ResidualMarkedLowerEndpoint_mem_active
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (selected : R324ResidualCovarianceSlot κp) :
    r324ResidualMarkedLowerEndpoint selected ∈
      momentResidualActive κp κm := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨selected.1,
      singles_subset_finalActive κp selected.2,
      rfl⟩

theorem r324ResidualMarkedUpperEndpoint_mem_active
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    r324ResidualMarkedUpperEndpoint π selected ∈
      momentResidualActive κp κm := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨(π selected).1,
      singles_subset_finalActive κm (π selected).2,
      rfl⟩

@[simp]
theorem momentCombinedPairing_r324ResidualMarkedLowerEndpoint
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    momentCombinedPairing κp κm π
        (r324ResidualMarkedLowerEndpoint selected) =
      r324ResidualMarkedUpperEndpoint π selected := by
  exact momentCombinedPairing_left_single
    κp κm π selected.1 selected.2

theorem r324ResidualMarkedLowerEndpoint_lt_upper
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    r324ResidualMarkedLowerEndpoint selected <
      r324ResidualMarkedUpperEndpoint π selected := by
  rw [←
    momentCombinedPairing_r324ResidualMarkedLowerEndpoint
      κp κm π selected]
  exact
    (leftMomentIndex_lt_combined_iff
      κp κm π selected.1).mpr (Or.inl selected.2)

/-- The selected cross lower endpoint belongs to a residual block in the
actual post-phase-A schedule. -/
theorem exists_residualBlock_mem_of_marked
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    ∃ B ∈ nonemptyMomentResidualCollapseBlocks κp κm π,
      r324ResidualMarkedLowerEndpoint selected ∈ B := by
  have hactive :=
    r324ResidualMarkedLowerEndpoint_mem_active
      κp κm selected
  rw [←
    finsetUnionList_momentResidualCollapseBlocks
      κp κm π] at hactive
  obtain ⟨B, hB, hmarkedB⟩ :=
    (mem_finsetUnionList_iff
      (momentResidualCollapseBlocks κp κm π)).mp hactive
  refine ⟨B, ?_, hmarkedB⟩
  exact mem_nonemptyMomentResidualCollapseBlocks.mpr
    ⟨hB, ⟨_, hmarkedB⟩⟩

/-- Pairwise disjointness makes the residual block containing the marked
cross slot unique. -/
theorem existsUnique_residualBlock_mem_of_marked
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    ∃! B : Finset (Fin (2 * m)),
      B ∈ nonemptyMomentResidualCollapseBlocks κp κm π ∧
        r324ResidualMarkedLowerEndpoint selected ∈ B := by
  obtain ⟨B, hB, hmarkedB⟩ :=
    exists_residualBlock_mem_of_marked
      κp κm π selected
  refine ⟨B, ⟨hB, hmarkedB⟩, ?_⟩
  intro C hC
  by_contra hne
  have hdisjoint :=
    (nonemptyMomentResidualCollapseBlocks_pairwise_disjoint
      κp κm π).forall hB hC.1 (fun h => hne h.symm)
  exact
    (Finset.disjoint_left.mp hdisjoint)
      hmarkedB hC.2

/-- The unique block carrying the projected cross covariance. -/
def r324MarkedResidualBlock
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Finset (Fin (2 * m)) :=
  Classical.choose
    (existsUnique_residualBlock_mem_of_marked
      κp κm π selected)

theorem r324MarkedResidualBlock_mem
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    r324MarkedResidualBlock κp κm π selected ∈
      nonemptyMomentResidualCollapseBlocks κp κm π :=
  (Classical.choose_spec
    (existsUnique_residualBlock_mem_of_marked
      κp κm π selected)).1.1

theorem r324ResidualMarkedLowerEndpoint_mem_markedBlock
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    r324ResidualMarkedLowerEndpoint selected ∈
      r324MarkedResidualBlock κp κm π selected :=
  (Classical.choose_spec
    (existsUnique_residualBlock_mem_of_marked
      κp κm π selected)).1.2

/-- Closedness of the genuine residual block carries the other endpoint
of the marked cross covariance in the same unique block. -/
theorem r324ResidualMarkedUpperEndpoint_mem_markedBlock
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    r324ResidualMarkedUpperEndpoint π selected ∈
      r324MarkedResidualBlock κp κm π selected := by
  have hB :=
    (mem_nonemptyMomentResidualCollapseBlocks.mp
      (r324MarkedResidualBlock_mem
        κp κm π selected)).1
  have hclosed :=
    momentResidualCollapseBlock_isFullyPairedOn_of_mem
      κp κm π
      (r324MarkedResidualBlock κp κm π selected) hB
  rw [←
    momentCombinedPairing_r324ResidualMarkedLowerEndpoint
      κp κm π selected]
  exact hclosed.2 _
    (r324ResidualMarkedLowerEndpoint_mem_markedBlock
      κp κm π selected)

/-- The genuine marked block contains exactly the selected projected
cross covariance; every other covariance in that block is still the
complete physical covariance. -/
theorem SmoothCutoff.r324MarkedResidualBlockProduct_eq
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (r324MarkedResidualBlock κp κm π selected) v =
      ρ.r324ProjectedCovarianceC ε L
          (v (r324ResidualMarkedLowerEndpoint selected) -
            v (r324ResidualMarkedUpperEndpoint π selected)) *
        ∏ i ∈
            ((r324MarkedResidualBlock κp κm π selected).filter
              (fun i =>
                i < momentCombinedPairing κp κm π i)).erase
              (r324ResidualMarkedLowerEndpoint selected),
          (ρ.etaEpsT4 ε
            (v i -
              v (momentCombinedPairing κp κm π i)) : ℂ) := by
  let marked :=
    r324ResidualMarkedLowerEndpoint selected
  let κ := momentCombinedPairing κp κm π
  let B := r324MarkedResidualBlock κp κm π selected
  let S := B.filter fun i => i < κ i
  let f : Fin (2 * m) → ℂ := fun i =>
    if i = marked then
      ρ.r324ProjectedCovarianceC ε L (v i - v (κ i))
    else
      (ρ.etaEpsT4 ε (v i - v (κ i)) : ℂ)
  have hmarkedS : marked ∈ S := by
    rw [Finset.mem_filter]
    exact
      ⟨r324ResidualMarkedLowerEndpoint_mem_markedBlock
          κp κm π selected,
        r324ResidualMarkedLowerEndpoint_lt_upper
          κp κm π selected |>.trans_le
            (le_of_eq
              (momentCombinedPairing_r324ResidualMarkedLowerEndpoint
                κp κm π selected).symm)⟩
  change (∏ i ∈ S, f i) =
    ρ.r324ProjectedCovarianceC ε L
          (v marked -
            v (r324ResidualMarkedUpperEndpoint π selected)) *
      ∏ i ∈ S.erase marked,
        (ρ.etaEpsT4 ε (v i - v (κ i)) : ℂ)
  rw [← Finset.mul_prod_erase S f hmarkedS]
  have hκmarked :
      κ marked =
        r324ResidualMarkedUpperEndpoint π selected :=
    momentCombinedPairing_r324ResidualMarkedLowerEndpoint
      κp κm π selected
  simp only [f, if_pos, hκmarked]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hine : i ≠ marked :=
    Finset.ne_of_mem_erase hi
  simp only [hine, ↓reduceIte]

/-- Every other residual block contains neither endpoint of the selected
cross covariance. -/
theorem r324ResidualMarkedEndpoints_not_mem_otherBlock
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ nonemptyMomentResidualCollapseBlocks κp κm π)
    (hne :
      B ≠ r324MarkedResidualBlock κp κm π selected) :
    r324ResidualMarkedLowerEndpoint selected ∉ B ∧
      r324ResidualMarkedUpperEndpoint π selected ∉ B := by
  have hdisjoint :=
    (nonemptyMomentResidualCollapseBlocks_pairwise_disjoint
      κp κm π).forall hB
        (r324MarkedResidualBlock_mem κp κm π selected)
        hne
  exact
    ⟨fun h =>
      (Finset.disjoint_left.mp hdisjoint) h
        (r324ResidualMarkedLowerEndpoint_mem_markedBlock
          κp κm π selected),
      fun h =>
      (Finset.disjoint_left.mp hdisjoint) h
        (r324ResidualMarkedUpperEndpoint_mem_markedBlock
          κp κm π selected)⟩

/-! ## Exact one-step preservation -/

/-- If the next residual block is unmarked, its covariance factor is
complete and the unique projected factor remains on the tail. -/
theorem SmoothCutoff.r324MarkedResidualCollapseStep_unmarked
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (B : Finset (Fin (2 * m)))
    (rest : List (Finset (Fin (2 * m))))
    (hdisjoint : Disjoint B (finsetUnionList rest))
    (hB :
      r324ResidualMarkedLowerEndpoint selected ∉ B)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (finsetUnionList (B :: rest)) v =
      (pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π) B v : ℂ) *
        ρ.r324MarkedPairingCovarianceProductOn ε L
          (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected)
          (finsetUnionList rest) v := by
  rw [finsetUnionList,
    ρ.r324MarkedPairingCovarianceProductOn_union
      ε L (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      B (finsetUnionList rest) hdisjoint v,
    ρ.r324MarkedPairingCovarianceProductOn_eq_complete
      ε L (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected) B v hB]

/-- If the next residual block carries the marker, its tail is literally
the complete unprojected covariance product.  Thus the marked factor is
consumed once and cannot be duplicated by later primitive collapses. -/
theorem SmoothCutoff.r324MarkedResidualCollapseStep_marked
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (B : Finset (Fin (2 * m)))
    (rest : List (Finset (Fin (2 * m))))
    (hdisjoint : Disjoint B (finsetUnionList rest))
    (hB :
      r324ResidualMarkedLowerEndpoint selected ∈ B)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (finsetUnionList (B :: rest)) v =
      ρ.r324MarkedPairingCovarianceProductOn ε L
          (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected) B v *
        (pairingCovarianceProductOn ρ ε
          (momentCombinedPairing κp κm π)
          (finsetUnionList rest) v : ℂ) := by
  have hnotTail :
      r324ResidualMarkedLowerEndpoint selected ∉
        finsetUnionList rest := by
    intro htail
    exact (Finset.disjoint_left.mp hdisjoint) hB htail
  rw [finsetUnionList,
    ρ.r324MarkedPairingCovarianceProductOn_union
      ε L (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      B (finsetUnionList rest) hdisjoint v,
    ρ.r324MarkedPairingCovarianceProductOn_eq_complete
      ε L (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (finsetUnionList rest) v hnotTail]

/-- On every genuine residual block other than the unique marked one, all
covariances remain the complete physical `etaEpsT4` factors. -/
theorem SmoothCutoff.r324MarkedResidualBlockFactor_eq_complete_of_ne
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (B : Finset (Fin (2 * m)))
    (hB : B ∈ nonemptyMomentResidualCollapseBlocks κp κm π)
    (hne :
      B ≠ r324MarkedResidualBlock κp κm π selected)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected) B v =
      (pairingCovarianceProductOn ρ ε
        (momentCombinedPairing κp κm π) B v : ℂ) := by
  exact
    ρ.r324MarkedPairingCovarianceProductOn_eq_complete
      ε L (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected) B v
      (r324ResidualMarkedEndpoints_not_mem_otherBlock
        κp κm π selected B hB hne).1

end

end Anderson4D
