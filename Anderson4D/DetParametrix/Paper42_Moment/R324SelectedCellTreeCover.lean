import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedCellSignature
import Anderson4D.HeppTree.Decomposition

/-!
# Hepp-tree cover of the augmented selected cell word

Within one exact support/raw-profile/endpoint signature fibre, the marked
block word is dummy-closed.  The augmented pairing is full and respects
the augmented word, so every occupied label now occurs at least twice.
The augmented word is also in the finite lattice box inherited from the
actual torus cells.

Thus every actual selected cell word lies in `rdec_repeatedTuples` after
augmentation and hence in at least one valid Hepp-tree slice.  The passage
from the repeated-tuple carrier to the sum of tree slices is a
nonnegative enlargement because the tree cover can overlap; all
support/profile/endpoint regrouping before it is exact.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open PlaneTree

/-! ## The actual finite box -/

/-- Natural half-width of the torus grid used by the selected cell
partition. -/
def selectedCellBoxRadius (ε : ℝ) : ℕ :=
  (torusGridRadius ε).natAbs

theorem torusGridRadius_nonneg
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ torusGridRadius ε := by
  unfold torusGridRadius
  apply Int.ceil_nonneg
  exact div_nonneg Real.pi_pos.le hε.le

theorem selectedCellBoxRadius_cast
    {ε : ℝ} (hε : 0 < ε) :
    (selectedCellBoxRadius ε : ℤ) =
      torusGridRadius ε := by
  exact Int.natAbs_of_nonneg
    (torusGridRadius_nonneg hε)

/-- Every label in the actual torus grid lies in the natural box consumed
by the Hepp-tree decomposition. -/
theorem abs_le_selectedCellBoxRadius_of_mem_torusGrid
    {ε : ℝ} (hε : 0 < ε) {y : Z4}
    (hy : y ∈ torusGrid ε) :
    ∀ i, |y i| ≤ (selectedCellBoxRadius ε : ℤ) := by
  unfold torusGrid at hy
  rw [Fintype.mem_piFinset] at hy
  intro i
  rw [selectedCellBoxRadius_cast hε, abs_le]
  exact Finset.mem_Icc.mp (hy i)

/-! ## Augmenting one actual marked-block cell word -/

/-- Dummy-closed marked-block word attached to one ambient cell index. -/
def r324SelectedMarkedAugmentedCellWord
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (y : Fin (2 * m) → Z4) :
    Fin
      (2 * residualBlockOrder
          (r324MarkedResidualBlock
            κp κm π selected) + 2) → Z4 :=
  openEdgeAugmentedWord
    (r324SelectedMarkedCellWord
      κp κm π selected y)
    (r324MarkedResidualLowerPosition
      κp κm π selected)
    (r324MarkedResidualUpperPosition
      κp κm π selected)

/-- Adding copies of two already occupied endpoint labels does not change
the finite support. -/
theorem tupleSupport_openEdgeAugmentedWord
    {α : Type*} [DecidableEq α] {q : ℕ}
    (w : Fin q → α) (a b : Fin q) :
    (Finset.univ.image
        (openEdgeAugmentedWord w a b)) =
      Finset.univ.image w := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    rcases s with i | j
    · exact ⟨i, by simpa using hi⟩
    · fin_cases j
      · exact
          ⟨a, by
            simpa [openEdgeAugmentedWord,
              openEdgeAugmentedSumWord] using hi⟩
      · exact
          ⟨b, by
            simpa [openEdgeAugmentedWord,
              openEdgeAugmentedSumWord] using hi⟩
  · rintro ⟨i, hi⟩
    exact
      ⟨Fin.castAdd 2 i, by
        simpa using hi⟩

theorem tupleSupport_r324SelectedMarkedAugmentedCellWord
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (y : Fin (2 * m) → Z4) :
    tupleSupport
        (r324SelectedMarkedAugmentedCellWord
          κp κm π selected y) =
      tupleSupport
        (r324SelectedMarkedCellWord
          κp κm π selected y) := by
  exact
    tupleSupport_openEdgeAugmentedWord
      (r324SelectedMarkedCellWord
        κp κm π selected y)
      (r324MarkedResidualLowerPosition
        κp κm π selected)
      (r324MarkedResidualUpperPosition
        κp κm π selected)

/-- Every coordinate of an actual ambient cell index lies in the torus
grid. -/
theorem mem_torusGrid_of_mem_r324SelectedPhysicalCells
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
    ∀ i, y i ∈ torusGrid ε := by
  change
    y ∈
      (r324MarkedResidualOpenEdgeCells
        κp κm π selected ε hε).indices at hy
  have hbox := (Finset.mem_filter.mp hy).1
  rw [Fintype.mem_piFinset] at hbox
  exact hbox

/-- Every label of the local marked-block word remains in the actual
torus grid. -/
theorem r324SelectedMarkedCellWord_mem_torusGrid
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
    ∀ i,
      r324SelectedMarkedCellWord
          κp κm π selected y i ∈
        torusGrid ε := by
  intro i
  exact
    mem_torusGrid_of_mem_r324SelectedPhysicalCells
      κp κm π selected ε hε hy _

/-- Dummy copies preserve membership in the actual torus grid. -/
theorem r324SelectedMarkedAugmentedCellWord_mem_torusGrid
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
    ∀ i,
      r324SelectedMarkedAugmentedCellWord
          κp κm π selected y i ∈
        torusGrid ε := by
  intro i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  rcases s with i | j
  · simpa [r324SelectedMarkedAugmentedCellWord,
      openEdgeAugmentedWord,
      openEdgeAugmentedSumWord] using
        (r324SelectedMarkedCellWord_mem_torusGrid
          κp κm π selected ε hε hy i)
  · fin_cases j
    · simpa [r324SelectedMarkedAugmentedCellWord,
        openEdgeAugmentedWord,
        openEdgeAugmentedSumWord] using
          (r324SelectedMarkedCellWord_mem_torusGrid
            κp κm π selected ε hε hy
            (r324MarkedResidualLowerPosition
              κp κm π selected))
    · simpa [r324SelectedMarkedAugmentedCellWord,
        openEdgeAugmentedWord,
        openEdgeAugmentedSumWord] using
          (r324SelectedMarkedCellWord_mem_torusGrid
            κp κm π selected ε hε hy
            (r324MarkedResidualUpperPosition
              κp κm π selected))

/-- The augmented actual marked-block word belongs to the finite bounded
tuple carrier. -/
theorem r324SelectedMarkedAugmentedCellWord_mem_boundedTuples
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
    r324SelectedMarkedAugmentedCellWord
        κp κm π selected y ∈
      rdec_boundedTuples
        (selectedCellBoxRadius ε)
        (2 * residualBlockOrder
          (r324MarkedResidualBlock
            κp κm π selected) + 2) := by
  rw [rdec_mem_boundedTuples]
  intro j i
  exact
    abs_le_selectedCellBoxRadius_of_mem_torusGrid
      hε
      (r324SelectedMarkedAugmentedCellWord_mem_torusGrid
        κp κm π selected ε hε hy j)
      i

/-- The dummy-closed word has no singleton occupied value and hence lies
in the repeated-tuple carrier used by the Hepp-tree cover. -/
theorem r324SelectedMarkedAugmentedCellWord_mem_repeatedTuples
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
    r324SelectedMarkedAugmentedCellWord
        κp κm π selected y ∈
      rdec_repeatedTuples
        (selectedCellBoxRadius ε)
        (2 * residualBlockOrder
          (r324MarkedResidualBlock
            κp κm π selected) + 2) := by
  let κB :=
    residualPrimitiveBlockPairing
      (momentCombinedPairing κp κm π)
      (r324MarkedResidualBlock κp κm π selected)
      (r324MarkedResidualBlock_isFullyPairedOn
        κp κm π selected)
  let a :=
    r324MarkedResidualLowerPosition
      κp κm π selected
  let b :=
    r324MarkedResidualUpperPosition
      κp κm π selected
  let w :=
    r324SelectedMarkedCellWord
      κp κm π selected y
  have hambient :=
    respectsExcept_of_mem_r324SelectedPhysicalOpenEdgeCells
      κp κm π selected ε hε hy
  have hrespectLocal :
      RespectsPairingExcept κB a b w :=
    r324MarkedResidualBlockWord_respectsExcept
      κp κm π selected y hambient
  have hfull : κB.IsFull :=
    (mem_primitiveFullPairings.mp
      (r324MarkedResidualBlockPairing_mem_primitiveFullPairings
        κp κm π selected)).1
  have haugFull :
      (openEdgeAugmentedPairing κB a b
        (r324MarkedResidualBlockPairing_lower
          κp κm π selected)
        (ne_of_lt
          (r324MarkedResidualLowerPosition_lt_upper
            κp κm π selected))).IsFull :=
    openEdgeAugmentedPairing_isFull
      κB a b
      (r324MarkedResidualBlockPairing_lower
        κp κm π selected)
      (ne_of_lt
        (r324MarkedResidualLowerPosition_lt_upper
          κp κm π selected))
      hfull
  have haugRespect :
      (openEdgeAugmentedPairing κB a b
        (r324MarkedResidualBlockPairing_lower
          κp κm π selected)
        (ne_of_lt
          (r324MarkedResidualLowerPosition_lt_upper
            κp κm π selected))).RespectsWord
        (openEdgeAugmentedWord w a b) :=
    openEdgeAugmentedPairing_respectsWord
      κB a b
      (r324MarkedResidualBlockPairing_lower
        κp κm π selected)
      (ne_of_lt
        (r324MarkedResidualLowerPosition_lt_upper
          κp κm π selected))
      w
      (fun i hia hib =>
        (hrespectLocal i hia hib).symm)
  rw [rdec_mem_repeatedTuples]
  refine
    ⟨r324SelectedMarkedAugmentedCellWord_mem_boundedTuples
        κp κm π selected ε hε hy,
      ?_⟩
  intro j
  have hpos :
      0 <
        wordFiberCount
          (openEdgeAugmentedWord w a b)
          (openEdgeAugmentedWord w a b j) := by
    unfold wordFiberCount
    apply Finset.card_pos.mpr
    exact
      ⟨j, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, rfl⟩⟩
  have heven :
      Even
        (wordFiberCount
          (openEdgeAugmentedWord w a b)
          (openEdgeAugmentedWord w a b j)) :=
    even_wordFiberCount_of_full_respectsWord
      haugFull haugRespect _
  have htwo :
    2 ≤
      wordFiberCount
        (openEdgeAugmentedWord w a b)
        (openEdgeAugmentedWord w a b j) := by
    obtain ⟨k, hk⟩ := heven
    omega
  simpa [wordFiberCount,
    r324SelectedMarkedAugmentedCellWord, w] using htwo

/-! ## The first nonnegative enlargement: overlapping tree slices -/

/-- Every actual augmented marked-block cell word occurs in at least one
valid Hepp-tree realization slice. -/
theorem exists_treeRealized_r324SelectedMarkedAugmentedCellWord
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
    ∃ t ∈
        rdec_treeEnum
          (2 * residualBlockOrder
            (r324MarkedResidualBlock
              κp κm π selected) + 2),
      r324SelectedMarkedAugmentedCellWord
          κp κm π selected y ∈
        rdec_treeRealized t
          (selectedCellBoxRadius ε)
          (2 * residualBlockOrder
            (r324MarkedResidualBlock
              κp κm π selected) + 2) := by
  let q :=
    2 * residualBlockOrder
      (r324MarkedResidualBlock
        κp κm π selected) + 2
  have hq : 1 ≤ q := by
    dsimp only [q]
    omega
  have hmem :=
    rdec_repeatedTuples_subset_treeUnion
      (selectedCellBoxRadius ε) q hq
      (r324SelectedMarkedAugmentedCellWord_mem_repeatedTuples
        κp κm π selected ε hε hy)
  rw [Finset.mem_biUnion] at hmem
  exact hmem

/-- A valid tree is either genuinely branched at the root or is the
one-leaf tree.  The latter is the constant-label base case and must not be
silently passed to Proposition 5.7, whose public statement assumes a
branched root. -/
theorem r324ValidTree_root_branch_or_eq_leaf
    {t : PlaneTree} (ht : t.isValid = true) :
    rootV t ∈ BranchNodes t ∨ t = PlaneTree.leaf := by
  obtain ⟨cs⟩ := t
  by_cases hbranch : 2 ≤ cs.length
  · left
    rw [mem_BranchNodes_iff]
    exact hbranch
  · right
    have hvalid :
        (cs.length != 1) = true := by
      have ht' :
          (cs.length != 1) = true ∧
            isValidList cs = true := by
        simpa only [PlaneTree.isValid,
          Bool.and_eq_true] using ht
      exact ht'.1
    have hne : cs.length ≠ 1 := by
      simpa only [bne_iff_ne] using hvalid
    have hzero : cs.length = 0 := by omega
    have hnil : cs = [] :=
      List.eq_nil_of_length_eq_zero hzero
    subst cs
    rfl

/-- The tree-cover witness can be refined to an admissible injective leaf
embedding whose image is exactly the occupied support of the old open
word.  This is the realization datum consumed by the occupied-label
Proposition 5.7 specialization.

The disjunction is intentional: a branched tree enters Proposition 5.7,
whereas the one-leaf constant-label tree remains an explicit base case. -/
theorem exists_admissible_realization_r324SelectedMarkedCellWord
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
    ∃ t ∈
        rdec_treeEnum
          (2 * residualBlockOrder
            (r324MarkedResidualBlock
              κp κm π selected) + 2),
      ∃ Nm : HeppMarking t,
        ∃ z : HeppLeaf t → Z4,
          t.isValid = true ∧
          IsAdmissible Nm
              (selectedCellBoxRadius ε) z ∧
          leafEmbeddingImage z =
            tupleSupport
              (r324SelectedMarkedCellWord
                κp κm π selected y) ∧
          (rootV t ∈ BranchNodes t ∨
            t = PlaneTree.leaf) := by
  obtain ⟨t, htmem, htreal⟩ :=
    exists_treeRealized_r324SelectedMarkedAugmentedCellWord
      κp κm π selected ε hε hy
  have ht : t.isValid = true :=
    (rdec_mem_treeEnum.mp htmem).1
  obtain ⟨_hbounded, Nm, mu, hreal⟩ :=
    rdec_mem_treeRealized.mp htreal
  obtain
    ⟨z, _u, hadm, _hu, _hyz, hsupport⟩ :=
      tupleSupport_eq_leafEmbeddingImage_of_realizes
        (t := t) (Nm := Nm) (mu := mu) hreal
  refine ⟨t, htmem, Nm, z, ht, hadm, ?_, ?_⟩
  · exact
      hsupport.symm.trans
        (tupleSupport_r324SelectedMarkedAugmentedCellWord
          κp κm π selected y)
  · exact r324ValidTree_root_branch_or_eq_leaf ht

/-- A genuine selected physical cell word either belongs to the explicit
constant-label leaf-tree base case, or its occupied-label realization
feeds directly into the raw-count fixed-endpoint Proposition 5.7 bound.

This theorem is still purely the word-sum consumer.  It neither asserts
the analytic cell majorant nor suppresses the later cell-volume and
automorphism ledgers. -/
theorem exists_tree_realization_and_rawFiberBound_of_selectedCell
    {C : ℝ} (hperm : PermSumEstimate C)
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
    ∃ t ∈
        rdec_treeEnum
          (2 * residualBlockOrder
            (r324MarkedResidualBlock
              κp κm π selected) + 2),
      ∃ Nm : HeppMarking t,
        ∃ z : HeppLeaf t → Z4,
          t.isValid = true ∧
          IsAdmissible Nm
              (selectedCellBoxRadius ε) z ∧
          leafEmbeddingImage z =
            tupleSupport
              (r324SelectedMarkedCellWord
                κp κm π selected y) ∧
          (t = PlaneTree.leaf ∨
            (rootV t ∈ BranchNodes t ∧
              ∃ e :
                  HeppLeaf t ≃
                    {x // x ∈
                      tupleSupport
                        (r324SelectedMarkedCellWord
                          κp κm π selected y)},
                (∀ l : HeppLeaf t, (e l).1 = z l) ∧
                (let κB :=
                  residualPrimitiveBlockPairing
                    (momentCombinedPairing κp κm π)
                    (r324MarkedResidualBlock
                      κp κm π selected)
                    (r324MarkedResidualBlock_isFullyPairedOn
                      κp κm π selected)
                let a :=
                  r324MarkedResidualLowerPosition
                    κp κm π selected
                let b :=
                  r324MarkedResidualUpperPosition
                    κp κm π selected
                let reference :=
                  r324MarkedResidualOccupiedLeafWord
                    κp κm π selected y e
                ∃ n : ℕ, 2 ≤ n ∧
                  (∑ w ∈
                      openEdgeRawCountFixedEndpointFiber
                        κB a b reference,
                    heppChainWeight
                      (fun l : HeppLeaf t =>
                        (e l).1) w) ≤
                    (1 +
                        (2 *
                          (selectedCellBoxRadius ε : ℝ)) ^
                            2) ^ 2 *
                      permSumRHS C n t Nm
                        (openEdgeArbitraryMultiplicities
                          κB a b
                          (r324MarkedResidualBlockPairing_lower
                            κp κm π selected)
                          (ne_of_lt
                            (r324MarkedResidualLowerPosition_lt_upper
                              κp κm π selected))
                          ((mem_primitiveFullPairings.mp
                            (r324MarkedResidualBlockPairing_mem_primitiveFullPairings
                              κp κm π selected)).1)
                          reference
                          (r324MarkedResidualOccupiedLeafWord_surjective
                            κp κm π selected y e)
                          (r324MarkedResidualOccupiedLeafWord_respectsExcept
                            κp κm π selected y
                            (respectsExcept_of_mem_r324SelectedPhysicalOpenEdgeCells
                              κp κm π selected ε hε hy)
                            e))))) := by
  obtain
    ⟨t, htmem, Nm, z, ht, hadm, himage,
      hroot | hleaf⟩ :=
      exists_admissible_realization_r324SelectedMarkedCellWord
        κp κm π selected ε hε hy
  · refine
      ⟨t, htmem, Nm, z, ht, hadm, himage,
        Or.inr ⟨hroot, ?_⟩⟩
    let e :=
      leafEquivSupport z hadm.inj himage
    refine ⟨e, ?_, ?_⟩
    · exact fun l =>
        leafEquivSupport_apply_val
          z hadm.inj himage l
    dsimp only
    exact
      r324MarkedResidualRawCountFiber_le_permSumRHS
        hperm κp κm π selected y
        (respectsExcept_of_mem_r324SelectedPhysicalOpenEdgeCells
          κp κm π selected ε hε hy)
        e
        Nm ht hroot hadm
  · exact
      ⟨t, htmem, Nm, z, ht, hadm, himage,
        Or.inl hleaf⟩

end

end Anderson4D
