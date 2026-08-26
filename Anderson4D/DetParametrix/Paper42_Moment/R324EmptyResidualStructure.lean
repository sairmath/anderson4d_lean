import Anderson4D.DetParametrix.Paper42_Moment.R324WholeRootPointwiseNormalization

/-!
# The empty residual branch of the R-324 reduction

When both within-half contractions are full, Definition 3.1 exhausts both
active carriers.  Consequently the doubled residual carrier is empty, the
filtered residual collapse schedule has no blocks, and its primitive-sum
product is the multiplicative identity.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The doubled residual carrier is empty exactly when both within-half
pairings are full. -/
theorem momentResidualActive_eq_empty_iff_isFull
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    momentResidualActive κp κm = ∅ ↔
      κp.IsFull ∧ κm.IsFull := by
  constructor
  · intro hactive
    have himages :
        (finalActive κp).image leftMomentIndex = ∅ ∧
          (finalActive κm).image rightMomentIndex = ∅ := by
      apply Finset.union_eq_empty.mp
      simpa only [momentResidualActive] using hactive
    have hpFinal : finalActive κp = ∅ :=
      Finset.image_eq_empty.mp himages.1
    have hmFinal : finalActive κm = ∅ :=
      Finset.image_eq_empty.mp himages.2
    constructor
    · rw [PartialPairing.isFull_iff_singles_eq_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hiFinal := singles_subset_finalActive κp hi
      simp [hpFinal] at hiFinal
    · rw [PartialPairing.isFull_iff_singles_eq_empty]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hiFinal := singles_subset_finalActive κm hi
      simp [hmFinal] at hiFinal
  · rintro ⟨hp, hm⟩
    simp only [momentResidualActive,
      finalActive_eq_empty_of_full hp,
      finalActive_eq_empty_of_full hm,
      Finset.image_empty, Finset.empty_union]

/-- A full pairing of `Fin m` supplies the even-order witness in the exact
shape used by the full/full R-324 branch. -/
theorem PartialPairing.IsFull.exists_fin_order_eq_two_mul
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (hκ : κ.IsFull) :
    ∃ q : ℕ, m = 2 * q := by
  obtain ⟨q, hq⟩ := hκ.even_card
  have hq' : m = q + q := by
    simpa only [Fintype.card_fin] using hq
  exact ⟨q, by omega⟩

/-- No nonempty cross-cut collapse block survives when both within-half
pairings are full. -/
theorem nonemptyMomentResidualCollapseBlocks_eq_nil_of_isFull
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (π : κp.singles ≃ κm.singles)
    (hp : κp.IsFull) (hm : κm.IsFull) :
    nonemptyMomentResidualCollapseBlocks κp κm π = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro B hB
  have hBdata :=
    mem_nonemptyMomentResidualCollapseBlocks.mp hB
  obtain ⟨i, hi⟩ := hBdata.2
  have hiUnion :
      i ∈ finsetUnionList
        (momentResidualCollapseBlocks κp κm π) :=
    (mem_finsetUnionList_iff
      (momentResidualCollapseBlocks κp κm π)).mpr
      ⟨B, hBdata.1, hi⟩
  rw [finsetUnionList_momentResidualCollapseBlocks,
    (momentResidualActive_eq_empty_iff_isFull κp κm).mpr
      ⟨hp, hm⟩] at hiUnion
  simp at hiUnion

/-- The exact residual primitive-sum product is the empty product in the
full/full branch. -/
theorem r324ResidualPrimitiveSumProduct_eq_one_of_isFull
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hp : κp.IsFull) (hm : κm.IsFull)
    (v : Fin (2 * m) → T4) :
    r324ResidualPrimitiveSumProduct
        ρ ε κp κm π v = 1 := by
  unfold r324ResidualPrimitiveSumProduct
  rw [
    nonemptyMomentResidualCollapseBlocks_eq_nil_of_isFull
      π hp hm]
  rfl

end

end Anderson4D
