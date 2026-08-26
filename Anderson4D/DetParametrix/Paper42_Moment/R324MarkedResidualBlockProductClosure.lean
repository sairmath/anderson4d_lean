import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse

/-!
# Exact residual block product with one surviving marker

After the signed within-half collapses, the residual carrier is partitioned
by the genuine nonempty residual blocks.  This module performs only the
finite-product part of the residual collapse: it extracts the unique marked
block and proves that every remaining block is still its complete physical
covariance factor.

No spatial norm, tree cover, cell volume, or automorphism factor is used
here.  In particular, the marked block remains open for the later analytic
cell estimate.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## A marked product over a disjoint block list -/

/-- Exact multiplicative decomposition of a marked covariance product over
a pairwise-disjoint list of blocks.  The distinguished factor occurs in at
most one block because the list is disjoint. -/
theorem SmoothCutoff.r324MarkedPairingCovarianceProductOn_finsetUnionList
    {n : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κ : PartialPairing (Fin n)) (marked : Fin n)
    (blocks : List (Finset (Fin n)))
    (hblocks : blocks.Pairwise Disjoint)
    (v : Fin n → T4) :
    ρ.r324MarkedPairingCovarianceProductOn
        ε L κ marked (finsetUnionList blocks) v =
      (blocks.map fun B =>
        ρ.r324MarkedPairingCovarianceProductOn
          ε L κ marked B v).prod := by
  induction blocks with
  | nil =>
      simp [finsetUnionList,
        SmoothCutoff.r324MarkedPairingCovarianceProductOn]
  | cons A blocks ih =>
      have hpair := List.pairwise_cons.mp hblocks
      rw [finsetUnionList, List.map_cons, List.prod_cons,
        ρ.r324MarkedPairingCovarianceProductOn_union]
      · rw [ih hpair.2]
      · exact disjoint_finsetUnionList_of_forall_mem
          A blocks hpair.1

/-! ## The concrete residual schedule -/

/-- Pairwise-disjoint nonempty residual blocks cannot repeat. -/
theorem nonemptyMomentResidualCollapseBlocks_nodup
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (nonemptyMomentResidualCollapseBlocks κp κm π).Nodup := by
  have haux :
      ∀ blocks : List (Finset (Fin (2 * m))),
        blocks.Pairwise Disjoint →
        blocks.Forall Finset.Nonempty →
        blocks.Nodup := by
    intro blocks hpair hnonempty
    induction blocks with
    | nil =>
        simp
    | cons B blocks ih =>
        rw [List.pairwise_cons] at hpair
        rw [List.forall_cons] at hnonempty
        rw [List.nodup_cons]
        constructor
        · intro hB
          obtain ⟨i, hi⟩ := hnonempty.1
          exact
            (Finset.disjoint_left.mp
              (hpair.1 B hB)) hi hi
        · exact ih hpair.2 hnonempty.2
  apply haux
  · exact
      nonemptyMomentResidualCollapseBlocks_pairwise_disjoint
        κp κm π
  · rw [List.forall_iff_forall_mem]
    intro B hB
    exact (mem_nonemptyMomentResidualCollapseBlocks.mp hB).2

/-- Product of the complete physical covariance factors on every residual
block except the unique marked block. -/
def SmoothCutoff.r324UnmarkedResidualBlockProduct
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) : ℂ :=
  ((nonemptyMomentResidualCollapseBlocks κp κm π).toFinset.erase
      (r324MarkedResidualBlock κp κm π selected)).prod
    fun B =>
      (pairingCovarianceProductOn ρ ε
        (momentCombinedPairing κp κm π) B v : ℂ)

/-- **Exact marker-preserving residual block collapse.**

The marked covariance product on the actual residual carrier is the genuine
marked-block factor times complete covariance factors on all other primitive
blocks.  Thus the preliminary collapses neither duplicate nor discard the
selected projected edge. -/
theorem SmoothCutoff.r324MarkedResidualActiveProduct_eq_marked_mul_unmarked
    {m : ℕ} (ρ : SmoothCutoff) (ε L : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (v : Fin (2 * m) → T4) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (momentResidualActive κp κm) v =
      ρ.r324MarkedPairingCovarianceProductOn ε L
          (momentCombinedPairing κp κm π)
          (r324ResidualMarkedLowerEndpoint selected)
          (r324MarkedResidualBlock κp κm π selected) v *
        ρ.r324UnmarkedResidualBlockProduct
          ε κp κm π selected v := by
  let blocks :=
    nonemptyMomentResidualCollapseBlocks κp κm π
  let marked :=
    r324MarkedResidualBlock κp κm π selected
  let κ :=
    momentCombinedPairing κp κm π
  let f : Finset (Fin (2 * m)) → ℂ := fun B =>
    ρ.r324MarkedPairingCovarianceProductOn ε L κ
      (r324ResidualMarkedLowerEndpoint selected) B v
  have hcover :
      finsetUnionList blocks =
        momentResidualActive κp κm := by
    dsimp only [blocks]
    unfold nonemptyMomentResidualCollapseBlocks
    rw [finsetUnionList_filter_nonempty,
      finsetUnionList_momentResidualCollapseBlocks]
  have hfactor :
      ρ.r324MarkedPairingCovarianceProductOn ε L κ
          (r324ResidualMarkedLowerEndpoint selected)
          (momentResidualActive κp κm) v =
        (blocks.map f).prod := by
    rw [← hcover]
    exact
      ρ.r324MarkedPairingCovarianceProductOn_finsetUnionList
        ε L κ (r324ResidualMarkedLowerEndpoint selected)
        blocks
        (nonemptyMomentResidualCollapseBlocks_pairwise_disjoint
          κp κm π) v
  have hmarked : marked ∈ blocks.toFinset := by
    exact List.mem_toFinset.mpr
      (r324MarkedResidualBlock_mem κp κm π selected)
  have hnodup : blocks.Nodup := by
    simpa only [blocks] using
      nonemptyMomentResidualCollapseBlocks_nodup κp κm π
  have hlistprod :
      (blocks.map f).prod = blocks.toFinset.prod f :=
    (List.prod_toFinset f hnodup).symm
  rw [hfactor, hlistprod]
  rw [← Finset.mul_prod_erase _ _ hmarked]
  congr 1
  unfold SmoothCutoff.r324UnmarkedResidualBlockProduct
  apply Finset.prod_congr rfl
  intro B hB
  have hne : B ≠ marked :=
    (Finset.mem_erase.mp hB).1
  have hBmem : B ∈ blocks :=
    List.mem_toFinset.mp (Finset.mem_erase.mp hB).2
  exact
    ρ.r324MarkedResidualBlockFactor_eq_complete_of_ne
      ε L κp κm π selected B hBmem hne v

end

end Anderson4D
