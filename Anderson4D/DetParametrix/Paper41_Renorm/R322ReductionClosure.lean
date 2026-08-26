import Anderson4D.DetParametrix.Paper41_Renorm.R322DetIntegrability
import Anderson4D.DetParametrix.Core.PrimitiveBlockPartition
import Anderson4D.DetParametrix.Core.ReductionPrimitive

/-!
# Closing the all-order R-322 reduction

This file contains the final multi-block interfaces for paper Section 4.1.
It starts with the concrete Definition 3.1 block schedule and the
generalized-input terminal primitive identity.  The subsequent section
iterates the exact block coordinates and connects their analytic collapse
to `RenormFiberReductionOutput`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The concrete extraction schedule is a complete partition -/

theorem extractionBlocksAux_forall_nonempty
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractionBlocksAux κ fuel active).Forall
        Finset.Nonempty := by
  induction fuel with
  | zero =>
      intro active
      simp
  | succ fuel ih =>
      intro active
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractionBlocksAux_succ_pos fuel h,
          List.forall_cons]
        constructor
        · exact
            ⟨(selectRel κ active h).1,
              (selectRel_isRelFullyPaired
                κ active h).left_mem_relIcc⟩
        · exact ih _
      · rw [extractionBlocksAux_succ_neg fuel h]
        simp

theorem extractionBlocks_forall_nonempty
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extractionBlocks κ).Forall Finset.Nonempty :=
  extractionBlocksAux_forall_nonempty
    κ m Finset.univ

/-- For a full pairing, its Definition 3.1 extraction list is a complete
partition by nonempty closed primitive blocks. -/
def extractionPrimitiveBlockPartition
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) :
    PrimitiveBlockPartition κ where
  blocks := extractionBlocks κ
  pairwise_disjoint :=
    extractionBlocks_pairwise_disjoint κ
  cover := by
    have hcover :=
      finsetUnionList_extractionBlocks_union_finalActive κ
    rw [finalActive_eq_empty_of_full hκ,
      Finset.union_empty] at hcover
    exact hcover
  nonempty :=
    extractionBlocks_forall_nonempty κ
  fullyPaired :=
    extractionBlocks_forall_isFullyPairedOn κ
  primitive :=
    extractionBlocks_forall_isRelPrimitiveOn κ

@[simp]
theorem extractionPrimitiveBlockPartition_blocks
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hκ : κ.IsFull) :
    (extractionPrimitiveBlockPartition κ hκ).blocks =
      extractionBlocks κ :=
  rfl

/-- Exact R-322 order ledger: the primitive block orders add to `q`. -/
theorem sum_extractionBlockOrders_of_full
    {q : ℕ} (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull) :
    ((extractionBlocks κ).map
      residualBlockOrder).sum = q := by
  have hledger :=
    (extractionPrimitiveBlockPartition κ hκ)
      |>.two_mul_sum_blockOrders
  simp only [
    extractionPrimitiveBlockPartition_blocks] at hledger
  omega

/-- Every concrete R-322 primitive block lies in the global perturbative
range. -/
theorem extractionBlockOrder_le_truncOrder
    {q : ℕ} (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ.IsFull)
    {B : Finset (Fin (2 * q))}
    (hB : B ∈ extractionBlocks κ)
    (ε : ℝ) (hq : q ≤ truncOrder ε) :
    residualBlockOrder B ≤ truncOrder ε := by
  have hpos :
      1 ≤ residualBlockOrder B :=
    (extractionPrimitiveBlockPartition κ hκ)
      |>.one_le_blockOrder hB
  have hmem :
      residualBlockOrder B ∈
        (extractionBlocks κ).map
          residualBlockOrder :=
    List.mem_map.mpr ⟨B, hB, rfl⟩
  have hsum :=
    List.single_le_sum
      (fun n _hn => Nat.zero_le n)
      _ hmem
  rw [sum_extractionBlockOrders_of_full κ hκ] at hsum
  omega

/-! ## Generalized-input terminal primitive identity -/

/-- A generalized closed `J` kernel.  Unlike `detJ`, its chain inputs are
an arbitrary family accepted by Proposition 4.1. -/
def detJWith
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (q : ℕ) (hq : 1 ≤ q)
    (G : Fin (2 * q - 1) → T4 → ℝ)
    (σ : PartialPairing (Fin (2 * q)))
    (z w : T4) : ℝ :=
  lamEps lam ε ^ (2 * q) *
    ∫ v : Fin (2 * q - 2) → T4,
      detJclosedIntegrandWith ρ ε (2 * q) σ G
        (primitiveAssemble q hq z w v)
      ∂(Measure.pi fun _ => paperMeasure)

/-- On a primitive full pairing, the terminal whole-interval replacement
is invalid and hence contributes `1`; the generalized closed `J` integrand
is exactly the Proposition 4.1 integrand. -/
theorem detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
    (ρ : SmoothCutoff) (ε : ℝ)
    (q : ℕ) (hq : 1 ≤ q)
    (G : Fin (2 * q - 1) → T4 → ℝ)
    (σ : PartialPairing (Fin (2 * q)))
    (hfull : σ.IsFull) (hprimitive : IsPrimitive σ)
    (x : Fin (2 * q) → T4) :
    detJclosedIntegrandWith ρ ε (2 * q) σ G x =
      primitiveIntegrand ρ ε q hq G σ x := by
  have hextract :
      extract σ =
        [((⟨0, by omega⟩ : Fin (2 * q)),
          (⟨2 * q - 1, by omega⟩ :
            Fin (2 * q)))] :=
    extract_eq_singleton_whole_of_pos_full_primitive
      (by omega) hfull hprimitive
  unfold detJclosedIntegrandWith
    primitiveIntegrand primitiveChainProduct
    primitiveCovarianceProduct
  rw [hextract]
  have hterminal :
      ¬(2 * q - 1) + 1 < 2 * q := by
    omega
  simp only [jReplacementList, hterminal,
    dite_false, List.map_nil, List.toFinset_nil,
    extractedJRightEdges, Finset.notMem_empty,
    if_false, List.prod_nil, mul_one]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro e _he
    unfold jChainEdgeWith
    rfl
  · rfl

/-- Exact terminal equality after summing the complete primitive pairing
coordinate. -/
theorem sum_detJWith_primitive_eq_primitiveKernel
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (q : ℕ) (hq : 1 ≤ q)
    (G : Fin (2 * q - 1) → T4 → ℝ)
    (z w : T4) :
    (∑ σ ∈ primitiveFullPairings q,
        detJWith ρ lam ε q hq G σ z w) =
      primitiveKernel ρ lam ε q hq G z w := by
  unfold detJWith primitiveKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp hσ
  apply congrArg
    (fun a : ℝ =>
      lamEps lam ε ^ (2 * q) * a)
  apply integral_congr_ae
  filter_upwards with v
  exact
    detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
      ρ ε q hq G σ hfull hprimitive
      (primitiveAssemble q hq z w v)

/-- The generalized kernel specializes exactly to the frozen `detJ`
kernel at the free Green family. -/
theorem detJWith_green_eq_detJ
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (q : ℕ) (hq : 1 ≤ q)
    (σ : PartialPairing (Fin (2 * q)))
    (z w : T4) :
    detJWith ρ lam ε q hq
        (fun _ => greenFn) σ z w =
      detJ ρ lam ε q σ z w := by
  cases q with
  | zero =>
      omega
  | succ q =>
      unfold detJWith detJ
      apply congrArg
        (fun a : ℝ =>
          lamEps lam ε ^ (2 * (q + 1)) * a)
      apply integral_congr_ae
      filter_upwards with v
      rw [
        detJclosedIntegrandWith_green_eq_detJintegrand]
      congr 1

end

end Anderson4D
