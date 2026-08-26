import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossQuantitativeStep
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualPrimitiveCoordinateExpansion

/-!
# Complete primitive sum at one residual R-324 head

Paper §4.2 Step 3 applies Proposition 4.1 to the complete primitive-pairing
sum carried by the current cross block.  This file keeps that finite sum
inside one head update.  In particular, it does not apply the proposition
term by term and introduces no pairing-cardinality loss.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-! ## The complete signed head sum -/

/-- The moving central-gap numerator multiplying the complete primitive
pairing sum at the current head.  The sum is retained before any norm or
Proposition 4.1 estimate is taken. -/
def completeCrossGapPrimitiveIntegrand
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (x : Fin (2 * ctx.order) → T4) : ℝ :=
  ∑ κ ∈ primitiveFullPairings ctx.order,
    torusDistSq
        (x ctx.leftGapIndex - x ctx.rightGapIndex) *
      primitiveIntegrand
        ρ ε ctx.order ctx.one_le_order G κ x

/-- The complete current-head contribution, with the exact coupling power.
This is one finite primitive sum, not a sum of separately estimated
Proposition 4.1 majorants. -/
def completeCrossGapPrimitiveTerm
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (z w : T4) : ℝ :=
  lamEps lam ε ^ (2 * ctx.order) *
    ∑ κ ∈ primitiveFullPairings ctx.order,
      ∫ v : Fin (2 * ctx.order - 2) → T4,
        torusDistSq
            (primitiveAssemble
                ctx.order ctx.one_le_order z w v
                ctx.leftGapIndex -
              primitiveAssemble
                ctx.order ctx.one_le_order z w v
                ctx.rightGapIndex) *
          primitiveIntegrand
            ρ ε ctx.order ctx.one_le_order G κ
            (primitiveAssemble
              ctx.order ctx.one_le_order z w v)
        ∂(Measure.pi fun _ => paperMeasure)

/-- Algebraic normal form exposing one complete covariance sum. -/
theorem completeCrossGapPrimitiveIntegrand_eq
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (x : Fin (2 * ctx.order) → T4) :
    ctx.completeCrossGapPrimitiveIntegrand ρ ε G x =
      torusDistSq
          (x ctx.leftGapIndex - x ctx.rightGapIndex) *
        primitiveChainProduct
          ctx.order ctx.one_le_order G x *
        ∑ κ ∈ primitiveFullPairings ctx.order,
          primitiveCovarianceProduct
            ρ ε ctx.order κ x := by
  unfold completeCrossGapPrimitiveIntegrand primitiveIntegrand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  ring

/-! ## Transport of the actual residual block factor -/

/-- The complete physical block sum on the literal current residual head,
after the proved head/post coordinate split, is exactly the complete
primitive covariance sum on canonical head coordinates. -/
theorem r324PrimitivePartitionBlockSum_head_reconstruct_split
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (t : Fin (2 * ctx.order) → T4)
    (v : ctx.PostCoordinate → T4) :
    r324PrimitivePartitionBlockSum
        ρ ε κp κm π ctx.head.carrier
        (ctx.reconstruct
          (ctx.splitSurvivingPiMeasurableEquiv.symm (t, v))) =
      ∑ σ : R324PrimitiveCoordinate ctx.order,
        primitiveCovarianceProduct
          ρ ε ctx.order σ.1 t := by
  let B : R324ResidualPrimitiveBlockIndex κp κm π :=
    ⟨ctx.head.carrier, ctx.head.mem_schedule⟩
  let hB :
      ctx.head.carrier ∈
        (momentPrimitiveBlockPartition κp κm π).blocks :=
    r324ResidualPrimitiveBlock_mem_partition κp κm π B
  rw [r324PrimitivePartitionBlockSum_of_mem
    ρ ε κp κm π ctx.head.carrier hB]
  apply Fintype.sum_congr
  intro σ
  unfold primitivePartitionBlockCovarianceFactor
  have hiso :
      residualPrimitiveBlockOrderIso
          (momentCombinedPairing κp κm π)
          ctx.head.carrier
          ((momentPrimitiveBlockPartition
            κp κm π).block_fullyPaired hB) =
        ctx.blockOrderIso := by
    unfold blockOrderIso
    congr
  rw [hiso]
  congr 1
  funext i
  exact ctx.reconstruct_split_symm_block t v i

/-- Fintype coordinates and the paper's filtered primitive-pairing sum are
the same complete finite family. -/
theorem sum_r324PrimitiveCoordinate_covariance_eq
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (t : Fin (2 * ctx.order) → T4) :
    (∑ σ : R324PrimitiveCoordinate ctx.order,
        primitiveCovarianceProduct
          ρ ε ctx.order σ.1 t) =
      ∑ κ ∈ primitiveFullPairings ctx.order,
        primitiveCovarianceProduct
          ρ ε ctx.order κ t := by
  symm
  rw [← Finset.sum_attach]
  rw [Finset.attach_eq_univ]

/-- Direct exact bridge from the literal physical head factor to the
complete central-gap primitive integrand. -/
theorem headGapChainBlockSum_eq_completeCrossGapPrimitiveIntegrand
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (t : Fin (2 * ctx.order) → T4)
    (v : ctx.PostCoordinate → T4) :
    torusDistSq
        (t ctx.leftGapIndex - t ctx.rightGapIndex) *
      primitiveChainProduct
        ctx.order ctx.one_le_order G t *
      r324PrimitivePartitionBlockSum
        ρ ε κp κm π ctx.head.carrier
        (ctx.reconstruct
          (ctx.splitSurvivingPiMeasurableEquiv.symm (t, v))) =
      ctx.completeCrossGapPrimitiveIntegrand ρ ε G t := by
  rw [ctx.completeCrossGapPrimitiveIntegrand_eq,
    ctx.r324PrimitivePartitionBlockSum_head_reconstruct_split,
    ctx.sum_r324PrimitiveCoordinate_covariance_eq]

/-! ## One application of the complete inserted kernel -/

/-- Pointwise, the complete moving-gap sum is bounded by the complete
inserted primitive sum.  No primitive-pairing term is estimated
individually by Proposition 4.1. -/
theorem completeCrossGapPrimitiveIntegrand_le_insertedSum
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z)
    (x : Fin (2 * ctx.order) → T4) :
    ctx.completeCrossGapPrimitiveIntegrand ρ ε G x ≤
      ∑ κ ∈ primitiveFullPairings ctx.order,
        primitiveInsertedIntegrand
          ρ ε ctx.order ctx.one_le_order G κ x := by
  unfold completeCrossGapPrimitiveIntegrand
  apply Finset.sum_le_sum
  intro κ hκ
  have hcard : 0 < 2 * ctx.order := by
    have horder := ctx.one_le_order
    omega
  letI : Nonempty (Fin (2 * ctx.order)) :=
    ⟨⟨0, hcard⟩⟩
  have hgap :
      torusDistSq
          (x ctx.leftGapIndex - x ctx.rightGapIndex) ≤
        ε ^ 2 + torusTupleDiameterSq x :=
    (torusDistSq_sub_le_torusTupleDiameterSq
      x ctx.leftGapIndex ctx.rightGapIndex).trans
      (le_add_of_nonneg_left (sq_nonneg ε))
  unfold primitiveInsertedIntegrand
  exact mul_le_mul_of_nonneg_right hgap
    (primitiveIntegrand_nonneg
      ρ ε ctx.order ctx.one_le_order G hG κ x)

/-! The following two lemmas provide integrability uniformly over the
complete primitive family.  They are deliberately parameterized by
membership rather than by `ctx.blockPairing`. -/

theorem integrable_primitiveIntegrand_blockAssemble_of_mem
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (κ : PartialPairing (Fin (2 * ctx.order)))
    (hκ : κ ∈ primitiveFullPairings ctx.order)
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * ctx.order - 2) → T4 =>
        primitiveIntegrand
          ρ ε ctx.order ctx.one_le_order G κ
          (primitiveAssemble
            ctx.order ctx.one_le_order z w v))
      (Measure.pi fun _ => paperMeasure) := by
  apply
    integrable_primitiveIntegrand_assemble_of_scaled_offDiagonal
      ρ hε hε1 ctx.one_le_order G
        (fun _ => 1) hGmeas
        (fun _ => zero_lt_one)
        hinput.1
        (fun j u _hu => by
          simpa only [one_mul] using hinput.2 j u)
        ⟨κ, hκ⟩ z w

theorem integrable_primitiveInsertedIntegrand_blockAssemble_of_mem
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (κ : PartialPairing (Fin (2 * ctx.order)))
    (hκ : κ ∈ primitiveFullPairings ctx.order)
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * ctx.order - 2) → T4 =>
        primitiveInsertedIntegrand
          ρ ε ctx.order ctx.one_le_order G κ
          (primitiveAssemble
            ctx.order ctx.one_le_order z w v))
      (Measure.pi fun _ => paperMeasure) := by
  have hcard : 0 < 2 * ctx.order := by
    have horder := ctx.one_le_order
    omega
  letI : Nonempty (Fin (2 * ctx.order)) :=
    ⟨⟨0, hcard⟩⟩
  let assemble :=
    fun v : Fin (2 * ctx.order - 2) → T4 =>
      primitiveAssemble
        ctx.order ctx.one_le_order z w v
  have hassemble : Measurable assemble :=
    measurable_primitiveAssemble
      ctx.order ctx.one_le_order z w
  have hdiamMeas :
      Measurable fun v =>
        ε ^ 2 + torusTupleDiameterSq (assemble v) :=
    measurable_const.add
      (measurable_r324TorusTupleDiameterSq
        assemble fun i =>
          (measurable_pi_apply i).comp hassemble)
  have hdiamBound :
      ∀ᵐ v ∂(Measure.pi fun _ :
          Fin (2 * ctx.order - 2) => paperMeasure),
        ‖ε ^ 2 + torusTupleDiameterSq (assemble v)‖ ≤
          ε ^ 2 + 4 * Real.pi ^ 2 := by
    filter_upwards with v
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (add_nonneg (sq_nonneg ε)
          (torusTupleDiameterSq_nonneg (assemble v)))]
    exact add_le_add (le_refl _)
      (r324TorusTupleDiameterSq_le_four_pi_sq
        (assemble v))
  have hordinary :=
    ctx.integrable_primitiveIntegrand_blockAssemble_of_mem
      ρ hε hε1 G hGmeas hinput κ hκ z w
  have hmul :=
    hordinary.bdd_mul hdiamMeas.aestronglyMeasurable
      hdiamBound
  simpa only [assemble, primitiveInsertedIntegrand] using hmul

theorem integrable_completeCrossGapSummand_blockAssemble_of_mem
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (κ : PartialPairing (Fin (2 * ctx.order)))
    (hκ : κ ∈ primitiveFullPairings ctx.order)
    (z w : T4) :
    Integrable
      (fun v : Fin (2 * ctx.order - 2) → T4 =>
        torusDistSq
            (primitiveAssemble
                ctx.order ctx.one_le_order z w v
                ctx.leftGapIndex -
              primitiveAssemble
                ctx.order ctx.one_le_order z w v
                ctx.rightGapIndex) *
          primitiveIntegrand
            ρ ε ctx.order ctx.one_le_order G κ
            (primitiveAssemble
              ctx.order ctx.one_le_order z w v))
      (Measure.pi fun _ => paperMeasure) := by
  let assemble :=
    fun v : Fin (2 * ctx.order - 2) → T4 =>
      primitiveAssemble
        ctx.order ctx.one_le_order z w v
  have hassemble : Measurable assemble :=
    measurable_primitiveAssemble
      ctx.order ctx.one_le_order z w
  have hgapMeas :
      Measurable fun v =>
        torusDistSq
          (assemble v ctx.leftGapIndex -
            assemble v ctx.rightGapIndex) :=
    measurable_torusDistSq.comp
      (((measurable_pi_apply ctx.leftGapIndex).comp
        hassemble).sub
      ((measurable_pi_apply ctx.rightGapIndex).comp
        hassemble))
  have hgapBound :
      ∀ᵐ v ∂(Measure.pi fun _ :
          Fin (2 * ctx.order - 2) => paperMeasure),
        ‖torusDistSq
          (assemble v ctx.leftGapIndex -
            assemble v ctx.rightGapIndex)‖ ≤
          4 * Real.pi ^ 2 := by
    filter_upwards with v
    rw [Real.norm_eq_abs,
      abs_of_nonneg (torusDistSq_nonneg _)]
    exact torusDistSq_le _
  have hordinary :=
    ctx.integrable_primitiveIntegrand_blockAssemble_of_mem
      ρ hε hε1 G hGmeas hinput κ hκ z w
  have hmul :=
    hordinary.bdd_mul hgapMeas.aestronglyMeasurable
      hgapBound
  simpa only [assemble] using hmul

/-- The sum-of-integrals presentation of the complete term is exactly the
integral of the complete pointwise primitive sum. -/
theorem completeCrossGapPrimitiveTerm_eq_integral
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (z w : T4) :
    ctx.completeCrossGapPrimitiveTerm ρ lam ε G z w =
      lamEps lam ε ^ (2 * ctx.order) *
        ∫ v : Fin (2 * ctx.order - 2) → T4,
          ctx.completeCrossGapPrimitiveIntegrand ρ ε G
            (primitiveAssemble
              ctx.order ctx.one_le_order z w v)
          ∂(Measure.pi fun _ => paperMeasure) := by
  unfold completeCrossGapPrimitiveTerm
    completeCrossGapPrimitiveIntegrand
  rw [integral_finsetSum
    (primitiveFullPairings ctx.order)
    (fun κ hκ =>
      ctx.integrable_completeCrossGapSummand_blockAssemble_of_mem
        ρ hε hε1 G hGmeas hinput κ hκ z w)]

/-- The complete moving-gap head is bounded by a single complete inserted
kernel.  This is the precise bridge needed before invoking Proposition 4.1;
there is no factor counting primitive pairings. -/
theorem completeCrossGapPrimitiveTerm_le_primitiveKernelInserted
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : Fin (2 * ctx.order - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hinput : IsAdmissiblePrimitiveInput ctx.order G)
    (hG : ∀ j z, 0 ≤ G j z)
    (z w : T4) :
    ctx.completeCrossGapPrimitiveTerm ρ lam ε G z w ≤
      primitiveKernelInserted
        ρ lam ε ctx.order ctx.one_le_order G z w := by
  unfold completeCrossGapPrimitiveTerm primitiveKernelInserted
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro κ hκ
    apply integral_mono
    · exact
        ctx.integrable_completeCrossGapSummand_blockAssemble_of_mem
          ρ hε hε1 G hGmeas hinput κ hκ z w
    · exact
        ctx.integrable_primitiveInsertedIntegrand_blockAssemble_of_mem
          ρ hε hε1 G hGmeas hinput κ hκ z w
    · intro v
      have hcard : 0 < 2 * ctx.order := by
        have horder := ctx.one_le_order
        omega
      letI : Nonempty (Fin (2 * ctx.order)) :=
        ⟨⟨0, hcard⟩⟩
      let x :=
        primitiveAssemble
          ctx.order ctx.one_le_order z w v
      have hgap :
          torusDistSq
              (x ctx.leftGapIndex -
                x ctx.rightGapIndex) ≤
            ε ^ 2 + torusTupleDiameterSq x :=
        (torusDistSq_sub_le_torusTupleDiameterSq
          x ctx.leftGapIndex ctx.rightGapIndex).trans
          (le_add_of_nonneg_left (sq_nonneg ε))
      unfold primitiveInsertedIntegrand
      exact mul_le_mul_of_nonneg_right hgap
        (primitiveIntegrand_nonneg
          ρ ε ctx.order ctx.one_le_order G hG κ x)
  · exact (even_two_mul ctx.order).pow_nonneg _

end R324NestedCrossStepContext

end

end Anderson4D
