import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointMajorantClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFiber
import Anderson4D.Continuum.PrimitiveMajorantIntegral

/-!
# Integrated primitive-iteration boundary for R-324

Paper Section 4.2 does not bound a pointwise physical density.  Step 2
successively removes the within-half primitive intervals while the physical
integrand is signed; Step 3 then integrates the endpoints in the uniform
branch and continues with the relative cross-cut primitive blocks.
Accordingly, the correct cancellation-preserving output of the complete
block iteration is a scalar bound for each residual-refined fibre.

This file supplies the cancellation-preserving downstream API and proves all
finite regrouping steps.  Its analytic input is the successive primitive-block
collapse for one residual-refined fibre; no pointwise domination of
`momentSignaturePhysicalDensity` appears.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The actual integrated refined fibres -/

/-- The already-integrated deterministic contribution of one complete
residual-refined contraction fibre. -/
def momentRefinedDeterministicTermSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))) : ℂ :=
  ∑ e ∈ momentRefinedContractionFiber m s r,
    deterministicMomentContractionTerm ρ ε m α β e

/-- Exact regrouping of one fixed-signature deterministic contribution by
the realized residual schedules. -/
theorem sum_momentRefinedDeterministicTermSum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    (∑ r ∈ momentResidualChainSignaturesAt m s,
        momentRefinedDeterministicTermSum
          ρ ε m α β s r) =
      ∑ e ∈ momentContractionFiber m s,
        deterministicMomentContractionTerm ρ ε m α β e := by
  unfold momentRefinedDeterministicTermSum
  exact
    sum_momentContractionFiber_by_residualChainSignature
      s (deterministicMomentContractionTerm ρ ε m α β)

/-- Correct analytic output of the successive block iteration: after the
external integrations, one complete residual-refined fibre is bounded by
the integral of the inserted Proposition 4.1 majorant. -/
structure MomentRefinedIntegratedReductionData
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) where
  refined_bound :
    ∀ s ∈ momentContractionSignatures m,
      ∀ r ∈ momentResidualChainSignaturesAt m s,
        |lamEps lam ε| ^ (2 * m) *
            ‖momentRefinedDeterministicTermSum
              ρ ε m α β s r‖ ≤
          ∫ z,
            primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant m z
            ∂paperMeasure

/-- Per-signature integrated output after summing the residual schedules.
This scalar statement matches the integration order in paper Section 4.2 Step 3. -/
structure MomentIntegratedFiberReductionData
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) where
  fiber_bound :
    ∀ s ∈ momentContractionSignatures m,
      |lamEps lam ε| ^ (2 * m) *
          ‖∑ e ∈ momentContractionFiber m s,
            deterministicMomentContractionTerm
              ρ ε m α β e‖ ≤
        ∫ z,
          primitiveInsertedMajorant
            primitiveConstant lam ε supportConstant m z
          ∂paperMeasure

/-- Scaling the primitive constant by `a` scales either majorant by
`a^(2m)`. -/
theorem primitiveInsertedMajorant_mul_constant
    (a C lam ε supportConstant : ℝ) (m : ℕ) (z : T4) :
    primitiveInsertedMajorant
        (a * C) lam ε supportConstant m z =
      a ^ (2 * m) *
        primitiveInsertedMajorant
          C lam ε supportConstant m z := by
  unfold primitiveInsertedMajorant
  rw [show (a * C) * lam =
      a * (C * lam) by ring, mul_pow]
  ring

/-- Sum the independent residual-refined estimates.  The exact
`4^(2m)` schedule count is absorbed by `C ↦ 4C`; no factorial loss is
introduced. -/
theorem MomentRefinedIntegratedReductionData.toIntegratedFiberReductionData
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (d : MomentRefinedIntegratedReductionData
      ρ lam ε m α β primitiveConstant supportConstant) :
    MomentIntegratedFiberReductionData
      ρ lam ε m α β
        (4 * primitiveConstant) supportConstant := by
  let I : ℝ :=
    ∫ z,
      primitiveInsertedMajorant
        primitiveConstant lam ε supportConstant m z
      ∂paperMeasure
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hC hlam
  refine ⟨?_⟩
  intro s hs
  have hsum :=
    sum_momentRefinedDeterministicTermSum
      ρ ε m α β s
  calc
    |lamEps lam ε| ^ (2 * m) *
          ‖∑ e ∈ momentContractionFiber m s,
            deterministicMomentContractionTerm
              ρ ε m α β e‖ =
        |lamEps lam ε| ^ (2 * m) *
          ‖∑ r ∈ momentResidualChainSignaturesAt m s,
            momentRefinedDeterministicTermSum
              ρ ε m α β s r‖ := by
      rw [hsum]
    _ ≤
        |lamEps lam ε| ^ (2 * m) *
          ∑ r ∈ momentResidualChainSignaturesAt m s,
            ‖momentRefinedDeterministicTermSum
              ρ ε m α β s r‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_sum_le _ _) (pow_nonneg (abs_nonneg _) _)
    _ =
        ∑ r ∈ momentResidualChainSignaturesAt m s,
          |lamEps lam ε| ^ (2 * m) *
            ‖momentRefinedDeterministicTermSum
              ρ ε m α β s r‖ := by
      rw [Finset.mul_sum]
    _ ≤
        ∑ _r ∈ momentResidualChainSignaturesAt m s, I := by
      apply Finset.sum_le_sum
      intro r hr
      exact d.refined_bound s hs r hr
    _ =
        ((momentResidualChainSignaturesAt m s).card : ℝ) * I := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * m) * I := by
      exact mul_le_mul_of_nonneg_right
        (by
          exact_mod_cast
            card_momentResidualChainSignaturesAt_le m s)
        hI
    _ =
        ∫ z,
          primitiveInsertedMajorant
            (4 * primitiveConstant) lam ε
              supportConstant m z
          ∂paperMeasure := by
      dsimp only [I]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      exact
        (primitiveInsertedMajorant_mul_constant
          4 primitiveConstant lam ε
            supportConstant m z).symm

/-- Existence wrapper for the corrected fixed-signature output. -/
def MomentIntegratedFiberReductionOutputAt
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  Nonempty
    (MomentIntegratedFiberReductionData
      ρ lam ε m α β primitiveConstant supportConstant)

/-- Existence wrapper for the corrected residual-refined output. -/
def MomentRefinedIntegratedReductionOutputAt
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (α β : Z4)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  Nonempty
    (MomentRefinedIntegratedReductionData
      ρ lam ε m α β primitiveConstant supportConstant)

theorem
    MomentRefinedIntegratedReductionOutputAt.toIntegratedFiberReductionOutputAt
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (h :
      MomentRefinedIntegratedReductionOutputAt
        ρ lam ε m α β primitiveConstant supportConstant) :
    MomentIntegratedFiberReductionOutputAt
      ρ lam ε m α β
        (4 * primitiveConstant) supportConstant := by
  obtain ⟨d⟩ := h
  exact
    ⟨d.toIntegratedFiberReductionData hC hlam⟩

/-! ## Direct uniform bound without the false pointwise density -/

/-- Summing the fixed-signature scalar estimates costs the second exact
`4^(2m)` factor, absorbed once more into the named primitive constant. -/
theorem deterministicMomentPairingSum_le_integral_insertedMajorant_of_integrated
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (hred :
      MomentIntegratedFiberReductionOutputAt
        ρ lam ε m α β primitiveConstant supportConstant) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      ∫ z,
        primitiveInsertedMajorant
          (4 * primitiveConstant) lam ε
            supportConstant m z
        ∂paperMeasure := by
  obtain ⟨d⟩ := hred
  let I : ℝ :=
    ∫ z,
      primitiveInsertedMajorant
        primitiveConstant lam ε supportConstant m z
      ∂paperMeasure
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg hC hlam
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          groupedDeterministicMomentTermNormSum
            ρ ε m α β :=
      deterministicMomentPairingSum_le_groupedSignatures
        ρ lam ε m α β
    _ =
        ∑ s ∈ momentContractionSignatures m,
          |lamEps lam ε| ^ (2 * m) *
            ‖∑ e ∈ momentContractionFiber m s,
              deterministicMomentContractionTerm
                ρ ε m α β e‖ := by
      unfold groupedDeterministicMomentTermNormSum
      rw [Finset.mul_sum]
      rfl
    _ ≤
        ∑ _s ∈ momentContractionSignatures m, I := by
      apply Finset.sum_le_sum
      intro s hs
      exact d.fiber_bound s hs
    _ =
        ((momentContractionSignatures m).card : ℝ) * I := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * m) * I := by
      exact mul_le_mul_of_nonneg_right
        (by
          exact_mod_cast
            card_momentContractionSignatures_le m)
        hI
    _ =
        ∫ z,
          primitiveInsertedMajorant
            (4 * primitiveConstant) lam ε
              supportConstant m z
          ∂paperMeasure := by
      dsimp only [I]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      exact
        (primitiveInsertedMajorant_mul_constant
          4 primitiveConstant lam ε
            supportConstant m z).symm

/-- Direct composition from residual-refined scalar collapse to the global
uniform deterministic moment bound.  The two exponential schedule counts
are visible as `C ↦ 16C`. -/
theorem deterministicMomentPairingSum_le_integral_insertedMajorant_of_refined
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (hred :
      MomentRefinedIntegratedReductionOutputAt
        ρ lam ε m α β primitiveConstant supportConstant) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      ∫ z,
        primitiveInsertedMajorant
          (16 * primitiveConstant) lam ε
            supportConstant m z
        ∂paperMeasure := by
  have hfiber :=
    hred.toIntegratedFiberReductionOutputAt hC hlam
  have hbound :=
    deterministicMomentPairingSum_le_integral_insertedMajorant_of_integrated
      (mul_nonneg (by norm_num) hC) hlam hfiber
  simpa only [show
      4 * (4 * primitiveConstant) =
        16 * primitiveConstant by ring] using hbound

end

end Anderson4D
