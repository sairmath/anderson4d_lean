import Anderson4D.DetParametrix.Paper41_Renorm.R322ActualFirstBlockClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticSchedule

/-!
# Spatial Fubini for an arbitrary analytic R-322 block

The paper-order schedule need not begin with the cardinality-first block of
the combinatorial extraction recursion.  The physical integral can nevertheless
put the coordinates of any certified analytic block on the inside.  This file
records that reindex directly for the original endpoint-fibre sum.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Exact signed Fubini form of the actual grouped kernel for an arbitrary
ambient block `B`.  No pairing sum is split and no absolute value is taken. -/
theorem endpointFiberDetJSum_eq_blockSpatialFubini
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (B : Finset (Fin (2 * q)))
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      lamEps lam ε ^ (2 * q) *
        ∫ vC :
            {i : Fin (2 * q - 2) //
              ¬r322SelectedFinPredicate
                (r322InternalCoordinatesOfBlock q hq B) i} → T4,
          ∫ vB :
              {i : Fin (2 * q - 2) //
                r322SelectedFinPredicate
                  (r322InternalCoordinatesOfBlock q hq B) i} → T4,
            ∑ τ : ReductionEndpointFiberAt κ,
              detJintegrand ρ ε q τ.1
                (primitiveAssemble q hq z 0
                  (r322MergeSelectedFinCoordinates
                    (r322InternalCoordinatesOfBlock q hq B)
                    vB vC))
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure := by
  rw [
    endpointFiberDetJSum_eq_integral_sum_detJintegrand
      ρ lam ε hq κ hκ z hint]
  apply congrArg
    (fun a : ℝ => lamEps lam ε ^ (2 * q) * a)
  apply
    integral_fin_pi_eq_integral_complement_integral_block_bochner
  exact integrable_finsetSum Finset.univ fun τ _hτ =>
    hint τ

/-- Schedule-step specialization of the arbitrary-block Fubini identity. -/
theorem endpointFiberDetJSum_eq_analyticStepSpatialFubini
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (step : R322ExtractionStep (2 * q))
    (_hstep : step ∈ r322AnalyticSchedule κ)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      lamEps lam ε ^ (2 * q) *
        ∫ vC :
            {i : Fin (2 * q - 2) //
              ¬r322SelectedFinPredicate
                (r322InternalCoordinatesOfBlock
                  q hq step.2) i} → T4,
          ∫ vB :
              {i : Fin (2 * q - 2) //
                r322SelectedFinPredicate
                  (r322InternalCoordinatesOfBlock
                    q hq step.2) i} → T4,
            ∑ τ : ReductionEndpointFiberAt κ,
              detJintegrand ρ ε q τ.1
                (primitiveAssemble q hq z 0
                  (r322MergeSelectedFinCoordinates
                    (r322InternalCoordinatesOfBlock
                      q hq step.2)
                    vB vC))
            ∂Measure.pi fun _ => paperMeasure
          ∂Measure.pi fun _ => paperMeasure :=
  endpointFiberDetJSum_eq_blockSpatialFubini
    ρ lam ε hq κ hκ step.2 z hint

end

end Anderson4D
