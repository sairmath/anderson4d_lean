import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfProcessedIntegrand

/-! # Outer Fubini for one processed R-324 within-half step

An arbitrary fixed outer factor passes through the current block integral.
The almost-everywhere wrapper then performs the exact outer-measure
substitution from the raw local factor to the absorbed predecessor edge.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfStepContext

variable {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)

/-- One processed inner integral may carry any fixed outer factor. -/
theorem rawLocalSpatialIntegral_mul_outer_eq_absorb
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : T4) (outer : ℝ)
    (hstandard :
      Integrable (ctx.localIntegrand ρ ε u)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder ctx.step.2) *
        (∫ t : Fin (2 * residualBlockOrder ctx.step.2) → T4,
          ctx.rawLocalIntegrand ρ ε u t * outer
          ∂Measure.pi fun _ => paperMeasure) =
      (ctx.absorb ρ lam ε).edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) u * outer := by
  simp_rw [ctx.rawLocalIntegrand_eq_localIntegrand]
  rw [integral_mul_const, ← mul_assoc]
  change
    ctx.localSpatialIntegral ρ lam ε u * outer =
      (ctx.absorb ρ lam ε).edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) u * outer
  rw [ctx.localSpatialIntegral_eq_absorb_predecessor
    ρ lam ε u hstandard hinternal]

/-- Exact outer-Fubini substitution for a genuine processed step.
Section integrability is required only almost everywhere in the actual
outer coordinate. -/
theorem integral_outer_rawLocalIntegrand_eq_absorb
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : Ω → T4) (outer : Ω → ℝ)
    (hstandard :
      ∀ᵐ ω ∂ν,
        Integrable (ctx.localIntegrand ρ ε (u ω))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    (∫ ω,
        lamEps lam ε ^
            (2 * residualBlockOrder ctx.step.2) *
          (∫ t :
              Fin (2 * residualBlockOrder ctx.step.2) → T4,
            ctx.rawLocalIntegrand ρ ε (u ω) t *
              outer ω
            ∂Measure.pi fun _ => paperMeasure)
        ∂ν) =
      ∫ ω,
        (ctx.absorb ρ lam ε).edges
            (r324WithinHalfPredecessorSlot
              ctx.state ctx.step) (u ω) *
          outer ω
        ∂ν := by
  apply integral_congr_ae
  filter_upwards [hstandard] with ω hω
  exact ctx.rawLocalSpatialIntegral_mul_outer_eq_absorb
    ρ lam ε (u ω) (outer ω) hω hinternal

end R324WithinHalfStepContext

end

end Anderson4D
