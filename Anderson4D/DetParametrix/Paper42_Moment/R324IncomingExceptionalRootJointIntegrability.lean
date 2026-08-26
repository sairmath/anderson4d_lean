import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalCrossProjection
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalTraceFourierBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedNonemptyRootEndpointBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFourierTermClosure

/-!
# Root joint integrability at an exceptional incoming stop

This module reindexes one genuine residual-refined physical fibre so that
the left initial residual is the last coordinate, while the remaining
endpoints and the right initial residual form the measured parameter of the
incoming-stop trace.  The already proved root integrability then supplies
the trace/Fourier bridge directly.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The three endpoints not integrated at the incoming stop, together with
the untouched right initial residual tuple. -/
abbrev R324IncomingExceptionalRootParameter
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κm : PartialPairing (Fin m)) :=
  (T4 × (T4 × T4)) ×
    ((R324WithinHalfResidualPrefix.initial
      ρ lam ε κm).SurvivingCoordinate → T4)

/-- Product Haar measure on the incoming-stop root parameter. -/
def r324IncomingExceptionalRootParameterMeasure
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κm : PartialPairing (Fin m)) :
    Measure
      (R324IncomingExceptionalRootParameter
        ρ lam ε κm) :=
  (paperMeasure.prod
    (paperMeasure.prod paperMeasure)).prod
      (Measure.pi fun _ :
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm).SurvivingCoordinate =>
            paperMeasure)

instance instSFiniteR324IncomingExceptionalRootParameterMeasure
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κm : PartialPairing (Fin m)) :
    SFinite
      (r324IncomingExceptionalRootParameterMeasure
        ρ lam ε κm) := by
  unfold r324IncomingExceptionalRootParameterMeasure
  infer_instance

/-- Root coordinates in the order expected by the exceptional-stop trace:
the incoming endpoint and measured parameter first, then the left initial
residual tuple. -/
abbrev R324IncomingExceptionalRootPoint
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m)) :=
  (T4 ×
      R324IncomingExceptionalRootParameter
        ρ lam ε κm) ×
    ((R324WithinHalfResidualPrefix.initial
      ρ lam ε κp).SurvivingCoordinate → T4)

/-- Reindex `(x,y,z,w,v)` as `((x,((y,z,w),vr)),vl)`, where the doubled
tuple `v` is split into the two literal initial sparse carriers. -/
def r324IncomingExceptionalRootMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m)) :
    R324PhysicalPoint m ≃ᵐ
      R324IncomingExceptionalRootPoint
        ρ lam ε κp κm :=
  let Left :=
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κp).SurvivingCoordinate → T4
  let Right :=
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κm).SurvivingCoordinate → T4
  let Rest := T4 × (T4 × T4)
  let Endpoint := T4 × Rest
  let splitInternal :=
    r324InitialTwoHalfProductPiMeasurableEquiv
      ρ lam ε κp κm
  let e₁ :
      R324PhysicalPoint m ≃ᵐ
        (Fin (2 * m) → T4) × Endpoint :=
    r324InternalFirstMeasurableEquiv m
  let e₂ :
      ((Fin (2 * m) → T4) × Endpoint) ≃ᵐ
        (Left × Right) × Endpoint :=
    MeasurableEquiv.prodCongr splitInternal.symm
      (MeasurableEquiv.refl Endpoint)
  let e₃ :
      (Left × Right) × Endpoint ≃ᵐ
        Endpoint × (Left × Right) :=
    MeasurableEquiv.prodComm
  let e₄ :
      Endpoint × (Left × Right) ≃ᵐ
        Left × (Endpoint × Right) :=
    r324MoveMiddleMeasurableEquiv Endpoint Left Right
  let e₅ :
      Left × (Endpoint × Right) ≃ᵐ
        (Endpoint × Right) × Left :=
    MeasurableEquiv.prodComm
  let e₆ :
      (Endpoint × Right) × Left ≃ᵐ
        (T4 × (Rest × Right)) × Left :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := Rest) (γ := Right))
      (MeasurableEquiv.refl Left)
  e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))

@[simp]
theorem r324IncomingExceptionalRootMeasurableEquiv_apply
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (q : R324PhysicalPoint m) :
    r324IncomingExceptionalRootMeasurableEquiv
        ρ lam ε κp κm q =
      ((q.1,
          ((q.2.1, (q.2.2.1, q.2.2.2.1)),
            (r324InitialTwoHalfProductPiMeasurableEquiv
              ρ lam ε κp κm).symm q.2.2.2.2 |>.2)),
        (r324InitialTwoHalfProductPiMeasurableEquiv
          ρ lam ε κp κm).symm q.2.2.2.2 |>.1) := by
  rfl

/-- The root reindexing preserves the exact product Haar measures. -/
theorem measurePreserving_r324IncomingExceptionalRootMeasurableEquiv
    (ρ : SmoothCutoff) (lam ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m)) :
    MeasurePreserving
      (r324IncomingExceptionalRootMeasurableEquiv
        ρ lam ε κp κm)
      (r324PhysicalMeasure m)
      ((paperMeasure.prod
          (r324IncomingExceptionalRootParameterMeasure
            ρ lam ε κm)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp).SurvivingCoordinate =>
              paperMeasure)) := by
  let Left :=
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κp).SurvivingCoordinate → T4
  let Right :=
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε κm).SurvivingCoordinate → T4
  let Rest := T4 × (T4 × T4)
  let Endpoint := T4 × Rest
  let μ : Measure T4 := paperMeasure
  let μLeft : Measure Left :=
    Measure.pi fun _ => paperMeasure
  let μRight : Measure Right :=
    Measure.pi fun _ => paperMeasure
  let μRest : Measure Rest :=
    μ.prod (μ.prod μ)
  let μEndpoint : Measure Endpoint :=
    μ.prod μRest
  let μInternal : Measure (Fin (2 * m) → T4) :=
    Measure.pi fun _ => paperMeasure
  let splitInternal :=
    r324InitialTwoHalfProductPiMeasurableEquiv
      ρ lam ε κp κm
  let e₁ :
      R324PhysicalPoint m ≃ᵐ
        (Fin (2 * m) → T4) × Endpoint :=
    r324InternalFirstMeasurableEquiv m
  let e₂ :
      ((Fin (2 * m) → T4) × Endpoint) ≃ᵐ
        (Left × Right) × Endpoint :=
    MeasurableEquiv.prodCongr splitInternal.symm
      (MeasurableEquiv.refl Endpoint)
  let e₃ :
      (Left × Right) × Endpoint ≃ᵐ
        Endpoint × (Left × Right) :=
    MeasurableEquiv.prodComm
  let e₄ :
      Endpoint × (Left × Right) ≃ᵐ
        Left × (Endpoint × Right) :=
    r324MoveMiddleMeasurableEquiv Endpoint Left Right
  let e₅ :
      Left × (Endpoint × Right) ≃ᵐ
        (Endpoint × Right) × Left :=
    MeasurableEquiv.prodComm
  let e₆ :
      (Endpoint × Right) × Left ≃ᵐ
        (T4 × (Rest × Right)) × Left :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := Rest) (γ := Right))
      (MeasurableEquiv.refl Left)
  have hp₁ :
      MeasurePreserving e₁
        (r324PhysicalMeasure m)
        (μInternal.prod μEndpoint) := by
    simpa only [e₁, μInternal, μEndpoint, μRest, μ,
      r324EndpointMeasure] using
      measurePreserving_r324InternalFirstMeasurableEquiv m
  have hp₂ :
      MeasurePreserving e₂
        (μInternal.prod μEndpoint)
        ((μLeft.prod μRight).prod μEndpoint) := by
    exact
      ((measurePreserving_r324InitialTwoHalfProductPiMeasurableEquiv
        ρ lam ε κp κm).symm.prod
          (MeasurePreserving.id μEndpoint))
  have hp₃ :
      MeasurePreserving e₃
        ((μLeft.prod μRight).prod μEndpoint)
        (μEndpoint.prod (μLeft.prod μRight)) :=
    Measure.measurePreserving_swap
  have hp₄ :
      MeasurePreserving e₄
        (μEndpoint.prod (μLeft.prod μRight))
        (μLeft.prod (μEndpoint.prod μRight)) :=
    measurePreserving_r324MoveMiddleMeasurableEquiv
      μEndpoint μLeft μRight
  have hp₅ :
      MeasurePreserving e₅
        (μLeft.prod (μEndpoint.prod μRight))
        ((μEndpoint.prod μRight).prod μLeft) :=
    Measure.measurePreserving_swap
  have hp₆ :
      MeasurePreserving e₆
        ((μEndpoint.prod μRight).prod μLeft)
        ((μ.prod (μRest.prod μRight)).prod μLeft) := by
    exact
      (measurePreserving_prodAssoc μ μRest μRight).prod
        (MeasurePreserving.id μLeft)
  change
    MeasurePreserving
      (e₁.trans
        (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆)))))
      (r324PhysicalMeasure m)
      ((μ.prod (μRest.prod μRight)).prod μLeft)
  exact hp₆.comp (hp₅.comp (hp₄.comp (hp₃.comp (hp₂.comp hp₁))))

namespace R324IncomingExceptionalStopTraceAssembly

/-- Remaining endpoint characters, the untouched right residual density,
and the cross-cut factor read after the retained left head. -/
def incomingExceptionalRefinedRootPostOuter
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω :
      R324IncomingExceptionalRootParameter
        ρ lam ε κm)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
          T4) : ℂ :=
  charT4 β ω.1.1 *
    charT4 (-α) ω.1.2.1 *
    charT4 (-β) ω.1.2.2 *
    (((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).residualIntegrand
      ρ ε ω.1.2.1 ω.1.2.2
      ((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).reconstruct ω.2) : ℂ) *
      (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq)
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm)
          (v, ω.2)) : ℂ))

/-- Under the exact root reindexing, the genuine refined physical density
is the initial source density consumed by the exceptional-stop trace. -/
theorem r324Flatten_momentRefinedPhysicalIntegrand_eq_initialSource_reindex
    (e₀ : MomentContraction m)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber m s r)
    (q : R324PhysicalPoint m) :
    r324Flatten
        (momentRefinedPhysicalIntegrand
          ρ ε m α β s r) q =
      data.incomingExceptionalInitialSourceDensity
        α
        (fun ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε e₀.2.1 =>
          ω.1.1)
        (data.incomingExceptionalRefinedRootPostOuter
          α β e₀.2.2)
        (r324IncomingExceptionalRootMeasurableEquiv
          ρ lam ε e₀.1 e₀.2.1 q) := by
  let splitInternal :=
    r324InitialTwoHalfProductPiMeasurableEquiv
      ρ lam ε e₀.1 e₀.2.1
  let halves := splitInternal.symm q.2.2.2.2
  have hroot :
      r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε e₀.1)
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε e₀.2.1)
          halves =
        q.2.2.2.2 := by
    calc
      _ = splitInternal halves := by
        exact
          (r324InitialTwoHalfProductPiMeasurableEquiv_apply
            ρ lam ε e₀.1 e₀.2.1 halves).symm
      _ = q.2.2.2.2 :=
        splitInternal.apply_symm_apply q.2.2.2.2
  have hleftCoordinates :
      (R324WithinHalfResidualPrefix.initial
          ρ lam ε e₀.1).reconstruct halves.1 =
        fun i => q.2.2.2.2 (leftMomentIndex i) := by
    funext i
    calc
      _ =
          r324TwoHalfRootDoubledReconstruct
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1)
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1)
            halves (leftMomentIndex i) := by
        rw [r324TwoHalfRootDoubledReconstruct,
          momentDoubleFinEquiv_symm_leftMomentIndex]
      _ = _ := congrFun hroot (leftMomentIndex i)
  have hrightCoordinates :
      (R324WithinHalfResidualPrefix.initial
          ρ lam ε e₀.2.1).reconstruct halves.2 =
        fun i => q.2.2.2.2 (rightMomentIndex i) := by
    funext i
    calc
      _ =
          r324TwoHalfRootDoubledReconstruct
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1)
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1)
            halves (rightMomentIndex i) := by
        rw [r324TwoHalfRootDoubledReconstruct,
          momentDoubleFinEquiv_symm_rightMomentIndex]
      _ = _ := congrFun hroot (rightMomentIndex i)
  unfold r324Flatten
  rw [
    momentRefinedPhysicalIntegrand_eq_twoInitialResiduals_mul_cross
      ρ lam ε m α β s r e₀ he₀
      q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2]
  change
    momentFourierPhase
        α β q.1 q.2.1 q.2.2.1 q.2.2.2.1 *
      ((R324WithinHalfResidualPrefix.initial
          ρ lam ε e₀.1).residualIntegrand
        ρ ε q.1 q.2.1
        (fun i => q.2.2.2.2 (leftMomentIndex i)) : ℂ) *
      ((R324WithinHalfResidualPrefix.initial
          ρ lam ε e₀.2.1).residualIntegrand
        ρ ε q.2.2.1 q.2.2.2.1
        (fun i => q.2.2.2.2 (rightMomentIndex i)) : ℂ) *
      (r324ResidualPrimitiveSumProduct
        ρ ε e₀.1 e₀.2.1 e₀.2.2 q.2.2.2.2 : ℂ) =
      _
  rw [← hleftCoordinates, ← hrightCoordinates, ← hroot]
  rw [
    data.r324ResidualPrimitiveSumProduct_eq_afterHeadProjection
      e₀.2.2 halves.1 halves.2]
  unfold incomingExceptionalInitialSourceDensity
    incomingExceptionalRefinedRootPostOuter
    momentFourierPhase
  simp only [
    r324IncomingExceptionalRootMeasurableEquiv_apply,
    splitInternal, halves]
  ring

/-- The genuine refined-root integrability theorem supplies exactly the
single `hcurrent` premise consumed by the exceptional trace/Fourier bridge. -/
theorem integrable_incomingExceptionalRefinedInitialSource
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K)
        e₀.1
        initialScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    Integrable
      (data.incomingExceptionalInitialSourceDensity
        α
        (fun ω :
            R324IncomingExceptionalRootParameter
              ρ lam ε
                e₀.2.1 =>
          ω.1.1)
        (data.incomingExceptionalRefinedRootPostOuter
          α β
          e₀.2.2))
      ((paperMeasure.prod
          (r324IncomingExceptionalRootParameterMeasure
            ρ lam ε
              e₀.2.1)).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε
              e₀.1)
              |>.SurvivingCoordinate =>
                paperMeasure)) := by
  let e :=
    r324IncomingExceptionalRootMeasurableEquiv
      ρ lam ε e₀.1 e₀.2.1
  let target :=
    data.incomingExceptionalInitialSourceDensity
      α
      (fun ω :
          R324IncomingExceptionalRootParameter
            ρ lam ε e₀.2.1 =>
        ω.1.1)
      (data.incomingExceptionalRefinedRootPostOuter
        α β e₀.2.2)
  have hsource :=
    integrable_r324RefinedPhysicalIntegrand
      ρ hε hε1 α β p
  have hcomp :
      Integrable (target ∘ e)
        (r324PhysicalMeasure m) := by
    convert hsource using 1
    funext q
    exact
      (data.r324Flatten_momentRefinedPhysicalIntegrand_eq_initialSource_reindex
        e₀ α β p.1.1 p.2.1
        he₀ q).symm
  exact
    (measurePreserving_r324IncomingExceptionalRootMeasurableEquiv
      ρ lam ε e₀.1 e₀.2.1).integrable_comp_emb
        e.measurableEmbedding |>.mp hcomp

/-- Root integrability is discharged internally before the certified left
trace and incoming-endpoint Fourier evaluation are composed.  Callers supply
only the realized refined representative and its fibre membership; there is
no residual `hcurrent` or Fubini premise. -/
theorem
    lamEps_pow_integral_refinedInitialSource_eq_incomingExceptionalStopFourier
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber
        m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        (∫ q,
          data.incomingExceptionalInitialSourceDensity
            α
            (fun ω :
                R324IncomingExceptionalRootParameter
                  ρ lam ε e₀.2.1 =>
              ω.1.1)
            (data.incomingExceptionalRefinedRootPostOuter
              α β e₀.2.2) q
          ∂((paperMeasure.prod
              (r324IncomingExceptionalRootParameterMeasure
                ρ lam ε e₀.2.1)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε e₀.1).SurvivingCoordinate =>
                  paperMeasure))) =
      (lamEps lam ε : ℂ) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ q,
          data.incomingExceptionalStopFourierDensity
            α
            (fun ω :
                R324IncomingExceptionalRootParameter
                  ρ lam ε e₀.2.1 =>
              ω.1.1)
            (data.incomingExceptionalRefinedRootPostOuter
              α β e₀.2.2) q
          ∂((r324IncomingExceptionalRootParameterMeasure
              ρ lam ε e₀.2.1).prod
            ((Measure.pi fun _ :
                Fin (2 *
                  residualBlockOrder data.terminal.2) =>
                    paperMeasure).prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure)))) := by
  exact
    data.lamEps_pow_integral_initialResidual_eq_incomingExceptionalStopFourier
      (r324IncomingExceptionalRootParameterMeasure
        ρ lam ε e₀.2.1)
      hm α
      (fun ω :
          R324IncomingExceptionalRootParameter
            ρ lam ε e₀.2.1 =>
        ω.1.1)
      (data.incomingExceptionalRefinedRootPostOuter
        α β e₀.2.2)
      (data.integrable_incomingExceptionalRefinedInitialSource
        p e₀ he₀ hε hε1 α β)

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
