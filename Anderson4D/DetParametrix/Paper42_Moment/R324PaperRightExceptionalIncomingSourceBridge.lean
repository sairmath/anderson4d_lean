import Anderson4D.DetParametrix.Paper42_Moment.R324PaperActualEndpointCollapse

/-!
# The right exceptional-incoming source after the completed left half

This is the product-measure reassociation used between the two halves in
paper Step 4(A) when the right incoming endpoint is exceptional.  The
completed signed left density is kept as one untouched coefficient of the
right initial residual density.  No absolute value, endpoint estimate, or
new summation occurs here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {alpha : Z4}
    {leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}

namespace R324PaperHalfEndpointUniformBound

/-- The completed left half, still signed, as the post-stop coefficient of
the exceptional right incoming endpoint.  The right post-stop carrier is
deliberately abstract: the concrete `ED` and `EE` routes supply respectively
their alternating-transport and outgoing-terminal projections. -/
def rightExceptionalPostOuter
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (beta : Z4)
    {rightScale : Fin (m + 1) -> Real}
    (rightData : R324IncomingExceptionalStopTraceAssembly
      (ρ := rho) (C := C) (lam := lam) (ε := eps)
      (K := K) kappaM rightScale)
    (projectedCoefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        ((rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq).SurvivingCoordinate ->
            T4) -> Complex)
    (omega : T4 × (left.carrier.SurvivingCoordinate -> T4))
    (post :
      (rightData.trace.stopPrefix.afterHead
        rightData.terminal rightData.suffix
        rightData.trace.stopPrefix_remaining_eq).SurvivingCoordinate -> T4) :
    Complex :=
  charT4 (-beta) omega.1 *
    left.density (fun v => projectedCoefficient v post) beta omega.2

/-- The paper's exact right-incoming regroup for an arbitrary completed
left endpoint route.

`hlinear` is the literal scalar linearity of the completed left density;
the four canonical constructors prove it by their already established
pointwise formulas.  `hproject` is only the existing coordinate identity
which reads the primitive cross factor on the right post-stop carrier.
Thus the conclusion supplies precisely the source integrability and source
equality consumed by both right `ED` and right `EE` transforms, before any
norm is taken. -/
theorem
    integrable_and_integral_completedLeft_eq_rightExceptionalInitialSource
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (beta : Z4)
    {rightScale : Fin (m + 1) -> Real}
    (rightData : R324IncomingExceptionalStopTraceAssembly
      (ρ := rho) (C := C) (lam := lam) (ε := eps)
      (K := K) kappaM rightScale)
    (pi : kappaP.singles ≃ kappaM.singles)
    (projectedCoefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        ((rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq).SurvivingCoordinate ->
            T4) -> Complex)
    (hlinear : forall
      (a : Complex)
      (coefficient :
        (left.carrier.SurvivingCoordinate -> T4) -> Complex)
      (outgoingMode : Z4)
      (v : left.carrier.SurvivingCoordinate -> T4),
      left.density (fun u => a * coefficient u) outgoingMode v =
        a * left.density coefficient outgoingMode v)
    (hproject : forall
      (s : R324PaperLeftOuterParameter rho lam eps kappaM)
      (v : left.carrier.SurvivingCoordinate -> T4),
      (r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            left.carrier
            (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
            (v, s.2)) : Complex) =
        projectedCoefficient v
          ((rightData.trace.stopPrefix
            |>.splitSurvivingPiMeasurableEquiv
              rightData.terminal rightData.suffix
              rightData.trace.stopPrefix_remaining_eq
              (rightData.trace.stopProjection s.2)).2))
    (hleft : Integrable
      (fun q :
          R324PaperLeftOuterParameter rho lam eps kappaM ×
            (left.carrier.SurvivingCoordinate -> T4) =>
        left.density
          (fun v => r324PaperLeftCanonicalCoefficient left.carrier
            alpha beta pi q.1 v)
          beta q.2)
      ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
        (Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure))) :
    Integrable
        (rightData.incomingExceptionalInitialSourceDensity
          (-alpha)
          (fun omega : T4 ×
              (left.carrier.SurvivingCoordinate -> T4) => omega.1)
          (left.rightExceptionalPostOuter beta rightData
            projectedCoefficient))
        ((paperMeasure.prod
            (paperMeasure.prod
              (Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
                paperMeasure))).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate => paperMeasure)) ∧
      left.transformTarget
          (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)
          (fun s v => r324PaperLeftCanonicalCoefficient left.carrier
            alpha beta pi s v)
          beta =
        ∫ p,
          rightData.incomingExceptionalInitialSourceDensity
            (-alpha)
            (fun omega : T4 ×
                (left.carrier.SurvivingCoordinate -> T4) => omega.1)
            (left.rightExceptionalPostOuter beta rightData
              projectedCoefficient) p
          ∂((paperMeasure.prod
              (paperMeasure.prod
                (Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
                  paperMeasure))).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate => paperMeasure)) := by
  let initial :=
    R324WithinHalfResidualPrefix.initial rho lam eps kappaM
  let muRight := Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure
  let muLeft := Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure
  let muOuter := (paperMeasure.prod paperMeasure).prod muRight
  let sigma :=
    r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
      T4 T4 (initial.SurvivingCoordinate -> T4)
        (left.carrier.SurvivingCoordinate -> T4)
  let leftF :
      (((T4 × T4) × (initial.SurvivingCoordinate -> T4)) ×
        (left.carrier.SurvivingCoordinate -> T4)) -> Complex :=
    fun q =>
      left.density
        (fun v => r324PaperLeftCanonicalCoefficient left.carrier
          alpha beta pi q.1 v)
        beta q.2
  let rightF :
      ((T4 × (T4 ×
          (left.carrier.SurvivingCoordinate -> T4))) ×
        (initial.SurvivingCoordinate -> T4)) -> Complex :=
    fun p =>
      rightData.incomingExceptionalInitialSourceDensity
        (-alpha)
        (fun omega : T4 ×
            (left.carrier.SurvivingCoordinate -> T4) => omega.1)
        (left.rightExceptionalPostOuter beta rightData
          projectedCoefficient) p
  have hsigma : MeasurePreserving sigma
      (muOuter.prod muLeft)
      ((paperMeasure.prod (paperMeasure.prod muLeft)).prod muRight) :=
    measurePreserving_r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
      paperMeasure paperMeasure muRight muLeft
  have hpoint : forall q, leftF q = rightF (sigma q) := by
    intro q
    have hcoefficient :
        (fun v => r324PaperLeftCanonicalCoefficient left.carrier
          alpha beta pi q.1 v) =
        (fun v =>
          (charT4 (-alpha) q.1.1.1 *
              charT4 (-beta) q.1.1.2 *
              ((initial.residualIntegrand rho eps
                q.1.1.1 q.1.1.2 (initial.reconstruct q.1.2) : Real) :
                  Complex)) *
            projectedCoefficient v
              ((rightData.trace.stopPrefix
                |>.splitSurvivingPiMeasurableEquiv
                  rightData.terminal rightData.suffix
                  rightData.trace.stopPrefix_remaining_eq
                  (rightData.trace.stopProjection q.1.2)).2)) := by
      funext v
      unfold r324PaperLeftCanonicalCoefficient
      rw [hproject q.1 v]
      ring
    unfold leftF rightF
    rw [hcoefficient, hlinear]
    unfold R324IncomingExceptionalStopTraceAssembly.incomingExceptionalInitialSourceDensity
      rightExceptionalPostOuter
    simp only [sigma,
      r324TwoHalfRightInitialSourceRegroupMeasurableEquiv_apply,
      initial]
    ring
  have hright : Integrable rightF
      ((paperMeasure.prod (paperMeasure.prod muLeft)).prod muRight) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hleft.congr
    filter_upwards with q
    exact hpoint q
  have hleft' : Integrable leftF (muOuter.prod muLeft) := by
    exact hleft
  refine ⟨by simpa only [rightF, muLeft, muRight, initial] using hright, ?_⟩
  change (∫ s, ∫ v, leftF (s, v) ∂muLeft ∂muOuter) =
    ∫ p, rightF p
      ∂((paperMeasure.prod (paperMeasure.prod muLeft)).prod muRight)
  rw [← integral_prod _ hleft']
  rw [← hsigma.integral_comp' rightF]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

end R324PaperHalfEndpointUniformBound
end R324WithinHalfResidualPrefix

end

end Anderson4D
