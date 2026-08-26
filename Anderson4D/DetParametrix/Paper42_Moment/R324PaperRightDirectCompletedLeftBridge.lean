import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightDirectIncomingSourceBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperActualEndpointCollapse

/-!
# Completed-left handoff to a direct right incoming endpoint

This is the literal Fubini handoff between the two halves in paper
Section 4.2, Step 4(A).  The already completed left density stays signed.
After its scalar outer factors are pulled through the left density, the
right incoming Fourier variable is integrated by the existing exact
initial-residual identity.  No norm or endpoint estimate occurs here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324PaperHalfEndpointUniformBound

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {alpha : Z4}
    {leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}

/-- Exact direct-incoming handoff for an arbitrary completed left route.

`project` is the already proved right transport projection (either the
full direct transport or the retained outgoing-terminal projection), and
`hproject` is precisely the corresponding primitive-cross identity. -/
theorem integrable_and_integral_completedLeft_eq_rightDirectInitialSource
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    {RightPost : Type*} [MeasurableSpace RightPost]
    (project :
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate → T4) → RightPost)
    (projectedCoefficient :
      (left.carrier.SurvivingCoordinate → T4) → RightPost → Complex)
    (hlinear : forall
      (a : Complex)
      (coefficient :
        (left.carrier.SurvivingCoordinate → T4) → Complex)
      (outgoingMode : Z4)
      (v : left.carrier.SurvivingCoordinate → T4),
      left.density (fun u => a * coefficient u) outgoingMode v =
        a * left.density coefficient outgoingMode v)
    (hproject : forall
      (s : R324PaperLeftOuterParameter rho lam eps kappaM)
      (v : left.carrier.SurvivingCoordinate → T4),
      (r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            left.carrier
            (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
            (v, s.2)) : Complex) =
        projectedCoefficient v (project s.2))
    (hleft : Integrable
      (fun q :
          R324PaperLeftOuterParameter rho lam eps kappaM ×
            (left.carrier.SurvivingCoordinate → T4) =>
        left.density
          (fun v => r324PaperLeftCanonicalCoefficient left.carrier
            alpha beta pi q.1 v)
          beta q.2)
      ((r324PaperLeftOuterParameterMeasure rho lam eps kappaM).prod
        (Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure))) :
    Integrable
        (fun q : (T4 ×
              (left.carrier.SurvivingCoordinate → T4)) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate → T4) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM
            |>.incomingPhasedResidualDensity
              ((paperSecondOrderModeDecay (-alpha) : Complex) *
                (charT4 (-beta) q.1.1 *
                  left.density
                    (fun v => projectedCoefficient v (project q.2))
                    beta q.1.2))
              (-alpha) rho eps 0 q.1.1 q.2))
        ((paperMeasure.prod
            (Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
              paperMeasure)).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate => paperMeasure)) ∧
      left.transformTarget
          (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)
          (fun s v => r324PaperLeftCanonicalCoefficient left.carrier
            alpha beta pi s v)
          beta =
        ∫ q : (T4 ×
              (left.carrier.SurvivingCoordinate → T4)) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate → T4),
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM
            |>.incomingPhasedResidualDensity
              ((paperSecondOrderModeDecay (-alpha) : Complex) *
                (charT4 (-beta) q.1.1 *
                  left.density
                    (fun v => projectedCoefficient v (project q.2))
                    beta q.1.2))
              (-alpha) rho eps 0 q.1.1 q.2)
          ∂((paperMeasure.prod
              (Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
                paperMeasure)).prod
              (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate => paperMeasure)) := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps kappaM
  let Left := left.carrier.SurvivingCoordinate → T4
  let muLeft : Measure Left := Measure.pi fun _ => paperMeasure
  let muRight : Measure (initial.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let coefficient := fun
      (w : T4) (vr : initial.SurvivingCoordinate → T4) (vl : Left) =>
    charT4 (-beta) w *
      left.density (fun v => projectedCoefficient v (project vr)) beta vl
  let raw := fun q :
      (((T4 × T4) × (initial.SurvivingCoordinate → T4)) × Left) =>
    charT4 (-alpha) q.1.1.1 *
      ((initial.residualIntegrand rho eps q.1.1.1 q.1.1.2
        (initial.reconstruct q.1.2) : Complex) *
        coefficient q.1.1.2 q.1.2 q.2)
  have hpoint (q :
      (((T4 × T4) × (initial.SurvivingCoordinate → T4)) × Left)) :
      left.density
          (fun v => r324PaperLeftCanonicalCoefficient left.carrier
            alpha beta pi q.1 v)
          beta q.2 = raw q := by
    let scalar : Complex :=
      charT4 (-alpha) q.1.1.1 *
        (charT4 (-beta) q.1.1.2 *
          (initial.residualIntegrand rho eps q.1.1.1 q.1.1.2
            (initial.reconstruct q.1.2) : Complex))
    have hcoefficient :
        (fun v => r324PaperLeftCanonicalCoefficient left.carrier
          alpha beta pi q.1 v) =
        (fun v => scalar * projectedCoefficient v (project q.1.2)) := by
      funext v
      unfold r324PaperLeftCanonicalCoefficient scalar
      rw [hproject q.1 v]
      ring
    rw [hcoefficient, hlinear]
    unfold raw coefficient scalar
    ring
  have hraw : Integrable raw
      ((((paperMeasure.prod paperMeasure).prod muRight).prod muLeft)) := by
    apply hleft.congr
    filter_upwards with q
    exact hpoint q
  obtain ⟨hsource, heq⟩ :=
    integrable_and_integral_rightDirectIncomingSource
      rho lam eps kappaM muLeft coefficient (-alpha)
      (by simpa only [raw, initial, muRight, muLeft, Left] using hraw)
  refine ⟨?_, ?_⟩
  · simpa only [coefficient, initial, muLeft, Left] using hsource
  · calc
      left.transformTarget
          (r324PaperLeftOuterParameterMeasure rho lam eps kappaM)
          (fun s v => r324PaperLeftCanonicalCoefficient left.carrier
            alpha beta pi s v)
          beta =
          ∫ s : (T4 × T4) ×
                (initial.SurvivingCoordinate → T4),
            ∫ u : Left, raw (s, u) ∂muLeft
            ∂((paperMeasure.prod paperMeasure).prod muRight) := by
        unfold transformTarget r324PaperLeftOuterParameterMeasure
        apply integral_congr_ae
        filter_upwards with s
        apply integral_congr_ae
        filter_upwards with u
        exact hpoint (s, u)
      _ = ∫ q : (T4 × Left) ×
              (initial.SurvivingCoordinate → T4),
            initial.incomingPhasedResidualDensity
              ((paperSecondOrderModeDecay (-alpha) : Complex) *
                coefficient q.1.1 q.2 q.1.2)
              (-alpha) rho eps 0 q.1.1 q.2
            ∂((paperMeasure.prod muLeft).prod muRight) := by
        simpa only [raw, coefficient, initial, muLeft, muRight, Left]
          using heq
      _ = _ := by
        rfl

end R324PaperHalfEndpointUniformBound
end R324WithinHalfResidualPrefix

end

end Anderson4D
