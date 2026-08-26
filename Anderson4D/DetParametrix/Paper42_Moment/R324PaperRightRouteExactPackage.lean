import Anderson4D.DetParametrix.Paper42_Moment.R324PaperLeftRouteExactPackage
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfExactCompose
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightDirectCompletedLeftBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightExceptionalIncomingSourceBridge

/-!
# Common exact output of the second endpoint half

The source equality is the single signed Fubini handoff between the two
halves.  `endpoint_integrable` is retained solely for the final product-Haar
regroup.  Neither field contains an estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {alpha beta : Z4}
    {p : R324RefinedScheduleIndex m}
    {e0 : MomentContraction m}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.2.1 (-alpha)}
    {leftRoute : R324PaperHalfEndpointRoute leftProviders}
    {rightRoute : R324PaperHalfEndpointRoute rightProviders}

/-- The completed right transform and the exact source/target seams needed
by `exactCollapse_to_nested_of_transforms`. -/
structure R324PaperRightRouteExactPackage
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (rightRoute : R324PaperHalfEndpointRoute rightProviders) where
  bound : R324PaperHalfEndpointUniformBound rightRoute.completedRoute
  transform : bound.ExactTransform
    (Measure.pi fun _ : left.bound.carrier.SurvivingCoordinate => paperMeasure)
    (fun leftPost rightPost =>
      left.bound.density
        (fun _ => left.bound.crossCoefficient bound e0.2.2
          leftPost rightPost)
        beta leftPost)
    (-beta)
  source_eq_left_target : transform.source =
    left.bound.transformTarget
      (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
      (fun s v => r324PaperLeftCanonicalCoefficient
        left.bound.carrier alpha beta e0.2.2 s v)
      beta
  endpoint_integrable : Integrable
    (left.bound.endpointProductDensity bound beta e0.2.2)
    ((Measure.pi fun _ : left.bound.carrier.SurvivingCoordinate =>
        paperMeasure).prod
      (Measure.pi fun _ : bound.carrier.SurvivingCoordinate => paperMeasure))
  density_mul : ∀ (a : ℂ)
      (coefficient :
        (bound.carrier.SurvivingCoordinate → T4) → ℂ)
      (outgoingMode : Z4)
      (v : bound.carrier.SurvivingCoordinate → T4),
    bound.density (fun u => a * coefficient u) outgoingMode v =
      a * bound.density coefficient outgoingMode v
  density_congr_at : ∀
      (leftCoefficient rightCoefficient :
        (bound.carrier.SurvivingCoordinate → T4) → ℂ)
      (outgoingMode : Z4)
      (v : bound.carrier.SurvivingCoordinate → T4),
    leftCoefficient v = rightCoefficient v →
      bound.density leftCoefficient outgoingMode v =
        bound.density rightCoefficient outgoingMode v

namespace R324PaperRightRouteExactPackage

/-- With both half packages in hand, the complete four-endpoint signed
collapse is exactly the already proved common two-half composition. -/
theorem exactCollapse_to_nested
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactPackage left rightRoute) :
    (lamEps lam eps : ℂ) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps e0.1).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).remainingOrder)) *
        r324RefinedPhysicalIntegral rho eps m alpha beta p =
      ∫ v,
        left.bound.nestedEndpointProductDensity
          right.bound beta e0.2.2 v
        ∂Measure.pi fun _ :
          (left.bound.twoHalfTerminal right.bound).NestedCoordinate
            e0.2.2 => paperMeasure := by
  exact left.bound.exactCollapse_to_nested_of_transforms
    right.bound
    (r324PaperLeftOuterParameterMeasure rho lam eps e0.2.1)
    (fun s v => r324PaperLeftCanonicalCoefficient
      left.bound.carrier alpha beta e0.2.2 s v)
    left.transform e0.2.2 right.transform
    right.source_eq_left_target
    (r324RefinedPhysicalIntegral rho eps m alpha beta p)
    left.source_eq_physical right.endpoint_integrable

end R324PaperRightRouteExactPackage

end R324WithinHalfResidualPrefix

end

end Anderson4D
