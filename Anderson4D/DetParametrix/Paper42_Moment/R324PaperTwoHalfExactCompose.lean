import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfEndpointProduct

/-!
# Exact two-half composition at the common paper endpoint carrier

This file contains the single algebraic/Fubini seam shared by all actual
endpoint cases.  The branch-specific work stops when it supplies the two
already proved one-half `ExactTransform`s and identifies the second source
with the first target.  The two transforms are then composed before any
norm is taken, and the completed signed density is transported once to the
initial nested-cross carrier.
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
    {alpha beta : Z4}
    {leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    {rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM (-alpha)}

/-- The common consumer of the two branch-literal one-half transforms.
The right coefficient is exactly the completed left signed density with the
untouched primitive cross factor.  Consequently its target is
definitionally `endpointProductDensity`; the only Fubini step is the final
product-Haar regroup, justified by the displayed integrability premise. -/
theorem exactCollapse_to_nested_of_transforms
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (right : R324PaperHalfEndpointUniformBound rightRoute)
    {U : Type*} [MeasurableSpace U]
    (muU : Measure U)
    (leftCoefficient : U ->
      (left.carrier.SurvivingCoordinate -> T4) -> Complex)
    (leftTransform : left.ExactTransform
      muU leftCoefficient beta)
    (pi : kappaP.singles ≃ kappaM.singles)
    (rightTransform : right.ExactTransform
      (Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure)
      (fun leftPost rightPost =>
        left.density
          (fun _ => left.crossCoefficient right pi leftPost rightPost)
          beta leftPost)
      (-beta))
    (hsource : rightTransform.source =
      left.transformTarget muU leftCoefficient beta)
    (physical : Complex)
    (hphysical : leftTransform.source = physical)
    (hintegrable : Integrable
      (left.endpointProductDensity right beta pi)
      ((Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate => paperMeasure))) :
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * physical =
      ∫ v, left.nestedEndpointProductDensity right beta pi v
        ∂Measure.pi fun _ :
          (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure := by
  have hcompose :=
    R324PaperHalfEndpointUniformBound.ExactTransform.compose
      leftTransform rightTransform hsource
  calc
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * physical =
        (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * leftTransform.source := by
      rw [hphysical]
    _ = right.transformTarget
          (Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure)
          (fun leftPost rightPost =>
            left.density
              (fun _ => left.crossCoefficient right pi leftPost rightPost)
              beta leftPost)
          (-beta) := hcompose
    _ = ∫ leftPost,
          ∫ rightPost,
            left.endpointProductDensity right beta pi
              (leftPost, rightPost)
            ∂Measure.pi fun _ : right.carrier.SurvivingCoordinate => paperMeasure
          ∂Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure := by
      rfl
    _ = ∫ p, left.endpointProductDensity right beta pi p
          ∂((Measure.pi fun _ : left.carrier.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ : right.carrier.SurvivingCoordinate => paperMeasure)) := by
      rw [integral_prod _ hintegrable]
    _ = ∫ v, left.nestedEndpointProductDensity right beta pi v
          ∂Measure.pi fun _ :
            (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure :=
      left.integral_endpointProductDensity_eq_nested right beta pi

end R324PaperHalfEndpointUniformBound
end R324WithinHalfResidualPrefix

end

end Anderson4D
