import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransformED
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransformEE

/-!
# Common ordered carrier after the four paper endpoint operations

The branch-specific signed transforms stop at one common object: first the
left completed density is formed with the still-grouped residual primitive
factor as its coefficient, then that signed scalar is left untouched while
the right completed density is formed.  This is the literal order of the
two applications in paper Step 4(A), so no coefficient-linearity lemma or
premature Fubini step is needed.  This file names that object and transports
it to the initial nested-cross carrier.  It performs no estimate.
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
    {rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM (-alpha)}

/-- The terminal built from the two literal carriers retained by the
uniform one-half packages. -/
def twoHalfTerminal
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (right : R324PaperHalfEndpointUniformBound rightRoute) :
    R324TwoHalfTerminalData rho lam eps kappaP kappaM where
  left := left.carrier
  right := right.carrier
  left_remaining := left.carrier_remaining
  right_remaining := right.carrier_remaining
  left_processed := left.carrier_processed
  right_processed := right.carrier_processed

/-- The untouched Step-3 primitive cross factor on the two completed
endpoint carriers. -/
def crossCoefficient
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (right : R324PaperHalfEndpointUniformBound rightRoute)
    (pi : kappaP.singles ≃ kappaM.singles)
    (leftPost : left.carrier.SurvivingCoordinate -> T4)
    (rightPost : right.carrier.SurvivingCoordinate -> T4) : Complex :=
  (r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
    (r324TwoHalfRootDoubledReconstruct left.carrier right.carrier
      (leftPost, rightPost)) : Complex)

/-- Literal ordered density after both endpoints of both halves have been
evaluated.  The residual primitive factor first enters as the left
coefficient; the completed left signed density is then the untouched
coefficient of the right endpoint operation.  This is definitionally the
target of `ExactTransform.compose`. -/
def endpointProductDensity
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (right : R324PaperHalfEndpointUniformBound rightRoute)
    (beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) : Complex :=
  right.density
    (fun rightPost =>
      left.density
        (fun _ => left.crossCoefficient right pi p.1 rightPost)
        beta p.1)
    (-beta) p.2

/-- The same signed density on the literal initial nested-cross carrier. -/
def nestedEndpointProductDensity
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (right : R324PaperHalfEndpointUniformBound rightRoute)
    (beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (v : (left.twoHalfTerminal right).NestedCoordinate pi -> T4) : Complex :=
  (left.twoHalfTerminal right).initialNestedPullback pi
    (left.endpointProductDensity right beta pi) v

/-- Product Haar and initial nested Haar give exactly the same signed
four-endpoint integral. -/
theorem integral_endpointProductDensity_eq_nested
    (left : R324PaperHalfEndpointUniformBound leftRoute)
    (right : R324PaperHalfEndpointUniformBound rightRoute)
    (beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles) :
    (∫ p, left.endpointProductDensity right beta pi p
      ∂((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure))) =
      ∫ v, left.nestedEndpointProductDensity right beta pi v
        ∂Measure.pi fun _ :
          (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure := by
  exact (left.twoHalfTerminal right)
    |>.integral_terminalProduct_eq_integral_initialNestedPullback
      pi (left.endpointProductDensity right beta pi)

variable {leftProviders : R324PaperHalfRouteProviders
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) kappaP alpha}
  {rightProviders : R324PaperHalfRouteProviders
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) kappaM (-alpha)}

/-- The terminal retained by the uniform packages is canonically the same
terminal retained by their structural routes. -/
theorem twoHalfTerminal_eq_routes
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute) :
    left.twoHalfTerminal right = routes.terminal := by
  unfold twoHalfTerminal R324PaperTwoHalfEndpointRoutes.terminal
    R324PaperHalfCompletedRoute.twoHalfTerminal
  rw [R324TwoHalfTerminalData.mk.injEq]
  exact ⟨left.route_final.symm, right.route_final.symm⟩

end R324PaperHalfEndpointUniformBound
end R324WithinHalfResidualPrefix

end

end Anderson4D
