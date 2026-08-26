import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightDirectDirectExact
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightExceptionalDirectExact
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightDirectExceptionalExact
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightExceptionalExceptionalExact

/-!
# The completed right endpoint half, in all four literal cases

This is only the paper Step 4(A) case split on the second half.  Each branch
has already completed its signed incoming operation, all intervening
intervals, and its outgoing operation before exposing the common exact
package.
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

namespace R324PaperRightRouteExactPackage

/-- Literal four-case constructor for the completed right half. -/
theorem exists_of_route
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (hsingles : e0.2.1.singles.Nonempty)
    (route : R324PaperHalfEndpointRoute rightProviders) :
    Nonempty (R324PaperRightRouteExactPackage left route) := by
  cases route with
  | directDirect hfirst houtgoing data =>
      exact exists_of_directDirect left hfirst houtgoing data
  | directExceptional hfirst houtgoing data =>
      exact exists_of_directExceptional left hfirst houtgoing data
  | exceptionalDirect hfirst houtgoing data =>
      exact exists_of_exceptionalDirect left hfirst houtgoing data
  | exceptionalExceptional hfirst houtgoing data =>
      exact exists_of_exceptionalExceptional
        left hfirst houtgoing hsingles data

end R324PaperRightRouteExactPackage
end R324WithinHalfResidualPrefix

end

end Anderson4D
