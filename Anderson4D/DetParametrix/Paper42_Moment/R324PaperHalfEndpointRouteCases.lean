import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointRoutes

/-!
# Exhaustive one-half and two-half endpoint route cases

This is the finite structural case split behind paper Step 4(A).  The four
constructors retain the branch-specific witness needed by the corresponding
signed identity; `completedRoute` forgets only that dependent witness and
keeps the common terminal budget.  Pairing two values therefore represents
the literal `4 x 4` endpoint table without duplicating any transport proof.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open SmoothCutoff

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}

/-- The actual incoming/outgoing endpoint cases of one half, in paper order.
-/
def r324PaperActualHalfEndpointCases
    (pairing : PartialPairing (Fin m)) : R324PaperHalfEndpointCases :=
  ![r324IncomingEndpointReductionCase pairing,
    r324EndpointReductionCaseOfFlag (r324OutgoingIsShortcut pairing)]

/-- Exhaustive structural route for one half.  Evidence for the two actual
classification tests is stored in the constructor, so a route cannot be
mislabelled by assigning a convenient endpoint ledger after the fact. -/
inductive R324PaperHalfEndpointRoute
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) where
  | directDirect
      (hfirst : (⟨0, providers.hm⟩ : Fin m) ∈ finalActive pairing)
      (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
      (data : R324PaperHalfDirectDirectRoute providers)
  | directExceptional
      (hfirst : (⟨0, providers.hm⟩ : Fin m) ∈ finalActive pairing)
      (houtgoing : Fin.last m ∈ extractedRightEdges pairing)
      (data : R324PaperHalfDirectExceptionalRoute providers)
  | exceptionalDirect
      (hfirst : (⟨0, providers.hm⟩ : Fin m) ∉ finalActive pairing)
      (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
      (data : R324PaperHalfExceptionalDirectRoute providers)
  | exceptionalExceptional
      (hfirst : (⟨0, providers.hm⟩ : Fin m) ∉ finalActive pairing)
      (houtgoing : Fin.last m ∈ extractedRightEdges pairing)
      (data : R324PaperHalfExceptionalExceptionalRoute providers)

namespace R324PaperHalfEndpointRoute

variable {providers : R324PaperHalfRouteProviders
  (rho := rho) (C := C) (lam := lam) (eps := eps)
  (K := K) (A := A) pairing incomingMode}

/-- Forget the branch-dependent signed witness only after it has produced the
common completed terminal route. -/
def completedRoute
    (route : R324PaperHalfEndpointRoute providers) :
    R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode :=
  match route with
  | .directDirect _ _ data => data.route
  | .directExceptional _ _ data => data.route
  | .exceptionalDirect _ _ data => data.route
  | .exceptionalExceptional _ _ data => data.route

/-- The stored literal branch ledger agrees with the classification of the
actual pairing. -/
theorem completedRoute_cases
    (route : R324PaperHalfEndpointRoute providers) :
    route.completedRoute.cases =
      r324PaperActualHalfEndpointCases pairing := by
  cases route with
  | directDirect hfirst houtgoing data =>
      change data.route.cases = r324PaperActualHalfEndpointCases pairing
      rw [data.route_cases]
      funext i
      fin_cases i <;>
        simp [r324PaperActualHalfEndpointCases,
          r324IncomingEndpointReductionCase, providers.hm, hfirst,
          r324OutgoingIsShortcut, houtgoing,
          r324EndpointReductionCaseOfFlag]
  | directExceptional hfirst houtgoing data =>
      change data.route.cases = r324PaperActualHalfEndpointCases pairing
      rw [data.route_cases]
      funext i
      fin_cases i <;>
        simp [r324PaperActualHalfEndpointCases,
          r324IncomingEndpointReductionCase, providers.hm, hfirst,
          r324OutgoingIsShortcut, houtgoing,
          r324EndpointReductionCaseOfFlag]
  | exceptionalDirect hfirst houtgoing data =>
      change data.route.cases = r324PaperActualHalfEndpointCases pairing
      rw [data.route_cases]
      funext i
      fin_cases i <;>
        simp [r324PaperActualHalfEndpointCases,
          r324IncomingEndpointReductionCase, providers.hm, hfirst,
          r324OutgoingIsShortcut, houtgoing,
          r324EndpointReductionCaseOfFlag]
  | exceptionalExceptional hfirst houtgoing data =>
      change data.route.cases = r324PaperActualHalfEndpointCases pairing
      rw [data.route_cases]
      funext i
      fin_cases i <;>
        simp [r324PaperActualHalfEndpointCases,
          r324IncomingEndpointReductionCase, providers.hm, hfirst,
          r324OutgoingIsShortcut, houtgoing,
          r324EndpointReductionCaseOfFlag]

/-- Construct the unique actual branch.  A residual single is needed only in
the `EE` branch, exactly where it proves that the incoming and outgoing
exceptional blocks are distinct. -/
theorem exists_of_singles
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode)
    (hsingles : pairing.singles.Nonempty) :
    Nonempty (R324PaperHalfEndpointRoute providers) := by
  by_cases hfirst :
      (⟨0, providers.hm⟩ : Fin m) ∈ finalActive pairing
  · by_cases houtgoing : Fin.last m ∈ extractedRightEdges pairing
    · obtain ⟨data⟩ := providers.exists_directExceptional hfirst houtgoing
      exact ⟨.directExceptional hfirst houtgoing data⟩
    · obtain ⟨data⟩ := providers.exists_directDirect hfirst houtgoing
      exact ⟨.directDirect hfirst houtgoing data⟩
  · by_cases houtgoing : Fin.last m ∈ extractedRightEdges pairing
    · obtain ⟨data⟩ :=
        providers.exists_exceptionalExceptional hfirst houtgoing hsingles
      exact ⟨.exceptionalExceptional hfirst houtgoing data⟩
    · obtain ⟨data⟩ := providers.exists_exceptionalDirect hfirst houtgoing
      exact ⟨.exceptionalDirect hfirst houtgoing data⟩

end R324PaperHalfEndpointRoute

/-! ## The literal `4 x 4` structural table -/

variable {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}

structure R324PaperTwoHalfEndpointRoutes
    (leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode)
    (rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode) where
  left : R324PaperHalfEndpointRoute leftProviders
  right : R324PaperHalfEndpointRoute rightProviders

namespace R324PaperTwoHalfEndpointRoutes

variable {leftProviders : R324PaperHalfRouteProviders
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) kappaP leftMode}
  {rightProviders : R324PaperHalfRouteProviders
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) kappaM rightMode}

def terminal
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders) :
    R324TwoHalfTerminalData rho lam eps kappaP kappaM :=
  R324PaperHalfCompletedRoute.twoHalfTerminal
    routes.left.completedRoute routes.right.completedRoute

def cases
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders) :
    Fin 4 -> R324EndpointReductionCase :=
  R324PaperHalfCompletedRoute.combinedCases
    routes.left.completedRoute routes.right.completedRoute

/-- The order is definitionally `LI, LO, RI, RO`, and both halves carry
their actual pairing classifications. -/
theorem cases_eq_actual
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders) :
    routes.cases =
      ![r324PaperActualHalfEndpointCases kappaP 0,
        r324PaperActualHalfEndpointCases kappaP 1,
        r324PaperActualHalfEndpointCases kappaM 0,
        r324PaperActualHalfEndpointCases kappaM 1] := by
  funext i
  fin_cases i <;>
    simp [cases, R324PaperHalfCompletedRoute.combinedCases,
      routes.left.completedRoute_cases,
      routes.right.completedRoute_cases]

/-- Exact multiplication of the two literal half costs; no `eps^-8`
uniformization is performed here. -/
theorem endpointSacrifice_mul_eq_product
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders) :
    routes.left.completedRoute.endpointSacrifice *
        routes.right.completedRoute.endpointSacrifice =
      r324EndpointPrimitiveSacrificeProduct eps routes.cases :=
  R324PaperHalfCompletedRoute.endpointSacrifice_mul_eq_combinedProduct
    routes.left.completedRoute routes.right.completedRoute

theorem exists_of_singles
    (leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode)
    (rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode)
    (hleft : kappaP.singles.Nonempty)
    (hright : kappaM.singles.Nonempty) :
    Nonempty (R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders) := by
  obtain ⟨left⟩ :=
    R324PaperHalfEndpointRoute.exists_of_singles leftProviders hleft
  obtain ⟨right⟩ :=
    R324PaperHalfEndpointRoute.exists_of_singles rightProviders hright
  exact ⟨{ left := left, right := right }⟩

end R324PaperTwoHalfEndpointRoutes

end R324WithinHalfResidualPrefix

end

end Anderson4D
