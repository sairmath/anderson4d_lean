import Anderson4D.DetParametrix.Paper42_Moment.R324PaperDEDDAEMajorant
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperExceptionalDirectEndpointBound

/-!
# Uniform interface for the four literal one-half endpoint branches

This file packages the four already completed signed endpoint calculations
without expanding the two-half argument into sixteen cases.  The carrier is
kept branch-literal, together with its equality to the common completed
route.  A direct outgoing endpoint contributes mass `1`; a retained
exceptional outgoing endpoint contributes the one genuine
`invSqKerMass`.  No uniform mass or endpoint sacrifice is inserted here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

/-- The exact spatial mass produced by the outgoing endpoint operation. -/
def r324PaperHalfOutgoingEndpointMass :
    R324EndpointReductionCase -> Real
  | .directFourier => 1
  | .insertedSacrifice => invSqKerMass

@[simp]
theorem r324PaperHalfOutgoingEndpointMass_direct :
    r324PaperHalfOutgoingEndpointMass .directFourier = 1 :=
  rfl

@[simp]
theorem r324PaperHalfOutgoingEndpointMass_inserted :
    r324PaperHalfOutgoingEndpointMass .insertedSacrifice =
      invSqKerMass :=
  rfl

theorem r324PaperHalfOutgoingEndpointMass_nonneg
    (c : R324EndpointReductionCase) :
    0 <= r324PaperHalfOutgoingEndpointMass c := by
  cases c with
  | directFourier => exact zero_le_one
  | insertedSacrifice => exact invSqKerMass_nonneg

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}

/-- Common pointwise output of any one-half endpoint branch.  The density
is coefficient-parametric because the second half supplies the untouched
cross primitive factor only after both signed endpoint computations have
been chosen. -/
structure R324PaperHalfEndpointUniformBound
    (route : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) where
  carrier : R324WithinHalfResidualPrefix rho lam eps pairing
  route_final : route.final = carrier
  carrier_remaining : carrier.remaining = []
  carrier_processed :
    carrier.state.processed = r322AnalyticSchedule pairing
  active : carrier.state.active.Nonempty
  density :
    ((carrier.SurvivingCoordinate -> T4) -> Complex) ->
      Z4 -> (carrier.SurvivingCoordinate -> T4) -> Complex
  norm_density_le :
    forall
      (coefficient :
        (carrier.SurvivingCoordinate -> T4) -> Complex)
      (outgoingMode : Z4)
      (v : carrier.SurvivingCoordinate -> T4),
      (∀ edge ∈ carrier.endpointErasedActiveEdgeSlots active,
        carrier.edgeDisplacement 0 0 (carrier.reconstruct v) edge ≠ 0) ->
      ‖density coefficient outgoingMode v‖ <=
        (paperSecondOrderModeDecay incomingMode *
            paperSecondOrderModeDecay outgoingMode) *
          route.endpointSacrifice *
          ((∏ edge ∈ carrier.activeEdgeSlots,
              route.terminalScale edge) *
            r324PaperHalfOutgoingEndpointMass (route.cases 1)) *
          carrier.endpointErasedInvSqChainProduct active v *
          ‖coefficient v‖

namespace R324PaperHalfEndpointUniformBound

variable {providers : R324PaperHalfRouteProviders
  (rho := rho) (C := C) (lam := lam) (eps := eps)
  (K := K) (A := A) pairing incomingMode}

/-- The direct/direct calculation in the common one-half interface. -/
def ofDirectDirect
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (data : R324PaperHalfDirectDirectRoute providers) :
    R324PaperHalfEndpointUniformBound data.route := by
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      providers.hm data.transport.final_processed_eq_schedule houtgoing
  refine {
    carrier := data.transport.final
    route_final := data.route_final
    carrier_remaining := data.transport.final_remaining
    carrier_processed := data.transport.final_processed_eq_schedule
    active := hactive
    density := fun coefficient outgoingMode v =>
      data.transportEndpointDensity hactive coefficient outgoingMode v
    norm_density_le := ?_ }
  intro coefficient outgoingMode v hne
  have hbound := data.norm_transportEndpointDensity_le
    houtgoing hactive coefficient outgoingMode v hne
  simpa only [R324PaperHalfCompletedRoute.endpointSacrifice,
    r324PaperHalfEndpointSacrifice, data.route_cases,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    r324EndpointPrimitiveSacrifice,
    r324PaperHalfOutgoingEndpointMass_direct,
    one_mul, mul_one] using hbound

/-- The direct/exceptional calculation in the common one-half interface. -/
def ofDirectExceptional
    (data : R324PaperHalfDirectExceptionalRoute providers) :
    R324PaperHalfEndpointUniformBound data.route := by
  refine {
    carrier := data.outgoing.terminalPost
    route_final := data.route_final
    carrier_remaining := data.outgoing.terminalPost_remaining
    carrier_processed := data.outgoing.terminalPost_processed_eq_schedule
    active := data.terminalPost_active
    density := fun coefficient outgoingMode v =>
      data.endpointDensity coefficient outgoingMode 0 v
    norm_density_le := ?_ }
  intro coefficient outgoingMode v hne
  have hbound := data.norm_endpointDensity_le
    coefficient outgoingMode 0 v hne
  simpa only [R324PaperHalfCompletedRoute.endpointSacrifice,
    r324PaperHalfEndpointSacrifice, data.route_cases,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    r324PaperHalfOutgoingEndpointMass_inserted] using hbound

/-- The exceptional/direct calculation in the common one-half interface. -/
def ofExceptionalDirect
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (data : R324PaperHalfExceptionalDirectRoute providers) :
    R324PaperHalfEndpointUniformBound data.route := by
  let hactive : data.transport.final.state.active.Nonempty :=
    data.transport.final.active_nonempty_of_directOutgoing
      providers.hm data.transport.final_processed_eq_schedule houtgoing
  refine {
    carrier := data.transport.final
    route_final := data.route_final
    carrier_remaining := data.transport.final_remaining
    carrier_processed := data.transport.final_processed_eq_schedule
    active := hactive
    density := fun coefficient outgoingMode v =>
      data.endpointDensity hactive coefficient outgoingMode v
    norm_density_le := ?_ }
  intro coefficient outgoingMode v hne
  have hbound := data.norm_endpointDensity_le
    houtgoing hactive coefficient outgoingMode v hne
  simpa only [R324PaperHalfCompletedRoute.endpointSacrifice,
    r324PaperHalfEndpointSacrifice, data.route_cases,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    r324EndpointPrimitiveSacrifice,
    r324PaperHalfOutgoingEndpointMass_direct,
    one_mul, mul_one] using hbound

/-- The exceptional/exceptional calculation in the common one-half
interface.  The surviving-single hypothesis supplies exactly the two
geometric facts required by the retained outgoing endpoint. -/
def ofExceptionalExceptional
    (hsingles : pairing.singles.Nonempty)
    (data : R324PaperHalfExceptionalExceptionalRoute providers) :
    R324PaperHalfEndpointUniformBound data.route := by
  let hactive := data.terminalPost_active_of_singles hsingles
  let hpred := data.predecessor_ne_zero_of_singles hsingles
  refine {
    carrier := data.outgoing.terminalPost
    route_final := data.route_final
    carrier_remaining := data.outgoing.terminalPost_remaining
    carrier_processed := data.outgoing.terminalPost_processed_eq_schedule
    active := hactive
    density := fun coefficient outgoingMode v =>
      data.endpointDensity coefficient outgoingMode 0 v
    norm_density_le := ?_ }
  intro coefficient outgoingMode v hne
  have hbound := data.norm_endpointDensity_le
    hpred hactive coefficient outgoingMode 0 v hne
  simpa only [R324PaperHalfCompletedRoute.endpointSacrifice,
    r324PaperHalfEndpointSacrifice, data.route_cases,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    r324PaperHalfOutgoingEndpointMass_inserted] using hbound

end R324PaperHalfEndpointUniformBound

namespace R324PaperHalfEndpointRoute

variable {providers : R324PaperHalfRouteProviders
  (rho := rho) (C := C) (lam := lam) (eps := eps)
  (K := K) (A := A) pairing incomingMode}

/-- Exhaustive one-half producer.  The four signed calculations are
packaged once here; later two-half code consumes two uniform packages and
does not repeat a sixteen-way case split. -/
theorem exists_endpointUniformBound_of_singles
    (route : R324PaperHalfEndpointRoute providers)
    (hsingles : pairing.singles.Nonempty) :
    Nonempty (R324PaperHalfEndpointUniformBound route.completedRoute) := by
  cases route with
  | directDirect _hfirst houtgoing data =>
      exact ⟨R324PaperHalfEndpointUniformBound.ofDirectDirect
        houtgoing data⟩
  | directExceptional _hfirst _houtgoing data =>
      exact ⟨R324PaperHalfEndpointUniformBound.ofDirectExceptional data⟩
  | exceptionalDirect _hfirst houtgoing data =>
      exact ⟨R324PaperHalfEndpointUniformBound.ofExceptionalDirect
        houtgoing data⟩
  | exceptionalExceptional _hfirst _houtgoing data =>
      exact ⟨R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
        hsingles data⟩

end R324PaperHalfEndpointRoute
end R324WithinHalfResidualPrefix

end

end Anderson4D
