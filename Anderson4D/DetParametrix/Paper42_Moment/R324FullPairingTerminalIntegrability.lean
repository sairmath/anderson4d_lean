import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingIntegratedTerminal
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualIntegrability

/-!
# Certificate-produced integrability for the full-pairing terminal block

The integrated full-pairing terminal identity is stated with the exact
per-primitive-pairing integrability premise needed by finite-sum Fubini.
For a budget/geometry adapter that premise is automatic: its terminal edge
certificate supplies measurability, a positive scale, class-`E` membership,
and the scaled off-diagonal bound for every heterogeneous internal edge.

The public scaled off-diagonal assembly theorem includes the order-one
zero-dimensional case, so no extra lower-order hypothesis is needed here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingBudgetTerminalAdapter

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {budget :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ}

/-- Every closed primitive summand in the adapter's retained terminal block
has an absolutely integrable internal section, pointwise in both endpoints.
This includes terminal block order one. -/
theorem integrable_terminalClosedIntegrand_section
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κB :
      {κB : PartialPairing
          (Fin
            (2 * residualBlockOrder
              data.geometry.terminalData.terminal.2)) //
        κB ∈ primitiveFullPairings
          (residualBlockOrder
            data.geometry.terminalData.terminal.2)})
    (z w : T4) :
    Integrable
      (fun u :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 2) →
            T4 =>
        detJclosedIntegrandWith ρ ε
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2)
          κB.1
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalEdges
          (primitiveAssemble
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            z w u))
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp κB.2
  have hraw :
      Integrable
        (fun u :
            Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2 - 2) →
              T4 =>
          primitiveIntegrand ρ ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges
            κB.1
            (primitiveAssemble
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              z w u))
        (Measure.pi fun _ => paperMeasure) :=
    integrable_primitiveIntegrand_assemble_of_scaled_offDiagonal
      ρ hε hε1
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
      (fun j =>
        budget.stopScale
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalSlot j))
      (fun j =>
        data.certificate.measurable
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalSlot j))
      (fun j =>
        data.certificate.scale_pos
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalSlot j))
      (fun j =>
        data.certificate.memE
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalSlot j))
      (fun j u hu =>
        data.certificate.bound
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalSlot j)
          u hu)
      κB z w
  apply hraw.congr
  filter_upwards with u
  exact
    (detJclosedIntegrandWith_eq_primitiveIntegrand_of_full_primitive
      ρ ε
      (residualBlockOrder
        data.geometry.terminalData.terminal.2)
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
      κB.1 hfull hprimitive
      (primitiveAssemble
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        z w u)).symm

/-- The integrated terminal identity with its finite-sum Fubini premise
discharged directly from the adapter's edge certificate. -/
theorem lamEps_pow_integral_terminalGroupedPrimitiveCore_eq_predecessor_mul_primitiveKernel_of_certificate
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x z w : T4) :
    lamEps lam ε ^
          (2 * residualBlockOrder
            data.geometry.terminalData.terminal.2) *
        (∫ u :
            Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2 - 2) →
              T4,
          data.geometry.terminalGroupedPrimitiveCore x
            (primitiveAssemble
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)
              (data.geometry.trace.stopPrefix.headContext
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
              z w u)
          ∂Measure.pi fun _ => paperMeasure) =
      data.geometry.trace.stopPrefix.state.edges
          (r324WithinHalfPredecessorSlot
            data.geometry.trace.stopPrefix.state
            data.geometry.terminalData.terminal)
          (x - z) *
        primitiveKernel ρ lam ε
          (residualBlockOrder
            data.geometry.terminalData.terminal.2)
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalEdges
          z w := by
  exact
    data.lamEps_pow_integral_terminalGroupedPrimitiveCore_eq_predecessor_mul_primitiveKernel
      x z w
      (fun κB =>
        data.integrable_terminalClosedIntegrand_section
          hε hε1 κB z w)

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
