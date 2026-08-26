import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingCosineSeam
import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingBudgetTerminalAdapter

/-!
# Integrated terminal primitive block for a full pairing

The budget/geometry adapter identifies the residual state reached by the
complete quantitative proper-prefix trace with the state used by the
terminal Fourier geometry.  This file uses that identification twice:

* the edge certificate supplies `𝓔`-membership for every heterogeneous
  internal edge of the retained primitive block;
* integration of the signed, grouped terminal core produces one literal
  predecessor edge times the heterogeneous primitive kernel.

The terminal `lamEps` power is kept separate from the proper-prefix budget,
and the complete finite primitive-pairing sum stays grouped until the exact
primitive-kernel integration theorem is applied.
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

/-- Every heterogeneous internal edge of the retained terminal primitive
block belongs to the paper's symmetry class, directly from the complete
budget certificate on the adapter's identified residual state. -/
theorem terminalInternalEdges_memE
    (data : R324FullPairingBudgetTerminalAdapter budget) :
    ∀ j,
      MemEClassT4
        ((data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges j) := by
  intro j
  simpa only [R324WithinHalfStepContext.internalEdges,
    R324WithinHalfResidualPrefix.headContext] using
    (data.certificate.memE
      ((data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalSlot j))

/-- **Exact integrated terminal core.**  After integrating precisely the
internal coordinates of the terminal primitive block, the grouped signed
primitive-pairing density becomes the heterogeneous `primitiveKernel`.
The remaining factor is the genuine predecessor edge evaluated from the
external point to the retained first endpoint. -/
theorem lamEps_pow_integral_terminalGroupedPrimitiveCore_eq_predecessor_mul_primitiveKernel
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (x z w : T4)
    (hint :
      ∀ κB :
          {κB : PartialPairing
              (Fin
                (2 * residualBlockOrder
                  data.geometry.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder
                data.geometry.terminalData.terminal.2)},
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
          (Measure.pi fun _ => paperMeasure)) :
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
  have hpoint :
      (fun u :
          Fin
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2 - 2) →
            T4 =>
        data.geometry.terminalGroupedPrimitiveCore x
          (primitiveAssemble
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            z w u)) =
        fun u =>
          data.geometry.trace.stopPrefix.state.edges
              (r324WithinHalfPredecessorSlot
                data.geometry.trace.stopPrefix.state
                data.geometry.terminalData.terminal)
              (x - z) *
            data.geometry.terminalCompletePrimitiveDensity
              (primitiveAssemble
                (residualBlockOrder
                  data.geometry.terminalData.terminal.2)
                (data.geometry.trace.stopPrefix.headContext
                  data.geometry.terminalData.terminal []
                  data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                z w u) := by
    funext u
    rw [
      data.geometry.terminalGroupedPrimitiveCore_eq_predecessor_mul_completeDensity,
      primitiveAssemble_zero]
  rw [hpoint, integral_const_mul]
  calc
    lamEps lam ε ^
            (2 * residualBlockOrder
              data.geometry.terminalData.terminal.2) *
          (data.geometry.trace.stopPrefix.state.edges
              (r324WithinHalfPredecessorSlot
                data.geometry.trace.stopPrefix.state
                data.geometry.terminalData.terminal)
              (x - z) *
            ∫ u :
                Fin
                    (2 * residualBlockOrder
                      data.geometry.terminalData.terminal.2 - 2) →
                  T4,
              data.geometry.terminalCompletePrimitiveDensity
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
          (lamEps lam ε ^
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2) *
            ∫ u :
                Fin
                    (2 * residualBlockOrder
                      data.geometry.terminalData.terminal.2 - 2) →
                  T4,
              data.geometry.terminalCompletePrimitiveDensity
                (primitiveAssemble
                  (residualBlockOrder
                    data.geometry.terminalData.terminal.2)
                  (data.geometry.trace.stopPrefix.headContext
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
                  z w u)
              ∂Measure.pi fun _ => paperMeasure) := by
      ring
    _ = _ := by
      rw [
        data.geometry.lamEps_pow_integral_terminalCompletePrimitiveDensity_eq_primitiveKernel
          z w hint]

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
