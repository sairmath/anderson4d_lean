import Anderson4D.DetParametrix.Paper42_Moment.R324ShortcutStopTraceAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointAggregate

/-!
# Outgoing Fourier integration before the terminal shortcut collapse

For an arbitrary certified within-half step whose outgoing named edge is
still `greenFn`, this file removes that edge from the translated raw local
density and Fourier-integrates the resulting Green difference exactly.
The predecessor edge, internal primitive chain, and complete primitive
covariance sum remain grouped in one scalar.

The consumer at the end specializes this identity to the retained head of
`R324ShortcutStopTraceAssembly`; its outgoing-Green hypothesis follows
from reachability.  Every result here is for one fixed block tuple and one
fixed outer factor.  No block-coordinate Fubini exchange, residual-sum
interchange, or global R-324 closure is asserted.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfStepContext

variable {m : ℕ} {κ : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext κ)

/-- The first point of the translated primitive block. -/
def outgoingBlockFirst
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) : T4 :=
  t ⟨0, by
    have hn := ctx.one_le_blockOrder
    omega⟩

/-- The last point of the translated primitive block. -/
def outgoingBlockLast
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) : T4 :=
  t (primitiveLast
    (residualBlockOrder ctx.step.2)
    ctx.one_le_blockOrder)

/-- The translated raw local density with only the outgoing edge removed.
It retains the predecessor edge, primitive chain, and the full finite sum
over primitive covariance pairings. -/
def outgoingErasedTranslatedRawLocalCore
    (ρ : SmoothCutoff) (ε : ℝ) (x : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) : ℂ :=
  ((ctx.state.edges
        (r324WithinHalfPredecessorSlot ctx.state ctx.step)
        (x - ctx.outgoingBlockFirst t) *
      primitiveChainProduct
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges t *
      ∑ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1 t : ℝ) : ℂ)

/-- Exact pointwise factorization retaining the signed outgoing Green
difference. -/
theorem rawLocalIntegrand_translated_eq_outgoingCore_mul_greenDifference
    (ρ : SmoothCutoff) (ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    (ctx.rawLocalIntegrand ρ ε (x - y)
        (fun j => t j - y) : ℂ) =
      ctx.outgoingErasedTranslatedRawLocalCore ρ ε x t *
        ((greenFn (ctx.outgoingBlockLast t - y) : ℂ) -
          (greenFn (ctx.outgoingBlockFirst t - y) : ℂ)) := by
  rw [ctx.rawLocalIntegrand_translated ρ ε x y t, houtgoing]
  unfold outgoingErasedTranslatedRawLocalCore
  unfold outgoingBlockFirst outgoingBlockLast
  push_cast
  ring

/-- Kernel form of the exact outgoing factorization. -/
theorem rawLocalIntegrand_translated_eq_outgoingCore_mul_endpointKernel
    (ρ : SmoothCutoff) (ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    (ctx.rawLocalIntegrand ρ ε (x - y)
        (fun j => t j - y) : ℂ) =
      ctx.outgoingErasedTranslatedRawLocalCore ρ ε x t *
        r324OutgoingEndpointKernel
          (ctx.outgoingBlockLast t)
          (ctx.outgoingBlockFirst t) true y := by
  rw [
    ctx.rawLocalIntegrand_translated_eq_outgoingCore_mul_greenDifference
      ρ ε houtgoing x y t]
  simp only [r324OutgoingEndpointKernel, ↓reduceIte]

/-- **Fixed-tuple outgoing Fourier identity.**  Only the external variable
`y` is integrated; the block tuple and `outer` remain fixed. -/
theorem integral_char_mul_rawLocal_translated_eq_endpointCoefficient
    (ρ : SmoothCutoff) (ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (k : Z4) (x : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4)
    (outer : ℂ) :
    (∫ y : T4,
        charT4 k y *
          ((ctx.rawLocalIntegrand ρ ε (x - y)
              (fun j => t j - y) : ℂ) * outer)
        ∂paperMeasure) =
      ctx.outgoingErasedTranslatedRawLocalCore ρ ε x t *
        r324EndpointCoefficient k
          (ctx.outgoingBlockLast t)
          (ctx.outgoingBlockFirst t) true *
        outer := by
  have hpoint (y : T4) :
      charT4 k y *
          ((ctx.rawLocalIntegrand ρ ε (x - y)
              (fun j => t j - y) : ℂ) * outer) =
        (ctx.outgoingErasedTranslatedRawLocalCore ρ ε x t * outer) *
          (charT4 k y *
            r324OutgoingEndpointKernel
              (ctx.outgoingBlockLast t)
              (ctx.outgoingBlockFirst t) true y) := by
    rw [
      ctx.rawLocalIntegrand_translated_eq_outgoingCore_mul_endpointKernel
        ρ ε houtgoing x y t]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    integral_char_mul_r324OutgoingEndpointKernel]
  ring

/-- The fixed-tuple identity gains the expected second-order outgoing
multiplier, with the literal factor two from the endpoint difference. -/
theorem norm_integral_char_mul_rawLocal_translated_le
    (ρ : SmoothCutoff) (ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (k : Z4) (x : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4)
    (outer : ℂ) :
    ‖∫ y : T4,
        charT4 k y *
          ((ctx.rawLocalIntegrand ρ ε (x - y)
              (fun j => t j - y) : ℂ) * outer)
        ∂paperMeasure‖ ≤
      (‖ctx.outgoingErasedTranslatedRawLocalCore ρ ε x t‖ *
          (2 * paperSecondOrderModeDecay k)) *
        ‖outer‖ := by
  rw [
    ctx.integral_char_mul_rawLocal_translated_eq_endpointCoefficient
      ρ ε houtgoing k x t outer,
    norm_mul, norm_mul]
  have hcoefficient :
      ‖r324EndpointCoefficient k
          (ctx.outgoingBlockLast t)
          (ctx.outgoingBlockFirst t) true‖ ≤
        2 * paperSecondOrderModeDecay k := by
    simpa using
      norm_r324EndpointCoefficient_le k
        (ctx.outgoingBlockLast t)
        (ctx.outgoingBlockFirst t) true
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoefficient (norm_nonneg _))
      (norm_nonneg _)

end R324WithinHalfStepContext

namespace R324WithinHalfResidualPrefix

namespace R324ShortcutStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The retained shortcut head as a generic within-half step context. -/
def terminalContext
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    R324WithinHalfStepContext κ :=
  data.trace.stopPrefix.headContext
    data.terminalData.terminal []
    data.stop_remaining_eq_singleton

/-- Reachability automatically supplies the outgoing-Green hypothesis for
the retained shortcut head. -/
theorem terminalContext_outgoing_eq_greenFn
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale) :
    data.terminalContext.state.edges
        data.terminalContext.outgoingSlot =
      greenFn := by
  change
    data.trace.stopPrefix.state.edges
        (r324InternalVertexEdgeSlot
          data.terminalData.terminal.1.2) =
      greenFn
  exact
    data.trace.stopPrefix.state_edges_head_outgoing_eq_greenFn
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton

/-- Shortcut-stop consumer of the generic fixed-tuple Fourier identity. -/
theorem integral_char_mul_terminal_rawLocal_translated_eq
    (data :
      R324ShortcutStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (x : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4)
    (outer : ℂ) :
    (∫ y : T4,
        charT4 k y *
          ((data.terminalContext.rawLocalIntegrand
              ρ ε (x - y) (fun j => t j - y) : ℂ) * outer)
        ∂paperMeasure) =
      data.terminalContext.outgoingErasedTranslatedRawLocalCore
          ρ ε x t *
        r324EndpointCoefficient k
          (data.terminalContext.outgoingBlockLast t)
          (data.terminalContext.outgoingBlockFirst t) true *
        outer :=
  data.terminalContext
    |>.integral_char_mul_rawLocal_translated_eq_endpointCoefficient
      ρ ε data.terminalContext_outgoing_eq_greenFn k x t outer

end R324ShortcutStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
