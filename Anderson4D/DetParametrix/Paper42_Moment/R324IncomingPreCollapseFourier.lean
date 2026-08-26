import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalStop
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointAggregate

/-!
# Incoming Fourier integration before an exceptional R-324 collapse

At an exceptional incoming step, the incoming external Green edge must be
Fourier-integrated before the block is absorbed into slot zero.  This file
proves that exact local identity for a fixed translated block tuple.  The
primitive-pairing sum stays grouped and no block-coordinate integral is
reordered.

The later global bridge must still transport the original refined physical
integral to this reachable pre-step state and justify the corresponding
joint Fubini exchange.
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

/-- The translated raw local factor after removing only its incoming
predecessor edge.  The outgoing signed difference and the complete
primitive covariance sum remain literal. -/
def incomingErasedTranslatedRawLocalCore
    (ρ : SmoothCutoff) (ε : ℝ) (a : T4)
    (t :
      Fin (2 * residualBlockOrder ctx.step.2) → T4) : ℂ :=
  ((primitiveChainProduct
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges t *
      (ctx.state.edges ctx.outgoingSlot
          (t (primitiveLast
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder) - a) -
        ctx.state.edges ctx.outgoingSlot
          (t ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩ - a)) *
      ∑ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1 t : ℝ) : ℂ)

/-- Pointwise separation of the untouched incoming Green edge from the
translated raw local density. -/
theorem rawLocalIntegrand_translated_eq_incomingGreen_mul_core
    (ρ : SmoothCutoff) (ε : ℝ)
    (hincoming :
      ctx.state.edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) =
        greenFn)
    (x a : T4)
    (t :
      Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    (ctx.rawLocalIntegrand ρ ε (x - a)
        (fun j => t j - a) : ℂ) =
      (greenFn
          (x - t ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩) : ℂ) *
        ctx.incomingErasedTranslatedRawLocalCore ρ ε a t := by
  rw [ctx.rawLocalIntegrand_translated ρ ε x a t, hincoming]
  unfold incomingErasedTranslatedRawLocalCore
  push_cast
  ring

/-- **Exact local pre-collapse Fourier identity.**  The incoming external
variable is integrated while its edge is still the free Green kernel.
Every other local factor, including the signed primitive sum, is a literal
constant with respect to that variable. -/
theorem integral_char_mul_rawLocal_translated_eq
    (ρ : SmoothCutoff) (ε : ℝ)
    (hincoming :
      ctx.state.edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) =
        greenFn)
    (k : Z4) (a : T4)
    (t :
      Fin (2 * residualBlockOrder ctx.step.2) → T4)
    (outer : ℂ) :
    (∫ x : T4,
        charT4 k x *
          ((ctx.rawLocalIntegrand ρ ε (x - a)
              (fun j => t j - a) : ℂ) * outer)
        ∂paperMeasure) =
      translatedGreenMode k
          (t ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩) *
        ctx.incomingErasedTranslatedRawLocalCore ρ ε a t *
        outer := by
  have hpoint (x : T4) :
      charT4 k x *
          ((ctx.rawLocalIntegrand ρ ε (x - a)
              (fun j => t j - a) : ℂ) * outer) =
        (charT4 k x *
            (greenFn
              (x - t ⟨0, by
                have hn := ctx.one_le_blockOrder
                omega⟩) : ℂ)) *
          (ctx.incomingErasedTranslatedRawLocalCore ρ ε a t *
            outer) := by
    rw [
      ctx.rawLocalIntegrand_translated_eq_incomingGreen_mul_core
        ρ ε hincoming x a t]
    ring
  simp_rw [hpoint]
  rw [integral_mul_const]
  unfold translatedGreenMode
  ring

/-- Norm form of the local incoming Fourier identity. -/
theorem norm_integral_char_mul_rawLocal_translated_eq
    (ρ : SmoothCutoff) (ε : ℝ)
    (hincoming :
      ctx.state.edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) =
        greenFn)
    (k : Z4) (a : T4)
    (t :
      Fin (2 * residualBlockOrder ctx.step.2) → T4)
    (outer : ℂ) :
    ‖∫ x : T4,
        charT4 k x *
          ((ctx.rawLocalIntegrand ρ ε (x - a)
              (fun j => t j - a) : ℂ) * outer)
        ∂paperMeasure‖ =
      paperSecondOrderModeDecay k *
        ‖ctx.incomingErasedTranslatedRawLocalCore ρ ε a t‖ *
        ‖outer‖ := by
  rw [
    ctx.integral_char_mul_rawLocal_translated_eq
      ρ ε hincoming k a t outer,
    norm_mul, norm_mul, norm_translatedGreenMode]

end R324WithinHalfStepContext

namespace R324IncomingExceptionalStop

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (stop : R324IncomingExceptionalStop ρ lam ε κ)

/-- Consumer form for the genuine exceptional stop constructed from the
analytic schedule. -/
theorem integral_char_mul_rawLocal_translated_eq
    (hm : 0 < m)
    (k : Z4) (a : T4)
    (t :
      Fin (2 * residualBlockOrder stop.ctx.step.2) → T4)
    (outer : ℂ) :
    (∫ x : T4,
        charT4 k x *
          ((stop.ctx.rawLocalIntegrand ρ ε (x - a)
              (fun j => t j - a) : ℂ) * outer)
        ∂paperMeasure) =
      translatedGreenMode k
          (t ⟨0, by
            have hn := stop.ctx.one_le_blockOrder
            omega⟩) *
        stop.ctx.incomingErasedTranslatedRawLocalCore ρ ε a t *
        outer :=
  stop.ctx.integral_char_mul_rawLocal_translated_eq
    ρ ε (stop.state_edge_predecessor_eq_greenFn hm)
    k a t outer

/-- The genuine exceptional stop gains exactly one second-order incoming
Green multiplier before its slot-zero collapse. -/
theorem norm_integral_char_mul_rawLocal_translated_eq
    (hm : 0 < m)
    (k : Z4) (a : T4)
    (t :
      Fin (2 * residualBlockOrder stop.ctx.step.2) → T4)
    (outer : ℂ) :
    ‖∫ x : T4,
        charT4 k x *
          ((stop.ctx.rawLocalIntegrand ρ ε (x - a)
              (fun j => t j - a) : ℂ) * outer)
        ∂paperMeasure‖ =
      paperSecondOrderModeDecay k *
        ‖stop.ctx.incomingErasedTranslatedRawLocalCore ρ ε a t‖ *
        ‖outer‖ :=
  stop.ctx.norm_integral_char_mul_rawLocal_translated_eq
    ρ ε (stop.state_edge_predecessor_eq_greenFn hm)
    k a t outer

end R324IncomingExceptionalStop

end

end Anderson4D
