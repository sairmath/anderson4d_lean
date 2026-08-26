import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalTraceFourierBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhaseAnchorGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingHeadGapReindex
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseATerminalBlockUpdate
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAProperBlockUpdate
import Anderson4D.DetParametrix.Paper42_Moment.R324Step4CosineLoss
import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyConservation

/-!
# The first Step-4 unit after an incoming exceptional Fourier stop

At an exceptional incoming stop, endpoint Fourier integration leaves its
character at the first point of the retained primitive block.  This file
performs the next local operation, before any suffix iteration:

* expose the exact Green multiplier and the retained head character;
* route that character across the outgoing signed difference;
* identify the resulting gap factor as
  `charT4 (-k) u - 1`, for `u = z - w`;
* reduce this complex defect to the real cosine defect and charge it with
  the ordinary half of Proposition 4.1.

The after-head coordinates and their outer factor remain fixed throughout.
No claim about propagation of the transported character through a later
suffix block is made here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-! ## Exposing the phase left by the incoming endpoint integral -/

/-- The stop Fourier density contains exactly one head character and one
paper Green multiplier.  Everything depending on the after-head tuple is
left untouched. -/
theorem incomingExceptionalStopFourierDensity_eq_phase
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (t : Fin (2 * residualBlockOrder data.terminal.2) → T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) :
    data.incomingExceptionalStopFourierDensity
        k y postOuter (ω, t, v) =
      (paperSecondOrderModeDecay k : ℂ) *
        charT4 k
          (t ⟨0, by
            have hn := data.stopContext.one_le_blockOrder
            exact Nat.mul_pos (by decide)
              (Nat.zero_lt_of_lt hn)⟩) *
        data.stopContext.incomingErasedTranslatedRawLocalCore
          ρ ε
          (data.trace.stopPrefix.headSuccessorPoint
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            0 (y ω) v)
          t *
        ((data.trace.stopPrefix.headOuterFactor
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            ρ ε 0 (y ω) v : ℂ) *
          postOuter ω v) := by
  unfold incomingExceptionalStopFourierDensity
  rw [translatedGreenMode_eq]
  unfold paperSecondOrderModeDecay paperModeNormSq
  ring

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

/-! ## Routing a head character through the outgoing difference -/

/-- The Fourier mode of the outgoing edge, translated to the genuine
after-head successor.  This is the factor that carries the character into
the remaining suffix. -/
def incomingExceptionalTransportedMode
    (k : Z4) (a : T4) (H : T4 → ℝ) : ℂ :=
  ∫ q : T4,
    charT4 k q * (H (q - a) : ℂ)
    ∂paperMeasure

/-- The complex Step-4 defect before the `𝓔` cosine reduction. -/
def incomingExceptionalPrimitiveDefect
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (k : Z4) : ℂ :=
  ∫ u : T4,
    (primitiveKernelDiff ρ lam ε n hn G u : ℂ) *
      (charT4 (-k) u - 1)
    ∂paperMeasure

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- At a genuine exceptional stop the outgoing edge of the retained head
is still the free Green kernel.  Hence its transported mode is exactly the
standard translated Green mode. -/
theorem incomingExceptionalTransportedMode_eq_translatedGreenMode
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (a : T4) :
    incomingExceptionalTransportedMode k a
        (data.stopContext.state.edges
          data.stopContext.outgoingSlot) =
      translatedGreenMode k a := by
  have hout :=
    data.trace.stopPrefix.state_edges_head_outgoing_eq_greenFn
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  change
    data.stopContext.state.edges
        data.stopContext.outgoingSlot =
      greenFn at hout
  rw [hout]
  rfl

/-- The outgoing Fourier section required by the exact head theorem is
automatically integrable at a genuine exceptional stop. -/
theorem integrable_char_mul_stopOutgoing_sub
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (a : T4) :
    Integrable
      (fun q : T4 =>
        charT4 k q *
          (data.stopContext.state.edges
            data.stopContext.outgoingSlot (q - a) : ℂ))
      paperMeasure := by
  have hout :=
    data.trace.stopPrefix.state_edges_head_outgoing_eq_greenFn
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  change
    data.stopContext.state.edges
        data.stopContext.outgoingSlot =
      greenFn at hout
  rw [hout]
  exact
    (integrable_greenFn_sub a).ofReal.bdd_mul
      (c := 1)
      (continuous_charT4 k).measurable.aestronglyMeasurable
      (.of_forall fun q => by
        rw [norm_charT4])

/-- The genuine post-head successor is the phase anchor of the residual
suffix.  The outgoing mode therefore contributes one further Green decay
and places the character on that named anchor. -/
theorem incomingExceptionalTransportedMode_eq_decay_mul_afterHeadAnchor
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4) (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) :
    incomingExceptionalTransportedMode k
        (data.trace.stopPrefix.headSuccessorPoint
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq
          0 (y ω) v)
        (data.stopContext.state.edges
          data.stopContext.outgoingSlot) =
      (paperSecondOrderModeDecay k : ℂ) *
        charT4 k
          ((data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).incomingPhaseAnchor
              0 (y ω) v) := by
  have hanchor :=
    data.trace.stopPrefix.incomingPhaseAnchor_afterHead_eq_headSuccessorPoint
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      data.stop_predecessorSlot_eq_zero
      0 (y ω) v
  rw [data.incomingExceptionalTransportedMode_eq_translatedGreenMode]
  rw [translatedGreenMode_eq]
  unfold paperSecondOrderModeDecay paperModeNormSq
  rw [hanchor]
  ring

/-- Consumer form for the exact head theorem: the incoming Green endpoint
and the genuine outgoing Green edge contribute two paper second-order
decays, while all remaining scalar data is carried unchanged. -/
theorem paperDecay_mul_incomingExceptionalTransportedMode_mul_eq_anchor
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4) (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4)
    (payload : ℂ) :
    (paperSecondOrderModeDecay k : ℂ) *
        incomingExceptionalTransportedMode k
          (data.trace.stopPrefix.headSuccessorPoint
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            0 (y ω) v)
          (data.stopContext.state.edges
            data.stopContext.outgoingSlot) *
        payload =
      (paperSecondOrderModeDecay k : ℂ) ^ 2 *
        charT4 k
          ((data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).incomingPhaseAnchor
              0 (y ω) v) *
        payload := by
  rw [
    data.incomingExceptionalTransportedMode_eq_decay_mul_afterHeadAnchor
      k y ω v]
  ring

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

namespace R324WithinHalfStepContext

variable {m : ℕ} {κ : PartialPairing (Fin m)}

/-- The post-Fourier raw head core is the complete signed primitive sum
times its literal outgoing edge difference.  This is the pointwise bridge
from the genuine stop density to the standard Proposition 4.1 kernel. -/
theorem incomingErasedTranslatedRawLocalCore_eq_completePrimitive_mul_outgoingDifference
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (ε : ℝ) (a : T4)
    (t :
      Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.incomingErasedTranslatedRawLocalCore ρ ε a t =
      (((∑ κB :
            {κB : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κB ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          detJclosedIntegrandWith ρ ε
            (2 * residualBlockOrder ctx.step.2)
            κB.1 ctx.internalEdges t) *
        (ctx.state.edges ctx.outgoingSlot
            (t (primitiveLast
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder) - a) -
          ctx.state.edges ctx.outgoingSlot
            (t ⟨0, by
              have hn := ctx.one_le_blockOrder
              exact Nat.mul_pos (by decide)
                (Nat.zero_lt_of_lt hn)⟩ - a)) : ℝ) : ℂ) := by
  have hcov :
      (∑ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1 t) =
        ∑ κB ∈
            primitiveFullPairings
              (residualBlockOrder ctx.step.2),
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder ctx.step.2) κB t := by
    symm
    apply Finset.sum_subtype
    intro κB
    rfl
  rw [
    sum_terminal_detJclosedIntegrandWith_eq_primitiveIntegrand
      ρ ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges t]
  unfold incomingErasedTranslatedRawLocalCore
  rw [hcov]
  simp only [primitiveIntegrand]
  push_cast
  rw [← Finset.mul_sum]
  ring

end R324WithinHalfStepContext

/-- Translation invariance of every generalized primitive summand gives the
one-gap form of the complete primitive kernel. -/
theorem primitiveKernel_eq_primitiveKernelDiff_sub
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    primitiveKernel ρ lam ε n hn G z w =
      primitiveKernelDiff ρ lam ε n hn G (z - w) := by
  calc
    primitiveKernel ρ lam ε n hn G z w =
        ∑ κB ∈ primitiveFullPairings n,
          detJWith ρ lam ε n hn G κB z w := by
            symm
            exact
              sum_detJWith_primitive_eq_primitiveKernel
                ρ lam ε n hn G z w
    _ =
        ∑ κB ∈ primitiveFullPairings n,
          detJWith ρ lam ε n hn G κB (z - w) 0 := by
            apply Finset.sum_congr rfl
            intro κB _hκB
            exact detJWith_eq_diff
              ρ lam ε n hn G κB z w
    _ = primitiveKernel ρ lam ε n hn G (z - w) 0 :=
      sum_detJWith_primitive_eq_primitiveKernel
        ρ lam ε n hn G (z - w) 0
    _ = _ := by
      rfl

namespace R324WithinHalfStepContext

/-- Integrating the internal coordinates of the genuine post-Fourier head
core produces the ordinary primitive kernel, while the outgoing signed
difference remains literal. -/
theorem lamEps_pow_integral_incomingErasedTranslatedRawLocalCore_eq
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (a first last : T4)
    (hint :
      ∀ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder first last r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder ctx.step.2) *
        (∫ r :
            Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ctx.incomingErasedTranslatedRawLocalCore
            ρ ε a
            (primitiveAssemble
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder first last r)
          ∂Measure.pi fun _ => paperMeasure) =
      ((primitiveKernelDiff ρ lam ε
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges
          (first - last) *
        (ctx.state.edges ctx.outgoingSlot (last - a) -
          ctx.state.edges ctx.outgoingSlot (first - a)) : ℝ) : ℂ) := by
  let D : ℝ :=
    ctx.state.edges ctx.outgoingSlot (last - a) -
      ctx.state.edges ctx.outgoingSlot (first - a)
  let S :
      (Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4) → ℝ :=
    fun r =>
      ∑ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        detJclosedIntegrandWith ρ ε
          (2 * residualBlockOrder ctx.step.2)
          κB.1 ctx.internalEdges
          (primitiveAssemble
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder first last r)
  have hpoint
      (r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4) :
      ctx.incomingErasedTranslatedRawLocalCore
          ρ ε a
          (primitiveAssemble
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder first last r) =
        ((S r * D : ℝ) : ℂ) := by
    rw [
      ctx.incomingErasedTranslatedRawLocalCore_eq_completePrimitive_mul_outgoingDifference]
    simp only [primitiveAssemble_zero, primitiveAssemble_last]
    rfl
  have hintegral :
      (∫ r :
          Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
        ctx.incomingErasedTranslatedRawLocalCore
          ρ ε a
          (primitiveAssemble
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder first last r)
        ∂Measure.pi fun _ => paperMeasure) =
      (((∫ r :
          Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
        S r * D
        ∂Measure.pi fun _ => paperMeasure) : ℝ) : ℂ) := by
    calc
      _ =
          ∫ r :
              Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
            ((S r * D : ℝ) : ℂ)
            ∂Measure.pi fun _ => paperMeasure := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_ofReal
  rw [hintegral]
  rw [integral_mul_const]
  push_cast
  rw [← mul_assoc]
  have hkernel :=
    integral_sum_terminal_detJclosedIntegrandWith_eq_primitiveKernel
      ρ lam ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges first last hint
  have hkernelC :=
    congrArg (fun z : ℝ => (z : ℂ)) hkernel
  push_cast at hkernelC
  rw [hkernelC]
  rw [
    primitiveKernel_eq_primitiveKernelDiff_sub
      ρ lam ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges first last]
  dsimp only [D]
  push_cast
  ring

end R324WithinHalfStepContext

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- Fixed after-head coordinates, fixed gap, and fixed first endpoint:
the genuine stop Fourier density integrates in its internal primitive
coordinates to the ordinary `primitiveKernelDiff`, with the transported
head character and outgoing edge difference still exact. -/
theorem lamEps_pow_integral_incomingExceptionalStopFourierDensity_internal_eq
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4)
    (gap first : T4)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)},
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ r :
            Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
          data.incomingExceptionalStopFourierDensity
            k y postOuter
            (ω,
              primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r,
              v)
          ∂Measure.pi fun _ => paperMeasure) =
      (paperSecondOrderModeDecay k : ℂ) *
        charT4 k first *
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges gap : ℂ) *
        ((data.stopContext.state.edges data.stopContext.outgoingSlot
            ((first + gap) -
              data.trace.stopPrefix.headSuccessorPoint
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                0 (y ω) v) -
          data.stopContext.state.edges data.stopContext.outgoingSlot
            (first -
              data.trace.stopPrefix.headSuccessorPoint
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                0 (y ω) v) : ℝ) : ℂ) *
        ((data.trace.stopPrefix.headOuterFactor
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            ρ ε 0 (y ω) v : ℂ) *
          postOuter ω v) := by
  let a : T4 :=
    data.trace.stopPrefix.headSuccessorPoint
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      0 (y ω) v
  let outer : ℂ :=
    (data.trace.stopPrefix.headOuterFactor
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      ρ ε 0 (y ω) v : ℂ) *
        postOuter ω v
  let core :
      (Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4) → ℂ :=
    fun r =>
      data.stopContext.incomingErasedTranslatedRawLocalCore
        ρ ε a
        (primitiveAssemble
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          first (first + gap) r)
  have hpoint
      (r : Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4) :
      data.incomingExceptionalStopFourierDensity
          k y postOuter
          (ω,
            primitiveAssemble
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              first (first + gap) r,
            v) =
        (paperSecondOrderModeDecay k : ℂ) *
          charT4 k first * core r * outer := by
    rw [data.incomingExceptionalStopFourierDensity_eq_phase]
    simp only [primitiveAssemble_zero]
    rfl
  have hcore :=
    data.stopContext
      |>.lamEps_pow_integral_incomingErasedTranslatedRawLocalCore_eq
        ρ lam ε a first (first + gap) hint
  unfold R324IncomingExceptionalStopTraceAssembly.stopContext at hcore
  unfold R324WithinHalfResidualPrefix.headContext at hcore
  have hcore' :
      (lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder data.terminal.2) *
          (∫ r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
            core r
            ∂Measure.pi fun _ => paperMeasure) =
        ((primitiveKernelDiff ρ lam ε
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges
            (first - (first + gap)) *
          (data.stopContext.state.edges data.stopContext.outgoingSlot
              ((first + gap) - a) -
            data.stopContext.state.edges data.stopContext.outgoingSlot
              (first - a)) : ℝ) : ℂ) := by
    dsimp only [core]
    unfold R324IncomingExceptionalStopTraceAssembly.stopContext
    unfold R324WithinHalfResidualPrefix.headContext
    exact hcore
  have hJ :
      MemEClassT4
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges) :=
    primitiveKernelDiff_memE ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges hG
  have hgap :
      primitiveKernelDiff ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges
          (first - (first + gap)) =
        primitiveKernelDiff ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges gap := by
    have hsub : first - (first + gap) = -gap := by
      abel
    rw [hsub, hJ.neg_invariant]
  calc
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ r :
            Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
          data.incomingExceptionalStopFourierDensity
            k y postOuter
            (ω,
              primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r,
              v)
          ∂Measure.pi fun _ => paperMeasure) =
        (lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder data.terminal.2) *
          (∫ r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
            (paperSecondOrderModeDecay k : ℂ) *
              charT4 k first * core r * outer
            ∂Measure.pi fun _ => paperMeasure) := by
              apply congrArg
                (fun z : ℂ =>
                  (lamEps lam ε : ℂ) ^
                    (2 * residualBlockOrder data.terminal.2) * z)
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hpoint
    _ =
        (paperSecondOrderModeDecay k : ℂ) *
          charT4 k first *
          ((lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder data.terminal.2) *
            ∫ r :
                Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
              core r
              ∂Measure.pi fun _ => paperMeasure) *
          outer := by
            rw [integral_mul_const, integral_const_mul]
            ring
    _ =
        (paperSecondOrderModeDecay k : ℂ) *
          charT4 k first *
          ((primitiveKernelDiff ρ lam ε
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              data.stopContext.internalEdges
              (first - (first + gap)) *
            (data.stopContext.state.edges data.stopContext.outgoingSlot
                ((first + gap) - a) -
              data.stopContext.state.edges data.stopContext.outgoingSlot
                (first - a)) : ℝ) : ℂ) *
          outer := by
            rw [hcore']
    _ = _ := by
      rw [hgap]
      dsimp only [a, outer]
      push_cast
      ring

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

/-- For the gap orientation `u = z - w`, translating the `z` term of the
outgoing signed difference leaves exactly
`charT4 (-k) u - 1`.  The assumptions are only those needed to split the
Bochner integral of the signed difference. -/
theorem integrable_char_mul_outgoing_shift_of_base
    (k : Z4) (a u : T4) (H : T4 → ℝ)
    (hbase :
      Integrable
        (fun w : T4 =>
          charT4 k w * (H (w - a) : ℂ))
        paperMeasure) :
    Integrable
      (fun w : T4 =>
        charT4 k w * (H ((w + u) - a) : ℂ))
      paperMeasure := by
  have hp :
      MeasurePreserving
        (fun w : T4 => w + u)
        paperMeasure paperMeasure := by
    rw [paperMeasure_eq_volume]
    exact measurePreserving_add_right
      (volume : Measure T4) u
  let F : T4 → ℂ :=
    fun q =>
      charT4 k (q - u) * (H (q - a) : ℂ)
  have hF : Integrable F paperMeasure := by
    have hc :
        Integrable
          (fun q : T4 =>
            charT4 (-k) u *
              (charT4 k q * (H (q - a) : ℂ)))
          paperMeasure :=
      hbase.const_mul (charT4 (-k) u)
    exact hc.congr (.of_forall fun q => by
      unfold F
      rw [charT4_sub_argument]
      ring)
  have hcomp :=
    (hp.integrable_comp hF.aestronglyMeasurable).mpr hF
  exact hcomp.congr (.of_forall fun w => by
    change
      F (w + u) =
        charT4 k w * (H ((w + u) - a) : ℂ)
    unfold F
    rw [add_sub_cancel_right])

/-- For the gap orientation `u = z - w`, translating the `z` term of the
outgoing signed difference leaves exactly
`charT4 (-k) u - 1`.  The sole integrability premise is the untranslated
outgoing Fourier section; translation invariance supplies the shifted
section automatically. -/
theorem integral_char_mul_outgoingDifference_eq_defect_mul_transportedMode
    (k : Z4) (a u : T4) (H : T4 → ℝ)
    (hbase :
      Integrable
        (fun w : T4 =>
          charT4 k w * (H (w - a) : ℂ))
        paperMeasure) :
    (∫ w : T4,
        charT4 k w *
          ((H ((w + u) - a) - H (w - a) : ℝ) : ℂ)
        ∂paperMeasure) =
      (charT4 (-k) u - 1) *
        incomingExceptionalTransportedMode k a H := by
  have hshift :=
    integrable_char_mul_outgoing_shift_of_base
      k a u H hbase
  let F : T4 → ℂ :=
    fun q =>
      charT4 k (q - u) * (H (q - a) : ℂ)
  have htranslate :
      (∫ w : T4,
          charT4 k w * (H ((w + u) - a) : ℂ)
          ∂paperMeasure) =
        charT4 (-k) u *
          incomingExceptionalTransportedMode k a H := by
    calc
      (∫ w : T4,
          charT4 k w * (H ((w + u) - a) : ℂ)
          ∂paperMeasure) =
          ∫ w : T4, F (w + u) ∂paperMeasure := by
            apply integral_congr_ae
            filter_upwards with w
            unfold F
            rw [add_sub_cancel_right]
      _ = ∫ q : T4, F q ∂paperMeasure := by
            rw [paperMeasure_eq_volume]
            simpa only using
              integral_add_right_eq_self F u
      _ =
          ∫ q : T4,
            charT4 (-k) u *
              (charT4 k q * (H (q - a) : ℂ))
            ∂paperMeasure := by
              apply integral_congr_ae
              filter_upwards with q
              unfold F
              rw [charT4_sub_argument]
              ring
      _ =
          charT4 (-k) u *
            incomingExceptionalTransportedMode k a H := by
              rw [integral_const_mul]
              rfl
  calc
    (∫ w : T4,
        charT4 k w *
          ((H ((w + u) - a) - H (w - a) : ℝ) : ℂ)
        ∂paperMeasure) =
      (∫ w : T4,
          charT4 k w * (H ((w + u) - a) : ℂ)
          ∂paperMeasure) -
        ∫ w : T4,
          charT4 k w * (H (w - a) : ℂ)
          ∂paperMeasure := by
            rw [← integral_sub hshift hbase]
            apply integral_congr_ae
            filter_upwards with w
            push_cast
            ring
    _ = _ := by
      rw [htranslate]
      unfold incomingExceptionalTransportedMode
      ring

/-- After the outgoing coordinate is integrated, the whole two-endpoint
phase is the transported Fourier mode times the one-variable primitive
defect.  This is the exact transported/base-plus-defect decomposition used
before taking any norm. -/
theorem integral_kernel_mul_char_outgoingDifference_eq_transportedMode_mul_defect
    (k : Z4) (a : T4) (H J : T4 → ℝ)
    (hbase :
      Integrable
        (fun w : T4 =>
          charT4 k w * (H (w - a) : ℂ))
        paperMeasure) :
    (∫ u : T4,
        (J u : ℂ) *
          (∫ w : T4,
            charT4 k w *
              ((H ((w + u) - a) - H (w - a) : ℝ) : ℂ)
            ∂paperMeasure)
        ∂paperMeasure) =
      incomingExceptionalTransportedMode k a H *
        ∫ u : T4,
          (J u : ℂ) * (charT4 (-k) u - 1)
          ∂paperMeasure := by
  simp_rw [
    integral_char_mul_outgoingDifference_eq_defect_mul_transportedMode
      k a _ H hbase]
  calc
    (∫ u : T4,
        (J u : ℂ) *
          ((charT4 (-k) u - 1) *
            incomingExceptionalTransportedMode k a H)
        ∂paperMeasure) =
      ∫ u : T4,
        ((J u : ℂ) * (charT4 (-k) u - 1)) *
          incomingExceptionalTransportedMode k a H
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with u
          ring
    _ =
        (∫ u : T4,
          (J u : ℂ) * (charT4 (-k) u - 1)
          ∂paperMeasure) *
          incomingExceptionalTransportedMode k a H := by
      rw [integral_mul_const]
    _ = _ := by ring

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- **Exact fixed-post head decomposition.**

The actual incoming exceptional stop density is integrated in the
reindexed head coordinates
`(gap, first, internal)`, where the last endpoint is `first + gap`.
The result is the transported outgoing Fourier mode times the single
ordinary primitive defect.  No norm and no suffix estimate occurs in this
identity. -/
theorem
    integral_lamEps_pow_incomingExceptionalStopFourierDensity_head_eq_transportedMode_mul_defect
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4)
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hbase :
      Integrable
        (fun first : T4 =>
          charT4 k first *
            (data.stopContext.state.edges
              data.stopContext.outgoingSlot
              (first -
                data.trace.stopPrefix.headSuccessorPoint
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  0 (y ω) v) : ℂ))
        paperMeasure) :
    (∫ gap : T4,
        ∫ first : T4,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder data.terminal.2) *
            (∫ r :
                Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
              data.incomingExceptionalStopFourierDensity
                k y postOuter
                (ω,
                  primitiveAssemble
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    first (first + gap) r,
                  v)
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure
        ∂paperMeasure) =
      (paperSecondOrderModeDecay k : ℂ) *
        incomingExceptionalTransportedMode k
          (data.trace.stopPrefix.headSuccessorPoint
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            0 (y ω) v)
          (data.stopContext.state.edges
            data.stopContext.outgoingSlot) *
        incomingExceptionalPrimitiveDefect ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges k *
        ((data.trace.stopPrefix.headOuterFactor
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            ρ ε 0 (y ω) v : ℂ) *
          postOuter ω v) := by
  let a : T4 :=
    data.trace.stopPrefix.headSuccessorPoint
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      0 (y ω) v
  let H : T4 → ℝ :=
    data.stopContext.state.edges data.stopContext.outgoingSlot
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges
  let outer : ℂ :=
    (data.trace.stopPrefix.headOuterFactor
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      ρ ε 0 (y ω) v : ℂ) *
        postOuter ω v
  have hfiber (gap first : T4) :
      (lamEps lam ε : ℂ) ^
            (2 * residualBlockOrder data.terminal.2) *
          (∫ r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
            data.incomingExceptionalStopFourierDensity
              k y postOuter
              (ω,
                primitiveAssemble
                  (residualBlockOrder data.terminal.2)
                  data.stopContext.one_le_blockOrder
                  first (first + gap) r,
                v)
            ∂Measure.pi fun _ => paperMeasure) =
        (paperSecondOrderModeDecay k : ℂ) *
          charT4 k first * (J gap : ℂ) *
          ((H ((first + gap) - a) -
            H (first - a) : ℝ) : ℂ) *
          outer := by
    exact
      data
        |>.lamEps_pow_integral_incomingExceptionalStopFourierDensity_internal_eq
          k y postOuter ω v gap first hG (hint gap first)
  have htransport :
      (∫ gap : T4,
          (J gap : ℂ) *
            (∫ first : T4,
              charT4 k first *
                ((H ((first + gap) - a) -
                  H (first - a) : ℝ) : ℂ)
              ∂paperMeasure)
          ∂paperMeasure) =
        incomingExceptionalTransportedMode k a H *
          ∫ gap : T4,
            (J gap : ℂ) * (charT4 (-k) gap - 1)
            ∂paperMeasure := by
    exact
      integral_kernel_mul_char_outgoingDifference_eq_transportedMode_mul_defect
        k a H J hbase
  calc
    (∫ gap : T4,
        ∫ first : T4,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder data.terminal.2) *
            (∫ r :
                Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
              data.incomingExceptionalStopFourierDensity
                k y postOuter
                (ω,
                  primitiveAssemble
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    first (first + gap) r,
                  v)
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure
        ∂paperMeasure) =
      ∫ gap : T4,
        ∫ first : T4,
          (paperSecondOrderModeDecay k : ℂ) *
            charT4 k first * (J gap : ℂ) *
            ((H ((first + gap) - a) -
              H (first - a) : ℝ) : ℂ) *
            outer
          ∂paperMeasure
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with gap
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (hfiber gap)
    _ =
      ∫ gap : T4,
        (paperSecondOrderModeDecay k : ℂ) *
          ((J gap : ℂ) *
            (∫ first : T4,
              charT4 k first *
                ((H ((first + gap) - a) -
                  H (first - a) : ℝ) : ℂ)
              ∂paperMeasure)) *
          outer
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with gap
          calc
            (∫ first : T4,
                (paperSecondOrderModeDecay k : ℂ) *
                  charT4 k first * (J gap : ℂ) *
                  ((H ((first + gap) - a) -
                    H (first - a) : ℝ) : ℂ) *
                  outer
                ∂paperMeasure) =
              ∫ first : T4,
                ((paperSecondOrderModeDecay k : ℂ) *
                  (J gap : ℂ)) *
                  (charT4 k first *
                    ((H ((first + gap) - a) -
                      H (first - a) : ℝ) : ℂ)) *
                  outer
                ∂paperMeasure := by
                  apply integral_congr_ae
                  filter_upwards with first
                  ring
            _ = _ := by
              rw [integral_mul_const, integral_const_mul]
              ring
    _ =
      (paperSecondOrderModeDecay k : ℂ) *
        (∫ gap : T4,
          (J gap : ℂ) *
            (∫ first : T4,
              charT4 k first *
                ((H ((first + gap) - a) -
                  H (first - a) : ℝ) : ℂ)
              ∂paperMeasure)
          ∂paperMeasure) *
        outer := by
          rw [integral_mul_const, integral_const_mul]
    _ =
      (paperSecondOrderModeDecay k : ℂ) *
        (incomingExceptionalTransportedMode k a H *
          ∫ gap : T4,
            (J gap : ℂ) *
              (charT4 (-k) gap - 1)
            ∂paperMeasure) *
        outer := by
          rw [htransport]
    _ = _ := by
      dsimp only [a, H, J, outer]
      unfold incomingExceptionalPrimitiveDefect
      ring

/-- Original-head-measure form of the preceding decomposition.  The
measure-preserving primitive-head gap shear is applied once, and the
perturbative power remains outside the raw head integral until that exact
reindexing has been performed. -/
theorem
    lamEps_pow_integral_incomingExceptionalStopFourierDensity_head_eq_transportedMode_mul_defect
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4)
    (hhead :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4 =>
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v))
        (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hbase :
      Integrable
        (fun first : T4 =>
          charT4 k first *
            (data.stopContext.state.edges
              data.stopContext.outgoingSlot
              (first -
                data.trace.stopPrefix.headSuccessorPoint
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  0 (y ω) v) : ℂ))
        paperMeasure) :
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4,
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v)
          ∂Measure.pi fun _ => paperMeasure) =
      (paperSecondOrderModeDecay k : ℂ) *
        incomingExceptionalTransportedMode k
          (data.trace.stopPrefix.headSuccessorPoint
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            0 (y ω) v)
          (data.stopContext.state.edges
            data.stopContext.outgoingSlot) *
        incomingExceptionalPrimitiveDefect ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges k *
        ((data.trace.stopPrefix.headOuterFactor
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            ρ ε 0 (y ω) v : ℂ) *
          postOuter ω v) := by
  let f :
      (Fin (2 * residualBlockOrder data.terminal.2) → T4) → ℂ :=
    fun t =>
      data.incomingExceptionalStopFourierDensity
        k y postOuter (ω, t, v)
  have hreindex :=
    integral_standardBlock_eq_integral_gap_first_internal
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder f hhead
  calc
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4,
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v)
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ gap : T4,
          ∫ first : T4,
            ∫ r :
                Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
              data.incomingExceptionalStopFourierDensity
                k y postOuter
                (ω,
                  primitiveAssemble
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    first (first + gap) r,
                  v)
              ∂Measure.pi fun _ => paperMeasure
            ∂paperMeasure
          ∂paperMeasure) := by
            exact congrArg
              (fun z : ℂ =>
                (lamEps lam ε : ℂ) ^
                  (2 * residualBlockOrder data.terminal.2) * z)
              hreindex
    _ =
      ∫ gap : T4,
        ∫ first : T4,
          (lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder data.terminal.2) *
            (∫ r :
                Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4,
              data.incomingExceptionalStopFourierDensity
                k y postOuter
                (ω,
                  primitiveAssemble
                    (residualBlockOrder data.terminal.2)
                    data.stopContext.one_le_blockOrder
                    first (first + gap) r,
                  v)
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure
        ∂paperMeasure := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with gap
          rw [← integral_const_mul]
    _ = _ :=
      data
        |>.integral_lamEps_pow_incomingExceptionalStopFourierDensity_head_eq_transportedMode_mul_defect
          k y postOuter ω v hG hint hbase

/-- Genuine-stop anchor form.  The outgoing-section integrability premise
is discharged by the untouched Green edge, and the exact coefficient is
the square of the paper second-order decay. -/
theorem
    lamEps_pow_integral_incomingExceptionalStopFourierDensity_head_eq_decay_sq_mul_anchor
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4)
    (hhead :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4 =>
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v))
        (Measure.pi fun _ => paperMeasure))
    (hG :
      ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4,
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v)
          ∂Measure.pi fun _ => paperMeasure) =
      (paperSecondOrderModeDecay k : ℂ) ^ 2 *
        charT4 k
          ((data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).incomingPhaseAnchor
              0 (y ω) v) *
        incomingExceptionalPrimitiveDefect ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges k *
        ((data.trace.stopPrefix.headOuterFactor
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq
            ρ ε 0 (y ω) v : ℂ) *
          postOuter ω v) := by
  let a : T4 :=
    data.trace.stopPrefix.headSuccessorPoint
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      0 (y ω) v
  let defect : ℂ :=
    incomingExceptionalPrimitiveDefect ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges k
  let outer : ℂ :=
    (data.trace.stopPrefix.headOuterFactor
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      ρ ε 0 (y ω) v : ℂ) *
        postOuter ω v
  have hbase :
      Integrable
        (fun first : T4 =>
          charT4 k first *
            (data.stopContext.state.edges
              data.stopContext.outgoingSlot
              (first - a) : ℂ))
        paperMeasure :=
    data.integrable_char_mul_stopOutgoing_sub k a
  have hmain :=
    data
      |>.lamEps_pow_integral_incomingExceptionalStopFourierDensity_head_eq_transportedMode_mul_defect
        k y postOuter ω v hhead hG hint hbase
  calc
    (lamEps lam ε : ℂ) ^
          (2 * residualBlockOrder data.terminal.2) *
        (∫ t :
            Fin (2 * residualBlockOrder data.terminal.2) → T4,
          data.incomingExceptionalStopFourierDensity
            k y postOuter (ω, t, v)
          ∂Measure.pi fun _ => paperMeasure) =
      (paperSecondOrderModeDecay k : ℂ) *
        incomingExceptionalTransportedMode k a
          (data.stopContext.state.edges
            data.stopContext.outgoingSlot) *
        defect * outer := by
          exact hmain
    _ =
      (paperSecondOrderModeDecay k : ℂ) *
        incomingExceptionalTransportedMode k a
          (data.stopContext.state.edges
            data.stopContext.outgoingSlot) *
        (defect * outer) := by
          ring
    _ =
      (paperSecondOrderModeDecay k : ℂ) ^ 2 *
        charT4 k
          ((data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).incomingPhaseAnchor
              0 (y ω) v) *
        (defect * outer) := by
          exact
            data
              |>.paperDecay_mul_incomingExceptionalTransportedMode_mul_eq_anchor
                k y ω v (defect * outer)
    _ = _ := by
      ring

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

/-! ## The ordinary Step-4 charge -/

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- The stored stop certificate and the normalized Proposition 4.1
provider make the exact complex defect density integrable. -/
theorem integrable_incomingExceptionalPrimitiveDefect_of_prop41
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hε : 0 < ε) (hlog : 0 < |Real.log ε|)
    (supportConstant : ℝ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hprop :
      R324WithinHalfProp41Provider
        ρ C lam ε supportConstant κ)
    (k : Z4) :
    Integrable
      (fun u : T4 =>
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges u : ℂ) *
          (charT4 (-k) u - 1))
      paperMeasure := by
  let ctx := data.stopContext
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale : ℝ :=
    r324WithinHalfInternalEdgeScaleProduct
      ctx data.stopScale
  let M : T4 → ℝ :=
    primitiveKernelMajorant C lam ε supportConstant
      (residualBlockOrder ctx.step.2)
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hprimitive :
      R324WithinHalfPrimitiveCertificate
        ctx data.stopScale ρ C lam ε supportConstant := by
    exact
      data.stopCertificate.primitiveCertificate
        ρ C lam ε supportConstant hε hlog
        (fun H hH =>
          hprop data.trace.stopPrefix
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq H hH)
  have hJscale : 0 < Jscale :=
    data.stopCertificate.internalEdgeScaleProduct_pos
  have hMnonneg : ∀ u, 0 ≤ M u := by
    intro u
    exact primitiveKernelMajorant_nonneg hC hlam
  have hmajor :
      Integrable M paperMeasure :=
    integrable_primitiveKernelMajorant
      C lam ε supportConstant
      (residualBlockOrder ctx.step.2) hε
  have hJ :
      Integrable J paperMeasure := by
    have hscaled :
        Integrable (fun u : T4 => Jscale * M u)
          paperMeasure :=
      hmajor.const_mul Jscale
    refine
      Integrable.mono' hscaled
        hprimitive.measurable.aestronglyMeasurable
        ?_
    filter_upwards [paperMeasure.ae_ne 0] with u hu
    have hbound := hprimitive.bound u hu
    change |J u| ≤ Jscale * M u at hbound
    have hnonneg : 0 ≤ Jscale * M u :=
      mul_nonneg hJscale.le (hMnonneg u)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      using hbound
  have hweightMeas :
      Measurable fun u : T4 =>
        charT4 (-k) u - 1 :=
    (continuous_charT4 (-k)).measurable.sub measurable_const
  change
    Integrable
      (fun u : T4 =>
        (J u : ℂ) * (charT4 (-k) u - 1))
      paperMeasure
  refine
    hJ.ofReal.mul_bdd (c := 2)
      hweightMeas.aestronglyMeasurable
      (.of_forall fun u => ?_)
  calc
    ‖charT4 (-k) u - 1‖ ≤
        ‖charT4 (-k) u‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 := by
      rw [norm_charT4]
      norm_num

/-- **Certificate-scaled incoming Step-4 charge.**

The raw internal head edges are normalized through the stored stop
certificate before Proposition 4.1 is used.  Their positive scale product
appears exactly once.  The value at the identity is discarded only through
atomlessness of paper Haar measure. -/
theorem norm_incomingExceptionalPrimitiveDefect_le_scaled_of_prop41
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (hε : 0 < ε) (supportConstant : ℝ)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hprop :
      R324WithinHalfProp41Provider
        ρ C lam ε supportConstant κ)
    (k : Z4) :
    ‖incomingExceptionalPrimitiveDefect ρ lam ε
        (residualBlockOrder data.terminal.2)
        data.stopContext.one_le_blockOrder
        data.stopContext.internalEdges k‖ ≤
      2 *
        r324WithinHalfInternalEdgeScaleProduct
          data.stopContext data.stopScale *
        ∫ u : T4,
          primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder data.terminal.2) u
          ∂paperMeasure := by
  let ctx := data.stopContext
  let J : T4 → ℝ :=
    primitiveKernelDiff ρ lam ε
      (residualBlockOrder data.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges
  let Jscale : ℝ :=
    r324WithinHalfInternalEdgeScaleProduct
      ctx data.stopScale
  let M : T4 → ℝ :=
    primitiveKernelMajorant C lam ε supportConstant
      (residualBlockOrder data.terminal.2)
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  have hJscale : 0 < Jscale :=
    data.stopCertificate.internalEdgeScaleProduct_pos
  have hJoff :
      ∀ u, u ≠ 0 → |J u| ≤ Jscale * M u := by
    intro u hu
    dsimp only [J, Jscale, M]
    simpa [
      ctx, stopContext,
      R324WithinHalfResidualPrefix.headContext,
      R324WithinHalfStepContext.internalEdges,
      r324WithinHalfInternalEdgeScaleProduct] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        ρ data.stopContext.one_le_blockOrder
        data.stopContext.internalEdges
        (fun j =>
          data.stopScale
            (data.stopContext.internalSlot j))
        (fun j =>
          data.stopCertificate.scale_pos
            (data.stopContext.internalSlot j))
        (fun j =>
          data.stopCertificate.memE
            (data.stopContext.internalSlot j))
        (fun j =>
          data.stopCertificate.bound
            (data.stopContext.internalSlot j))
        (fun H hH =>
          hprop data.trace.stopPrefix
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq H hH)
        u hu
  have hMnonneg : ∀ u, 0 ≤ M u := by
    intro u
    exact primitiveKernelMajorant_nonneg hC hlam
  have hJrepresentative :
      ∀ u,
        |offDiagonalRepresentative J u| ≤
          Jscale * M u := by
    intro u
    by_cases hu : u = 0
    · subst u
      rw [offDiagonalRepresentative_zero, abs_zero]
      exact mul_nonneg hJscale.le (hMnonneg 0)
    · rw [offDiagonalRepresentative_eq J hu]
      exact hJoff u hu
  have hmajor :
      Integrable M paperMeasure :=
    integrable_primitiveKernelMajorant
      C lam ε supportConstant
      (residualBlockOrder data.terminal.2) hε
  have hphase :
      ‖∫ u : T4,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-k) u - 1)
          ∂paperMeasure‖ ≤
        2 * Jscale * ∫ u : T4, M u ∂paperMeasure := by
    have hscaled :
        Integrable
          (fun u : T4 => 2 * (Jscale * M u))
          paperMeasure :=
      (hmajor.const_mul Jscale).const_mul 2
    calc
      ‖∫ u : T4,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-k) u - 1)
          ∂paperMeasure‖ ≤
          ∫ u : T4,
            ‖(offDiagonalRepresentative J u : ℂ) *
              (charT4 (-k) u - 1)‖
            ∂paperMeasure :=
        norm_integral_le_integral_norm _
      _ ≤
          ∫ u : T4, 2 * (Jscale * M u)
            ∂paperMeasure := by
              refine integral_mono_of_nonneg
                (.of_forall fun u => norm_nonneg _)
                hscaled
                (.of_forall fun u => ?_)
              change
                ‖(offDiagonalRepresentative J u : ℂ) *
                    (charT4 (-k) u - 1)‖ ≤
                  2 * (Jscale * M u)
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              have hchar :
                  ‖charT4 (-k) u - 1‖ ≤ 2 := by
                calc
                  ‖charT4 (-k) u - 1‖ ≤
                      ‖charT4 (-k) u‖ + ‖(1 : ℂ)‖ :=
                    norm_sub_le _ _
                  _ = 2 := by
                    rw [norm_charT4]
                    norm_num
              calc
                |offDiagonalRepresentative J u| *
                      ‖charT4 (-k) u - 1‖ ≤
                    |offDiagonalRepresentative J u| * 2 :=
                  mul_le_mul_of_nonneg_left
                    hchar (abs_nonneg _)
                _ ≤ (Jscale * M u) * 2 :=
                  mul_le_mul_of_nonneg_right
                    (hJrepresentative u) (by norm_num)
                _ = 2 * (Jscale * M u) := by
                  ring
      _ = 2 * Jscale * ∫ u : T4, M u ∂paperMeasure := by
        rw [integral_const_mul, integral_const_mul]
        ring
  have hrepresentativeIntegral :
      (∫ u : T4,
          (J u : ℂ) * (charT4 (-k) u - 1)
          ∂paperMeasure) =
        ∫ u : T4,
          (offDiagonalRepresentative J u : ℂ) *
            (charT4 (-k) u - 1)
          ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards [paperMeasure.ae_ne 0] with u hu
    rw [offDiagonalRepresentative_eq J hu]
  unfold incomingExceptionalPrimitiveDefect
  change
    ‖∫ u : T4,
        (J u : ℂ) * (charT4 (-k) u - 1)
        ∂paperMeasure‖ ≤ _
  rw [hrepresentativeIntegral]
  simpa only [ctx, Jscale, M] using hphase

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

/-- Measurable primitive inputs and the ordinary Proposition 4.1 majorant
make the primitive gap kernel integrable. -/
theorem integrable_incomingExceptionalPrimitiveKernelDiff_of_bounds
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant) :
    Integrable
      (primitiveKernelDiff ρ lam ε n hn G)
      paperMeasure := by
  have hkernelMeas :=
    measurable_primitiveKernelDiff
      ρ lam ε n hn G hGmeas
  have hmajor :
      Integrable
        (primitiveKernelMajorant
          primitiveConstant lam ε supportConstant n)
        paperMeasure :=
    integrable_primitiveKernelMajorant
      primitiveConstant lam ε supportConstant n hε
  refine
    Integrable.mono' hmajor
      hkernelMeas.aestronglyMeasurable
      (.of_forall fun u => ?_)
  have hpoint := (hbound u).1
  have hmajorNonneg :
      0 ≤ primitiveKernelMajorant
        primitiveConstant lam ε supportConstant n u :=
    (abs_nonneg _).trans hpoint
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg]
    using hpoint

/-- The cosine defect is integrable under the same ordinary majorant. -/
theorem
    integrable_incomingExceptionalPrimitiveKernelDiff_mul_characterCosSubOne_of_bounds
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (k : Z4) :
    Integrable
      (fun u =>
        primitiveKernelDiff ρ lam ε n hn G u *
          (r324CharacterCos k u - 1))
      paperMeasure := by
  have hkernel :=
    integrable_incomingExceptionalPrimitiveKernelDiff_of_bounds
      ρ lam ε n hn G hGmeas
      supportConstant primitiveConstant hε hbound
  have hweightMeas :
      Measurable fun u : T4 =>
        r324CharacterCos k u - 1 :=
    (Complex.measurable_re.comp
      (continuous_charT4 k).measurable).sub measurable_const
  refine
    hkernel.mul_bdd (c := 2)
      hweightMeas.aestronglyMeasurable
      (.of_forall fun u => ?_)
  have hre :
      ‖(charT4 k u).re‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, norm_charT4] using
      Complex.abs_re_le_norm (charT4 k u)
  unfold r324CharacterCos
  calc
    ‖(charT4 k u).re - 1‖ ≤
        ‖(charT4 k u).re‖ + ‖(1 : ℝ)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hre (by norm_num)
    _ = 2 := by norm_num

/-- The sine component is integrable under the same ordinary majorant. -/
theorem
    integrable_incomingExceptionalPrimitiveKernelDiff_mul_characterSin_of_bounds
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (k : Z4) :
    Integrable
      (fun u =>
        primitiveKernelDiff ρ lam ε n hn G u *
          r324CharacterSin k u)
      paperMeasure := by
  have hkernel :=
    integrable_incomingExceptionalPrimitiveKernelDiff_of_bounds
      ρ lam ε n hn G hGmeas
      supportConstant primitiveConstant hε hbound
  have hweightMeas :
      Measurable (r324CharacterSin k) :=
    Complex.measurable_im.comp
      (continuous_charT4 k).measurable
  refine
    hkernel.mul_bdd (c := 1)
      hweightMeas.aestronglyMeasurable
      (.of_forall fun u => ?_)
  unfold r324CharacterSin
  simpa only [Real.norm_eq_abs, norm_charT4] using
    Complex.abs_im_le_norm (charT4 k u)

/-- `𝓔` symmetry removes the sine part of the incoming exceptional defect.
The orientation remains `charT4 (-k) u - 1`. -/
theorem incomingExceptionalPrimitiveDefect_eq_cos
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (k : Z4)
    (hcos :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            (r324CharacterCos k u - 1))
        paperMeasure)
    (hsin :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            r324CharacterSin (-k) u)
        paperMeasure) :
    incomingExceptionalPrimitiveDefect
        ρ lam ε n hn G k =
      ∫ u : T4,
        ((primitiveKernelDiff ρ lam ε n hn G u *
          (r324CharacterCos k u - 1) : ℝ) : ℂ)
        ∂paperMeasure := by
  unfold incomingExceptionalPrimitiveDefect
  exact
    integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos
      ρ lam ε n hn G hG k hcos hsin

/-- The ordinary half of Proposition 4.1 charges the whole complex defect.
There is no additional frequency gain and no inserted-kernel estimate in
this branch. -/
theorem norm_incomingExceptionalPrimitiveDefect_le_two_mul
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (hG : ∀ j, MemEClassT4 (G j))
    (k : Z4)
    (hcos :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            (r324CharacterCos k u - 1))
        paperMeasure)
    (hsin :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            r324CharacterSin (-k) u)
        paperMeasure) :
    ‖incomingExceptionalPrimitiveDefect
        ρ lam ε n hn G k‖ ≤
      2 *
        ∫ u : T4,
          primitiveKernelMajorant
            primitiveConstant lam ε supportConstant n u
          ∂paperMeasure := by
  rw [
    incomingExceptionalPrimitiveDefect_eq_cos
      ρ lam ε n hn G hG k hcos hsin]
  exact
    norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le_two_mul
      ρ lam ε n hn G supportConstant primitiveConstant hε hbound k

/-- Certificate-ready form: measurability and the ordinary
`PrimitiveKernelBounds` premise produce both cosine-seam integrability
requirements. -/
theorem norm_incomingExceptionalPrimitiveDefect_le_two_mul_of_bounds
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hG : ∀ j, MemEClassT4 (G j))
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (k : Z4) :
    ‖incomingExceptionalPrimitiveDefect
        ρ lam ε n hn G k‖ ≤
      2 *
        ∫ u : T4,
          primitiveKernelMajorant
            primitiveConstant lam ε supportConstant n u
          ∂paperMeasure := by
  exact
    norm_incomingExceptionalPrimitiveDefect_le_two_mul
      ρ lam ε n hn G
      supportConstant primitiveConstant hε hbound hG k
      (integrable_incomingExceptionalPrimitiveKernelDiff_mul_characterCosSubOne_of_bounds
        ρ lam ε n hn G hGmeas
        supportConstant primitiveConstant hε hbound k)
      (integrable_incomingExceptionalPrimitiveKernelDiff_mul_characterSin_of_bounds
        ρ lam ε n hn G hGmeas
        supportConstant primitiveConstant hε hbound (-k))

/-- The local head output is the norm of the transported suffix mode times
the ordinary Step-4 charge. -/
theorem norm_transportedMode_mul_incomingExceptionalPrimitiveDefect_le
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (hG : ∀ j, MemEClassT4 (G j))
    (k : Z4) (a : T4) (H : T4 → ℝ)
    (hcos :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            (r324CharacterCos k u - 1))
        paperMeasure)
    (hsin :
      Integrable
        (fun u =>
          primitiveKernelDiff ρ lam ε n hn G u *
            r324CharacterSin (-k) u)
        paperMeasure) :
    ‖incomingExceptionalTransportedMode k a H *
        incomingExceptionalPrimitiveDefect
          ρ lam ε n hn G k‖ ≤
      ‖incomingExceptionalTransportedMode k a H‖ *
        (2 *
          ∫ u : T4,
            primitiveKernelMajorant
              primitiveConstant lam ε supportConstant n u
            ∂paperMeasure) := by
  rw [norm_mul]
  exact
    mul_le_mul_of_nonneg_left
      (norm_incomingExceptionalPrimitiveDefect_le_two_mul
        ρ lam ε n hn G supportConstant primitiveConstant
        hε hbound hG k hcos hsin)
      (norm_nonneg _)

/-- Certificate-ready local head bound with no explicit cosine or sine
integrability premises. -/
theorem
    norm_transportedMode_mul_incomingExceptionalPrimitiveDefect_le_of_bounds
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j))
    (hG : ∀ j, MemEClassT4 (G j))
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (k : Z4) (a : T4) (H : T4 → ℝ) :
    ‖incomingExceptionalTransportedMode k a H *
        incomingExceptionalPrimitiveDefect
          ρ lam ε n hn G k‖ ≤
      ‖incomingExceptionalTransportedMode k a H‖ *
        (2 *
          ∫ u : T4,
            primitiveKernelMajorant
              primitiveConstant lam ε supportConstant n u
            ∂paperMeasure) := by
  rw [norm_mul]
  exact
    mul_le_mul_of_nonneg_left
      (norm_incomingExceptionalPrimitiveDefect_le_two_mul_of_bounds
        ρ lam ε n hn G hGmeas hG
        supportConstant primitiveConstant hε hbound k)
      (norm_nonneg _)

end

end Anderson4D
