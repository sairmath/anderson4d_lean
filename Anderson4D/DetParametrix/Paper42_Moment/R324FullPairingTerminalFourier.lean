import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingFinalHeadGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointAggregate

/-!
# Fourier integration of the retained full-pairing head

For a full within-half pairing, the certified trace stops immediately
before its unique terminal block.  The exact geometry of that block leaves
one outgoing Green difference.  This file identifies that literal
difference with `r324OutgoingEndpointKernel` and integrates the external
endpoint before taking any norm.

The remaining scalar keeps the complete primitive-pairing sum grouped.
Consequently these identities do not move an absolute value through the
Proposition 4.1 cancellation.  The later cosine reduction still has to be
performed after the terminal spatial variables have been integrated into
the corresponding `MemEClassT4` kernel; it is deliberately not asserted
pointwise for the raw primitive density here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {initialScale : Fin (2 * q + 1) → ℝ}

/-- Everything in the retained terminal raw local density except its
outgoing Green difference.  In particular, the primitive-pairing sum is
the complete signed finite sum and remains inside this single scalar. -/
def terminalGroupedPrimitiveCore
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) : ℝ :=
  data.trace.stopPrefix.state.edges
      (r324WithinHalfPredecessorSlot
        data.trace.stopPrefix.state
        data.terminalData.terminal)
      (x - t ⟨0, by
        have hn :=
          (data.trace.stopPrefix.headContext
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).one_le_blockOrder
        exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩) *
    primitiveChainProduct
      (residualBlockOrder data.terminalData.terminal.2)
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).one_le_blockOrder
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).internalEdges t *
    ∑ κB :
        {κB : PartialPairing
            (Fin
              (2 * residualBlockOrder
                data.terminalData.terminal.2)) //
          κB ∈ primitiveFullPairings
            (residualBlockOrder
              data.terminalData.terminal.2)},
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder data.terminalData.terminal.2)
        κB.1 t

/-- Exact real factorization of the translated terminal raw local density.
The endpoint-dependent factor is literally the outgoing Green difference
of paper (4.17); the predecessor kernel, internal chain, and complete
primitive sum stay grouped in `terminalGroupedPrimitiveCore`. -/
theorem terminal_rawLocal_translated_eq_groupedCore_mul_greenDifference
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x y : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) :
    (data.trace.stopPrefix.headContext
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton).rawLocalIntegrand
        ρ ε (x - y) (fun j => t j - y) =
      data.terminalGroupedPrimitiveCore x t *
        (greenFn
            (t (primitiveLast
              (residualBlockOrder
                data.terminalData.terminal.2)
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).one_le_blockOrder) -
              y) -
          greenFn
            (t ⟨0, by
              have hn :=
                (data.trace.stopPrefix.headContext
                  data.terminalData.terminal []
                  data.stop_remaining_eq_singleton).one_le_blockOrder
              exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩ - y)) := by
  let ctx :=
    data.trace.stopPrefix.headContext
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton
  have hout :
      data.trace.stopPrefix.state.edges
          (r324InternalVertexEdgeSlot
            data.terminalData.terminal.1.2) =
        greenFn := by
    have h := data.terminal_outgoingEdge_eq_greenFn
    change
      data.trace.stopPrefix.state.edges
          (r324InternalVertexEdgeSlot
            data.terminalData.terminal.1.2) =
        greenFn at h
    exact h
  rw [ctx.rawLocalIntegrand_translated]
  dsimp only [ctx]
  simp only [R324WithinHalfResidualPrefix.headContext]
  simp only [R324WithinHalfStepContext.outgoingSlot]
  rw [hout]
  unfold terminalGroupedPrimitiveCore
  simp only [R324WithinHalfResidualPrefix.headContext]
  ring_nf
  congr 1

/-- Complex form of the preceding identity.  It identifies the terminal
outgoing factor with the existing endpoint kernel without taking a norm. -/
theorem terminal_rawLocal_translated_eq_groupedCore_mul_outgoingKernel
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (x y : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) :
    ((data.trace.stopPrefix.headContext
      data.terminalData.terminal []
      data.stop_remaining_eq_singleton).rawLocalIntegrand
        ρ ε (x - y) (fun j => t j - y) : ℂ) =
      (data.terminalGroupedPrimitiveCore x t : ℂ) *
        r324OutgoingEndpointKernel
          (t (primitiveLast
            (residualBlockOrder
              data.terminalData.terminal.2)
            (data.trace.stopPrefix.headContext
              data.terminalData.terminal []
              data.stop_remaining_eq_singleton).one_le_blockOrder))
          (t ⟨0, by
            have hn :=
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).one_le_blockOrder
            exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩)
          true y := by
  rw [
    data.terminal_rawLocal_translated_eq_groupedCore_mul_greenDifference]
  simp only [r324OutgoingEndpointKernel, ↓reduceIte]
  push_cast
  rfl

/-- **Terminal endpoint-first identity.**  The external endpoint is
Fourier-integrated while the predecessor factor and the complete primitive
pairing sum are still signed and grouped. -/
theorem integral_char_mul_terminal_rawLocal_translated
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (β : Z4) (x : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) :
    (∫ y : T4,
        charT4 β y *
          ((data.trace.stopPrefix.headContext
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).rawLocalIntegrand
              ρ ε (x - y) (fun j => t j - y) : ℂ)
        ∂paperMeasure) =
      (data.terminalGroupedPrimitiveCore x t : ℂ) *
        r324EndpointCoefficient β
          (t (primitiveLast
            (residualBlockOrder
              data.terminalData.terminal.2)
            (data.trace.stopPrefix.headContext
              data.terminalData.terminal []
              data.stop_remaining_eq_singleton).one_le_blockOrder))
          (t ⟨0, by
            have hn :=
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).one_le_blockOrder
            exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩)
          true := by
  let lastPoint :=
    t (primitiveLast
      (residualBlockOrder data.terminalData.terminal.2)
      (data.trace.stopPrefix.headContext
        data.terminalData.terminal []
        data.stop_remaining_eq_singleton).one_le_blockOrder)
  let firstPoint :=
    t ⟨0, by
      have hn :=
        (data.trace.stopPrefix.headContext
          data.terminalData.terminal []
          data.stop_remaining_eq_singleton).one_le_blockOrder
      exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩
  calc
    (∫ y : T4,
        charT4 β y *
          ((data.trace.stopPrefix.headContext
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).rawLocalIntegrand
              ρ ε (x - y) (fun j => t j - y) : ℂ)
        ∂paperMeasure) =
      ∫ y : T4,
        (data.terminalGroupedPrimitiveCore x t : ℂ) *
          (charT4 β y *
            r324OutgoingEndpointKernel
              lastPoint firstPoint true y)
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with y
          rw [
            data.terminal_rawLocal_translated_eq_groupedCore_mul_outgoingKernel]
          dsimp only [lastPoint, firstPoint]
          ring
    _ =
      (data.terminalGroupedPrimitiveCore x t : ℂ) *
        (∫ y : T4,
          charT4 β y *
            r324OutgoingEndpointKernel
              lastPoint firstPoint true y
          ∂paperMeasure) := by
            rw [integral_const_mul]
    _ =
      (data.terminalGroupedPrimitiveCore x t : ℂ) *
        r324EndpointCoefficient β lastPoint firstPoint true := by
          rw [integral_char_mul_r324OutgoingEndpointKernel]
    _ = _ := by
      rfl

/-- Expanded phase-difference form of the terminal endpoint coefficient.
This is still an exact identity, prior to the later `𝓔`-symmetry/cosine
reduction. -/
theorem integral_char_mul_terminal_rawLocal_translated_eq_phaseDifference
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (β : Z4) (x : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) :
    (∫ y : T4,
        charT4 β y *
          ((data.trace.stopPrefix.headContext
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).rawLocalIntegrand
              ρ ε (x - y) (fun j => t j - y) : ℂ)
        ∂paperMeasure) =
      (data.terminalGroupedPrimitiveCore x t : ℂ) *
        (translatedGreenMode β
            (t (primitiveLast
              (residualBlockOrder
                data.terminalData.terminal.2)
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).one_le_blockOrder)) -
          translatedGreenMode β
            (t ⟨0, by
              have hn :=
                (data.trace.stopPrefix.headContext
                  data.terminalData.terminal []
                  data.stop_remaining_eq_singleton).one_le_blockOrder
              exact Nat.mul_pos (by decide) (Nat.zero_lt_of_lt hn)⟩)) := by
  rw [data.integral_char_mul_terminal_rawLocal_translated]
  simp [r324EndpointCoefficient]

/-- Fully explicit character form of the exact endpoint phase difference.
The Green multiplier is retained exactly; no `≤ 2` shortcut bound has been
used. -/
theorem integral_char_mul_terminal_rawLocal_translated_eq_characterDifference
    (data :
      R324FullPairingStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κ initialScale)
    (β : Z4) (x : T4)
    (t :
      Fin
          (2 * residualBlockOrder
            data.terminalData.terminal.2) →
        T4) :
    (∫ y : T4,
        charT4 β y *
          ((data.trace.stopPrefix.headContext
            data.terminalData.terminal []
            data.stop_remaining_eq_singleton).rawLocalIntegrand
              ρ ε (x - y) (fun j => t j - y) : ℂ)
        ∂paperMeasure) =
      (data.terminalGroupedPrimitiveCore x t : ℂ) *
        ((charT4 β
            (t (primitiveLast
              (residualBlockOrder
                data.terminalData.terminal.2)
              (data.trace.stopPrefix.headContext
                data.terminalData.terminal []
                data.stop_remaining_eq_singleton).one_le_blockOrder)) -
          charT4 β
            (t ⟨0, by
              have hn :=
                (data.trace.stopPrefix.headContext
                  data.terminalData.terminal []
                  data.stop_remaining_eq_singleton).one_le_blockOrder
              exact
                Nat.mul_pos (by decide)
                  (Nat.zero_lt_of_lt hn)⟩)) *
          (paperSecondOrderModeDecay β : ℂ)) := by
  rw [
    data.integral_char_mul_terminal_rawLocal_translated_eq_phaseDifference,
    translatedGreenMode_eq,
    translatedGreenMode_eq]
  unfold paperSecondOrderModeDecay paperModeNormSq
  ring

end R324FullPairingStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
