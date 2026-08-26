import Anderson4D.DetParametrix.Paper42_Moment.R324OutgoingPreCollapseFourier
import Anderson4D.DetParametrix.Paper42_Moment.R324CertificateScaledPrimitiveDefect

/-!
# The outgoing-shortcut terminal Step-4 charge

This file closes the local analytic seam at a shortcut terminal block for an
arbitrary partial pairing.  It follows paper §4.2, Step 4 in the required
order: the outgoing endpoint is Fourier-integrated exactly, the complete
signed primitive sum is integrated into the ordinary primitive kernel, and
only then is `𝓔` symmetry used to expose the cosine defect.  The final bound
therefore uses the ordinary `primitiveKernelMajorant`, with the paper's one
`ε⁻²` loss for this endpoint; no inserted kernel occurs here.

No trace or routing structure is introduced.  The input is precisely the
existing `R324ShortcutStopTraceAssembly`, which leaves the terminal shortcut
visible after the proper-prefix reduction.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Exact endpoint phase -/

/-- With the paper gap orientation `u = first - last`, the outgoing shortcut
coefficient is the free Green multiplier times the genuine phase defect.
This is an exact identity, before taking a norm. -/
theorem r324EndpointCoefficient_first_sub_gap_eq_defect
    (k : Z4) (first gap : T4) :
    r324EndpointCoefficient k (first - gap) first true =
      (paperSecondOrderModeDecay k : ℂ) *
        charT4 k first * (charT4 (-k) gap - 1) := by
  simp only [r324EndpointCoefficient, ↓reduceIte]
  rw [translatedGreenMode_eq, translatedGreenMode_eq]
  rw [charT4_sub_argument]
  unfold paperSecondOrderModeDecay paperModeNormSq
  push_cast
  ring

namespace R324WithinHalfStepContext

variable {m : ℕ} {κ : PartialPairing (Fin m)}

/-- The core left by outgoing endpoint Fourier integration is one genuine
predecessor edge times the complete signed primitive density. -/
theorem outgoingErasedTranslatedRawLocalCore_eq_predecessor_mul_completePrimitive
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (ε : ℝ) (x : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.outgoingErasedTranslatedRawLocalCore ρ ε x t =
      (ctx.state.edges
          (r324WithinHalfPredecessorSlot ctx.state ctx.step)
          (x - ctx.outgoingBlockFirst t) : ℂ) *
        ((∑ κB :
            {κB : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κB ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          detJclosedIntegrandWith ρ ε
            (2 * residualBlockOrder ctx.step.2)
            κB.1 ctx.internalEdges t : ℝ) : ℂ) := by
  have hcov :
      (∑ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1 t) =
        ∑ κB ∈ primitiveFullPairings
            (residualBlockOrder ctx.step.2),
          primitiveCovarianceProduct ρ ε
            (residualBlockOrder ctx.step.2) κB t := by
    symm
    apply Finset.sum_subtype
    intro κB
    rfl
  rw [
    sum_terminal_detJclosedIntegrandWith_eq_primitiveIntegrand
      ρ ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges t]
  unfold outgoingErasedTranslatedRawLocalCore outgoingBlockFirst
  unfold primitiveIntegrand
  rw [hcov]
  push_cast
  rw [← Finset.mul_sum]
  ring

/-- Integrating the internal coordinates of the outgoing-erased terminal
core produces the ordinary heterogeneous primitive kernel.  The complete
finite primitive-pairing sum remains inside the integral until this exact
identity is applied. -/
theorem lamEps_pow_integral_outgoingErasedTranslatedRawLocalCore_eq
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (x first last : T4)
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
    (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
        (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ctx.outgoingErasedTranslatedRawLocalCore ρ ε x
            (primitiveAssemble
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder first last r)
          ∂Measure.pi fun _ => paperMeasure) =
      ((ctx.state.edges
            (r324WithinHalfPredecessorSlot ctx.state ctx.step)
            (x - first) *
          primitiveKernelDiff ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges
            (first - last) : ℝ) : ℂ) := by
  let P : ℝ :=
    ctx.state.edges
      (r324WithinHalfPredecessorSlot ctx.state ctx.step) (x - first)
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
      ctx.outgoingErasedTranslatedRawLocalCore ρ ε x
          (primitiveAssemble
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder first last r) =
        ((P * S r : ℝ) : ℂ) := by
    rw [
      ctx.outgoingErasedTranslatedRawLocalCore_eq_predecessor_mul_completePrimitive]
    simp only [outgoingBlockFirst, primitiveAssemble_zero]
    dsimp only [P, S]
    push_cast
    ring
  have hintegral :
      (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ctx.outgoingErasedTranslatedRawLocalCore ρ ε x
            (primitiveAssemble
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder first last r)
          ∂Measure.pi fun _ => paperMeasure) =
        (((∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
            P * S r
            ∂Measure.pi fun _ => paperMeasure) : ℝ) : ℂ) := by
    calc
      _ = ∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ((P * S r : ℝ) : ℂ)
          ∂Measure.pi fun _ => paperMeasure := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_ofReal
  have hkernel :=
    integral_sum_terminal_detJclosedIntegrandWith_eq_primitiveKernel
      ρ lam ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges first last hint
  have hkernelC := congrArg (fun z : ℝ => (z : ℂ)) hkernel
  push_cast at hkernelC
  rw [hintegral, integral_const_mul]
  push_cast
  dsimp only [P, S]
  calc
    (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
        ((ctx.state.edges
              (r324WithinHalfPredecessorSlot ctx.state ctx.step)
              (x - first) : ℂ) *
          ((∫ r :
              Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
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
            ∂Measure.pi fun _ => paperMeasure : ℝ) : ℂ)) =
        (ctx.state.edges
            (r324WithinHalfPredecessorSlot ctx.state ctx.step)
            (x - first) : ℂ) *
          ((lamEps lam ε : ℂ) ^
              (2 * residualBlockOrder ctx.step.2) *
            ((∫ r :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
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
              ∂Measure.pi fun _ => paperMeasure : ℝ) : ℂ)) := by
                ring
    _ =
        (ctx.state.edges
            (r324WithinHalfPredecessorSlot ctx.state ctx.step)
            (x - first) : ℂ) *
          (Anderson4D.primitiveKernel ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges first last : ℂ) := by
              rw [hkernelC]
    _ = _ := by
      rw [
        primitiveKernel_eq_primitiveKernelDiff_sub
          ρ lam ε (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges first last]

end R324WithinHalfStepContext

namespace R324WithinHalfStepContext

variable {m : ℕ} {κ : PartialPairing (Fin m)}

/-- Fixed-first, fixed-gap form of the shortcut endpoint operation for an
arbitrary stopped terminal `R324WithinHalfStepContext`.  The `y` integral
is performed first, then the complete signed primitive sum is integrated
in the internal block coordinates. -/
theorem lamEps_pow_integral_terminalOutgoingFourier_internal_eq_defect
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (k : Z4) (x first gap : T4) (outer : ℂ)
    (hint :
      ∀ κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        Integrable
          (fun r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
        (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ∫ y : T4,
            charT4 k y *
              ((ctx.rawLocalIntegrand ρ ε (x - y)
                (fun j =>
                  primitiveAssemble
                    (residualBlockOrder ctx.step.2)
                    ctx.one_le_blockOrder first (first - gap) r j - y) : ℂ) *
                outer)
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure) =
      ((ctx.state.edges
            (r324WithinHalfPredecessorSlot ctx.state ctx.step)
            (x - first) : ℝ) : ℂ) *
        (primitiveKernelDiff ρ lam ε
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges gap : ℂ) *
        (paperSecondOrderModeDecay k : ℂ) *
        charT4 k first * (charT4 (-k) gap - 1) * outer := by
  let coeff : ℂ :=
    r324EndpointCoefficient k (first - gap) first true
  have hpoint
      (r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4) :
      (∫ y : T4,
          charT4 k y *
            ((ctx.rawLocalIntegrand ρ ε (x - y)
              (fun j =>
                primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder first (first - gap) r j - y) : ℂ) *
              outer)
          ∂paperMeasure) =
        ctx.outgoingErasedTranslatedRawLocalCore ρ ε x
            (primitiveAssemble
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder first (first - gap) r) *
          coeff * outer := by
    let t :=
      primitiveAssemble
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder first (first - gap) r
    have hfirst : ctx.outgoingBlockFirst t = first := by
      dsimp only [t]
      unfold outgoingBlockFirst
      rw [primitiveAssemble_zero]
    have hlast : ctx.outgoingBlockLast t = first - gap := by
      dsimp only [t]
      unfold outgoingBlockLast
      rw [primitiveAssemble_last]
    have hfourier :=
      ctx.integral_char_mul_rawLocal_translated_eq_endpointCoefficient
        ρ ε houtgoing k x t outer
    change
      (∫ y : T4,
          charT4 k y *
            ((ctx.rawLocalIntegrand ρ ε (x - y)
              (fun j => t j - y) : ℂ) * outer)
          ∂paperMeasure) =
        ctx.outgoingErasedTranslatedRawLocalCore ρ ε x t *
          coeff * outer
    rw [hfourier, hfirst, hlast]
  have hcore :=
    ctx.lamEps_pow_integral_outgoingErasedTranslatedRawLocalCore_eq
      ρ lam ε x first (first - gap) hint
  have hgap : first - (first - gap) = gap := by
    abel
  calc
    (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
        (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ∫ y : T4,
            charT4 k y *
              ((ctx.rawLocalIntegrand ρ ε (x - y)
                (fun j =>
                  primitiveAssemble
                    (residualBlockOrder ctx.step.2)
                    ctx.one_le_blockOrder first (first - gap) r j - y) : ℂ) *
                outer)
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
        (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ctx.outgoingErasedTranslatedRawLocalCore ρ ε x
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder first (first - gap) r) *
            coeff * outer
          ∂Measure.pi fun _ => paperMeasure) := by
            apply congrArg
              (fun z : ℂ =>
                (lamEps lam ε : ℂ) ^
                  (2 * residualBlockOrder ctx.step.2) * z)
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
    _ =
      ((lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
        ∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
          ctx.outgoingErasedTranslatedRawLocalCore ρ ε x
            (primitiveAssemble
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder first (first - gap) r)
          ∂Measure.pi fun _ => paperMeasure) * coeff * outer := by
            rw [integral_mul_const, integral_mul_const]
            ring
    _ =
      ((ctx.state.edges
            (r324WithinHalfPredecessorSlot ctx.state ctx.step)
            (x - first) *
          primitiveKernelDiff ρ lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder ctx.internalEdges
            (first - (first - gap)) : ℝ) : ℂ) * coeff * outer := by
              rw [hcore]
    _ = _ := by
      rw [hgap]
      rw [show coeff =
          (paperSecondOrderModeDecay k : ℂ) *
            charT4 k first * (charT4 (-k) gap - 1) by
        exact r324EndpointCoefficient_first_sub_gap_eq_defect
          k first gap]
      rw [Complex.ofReal_mul]
      ring

/-- After the exact endpoint and internal-coordinate operations, integrating
the terminal gap leaves precisely the ordinary primitive phase defect.
No absolute value has yet been taken. -/
theorem integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (k : Z4) (x first : T4) (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (∫ gap : T4,
        (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
          (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((ctx.rawLocalIntegrand ρ ε (x - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder ctx.step.2)
                      ctx.one_le_blockOrder first (first - gap) r j - y) : ℂ) *
                  outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure) =
      ((ctx.state.edges
            (r324WithinHalfPredecessorSlot ctx.state ctx.step)
            (x - first) : ℝ) : ℂ) *
        (paperSecondOrderModeDecay k : ℂ) * charT4 k first *
        (∫ gap : T4,
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges gap : ℂ) *
            (charT4 (-k) gap - 1)
          ∂paperMeasure) * outer := by
  let A : ℂ :=
    ((ctx.state.edges
          (r324WithinHalfPredecessorSlot ctx.state ctx.step)
          (x - first) : ℝ) : ℂ) *
      (paperSecondOrderModeDecay k : ℂ) * charT4 k first
  have hfiber (gap : T4) :=
    ctx.lamEps_pow_integral_terminalOutgoingFourier_internal_eq_defect
      ρ lam ε houtgoing k x first gap outer (hint gap)
  calc
    _ = ∫ gap : T4,
        ((ctx.state.edges
              (r324WithinHalfPredecessorSlot ctx.state ctx.step)
              (x - first) : ℝ) : ℂ) *
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges gap : ℂ) *
          (paperSecondOrderModeDecay k : ℂ) *
          charT4 k first * (charT4 (-k) gap - 1) * outer
        ∂paperMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hfiber
    _ = ∫ gap : T4,
        A *
          ((primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges gap : ℂ) *
            (charT4 (-k) gap - 1)) * outer
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with gap
          dsimp only [A]
          ring
    _ = A *
        (∫ gap : T4,
          (primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges gap : ℂ) *
            (charT4 (-k) gap - 1)
          ∂paperMeasure) * outer := by
            rw [integral_mul_const, integral_const_mul]
    _ = _ := by
      dsimp only [A]

/-- `𝓔` symmetry is applied only after both endpoint and interval variables
have been removed.  The resulting kernel is the ordinary `J`, not the
inserted `J̃`. -/
theorem integral_lamEps_pow_terminalOutgoingFourier_gap_eq_cos
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (k : Z4) (x first : T4) (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder first (first - gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hG : ∀ j, MemEClassT4 (ctx.internalEdges j))
    (hcos :
      Integrable
        (fun gap =>
          primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges gap *
            (r324CharacterCos k gap - 1))
        paperMeasure)
    (hsin :
      Integrable
        (fun gap =>
          primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges gap *
            r324CharacterSin (-k) gap)
        paperMeasure) :
    (∫ gap : T4,
        (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
          (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((ctx.rawLocalIntegrand ρ ε (x - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder ctx.step.2)
                      ctx.one_le_blockOrder first (first - gap) r j - y) : ℂ) *
                  outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure) =
      ((ctx.state.edges
            (r324WithinHalfPredecessorSlot ctx.state ctx.step)
            (x - first) : ℝ) : ℂ) *
        (paperSecondOrderModeDecay k : ℂ) * charT4 k first *
        (∫ gap : T4,
          ((primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder ctx.internalEdges gap *
            (r324CharacterCos k gap - 1) : ℝ) : ℂ)
          ∂paperMeasure) * outer := by
  rw [ctx.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
    ρ lam ε houtgoing k x first outer hint]
  rw [integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos
    ρ lam ε (residualBlockOrder ctx.step.2)
    ctx.one_le_blockOrder ctx.internalEdges hG k hcos hsin]

/-- Certificate-ready numerical endpoint charge.  The Fourier multiplier
`⟨k⟩⁻²` remains explicit and the terminal primitive block is charged by the
ordinary Proposition 4.1 majorant. -/
theorem norm_integral_lamEps_pow_terminalOutgoingFourier_gap_le_two_mul
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (k : Z4) (x first : T4) (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder first (first - gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hGmeas : ∀ j, Measurable (ctx.internalEdges j))
    (hG : ∀ j, MemEClassT4 (ctx.internalEdges j))
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder ctx.internalEdges
        supportConstant primitiveConstant) :
    ‖∫ gap : T4,
        (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
          (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((ctx.rawLocalIntegrand ρ ε (x - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder ctx.step.2)
                      ctx.one_le_blockOrder first (first - gap) r j - y) : ℂ) *
                  outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure‖ ≤
      |ctx.state.edges
          (r324WithinHalfPredecessorSlot ctx.state ctx.step)
          (x - first)| *
        paperSecondOrderModeDecay k *
        (2 *
          ∫ gap : T4,
            primitiveKernelMajorant
              primitiveConstant lam ε supportConstant
              (residualBlockOrder ctx.step.2) gap
            ∂paperMeasure) * ‖outer‖ := by
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_two_mul_of_bounds
      ρ lam ε (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges hGmeas hG
      supportConstant primitiveConstant hε hbound k
  rw [ctx.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
    ρ lam ε houtgoing k x first outer hint]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg k),
    norm_charT4, mul_one]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdefect
        (mul_nonneg (abs_nonneg _)
          (paperSecondOrderModeDecay_nonneg k)))
      (norm_nonneg outer)

/-- The usable certificate-scaled form of the outgoing shortcut charge.
The stopped block's internal edges carry their actual inverse-square
constants in `certificate`; Proposition 4.1 is applied only after those
constants are normalized out. -/
theorem norm_integral_lamEps_pow_terminalOutgoingFourier_gap_le_scaled
    (ctx : R324WithinHalfStepContext κ)
    (ρ : SmoothCutoff) (C lam ε supportConstant : ℝ)
    (scale : Fin (m + 1) → ℝ)
    (certificate : R324WithinHalfEdgeCertificate ctx.state scale)
    (houtgoing : ctx.state.edges ctx.outgoingSlot = greenFn)
    (k : Z4) (x first : T4) (outer : ℂ)
    (hint :
      ∀ (gap : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.step.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder first (first - gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hε : 0 < ε) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H :
          Fin (2 * residualBlockOrder ctx.step.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder ctx.step.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder ctx.step.2)
                ctx.one_le_blockOrder H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder H supportConstant C) :
    ‖∫ gap : T4,
        (lamEps lam ε : ℂ) ^ (2 * residualBlockOrder ctx.step.2) *
          (∫ r : Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4,
            ∫ y : T4,
              charT4 k y *
                ((ctx.rawLocalIntegrand ρ ε (x - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder ctx.step.2)
                      ctx.one_le_blockOrder first (first - gap) r j - y) : ℂ) *
                  outer)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure‖ ≤
      |ctx.state.edges
          (r324WithinHalfPredecessorSlot ctx.state ctx.step)
          (x - first)| *
        paperSecondOrderModeDecay k *
        (2 * r324WithinHalfInternalEdgeScaleProduct ctx scale *
          ∫ gap : T4,
            primitiveKernelMajorant
              C lam ε supportConstant
              (residualBlockOrder ctx.step.2) gap
            ∂paperMeasure) * ‖outer‖ := by
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
      ctx scale certificate hε hC hlam hprop k
  rw [ctx.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
    ρ lam ε houtgoing k x first outer hint]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg k),
    norm_charT4, mul_one]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdefect
        (mul_nonneg (abs_nonneg _)
          (paperSecondOrderModeDecay_nonneg k)))
      (norm_nonneg outer)

end R324WithinHalfStepContext

end

end Anderson4D
