import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingTerminalIntegrability
import Anderson4D.Continuum.PrimitiveMajorantIntegral

/-!
# Automatic cosine integrability at a full-pairing terminal block

The exact terminal cosine identity previously exposed the two real
integrability premises needed for Bochner linearity.  For a genuine
full-pairing budget/geometry adapter these premises follow directly from
the ordinary Proposition 4.1 bound:

* the adapter certificate makes every terminal internal edge measurable;
* `PrimitiveKernelBounds` dominates the resulting `primitiveKernelDiff` by
  the integrable ordinary majorant; and
* the real and imaginary parts of a torus character are bounded measurable
  multipliers.

Thus the terminal cosine identity below has no explicit `hcos` or `hsin`
input.  No target moment estimate or routing output is assumed.
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

/-- The ordinary Proposition 4.1 majorant makes the genuine terminal
primitive kernel integrable.  Measurability is supplied by the same edge
certificate that was used to reach the terminal block. -/
theorem integrable_terminalPrimitiveKernelDiff_of_bounds
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hbound :
      PrimitiveKernelBounds ρ lam ε
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges
        supportConstant primitiveConstant) :
    Integrable
      (primitiveKernelDiff ρ lam ε
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges)
      paperMeasure := by
  have hGmeas :
      ∀ j,
        Measurable
          ((data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalEdges j) := by
    intro j
    simpa only [R324WithinHalfStepContext.internalEdges,
      R324WithinHalfResidualPrefix.headContext] using
      (data.certificate.measurable
        ((data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalSlot j))
  have hkernelMeas :=
    measurable_primitiveKernelDiff ρ lam ε
      (residualBlockOrder
        data.geometry.terminalData.terminal.2)
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
      hGmeas
  have hmajor :
      Integrable
        (primitiveKernelMajorant primitiveConstant lam ε
          supportConstant
          (residualBlockOrder
            data.geometry.terminalData.terminal.2))
        paperMeasure :=
    integrable_primitiveKernelMajorant primitiveConstant lam ε
      supportConstant
      (residualBlockOrder
        data.geometry.terminalData.terminal.2)
      hε
  refine Integrable.mono' hmajor hkernelMeas.aestronglyMeasurable
    (.of_forall fun u => ?_)
  have hpoint := (hbound u).1
  have hmajorNonneg :
      0 ≤ primitiveKernelMajorant primitiveConstant lam ε
        supportConstant
        (residualBlockOrder
          data.geometry.terminalData.terminal.2) u :=
    (abs_nonneg _).trans hpoint
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg] using hpoint

/-- The cosine-minus-one weighted terminal primitive kernel is integrable.
The multiplier has norm at most two. -/
theorem
    integrable_terminalPrimitiveKernelDiff_mul_characterCosSubOne_of_bounds
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hbound :
      PrimitiveKernelBounds ρ lam ε
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges
        supportConstant primitiveConstant)
    (β : Z4) :
    Integrable
      (fun u =>
        primitiveKernelDiff ρ lam ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges u *
          (r324CharacterCos β u - 1))
      paperMeasure := by
  have hkernel :=
    data.integrable_terminalPrimitiveKernelDiff_of_bounds
      hε supportConstant primitiveConstant hbound
  have hweightMeas :
      Measurable fun u : T4 =>
        r324CharacterCos β u - 1 := by
    exact
      (Complex.measurable_re.comp
        (continuous_charT4 β).measurable).sub measurable_const
  refine hkernel.mul_bdd (c := 2) hweightMeas.aestronglyMeasurable
    (.of_forall fun u => ?_)
  have hre :
      ‖(charT4 β u).re‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, norm_charT4] using
      Complex.abs_re_le_norm (charT4 β u)
  unfold r324CharacterCos
  calc
    ‖(charT4 β u).re - 1‖ ≤
        ‖(charT4 β u).re‖ + ‖(1 : ℝ)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hre (by norm_num)
    _ = 2 := by norm_num

/-- The sine-weighted terminal primitive kernel is integrable.  The
multiplier has norm at most one. -/
theorem integrable_terminalPrimitiveKernelDiff_mul_characterSin_of_bounds
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hbound :
      PrimitiveKernelBounds ρ lam ε
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges
        supportConstant primitiveConstant)
    (β : Z4) :
    Integrable
      (fun u =>
        primitiveKernelDiff ρ lam ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges u *
          r324CharacterSin β u)
      paperMeasure := by
  have hkernel :=
    data.integrable_terminalPrimitiveKernelDiff_of_bounds
      hε supportConstant primitiveConstant hbound
  have hweightMeas :
      Measurable (r324CharacterSin β) :=
    Complex.measurable_im.comp (continuous_charT4 β).measurable
  refine hkernel.mul_bdd (c := 1) hweightMeas.aestronglyMeasurable
    (.of_forall fun u => ?_)
  unfold r324CharacterSin
  simpa only [Real.norm_eq_abs, norm_charT4] using
    Complex.abs_im_le_norm (charT4 β u)

/-- **Terminal cosine identity with certificate-produced integrability.**
The exact gap orientation is unchanged from the endpoint Fourier identity;
the adapter supplies `𝓔`-membership and the Proposition 4.1 bound supplies
both Bochner-integrability premises. -/
theorem
    integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos_of_bounds
    (data : R324FullPairingBudgetTerminalAdapter budget)
    (hε : 0 < ε) (supportConstant primitiveConstant : ℝ)
    (hbound :
      PrimitiveKernelBounds ρ lam ε
        (residualBlockOrder
          data.geometry.terminalData.terminal.2)
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
        (data.geometry.trace.stopPrefix.headContext
          data.geometry.terminalData.terminal []
          data.geometry.stop_remaining_eq_singleton).internalEdges
        supportConstant primitiveConstant)
    (β : Z4) :
    (∫ u,
        (primitiveKernelDiff ρ lam ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges u :
          ℂ) *
          (charT4 (-β) u - 1)
        ∂paperMeasure) =
      ∫ u,
        ((primitiveKernelDiff ρ lam ε
            (residualBlockOrder
              data.geometry.terminalData.terminal.2)
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
            (data.geometry.trace.stopPrefix.headContext
              data.geometry.terminalData.terminal []
              data.geometry.stop_remaining_eq_singleton).internalEdges u *
          (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure := by
  exact
    integral_terminalPrimitiveKernelDiff_mul_negCharacterSubOne_eq_cos
      ρ lam ε
      (residualBlockOrder
        data.geometry.terminalData.terminal.2)
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
      data.terminalInternalEdges_memE β
      (data
        |>.integrable_terminalPrimitiveKernelDiff_mul_characterCosSubOne_of_bounds
          hε supportConstant primitiveConstant hbound β)
      (data
        |>.integrable_terminalPrimitiveKernelDiff_mul_characterSin_of_bounds
          hε supportConstant primitiveConstant hbound (-β))

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
