import Anderson4D.DetParametrix.Paper42_Moment.R324CharacterCosineEstimate
import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingTerminalCosineIntegrability

/-!
# The frequency-independent cosine loss in R-324 Step 4

Paper §4.2, Step 4 keeps the Green multiplier
`⟨β⟩⁻²` outside the terminal primitive block.  At that point the character
factor is estimated only by `|cos - 1| ≤ 2`.  Consequently the ordinary
Proposition 4.1 majorant is integrated without a squared-distance weight,
and the resulting loss is the paper's
`ε⁻² |log ε|⁻¹` loss.

This file deliberately does not use the sharper local quadratic character
estimate: doing so here would incorrectly claim an additional frequency
decay after the Green multiplier has already been retained.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Generic frequency-independent integral domination -/

/-- A signed real kernel dominated by an integrable majorant loses at most
the exact factor `2` after multiplication by the terminal cosine defect.
The conclusion is a complex Bochner-integral bound, matching the terminal
Fourier identity. -/
theorem
    norm_integral_mul_r324CharacterCos_sub_one_le_two_mul_of_abs_le
    {J M : T4 → ℝ} (β : Z4)
    (hJ : ∀ u, |J u| ≤ M u)
    (hint : Integrable M paperMeasure) :
    ‖∫ u,
        ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure‖ ≤
      2 * ∫ u, M u ∂paperMeasure := by
  have hscaled :
      Integrable (fun u => 2 * M u) paperMeasure :=
    hint.const_mul 2
  calc
    ‖∫ u,
        ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure‖ ≤
        ∫ u,
          ‖((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)‖
          ∂paperMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u, 2 * M u ∂paperMeasure := by
      refine integral_mono_of_nonneg
        (.of_forall fun u => norm_nonneg _)
        hscaled
        (.of_forall fun u => ?_)
      dsimp only
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc
        |J u| * |r324CharacterCos β u - 1| ≤ |J u| * 2 :=
          mul_le_mul_of_nonneg_left
            (abs_r324CharacterCos_sub_one_le_two β u)
            (abs_nonneg _)
        _ ≤ M u * 2 :=
          mul_le_mul_of_nonneg_right (hJ u) (by norm_num)
        _ = 2 * M u := by ring
    _ = 2 * ∫ u, M u ∂paperMeasure := by
      rw [integral_const_mul]

/-! ## Ordinary Proposition 4.1 majorant -/

/-- The ordinary half of `PrimitiveKernelBounds` supplies exactly the
majorant used in Step 4.  In particular, the right-hand side has no
distance weight and no hidden sign assumption. -/
theorem
    norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le_two_mul
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (β : Z4) :
    ‖∫ u,
        ((primitiveKernelDiff ρ lam ε n hn G u *
          (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure‖ ≤
      2 *
        ∫ u,
          primitiveKernelMajorant
            primitiveConstant lam ε supportConstant n u
          ∂paperMeasure := by
  exact
    norm_integral_mul_r324CharacterCos_sub_one_le_two_mul_of_abs_le β
      (fun u => (hbound u).1)
      (integrable_primitiveKernelMajorant
        primitiveConstant lam ε supportConstant n hε)

/-- Quantifier-honest numerical form of the preceding estimate.  The
integration constants are chosen once, before the cutoff, coupling, scale,
order, primitive input, and pointwise-bound constants. -/
theorem
    exists_norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le_raw :
    ∃ Cball Creg : ℝ, 0 < Cball ∧ 0 < Creg ∧
      ∀ (ρ : SmoothCutoff)
        (primitiveConstant supportConstant lam ε : ℝ)
        (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        0 < ε →
        0 < supportConstant →
        1 ≤ |Real.log ε| →
        PrimitiveKernelBounds ρ lam ε n hn G
          supportConstant primitiveConstant →
        ∀ β : Z4,
          ‖∫ u,
              ((primitiveKernelDiff ρ lam ε n hn G u *
                (r324CharacterCos β u - 1) : ℝ) : ℂ)
              ∂paperMeasure‖ ≤
            2 *
              ((primitiveConstant * lam) ^ (2 * n) *
                ((Cball * supportConstant ^ 2 + Creg) *
                  ε⁻¹ ^ (2 : ℕ) / |Real.log ε|)) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveKernelMajorant_le
  refine ⟨Cball, Creg, hCball, hCreg, ?_⟩
  intro ρ primitiveConstant supportConstant lam ε n hn G
    hε hsupport hlog hbound β
  exact
    (norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le_two_mul
      ρ lam ε n hn G supportConstant primitiveConstant hε hbound β).trans
      (mul_le_mul_of_nonneg_left
        (hmajorant primitiveConstant lam ε supportConstant n
          hε hsupport hlog)
        (by norm_num))

/-! ## Full-pairing terminal adapter -/

namespace R324WithinHalfResidualPrefix

namespace R324FullPairingBudgetTerminalAdapter

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    {budget :
      R324FullPairingBudgetStopTrace
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) (A := A) κ}

/-- The Step 4 loss specialized to the genuine terminal block of a
full-pairing budget trace.  The adapter fixes the retained block and its
internal edges; `PrimitiveKernelBounds` supplies the ordinary `J`
majorant. -/
theorem
    norm_integral_terminalPrimitiveKernelDiff_mul_r324CharacterCos_sub_one_le_two_mul
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
    ‖∫ u,
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
        ∂paperMeasure‖ ≤
      2 *
        ∫ u,
          primitiveKernelMajorant primitiveConstant lam ε supportConstant
            (residualBlockOrder
              data.geometry.terminalData.terminal.2) u
          ∂paperMeasure := by
  exact
    norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le_two_mul
      ρ lam ε
      (residualBlockOrder
        data.geometry.terminalData.terminal.2)
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
      supportConstant primitiveConstant hε hbound β

/-- Numerical Step 4 loss for every genuine full-pairing terminal adapter.
The constants `Cball` and `Creg` precede every geometric and analytic
parameter, so in particular they cannot depend on the trace, the cutoff,
the coupling, or the terminal order. -/
theorem
    exists_norm_integral_terminalPrimitiveKernelDiff_mul_r324CharacterCos_sub_one_le_raw :
    ∃ Cball Creg : ℝ, 0 < Cball ∧ 0 < Creg ∧
      ∀ (ρ : SmoothCutoff) (C lam ε K A : ℝ)
        (q : ℕ) (κ : PartialPairing (Fin (2 * q)))
        (budget :
          R324FullPairingBudgetStopTrace
            (ρ := ρ) (C := C) (lam := lam)
            (ε := ε) (K := K) (A := A) κ)
        (data : R324FullPairingBudgetTerminalAdapter budget)
        (supportConstant primitiveConstant : ℝ),
        0 < ε →
        0 < supportConstant →
        1 ≤ |Real.log ε| →
        PrimitiveKernelBounds ρ lam ε
          (residualBlockOrder
            data.geometry.terminalData.terminal.2)
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
          (data.geometry.trace.stopPrefix.headContext
            data.geometry.terminalData.terminal []
            data.geometry.stop_remaining_eq_singleton).internalEdges
          supportConstant primitiveConstant →
        ∀ β : Z4,
          ‖∫ u,
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
              ∂paperMeasure‖ ≤
            2 *
              ((primitiveConstant * lam) ^
                  (2 *
                    residualBlockOrder
                      data.geometry.terminalData.terminal.2) *
                ((Cball * supportConstant ^ 2 + Creg) *
                  ε⁻¹ ^ (2 : ℕ) / |Real.log ε|)) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hraw⟩ :=
    exists_norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le_raw
  refine ⟨Cball, Creg, hCball, hCreg, ?_⟩
  intro ρ C lam ε K A q κ budget data
    supportConstant primitiveConstant hε hsupport hlog hbound β
  exact
    hraw ρ primitiveConstant supportConstant lam ε
      (residualBlockOrder
        data.geometry.terminalData.terminal.2)
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).one_le_blockOrder
      (data.geometry.trace.stopPrefix.headContext
        data.geometry.terminalData.terminal []
        data.geometry.stop_remaining_eq_singleton).internalEdges
      hε hsupport hlog hbound β

end R324FullPairingBudgetTerminalAdapter

end R324WithinHalfResidualPrefix

end

end Anderson4D
