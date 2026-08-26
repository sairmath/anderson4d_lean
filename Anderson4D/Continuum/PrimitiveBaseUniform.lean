import Anderson4D.Continuum.PrimitiveBaseBound

/-!
# Uniform constants for the first primitive order

This file packages the analytic `n = 1` bounds with constants chosen once
from the cutoff, before the coupling, scale, or input kernel.  It is the
uniform base case needed by the global Proposition 4.1 induction.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- Uniform cutoff-dependent constants close both pointwise estimates of
Proposition 4.1 at order `n = 1`.  The symmetry-class conclusion is kept
separate, since it is a structural periodization lemma rather than an
analytic estimate. -/
theorem exists_uniform_primitiveKernelBounds_one (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
        ∀ (lam ε orderConstant : ℝ) (G : Fin 1 → T4 → ℝ),
          PrimitiveEstimateRegime 1 lam ε orderConstant supportConstant C →
          IsAdmissiblePrimitiveInput 1 G →
            PrimitiveKernelBounds ρ lam ε 1 (by omega) G supportConstant C := by
  obtain ⟨Cη, hCηpos, hη⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  let supportConstant : ℝ := 4 * ρ.radius
  let A : ℝ := Cη * (1 + supportConstant ^ 2)
  let C : ℝ := A + 1
  have hsupportPos : 0 < supportConstant := by
    dsimp [supportConstant]
    nlinarith [ρ.radius_pos]
  have hfactor : 1 ≤ 1 + supportConstant ^ 2 := by
    nlinarith [sq_nonneg supportConstant]
  have hApos : 0 < A := by
    exact mul_pos hCηpos (lt_of_lt_of_le zero_lt_one hfactor)
  have hCpos : 0 < C := by
    dsimp [C]
    linarith
  have hCηleA : Cη ≤ A := by
    dsimp [A]
    exact le_mul_of_one_le_right hCηpos.le hfactor
  have hAleCsq : A ≤ C ^ 2 := by
    dsimp [C]
    nlinarith [sq_nonneg A]
  have hCηleCsq : Cη ≤ C ^ 2 :=
    hCηleA.trans hAleCsq
  refine ⟨supportConstant, C, hsupportPos, hCpos, ?_⟩
  intro lam ε orderConstant G hreg hadm
  rcases hreg with
    ⟨_hn, hε, hε1, hlam, _horder, _hsupport, _hC, hord⟩
  have hlogne : |Real.log ε| ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hord
    norm_num at hord
  have hlog : 0 < |Real.log ε| :=
    lt_of_le_of_ne (abs_nonneg _) hlogne.symm
  apply primitiveKernelBounds_one ρ hε hε1 hlog hlam.le hCpos.le
    (fun z => hη hε hε1 z) hCηleCsq hAleCsq
  · exact le_rfl
  · exact fun z => hadm.2 0 z

end

end Anderson4D
