import Anderson4D.Continuum.FourPointFourier
import Anderson4D.Main.GaussianQuadratic

/-!
# Positive semidefiniteness of the explicit Gaussian limit covariance

The four-point Fourier coefficient is a bilinear Gram form.  Combining
its bilinear and Hermitian specializations shows that `limitVar` is the
integral of the square of the real part of a finite profile combination,
which proves positive semidefiniteness of `gaussianLimitLaw`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

/-! ## Elementary symmetries of the four-point coefficient -/

/-- Swapping the two pairs of external modes leaves the four-point
coefficient unchanged. -/
theorem fourPointHCoeff_swap_pairs
    (α₁ β₁ α₂ β₂ : Z4) :
    fourPointHCoeff α₁ β₁ α₂ β₂ =
      fourPointHCoeff α₂ β₂ α₁ β₁ := by
  have hfreq :
      α₁ + β₁ + (α₂ + β₂) = 0 ↔
        α₂ + β₂ + (α₁ + β₁) = 0 := by
    constructor <;> intro h
    · calc
        α₂ + β₂ + (α₁ + β₁) =
            α₁ + β₁ + (α₂ + β₂) := by abel
        _ = 0 := h
    · calc
        α₁ + β₁ + (α₂ + β₂) =
            α₂ + β₂ + (α₁ + β₁) := by abel
        _ = 0 := h
  rw [fourPointHCoeff_eq_indicator,
    fourPointHCoeff_eq_indicator]
  by_cases h : α₁ + β₁ + (α₂ + β₂) = 0
  · rw [if_pos h, if_pos (hfreq.mp h)]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun h' => h (hfreq.mpr h'))]

/-- After negating the second pair, swapping the two unnegated pairs
preserves the coefficient. -/
theorem fourPointHCoeff_cross_swap
    (α₁ β₁ α₂ β₂ : Z4) :
    fourPointHCoeff α₁ β₁ (-α₂) (-β₂) =
      fourPointHCoeff α₂ β₂ (-α₁) (-β₁) := by
  have hfreq :
      α₁ + β₁ + (-α₂ + -β₂) = 0 ↔
        α₂ + β₂ + (-α₁ + -β₁) = 0 := by
    constructor <;> intro h
    · calc
        α₂ + β₂ + (-α₁ + -β₁) =
            -(α₁ + β₁ + (-α₂ + -β₂)) := by abel
        _ = -0 := congrArg Neg.neg h
        _ = 0 := neg_zero
    · calc
        α₁ + β₁ + (-α₂ + -β₂) =
            -(α₂ + β₂ + (-α₁ + -β₁)) := by abel
        _ = -0 := congrArg Neg.neg h
        _ = 0 := neg_zero
  rw [fourPointHCoeff_eq_indicator,
    fourPointHCoeff_eq_indicator]
  by_cases h : α₁ + β₁ + (-α₂ + -β₂) = 0
  · rw [if_pos h, if_pos (hfreq.mp h)]
    simp only [greenModeWeight_neg]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun h' => h (hfreq.mpr h'))]

/-- Every four-point Fourier coefficient is real. -/
theorem fourPointHCoeff_im_eq_zero
    (α₁ β₁ α₂ β₂ : Z4) :
    (fourPointHCoeff α₁ β₁ α₂ β₂).im = 0 := by
  rw [fourPointHCoeff_eq_indicator]
  by_cases h : α₁ + β₁ + (α₂ + β₂) = 0
  · rw [if_pos h, ← Complex.ofReal_mul, Complex.ofReal_im]
  · rw [if_neg h]
    norm_num

theorem limitPseudoCov_comm
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (i j : Fin s) :
    limitPseudoCov lam modes i j =
      limitPseudoCov lam modes j i := by
  unfold limitPseudoCov
  rw [fourPointHCoeff_swap_pairs]

theorem limitConjCov_comm
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (i j : Fin s) :
    limitConjCov lam modes i j =
      limitConjCov lam modes j i := by
  unfold limitConjCov
  rw [fourPointHCoeff_cross_swap]

theorem limitPseudoCov_im_eq_zero
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (i j : Fin s) :
    (limitPseudoCov lam modes i j).im = 0 := by
  unfold limitPseudoCov
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    fourPointHCoeff_im_eq_zero]
  ring

theorem limitConjCov_im_eq_zero
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (i j : Fin s) :
    (limitConjCov lam modes i j).im = 0 := by
  unfold limitConjCov
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    fourPointHCoeff_im_eq_zero]
  ring

/-- The block matrix obtained by realifying the complex covariance is
symmetric (hence Hermitian over `ℝ`). -/
theorem limitCovMatrix_isHermitian
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4) :
    (limitCovMatrix lam modes).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  apply Matrix.IsSymm.ext
  intro p q
  rcases p with ⟨i, bi⟩
  rcases q with ⟨j, bj⟩
  cases bi <;> cases bj
  · simp only [limitCovMatrix]
    rw [limitPseudoCov_comm lam modes j i,
      limitConjCov_comm lam modes j i]
  · simp only [limitCovMatrix]
    simp only [Complex.add_im, Complex.sub_im]
    rw [limitPseudoCov_im_eq_zero, limitConjCov_im_eq_zero,
      limitPseudoCov_im_eq_zero, limitConjCov_im_eq_zero]
    norm_num
  · simp only [limitCovMatrix]
    simp only [Complex.add_im, Complex.sub_im]
    rw [limitPseudoCov_im_eq_zero, limitConjCov_im_eq_zero,
      limitPseudoCov_im_eq_zero, limitConjCov_im_eq_zero]
    norm_num
  · simp only [limitCovMatrix]
    rw [limitPseudoCov_comm lam modes j i,
      limitConjCov_comm lam modes j i]

/-! ## Real vectors as complex coefficients -/

/-- Inverse to `realifiedLinearCoeff`: the minus sign compensates for
the convention used by `Re (cᵢ Zᵢ)`. -/
def complexCoeffOfRealified {s : ℕ}
    (v : Fin s × Bool → ℝ) (i : Fin s) : ℂ :=
  (v (i, false) : ℂ) - Complex.I * (v (i, true) : ℂ)

@[simp]
theorem realifiedLinearCoeff_complexCoeffOfRealified
    {s : ℕ} (v : Fin s × Bool → ℝ) :
    realifiedLinearCoeff (complexCoeffOfRealified v) = v := by
  funext p
  rcases p with ⟨i, b⟩
  cases b <;>
    simp [realifiedLinearCoeff, complexCoeffOfRealified,
      Complex.mul_re, Complex.mul_im]

/-! ## The bilinear profile identity -/

theorem integrable_fourPointProfileCombination_mul_self
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Integrable
      (fun z =>
        fourPointProfileCombination modes c z *
          fourPointProfileCombination modes c z)
      paperMeasure := by
  have hcont :
      Continuous
        (fun z =>
          fourPointProfileCombination modes c z *
            fourPointProfileCombination modes c z) :=
    (continuous_fourPointProfileCombination modes c).mul
      (continuous_fourPointProfileCombination modes c)
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The non-Hermitian finite four-point form is the integral of the
square (without conjugation) of the same profile combination. -/
theorem sum_fourPointHCoeff_eq_profileCombination_sq
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    (∑ i, ∑ j,
      c i * c j *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (modes j).1 (modes j).2) =
      ∫ z : T4,
        fourPointProfileCombination modes c z *
          fourPointProfileCombination modes c z
        ∂paperMeasure := by
  have hterm : ∀ i j : Fin s,
      Integrable
        (fun z =>
          (c i *
            fourPointModeProfile (modes i).1 (modes i).2 z) *
          (c j *
            fourPointModeProfile
              (modes j).1 (modes j).2 z))
        paperMeasure := by
    intro i j
    have hcont :
        Continuous
          (fun z =>
            (c i *
              fourPointModeProfile (modes i).1 (modes i).2 z) *
            (c j *
              fourPointModeProfile
                (modes j).1 (modes j).2 z)) :=
      (continuous_const.mul
        (continuous_fourPointModeProfile
          (modes i).1 (modes i).2)).mul
        (continuous_const.mul
          (continuous_fourPointModeProfile
            (modes j).1 (modes j).2))
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∑ i, ∑ j,
        c i * c j *
          fourPointHCoeff
            (modes i).1 (modes i).2
            (modes j).1 (modes j).2) =
        ∑ i, ∑ j,
          ∫ z : T4,
            (c i *
              fourPointModeProfile (modes i).1 (modes i).2 z) *
            (c j *
              fourPointModeProfile
                (modes j).1 (modes j).2 z)
            ∂paperMeasure := by
      apply Fintype.sum_congr
      intro i
      apply Fintype.sum_congr
      intro j
      rw [fourPointHCoeff_eq_profileGram,
        ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = ∫ z : T4,
        ∑ i, ∑ j,
          (c i *
            fourPointModeProfile (modes i).1 (modes i).2 z) *
          (c j *
            fourPointModeProfile
              (modes j).1 (modes j).2 z)
        ∂paperMeasure := by
      symm
      rw [integral_finsetSum]
      · apply Fintype.sum_congr
        intro i
        rw [integral_finsetSum]
        intro j _hj
        exact hterm i j
      · intro i _hi
        exact integrable_finsetSum _ fun j _hj => hterm i j
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        unfold fourPointProfileCombination
        simp only
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]

/-! ## The scalar variance as an integral of a square -/

/-- The explicit scalar variance is the positive prefactor times the
integral of the square of the real part of a profile combination. -/
theorem limitVar_eq_integral_re_sq
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) :
    limitVar lam modes c =
      limitPrefactor lam *
        ∫ z : T4,
          (fourPointProfileCombination modes c z).re ^ 2
          ∂paperMeasure := by
  let L : T4 → ℂ := fourPointProfileCombination modes c
  have hself : Integrable (fun z => L z * L z) paperMeasure := by
    simpa only [L] using
      integrable_fourPointProfileCombination_mul_self modes c
  have hconj :
      Integrable (fun z => L z * conj (L z)) paperMeasure := by
    simpa only [L] using
      integrable_fourPointProfileCombination_mul_conj modes c
  have hsum :
      (∫ z : T4, L z * L z ∂paperMeasure).re +
          (∫ z : T4, L z * conj (L z) ∂paperMeasure).re =
        2 * ∫ z : T4, (L z).re ^ 2 ∂paperMeasure := by
    calc
      (∫ z : T4, L z * L z ∂paperMeasure).re +
          (∫ z : T4, L z * conj (L z) ∂paperMeasure).re =
          (∫ z : T4, (L z * L z).re ∂paperMeasure) +
            ∫ z : T4, (L z * conj (L z)).re
              ∂paperMeasure := by
        exact congrArg₂ (· + ·)
          (integral_re hself).symm
          (integral_re hconj).symm
      _ = ∫ z : T4,
          (L z * L z).re + (L z * conj (L z)).re
          ∂paperMeasure := by
        exact (integral_add hself.re hconj.re).symm
      _ = ∫ z : T4, 2 * (L z).re ^ 2
          ∂paperMeasure := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          simp only [Complex.mul_re, Complex.conj_re,
            Complex.conj_im]
          ring
      _ = 2 * ∫ z : T4, (L z).re ^ 2
          ∂paperMeasure := by
        rw [integral_const_mul]
  unfold limitVar
  rw [sum_fourPointHCoeff_eq_profileCombination_sq,
    sum_fourPointHCoeff_neg_eq_profileCombination]
  change
    limitPrefactor lam / 2 *
        ((∫ z : T4, L z * L z ∂paperMeasure).re +
          (∫ z : T4, L z * conj (L z) ∂paperMeasure).re) =
      limitPrefactor lam *
        ∫ z : T4, (L z).re ^ 2 ∂paperMeasure
  rw [hsum]
  ring

/-- The scalar multiplying the limiting four-point covariance is
strictly positive throughout the subcritical parameter range. -/
theorem limitPrefactor_pos
    (lam : ℝ) (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    0 < limitPrefactor lam := by
  unfold limitPrefactor
  have hden : 0 < 2 * Real.pi ^ 2 - lam ^ 2 :=
    sub_pos.mpr hlam
  exact div_pos (by positivity) hden

/-- Direct nonnegativity of the scalar limit variance, with no
separate matrix-positivity hypothesis. -/
theorem limitVar_nonneg
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2)
    (c : Fin s → ℂ) :
    0 ≤ limitVar lam modes c := by
  rw [limitVar_eq_integral_re_sq]
  apply mul_nonneg (limitPrefactor_pos lam hlam).le
  apply integral_nonneg
  intro z
  exact sq_nonneg _

/-! ## Positive semidefiniteness and unconditional corollaries -/

/-- **PSD completion of node `D-limit`.**  The explicit realified
covariance matrix is positive semidefinite for every subcritical
coupling. -/
theorem limitCovMatrix_posSemidef
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2) :
    (limitCovMatrix lam modes).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (limitCovMatrix_isHermitian lam modes) ?_
  intro v
  have hquad :=
    realifiedLinearCoeff_quadratic lam modes
      (complexCoeffOfRealified v)
  rw [realifiedLinearCoeff_complexCoeffOfRealified] at hquad
  rw [show star v = v by simp, hquad]
  exact limitVar_nonneg lam modes hlam
    (complexCoeffOfRealified v)

/-- Characteristic function of the Gaussian limit, now discharged
solely from the subcritical parameter inequality. -/
theorem charFun_gaussianLimitLaw_of_subcritical
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2)
    (t : EuclideanSpace ℝ (Fin s × Bool)) :
    charFun (gaussianLimitLaw lam modes : Measure
      (EuclideanSpace ℝ (Fin s × Bool))) t =
      Complex.exp
        (-((((t : Fin s × Bool → ℝ) ⬝ᵥ
          (limitCovMatrix lam modes).mulVec
            (t : Fin s × Bool → ℝ)) : ℝ) : ℂ) / 2) :=
  charFun_gaussianLimitLaw lam modes hlam
    (limitCovMatrix_posSemidef lam modes hlam) t

/-- Coordinate covariance of the Gaussian limit, with the PSD
obligation discharged. -/
theorem covariance_gaussianLimitLaw_of_subcritical
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2)
    (p q : Fin s × Bool) :
    cov[fun x : EuclideanSpace ℝ (Fin s × Bool) ↦ x p,
        fun x : EuclideanSpace ℝ (Fin s × Bool) ↦ x q;
        (gaussianLimitLaw lam modes :
          Measure (EuclideanSpace ℝ (Fin s × Bool)))] =
      limitCovMatrix lam modes p q :=
  covariance_gaussianLimitLaw lam modes hlam
    (limitCovMatrix_posSemidef lam modes hlam) p q

/-- Scalar characteristic-function formula for
`Re ∑ᵢ cᵢ Zᵢ`, without an extra PSD hypothesis. -/
theorem charFun_gaussianLimitLaw_realifiedLinearCoeff_of_subcritical
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hlam : lam ^ 2 < 2 * Real.pi ^ 2)
    (c : Fin s → ℂ) :
    charFun (gaussianLimitLaw lam modes :
        Measure (EuclideanSpace ℝ (Fin s × Bool)))
        (WithLp.toLp 2 (realifiedLinearCoeff c)) =
      Complex.exp (-((limitVar lam modes c : ℂ) / 2)) :=
  charFun_gaussianLimitLaw_realifiedLinearCoeff
    lam modes hlam (limitCovMatrix_posSemidef lam modes hlam) c

end

end Anderson4D
