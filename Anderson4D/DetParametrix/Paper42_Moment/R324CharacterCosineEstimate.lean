import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingCosineSeam
import Anderson4D.DetParametrix.Core.MomentReduction

/-!
# Quantitative character cosine estimate for R-324

This file supplies the deterministic Fourier estimate used at the terminal
cosine step of paper §4.2.  With the project's conventions

* `T4 = Fin 4 → AddCircle (2π)`,
* `charT4 β u = ∏ i, exp (I * βᵢ * uᵢ)`,
* `paperModeNormSq β = ∑ i βᵢ²`, and
* `torusDistSq u = ∑ i (torusLift u i)²`,

the canonical representative gives the exact identity
`charT4 β u = exp (I * ∑ i βᵢ * torusLift u i)`.  Cauchy--Schwarz and
`1 - cos θ ≤ θ² / 2` then give

`|r324CharacterCos β u - 1|
    ≤ (1 / 2) * paperModeNormSq β * torusDistSq u`.

The absolute constant `1 / 2` is the sharp scalar cosine constant.  No
compatibility or non-wrapping hypothesis is needed: the only representative
fact used below is the proved quotient identity `AddCircle.coe_equivIco`.
The final lemmas package the pointwise estimate as a norm-of-integral bound
for either half of `PrimitiveKernelBounds`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Exact phase identity and scalar estimate -/

/-- A product character is the exponential of the dot product with the
canonical componentwise lift.  This is an exact quotient identity, not a
choice of a locally compatible lift. -/
theorem charT4_eq_exp_dot_torusLift
    (β : Z4) (u : T4) :
    charT4 β u =
      Complex.exp
        (Complex.I *
          ((∑ i, (β i : ℝ) * torusLift u i : ℝ) : ℂ)) := by
  unfold charT4
  rw [show
      Complex.I *
          ((∑ i, (β i : ℝ) * torusLift u i : ℝ) : ℂ) =
        ∑ i,
          Complex.I *
            (((β i : ℝ) * torusLift u i : ℝ) : ℂ) by
      rw [Complex.ofReal_sum, Finset.mul_sum]]
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  have hcoe :
      ((torusLift u i : ℝ) : AddCircle (2 * Real.pi)) = u i := by
    exact AddCircle.coe_equivIco
  rw [← hcoe, fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- First-order character distance, expressed without choosing any
noncanonical lift. -/
theorem norm_charT4_sub_one_le_abs_dot_torusLift
    (β : Z4) (u : T4) :
    ‖charT4 β u - 1‖ ≤
      |∑ i, (β i : ℝ) * torusLift u i| := by
  rw [charT4_eq_exp_dot_torusLift]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le
      (x := ∑ i, (β i : ℝ) * torusLift u i))

/-- Cauchy--Schwarz in the exact frequency/distance normalizations used by
the paper. -/
theorem sq_abs_dot_torusLift_le
    (β : Z4) (u : T4) :
    |∑ i, (β i : ℝ) * torusLift u i| ^ 2 ≤
      paperModeNormSq β * torusDistSq u := by
  simpa only [paperModeNormSq, torusDistSq, sq_abs] using
    (Finset.sum_mul_sq_le_sq_mul_sq
      (s := Finset.univ)
      (fun i : Fin dim => (β i : ℝ))
      (fun i : Fin dim => torusLift u i))

/-- For a unit-modulus character, twice the cosine defect is exactly the
squared chordal distance to `1`. -/
theorem two_mul_abs_r324CharacterCos_sub_one_eq_norm_sq
    (β : Z4) (u : T4) :
    2 * |r324CharacterCos β u - 1| =
      ‖charT4 β u - 1‖ ^ 2 := by
  have hnormSq : Complex.normSq (charT4 β u) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_charT4]
    norm_num
  have hre : (charT4 β u).re ≤ 1 := by
    have h :=
      Complex.abs_re_le_norm (charT4 β u)
    rw [norm_charT4] at h
    exact le_trans (le_abs_self _) h
  rw [Complex.sq_norm, Complex.normSq_sub, hnormSq,
    Complex.normSq_one]
  unfold r324CharacterCos
  rw [abs_of_nonpos (sub_nonpos.mpr hre)]
  simp
  ring

/-- **Terminal cosine estimate.**  The constant `1 / 2` is the sharp
one-dimensional cosine constant; Cauchy--Schwarz introduces no further
dimension-dependent loss. -/
theorem abs_r324CharacterCos_sub_one_le_half_mul
    (β : Z4) (u : T4) :
    |r324CharacterCos β u - 1| ≤
      (1 / 2 : ℝ) * paperModeNormSq β * torusDistSq u := by
  have hnorm :=
    norm_charT4_sub_one_le_abs_dot_torusLift β u
  have hsq :
      ‖charT4 β u - 1‖ ^ 2 ≤
        |∑ i, (β i : ℝ) * torusLift u i| ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hdot := sq_abs_dot_torusLift_le β u
  rw [← two_mul_abs_r324CharacterCos_sub_one_eq_norm_sq β u] at hsq
  nlinarith

/-- The frequency-independent unit-circle bound. -/
theorem abs_r324CharacterCos_sub_one_le_two
    (β : Z4) (u : T4) :
    |r324CharacterCos β u - 1| ≤ 2 := by
  have hre :
      |(charT4 β u).re| ≤ 1 := by
    simpa only [norm_charT4] using
      Complex.abs_re_le_norm (charT4 β u)
  unfold r324CharacterCos
  calc
    |(charT4 β u).re - 1| ≤
        |(charT4 β u).re| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hre (by norm_num)
    _ = 2 := by norm_num

/-- The local quadratic estimate and the global unit-circle estimate in
the usual single `min` envelope. -/
theorem abs_r324CharacterCos_sub_one_le_min
    (β : Z4) (u : T4) :
    |r324CharacterCos β u - 1| ≤
      min 2
        ((1 / 2 : ℝ) * paperModeNormSq β * torusDistSq u) := by
  exact le_min
    (abs_r324CharacterCos_sub_one_le_two β u)
    (abs_r324CharacterCos_sub_one_le_half_mul β u)

/-! ## Majorant and integral interfaces -/

theorem paperModeNormSq_nonneg (β : Z4) :
    0 ≤ paperModeNormSq β := by
  unfold paperModeNormSq
  positivity

/-- Pointwise cosine domination for any signed real kernel controlled by a
nonnegative majorant.  Nonnegativity of `M u` follows from the stated
absolute-value bound. -/
theorem abs_mul_r324CharacterCos_sub_one_le_of_abs_le
    {J M : T4 → ℝ} (β : Z4) (u : T4)
    (hJ : |J u| ≤ M u) :
    |J u * (r324CharacterCos β u - 1)| ≤
      ((1 / 2 : ℝ) * paperModeNormSq β) *
        (torusDistSq u * M u) := by
  have hcoefficient :
      0 ≤ (1 / 2 : ℝ) * paperModeNormSq β :=
    mul_nonneg (by norm_num) (paperModeNormSq_nonneg β)
  rw [abs_mul]
  calc
    |J u| * |r324CharacterCos β u - 1| ≤
        |J u| *
          (((1 / 2 : ℝ) * paperModeNormSq β) *
            torusDistSq u) :=
      mul_le_mul_of_nonneg_left
        (abs_r324CharacterCos_sub_one_le_half_mul β u) (abs_nonneg _)
    _ ≤
        M u *
          (((1 / 2 : ℝ) * paperModeNormSq β) *
            torusDistSq u) :=
      mul_le_mul_of_nonneg_right hJ
        (mul_nonneg hcoefficient (torusDistSq_nonneg u))
    _ =
        ((1 / 2 : ℝ) * paperModeNormSq β) *
          (torusDistSq u * M u) := by ring

/-- Multiplication by the bounded torus distance preserves integrability.
This is the small adapter needed for both explicit Proposition 4.1
majorants. -/
theorem integrable_torusDistSq_mul_of_integrable
    {M : T4 → ℝ} (hM : Integrable M paperMeasure) :
    Integrable
      (fun u => torusDistSq u * M u)
      paperMeasure := by
  refine hM.bdd_mul (c := 4 * Real.pi ^ 2)
    measurable_torusDistSq.aestronglyMeasurable
    (.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (torusDistSq_nonneg u)]
  exact torusDistSq_le u

/-- Direct Bochner-integral domination by a squared-distance-weighted
majorant.  The complex cast matches the terminal cosine identity. -/
theorem norm_integral_mul_r324CharacterCos_sub_one_le_of_abs_le
    {J M : T4 → ℝ} (β : Z4)
    (hJ : ∀ u, |J u| ≤ M u)
    (hint :
      Integrable
        (fun u => torusDistSq u * M u)
        paperMeasure) :
    ‖∫ u,
        ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure‖ ≤
      ((1 / 2 : ℝ) * paperModeNormSq β) *
        ∫ u, torusDistSq u * M u ∂paperMeasure := by
  let A : ℝ := (1 / 2 : ℝ) * paperModeNormSq β
  have hscaled :
      Integrable
        (fun u => A * (torusDistSq u * M u))
        paperMeasure :=
    hint.const_mul A
  calc
    ‖∫ u,
        ((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure‖ ≤
        ∫ u,
          ‖((J u * (r324CharacterCos β u - 1) : ℝ) : ℂ)‖
          ∂paperMeasure :=
      norm_integral_le_integral_norm _
    _ ≤
        ∫ u, A * (torusDistSq u * M u)
          ∂paperMeasure := by
      refine integral_mono_of_nonneg
        (.of_forall fun u => norm_nonneg _)
        hscaled
        (.of_forall fun u => ?_)
      simpa only [A, Complex.norm_real, Real.norm_eq_abs] using
        abs_mul_r324CharacterCos_sub_one_le_of_abs_le β u (hJ u)
    _ =
        ((1 / 2 : ℝ) * paperModeNormSq β) *
          ∫ u, torusDistSq u * M u ∂paperMeasure := by
      simp only [A, integral_const_mul]

/-- The ordinary half of `PrimitiveKernelBounds`, fed directly into the
terminal cosine integral estimate. -/
theorem
    norm_integral_primitiveKernelDiff_mul_r324CharacterCos_sub_one_le
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
      ((1 / 2 : ℝ) * paperModeNormSq β) *
        ∫ u,
          torusDistSq u *
            primitiveKernelMajorant
              primitiveConstant lam ε supportConstant n u
          ∂paperMeasure := by
  apply norm_integral_mul_r324CharacterCos_sub_one_le_of_abs_le
  · exact fun u => (hbound u).1
  · exact integrable_torusDistSq_mul_of_integrable
      (integrable_primitiveKernelMajorant
        primitiveConstant lam ε supportConstant n hε)

/-- The inserted half of `PrimitiveKernelBounds`, fed directly into the
same terminal cosine integral estimate. -/
theorem
    norm_integral_primitiveKernelInsertedDiff_mul_r324CharacterCos_sub_one_le
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (supportConstant primitiveConstant : ℝ)
    (hε : 0 < ε)
    (hbound :
      PrimitiveKernelBounds ρ lam ε n hn G
        supportConstant primitiveConstant)
    (β : Z4) :
    ‖∫ u,
        ((primitiveKernelInsertedDiff ρ lam ε n hn G u *
          (r324CharacterCos β u - 1) : ℝ) : ℂ)
        ∂paperMeasure‖ ≤
      ((1 / 2 : ℝ) * paperModeNormSq β) *
        ∫ u,
          torusDistSq u *
            primitiveInsertedMajorant
              primitiveConstant lam ε supportConstant n u
          ∂paperMeasure := by
  apply norm_integral_mul_r324CharacterCos_sub_one_le_of_abs_le
  · exact fun u => (hbound u).2
  · exact integrable_torusDistSq_mul_of_integrable
      (integrable_primitiveInsertedMajorant
        primitiveConstant lam ε supportConstant n hε)

end

end Anderson4D
