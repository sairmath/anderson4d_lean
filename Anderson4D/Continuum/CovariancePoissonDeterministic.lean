import Anderson4D.Continuum.FourierCovariance
import Anderson4D.Continuum.SingularConv
import Anderson4D.Continuum.CovarianceSymmetry
import Anderson4D.Continuum.TorusFourier
import Mathlib.Analysis.Fourier.Convolution

/-!
# Poisson summation for the mollified covariance

This file identifies the absolutely convergent Fourier covariance of the
Lebesgue-normalized noise with the spatial periodization of the Euclidean
cutoff covariance.  It is the deterministic final bridge in blueprint node
`I-noise`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set ComplexConjugate
open scoped BigOperators Convolution ENNReal

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

private def poissonBox : Set R4 :=
  Set.univ.pi fun _ : Fin dim => Set.Ico (-Real.pi) Real.pi

private theorem measurableSet_poissonBox :
    MeasurableSet poissonBox :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

private def poissonQuotient (x : R4) : T4 :=
  fun i => (x i : AddCircle (2 * Real.pi))

/-- The componentwise quotient map on the canonical half-open cube
preserves Lebesgue measure. -/
private theorem measurePreserving_poissonQuotient :
    MeasurePreserving poissonQuotient
      (volume.restrict poissonBox) paperMeasure := by
  rw [paperMeasure_eq_volume]
  have h := measurePreserving_pi
    (fun _ : Fin dim =>
      volume.restrict (Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)))
    (fun _ : Fin dim =>
      (volume : Measure (AddCircle (2 * Real.pi))))
    (fun _ => AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi))
  have hperiod :
      -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [hperiod] at h
  have hcoord :
      (volume : Measure ℝ).restrict (Set.Ioc (-Real.pi) Real.pi) =
        volume.restrict (Set.Ico (-Real.pi) Real.pi) :=
    restrict_Ico_eq_restrict_Ioc.symm
  simp_rw [hcoord] at h
  have hsrc :
      (Measure.pi fun _ : Fin dim =>
        (volume : Measure ℝ).restrict (Set.Ico (-Real.pi) Real.pi)) =
        volume.restrict poissonBox := by
    rw [← Measure.restrict_pi_pi]
    rfl
  rwa [hsrc] at h

/-- On the canonical half-open cube, quotienting and lifting is the
identity in every coordinate. -/
private theorem torusLift_poissonQuotient
    {x : R4} (hx : x ∈ poissonBox) :
    torusLift (poissonQuotient x) = x := by
  funext i
  have hi := hx i (Set.mem_univ i)
  apply AddCircle.equivIco_coe_of_mem
  simpa [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hi

/-- The translate of the canonical cube indexed by `k ∈ ℤ⁴`. -/
private def poissonBoxAt (k : Z4) : Set R4 :=
  Set.univ.pi fun i : Fin dim =>
    Set.Ico
      (-Real.pi + (k i) • (2 * Real.pi))
      (-Real.pi + (k i + 1) • (2 * Real.pi))

private theorem measurableSet_poissonBoxAt (k : Z4) :
    MeasurableSet (poissonBoxAt k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

private theorem pairwise_disjoint_poissonBoxAt :
    Pairwise (Function.onFun Disjoint poissonBoxAt) := by
  have hcoord :
      ∀ _i : Fin dim,
        Pairwise (Function.onFun Disjoint fun n : ℤ =>
          Set.Ico
            (-Real.pi + n • (2 * Real.pi))
            (-Real.pi + (n + 1) • (2 * Real.pi))) :=
    fun _ => Set.pairwise_disjoint_Ico_add_zsmul _ _
  have hcoord' :
      ∀ i : Fin dim,
        (Set.univ : Set ℤ).PairwiseDisjoint fun n =>
          Set.Ico
            (-Real.pi + n • (2 * Real.pi))
            (-Real.pi + (n + 1) • (2 * Real.pi)) := by
    intro i a ha b hb hab
    exact hcoord i hab
  have hpi :=
    Set.pairwiseDisjoint_pi (s := fun _ : Fin dim => Set.univ) hcoord'
  intro k l hkl
  exact hpi (by simp) (by simp) hkl

private theorem iUnion_poissonBoxAt :
    (⋃ k : Z4, poissonBoxAt k) = Set.univ := by
  rw [show (⋃ k : Z4, poissonBoxAt k) =
      Set.univ.pi (fun i : Fin dim =>
        ⋃ n : ℤ,
          Set.Ico
            (-Real.pi + n • (2 * Real.pi))
            (-Real.pi + (n + 1) • (2 * Real.pi))) by
    exact Set.iUnion_univ_pi
      (fun (_i : Fin dim) (n : ℤ) =>
        Set.Ico
          (-Real.pi + n • (2 * Real.pi))
          (-Real.pi + (n + 1) • (2 * Real.pi)))]
  simp only [iUnion_Ico_add_zsmul (by positivity : 0 < 2 * Real.pi)]
  ext x
  simp

/-- Translation by the period vector sends the canonical cube onto its
`k`-th lattice translate. -/
private theorem image_add_covariancePeriodVector_poissonBox
    (k : Z4) :
    (fun x : R4 => x + covariancePeriodVector k) '' poissonBox =
      poissonBoxAt k := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i hi
    have hxi := hx i (Set.mem_univ i)
    constructor
    · dsimp only [Pi.add_apply, covariancePeriodVector]
      simp only [zsmul_eq_mul]
      calc
        -Real.pi + (k i : ℝ) * (2 * Real.pi) =
            -Real.pi + 2 * Real.pi * (k i : ℝ) := by ring
        _ ≤ x i + 2 * Real.pi * (k i : ℝ) :=
          by simpa [add_comm] using
            add_le_add_right hxi.1 (2 * Real.pi * (k i : ℝ))
    · dsimp only [Pi.add_apply, covariancePeriodVector]
      simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one]
      calc
        x i + 2 * Real.pi * (k i : ℝ) <
            Real.pi + 2 * Real.pi * (k i : ℝ) :=
          by simpa [add_comm] using
            add_lt_add_right hxi.2 (2 * Real.pi * (k i : ℝ))
        _ = -Real.pi + ((k i : ℝ) + 1) * (2 * Real.pi) := by ring
  · intro hy
    let x : R4 := y - covariancePeriodVector k
    refine ⟨x, ?_, by simp [x]⟩
    intro i hi
    have hyi := hy i (Set.mem_univ i)
    constructor
    · dsimp only [x, Pi.sub_apply, covariancePeriodVector]
      simp only [zsmul_eq_mul] at hyi ⊢
      calc
        -Real.pi =
            (-Real.pi + (k i : ℝ) * (2 * Real.pi)) -
              2 * Real.pi * (k i : ℝ) := by ring
        _ ≤ y i - 2 * Real.pi * (k i : ℝ) :=
          sub_le_sub_right hyi.1 _
    · dsimp only [x, Pi.sub_apply, covariancePeriodVector]
      simp only [zsmul_eq_mul, Int.cast_add, Int.cast_one] at hyi ⊢
      calc
        y i - 2 * Real.pi * (k i : ℝ) <
            (-Real.pi + ((k i : ℝ) + 1) * (2 * Real.pi)) -
              2 * Real.pi * (k i : ℝ) :=
          sub_lt_sub_right hyi.2 _
        _ = Real.pi := by ring

/-- Integrating an integrable function over all lattice translates of
the fundamental cube recovers its integral over `ℝ⁴`. -/
private theorem hasSum_integral_poissonBoxAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : R4 → E} (hf : Integrable f) :
    HasSum
      (fun k : Z4 => ∫ x in poissonBoxAt k, f x)
      (∫ x : R4, f x) := by
  have h := MeasureTheory.hasSum_integral_iUnion
    (fun k : Z4 => measurableSet_poissonBoxAt k)
    pairwise_disjoint_poissonBoxAt
    (hf.integrableOn :
      IntegrableOn f (⋃ k : Z4, poissonBoxAt k))
  rw [iUnion_poissonBoxAt] at h
  simpa only [Measure.restrict_univ] using h

/-- Set-integral transport from the canonical cube to one lattice
translate. -/
private theorem integral_comp_add_covariancePeriodVector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : R4 → E) (k : Z4) :
    (∫ x in poissonBox, f (x + covariancePeriodVector k)) =
      ∫ x in poissonBoxAt k, f x := by
  have h :=
    (measurePreserving_add_right (volume : Measure R4)
      (covariancePeriodVector k)).setIntegral_image_emb
      (MeasurableEquiv.addRight
        (covariancePeriodVector k)).measurableEmbedding
      f poissonBox
  rw [image_add_covariancePeriodVector_poissonBox] at h
  exact h.symm

/-- Tiling in the translated-integrand form used to unfold a
periodization on the base cube. -/
private theorem hasSum_integral_comp_add_covariancePeriodVector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : R4 → E} (hf : Integrable f) :
    HasSum
      (fun k : Z4 =>
        ∫ x in poissonBox, f (x + covariancePeriodVector k))
      (∫ x : R4, f x) := by
  exact (hasSum_integral_poissonBoxAt hf).congr_fun
    (fun k => integral_comp_add_covariancePeriodVector f k)

/-! ## Euclidean covariance Fourier transform -/

/-- The negative-exponential character used by `fourierR4`. -/
private def negativeCharR4 (ξ x : R4) : ℂ :=
  Complex.exp (-Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ))

private theorem negativeCharR4_add (ξ x y : R4) :
    negativeCharR4 ξ (x + y) =
      negativeCharR4 ξ x * negativeCharR4 ξ y := by
  unfold negativeCharR4
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  push_cast
  ring

private theorem norm_negativeCharR4 (ξ x : R4) :
    ‖negativeCharR4 ξ x‖ = 1 := by
  rw [negativeCharR4, Complex.norm_exp]
  have him :
      (-Complex.I * ((∑ i, x i * ξ i : ℝ) : ℂ)).re = 0 := by
    simp
  rw [him, Real.exp_zero]

private theorem continuous_negativeCharR4 (ξ : R4) :
    Continuous (negativeCharR4 ξ) := by
  unfold negativeCharR4
  fun_prop

/-- Flipping all four coordinates is global negation.  This packages the
single-coordinate evenness in `MemEClassR4` into the form needed below. -/
private theorem cutoff_neg (x : R4) :
    ρ (-x) = ρ x := by
  let x₀ : R4 := -x
  let x₁ : R4 := coordinateFlipR4 0 x₀
  let x₂ : R4 := coordinateFlipR4 1 x₁
  let x₃ : R4 := coordinateFlipR4 2 x₂
  let x₄ : R4 := coordinateFlipR4 3 x₃
  have h₀ : ρ x₁ = ρ x₀ := ρ.memE.even_coord 0 x₀
  have h₁ : ρ x₂ = ρ x₁ := ρ.memE.even_coord 1 x₁
  have h₂ : ρ x₃ = ρ x₂ := ρ.memE.even_coord 2 x₂
  have h₃ : ρ x₄ = ρ x₃ := ρ.memE.even_coord 3 x₃
  have hx₄ : x₄ = x := by
    funext i
    fin_cases i <;>
      simp [x₄, x₃, x₂, x₁, x₀, coordinateFlipR4]
  calc
    ρ (-x) = ρ x₀ := rfl
    _ = ρ x₁ := h₀.symm
    _ = ρ x₂ := h₁.symm
    _ = ρ x₃ := h₂.symm
    _ = ρ x₄ := h₃.symm
    _ = ρ x := by rw [hx₄]

/-- Hyperoctahedral symmetry makes the cutoff Fourier transform even. -/
private theorem fourierR4_cutoff_neg (ξ : R4) :
    fourierR4 ρ (-ξ) = fourierR4 ρ ξ := by
  unfold fourierR4
  calc
    (∫ x : R4,
        Complex.exp (-Complex.I * (↑(∑ i, x i * (-ξ) i) : ℂ)) *
          (ρ x : ℂ)) =
        ∫ x : R4,
          (Complex.exp
              (-Complex.I * (↑(∑ i, (-x) i * (-ξ) i) : ℂ)) *
            (ρ (-x) : ℂ)) := by
      rw [integral_neg_eq_self
        (fun x : R4 =>
          Complex.exp
              (-Complex.I * (↑(∑ i, x i * (-ξ) i) : ℂ)) *
            (ρ x : ℂ)) volume]
    _ = ∫ x : R4,
        Complex.exp (-Complex.I * (↑(∑ i, x i * ξ i) : ℂ)) *
          (ρ x : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [cutoff_neg]
      congr 2
      simp

private theorem fourierR4_cutoff_eq_conj (ξ : R4) :
    fourierR4 ρ ξ = conj (fourierR4 ρ ξ) := by
  rw [← fourierR4_neg_eq_conj, fourierR4_cutoff_neg]

/-- The Euclidean covariance is an integrable convolution. -/
private theorem integrable_eta :
    Integrable ρ.eta := by
  change Integrable
    ((ρ : R4 → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ] (ρ : R4 → ℝ))
  exact ρ.integrable.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) ρ.integrable

/-- The Euclidean covariance is continuous. -/
private theorem continuous_eta :
    Continuous ρ.eta := by
  change Continuous
    ((ρ : R4 → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ] (ρ : R4 → ℝ))
  exact ρ.hasCompactSupport.continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ)
    ρ.integrable.locallyIntegrable ρ.continuous

private theorem integrable_cutoffTwist (ξ : R4) :
    Integrable fun x : R4 => negativeCharR4 ξ x * (ρ x : ℂ) := by
  have hρ :
      Integrable fun x : R4 => (ρ x : ℂ) :=
    Complex.ofRealCLM.integrable_comp ρ.integrable
  exact hρ.bdd_mul
    (continuous_negativeCharR4 ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [norm_negativeCharR4])

/-- Multiplicativity of the exponential character turns the twisted
covariance into the convolution of two twisted cutoffs. -/
private theorem negativeCharR4_mul_eta_eq_convolution
    (ξ x : R4) :
    negativeCharR4 ξ x * (ρ.eta x : ℂ) =
      ((fun y : R4 => negativeCharR4 ξ y * (ρ y : ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ]
      (fun y : R4 => negativeCharR4 ξ y * (ρ y : ℂ))) x := by
  change
    negativeCharR4 ξ x * (↑(∫ y : R4, ρ y * ρ (x - y)) : ℂ) =
      ∫ y : R4,
        (negativeCharR4 ξ y * (ρ y : ℂ)) *
          (negativeCharR4 ξ (x - y) * (ρ (x - y) : ℂ))
  rw [← integral_complex_ofReal, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [Complex.ofReal_mul]
  have hadd :
      negativeCharR4 ξ x =
        negativeCharR4 ξ y * negativeCharR4 ξ (x - y) := by
    rw [← negativeCharR4_add]
    congr 1
    abel
  rw [hadd]
  ring

/-- Exact Fourier transform of `η = ρ ⋆ ρ`.  Evenness of `ρ` converts
the square of its Fourier transform into the squared norm. -/
private theorem integral_negativeCharR4_mul_eta (ξ : R4) :
    (∫ x : R4, negativeCharR4 ξ x * (ρ.eta x : ℂ)) =
      ((‖fourierR4 ρ ξ‖ ^ 2 : ℝ) : ℂ) := by
  let f : R4 → ℂ :=
    fun x => negativeCharR4 ξ x * (ρ x : ℂ)
  have hf : Integrable f := ρ.integrable_cutoffTwist ξ
  calc
    (∫ x : R4, negativeCharR4 ξ x * (ρ.eta x : ℂ)) =
        ∫ x : R4,
          (f ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact ρ.negativeCharR4_mul_eta_eq_convolution ξ x
    _ = (∫ x : R4, f x) * ∫ x : R4, f x := by
      simpa using
        integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hf
    _ = fourierR4 ρ ξ * fourierR4 ρ ξ := by
      rfl
    _ = fourierR4 ρ ξ * conj (fourierR4 ρ ξ) := by
      rw [← fourierR4_cutoff_eq_conj]
    _ = ((‖fourierR4 ρ ξ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, ← Complex.sq_norm]

/-! ## Rescaling -/

/-- Euclidean covariance at scale `ε`, before lattice periodization. -/
private def etaRescaledR4 (ε : ℝ) (x : R4) : ℝ :=
  ε⁻¹ ^ (dim : ℕ) * ρ.eta (ε⁻¹ • x)

private theorem integrable_etaRescaledR4
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (ρ.etaRescaledR4 ε) := by
  unfold etaRescaledR4
  exact (ρ.integrable_eta.comp_smul (inv_ne_zero hε.ne')).const_mul _

private theorem negativeCharR4_smul (ξ x : R4) (a : ℝ) :
    negativeCharR4 ξ (a • x) =
      negativeCharR4 (a • ξ) x := by
  unfold negativeCharR4
  congr 2
  push_cast
  simp only [Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

private theorem negativeCharR4_scaled_inv
    {ε : ℝ} (hε : 0 < ε) (ξ x : R4) :
    negativeCharR4 (ε • ξ) (ε⁻¹ • x) =
      negativeCharR4 ξ x := by
  rw [negativeCharR4_smul]
  congr 1
  funext i
  simp [hε.ne']

/-- Fourier transform of the scaled Euclidean covariance. -/
private theorem integral_negativeCharR4_mul_etaRescaledR4
    {ε : ℝ} (hε : 0 < ε) (ξ : R4) :
    (∫ x : R4,
      negativeCharR4 ξ x * (ρ.etaRescaledR4 ε x : ℂ)) =
      ((‖fourierR4 ρ (ε • ξ)‖ ^ 2 : ℝ) : ℂ) := by
  let g : R4 → ℂ :=
    fun x => negativeCharR4 (ε • ξ) x * (ρ.eta x : ℂ)
  have hpoint : ∀ x : R4,
      negativeCharR4 ξ x * (ρ.etaRescaledR4 ε x : ℂ) =
        ((ε⁻¹ ^ (dim : ℕ) : ℝ) : ℂ) * g (ε⁻¹ • x) := by
    intro x
    unfold etaRescaledR4 g
    rw [negativeCharR4_scaled_inv hε]
    push_cast
    ring
  calc
    (∫ x : R4,
        negativeCharR4 ξ x * (ρ.etaRescaledR4 ε x : ℂ)) =
        ∫ x : R4,
          ((ε⁻¹ ^ (dim : ℕ) : ℝ) : ℂ) *
            g (ε⁻¹ • x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ((ε⁻¹ ^ (dim : ℕ) : ℝ) : ℂ) *
        ∫ x : R4, g (ε⁻¹ • x) := by
      rw [integral_const_mul]
    _ = ((ε⁻¹ ^ (dim : ℕ) : ℝ) : ℂ) *
        ((ε ^ Module.finrank ℝ R4 : ℝ) •
          ∫ x : R4, g x) := by
      rw [(volume : Measure R4).integral_comp_inv_smul_of_nonneg
        g hε.le]
    _ = ∫ x : R4, g x := by
      simp only [Module.finrank_pi, Fintype.card_fin, dim,
        Complex.real_smul]
      rw [← mul_assoc]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hε.ne']
    _ = ((‖fourierR4 ρ (ε • ξ)‖ ^ 2 : ℝ) : ℂ) := by
      exact ρ.integral_negativeCharR4_mul_eta (ε • ξ)

/-! ## Characters and periodization on the fundamental cube -/

private def latticeFrequencyR4 (q : Z4) : R4 :=
  fun i => (q i : ℝ)

private theorem conj_charT4_poissonQuotient (q : Z4) (x : R4) :
    conj (charT4 q (poissonQuotient x)) =
      negativeCharR4 (latticeFrequencyR4 q) x := by
  rw [conj_charT4]
  unfold charT4 poissonQuotient negativeCharR4 latticeFrequencyR4
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.neg_apply, Int.cast_neg]
  field_simp [hpi]

private theorem poissonQuotient_add_covariancePeriodVector
    (x : R4) (k : Z4) :
    poissonQuotient (x + covariancePeriodVector k) =
      poissonQuotient x := by
  funext i
  unfold poissonQuotient covariancePeriodVector
  simp only [Pi.add_apply]
  rw [show
      x i + 2 * Real.pi * (k i : ℝ) =
        x i + (k i) • (2 * Real.pi) by
    simp only [zsmul_eq_mul]
    ring]
  simp

private theorem negativeCharR4_add_covariancePeriodVector
    (q k : Z4) (x : R4) :
    negativeCharR4 (latticeFrequencyR4 q)
        (x + covariancePeriodVector k) =
      negativeCharR4 (latticeFrequencyR4 q) x := by
  rw [← conj_charT4_poissonQuotient,
    poissonQuotient_add_covariancePeriodVector,
    conj_charT4_poissonQuotient]

/-- On the fundamental cube, the torus periodization is literally the
sum of translates of the scaled Euclidean covariance. -/
private theorem etaEpsT4_poissonQuotient
    {ε : ℝ} (x : R4) (hx : x ∈ poissonBox) :
    (ρ.etaEpsT4 ε (poissonQuotient x) : ℂ) =
      ∑' k : Z4,
        (ρ.etaRescaledR4 ε
          (x + covariancePeriodVector k) : ℂ) := by
  rw [etaEpsT4_eq_tsum_etaPeriodTerm]
  push_cast
  apply tsum_congr
  intro k
  unfold etaPeriodTerm etaRescaledR4
  rw [torusLift_poissonQuotient hx]
  congr 2

/-- Every positive-scale periodized covariance is Borel measurable. -/
theorem measurable_etaEpsT4 (ε : ℝ) :
    Measurable (ρ.etaEpsT4 ε) := by
  unfold SmoothCutoff.etaEpsT4
  apply Measurable.tsum
  intro k
  apply Measurable.const_mul
  exact ρ.continuous_eta.measurable.comp
    (measurable_pi_lambda _ fun i =>
      (measurable_const.mul
        (((measurable_pi_apply i).comp measurable_torusLift).add
          measurable_const)))

/-! ## Fourier coefficient of the periodization -/

/-- The periodization/tiling identity after multiplication by one
negative character. -/
private theorem integral_poissonBox_periodizedTwist
    {ε : ℝ} (hε : 0 < ε) (q : Z4) :
    (∫ x in poissonBox,
      negativeCharR4 (latticeFrequencyR4 q) x *
        (ρ.etaEpsT4 ε (poissonQuotient x) : ℂ)) =
      ((‖ρ.symbol ε q‖ ^ 2 : ℝ) : ℂ) := by
  let g : R4 → ℂ :=
    fun x =>
      negativeCharR4 (latticeFrequencyR4 q) x *
        (ρ.etaRescaledR4 ε x : ℂ)
  let F : Z4 → R4 → ℂ :=
    fun k x => g (x + covariancePeriodVector k)
  have hηc :
      Integrable fun x : R4 => (ρ.etaRescaledR4 ε x : ℂ) :=
    Complex.ofRealCLM.integrable_comp
      (ρ.integrable_etaRescaledR4 hε)
  have hg : Integrable g := by
    exact hηc.bdd_mul
      (continuous_negativeCharR4
        (latticeFrequencyR4 q)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [norm_negativeCharR4])
  have hFint :
      ∀ k : Z4, Integrable (F k) (volume.restrict poissonBox) := by
    intro k
    exact
      (hg.comp_add_right
        (covariancePeriodVector k)).integrableOn
  have hFnorm :
      Summable fun k : Z4 =>
        ∫ x in poissonBox, ‖F k x‖ := by
    exact
      (hasSum_integral_comp_add_covariancePeriodVector
        hg.norm).summable.congr fun k => rfl
  have hswap :
      (∑' k : Z4, ∫ x in poissonBox, F k x) =
        ∫ x in poissonBox, ∑' k : Z4, F k x :=
    integral_tsum_of_summable_integral_norm hFint hFnorm
  have hperiodized :
      ∀ x ∈ poissonBox,
        negativeCharR4 (latticeFrequencyR4 q) x *
            (ρ.etaEpsT4 ε (poissonQuotient x) : ℂ) =
          ∑' k : Z4, F k x := by
    intro x hx
    rw [etaEpsT4_poissonQuotient ρ x hx]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    unfold F g
    rw [negativeCharR4_add_covariancePeriodVector]
  calc
    (∫ x in poissonBox,
        negativeCharR4 (latticeFrequencyR4 q) x *
          (ρ.etaEpsT4 ε (poissonQuotient x) : ℂ)) =
        ∫ x in poissonBox, ∑' k : Z4, F k x :=
      setIntegral_congr_fun measurableSet_poissonBox hperiodized
    _ = ∑' k : Z4, ∫ x in poissonBox, F k x :=
      hswap.symm
    _ = ∫ x : R4, g x :=
      (hasSum_integral_comp_add_covariancePeriodVector hg).tsum_eq
    _ = ((‖fourierR4 ρ
          (ε • latticeFrequencyR4 q)‖ ^ 2 : ℝ) : ℂ) := by
      exact ρ.integral_negativeCharR4_mul_etaRescaledR4 hε
        (latticeFrequencyR4 q)
    _ = ((‖ρ.symbol ε q‖ ^ 2 : ℝ) : ℂ) := by
      congr 3

/-- Exact unnormalized (`paperMeasure`) Fourier coefficient of the
periodized covariance. -/
private theorem paperIntegral_conj_char_mul_etaEpsT4
    {ε : ℝ} (hε : 0 < ε) (q : Z4) :
    (∫ z : T4,
      conj (charT4 q z) * (ρ.etaEpsT4 ε z : ℂ)
        ∂paperMeasure) =
      ((‖ρ.symbol ε q‖ ^ 2 : ℝ) : ℂ) := by
  let f : T4 → ℂ :=
    fun z => conj (charT4 q z) * (ρ.etaEpsT4 ε z : ℂ)
  have hfmeas : Measurable f := by
    exact (continuous_charT4 q).star.measurable.mul
      (Complex.continuous_ofReal.measurable.comp
        (ρ.measurable_etaEpsT4 ε))
  have htransport :=
    integral_map
      measurePreserving_poissonQuotient.aemeasurable
      (show AEStronglyMeasurable f
          (Measure.map poissonQuotient
            (volume.restrict poissonBox)) by
        exact hfmeas.aestronglyMeasurable)
  rw [measurePreserving_poissonQuotient.map_eq] at htransport
  calc
    (∫ z : T4,
        conj (charT4 q z) * (ρ.etaEpsT4 ε z : ℂ)
          ∂paperMeasure) =
        ∫ x in poissonBox, f (poissonQuotient x) :=
      htransport
    _ = ∫ x in poissonBox,
        negativeCharR4 (latticeFrequencyR4 q) x *
          (ρ.etaEpsT4 ε (poissonQuotient x) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_poissonBox
      intro x hx
      dsimp only [f]
      rw [conj_charT4_poissonQuotient]
    _ = ((‖ρ.symbol ε q‖ ^ 2 : ℝ) : ℂ) :=
      ρ.integral_poissonBox_periodizedTwist hε q

private theorem whiteNoiseFourierScale_sq_mul_volume :
    (NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2 *
      ((((2 * Real.pi) ^ dim : ℝ) : ℂ)) = 1 := by
  unfold NoiseModel.whiteNoiseFourierScale dim
  have h : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  push_cast
  norm_num [zpow_neg]
  field_simp

/-- Probability-Haar Fourier coefficient, with the exact reciprocal
volume factor supplied by the white-noise half-density. -/
private theorem torusFourierCoeff_etaEpsT4
    {ε : ℝ} (hε : 0 < ε) (q : Z4) :
    torusFourierCoeff
        (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ)) q =
      (NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2 *
        ((‖ρ.symbol ε q‖ ^ 2 : ℝ) : ℂ) := by
  have hpaper :=
    ρ.paperIntegral_conj_char_mul_etaEpsT4 hε q
  have hvolume :
      (∫ z : T4,
        conj (charT4 q z) * (ρ.etaEpsT4 ε z : ℂ)
          ∂paperMeasure) =
        ((((2 * Real.pi) ^ dim : ℝ) : ℂ)) *
          torusFourierCoeff
            (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ)) q := by
    have h2π :
        (ENNReal.ofReal ((2 * Real.pi) ^ dim)).toReal =
          (2 * Real.pi) ^ dim :=
      ENNReal.toReal_ofReal (by positivity)
    simp only [paperMeasure, integral_smul_measure, h2π,
      Complex.real_smul, torusFourierCoeff]
  rw [hvolume] at hpaper
  calc
    torusFourierCoeff
        (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ)) q =
        1 * torusFourierCoeff
          (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ)) q := by
      rw [one_mul]
    _ = ((NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2 *
          ((((2 * Real.pi) ^ dim : ℝ) : ℂ))) *
        torusFourierCoeff
          (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ)) q := by
      rw [whiteNoiseFourierScale_sq_mul_volume]
    _ = (NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2 *
        (((((2 * Real.pi) ^ dim : ℝ) : ℂ)) *
          torusFourierCoeff
            (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ)) q) := by
      ring
    _ = (NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2 *
        ((‖ρ.symbol ε q‖ ^ 2 : ℝ) : ℂ) := by
      rw [hpaper]

/-! ## The absolutely convergent torus Fourier series -/

/-- One Fourier coefficient of the Lebesgue-normalized cutoff
covariance. -/
def covarianceModeCoeff (ε : ℝ) (k : Z4) : ℂ :=
  (NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2 *
    ((‖ρ.symbol ε k‖ ^ 2 : ℝ) : ℂ)

/-- The absolutely convergent complex Fourier series of the cutoff
covariance.  Its values are real, but the complex form is the useful
one for frequency routing. -/
def complexFourierCovarianceT4
    (ε : ℝ) (z : T4) : ℂ :=
  ∑' k : Z4, ρ.covarianceModeCoeff ε k * charT4 k z

theorem summable_norm_covarianceModeCoeff
    {ε : ℝ} (hε : 0 < ε) :
    Summable fun k : Z4 => ‖ρ.covarianceModeCoeff ε k‖ := by
  have hsq :
      Summable fun k : Z4 => ‖ρ.symbol ε k‖ ^ 2 := by
    exact (ρ.summable_norm_symbol hε).of_nonneg_of_le
      (fun k => sq_nonneg _)
      (fun k => by
        have hnonneg := norm_nonneg (ρ.symbol ε k)
        have hle := ρ.norm_symbol_le_one ε k
        nlinarith)
  exact
    (hsq.mul_left
      ‖(NoiseModel.whiteNoiseFourierScale : ℂ) ^ 2‖).congr
      (fun k => by
        unfold covarianceModeCoeff
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _)])

private theorem continuous_complexFourierCovarianceT4
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (ρ.complexFourierCovarianceT4 ε) := by
  unfold complexFourierCovarianceT4
  apply continuous_tsum
  · intro k
    exact continuous_const.mul (continuous_charT4 k)
  · exact ρ.summable_norm_covarianceModeCoeff hε
  · intro k z
    rw [norm_mul, norm_charT4, mul_one]

private theorem torusFourierCoeff_complexFourierCovarianceT4
    {ε : ℝ} (hε : 0 < ε) (q : Z4) :
    torusFourierCoeff (ρ.complexFourierCovarianceT4 ε) q =
      ρ.covarianceModeCoeff ε q := by
  let G : Z4 → T4 → ℂ :=
    fun k z =>
      conj (charT4 q z) *
        (ρ.covarianceModeCoeff ε k * charT4 k z)
  have hGint :
      ∀ k : Z4, Integrable (G k) haarT4 := by
    intro k
    exact
      ((continuous_charT4 q).star.mul
        (continuous_const.mul
          (continuous_charT4 k))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hGsum :
      Summable fun k : Z4 =>
        ∫ z : T4, ‖G k z‖ ∂haarT4 := by
    exact
      (ρ.summable_norm_covarianceModeCoeff hε).congr
        (fun k => by
          simp only [G, norm_mul, Complex.norm_conj, norm_charT4,
            mul_one]
          rw [integral_const]
          simp [haarT4])
  have hswap :
      (∑' k : Z4, ∫ z : T4, G k z ∂haarT4) =
        ∫ z : T4, ∑' k : Z4, G k z ∂haarT4 :=
    integral_tsum_of_summable_integral_norm hGint hGsum
  calc
    torusFourierCoeff (ρ.complexFourierCovarianceT4 ε) q =
        ∫ z : T4, ∑' k : Z4, G k z ∂haarT4 := by
      unfold torusFourierCoeff complexFourierCovarianceT4
      apply integral_congr_ae
      filter_upwards with z
      rw [← tsum_mul_left]
    _ = ∑' k : Z4, ∫ z : T4, G k z ∂haarT4 :=
      hswap.symm
    _ = ∑' k : Z4,
        if k = q then ρ.covarianceModeCoeff ε k else 0 := by
      apply tsum_congr
      intro k
      unfold G
      calc
        (∫ z : T4,
            conj (charT4 q z) *
              (ρ.covarianceModeCoeff ε k * charT4 k z)
              ∂haarT4) =
            ρ.covarianceModeCoeff ε k *
              ∫ z : T4,
                charT4 k z * conj (charT4 q z) ∂haarT4 := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with z
          ring
        _ = if k = q then ρ.covarianceModeCoeff ε k else 0 := by
          rw [charT4_orthogonality]
          split_ifs <;> simp_all
    _ = ρ.covarianceModeCoeff ε q := by
      simp

/-! ## Fixed-scale boundedness of the periodization -/

/-- Unlike `covariancePeriodRadius`, this radius is allowed to depend on
an arbitrary positive scale and therefore does not require `ε ≤ 1`. -/
private def covariancePeriodRadiusAt (ε : ℝ) : ℤ :=
  ⌈(2 * ρ.radius * ε + Real.pi) / (2 * Real.pi)⌉

private def covariancePeriodBoxAt (ε : ℝ) : Finset Z4 :=
  Fintype.piFinset fun _ : Fin dim =>
    Finset.Icc (-ρ.covariancePeriodRadiusAt ε)
      (ρ.covariancePeriodRadiusAt ε)

private theorem etaPeriodTerm_ne_zero_mem_covariancePeriodBoxAt
    {ε : ℝ} (hε : 0 < ε) (z : T4) {k : Z4}
    (hk : ρ.etaPeriodTerm ε z k ≠ 0) :
    k ∈ ρ.covariancePeriodBoxAt ε := by
  have heta :
      ρ.eta (fun i => ε⁻¹ *
        (torusLift z i + 2 * Real.pi * (k i : ℝ))) ≠ 0 :=
    (mul_ne_zero_iff.mp hk).2
  have hsupport := ρ.norm_lt_two_radius_of_eta_ne_zero heta
  change ‖ε⁻¹ • periodicDisplacement z k‖ <
    2 * ρ.radius at hsupport
  have hdisp :
      ‖periodicDisplacement z k‖ < 2 * ρ.radius * ε := by
    have hscaled :
        ε⁻¹ * ‖periodicDisplacement z k‖ < 2 * ρ.radius := by
      simpa [norm_smul, abs_of_pos hε, abs_inv] using hsupport
    calc
      ‖periodicDisplacement z k‖ =
          ε * (ε⁻¹ * ‖periodicDisplacement z k‖) := by
        field_simp
      _ < ε * (2 * ρ.radius) :=
        mul_lt_mul_of_pos_left hscaled hε
      _ = 2 * ρ.radius * ε := by ring
  unfold covariancePeriodBoxAt
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hcoord :
      |torusLift z i + 2 * Real.pi * (k i : ℝ)|
        < 2 * ρ.radius * ε := by
    calc
      |torusLift z i + 2 * Real.pi * (k i : ℝ)| =
          ‖periodicDisplacement z k i‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖periodicDisplacement z k‖ :=
        norm_le_pi_norm _ _
      _ < 2 * ρ.radius * ε := hdisp
  have hlift : |torusLift z i| ≤ Real.pi := by
    obtain ⟨hlo, hhi⟩ := torusLift_mem_Ico z i
    rw [abs_le]
    exact ⟨hlo, hhi.le⟩
  have hperiod :
      |2 * Real.pi * (k i : ℝ)|
        < 2 * ρ.radius * ε + Real.pi := by
    calc
      |2 * Real.pi * (k i : ℝ)| =
          |(torusLift z i + 2 * Real.pi * (k i : ℝ)) -
            torusLift z i| := by
        congr 1
        ring
      _ ≤ |torusLift z i + 2 * Real.pi * (k i : ℝ)| +
          |torusLift z i| := abs_sub _ _
      _ < 2 * ρ.radius * ε + Real.pi :=
        add_lt_add_of_lt_of_le hcoord hlift
  have hkabs :
      |(k i : ℝ)| <
        (2 * ρ.radius * ε + Real.pi) / (2 * Real.pi) := by
    rw [abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hperiod
    exact (lt_div_iff₀
      (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      (by simpa [mul_comm] using hperiod)
  have hceil :
      (2 * ρ.radius * ε + Real.pi) / (2 * Real.pi) ≤
        (ρ.covariancePeriodRadiusAt ε : ℝ) :=
    Int.le_ceil _
  have hkupperReal :
      (k i : ℝ) ≤ (ρ.covariancePeriodRadiusAt ε : ℝ) :=
    (le_abs_self _).trans (hkabs.le.trans hceil)
  have hklowerReal :
      (-(ρ.covariancePeriodRadiusAt ε : ℤ) : ℝ) ≤
        (k i : ℝ) := by
    have hneg :
        -(ρ.covariancePeriodRadiusAt ε : ℝ) ≤
          -|(k i : ℝ)| :=
      neg_le_neg (hkabs.le.trans hceil)
    exact hneg.trans (neg_abs_le _)
  constructor
  · exact_mod_cast hklowerReal
  · exact_mod_cast hkupperReal

private theorem etaEpsT4_eq_sum_covariancePeriodBoxAt
    {ε : ℝ} (hε : 0 < ε) (z : T4) :
    ρ.etaEpsT4 ε z =
      ∑ k ∈ ρ.covariancePeriodBoxAt ε,
        ρ.etaPeriodTerm ε z k := by
  rw [etaEpsT4_eq_tsum_etaPeriodTerm]
  exact tsum_eq_sum fun k hk => by
    by_contra hne
    exact hk
      (ρ.etaPeriodTerm_ne_zero_mem_covariancePeriodBoxAt hε z hne)

private theorem exists_etaEpsT4_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ z : T4, ρ.etaEpsT4 ε z ≤ B := by
  obtain ⟨C, hCpos, hC⟩ := ρ.exists_pos_eta_uniform_bound
  let B : ℝ :=
    (ρ.covariancePeriodBoxAt ε).card *
      (ε⁻¹ ^ (dim : ℕ) * C)
  refine ⟨B, fun z => ?_⟩
  rw [ρ.etaEpsT4_eq_sum_covariancePeriodBoxAt hε z]
  calc
    (∑ k ∈ ρ.covariancePeriodBoxAt ε,
        ρ.etaPeriodTerm ε z k) ≤
        ∑ _k ∈ ρ.covariancePeriodBoxAt ε,
          ε⁻¹ ^ (dim : ℕ) * C := by
      apply Finset.sum_le_sum
      intro k hk
      unfold etaPeriodTerm
      exact mul_le_mul_of_nonneg_left
        (hC _) (pow_nonneg (inv_nonneg.mpr hε.le) _)
    _ = B := by
      simp [B]

private theorem memLp_etaEpsT4
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ))
      2 haarT4 := by
  obtain ⟨B, hB⟩ := ρ.exists_etaEpsT4_bound hε
  apply MemLp.of_bound
    (Complex.continuous_ofReal.measurable.comp
      (ρ.measurable_etaEpsT4 ε)).aestronglyMeasurable B
  exact Filter.Eventually.of_forall fun z => by
    change ‖(ρ.etaEpsT4 ε z : ℂ)‖ ≤ B
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ρ.etaEpsT4_nonneg ε z)]
    exact hB z

/-! ## Continuity of the Euclidean periodization -/

private def etaPeriodizationEuclidean
    (ε : ℝ) (x : R4) : ℝ :=
  ∑' k : Z4,
    ρ.etaRescaledR4 ε (x + covariancePeriodVector k)

private theorem norm_lt_two_radius_mul_of_etaRescaledR4_ne_zero
    {ε : ℝ} (hε : 0 < ε) {x : R4}
    (hx : ρ.etaRescaledR4 ε x ≠ 0) :
    ‖x‖ < 2 * ρ.radius * ε := by
  have heta : ρ.eta (ε⁻¹ • x) ≠ 0 :=
    (mul_ne_zero_iff.mp hx).2
  have hsupport := ρ.norm_lt_two_radius_of_eta_ne_zero heta
  have hscaled :
      ε⁻¹ * ‖x‖ < 2 * ρ.radius := by
    simpa [norm_smul, abs_of_pos hε, abs_inv] using hsupport
  calc
    ‖x‖ = ε * (ε⁻¹ * ‖x‖) := by
      field_simp
    _ < ε * (2 * ρ.radius) :=
      mul_lt_mul_of_pos_left hscaled hε
    _ = 2 * ρ.radius * ε := by ring

private def localPeriodRadius (ε : ℝ) (x₀ : R4) : ℤ :=
  ⌈(2 * ρ.radius * ε + ‖x₀‖ + 1) / (2 * Real.pi)⌉

private def localPeriodBox (ε : ℝ) (x₀ : R4) : Finset Z4 :=
  Fintype.piFinset fun _ : Fin dim =>
    Finset.Icc (-ρ.localPeriodRadius ε x₀)
      (ρ.localPeriodRadius ε x₀)

private theorem mem_localPeriodBox_of_ne_zero
    {ε : ℝ} (hε : 0 < ε) (x₀ x : R4)
    (hx : dist x x₀ < 1) {k : Z4}
    (hk :
      ρ.etaRescaledR4 ε
        (x + covariancePeriodVector k) ≠ 0) :
    k ∈ ρ.localPeriodBox ε x₀ := by
  have hterm :=
    ρ.norm_lt_two_radius_mul_of_etaRescaledR4_ne_zero hε hk
  have hxnorm : ‖x‖ < ‖x₀‖ + 1 := by
    calc
      ‖x‖ = ‖(x - x₀) + x₀‖ := by
        congr 1
        abel
      _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
      _ < 1 + ‖x₀‖ := by
        simpa [dist_eq_norm] using add_lt_add_right hx ‖x₀‖
      _ = ‖x₀‖ + 1 := by ring
  unfold localPeriodBox
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hcoord :
      |x i + 2 * Real.pi * (k i : ℝ)|
        < 2 * ρ.radius * ε := by
    calc
      |x i + 2 * Real.pi * (k i : ℝ)| =
          ‖(x + covariancePeriodVector k) i‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖x + covariancePeriodVector k‖ :=
        norm_le_pi_norm _ _
      _ < 2 * ρ.radius * ε := hterm
  have hxcoord : |x i| < ‖x₀‖ + 1 := by
    calc
      |x i| = ‖x i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖x‖ := norm_le_pi_norm _ _
      _ < ‖x₀‖ + 1 := hxnorm
  have hperiod :
      |2 * Real.pi * (k i : ℝ)|
        < 2 * ρ.radius * ε + ‖x₀‖ + 1 := by
    calc
      |2 * Real.pi * (k i : ℝ)| =
          |(x i + 2 * Real.pi * (k i : ℝ)) - x i| := by
        congr 1
        ring
      _ ≤ |x i + 2 * Real.pi * (k i : ℝ)| + |x i| :=
        abs_sub _ _
      _ < 2 * ρ.radius * ε + (‖x₀‖ + 1) :=
        add_lt_add hcoord hxcoord
      _ = 2 * ρ.radius * ε + ‖x₀‖ + 1 := by ring
  have hkabs :
      |(k i : ℝ)| <
        (2 * ρ.radius * ε + ‖x₀‖ + 1) /
          (2 * Real.pi) := by
    rw [abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hperiod
    exact (lt_div_iff₀
      (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      (by simpa [mul_comm] using hperiod)
  have hceil :
      (2 * ρ.radius * ε + ‖x₀‖ + 1) /
          (2 * Real.pi) ≤
        (ρ.localPeriodRadius ε x₀ : ℝ) :=
    Int.le_ceil _
  have hkupperReal :
      (k i : ℝ) ≤ (ρ.localPeriodRadius ε x₀ : ℝ) :=
    (le_abs_self _).trans (hkabs.le.trans hceil)
  have hklowerReal :
      (-(ρ.localPeriodRadius ε x₀ : ℤ) : ℝ) ≤
        (k i : ℝ) := by
    have hneg :
        -(ρ.localPeriodRadius ε x₀ : ℝ) ≤
          -|(k i : ℝ)| :=
      neg_le_neg (hkabs.le.trans hceil)
    exact hneg.trans (neg_abs_le _)
  constructor
  · exact_mod_cast hklowerReal
  · exact_mod_cast hkupperReal

private theorem etaPeriodizationEuclidean_eq_local_sum
    {ε : ℝ} (hε : 0 < ε) (x₀ x : R4)
    (hx : dist x x₀ < 1) :
    ρ.etaPeriodizationEuclidean ε x =
      ∑ k ∈ ρ.localPeriodBox ε x₀,
        ρ.etaRescaledR4 ε
          (x + covariancePeriodVector k) := by
  unfold etaPeriodizationEuclidean
  exact tsum_eq_sum fun k hk => by
    by_contra hne
    exact hk (ρ.mem_localPeriodBox_of_ne_zero hε x₀ x hx hne)

private theorem continuous_etaRescaledR4 (ε : ℝ) :
    Continuous (ρ.etaRescaledR4 ε) := by
  unfold etaRescaledR4
  have hs : Continuous (fun x : R4 => ε⁻¹ • x) :=
    continuous_const_smul ε⁻¹
  exact continuous_const.mul
    (ρ.continuous_eta.comp hs)

private theorem continuous_etaPeriodizationEuclidean
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (ρ.etaPeriodizationEuclidean ε) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let Q : R4 → ℝ :=
    fun x =>
      ∑ k ∈ ρ.localPeriodBox ε x₀,
        ρ.etaRescaledR4 ε
          (x + covariancePeriodVector k)
  have hQ : Continuous Q := by
    unfold Q
    apply continuous_finsetSum
    intro k hk
    exact (ρ.continuous_etaRescaledR4 ε).comp
      (continuous_id.add continuous_const)
  apply hQ.continuousAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
  exact ρ.etaPeriodizationEuclidean_eq_local_sum hε x₀ x hx

/-! ## Fourier uniqueness and pointwise upgrade -/

private theorem ae_complexFourierCovarianceT4_eq_etaEpsT4
    {ε : ℝ} (hε : 0 < ε) :
    ρ.complexFourierCovarianceT4 ε =ᵐ[haarT4]
      fun z : T4 => (ρ.etaEpsT4 ε z : ℂ) := by
  have hS :
      MemLp (ρ.complexFourierCovarianceT4 ε) 2 haarT4 :=
    (ρ.continuous_complexFourierCovarianceT4 hε).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hη := ρ.memLp_etaEpsT4 hε
  have hLp :
      hS.toLp (ρ.complexFourierCovarianceT4 ε) =
        hη.toLp (fun z : T4 => (ρ.etaEpsT4 ε z : ℂ)) := by
    apply torusFourierCoeff_l2_ext
    intro q
    rw [torusFourierCoeff_toLp, torusFourierCoeff_toLp,
      ρ.torusFourierCoeff_complexFourierCovarianceT4 hε q,
      ρ.torusFourierCoeff_etaEpsT4 hε q]
    rfl
  filter_upwards [hS.coeFn_toLp, hη.coeFn_toLp] with z hSz hηz
  rw [hLp] at hSz
  exact hSz.symm.trans hηz

private theorem etaEpsT4_poissonQuotient_eq_etaPeriodizationEuclidean
    {ε : ℝ} (x : R4) (hx : x ∈ poissonBox) :
    (ρ.etaEpsT4 ε (poissonQuotient x) : ℂ) =
      (ρ.etaPeriodizationEuclidean ε x : ℂ) := by
  rw [ρ.etaEpsT4_poissonQuotient x hx]
  unfold etaPeriodizationEuclidean
  push_cast
  rfl

private theorem covariancePeriodVector_add (k l : Z4) :
    covariancePeriodVector (k + l) =
      covariancePeriodVector k + covariancePeriodVector l := by
  funext i
  unfold covariancePeriodVector
  simp only [Pi.add_apply, Int.cast_add]
  ring

private theorem etaPeriodizationEuclidean_add_period
    (ε : ℝ) (x : R4) (n : Z4) :
    ρ.etaPeriodizationEuclidean ε
        (x + covariancePeriodVector n) =
      ρ.etaPeriodizationEuclidean ε x := by
  unfold etaPeriodizationEuclidean
  calc
    (∑' k : Z4,
        ρ.etaRescaledR4 ε
          ((x + covariancePeriodVector n) +
            covariancePeriodVector k)) =
        ∑' k : Z4,
          ρ.etaRescaledR4 ε
            (x + covariancePeriodVector (n + k)) := by
      apply tsum_congr
      intro k
      apply congrArg (ρ.etaRescaledR4 ε)
      rw [covariancePeriodVector_add]
      abel
    _ = ∑' k : Z4,
        ρ.etaRescaledR4 ε
          (x + covariancePeriodVector k) := by
      exact (Equiv.addLeft n).tsum_eq
        (fun k : Z4 =>
          ρ.etaRescaledR4 ε
            (x + covariancePeriodVector k))

/-- After pullback to `ℝ⁴`, Fourier uniqueness upgrades from almost
everywhere equality to pointwise equality because both sides are
continuous periodic functions. -/
private theorem complexFourierCovarianceT4_poissonQuotient
    {ε : ℝ} (hε : 0 < ε) :
    (fun x : R4 =>
      ρ.complexFourierCovarianceT4 ε (poissonQuotient x)) =
      fun x : R4 =>
        (ρ.etaPeriodizationEuclidean ε x : ℂ) := by
  let A : R4 → ℂ :=
    fun x =>
      ρ.complexFourierCovarianceT4 ε (poissonQuotient x)
  let B : R4 → ℂ :=
    fun x => (ρ.etaPeriodizationEuclidean ε x : ℂ)
  have haeHaar :=
    ρ.ae_complexFourierCovarianceT4_eq_etaEpsT4 hε
  have hpaperHaar : paperMeasure ≪ haarT4 := by
    unfold paperMeasure
    exact Measure.smul_absolutelyContinuous
  have haePaper :
      ρ.complexFourierCovarianceT4 ε =ᵐ[paperMeasure]
        fun z : T4 => (ρ.etaEpsT4 ε z : ℂ) :=
    hpaperHaar.ae_le haeHaar
  have hpull :=
    measurePreserving_poissonQuotient.quasiMeasurePreserving.ae_eq
      haePaper
  have hbase :
      A =ᵐ[volume.restrict poissonBox] B := by
    filter_upwards [hpull,
      ae_restrict_mem measurableSet_poissonBox] with x hx hmem
    exact hx.trans
      (ρ.etaEpsT4_poissonQuotient_eq_etaPeriodizationEuclidean
        x hmem)
  have hAperiod :
      ∀ x : R4, ∀ k : Z4,
        A (x + covariancePeriodVector k) = A x := by
    intro x k
    unfold A
    rw [poissonQuotient_add_covariancePeriodVector]
  have hBperiod :
      ∀ x : R4, ∀ k : Z4,
        B (x + covariancePeriodVector k) = B x := by
    intro x k
    unfold B
    rw [ρ.etaPeriodizationEuclidean_add_period]
  have hall :
      ∀ k : Z4,
        A =ᵐ[volume.restrict (poissonBoxAt k)] B := by
    intro k
    let e : R4 ≃ᵐ R4 :=
      MeasurableEquiv.addRight (covariancePeriodVector k)
    have hforward :
        MeasurePreserving e
          (volume.restrict poissonBox)
          (volume.restrict (poissonBoxAt k)) := by
      have h :=
        (measurePreserving_add_right (volume : Measure R4)
          (covariancePeriodVector k)).restrict_image_emb
          e.measurableEmbedding poissonBox
      rw [image_add_covariancePeriodVector_poissonBox] at h
      exact h
    have hback :
        MeasurePreserving e.symm
          (volume.restrict (poissonBoxAt k))
          (volume.restrict poissonBox) :=
      MeasurePreserving.symm e hforward
    have hk :=
      hback.quasiMeasurePreserving.ae_eq hbase
    filter_upwards [hk] with x hx
    have he :
        e.symm x + covariancePeriodVector k = x := by
      simp [e]
    calc
      A x = A (e.symm x) := by
        exact (congrArg A he).symm.trans
          (hAperiod (e.symm x) k)
      _ = B (e.symm x) := hx
      _ = B x := by
        exact (hBperiod (e.symm x) k).symm.trans
          (congrArg B he)
  have hglobal : A =ᵐ[volume] B := by
    have hu :
        A =ᵐ[volume.restrict
          (⋃ k : Z4, poissonBoxAt k)] B := by
      rw [ae_restrict_iUnion_eq]
      exact Filter.eventually_iSup.mpr hall
    rw [iUnion_poissonBoxAt, Measure.restrict_univ] at hu
    exact hu
  have hquot : Continuous poissonQuotient := by
    unfold poissonQuotient
    fun_prop
  have hA : Continuous A := by
    exact
      (ρ.continuous_complexFourierCovarianceT4 hε).comp hquot
  have hB : Continuous B := by
    exact Complex.continuous_ofReal.comp
      (ρ.continuous_etaPeriodizationEuclidean hε)
  exact (hA.ae_eq_iff_eq volume hB).mp hglobal

private theorem poissonQuotient_torusLift (z : T4) :
    poissonQuotient (torusLift z) = z := by
  funext i
  unfold poissonQuotient torusLift
  exact AddCircle.coe_equivIco

private theorem torusLift_mem_poissonBox (z : T4) :
    torusLift z ∈ poissonBox := by
  intro i hi
  exact torusLift_mem_Ico z i

theorem complexFourierCovarianceT4_eq_etaEpsT4
    {ε : ℝ} (hε : 0 < ε) (z : T4) :
    ρ.complexFourierCovarianceT4 ε z =
      (ρ.etaEpsT4 ε z : ℂ) := by
  let x : R4 := torusLift z
  have hglobal :=
    congrFun (ρ.complexFourierCovarianceT4_poissonQuotient hε) x
  have hquot : poissonQuotient x = z := by
    exact poissonQuotient_torusLift z
  have hx : x ∈ poissonBox :=
    torusLift_mem_poissonBox z
  have heta :=
    ρ.etaEpsT4_poissonQuotient_eq_etaPeriodizationEuclidean
      (ε := ε) x hx
  rw [hquot] at hglobal heta
  exact hglobal.trans heta.symm

end SmoothCutoff

namespace NoiseModel

/-- Multidimensional Poisson summation for the mollified covariance,
with the exact Lebesgue/probability-Haar normalization
`whiteNoiseFourierScale² = (2π)⁻⁴`. -/
theorem fourierCovarianceT4_eq_etaEpsT4
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (z : T4) :
    fourierCovarianceT4 ρ ε z = ρ.etaEpsT4 ε z := by
  have hcomplex :=
    ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε z
  have hre := congrArg Complex.re hcomplex
  simpa only [fourierCovarianceT4,
    SmoothCutoff.complexFourierCovarianceT4,
    SmoothCutoff.covarianceModeCoeff,
    Complex.ofReal_re] using hre

end NoiseModel

end

end Anderson4D
