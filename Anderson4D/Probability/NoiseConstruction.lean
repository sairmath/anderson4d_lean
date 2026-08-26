import Anderson4D.Probability.Noise
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration

/-!
# Construction of the Fourier white-noise model

This module realizes the interface in `Probability.Noise` on a genuine
probability space.  The underlying coordinates are an independent family
of standard real Gaussian random variables.  An encoding-dependent
fundamental domain for `k ↦ -k` is used only to choose which member of each
two-point orbit receives the positive imaginary coordinate.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory ComplexConjugate
open scoped BigOperators NNReal

/-- Two real Gaussian generators are reserved for every nonzero
`{k,-k}` orbit.  The unused duplicate coordinates make the ambient product
space especially simple; coefficients only read the canonical orbit
representative. -/
abbrev NoiseGenerator := Z4 × Bool

/-- An encoding-dependent representative of the orbit `{k,-k}`. -/
def noiseOrbitRep (k : Z4) : Z4 :=
  if Encodable.encode k ≤ Encodable.encode (-k) then k else -k

/-- The sign of the imaginary coordinate.  It is zero at the zero mode and
changes sign under `k ↦ -k` away from zero. -/
def noiseOrbitSign (k : Z4) : ℝ :=
  if k = 0 then 0
  else if Encodable.encode k ≤ Encodable.encode (-k) then 1 else -1

private theorem encode_ne_encode_neg {k : Z4} (hk : k ≠ 0) :
    Encodable.encode k ≠ Encodable.encode (-k) := by
  intro h
  have hself : k = -k := Encodable.encode_injective h
  exact hk (self_eq_neg.mp hself)

@[simp]
theorem noiseOrbitRep_neg (k : Z4) :
    noiseOrbitRep (-k) = noiseOrbitRep k := by
  by_cases hk : k = 0
  · simp [hk, noiseOrbitRep]
  · have hne := encode_ne_encode_neg hk
    unfold noiseOrbitRep
    simp only [neg_neg]
    by_cases hle : Encodable.encode k ≤ Encodable.encode (-k)
    · have hlt : Encodable.encode k < Encodable.encode (-k) :=
        lt_of_le_of_ne hle hne
      simp [hle, Nat.not_le.mpr hlt]
    · have hrev : Encodable.encode (-k) ≤ Encodable.encode k :=
        Nat.le_of_lt (Nat.lt_of_not_ge hle)
      simp [hle, hrev]

@[simp]
theorem noiseOrbitSign_zero : noiseOrbitSign (0 : Z4) = 0 := by
  simp [noiseOrbitSign]

@[simp]
theorem noiseOrbitSign_neg (k : Z4) :
    noiseOrbitSign (-k) = -noiseOrbitSign k := by
  by_cases hk : k = 0
  · simp [hk]
  · have hneg : -k ≠ 0 := neg_ne_zero.mpr hk
    have hne := encode_ne_encode_neg hk
    unfold noiseOrbitSign
    simp only [hneg, hk, if_false, neg_neg]
    by_cases hle : Encodable.encode k ≤ Encodable.encode (-k)
    · have hlt : Encodable.encode k < Encodable.encode (-k) :=
        lt_of_le_of_ne hle hne
      simp [hle, Nat.not_le.mpr hlt]
    · have hrev : Encodable.encode (-k) ≤ Encodable.encode k :=
        Nat.le_of_lt (Nat.lt_of_not_ge hle)
      simp [hle, hrev]

theorem noiseOrbitRep_eq_self_or_neg (k : Z4) :
    noiseOrbitRep k = k ∨ noiseOrbitRep k = -k := by
  unfold noiseOrbitRep
  split_ifs <;> simp

theorem noiseOrbitRep_eq_iff (k l : Z4) :
    noiseOrbitRep k = noiseOrbitRep l ↔ l = k ∨ l = -k := by
  constructor
  · intro h
    rcases noiseOrbitRep_eq_self_or_neg k with hk | hk <;>
      rcases noiseOrbitRep_eq_self_or_neg l with hl | hl
    · left
      rw [hk, hl] at h
      exact h.symm
    · right
      rw [hk, hl] at h
      have hneg := congrArg Neg.neg h
      simpa using hneg.symm
    · right
      rw [hk, hl] at h
      exact h.symm
    · left
      rw [hk, hl] at h
      exact (neg_inj.mp h).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (noiseOrbitRep_neg k).symm

/-- A genuine probability space carrying mutually independent standard
real Gaussian coordinates. -/
structure StandardGaussianFamily where
  /-- Sample space. -/
  Ω : Type
  /-- Probability measure, exposed as `volume`. -/
  [measureSpace : MeasureSpace Ω]
  /-- The coordinate product measure is a probability measure. -/
  [isProbabilityMeasure : IsProbabilityMeasure (volume : Measure Ω)]
  /-- Independent standard Gaussian coordinates. -/
  X : NoiseGenerator → Ω → ℝ
  measurable_X : ∀ i, Measurable (X i)
  hasLaw_X : ∀ i, HasLaw (X i) (gaussianReal 0 1) volume
  indep_X : iIndepFun X volume

attribute [instance] StandardGaussianFamily.measureSpace
  StandardGaussianFamily.isProbabilityMeasure

/-- The countable product theorem constructs the required real Gaussian
family without any extra postulate. -/
theorem nonempty_standardGaussianFamily :
    Nonempty StandardGaussianFamily := by
  obtain ⟨Ω, mΩ, P, X, hmeas, hlaw, hindep, hprob⟩ :=
    exists_iid NoiseGenerator (gaussianReal 0 1)
  letI : MeasurableSpace Ω := mΩ
  letI : MeasureSpace Ω := ⟨P⟩
  letI : IsProbabilityMeasure (volume : Measure Ω) := by
    change IsProbabilityMeasure P
    exact hprob
  exact ⟨{
    Ω := Ω
    X := X
    measurable_X := hmeas
    hasLaw_X := hlaw
    indep_X := hindep
  }⟩

/-- A fixed countable product of standard real Gaussian laws. -/
def canonicalStandardGaussianFamily : StandardGaussianFamily :=
  Classical.choice nonempty_standardGaussianFamily

namespace StandardGaussianFamily

variable (F : StandardGaussianFamily)

/-- Every finite subfamily of the product coordinates is jointly
Gaussian. -/
theorem isGaussianProcess_X :
    IsGaussianProcess F.X (volume : Measure F.Ω) := by
  constructor
  intro I
  have hindep :
      iIndepFun (fun i : I => F.X i) (volume : Measure F.Ω) :=
    F.indep_X.precomp Subtype.val_injective
  exact hindep.hasGaussianLaw
    (fun i => (F.hasLaw_X i).hasGaussianLaw)

/-- Every generator is centered. -/
@[simp]
theorem integral_X (i : NoiseGenerator) :
    ∫ ω, F.X i ω = 0 := by
  rw [(F.hasLaw_X i).integral_eq, integral_id_gaussianReal]

/-- Every generator has variance and second moment one. -/
@[simp]
theorem integral_X_sq (i : NoiseGenerator) :
    ∫ ω, F.X i ω ^ 2 = 1 := by
  rw [← variance_of_integral_eq_zero
    (F.measurable_X i).aemeasurable (F.integral_X i)]
  rw [(F.hasLaw_X i).variance_eq, variance_id_gaussianReal]
  norm_num

/-- Distinct product coordinates are orthogonal in `L²`; equal coordinates
have second moment one. -/
theorem integral_X_mul_X (i j : NoiseGenerator) :
    ∫ ω, F.X i ω * F.X j ω = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [if_pos]
    simpa only [pow_two] using F.integral_X_sq i
  · have hindep : IndepFun (F.X i) (F.X j)
        (volume : Measure F.Ω) :=
      F.indep_X.indepFun hij
    change ∫ ω, (F.X i * F.X j) ω = if i = j then 1 else 0
    rw [hindep.integral_mul_eq_mul_integral
      (F.measurable_X i).aestronglyMeasurable
      (F.measurable_X j).aestronglyMeasurable]
    simp [hij]

end StandardGaussianFamily

/-- Real-coordinate normalization: one at the real zero mode and
`1 / √2` on nonzero orbit pairs. -/
def noiseRealScale (k : Z4) : ℝ :=
  if k = 0 then 1 else 1 / Real.sqrt 2

/-- Imaginary-coordinate normalization and orientation. -/
def noiseImagScale (k : Z4) : ℝ :=
  if k = 0 then 0 else noiseOrbitSign k / Real.sqrt 2

@[simp]
theorem noiseRealScale_neg (k : Z4) :
    noiseRealScale (-k) = noiseRealScale k := by
  simp only [noiseRealScale, neg_eq_zero]

@[simp]
theorem noiseImagScale_neg (k : Z4) :
    noiseImagScale (-k) = -noiseImagScale k := by
  by_cases hk : k = 0
  · simp [hk, noiseImagScale]
  · simp [noiseImagScale, hk, noiseOrbitSign_neg]
    ring

theorem noiseScale_sq_add (k : Z4) :
    noiseRealScale k ^ 2 + noiseImagScale k ^ 2 = 1 := by
  by_cases hk : k = 0
  · subst k
    simp [noiseRealScale, noiseImagScale]
  · have hsqrt :
      (1 / Real.sqrt 2) ^ 2 + (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) := by
      rw [div_pow, one_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    by_cases henc : Encodable.encode k ≤ Encodable.encode (-k)
    · unfold noiseRealScale noiseImagScale noiseOrbitSign
      simp only [hk, if_false, henc, if_true]
      exact hsqrt
    · unfold noiseRealScale noiseImagScale noiseOrbitSign
      simp only [hk, if_false, henc]
      calc
        (1 / Real.sqrt 2) ^ 2 + (-1 / Real.sqrt 2) ^ 2 =
            (1 / Real.sqrt 2) ^ 2 + (1 / Real.sqrt 2) ^ 2 := by ring
        _ = 1 := hsqrt

theorem noiseScale_sq_sub_of_ne {k : Z4} (hk : k ≠ 0) :
    noiseRealScale k ^ 2 - noiseImagScale k ^ 2 = 0 := by
  by_cases henc : Encodable.encode k ≤ Encodable.encode (-k)
  · unfold noiseRealScale noiseImagScale noiseOrbitSign
    simp only [hk, if_false, henc, if_true]
    ring
  · unfold noiseRealScale noiseImagScale noiseOrbitSign
    simp only [hk, if_false, henc]
    ring

/-- Fourier coefficient assembled from the two real Gaussian generators of
the canonical `±k` orbit. -/
def StandardGaussianFamily.fourierCoeff
    (F : StandardGaussianFamily) (k : Z4) (ω : F.Ω) : ℂ :=
  ⟨noiseRealScale k * F.X (noiseOrbitRep k, false) ω,
    noiseImagScale k * F.X (noiseOrbitRep k, true) ω⟩

namespace StandardGaussianFamily

variable (F : StandardGaussianFamily)

theorem measurable_fourierCoeff (k : Z4) :
    Measurable (F.fourierCoeff k) := by
  change Measurable (fun ω =>
    Complex.measurableEquivRealProd.symm
      (noiseRealScale k * F.X (noiseOrbitRep k, false) ω,
        noiseImagScale k * F.X (noiseOrbitRep k, true) ω))
  exact Complex.measurableEquivRealProd.symm.measurable.comp
    ((measurable_const.mul (F.measurable_X _)).prodMk
      (measurable_const.mul (F.measurable_X _)))

/-- The orbit orientation gives the Fourier reality constraint
pointwise, not merely almost surely. -/
theorem fourierCoeff_neg (k : Z4) (ω : F.Ω) :
    F.fourierCoeff (-k) ω = conj (F.fourierCoeff k ω) := by
  apply Complex.ext
  · simp [fourierCoeff]
  · simp [fourierCoeff]

/-- Products of any two real product coordinates are integrable. -/
theorem integrable_X_mul_X (i j : NoiseGenerator) :
    Integrable (fun ω => F.X i ω * F.X j ω) := by
  have hi := ((F.hasLaw_X i).hasGaussianLaw).memLp_two
  have hj := ((F.hasLaw_X j).hasGaussianLaw).memLp_two
  change Integrable (F.X i * F.X j)
  exact hi.integrable_mul hj

/-- A scalar multiple of a coordinate product is integrable. -/
theorem integrable_const_mul_X_mul_X
    (c : ℝ) (i j : NoiseGenerator) :
    Integrable (fun ω => c * (F.X i ω * F.X j ω)) :=
  (F.integrable_X_mul_X i j).const_mul c

/-- A scalar multiple of a coordinate product integrates according to the
Kronecker covariance of the product family. -/
theorem integral_const_mul_X_mul_X
    (c : ℝ) (i j : NoiseGenerator) :
    ∫ ω, c * (F.X i ω * F.X j ω) =
      c * (if i = j then 1 else 0) := by
  rw [integral_const_mul, F.integral_X_mul_X]

/-- The product of any two Fourier coefficients is integrable. -/
theorem integrable_fourierCoeff_mul (k l : Z4) :
    Integrable (fun ω => F.fourierCoeff k ω * F.fourierCoeff l ω) := by
  rw [← Integrable.re_im_iff]
  constructor
  · change Integrable (fun ω =>
      (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
          (noiseRealScale l * F.X (noiseOrbitRep l, false) ω) -
        (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
          (noiseImagScale l * F.X (noiseOrbitRep l, true) ω))
    have hre : Integrable (fun ω =>
        (noiseRealScale k * noiseRealScale l) *
          (F.X (noiseOrbitRep k, false) ω *
            F.X (noiseOrbitRep l, false) ω)) :=
      F.integrable_const_mul_X_mul_X _ _ _
    have him : Integrable (fun ω =>
        (noiseImagScale k * noiseImagScale l) *
          (F.X (noiseOrbitRep k, true) ω *
            F.X (noiseOrbitRep l, true) ω)) :=
      F.integrable_const_mul_X_mul_X _ _ _
    exact (hre.sub him).congr (ae_of_all _ fun ω => by
      simp only [Pi.sub_apply]
      ring)
  · change Integrable (fun ω =>
      (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
          (noiseImagScale l * F.X (noiseOrbitRep l, true) ω) +
        (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
          (noiseRealScale l * F.X (noiseOrbitRep l, false) ω))
    have hri : Integrable (fun ω =>
        (noiseRealScale k * noiseImagScale l) *
          (F.X (noiseOrbitRep k, false) ω *
            F.X (noiseOrbitRep l, true) ω)) :=
      F.integrable_const_mul_X_mul_X _ _ _
    have hir : Integrable (fun ω =>
        (noiseImagScale k * noiseRealScale l) *
          (F.X (noiseOrbitRep k, true) ω *
            F.X (noiseOrbitRep l, false) ω)) :=
      F.integrable_const_mul_X_mul_X _ _ _
    exact (hri.add hir).congr (ae_of_all _ fun ω => by
      simp only [Pi.add_apply]
      ring)

/-- Before the final orbit arithmetic, the covariance of two Fourier
coefficients is the scalar covariance of their common orbit. -/
theorem integral_fourierCoeff_mul (k l : Z4) :
    ∫ ω, F.fourierCoeff k ω * F.fourierCoeff l ω =
      (((noiseRealScale k * noiseRealScale l -
        noiseImagScale k * noiseImagScale l) *
        (if noiseOrbitRep k = noiseOrbitRep l then 1 else 0) : ℝ) : ℂ) := by
  let δ : ℝ := if noiseOrbitRep k = noiseOrbitRep l then 1 else 0
  have hrr :
      ∫ ω,
          (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
            (noiseRealScale l * F.X (noiseOrbitRep l, false) ω) =
        noiseRealScale k * noiseRealScale l * δ := by
    rw [show (fun ω =>
        (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
          (noiseRealScale l * F.X (noiseOrbitRep l, false) ω)) =
        (fun ω => (noiseRealScale k * noiseRealScale l) *
          (F.X (noiseOrbitRep k, false) ω *
            F.X (noiseOrbitRep l, false) ω)) by
          funext ω
          ring]
    rw [F.integral_const_mul_X_mul_X]
    simp [δ]
  have hii :
      ∫ ω,
          (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
            (noiseImagScale l * F.X (noiseOrbitRep l, true) ω) =
        noiseImagScale k * noiseImagScale l * δ := by
    rw [show (fun ω =>
        (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
          (noiseImagScale l * F.X (noiseOrbitRep l, true) ω)) =
        (fun ω => (noiseImagScale k * noiseImagScale l) *
          (F.X (noiseOrbitRep k, true) ω *
            F.X (noiseOrbitRep l, true) ω)) by
          funext ω
          ring]
    rw [F.integral_const_mul_X_mul_X]
    simp [δ]
  have hri :
      ∫ ω,
          (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
            (noiseImagScale l * F.X (noiseOrbitRep l, true) ω) = 0 := by
    rw [show (fun ω =>
        (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
          (noiseImagScale l * F.X (noiseOrbitRep l, true) ω)) =
        (fun ω => (noiseRealScale k * noiseImagScale l) *
          (F.X (noiseOrbitRep k, false) ω *
            F.X (noiseOrbitRep l, true) ω)) by
          funext ω
          ring]
    rw [F.integral_const_mul_X_mul_X]
    simp
  have hir :
      ∫ ω,
          (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
            (noiseRealScale l * F.X (noiseOrbitRep l, false) ω) = 0 := by
    rw [show (fun ω =>
        (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
          (noiseRealScale l * F.X (noiseOrbitRep l, false) ω)) =
        (fun ω => (noiseImagScale k * noiseRealScale l) *
          (F.X (noiseOrbitRep k, true) ω *
            F.X (noiseOrbitRep l, false) ω)) by
          funext ω
          ring]
    rw [F.integral_const_mul_X_mul_X]
    simp
  have hprod := F.integrable_fourierCoeff_mul k l
  apply Complex.ext
  · calc
      (∫ ω, F.fourierCoeff k ω * F.fourierCoeff l ω).re =
          ∫ ω, (F.fourierCoeff k ω * F.fourierCoeff l ω).re :=
        (integral_re hprod).symm
      _ = _ := by
        change
          (∫ ω,
            (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
                (noiseRealScale l * F.X (noiseOrbitRep l, false) ω) -
              (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
                (noiseImagScale l * F.X (noiseOrbitRep l, true) ω)) =
            _
        rw [integral_sub]
        · rw [hrr, hii]
          simp only [Complex.ofReal_re]
          dsimp [δ]
          ring
        · exact (F.integrable_const_mul_X_mul_X
            (noiseRealScale k * noiseRealScale l)
            (noiseOrbitRep k, false) (noiseOrbitRep l, false)).congr
            (ae_of_all _ fun ω => by ring)
        · exact (F.integrable_const_mul_X_mul_X
            (noiseImagScale k * noiseImagScale l)
            (noiseOrbitRep k, true) (noiseOrbitRep l, true)).congr
            (ae_of_all _ fun ω => by ring)
  · calc
      (∫ ω, F.fourierCoeff k ω * F.fourierCoeff l ω).im =
          ∫ ω, (F.fourierCoeff k ω * F.fourierCoeff l ω).im :=
        (integral_im hprod).symm
      _ = _ := by
        change
          (∫ ω,
            (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) *
                (noiseImagScale l * F.X (noiseOrbitRep l, true) ω) +
              (noiseImagScale k * F.X (noiseOrbitRep k, true) ω) *
                (noiseRealScale l * F.X (noiseOrbitRep l, false) ω)) =
            _
        rw [integral_add]
        · rw [hri, hir]
          simp
        · exact (F.integrable_const_mul_X_mul_X
            (noiseRealScale k * noiseImagScale l)
            (noiseOrbitRep k, false) (noiseOrbitRep l, true)).congr
            (ae_of_all _ fun ω => by ring)
        · exact (F.integrable_const_mul_X_mul_X
            (noiseImagScale k * noiseRealScale l)
            (noiseOrbitRep k, true) (noiseOrbitRep l, false)).congr
            (ae_of_all _ fun ω => by ring)

/-- The orbit normalization is exactly the Fourier white-noise
Kronecker covariance. -/
theorem fourierCovarianceScalar (k l : Z4) :
    (noiseRealScale k * noiseRealScale l -
        noiseImagScale k * noiseImagScale l) *
        (if noiseOrbitRep k = noiseOrbitRep l then 1 else 0) =
      if k = -l then 1 else 0 := by
  by_cases hrep : noiseOrbitRep k = noiseOrbitRep l
  · rcases (noiseOrbitRep_eq_iff k l).mp hrep with hl | hl
    · subst l
      by_cases hk : k = 0
      · subst k
        simp [noiseRealScale, noiseImagScale]
      · have hself : k ≠ -k := by
          intro h
          exact hk (self_eq_neg.mp h)
        simp only [if_pos, hself, if_false, mul_one]
        calc
          noiseRealScale k * noiseRealScale k -
              noiseImagScale k * noiseImagScale k =
              noiseRealScale k ^ 2 - noiseImagScale k ^ 2 := by ring
          _ = 0 := noiseScale_sq_sub_of_ne hk
    · subst l
      simp only [noiseOrbitRep_neg, if_pos, neg_neg]
      rw [noiseRealScale_neg, noiseImagScale_neg]
      simp only [mul_one]
      calc
        noiseRealScale k * noiseRealScale k -
            noiseImagScale k * -noiseImagScale k =
            noiseRealScale k ^ 2 + noiseImagScale k ^ 2 := by ring
        _ = 1 := noiseScale_sq_add k
  · have hpair : k ≠ -l := by
      intro h
      apply hrep
      have hl : l = -k := by
        rw [h]
        simp
      rw [hl, noiseOrbitRep_neg]
    simp [hrep, hpair]

/-- Exact covariance `E[gₖ gₗ] = 1_{k=-l}`. -/
theorem fourierCoeff_cov_pair (k l : Z4) :
    ∫ ω, F.fourierCoeff k ω * F.fourierCoeff l ω =
      if k = -l then 1 else 0 := by
  rw [F.integral_fourierCoeff_mul, fourierCovarianceScalar]
  split_ifs <;> norm_num

/-- Exact conjugated covariance, obtained from the pointwise reality
constraint and the preceding pair covariance. -/
theorem fourierCoeff_cov_conj (k l : Z4) :
    ∫ ω, F.fourierCoeff k ω * conj (F.fourierCoeff l ω) =
      if k = l then 1 else 0 := by
  have hfun :
      (fun ω => F.fourierCoeff k ω * conj (F.fourierCoeff l ω)) =
        (fun ω => F.fourierCoeff k ω * F.fourierCoeff (-l) ω) := by
    funext ω
    rw [F.fourierCoeff_neg]
  rw [hfun, F.fourierCoeff_cov_pair]
  simp

/-- The finite set of independent real coordinates read by a finite set of
Fourier modes. -/
def noiseGeneratorSet (s : Finset Z4) : Finset NoiseGenerator :=
  (s.image fun k => (noiseOrbitRep k, false)) ∪
    (s.image fun k => (noiseOrbitRep k, true))

private theorem realGenerator_mem_noiseGeneratorSet
    (s : Finset Z4) {k : Z4} (hk : k ∈ s) :
    (noiseOrbitRep k, false) ∈ noiseGeneratorSet s := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

private theorem imagGenerator_mem_noiseGeneratorSet
    (s : Finset Z4) {k : Z4} (hk : k ∈ s) :
    (noiseOrbitRep k, true) ∈ noiseGeneratorSet s := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨k, hk, rfl⟩

/-- The continuous linear functional on the finite coordinate vector that
realizes a prescribed Fourier-coordinate combination. -/
def noiseFiniteCombinationCLM
    (s : Finset Z4) (a b : Z4 → ℝ) :
    (noiseGeneratorSet s → ℝ) →L[ℝ] ℝ where
  toFun x :=
    ∑ k : s,
      (a k * noiseRealScale k *
          x ⟨(noiseOrbitRep k, false),
            realGenerator_mem_noiseGeneratorSet s k.property⟩ +
        b k * noiseImagScale k *
          x ⟨(noiseOrbitRep k, true),
            imagGenerator_mem_noiseGeneratorSet s k.property⟩)
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The exact real combination appearing in the `NoiseModel` interface. -/
def fourierLinearCombination
    (F : StandardGaussianFamily) (s : Finset Z4)
    (a b : Z4 → ℝ) (ω : F.Ω) : ℝ :=
  ∑ k ∈ s,
    (a k * (F.fourierCoeff k ω).re +
      b k * (F.fourierCoeff k ω).im)

theorem integrable_fourierCoeff_re (k : Z4) :
    Integrable (fun ω => (F.fourierCoeff k ω).re) := by
  change Integrable (fun ω =>
    noiseRealScale k * F.X (noiseOrbitRep k, false) ω)
  exact (((F.hasLaw_X (noiseOrbitRep k, false)).hasGaussianLaw).integrable).const_mul _

theorem integrable_fourierCoeff_im (k : Z4) :
    Integrable (fun ω => (F.fourierCoeff k ω).im) := by
  change Integrable (fun ω =>
    noiseImagScale k * F.X (noiseOrbitRep k, true) ω)
  exact (((F.hasLaw_X (noiseOrbitRep k, true)).hasGaussianLaw).integrable).const_mul _

@[simp]
theorem integral_fourierCoeff_re (k : Z4) :
    ∫ ω, (F.fourierCoeff k ω).re = 0 := by
  change ∫ ω, noiseRealScale k * F.X (noiseOrbitRep k, false) ω = 0
  rw [integral_const_mul, F.integral_X]
  ring

@[simp]
theorem integral_fourierCoeff_im (k : Z4) :
    ∫ ω, (F.fourierCoeff k ω).im = 0 := by
  change ∫ ω, noiseImagScale k * F.X (noiseOrbitRep k, true) ω = 0
  rw [integral_const_mul, F.integral_X]
  ring

/-- Every finite real Fourier-coordinate combination is integrable. -/
theorem integrable_fourierLinearCombination
    (s : Finset Z4) (a b : Z4 → ℝ) :
    Integrable (F.fourierLinearCombination s a b) := by
  unfold fourierLinearCombination
  apply integrable_finsetSum
  intro k hk
  exact ((F.integrable_fourierCoeff_re k).const_mul (a k)).add
    ((F.integrable_fourierCoeff_im k).const_mul (b k))

/-- Every finite real Fourier-coordinate combination is centered. -/
@[simp]
theorem integral_fourierLinearCombination
    (s : Finset Z4) (a b : Z4 → ℝ) :
    ∫ ω, F.fourierLinearCombination s a b ω = 0 := by
  unfold fourierLinearCombination
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro k hk
    rw [integral_add]
    · rw [integral_const_mul, integral_const_mul,
        F.integral_fourierCoeff_re, F.integral_fourierCoeff_im]
      ring
    · exact (F.integrable_fourierCoeff_re k).const_mul _
    · exact (F.integrable_fourierCoeff_im k).const_mul _
  · intro k hk
    exact ((F.integrable_fourierCoeff_re k).const_mul (a k)).add
      ((F.integrable_fourierCoeff_im k).const_mul (b k))

/-- The finite combination is a Gaussian random variable because it is a
linear image of a finite subvector of the independent Gaussian product. -/
theorem hasGaussianLaw_fourierLinearCombination
    (s : Finset Z4) (a b : Z4 → ℝ) :
    HasGaussianLaw (F.fourierLinearCombination s a b)
      (volume : Measure F.Ω) := by
  have hbase :=
    (F.isGaussianProcess_X.hasGaussianLaw (noiseGeneratorSet s)).map
      (noiseFiniteCombinationCLM s a b)
  have hfun :
      F.fourierLinearCombination s a b =
        (noiseFiniteCombinationCLM s a b) ∘
          (fun ω => (noiseGeneratorSet s).restrict (F.X · ω)) := by
    funext ω
    unfold fourierLinearCombination noiseFiniteCombinationCLM fourierCoeff
    simp only [Function.comp_apply, Finset.restrict_def]
    rw [← Finset.sum_attach]
    change
      (∑ k : s,
        (a k * (noiseRealScale k * F.X (noiseOrbitRep k, false) ω) +
          b k * (noiseImagScale k * F.X (noiseOrbitRep k, true) ω))) =
        ∑ k : s,
          (a k * noiseRealScale k * F.X (noiseOrbitRep k, false) ω +
            b k * noiseImagScale k * F.X (noiseOrbitRep k, true) ω)
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfun]
  exact hbase

/-- Exact centered Gaussian pushforward law, in the shape required by
`NoiseModel.gaussian_lincomb`. -/
theorem exists_map_fourierLinearCombination_eq_gaussianReal
    (s : Finset Z4) (a b : Z4 → ℝ) :
    ∃ v : NNReal,
      Measure.map (F.fourierLinearCombination s a b)
          (volume : Measure F.Ω) =
        gaussianReal 0 v := by
  let v : NNReal :=
    (variance (F.fourierLinearCombination s a b)
      (volume : Measure F.Ω)).toNNReal
  refine ⟨v, ?_⟩
  have hmap :=
    (F.hasGaussianLaw_fourierLinearCombination s a b).map_eq_gaussianReal
  rw [F.integral_fourierLinearCombination s a b] at hmap
  exact hmap

end StandardGaussianFamily

/-- The canonical countable product construction realizes the complete
`NoiseModel` interface. -/
def canonicalNoiseModel : NoiseModel :=
  let F := canonicalStandardGaussianFamily
  {
    Ω := F.Ω
    g := F.fourierCoeff
    measurable_g := F.measurable_fourierCoeff
    reality := F.fourierCoeff_neg
    cov_pair := F.fourierCoeff_cov_pair
    cov_conj := F.fourierCoeff_cov_conj
    gaussian_lincomb := by
      intro s a b
      change ∃ v : NNReal,
        Measure.map (F.fourierLinearCombination s a b)
            (volume : Measure F.Ω) =
          gaussianReal 0 v
      exact F.exists_map_fourierLinearCombination_eq_gaussianReal s a b
  }

/-- In particular, the `NoiseModel` interface is inhabited without adding
a postulate or treating its specification as a certificate. -/
theorem nonempty_noiseModel : Nonempty NoiseModel :=
  ⟨canonicalNoiseModel⟩

end

end Anderson4D
