import Anderson4D.Probability.NoiseRegularity
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Smooth sample paths of the mollified noise

The torus is represented in the project as a product of quotient
groups, for which mathlib does not currently expose a smooth-manifold
structure.  We therefore use the standard equivalent definition:
a torus function is smooth when its periodic pullback to `ℝ⁴` is
smooth.  This file proves that property almost surely for every fixed
positive mollification scale.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory ComplexConjugate
open scoped BigOperators

/-- The quotient map from the universal cover `ℝ⁴` to the torus. -/
def torusQuotient (x : R4) : T4 :=
  fun i => (x i : AddCircle (2 * Real.pi))

/-- The real phase `k · x`, as a continuous linear functional. -/
def frequencyPhase (k : Z4) : R4 →L[ℝ] ℝ :=
  ∑ i : Fin dim, (k i : ℝ) • ContinuousLinearMap.proj i

@[simp]
theorem frequencyPhase_apply (k : Z4) (x : R4) :
    frequencyPhase k x = ∑ i, (k i : ℝ) * x i := by
  simp [frequencyPhase]

/-- The one-dimensional unit-modulus plane wave. -/
def realPlaneWave (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ))

theorem contDiff_realPlaneWave (n : ℕ∞) :
    ContDiff ℝ n realPlaneWave := by
  unfold realPlaneWave
  exact
    (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.of_le le_top)).cexp

theorem iteratedDeriv_realPlaneWave (n : ℕ) :
    iteratedDeriv n realPlaneWave =
      fun t => Complex.I ^ n * realPlaneWave t := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have h :
          HasDerivAt realPlaneWave
            (Complex.I * realPlaneWave t) t := by
        unfold realPlaneWave
        have hinner :
            HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ))
              Complex.I t := by
          simpa using Complex.ofRealCLM.hasDerivAt.const_mul Complex.I
        simpa [mul_comm] using hinner.cexp
      rw [h.const_mul (Complex.I ^ n) |>.deriv]
      ring

theorem norm_iteratedFDeriv_realPlaneWave (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n realPlaneWave t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    congrFun (iteratedDeriv_realPlaneWave n) t]
  simp [realPlaneWave, Complex.norm_exp]

/-- A Fourier character pulled back to the universal cover. -/
def liftedChar (k : Z4) : R4 → ℂ :=
  realPlaneWave ∘ frequencyPhase k

theorem contDiff_liftedChar (k : Z4) (n : ℕ∞) :
    ContDiff ℝ n (liftedChar k) := by
  change ContDiff ℝ n (realPlaneWave ∘ frequencyPhase k)
  exact (contDiff_realPlaneWave n).comp_continuousLinearMap

/-- Pulling a project character back along the quotient map gives the
usual Euclidean plane wave. -/
theorem liftedChar_eq_charT4_torusQuotient (k : Z4) (x : R4) :
    liftedChar k x = charT4 k (torusQuotient x) := by
  change realPlaneWave (frequencyPhase k x) =
    charT4 k (torusQuotient x)
  unfold realPlaneWave charT4 torusQuotient
  rw [frequencyPhase_apply]
  simp only [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The phase functional is bounded by the project's degree-one
lattice weight. -/
theorem norm_frequencyPhase_le (k : Z4) :
    ‖frequencyPhase k‖ ≤ latticePolynomialWeight 1 k := by
  apply (frequencyPhase k).opNorm_le_bound
    (latticePolynomialWeight_nonneg 1 k)
  intro x
  rw [Real.norm_eq_abs, frequencyPhase_apply]
  calc
    |∑ i, (k i : ℝ) * x i| ≤
        ∑ i, |(k i : ℝ) * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,
        ((Int.natAbs (k i) : ℝ) + 1) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, ← Int.cast_abs, ← Nat.cast_natAbs]
      gcongr
      · linarith
      · exact norm_le_pi_norm x i
    _ = latticePolynomialWeight 1 k * ‖x‖ := by
      simp [latticePolynomialWeight, Finset.sum_mul]

/-- Uniform derivative bound for a lifted Fourier character.  It is
tailored to the weighted summability theorem in `NoiseRegularity`. -/
theorem norm_iteratedFDeriv_liftedChar_le
    (n : ℕ) (k : Z4) (x : R4) :
    ‖iteratedFDeriv ℝ n (liftedChar k) x‖ ≤
      latticePolynomialWeight n k := by
  rw [liftedChar,
    (frequencyPhase k).iteratedFDeriv_comp_right
      (contDiff_realPlaneWave (n : ℕ∞)) x le_rfl]
  calc
    ‖(iteratedFDeriv ℝ n realPlaneWave (frequencyPhase k x)).compContinuousLinearMap
        fun _ => frequencyPhase k‖ ≤
        ‖iteratedFDeriv ℝ n realPlaneWave (frequencyPhase k x)‖ *
          ∏ _i : Fin n, ‖frequencyPhase k‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖frequencyPhase k‖ ^ n := by
      rw [norm_iteratedFDeriv_realPlaneWave]
      simp
    _ ≤ (latticePolynomialWeight 1 k) ^ n := by
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_frequencyPhase_le k) n
    _ = latticePolynomialWeight n k := by
      simp [latticePolynomialWeight]

namespace NoiseModel

variable (M : NoiseModel)

/-- One Fourier summand of the mollified field, pulled back to `ℝ⁴`
and including the Lebesgue white-noise normalization. -/
def smoothMollifiedTerm
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (k : Z4) (x : R4) : ℂ :=
  (whiteNoiseFourierScale : ℂ) *
    M.mollifiedRandomCoeff ρ ε k ω * liftedChar k x

theorem contDiff_smoothMollifiedTerm
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (k : Z4)
    (n : ℕ∞) :
    ContDiff ℝ n (M.smoothMollifiedTerm ρ ε ω k) := by
  unfold smoothMollifiedTerm
  exact contDiff_const.mul (contDiff_liftedChar k n)

/-- The derivative of a Fourier summand is controlled by the
corresponding polynomially weighted random coefficient. -/
theorem norm_iteratedFDeriv_smoothMollifiedTerm_le
    (r : ℕ) (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (k : Z4) (x : R4) :
    ‖iteratedFDeriv ℝ r (M.smoothMollifiedTerm ρ ε ω k) x‖ ≤
      ‖whiteNoiseFourierScale‖ *
        ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖ := by
  let c : ℂ :=
    (whiteNoiseFourierScale : ℂ) *
      M.mollifiedRandomCoeff ρ ε k ω
  let L : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ c
  have hfun :
      M.smoothMollifiedTerm ρ ε ω k = L ∘ liftedChar k := by
    funext y
    simp [smoothMollifiedTerm, L, c]
  rw [hfun,
    L.iteratedFDeriv_comp_left
      (contDiff_liftedChar k (r : ℕ∞)).contDiffAt le_rfl]
  calc
    ‖L.compContinuousMultilinearMap
        (iteratedFDeriv ℝ r (liftedChar k) x)‖ ≤
        ‖L‖ * ‖iteratedFDeriv ℝ r (liftedChar k) x‖ :=
      L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖c‖ * latticePolynomialWeight r k := by
      gcongr
      · exact ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ c
      · exact norm_iteratedFDeriv_liftedChar_le r k x
    _ = ‖whiteNoiseFourierScale‖ *
        ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖ := by
      simp only [c, weightedMollifiedRandomCoeff, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (latticePolynomialWeight_nonneg r k)]
      ring

/-- Complex pullback of the mollified Fourier series to the universal
cover. -/
def xiEpsLiftC
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : R4) : ℂ :=
  ∑' k : Z4, M.smoothMollifiedTerm ρ ε ω k x

/-- Summability at every polynomial weight implies smoothness of the
complex periodic pullback. -/
theorem contDiff_xiEpsLiftC_of_weightedSummable
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (hω : ∀ r : ℕ, Summable fun k : Z4 =>
      ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖) :
    ContDiff ℝ (⊤ : ℕ∞) (M.xiEpsLiftC ρ ε ω) := by
  unfold xiEpsLiftC
  apply contDiff_tsum
    (v := fun r k =>
      ‖whiteNoiseFourierScale‖ *
        ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖)
  · intro k
    exact M.contDiff_smoothMollifiedTerm ρ ε ω k ⊤
  · intro r hr
    exact (hω r).mul_left ‖whiteNoiseFourierScale‖
  · intro r k x hr
    exact M.norm_iteratedFDeriv_smoothMollifiedTerm_le
      r ρ ε ω k x

/-- Real-valued smooth pullback of the mollified noise. -/
def xiEpsLift
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : R4) : ℝ :=
  (M.xiEpsLiftC ρ ε ω x).re

/-- The smooth Euclidean pullback is exactly the project field
evaluated after quotienting to the torus. -/
theorem xiEpsLift_eq_xiEps_torusQuotient
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω) (x : R4) :
    M.xiEpsLift ρ ε ω x =
      M.xiEps ρ ε ω (torusQuotient x) := by
  have hseries :
      M.xiEpsLiftC ρ ε ω x =
        (whiteNoiseFourierScale : ℂ) *
          ∑' k : Z4,
            ρ.symbol ε k * M.g k ω *
              charT4 k (torusQuotient x) := by
    unfold xiEpsLiftC smoothMollifiedTerm mollifiedRandomCoeff
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [liftedChar_eq_charT4_torusQuotient]
    ring
  rw [xiEpsLift, hseries]
  simp [xiEps]

theorem contDiff_xiEpsLift_of_weightedSummable
    (ρ : SmoothCutoff) (ε : ℝ) (ω : M.Ω)
    (hω : ∀ r : ℕ, Summable fun k : Z4 =>
      ‖M.weightedMollifiedRandomCoeff r ρ ε k ω‖) :
    ContDiff ℝ (⊤ : ℕ∞) (M.xiEpsLift ρ ε ω) := by
  unfold xiEpsLift
  exact Complex.reCLM.contDiff.comp
    (M.contDiff_xiEpsLiftC_of_weightedSummable ρ ε ω hω)

/-- For every fixed positive scale, the mollified field has a smooth
periodic pullback almost surely. -/
theorem ae_contDiff_xiEpsLift
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      ContDiff ℝ (⊤ : ℕ∞) (M.xiEpsLift ρ ε ω) := by
  filter_upwards
    [M.ae_forall_nat_summable_norm_weightedMollifiedRandomCoeff
      ρ hε] with ω hω
  exact M.contDiff_xiEpsLift_of_weightedSummable ρ ε ω hω

/-- A single probability-one event works simultaneously for every
member of an arbitrary countable positive scale family.  This is the
form used for a prescribed sequence `εₙ → 0`. -/
theorem ae_forall_nat_scale_contDiff_xiEpsLift
    (ρ : SmoothCutoff) (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ n : ℕ,
      ContDiff ℝ (⊤ : ℕ∞) (M.xiEpsLift ρ (ε n) ω) := by
  filter_upwards
    [M.ae_forall_nat_scale_forall_nat_weight ρ ε hε] with ω hω
  intro n
  exact M.contDiff_xiEpsLift_of_weightedSummable
    ρ (ε n) ω (hω n)

end NoiseModel

end

end Anderson4D
