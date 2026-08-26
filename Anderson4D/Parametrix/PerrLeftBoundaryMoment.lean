import Anderson4D.Parametrix.L2OneSidedGoodEvent
import Anderson4D.Parametrix.P35bClosure
import Anderson4D.DetParametrix.Core.FinalBound

/-!
# First-moment bound for the one-sided parametrix boundary

This file closes the elementary probabilistic part of paper (3.32).
The last-block boundary from (3.21) is first identified almost surely
with a measurable finite sum of the physical coefficient operators.
Cauchy--Schwarz then reduces its first moment to the orderwise
P-3.5b second-moment bounds, the continuous-noise second moment, and
the P-3.5a bounds on the deterministic counterterms.

The zeroth physical order is kept separate: it is the bounded Green
operator, not a Hilbert--Schmidt coefficient operator.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace PartialPairing

/-! ## A measurable physical representative of each graded order -/

/-- The physical order `P_m = Q_m G`.  At order zero this is `G`;
positive orders use the canonical Fourier-coefficient realization. -/
def canonicalPhysicalParametrixOrderL2Operator
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (m : ℕ) (ω : M.Ω) : TorusL2 →L[ℂ] TorusL2 :=
  if m = 0 then
    greenL2Op
  else
    canonicalParametrixOrderL2Operator M ρ lam ε m ω

/-- Its second-moment budget, with the deterministic zeroth order
bounded by one. -/
def canonicalPhysicalParametrixOrderL2SecondMomentBudget
    (outerConstant powerConstant lam ε : ℝ)
    (m : ℕ) : ℝ :=
  if m = 0 then
    1
  else
    canonicalParametrixOrderL2SecondMomentBudget
      outerConstant powerConstant lam ε m

theorem canonicalPhysicalParametrixOrderL2SecondMomentBudget_nonneg
    {outerConstant powerConstant lam ε : ℝ}
    (m : ℕ)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    0 ≤ canonicalPhysicalParametrixOrderL2SecondMomentBudget
      outerConstant powerConstant lam ε m := by
  unfold canonicalPhysicalParametrixOrderL2SecondMomentBudget
  split_ifs
  · norm_num
  · exact
      canonicalParametrixOrderL2SecondMomentBudget_nonneg
        houter hpower hlam

theorem gradedParametrixL2FactorOrder_mul_green_eq_physical
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A m : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (hm : m ≤ A)
    (hagree :
      ParametrixGradedCoefficientAgreement
        M ρ lam ε A ω)
    (hcanonical :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        torusFourierMatrixCoeff
            (canonicalParametrixOrderL2Operator
              M ρ lam ε n ω) α β =
          (paperTorusVolume : ℂ)⁻¹ *
            pmCoeff M ρ lam ε n α β ω) :
    gradedParametrixL2FactorOrder
          M ρ lam ε ω hξ m *
        greenL2Op =
      canonicalPhysicalParametrixOrderL2Operator
        M ρ lam ε m ω := by
  by_cases hm0 : m = 0
  · subst m
    rw [gradedParametrixL2FactorOrder_zero, one_mul]
    simp [canonicalPhysicalParametrixOrderL2Operator]
  · rw [canonicalPhysicalParametrixOrderL2Operator, if_neg hm0]
    exact
      gradedParametrixL2FactorOrder_mul_green_eq_canonical
        M ρ lam ε A m ω hξ hm hagree
        (hcanonical m (Nat.one_le_iff_ne_zero.mpr hm0) hm)

/-! ## Measurable noise and counterterm multipliers -/

/-- The measurable degree-one multiplier. -/
def canonicalNoiseMultiplicationL2Operator
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) : TorusL2 →L[ℂ] TorusL2 :=
  continuousMultiplicationOp
    ((lamEps lam ε : ℂ) • xiEpsContinuousMap M ρ ε ω)

/-- Multiplication by the deterministic order-`2q` counterterm. -/
def canonicalCountertermMultiplicationL2Operator
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ) :
    TorusL2 →L[ℂ] TorusL2 :=
  continuousMultiplicationOp
    (ContinuousMap.const T4 (renormC2q ρ lam ε q : ℂ))

theorem renormWordWeightContinuousMap_one_eq
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (hsum : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖) :
    renormWordWeightContinuousMap M ρ lam ε ω hξ 1 =
      (lamEps lam ε : ℂ) • xiEpsContinuousMap M ρ ε ω := by
  apply ContinuousMap.ext
  intro x
  rw [renormWordWeightContinuousMap_apply]
  change
    (renormWordWeight M ρ lam ε 1 x ω : ℂ) =
      (lamEps lam ε : ℂ) *
        xiEpsContinuousMap M ρ ε ω x
  rw [xiEpsContinuousMap_eq_xiEps_of_summable
    M ρ ε ω hsum x]
  simp [renormWordWeight]

theorem gradedNoiseL2Factor_eq_measurable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (hsum : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖) :
    gradedNoiseL2Factor M ρ lam ε ω hξ =
      greenL2Op *
        canonicalNoiseMultiplicationL2Operator
          M ρ lam ε ω := by
  unfold gradedNoiseL2Factor gradedBlockL2Factor
  unfold canonicalNoiseMultiplicationL2Operator Kop
  rw [renormWordWeightContinuousMap_one_eq
    M ρ lam ε ω hξ hsum]

theorem gradedCountertermL2Factor_eq_measurable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (q : ℕ) :
    gradedCountertermL2Factor M ρ lam ε ω hξ q =
      greenL2Op *
        canonicalCountertermMultiplicationL2Operator
          ρ lam ε q := by
  have hne : 2 * q ≠ 1 := by omega
  have heven : Even (2 * q) := even_two_mul q
  have hhalf : 2 * q / 2 = q := by omega
  unfold gradedCountertermL2Factor gradedBlockL2Factor
  unfold canonicalCountertermMultiplicationL2Operator Kop
  have hweight :
      renormWordWeightContinuousMap
          M ρ lam ε ω hξ (2 * q) =
        -ContinuousMap.const T4
          (renormC2q ρ lam ε q : ℂ) := by
    apply ContinuousMap.ext
    intro x
    simp [renormWordWeightContinuousMap,
      renormWordWeight, hne, heven, hhalf]
  rw [hweight]
  change
    -(greenL2Op *
        continuousMultiplicationLM
          (-ContinuousMap.const T4
            (renormC2q ρ lam ε q : ℂ))) =
      greenL2Op *
        continuousMultiplicationLM
          (ContinuousMap.const T4
            (renormC2q ρ lam ε q : ℂ))
  rw [map_neg, mul_neg, neg_neg]

/-! ## The measurable physical boundary -/

/-- Measurable physical realization of the last-block boundary in
(3.21). -/
def measurableCanonicalPerrLeftBoundary
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω) : TorusL2 →L[ℂ] TorusL2 :=
  -(canonicalPhysicalParametrixOrderL2Operator
        M ρ lam ε A ω *
      canonicalNoiseMultiplicationL2Operator
        M ρ lam ε ω) +
    ∑ r ∈ Finset.range (A + 1),
      ∑ q ∈ (Finset.Icc 1 A).filter
        (fun q => A < r + 2 * q),
        canonicalPhysicalParametrixOrderL2Operator
              M ρ lam ε r ω *
          canonicalCountertermMultiplicationL2Operator
            ρ lam ε q

theorem gradedPerrLeftBoundary_eq_measurable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (hsum : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (hagree :
      ParametrixGradedCoefficientAgreement
        M ρ lam ε A ω)
    (hcanonical :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        torusFourierMatrixCoeff
            (canonicalParametrixOrderL2Operator
              M ρ lam ε n ω) α β =
          (paperTorusVolume : ℂ)⁻¹ *
            pmCoeff M ρ lam ε n α β ω) :
    gradedPerrLeftBoundary M ρ lam ε ω hξ A =
      measurableCanonicalPerrLeftBoundary
        M ρ lam ε A ω := by
  unfold gradedPerrLeftBoundary
  unfold measurableCanonicalPerrLeftBoundary
  rw [gradedNoiseL2Factor_eq_measurable
    M ρ lam ε ω hξ hsum]
  rw [← mul_assoc,
    gradedParametrixL2FactorOrder_mul_green_eq_physical
      M ρ lam ε A A ω hξ le_rfl hagree hcanonical]
  apply congrArg
    (fun S =>
      -(canonicalPhysicalParametrixOrderL2Operator
            M ρ lam ε A ω *
          canonicalNoiseMultiplicationL2Operator
            M ρ lam ε ω) + S)
  apply Finset.sum_congr rfl
  intro r hr
  have hrA : r ≤ A := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  apply Finset.sum_congr rfl
  intro q hq
  rw [gradedCountertermL2Factor_eq_measurable
    M ρ lam ε ω hξ q]
  rw [← mul_assoc,
    gradedParametrixL2FactorOrder_mul_green_eq_physical
      M ρ lam ε A r ω hξ hrA hagree hcanonical]

theorem ae_canonicalPerrLeftBoundary_eq_measurable
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ A →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω) :
    canonicalPerrLeftBoundary M ρ lam ε A =ᵐ[
        (volume : Measure M.Ω)]
      measurableCanonicalPerrLeftBoundary
        M ρ lam ε A := by
  have hcanonical :=
    ae_canonicalParametrixOrderL2Operator_coeff_of_momentBounds
      hfubini hwick hdet
      houter hpower hlam hε hεle
  filter_upwards
    [M.ae_continuous_xiEps ρ hε,
      M.ae_summable_norm_mollifiedRandomCoeff ρ hε,
      hagree, hcanonical] with
      ω hξ hsum hagreeω hcanonicalω
  unfold canonicalPerrLeftBoundary
  rw [dif_pos hξ]
  exact gradedPerrLeftBoundary_eq_measurable
    M ρ lam ε A ω hξ hsum hagreeω hcanonicalω

/-! ## Measurability and `L²` control of the physical pieces -/

theorem
    aestronglyMeasurable_canonicalPhysicalParametrixOrderL2Operator
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    AEStronglyMeasurable
      (canonicalPhysicalParametrixOrderL2Operator
        M ρ lam ε m)
      (volume : Measure M.Ω) := by
  unfold canonicalPhysicalParametrixOrderL2Operator
  split_ifs with hm0
  · exact stronglyMeasurable_const.aestronglyMeasurable
  · exact
      aestronglyMeasurable_canonicalParametrixOrderL2Operator
        (hfubini m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        (hwick m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        (hdet m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        houter hpower hlam hε hεle

theorem integrable_normSq_canonicalPhysicalParametrixOrderL2Operator
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    Integrable
      (fun ω =>
        ‖canonicalPhysicalParametrixOrderL2Operator
            M ρ lam ε m ω‖ ^ 2)
      (volume : Measure M.Ω) := by
  unfold canonicalPhysicalParametrixOrderL2Operator
  split_ifs with hm0
  · exact integrable_const _
  · exact
      integrable_normSq_canonicalParametrixOrderL2Operator
        (hfubini m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        (hwick m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        (hdet m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        houter hpower hlam hε hεle

theorem memLp_canonicalPhysicalParametrixOrderL2Operator
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    MemLp
      (canonicalPhysicalParametrixOrderL2Operator
        M ρ lam ε m)
      2 (volume : Measure M.Ω) :=
  (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_canonicalPhysicalParametrixOrderL2Operator
      hm hfubini hwick hdet houter hpower hlam hε hεle)).2
    (integrable_normSq_canonicalPhysicalParametrixOrderL2Operator
      hm hfubini hwick hdet houter hpower hlam hε hεle)

theorem
    integral_normSq_canonicalPhysicalParametrixOrderL2Operator_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∫ ω,
        ‖canonicalPhysicalParametrixOrderL2Operator
            M ρ lam ε m ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
      canonicalPhysicalParametrixOrderL2SecondMomentBudget
        outerConstant powerConstant lam ε m := by
  by_cases hm0 : m = 0
  · subst m
    simp only [canonicalPhysicalParametrixOrderL2Operator,
      canonicalPhysicalParametrixOrderL2SecondMomentBudget,
      if_pos]
    rw [integral_const]
    norm_num
    nlinarith [norm_greenL2Op_le_one,
      norm_nonneg greenL2Op]
  · simp only [canonicalPhysicalParametrixOrderL2Operator,
      canonicalPhysicalParametrixOrderL2SecondMomentBudget,
      hm0, if_false]
    exact
      integral_normSq_canonicalParametrixOrderL2Operator_le
        (hfubini m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        (hwick m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        (hdet m (Nat.one_le_iff_ne_zero.mpr hm0) hm)
        houter hpower hlam hε hεle

/-! ## The measurable degree-one multiplier -/

theorem measurable_canonicalNoiseMultiplicationL2Operator
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) :
    Measurable
      (canonicalNoiseMultiplicationL2Operator
        M ρ lam ε) := by
  unfold canonicalNoiseMultiplicationL2Operator
  exact continuousMultiplicationCLM.measurable.comp
    ((measurable_xiEpsContinuousMap M ρ ε).const_smul
      (lamEps lam ε : ℂ))

/-- Explicit second-moment budget for the degree-one multiplication
operator. -/
def canonicalNoiseMultiplicationL2SecondMomentBudget
    (ρ : SmoothCutoff) (lam ε : ℝ) : ℝ :=
  (‖(lamEps lam ε : ℂ)‖ *
    (‖NoiseModel.whiteNoiseFourierScale‖ *
      ∑' k : Z4, ‖ρ.symbol ε k‖)) ^ 2

theorem canonicalNoiseMultiplicationL2SecondMomentBudget_nonneg
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    0 ≤ canonicalNoiseMultiplicationL2SecondMomentBudget
      ρ lam ε :=
  sq_nonneg _

theorem memLp_canonicalNoiseMultiplicationL2Operator
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    MemLp
      (canonicalNoiseMultiplicationL2Operator
        M ρ lam ε)
      2 (volume : Measure M.Ω) := by
  apply
    (memLp_xiEpsContinuousMap M ρ hε).of_le_mul
      (continuousMultiplicationCLM.continuous.comp_aestronglyMeasurable
        (((measurable_xiEpsContinuousMap M ρ ε).const_smul
          (lamEps lam ε : ℂ)).aestronglyMeasurable))
  filter_upwards with ω
  calc
    ‖canonicalNoiseMultiplicationL2Operator
        M ρ lam ε ω‖ ≤
        ‖(lamEps lam ε : ℂ) •
          xiEpsContinuousMap M ρ ε ω‖ :=
      continuousMultiplicationOp_norm_le _
    _ = ‖(lamEps lam ε : ℂ)‖ *
        ‖xiEpsContinuousMap M ρ ε ω‖ := norm_smul _ _

theorem
    integral_normSq_canonicalNoiseMultiplicationL2Operator_le
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ ω,
        ‖canonicalNoiseMultiplicationL2Operator
            M ρ lam ε ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
      canonicalNoiseMultiplicationL2SecondMomentBudget
        ρ lam ε := by
  have hnoise :=
    memLp_canonicalNoiseMultiplicationL2Operator
      M ρ lam hε
  have hintOp :
      Integrable
        (fun ω =>
          ‖canonicalNoiseMultiplicationL2Operator
              M ρ lam ε ω‖ ^ 2)
        (volume : Measure M.Ω) :=
    (memLp_two_iff_integrable_sq_norm
      hnoise.aestronglyMeasurable).1 hnoise
  have hintXi :=
    integrable_norm_sq_xiEpsContinuousMap M ρ hε
  calc
    (∫ ω,
        ‖canonicalNoiseMultiplicationL2Operator
            M ρ lam ε ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
        ∫ ω,
          (‖(lamEps lam ε : ℂ)‖ *
            ‖xiEpsContinuousMap M ρ ε ω‖) ^ 2
          ∂(volume : Measure M.Ω) := by
      apply integral_mono_ae hintOp
      · simpa only [mul_pow] using
          hintXi.const_mul
            (‖(lamEps lam ε : ℂ)‖ ^ 2)
      · filter_upwards with ω
        have hop :
            ‖canonicalNoiseMultiplicationL2Operator
                M ρ lam ε ω‖ ≤
              ‖(lamEps lam ε : ℂ)‖ *
                ‖xiEpsContinuousMap M ρ ε ω‖ := by
          unfold canonicalNoiseMultiplicationL2Operator
          exact (continuousMultiplicationOp_norm_le _).trans_eq
            (norm_smul _ _)
        exact pow_le_pow_left₀
          (norm_nonneg _)
          hop 2
    _ = ‖(lamEps lam ε : ℂ)‖ ^ 2 *
        ∫ ω, ‖xiEpsContinuousMap M ρ ε ω‖ ^ 2
          ∂(volume : Measure M.Ω) := by
      simp_rw [mul_pow]
      rw [integral_const_mul]
    _ ≤ ‖(lamEps lam ε : ℂ)‖ ^ 2 *
        (‖NoiseModel.whiteNoiseFourierScale‖ *
          ∑' k : Z4, ‖ρ.symbol ε k‖) ^ 2 := by
      gcongr
      exact integral_norm_sq_xiEpsContinuousMap_le M ρ hε
    _ = canonicalNoiseMultiplicationL2SecondMomentBudget
        ρ lam ε := by
      unfold canonicalNoiseMultiplicationL2SecondMomentBudget
      ring

/-! ## Cauchy--Schwarz estimates for the boundary summands -/

private theorem integral_norm_le_sqrt_integral_norm_sq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → E)
    (hf : MemLp f 2 μ) :
    ∫ ω, ‖f ω‖ ∂μ ≤
      Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
  have hfnorm :
      MemLp (fun ω => ‖f ω‖) (ENNReal.ofReal 2) μ := by
    norm_num
    exact hf.norm
  have hone :
      MemLp (fun _ω : Ω => (1 : ℝ)) (ENNReal.ofReal 2) μ :=
    memLp_const 1
  have h :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ)
      Real.HolderConjugate.two_two
      (f := fun ω => ‖f ω‖) (g := fun _ω => (1 : ℝ))
      (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun _ => zero_le_one)
      hfnorm hone
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h

private theorem integral_norm_mul_le_sqrt_integral_norm_sq_mul
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedRing E]
    (μ : Measure Ω)
    (f g : Ω → E)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, ‖f ω * g ω‖ ∂μ) ≤
      Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) *
        Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
  have hprod : Integrable (f * g) μ :=
    hf.integrable_mul hg
  have hnormProd :
      Integrable (fun ω => ‖f ω‖ * ‖g ω‖) μ :=
    hf.norm.integrable_mul hg.norm
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ)
      Real.HolderConjugate.two_two
      (f := fun ω => ‖f ω‖)
      (g := fun ω => ‖g ω‖)
      (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun _ => norm_nonneg _)
      (by
        norm_num
        exact hf.norm)
      (by
        norm_num
        exact hg.norm)
  calc
    (∫ ω, ‖f ω * g ω‖ ∂μ) ≤
        ∫ ω, ‖f ω‖ * ‖g ω‖ ∂μ := by
      apply integral_mono_ae hprod.norm hnormProd
      filter_upwards with ω
      exact norm_mul_le _ _
    _ ≤
        Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ) *
          Real.sqrt (∫ ω, ‖g ω‖ ^ 2 ∂μ) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two] using hholder

theorem
    integral_norm_physicalParametrixOrder_mul_noise_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∫ ω,
        ‖canonicalPhysicalParametrixOrderL2Operator
              M ρ lam ε m ω *
            canonicalNoiseMultiplicationL2Operator
              M ρ lam ε ω‖
        ∂(volume : Measure M.Ω)) ≤
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε m) *
        Real.sqrt
          (canonicalNoiseMultiplicationL2SecondMomentBudget
            ρ lam ε) := by
  have hP :=
    memLp_canonicalPhysicalParametrixOrderL2Operator
      hm hfubini hwick hdet houter hpower hlam hε hεle
  have hN :=
    memLp_canonicalNoiseMultiplicationL2Operator
      M ρ lam hε
  calc
    (∫ ω,
        ‖canonicalPhysicalParametrixOrderL2Operator
              M ρ lam ε m ω *
            canonicalNoiseMultiplicationL2Operator
              M ρ lam ε ω‖
        ∂(volume : Measure M.Ω)) ≤
      Real.sqrt
          (∫ ω,
            ‖canonicalPhysicalParametrixOrderL2Operator
                M ρ lam ε m ω‖ ^ 2
            ∂(volume : Measure M.Ω)) *
        Real.sqrt
          (∫ ω,
            ‖canonicalNoiseMultiplicationL2Operator
                M ρ lam ε ω‖ ^ 2
            ∂(volume : Measure M.Ω)) :=
      integral_norm_mul_le_sqrt_integral_norm_sq_mul
        (volume : Measure M.Ω) _ _ hP hN
    _ ≤
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε m) *
        Real.sqrt
          (canonicalNoiseMultiplicationL2SecondMomentBudget
            ρ lam ε) := by
      gcongr
      · exact
          integral_normSq_canonicalPhysicalParametrixOrderL2Operator_le
            hm hfubini hwick hdet
            houter hpower hlam hε hεle
      · exact
          integral_normSq_canonicalNoiseMultiplicationL2Operator_le
            M ρ lam hε

theorem
    integral_norm_physicalParametrixOrder_mul_counterterm_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A) (q : ℕ)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∫ ω,
        ‖canonicalPhysicalParametrixOrderL2Operator
              M ρ lam ε m ω *
            canonicalCountertermMultiplicationL2Operator
              ρ lam ε q‖
        ∂(volume : Measure M.Ω)) ≤
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε m) *
        |renormC2q ρ lam ε q| := by
  let P :=
    canonicalPhysicalParametrixOrderL2Operator
      M ρ lam ε m
  let C :=
    canonicalCountertermMultiplicationL2Operator
      ρ lam ε q
  have hP : MemLp P 2 (volume : Measure M.Ω) :=
    memLp_canonicalPhysicalParametrixOrderL2Operator
      hm hfubini hwick hdet houter hpower hlam hε hεle
  have hcs :
      (∫ ω, ‖P ω * C‖
        ∂(volume : Measure M.Ω)) ≤
        Real.sqrt
            (∫ ω, ‖P ω‖ ^ 2
              ∂(volume : Measure M.Ω)) *
          ‖C‖ := by
    have h :=
      integral_norm_mul_le_sqrt_integral_norm_sq_mul
        (volume : Measure M.Ω)
        P (fun _ω => C) hP (memLp_const C)
    simpa [Real.sqrt_sq (norm_nonneg C)] using h
  have hC :
      ‖C‖ ≤ |renormC2q ρ lam ε q| := by
    unfold C canonicalCountertermMultiplicationL2Operator
    calc
      ‖continuousMultiplicationOp
          (ContinuousMap.const T4
            (renormC2q ρ lam ε q : ℂ))‖ ≤
          ‖ContinuousMap.const T4
            (renormC2q ρ lam ε q : ℂ)‖ :=
        continuousMultiplicationOp_norm_le _
      _ ≤ ‖(renormC2q ρ lam ε q : ℂ)‖ :=
        ((ContinuousMap.const T4
          (renormC2q ρ lam ε q : ℂ)).norm_le
            (norm_nonneg (renormC2q ρ lam ε q : ℂ))).2
          fun _ => le_rfl
      _ = |renormC2q ρ lam ε q| := by simp
  calc
    (∫ ω,
        ‖canonicalPhysicalParametrixOrderL2Operator
              M ρ lam ε m ω *
            canonicalCountertermMultiplicationL2Operator
              ρ lam ε q‖
        ∂(volume : Measure M.Ω)) ≤
      Real.sqrt
          (∫ ω,
            ‖canonicalPhysicalParametrixOrderL2Operator
                M ρ lam ε m ω‖ ^ 2
            ∂(volume : Measure M.Ω)) *
        ‖canonicalCountertermMultiplicationL2Operator
          ρ lam ε q‖ := by
      simpa only [P, C] using hcs
    _ ≤
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε m) *
        |renormC2q ρ lam ε q| := by
      apply mul_le_mul
      · exact Real.sqrt_le_sqrt
          (integral_normSq_canonicalPhysicalParametrixOrderL2Operator_le
            hm hfubini hwick hdet
            houter hpower hlam hε hεle)
      · exact hC
      · exact norm_nonneg _
      · exact Real.sqrt_nonneg _

/-! ## Integrability and finite-sum bookkeeping -/

theorem integrable_physicalParametrixOrder_mul_noise
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    Integrable
      (fun ω =>
        canonicalPhysicalParametrixOrderL2Operator
              M ρ lam ε m ω *
            canonicalNoiseMultiplicationL2Operator
              M ρ lam ε ω)
      (volume : Measure M.Ω) :=
  (memLp_canonicalPhysicalParametrixOrderL2Operator
      hm hfubini hwick hdet houter hpower hlam hε hεle).integrable_mul
    (memLp_canonicalNoiseMultiplicationL2Operator
      M ρ lam hε)

theorem integrable_physicalParametrixOrder_mul_counterterm
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A m : ℕ} (hm : m ≤ A) (q : ℕ)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    Integrable
      (fun ω =>
        canonicalPhysicalParametrixOrderL2Operator
              M ρ lam ε m ω *
            canonicalCountertermMultiplicationL2Operator
              ρ lam ε q)
      (volume : Measure M.Ω) :=
  (memLp_canonicalPhysicalParametrixOrderL2Operator
      hm hfubini hwick hdet houter hpower hlam hε hεle).integrable_mul
    (memLp_const
      (canonicalCountertermMultiplicationL2Operator
        ρ lam ε q) :
      MemLp
        (fun _ω : M.Ω =>
          canonicalCountertermMultiplicationL2Operator
            ρ lam ε q)
        2 (volume : Measure M.Ω))

private theorem integral_norm_add_le
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    {μ : Measure Ω} (f g : Ω → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ ω, ‖f ω + g ω‖ ∂μ) ≤
      (∫ ω, ‖f ω‖ ∂μ) + ∫ ω, ‖g ω‖ ∂μ := by
  calc
    (∫ ω, ‖f ω + g ω‖ ∂μ) ≤
        ∫ ω, ‖f ω‖ + ‖g ω‖ ∂μ := by
      apply integral_mono_ae (hf.add hg).norm (hf.norm.add hg.norm)
      filter_upwards with ω
      exact norm_add_le _ _
    _ = (∫ ω, ‖f ω‖ ∂μ) +
        ∫ ω, ‖g ω‖ ∂μ :=
      integral_add hf.norm hg.norm

private theorem integral_norm_finsetSum_le
    {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    {μ : Measure Ω}
    (s : Finset ι) (F : ι → Ω → E)
    (hF : ∀ i ∈ s, Integrable (F i) μ) :
    (∫ ω, ‖∑ i ∈ s, F i ω‖ ∂μ) ≤
      ∑ i ∈ s, ∫ ω, ‖F i ω‖ ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hFa : Integrable (F a) μ :=
        hF a (Finset.mem_insert_self a s)
      have hFs :
          Integrable (fun ω => ∑ i ∈ s, F i ω) μ :=
        integrable_finsetSum s fun i hi =>
          hF i (Finset.mem_insert_of_mem hi)
      simp only [Finset.sum_insert ha]
      exact
        (integral_norm_add_le
          (F a) (fun ω => ∑ i ∈ s, F i ω)
          hFa hFs).trans
          (add_le_add_right
            (ih fun i hi =>
              hF i (Finset.mem_insert_of_mem hi))
            _)

set_option maxHeartbeats 800000 in
theorem integrable_measurableCanonicalPerrLeftBoundary
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    Integrable
      (measurableCanonicalPerrLeftBoundary
        M ρ lam ε A)
      (volume : Measure M.Ω) := by
  have hhead :
      Integrable
        (fun ω =>
          -(canonicalPhysicalParametrixOrderL2Operator
                M ρ lam ε A ω *
              canonicalNoiseMultiplicationL2Operator
                M ρ lam ε ω))
        (volume : Measure M.Ω) :=
    (integrable_physicalParametrixOrder_mul_noise
      le_rfl hfubini hwick hdet
      houter hpower hlam hε hεle).neg
  let F :
      ℕ → ℕ → M.Ω → TorusL2 →L[ℂ] TorusL2 :=
    fun r q ω =>
      canonicalPhysicalParametrixOrderL2Operator
            M ρ lam ε r ω *
        canonicalCountertermMultiplicationL2Operator
          ρ lam ε q
  have hF :
      ∀ r, r ≤ A → ∀ q,
        Integrable (F r q) (volume : Measure M.Ω) := by
    intro r hr q
    dsimp only [F]
    exact
      integrable_physicalParametrixOrder_mul_counterterm
        hr q hfubini hwick hdet
        houter hpower hlam hε hεle
  have htail :
      Integrable
        (fun ω =>
          ∑ r ∈ Finset.range (A + 1),
            ∑ q ∈ (Finset.Icc 1 A).filter
              (fun q => A < r + 2 * q),
              canonicalPhysicalParametrixOrderL2Operator
                    M ρ lam ε r ω *
                canonicalCountertermMultiplicationL2Operator
                  ρ lam ε q)
        (volume : Measure M.Ω) := by
    have htailF :
        Integrable
          (fun ω =>
            ∑ r ∈ Finset.range (A + 1),
              ∑ q ∈ (Finset.Icc 1 A).filter
                (fun q => A < r + 2 * q),
                F r q ω)
          (volume : Measure M.Ω) := by
      apply integrable_finsetSum
        (μ := (volume : Measure M.Ω))
        (f := fun r ω =>
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q),
            F r q ω)
      intro r hr
      apply integrable_finsetSum
        (μ := (volume : Measure M.Ω))
        (f := fun q ω => F r q ω)
      intro q _hq
      exact hF r (Nat.le_of_lt_succ
        (Finset.mem_range.mp hr)) q
    simpa only [F] using htailF
  unfold measurableCanonicalPerrLeftBoundary
  apply (hhead.norm.add htail.norm).mono'
    (hhead.aestronglyMeasurable.add
      htail.aestronglyMeasurable)
  filter_upwards with ω
  exact norm_add_le _ _

theorem integrable_canonicalPerrLeftBoundary
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω) :
    Integrable
      (canonicalPerrLeftBoundary M ρ lam ε A)
      (volume : Measure M.Ω) := by
  exact
    (integrable_measurableCanonicalPerrLeftBoundary
      hfubini hwick hdet houter hpower hlam hε hεle).congr
      (ae_canonicalPerrLeftBoundary_eq_measurable
        hfubini hwick hdet houter hpower hlam hε hεle
        hagree).symm

/-! ## Explicit first-moment budget -/

/-- The finite expression obtained from P-3.5b, the continuous-noise
second moment, and a supplied P-3.5a envelope for `|C_{2q}|`. -/
def canonicalPerrLeftBoundaryFirstMomentBudget
    (outerConstant powerConstant : ℝ)
    (ρ : SmoothCutoff) (lam ε : ℝ) (A : ℕ)
    (countertermBudget : ℕ → ℝ) : ℝ :=
  Real.sqrt
      (canonicalPhysicalParametrixOrderL2SecondMomentBudget
        outerConstant powerConstant lam ε A) *
    Real.sqrt
      (canonicalNoiseMultiplicationL2SecondMomentBudget
        ρ lam ε) +
  ∑ r ∈ Finset.range (A + 1),
    ∑ q ∈ (Finset.Icc 1 A).filter
      (fun q => A < r + 2 * q),
      Real.sqrt
          (canonicalPhysicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε r) *
        countertermBudget q

theorem integral_norm_canonicalPerrLeftBoundary_le_budget
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (countertermBudget : ℕ → ℝ)
    (hfubini :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε n α β)
    (hwick :
      ∀ n, 1 ≤ n → n ≤ A →
        WickAtSecondMomentLaw M ρ ε n)
    (hdet :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε n α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε n α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω)
    (hcounter :
      ∀ q ∈ Finset.Icc 1 A,
        |renormC2q ρ lam ε q| ≤ countertermBudget q) :
    (∫ ω,
        ‖canonicalPerrLeftBoundary
          M ρ lam ε A ω‖
        ∂(volume : Measure M.Ω)) ≤
      canonicalPerrLeftBoundaryFirstMomentBudget
        outerConstant powerConstant ρ lam ε A
        countertermBudget := by
  let P : ℕ → M.Ω → TorusL2 →L[ℂ] TorusL2 :=
    fun m =>
      canonicalPhysicalParametrixOrderL2Operator
        M ρ lam ε m
  let N : M.Ω → TorusL2 →L[ℂ] TorusL2 :=
    canonicalNoiseMultiplicationL2Operator M ρ lam ε
  let C : ℕ → TorusL2 →L[ℂ] TorusL2 :=
    canonicalCountertermMultiplicationL2Operator ρ lam ε
  let H : M.Ω → TorusL2 →L[ℂ] TorusL2 :=
    fun ω => -(P A ω * N ω)
  let F : ℕ → ℕ → M.Ω → TorusL2 →L[ℂ] TorusL2 :=
    fun r q ω => P r ω * C q
  let S : M.Ω → TorusL2 →L[ℂ] TorusL2 :=
    fun ω =>
      ∑ r ∈ Finset.range (A + 1),
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => A < r + 2 * q),
          F r q ω
  have hH : Integrable H (volume : Measure M.Ω) := by
    dsimp only [H, P, N]
    exact
      (integrable_physicalParametrixOrder_mul_noise
        le_rfl hfubini hwick hdet
        houter hpower hlam hε hεle).neg
  have hF :
      ∀ r, r ≤ A → ∀ q,
        Integrable (F r q) (volume : Measure M.Ω) := by
    intro r hr q
    dsimp only [F, P, C]
    exact
      integrable_physicalParametrixOrder_mul_counterterm
        hr q hfubini hwick hdet
        houter hpower hlam hε hεle
  have hS : Integrable S (volume : Measure M.Ω) := by
    dsimp only [S]
    apply integrable_finsetSum
      (μ := (volume : Measure M.Ω))
      (f := fun r ω =>
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => A < r + 2 * q),
          F r q ω)
    intro r hr
    apply integrable_finsetSum
      (μ := (volume : Measure M.Ω))
      (f := fun q ω => F r q ω)
    intro q _hq
    exact hF r (Nat.le_of_lt_succ
      (Finset.mem_range.mp hr)) q
  have hhead :
      (∫ ω, ‖H ω‖ ∂(volume : Measure M.Ω)) ≤
        Real.sqrt
            (canonicalPhysicalParametrixOrderL2SecondMomentBudget
              outerConstant powerConstant lam ε A) *
          Real.sqrt
            (canonicalNoiseMultiplicationL2SecondMomentBudget
              ρ lam ε) := by
    simpa only [H, P, N, norm_neg] using
      (integral_norm_physicalParametrixOrder_mul_noise_le
        (M := M) (ρ := ρ) le_rfl
        hfubini hwick hdet
        houter hpower hlam hε hεle)
  have hterm :
      ∀ r, r ≤ A → ∀ q ∈ Finset.Icc 1 A,
        (∫ ω, ‖F r q ω‖
          ∂(volume : Measure M.Ω)) ≤
          Real.sqrt
              (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                outerConstant powerConstant lam ε r) *
            countertermBudget q := by
    intro r hr q hq
    calc
      (∫ ω, ‖F r q ω‖
        ∂(volume : Measure M.Ω)) ≤
          Real.sqrt
              (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                outerConstant powerConstant lam ε r) *
            |renormC2q ρ lam ε q| := by
        simpa only [F, P, C] using
          (integral_norm_physicalParametrixOrder_mul_counterterm_le
            (M := M) hr q hfubini hwick hdet
            houter hpower hlam hε hεle)
      _ ≤
          Real.sqrt
              (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                outerConstant powerConstant lam ε r) *
            countertermBudget q :=
        mul_le_mul_of_nonneg_left (hcounter q hq)
          (Real.sqrt_nonneg _)
  have htail :
      (∫ ω, ‖S ω‖ ∂(volume : Measure M.Ω)) ≤
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q),
            Real.sqrt
                (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                  outerConstant powerConstant lam ε r) *
              countertermBudget q := by
    dsimp only [S]
    calc
      (∫ ω,
          ‖∑ r ∈ Finset.range (A + 1),
              ∑ q ∈ (Finset.Icc 1 A).filter
                (fun q => A < r + 2 * q),
                F r q ω‖
          ∂(volume : Measure M.Ω)) ≤
          ∑ r ∈ Finset.range (A + 1),
            ∫ ω,
              ‖∑ q ∈ (Finset.Icc 1 A).filter
                  (fun q => A < r + 2 * q),
                  F r q ω‖
              ∂(volume : Measure M.Ω) := by
        apply integral_norm_finsetSum_le
        intro r hr
        apply integrable_finsetSum
          (μ := (volume : Measure M.Ω))
          (f := fun q ω => F r q ω)
        intro q _hq
        exact hF r (Nat.le_of_lt_succ
          (Finset.mem_range.mp hr)) q
      _ ≤
          ∑ r ∈ Finset.range (A + 1),
            ∑ q ∈ (Finset.Icc 1 A).filter
              (fun q => A < r + 2 * q),
              ∫ ω, ‖F r q ω‖
                ∂(volume : Measure M.Ω) := by
        apply Finset.sum_le_sum
        intro r hr
        apply integral_norm_finsetSum_le
        intro q _hq
        exact hF r (Nat.le_of_lt_succ
          (Finset.mem_range.mp hr)) q
      _ ≤
          ∑ r ∈ Finset.range (A + 1),
            ∑ q ∈ (Finset.Icc 1 A).filter
              (fun q => A < r + 2 * q),
              Real.sqrt
                  (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                    outerConstant powerConstant lam ε r) *
                countertermBudget q := by
        apply Finset.sum_le_sum
        intro r hr
        have hrA := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
        apply Finset.sum_le_sum
        intro q hq
        exact hterm r hrA q (Finset.mem_filter.mp hq).1
  have heq :=
    ae_canonicalPerrLeftBoundary_eq_measurable
      hfubini hwick hdet houter hpower hlam hε hεle hagree
  have hnorm :
      (fun ω =>
        ‖canonicalPerrLeftBoundary M ρ lam ε A ω‖) =ᵐ[
          (volume : Measure M.Ω)]
        fun ω =>
          ‖measurableCanonicalPerrLeftBoundary
            M ρ lam ε A ω‖ :=
    heq.mono fun _ω hω => congrArg norm hω
  rw [integral_congr_ae hnorm]
  change
    (∫ ω, ‖H ω + S ω‖
      ∂(volume : Measure M.Ω)) ≤ _
  calc
    (∫ ω, ‖H ω + S ω‖
      ∂(volume : Measure M.Ω)) ≤
        (∫ ω, ‖H ω‖ ∂(volume : Measure M.Ω)) +
          ∫ ω, ‖S ω‖ ∂(volume : Measure M.Ω) :=
      integral_norm_add_le H S hH hS
    _ ≤
        Real.sqrt
            (canonicalPhysicalParametrixOrderL2SecondMomentBudget
              outerConstant powerConstant lam ε A) *
          Real.sqrt
            (canonicalNoiseMultiplicationL2SecondMomentBudget
              ρ lam ε) +
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q),
            Real.sqrt
                (canonicalPhysicalParametrixOrderL2SecondMomentBudget
                  outerConstant powerConstant lam ε r) *
              countertermBudget q :=
      add_le_add hhead htail
    _ =
        canonicalPerrLeftBoundaryFirstMomentBudget
          outerConstant powerConstant ρ lam ε A
          countertermBudget := rfl

/-! ## The concrete one-sided event estimate -/

/-- The one-sided good-event probability with both former boundary
interfaces discharged by the explicit first-moment theorem above. -/
theorem
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_budget
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    (countertermBudget : ℕ → ℝ)
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω)
    (hcounter :
      ∀ q ∈ Finset.Icc 1 (truncOrder ε),
        |renormC2q ρ lam ε q| ≤ countertermBudget q) :
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε (truncOrder ε)
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε (truncOrder ε))
          (canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε)))ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε (truncOrder ε) /
        (ε ^ (-14 : ℤ)) ^ 2 +
      canonicalPerrLeftBoundaryFirstMomentBudget
          outerConstant powerConstant ρ lam ε (truncOrder ε)
          countertermBudget /
        ε ^ 28 := by
  have hint :=
    integrable_canonicalPerrLeftBoundary
      hfubini hwick hdet
      houter hpower hlam hε hεle hagree
  have hfirst :=
    integral_norm_canonicalPerrLeftBoundary_le_budget
      countertermBudget hfubini hwick hdet
      houter hpower hlam hε hεle hagree hcounter
  exact
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_boundary
      hfubini hwick hdet
      houter hpower hlam hε hεle hagree
      hint.norm
      (canonicalPerrLeftBoundaryFirstMomentBudget
        outerConstant powerConstant ρ lam ε (truncOrder ε)
        countertermBudget)
      hfirst

/-- The qualitative P-3.5b inputs in the preceding theorem are
constructive consequences of the mollified-noise model.  Only the
quantitative deterministic moment estimate remains. -/
theorem
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_deterministic
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    (countertermBudget : ℕ → ℝ)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω)
    (hcounter :
      ∀ q ∈ Finset.Icc 1 (truncOrder ε),
        |renormC2q ρ lam ε q| ≤ countertermBudget q) :
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε (truncOrder ε)
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε (truncOrder ε))
          (canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε)))ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε (truncOrder ε) /
        (ε ^ (-14 : ℤ)) ^ 2 +
      canonicalPerrLeftBoundaryFirstMomentBudget
          outerConstant powerConstant ρ lam ε (truncOrder ε)
          countertermBudget /
        ε ^ 28 := by
  exact
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_budget
      countertermBudget
      (fun m _hm _hmA α β =>
        pmCoeffMomentFubiniOutput_of_r324
          M ρ lam hε hεle m α β)
      (fun m _hm _hmA =>
        M.wickAtSecondMomentLaw ρ hε m)
      hdet houter hpower hlam hε hεle hagree hcounter

/-- R-322 supplies the counterterm envelope in the exact form consumed
by the boundary budget, with one constant selected before `q`. -/
theorem
    exists_measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_reductions
    {M : NoiseModel} {ρ : SmoothCutoff}
    {primitiveConstant supportConstant : ℝ}
    {outerConstant powerConstant lam ε : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant)
    (hred :
      ∀ q ∈ Finset.Icc 1 (truncOrder ε),
        RenormReductionOutput
          ρ lam ε q primitiveConstant supportConstant)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω) :
    ∃ Crenorm : ℝ, 0 < Crenorm ∧
      (volume : Measure M.Ω).real
          (canonicalOneSidedL2ParametrixGoodEvent
            M ρ lam ε (truncOrder ε)
            (canonicalGradedTruncatedParametrixL2Factor
              M ρ lam ε (truncOrder ε))
            (canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε)))ᶜ ≤
        canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
            outerConstant powerConstant lam ε (truncOrder ε) /
          (ε ^ (-14 : ℤ)) ^ 2 +
        canonicalPerrLeftBoundaryFirstMomentBudget
            outerConstant powerConstant ρ lam ε (truncOrder ε)
            (fun q =>
              ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
                (Crenorm * lam) ^ (2 * q)) /
          ε ^ 28 := by
  obtain ⟨Crenorm, hCrenorm, hCbound⟩ :=
    exists_renormC_bound_of_reduction
      hprimitive hsupport
  refine ⟨Crenorm, hCrenorm, ?_⟩
  apply
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_deterministic
      (fun q =>
        ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
          (Crenorm * lam) ^ (2 * q))
      hdet houter hpower hlam hε hεle hagree
  intro q hq
  exact
    hCbound ρ lam ε q hlam hε hlog
      (Finset.mem_Icc.mp hq).1 (hred q hq)

/-- Complete event/first-moment assembly from the literal quantitative
R-322 and R-324 outputs.  All qualitative P-3.5b, Wick, boundary
integrability, and abstract first-moment premises have disappeared.
The only P-3.4 input left is `hagree`. -/
theorem
    exists_measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_r322_r324
    {M : NoiseModel} {ρ : SmoothCutoff}
    {renormPrimitive renormSupport momentPrimitive momentSupport : ℝ}
    {lam ε : ℝ}
    (hrenormPrimitive : 0 < renormPrimitive)
    (hrenormSupport : 0 < renormSupport)
    (hmomentPrimitive : 0 < momentPrimitive)
    (hmomentSupport : 0 < momentSupport)
    (hrenorm :
      ∀ q ∈ Finset.Icc 1 (truncOrder ε),
        RenormReductionOutput
          ρ lam ε q renormPrimitive renormSupport)
    (huniform :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        MomentUniformReductionOutputAt
          ρ lam ε m α β momentPrimitive momentSupport)
    (hrouted :
      ∀ outerConstant : ℝ, 0 < outerConstant →
        ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
          RoutedMomentReductionOutput ρ lam ε m α β
            (lamEps lam ε ^ 2 * outerConstant *
              (momentPrimitive * lam) ^ (2 * m - 2)))
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω) :
    ∃ outerConstant Crenorm : ℝ,
      0 < outerConstant ∧ 0 < Crenorm ∧
      (volume : Measure M.Ω).real
          (canonicalOneSidedL2ParametrixGoodEvent
            M ρ lam ε (truncOrder ε)
            (canonicalGradedTruncatedParametrixL2Factor
              M ρ lam ε (truncOrder ε))
            (canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε)))ᶜ ≤
        canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
            outerConstant momentPrimitive lam ε (truncOrder ε) /
          (ε ^ (-14 : ℤ)) ^ 2 +
        canonicalPerrLeftBoundaryFirstMomentBudget
            outerConstant momentPrimitive ρ lam ε (truncOrder ε)
            (fun q =>
              ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
                (Crenorm * lam) ^ (2 * q)) /
          ε ^ 28 := by
  obtain ⟨outerConstant, houter, hdetClose⟩ :=
    exists_deterministicMoment_bound_of_reductions
      hmomentPrimitive hmomentSupport
  have hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant momentPrimitive lam ε m α β := by
    intro m hm hmA α β
    exact
      hdetClose ρ lam ε m α β
        hε hεsmall hlog hm
        (huniform m hm hmA α β)
        (hrouted outerConstant houter m hm hmA α β)
  obtain ⟨Crenorm, hCrenorm, hevent⟩ :=
    exists_measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_of_reductions
      hrenormPrimitive hrenormSupport hrenorm hdet
      houter.le hmomentPrimitive.le hlam hε
      (hεsmall.trans (by norm_num)) hlog hagree
  exact ⟨outerConstant, Crenorm, houter, hCrenorm, hevent⟩

/-- Paper-scale numerical budgets now imply the exact `2 ε²`
exceptional-set estimate without any separate boundary integrability or
first-moment hypotheses. -/
theorem
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq_of_budgets
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    (countertermBudget : ℕ → ℝ)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hphysical :
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε (truncOrder ε) ≤
        ε ^ (-24 : ℤ))
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω)
    (hcounter :
      ∀ q ∈ Finset.Icc 1 (truncOrder ε),
        |renormC2q ρ lam ε q| ≤ countertermBudget q)
    (hboundary :
      canonicalPerrLeftBoundaryFirstMomentBudget
          outerConstant powerConstant ρ lam ε (truncOrder ε)
          countertermBudget ≤
        ε ^ 30) :
    (volume : Measure M.Ω).real
        (canonicalOneSidedL2ParametrixGoodEvent
          M ρ lam ε (truncOrder ε)
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε (truncOrder ε))
          (canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε)))ᶜ ≤
      2 * ε ^ 2 := by
  let hfubini :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β :=
    fun m _hm _hmA α β =>
      pmCoeffMomentFubiniOutput_of_r324
        M ρ lam hε hεle m α β
  let hwick :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε →
        WickAtSecondMomentLaw M ρ ε m :=
    fun m _hm _hmA =>
      M.wickAtSecondMomentLaw ρ hε m
  have hint :=
    integrable_canonicalPerrLeftBoundary
      hfubini hwick hdet
      houter hpower hlam hε hεle hagree
  have hfirst :
      (∫ ω,
          ‖canonicalPerrLeftBoundary
            M ρ lam ε (truncOrder ε) ω‖
        ∂(volume : Measure M.Ω)) ≤ ε ^ 30 :=
    (integral_norm_canonicalPerrLeftBoundary_le_budget
      countertermBudget hfubini hwick hdet
      houter hpower hlam hε hεle hagree hcounter).trans
        hboundary
  exact
    measureReal_compl_canonicalConstructedOneSidedGoodEvent_le_two_mul_sq
      hfubini hwick hdet
      houter hpower hlam hε hεle hphysical hagree
      hint.norm hfirst

end PartialPairing

end

end Anderson4D
