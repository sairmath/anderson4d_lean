import Anderson4D.Parametrix.L2KernelBridge
import Anderson4D.Parametrix.L2ParametrixInverse
import Anderson4D.DetParametrix.Core.MomentReduction
import Anderson4D.Parametrix.MomentBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Paper-scale `L²` good event

This file packages the quantitative last step of paper §3.4, Step 1.
The analytic estimates (3.31)--(3.32) must supply a factorized
parametrix `Q` and its two operator remainders.  On the paper-scale
event

`‖Q‖ ≤ ε⁻¹⁴`, `‖Rleft‖ + ‖Rright‖ ≤ ε²⁸`,

the two-sided algebra from `L2ParametrixInverse.lean` constructs the
inverse of `1 - G M`.  Since `‖G‖ ≤ 1`, its inverse Green operator
differs from `QG` by at most `ε¹²` for sufficiently small positive
`ε`.

The event is kept separate from its probabilistic estimate: the
moment bounds in P-3.5/P-err provide the hypotheses of the Markov
lemmas below.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

/-! ## Fourier matrix coefficients and the `(3.30)` bound -/

/-- The `(3.23)`-signed Fourier matrix coefficient of a bounded operator.
The minus sign on the left mode is the one forced by the paper's
non-conjugated Fourier kernel convention. -/
def torusFourierMatrixCoeff
    (A : TorusL2 →L[ℂ] TorusL2) (α β : Z4) : ℂ :=
  ⟪torusFourierBasis (-α), A (torusFourierBasis β)⟫_ℂ

/-- Parseval in squared-norm form for the torus Hilbert basis. -/
theorem tsum_norm_sq_inner_torusFourierBasis
    (x : TorusL2) :
    (∑' k : Z4, ‖⟪torusFourierBasis k, x⟫_ℂ‖ ^ 2) =
      ‖x‖ ^ 2 := by
  simp_rw [← torusFourierBasis.repr_apply_apply x]
  have h := lp.norm_rpow_eq_tsum
    (by norm_num)
    (torusFourierBasis.repr x)
  norm_num at h
  exact h.symm

/-- Parseval with the left Fourier index written in the paper's
`-α` convention. -/
theorem tsum_norm_sq_torusFourierMatrixCoeff
    (A : TorusL2 →L[ℂ] TorusL2) (β : Z4) :
    (∑' α : Z4, ‖torusFourierMatrixCoeff A α β‖ ^ 2) =
      ‖A (torusFourierBasis β)‖ ^ 2 := by
  unfold torusFourierMatrixCoeff
  calc
    (∑' α : Z4,
        ‖⟪torusFourierBasis (-α),
          A (torusFourierBasis β)⟫_ℂ‖ ^ 2) =
        ∑' α : Z4,
          ‖⟪torusFourierBasis α,
            A (torusFourierBasis β)⟫_ℂ‖ ^ 2 := by
      rw [← (Equiv.neg Z4).tsum_eq]
      simp only [Equiv.neg_apply, neg_neg]
    _ = ‖A (torusFourierBasis β)‖ ^ 2 :=
      tsum_norm_sq_inner_torusFourierBasis _

/-- A bounded operator is controlled by the square-sum of its values on
the torus Fourier basis.  This is the Hilbert-space core of (3.30),
proved directly because no named Hilbert--Schmidt API is required. -/
theorem operatorNormSq_le_tsum_normSq_torusFourierBasis
    (A : TorusL2 →L[ℂ] TorusL2)
    (hsum :
      Summable fun k : Z4 =>
        ‖A (torusFourierBasis k)‖ ^ 2) :
    ‖A‖ ^ 2 ≤
      ∑' k : Z4, ‖A (torusFourierBasis k)‖ ^ 2 := by
  let S : ℝ :=
    ∑' k : Z4, ‖A (torusFourierBasis k)‖ ^ 2
  have hS : 0 ≤ S :=
    tsum_nonneg fun _ => sq_nonneg _
  have hadj_apply :
      ∀ x : TorusL2,
        ‖ContinuousLinearMap.adjoint A x‖ ≤
          Real.sqrt S * ‖x‖ := by
    intro x
    apply (sq_le_sq₀
      (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hS]
    calc
      ‖ContinuousLinearMap.adjoint A x‖ ^ 2 =
          ∑' k : Z4,
            ‖⟪torusFourierBasis k,
              ContinuousLinearMap.adjoint A x⟫_ℂ‖ ^ 2 :=
        (tsum_norm_sq_inner_torusFourierBasis _).symm
      _ = ∑' k : Z4,
            ‖⟪A (torusFourierBasis k), x⟫_ℂ‖ ^ 2 := by
        congr 1
        funext k
        rw [ContinuousLinearMap.adjoint_inner_right]
      _ ≤ ∑' k : Z4,
            ‖A (torusFourierBasis k)‖ ^ 2 * ‖x‖ ^ 2 := by
        have hleft :
            Summable fun k : Z4 =>
              ‖⟪A (torusFourierBasis k), x⟫_ℂ‖ ^ 2 := by
          have hbase :=
            torusFourierBasis.orthonormal.inner_products_summable
              (x := ContinuousLinearMap.adjoint A x)
          apply hbase.congr
          intro k
          rw [ContinuousLinearMap.adjoint_inner_right]
        apply hleft.tsum_le_tsum
        · intro k
          have hinner :
              ‖⟪A (torusFourierBasis k), x⟫_ℂ‖ ≤
                ‖A (torusFourierBasis k)‖ * ‖x‖ :=
            norm_inner_le_norm _ _
          simpa only [mul_pow] using
            pow_le_pow_left₀
              (norm_nonneg
                ⟪A (torusFourierBasis k), x⟫_ℂ)
              hinner 2
        · exact hsum.mul_right _
      _ = S * ‖x‖ ^ 2 := by
        rw [← tsum_mul_right]
  have hadj :
      ‖ContinuousLinearMap.adjoint A‖ ≤ Real.sqrt S :=
    ContinuousLinearMap.opNorm_le_bound
      (ContinuousLinearMap.adjoint A)
      (Real.sqrt_nonneg _) hadj_apply
  have hA : ‖A‖ ≤ Real.sqrt S := by
    rw [← ContinuousLinearMap.adjoint.norm_map A]
    exact hadj
  have hsquare :
      ‖A‖ ^ 2 ≤ (Real.sqrt S) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hA
  rw [Real.sq_sqrt hS] at hsquare
  simpa only [S] using hsquare

/-- Direct Fourier double-sum form of the unweighted part of paper
(3.30). -/
theorem operatorNormSq_le_tsum_tsum_fourierMatrixCoeff
    (A : TorusL2 →L[ℂ] TorusL2)
    (hsum :
      Summable fun β : Z4 =>
        ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2) :
    ‖A‖ ^ 2 ≤
      ∑' β : Z4, ∑' α : Z4,
        ‖torusFourierMatrixCoeff A α β‖ ^ 2 := by
  have hnorm :
      Summable fun β : Z4 =>
        ‖A (torusFourierBasis β)‖ ^ 2 := by
    apply hsum.congr
    intro β
    exact tsum_norm_sq_torusFourierMatrixCoeff A β
  calc
    ‖A‖ ^ 2 ≤
        ∑' β : Z4, ‖A (torusFourierBasis β)‖ ^ 2 :=
      operatorNormSq_le_tsum_normSq_torusFourierBasis A hnorm
    _ = ∑' β : Z4, ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 := by
      apply tsum_congr
      intro β
      exact (tsum_norm_sq_torusFourierMatrixCoeff A β).symm

/-- Weighted Fourier double-sum form of (3.30).  Any nonnegative weight
bounded below by one may be used; the paper later instantiates this with
`ε⁻⁸ ⟨ε²(α+β)⟩⁶`.  The two summability hypotheses are the honest
non-junk conditions for the nested real `tsum`. -/
theorem operatorNormSq_le_weighted_fourierMatrixCoeff
    (A : TorusL2 →L[ℂ] TorusL2)
    (weight : Z4 → Z4 → ℝ)
    (hweight : ∀ α β, 1 ≤ weight α β)
    (hinner :
      ∀ β : Z4,
        Summable fun α : Z4 =>
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
            weight α β)
    (houter :
      Summable fun β : Z4 =>
        ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
            weight α β) :
    ‖A‖ ^ 2 ≤
      ∑' β : Z4, ∑' α : Z4,
        ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
          weight α β := by
  have hinner_plain :
      ∀ β : Z4,
        Summable fun α : Z4 =>
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 := by
    intro β
    exact (hinner β).of_nonneg_of_le
      (fun _ => sq_nonneg _)
      (fun α =>
        le_mul_of_one_le_right
          (sq_nonneg ‖torusFourierMatrixCoeff A α β‖)
          (hweight α β))
  have hrow :
      ∀ β : Z4,
        (∑' α : Z4,
            ‖torusFourierMatrixCoeff A α β‖ ^ 2) ≤
          ∑' α : Z4,
            ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
              weight α β := by
    intro β
    apply (hinner_plain β).tsum_le_tsum
    · intro α
      exact le_mul_of_one_le_right
        (sq_nonneg ‖torusFourierMatrixCoeff A α β‖)
        (hweight α β)
    · exact hinner β
  have houter_plain :
      Summable fun β : Z4 =>
        ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 :=
    houter.of_nonneg_of_le
      (fun _ => tsum_nonneg fun _ => sq_nonneg _)
      hrow
  exact
    (operatorNormSq_le_tsum_tsum_fourierMatrixCoeff
      A houter_plain).trans
      (houter_plain.tsum_le_tsum hrow houter)

/-- The exact weight printed in paper (3.30):
`ε⁻⁸ ⟨ε²(α+β)⟩⁶`.  The Japanese bracket is expanded as
`⟨t⟩⁶ = (1 + ‖t‖²)³`, avoiding fractional powers. -/
def paperL2FourierWeight
    (ε : ℝ) (α β : Z4) : ℝ :=
  ε⁻¹ ^ (8 : ℕ) *
    (1 +
      (ε ^ 2 *
        ‖z4EuclideanFrequency (α + β)‖) ^ 2) ^ 3

theorem paperL2FourierWeight_nonneg
    (ε : ℝ) (α β : Z4) :
    0 ≤ paperL2FourierWeight ε α β := by
  unfold paperL2FourierWeight
  positivity

theorem one_le_paperL2FourierWeight
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (α β : Z4) :
    1 ≤ paperL2FourierWeight ε α β := by
  have hinv : 1 ≤ ε⁻¹ :=
    (one_le_inv₀ hε).2 hεle
  have hfirst : 1 ≤ ε⁻¹ ^ (8 : ℕ) :=
    one_le_pow₀ hinv
  have hbase :
      1 ≤ 1 +
        (ε ^ 2 *
          ‖z4EuclideanFrequency (α + β)‖) ^ 2 := by
    nlinarith [sq_nonneg
      (ε ^ 2 *
        ‖z4EuclideanFrequency (α + β)‖)]
  have hsecond :
      1 ≤
        (1 +
          (ε ^ 2 *
            ‖z4EuclideanFrequency (α + β)‖) ^ 2) ^ 3 :=
    one_le_pow₀ hbase
  unfold paperL2FourierWeight
  exact one_le_mul_of_one_le_of_one_le hfirst hsecond

/-- Exact paper-weight specialization of (3.30). -/
theorem operatorNormSq_le_paperL2FourierWeight
    (A : TorusL2 →L[ℂ] TorusL2)
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hinner :
      ∀ β : Z4,
        Summable fun α : Z4 =>
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
            paperL2FourierWeight ε α β)
    (houter :
      Summable fun β : Z4 =>
        ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
            paperL2FourierWeight ε α β) :
    ‖A‖ ^ 2 ≤
      ∑' β : Z4, ∑' α : Z4,
        ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
          paperL2FourierWeight ε α β :=
  operatorNormSq_le_weighted_fourierMatrixCoeff
    A (paperL2FourierWeight ε)
    (one_le_paperL2FourierWeight hε hεle)
    hinner houter

/-- Product-index version of the exact paper-weight bound.  This is the
convenient form for Tonelli: one summability hypothesis replaces the
two nested non-junk hypotheses. -/
theorem operatorNormSq_le_paperL2FourierWeight_prod
    (A : TorusL2 →L[ℂ] TorusL2)
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hsum :
      Summable fun p : Z4 × Z4 =>
        ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2 *
          paperL2FourierWeight ε p.2 p.1) :
    ‖A‖ ^ 2 ≤
      ∑' p : Z4 × Z4,
        ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2 *
          paperL2FourierWeight ε p.2 p.1 := by
  have hinner :
      ∀ β : Z4,
        Summable fun α : Z4 =>
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
            paperL2FourierWeight ε α β :=
    hsum.prod_factor
  have houter :
      Summable fun β : Z4 =>
        ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
            paperL2FourierWeight ε α β :=
    hsum.prod
  calc
    ‖A‖ ^ 2 ≤
        ∑' β : Z4, ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 *
            paperL2FourierWeight ε α β :=
      operatorNormSq_le_paperL2FourierWeight
        A hε hεle hinner houter
    _ = ∑' p : Z4 × Z4,
          ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2 *
            paperL2FourierWeight ε p.2 p.1 :=
      hsum.tsum_prod.symm

/-- Tonelli form of the expected `(3.30)` estimate.  It needs only
termwise measurability and almost-everywhere summability; no integrability
of the full random double sum is assumed in advance. -/
theorem lintegral_operatorNormSq_le_paperL2FourierWeight
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (A : Ω → TorusL2 →L[ℂ] TorusL2)
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hmeas :
      ∀ p : Z4 × Z4,
        AEMeasurable
          (fun ω =>
            ENNReal.ofReal
              (‖torusFourierMatrixCoeff (A ω) p.2 p.1‖ ^ 2 *
                paperL2FourierWeight ε p.2 p.1))
          μ)
    (hsum :
      ∀ᵐ ω ∂μ,
        Summable fun p : Z4 × Z4 =>
          ‖torusFourierMatrixCoeff (A ω) p.2 p.1‖ ^ 2 *
            paperL2FourierWeight ε p.2 p.1) :
    (∫⁻ ω,
        ENNReal.ofReal (‖A ω‖ ^ 2) ∂μ) ≤
      ∑' p : Z4 × Z4,
        ∫⁻ ω,
          ENNReal.ofReal
            (‖torusFourierMatrixCoeff (A ω) p.2 p.1‖ ^ 2 *
              paperL2FourierWeight ε p.2 p.1)
          ∂μ := by
  calc
    (∫⁻ ω, ENNReal.ofReal (‖A ω‖ ^ 2) ∂μ) ≤
        ∫⁻ ω, ∑' p : Z4 × Z4,
          ENNReal.ofReal
            (‖torusFourierMatrixCoeff (A ω) p.2 p.1‖ ^ 2 *
              paperL2FourierWeight ε p.2 p.1)
          ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hsum] with ω hω
      have hop :=
        operatorNormSq_le_paperL2FourierWeight_prod
          (A ω) hε hεle hω
      calc
        ENNReal.ofReal (‖A ω‖ ^ 2) ≤
            ENNReal.ofReal
              (∑' p : Z4 × Z4,
                ‖torusFourierMatrixCoeff
                    (A ω) p.2 p.1‖ ^ 2 *
                  paperL2FourierWeight ε p.2 p.1) :=
          ENNReal.ofReal_le_ofReal hop
        _ = ∑' p : Z4 × Z4,
              ENNReal.ofReal
                (‖torusFourierMatrixCoeff
                    (A ω) p.2 p.1‖ ^ 2 *
                  paperL2FourierWeight ε p.2 p.1) :=
          ENNReal.ofReal_tsum_of_nonneg
            (fun p =>
              mul_nonneg
                (sq_nonneg _)
                (zero_le_one.trans
                  (one_le_paperL2FourierWeight
                    hε hεle p.2 p.1)))
            hω
    _ = _ := lintegral_tsum hmeas

/-- Numerical closure of the Tonelli estimate from termwise weighted
second-moment bounds.  This is the exact adapter between P-3.5b and
P-L2: all probability is confined to `hterm`, while the remaining
obligation is a deterministic summable majorant. -/
theorem lintegral_operatorNormSq_le_of_weightedMomentBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (A : Ω → TorusL2 →L[ℂ] TorusL2)
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (bound : Z4 × Z4 → ℝ)
    (hbound_nonneg : ∀ p, 0 ≤ bound p)
    (hbound_sum : Summable bound)
    (hmeas :
      ∀ p : Z4 × Z4,
        AEMeasurable
          (fun ω =>
            ENNReal.ofReal
              (‖torusFourierMatrixCoeff (A ω) p.2 p.1‖ ^ 2 *
                paperL2FourierWeight ε p.2 p.1))
          μ)
    (hsum :
      ∀ᵐ ω ∂μ,
        Summable fun p : Z4 × Z4 =>
          ‖torusFourierMatrixCoeff (A ω) p.2 p.1‖ ^ 2 *
            paperL2FourierWeight ε p.2 p.1)
    (hterm :
      ∀ p : Z4 × Z4,
        (∫⁻ ω,
            ENNReal.ofReal
              (‖torusFourierMatrixCoeff
                  (A ω) p.2 p.1‖ ^ 2 *
                paperL2FourierWeight ε p.2 p.1)
            ∂μ) ≤
          ENNReal.ofReal (bound p)) :
    (∫⁻ ω,
        ENNReal.ofReal (‖A ω‖ ^ 2) ∂μ) ≤
      ENNReal.ofReal (∑' p : Z4 × Z4, bound p) := by
  calc
    (∫⁻ ω, ENNReal.ofReal (‖A ω‖ ^ 2) ∂μ) ≤
        ∑' p : Z4 × Z4,
          ∫⁻ ω,
            ENNReal.ofReal
              (‖torusFourierMatrixCoeff
                  (A ω) p.2 p.1‖ ^ 2 *
                paperL2FourierWeight ε p.2 p.1)
            ∂μ :=
      lintegral_operatorNormSq_le_paperL2FourierWeight
        μ A hε hεle hmeas hsum
    _ ≤ ∑' p : Z4 × Z4,
          ENNReal.ofReal (bound p) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal
          (∑' p : Z4 × Z4, bound p) :=
      (ENNReal.ofReal_tsum_of_nonneg
        hbound_nonneg hbound_sum).symm

/-- Turn an ordinary second-moment bound into the weighted `lintegral`
bound consumed by `lintegral_operatorNormSq_le_of_weightedMomentBound`.
The scalar `c` records normalization changes such as the paper-volume
factor in the kernel/operator ledger. -/
theorem lintegral_ofReal_norm_sq_const_mul_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (f : Ω → ℂ) (hf : MemLp f 2 μ)
    (c : ℂ) {w B : ℝ}
    (hw : 0 ≤ w)
    (hB : (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ B) :
    (∫⁻ ω,
        ENNReal.ofReal (‖c * f ω‖ ^ 2 * w) ∂μ) ≤
      ENNReal.ofReal (‖c‖ ^ 2 * B * w) := by
  have hint :
      Integrable (fun ω => ‖f ω‖ ^ 2) μ :=
    hf.integrable_norm_pow (by norm_num)
  let s : ℝ := ‖c‖ ^ 2 * w
  have hs : 0 ≤ s :=
    mul_nonneg (sq_nonneg _) hw
  have heq :
      (fun ω => ‖c * f ω‖ ^ 2 * w) =
        fun ω => s * ‖f ω‖ ^ 2 := by
    funext ω
    simp only [norm_mul, s]
    ring
  have heqpoint (ω : Ω) :
      ‖c * f ω‖ ^ 2 * w = s * ‖f ω‖ ^ 2 :=
    congrFun heq ω
  simp_rw [heqpoint]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hint.const_mul s)
    (ae_of_all μ fun ω =>
      mul_nonneg hs (sq_nonneg ‖f ω‖))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  calc
    s * (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ s * B :=
      mul_le_mul_of_nonneg_left hB hs
    _ = ‖c‖ ^ 2 * B * w := by
      unfold s
      ring

/-! ## The concrete orderwise P-3.5b to P-L2 bridge -/

/-- An order-`m` bounded random operator realizes the physical random
kernel `P_m` when its Fourier matrix coefficients equal the paper
coefficients almost surely, including the inverse torus-volume
normalization forced by the use of probability Haar measure in
`TorusL2`.

Almost-sure equality is essential here: the noise model specifies
random variables only up to null sets, and P-3.5b yields simultaneous
square summability only almost surely.  Requiring the equality at every
sample would add a non-probabilistic regularity hypothesis not present
in the paper. -/
def ParametrixOrderL2CoeffRealization
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (m : ℕ)
    (A : M.Ω → TorusL2 →L[ℂ] TorusL2) : Prop :=
  ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ α β,
      torusFourierMatrixCoeff (A ω) α β =
        (paperTorusVolume : ℂ)⁻¹ *
          pmCoeff M ρ lam ε m α β ω

/-- Deterministic weighted moment majorant after translating the
paper-normalized coefficient to the probability-Haar operator
coefficient. -/
def parametrixOrderL2WeightedMomentRHS
    (outerConstant powerConstant lam ε : ℝ)
    (m : ℕ) (α β : Z4) : ℝ :=
  ‖(paperTorusVolume : ℂ)⁻¹‖ ^ 2 *
    deterministicMomentRHS
      outerConstant powerConstant lam ε m α β *
    paperL2FourierWeight ε α β

theorem parametrixOrderL2WeightedMomentRHS_nonneg
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ} {α β : Z4}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    0 ≤ parametrixOrderL2WeightedMomentRHS
      outerConstant powerConstant lam ε m α β := by
  unfold parametrixOrderL2WeightedMomentRHS
  exact mul_nonneg
    (mul_nonneg
      (sq_nonneg _)
      (deterministicMomentRHS_nonneg
        houter hpower hlam))
    (paperL2FourierWeight_nonneg ε α β)

/-- P-3.5b gives both measurability and the weighted term estimate
needed by the Tonelli form of (3.30), with every normalization factor
visible. -/
theorem parametrixOrder_weightedCoeff_measurable_and_bound
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ} {α β : Z4}
    (A : M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hreal :
      ParametrixOrderL2CoeffRealization
        M ρ lam ε m A)
    (hfubini :
      PmCoeffMomentFubiniOutput
        M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ‖deterministicMomentPairingSum
          ρ lam ε m α β‖ ≤
        deterministicMomentRHS
          outerConstant powerConstant lam ε m α β)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    AEMeasurable
        (fun ω =>
          ENNReal.ofReal
            (‖torusFourierMatrixCoeff
                (A ω) α β‖ ^ 2 *
              paperL2FourierWeight ε α β))
        (volume : Measure M.Ω) ∧
      (∫⁻ ω,
          ENNReal.ofReal
            (‖torusFourierMatrixCoeff
                (A ω) α β‖ ^ 2 *
              paperL2FourierWeight ε α β)
          ∂(volume : Measure M.Ω)) ≤
        ENNReal.ofReal
          (parametrixOrderL2WeightedMomentRHS
            outerConstant powerConstant lam ε m α β) := by
  have hpm :=
    parametrix_coeff_bound hfubini hwick hdet
  let c : ℂ := (paperTorusVolume : ℂ)⁻¹
  have hscaled :
      MemLp
        (fun ω =>
          c * pmCoeff M ρ lam ε m α β ω)
        2 (volume : Measure M.Ω) :=
    hpm.1.const_mul c
  have hbase :
      AEMeasurable
        (fun ω =>
          ENNReal.ofReal
            (‖c * pmCoeff M ρ lam ε m α β ω‖ ^ 2 *
              paperL2FourierWeight ε α β))
        (volume : Measure M.Ω) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hscaled.aestronglyMeasurable.norm.aemeasurable.pow_const 2).mul_const _)
  have hrealαβ :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        torusFourierMatrixCoeff (A ω) α β =
          c * pmCoeff M ρ lam ε m α β ω :=
    hreal.mono fun ω hω => hω α β
  constructor
  · apply hbase.congr
    filter_upwards [hrealαβ] with ω hω
    rw [hω]
  · calc
      (∫⁻ ω,
          ENNReal.ofReal
            (‖torusFourierMatrixCoeff
                (A ω) α β‖ ^ 2 *
              paperL2FourierWeight ε α β)
          ∂(volume : Measure M.Ω)) =
          ∫⁻ ω,
            ENNReal.ofReal
              (‖c * pmCoeff
                  M ρ lam ε m α β ω‖ ^ 2 *
                paperL2FourierWeight ε α β)
            ∂(volume : Measure M.Ω) := by
        apply lintegral_congr_ae
        filter_upwards [hrealαβ] with ω hω
        rw [hω]
      _ ≤ ENNReal.ofReal
          (‖c‖ ^ 2 *
            deterministicMomentRHS
              outerConstant powerConstant lam ε m α β *
            paperL2FourierWeight ε α β) :=
        lintegral_ofReal_norm_sq_const_mul_le
          (volume : Measure M.Ω)
          (pmCoeff M ρ lam ε m α β)
          hpm.1 c
          (zero_le_one.trans
            (one_le_paperL2FourierWeight
              hε hεle α β))
          hpm.2
      _ = ENNReal.ofReal
          (parametrixOrderL2WeightedMomentRHS
            outerConstant powerConstant lam ε m α β) := by
        rfl

/-- Orderwise P-3.5b to P-L2 closure.  After the deterministic weighted
majorant is summable and the realized coefficient square-sum is
non-junk almost surely, the expected `L² → L²` norm is bounded by the
sum of the explicit `(3.24) × (3.30)` majorant. -/
theorem lintegral_parametrixOrder_normSq_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (A : M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hreal :
      ParametrixOrderL2CoeffRealization
        M ρ lam ε m A)
    (hfubini :
      ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hmajorant :
      Summable fun p : Z4 × Z4 =>
        parametrixOrderL2WeightedMomentRHS
          outerConstant powerConstant lam ε m p.2 p.1)
    (hsum :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        Summable fun p : Z4 × Z4 =>
          ‖torusFourierMatrixCoeff
              (A ω) p.2 p.1‖ ^ 2 *
            paperL2FourierWeight ε p.2 p.1) :
    (∫⁻ ω,
        ENNReal.ofReal (‖A ω‖ ^ 2)
        ∂(volume : Measure M.Ω)) ≤
      ENNReal.ofReal
        (∑' p : Z4 × Z4,
          parametrixOrderL2WeightedMomentRHS
            outerConstant powerConstant lam ε m p.2 p.1) := by
  have hcoeff (p : Z4 × Z4) :=
    parametrixOrder_weightedCoeff_measurable_and_bound
      A hreal (hfubini p.2 p.1) hwick
        (hdet p.2 p.1) hε hεle
  exact lintegral_operatorNormSq_le_of_weightedMomentBound
    (volume : Measure M.Ω) A hε hεle
    (fun p =>
      parametrixOrderL2WeightedMomentRHS
        outerConstant powerConstant lam ε m p.2 p.1)
    (fun p =>
      parametrixOrderL2WeightedMomentRHS_nonneg
        houter hpower hlam)
    hmajorant
    (fun p => (hcoeff p).1)
    hsum
    (fun p => (hcoeff p).2)

/-- Real-valued expectation form of the preceding theorem. -/
theorem integral_parametrixOrder_normSq_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (A : M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hreal :
      ParametrixOrderL2CoeffRealization
        M ρ lam ε m A)
    (hfubini :
      ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick : WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hmajorant :
      Summable fun p : Z4 × Z4 =>
        parametrixOrderL2WeightedMomentRHS
          outerConstant powerConstant lam ε m p.2 p.1)
    (hsum :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        Summable fun p : Z4 × Z4 =>
          ‖torusFourierMatrixCoeff
              (A ω) p.2 p.1‖ ^ 2 *
            paperL2FourierWeight ε p.2 p.1)
    (hintA :
      Integrable (fun ω => ‖A ω‖ ^ 2)
        (volume : Measure M.Ω)) :
    (∫ ω, ‖A ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
      ∑' p : Z4 × Z4,
        parametrixOrderL2WeightedMomentRHS
          outerConstant powerConstant lam ε m p.2 p.1 := by
  apply (ENNReal.ofReal_le_ofReal_iff
    (tsum_nonneg fun p =>
      parametrixOrderL2WeightedMomentRHS_nonneg
        houter hpower hlam)).mp
  rw [ofReal_integral_eq_lintegral_ofReal
    hintA (ae_of_all _ fun _ => sq_nonneg _)]
  exact lintegral_parametrixOrder_normSq_le
    A hreal hfubini hwick hdet
    houter hpower hlam hε hεle
    hmajorant hsum

/-- Expectation adapter for (3.30).  Once both nonnegative sides are
integrable, the pointwise Fourier double-sum bound passes directly to
expectation. -/
theorem integral_operatorNormSq_le_paperL2FourierWeight
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (A : Ω → TorusL2 →L[ℂ] TorusL2)
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hinner :
      ∀ ω β,
        Summable fun α : Z4 =>
          ‖torusFourierMatrixCoeff (A ω) α β‖ ^ 2 *
            paperL2FourierWeight ε α β)
    (houter :
      ∀ ω,
        Summable fun β : Z4 =>
          ∑' α : Z4,
            ‖torusFourierMatrixCoeff (A ω) α β‖ ^ 2 *
              paperL2FourierWeight ε α β)
    (hintA :
      Integrable (fun ω => ‖A ω‖ ^ 2) μ)
    (hintCoeff :
      Integrable
        (fun ω =>
          ∑' β : Z4, ∑' α : Z4,
            ‖torusFourierMatrixCoeff (A ω) α β‖ ^ 2 *
              paperL2FourierWeight ε α β)
        μ) :
    (∫ ω, ‖A ω‖ ^ 2 ∂μ) ≤
      ∫ ω, ∑' β : Z4, ∑' α : Z4,
        ‖torusFourierMatrixCoeff (A ω) α β‖ ^ 2 *
          paperL2FourierWeight ε α β ∂μ := by
  apply integral_mono hintA hintCoeff
  intro ω
  exact operatorNormSq_le_paperL2FourierWeight
    (A ω) hε hεle (hinner ω) (houter ω)

/-- The precise norm thresholds used after (3.32).  In the factorized
bounded-operator realization, `Q * greenL2Op` is the paper
parametrix. -/
def paperScaleParametrixGoodEvent
    {Ω : Type*}
    (Q Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (ε : ℝ) : Set Ω :=
  {ω |
    ‖Q ω‖ ≤ ε ^ (-14 : ℤ) ∧
      ‖Rleft ω‖ + ‖Rright ω‖ ≤ ε ^ 28}

/-- The paper-scale remainder threshold implies the half-ball event
used by the Banach-algebra inversion theorem. -/
theorem paperScaleParametrixGoodEvent_subset_twoSided
    {Ω : Type*}
    (Q Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (ε : ℝ) (hεpow : ε ^ 28 < 1 / 2) :
    paperScaleParametrixGoodEvent Q Rleft Rright ε ⊆
      twoSidedParametrixGoodEvent Rleft Rright := by
  intro ω hω
  constructor
  · exact
      (le_add_of_nonneg_right (norm_nonneg (Rright ω))).trans_lt
        (hω.2.trans_lt hεpow)
  · exact
      (le_add_of_nonneg_left (norm_nonneg (Rleft ω))).trans_lt
        (hω.2.trans_lt hεpow)

/-- Membership in the paper-scale event constructs the factorized
Anderson inverse. -/
theorem lopInvertible_on_paperScaleParametrixGoodEvent
    {Ω : Type*}
    (M Q Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (ε : ℝ)
    (hdata : ∀ ω,
      AndersonParametrixData
        greenL2Op (M ω) (Q ω) (Rleft ω) (Rright ω))
    (hεpow : ε ^ 28 < 1 / 2)
    {ω : Ω}
    (hω : ω ∈
      paperScaleParametrixGoodEvent Q Rleft Rright ε) :
    LopInvertible greenL2Op (M ω) := by
  exact lopInvertible_on_twoSidedParametrixGoodEvent
    (fun _ => greenL2Op) M Q Rleft Rright hdata
      (paperScaleParametrixGoodEvent_subset_twoSided
        Q Rleft Rright ε hεpow hω)

/-- Quantitative form of (3.33) for the factorized bounded-operator
realization. -/
theorem norm_inverseGreen_sub_parametrix_on_paperScaleGoodEvent
    {Ω : Type*}
    (M Q Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (ε : ℝ)
    (hdata : ∀ ω,
      AndersonParametrixData
        greenL2Op (M ω) (Q ω) (Rleft ω) (Rright ω))
    (hεpos : 0 < ε)
    (hεsmall : 2 * ε ^ 2 ≤ 1)
    (hεpow : ε ^ 28 < 1 / 2)
    {ω : Ω}
    (hω : ω ∈
      paperScaleParametrixGoodEvent Q Rleft Rright ε) :
    ‖inverseGreen greenL2Op (M ω)
        (lopInvertible_on_paperScaleParametrixGoodEvent
          M Q Rleft Rright ε hdata hεpow hω) -
      Q ω * greenL2Op‖ ≤ ε ^ 12 := by
  letI : Nontrivial TorusL2 :=
    nontrivial_of_ne (torusFourierBasis (0 : Z4)) 0
      (torusFourierBasis.orthonormal.ne_zero 0)
  let htwo :
      ω ∈ twoSidedParametrixGoodEvent Rleft Rright :=
    paperScaleParametrixGoodEvent_subset_twoSided
      Q Rleft Rright ε hεpow hω
  have hproof :
      lopInvertible_on_paperScaleParametrixGoodEvent
          M Q Rleft Rright ε hdata hεpow hω =
        lopInvertible_on_twoSidedParametrixGoodEvent
          (fun _ => greenL2Op) M Q Rleft Rright hdata htwo :=
    Subsingleton.elim _ _
  rw [hproof]
  calc
    ‖inverseGreen greenL2Op (M ω)
          (lopInvertible_on_twoSidedParametrixGoodEvent
            (fun _ => greenL2Op) M Q Rleft Rright hdata htwo) -
        Q ω * greenL2Op‖ ≤
        2 * ‖Q ω‖ * ‖Rright ω‖ * ‖greenL2Op‖ :=
      norm_inverseGreen_sub_parametrix_mul_on_goodEvent
        (fun _ => greenL2Op) M Q Rleft Rright hdata htwo
    _ ≤ 2 * (ε ^ (-14 : ℤ)) * (ε ^ 28) * 1 := by
      gcongr
      · exact hω.1
      · exact
          (le_add_of_nonneg_left
            (norm_nonneg (Rleft ω))).trans hω.2
      · exact norm_greenL2Op_le_one
    _ = 2 * ε ^ 14 := by
      field_simp [ne_of_gt hεpos]
    _ = (2 * ε ^ 2) * ε ^ 12 := by ring
    _ ≤ 1 * ε ^ 12 :=
      mul_le_mul_of_nonneg_right hεsmall
        (pow_nonneg hεpos.le 12)
    _ = ε ^ 12 := one_mul _

/-- The elementary small-`ε` hypotheses needed by the preceding
theorem follow from the convenient range `0 < ε ≤ 1/2`. -/
theorem norm_inverseGreen_sub_parametrix_on_paperScaleGoodEvent_of_half
    {Ω : Type*}
    (M Q Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (ε : ℝ)
    (hdata : ∀ ω,
      AndersonParametrixData
        greenL2Op (M ω) (Q ω) (Rleft ω) (Rright ω))
    (hεpos : 0 < ε)
    (hεle : ε ≤ 1 / 2)
    {ω : Ω}
    (hω : ω ∈
      paperScaleParametrixGoodEvent Q Rleft Rright ε) :
    ‖inverseGreen greenL2Op (M ω)
        (lopInvertible_on_paperScaleParametrixGoodEvent
          M Q Rleft Rright ε hdata
            (by
              calc
                ε ^ 28 ≤ (1 / 2 : ℝ) ^ 28 :=
                  pow_le_pow_left₀ hεpos.le hεle 28
                _ < 1 / 2 := by norm_num)
          hω) -
      Q ω * greenL2Op‖ ≤ ε ^ 12 := by
  have hεsmall : 2 * ε ^ 2 ≤ 1 := by
    have hsquare :
        ε ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hεpos.le hεle 2
    norm_num at hsquare ⊢
    linarith
  have hεpow : ε ^ 28 < 1 / 2 := by
    calc
      ε ^ 28 ≤ (1 / 2 : ℝ) ^ 28 :=
        pow_le_pow_left₀ hεpos.le hεle 28
      _ < 1 / 2 := by norm_num
  have hproof :
      lopInvertible_on_paperScaleParametrixGoodEvent
          M Q Rleft Rright ε hdata
            (by
              calc
                ε ^ 28 ≤ (1 / 2 : ℝ) ^ 28 :=
                  pow_le_pow_left₀ hεpos.le hεle 28
                _ < 1 / 2 := by norm_num)
          hω =
        lopInvertible_on_paperScaleParametrixGoodEvent
          M Q Rleft Rright ε hdata hεpow hω :=
    Subsingleton.elim _ _
  rw [hproof]
  exact norm_inverseGreen_sub_parametrix_on_paperScaleGoodEvent
    M Q Rleft Rright ε hdata hεpos hεsmall hεpow hω

/-! ## First-moment control of the event -/

/-- A thresholded first moment bounds the real measure of the
corresponding norm-bad event. -/
theorem measureReal_norm_ge_le_div_firstMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (F : Ω → TorusL2 →L[ℂ] TorusL2)
    (r δ : ℝ) (hr : 0 < r)
    (hint : Integrable (fun ω => ‖F ω‖) μ)
    (hfirst : (∫ ω, ‖F ω‖ ∂μ) ≤ δ) :
    μ.real {ω | r ≤ ‖F ω‖} ≤ δ / r := by
  have hmark :=
    mul_measureReal_operatorBadEvent_le μ F r hint
  rw [operatorBadEvent] at hmark
  rw [le_div_iff₀ hr]
  simpa [mul_comm] using hmark.trans hfirst

/-- Markov and the union bound control failure of the two paper-scale
thresholds.  The remainder sum is treated as one nonnegative random
variable, exactly as in (3.32). -/
theorem measureReal_compl_paperScaleParametrixGoodEvent_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (Q Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (ε δQ δR : ℝ)
    (hεpos : 0 < ε)
    (hintQ : Integrable (fun ω => ‖Q ω‖) μ)
    (hintR :
      Integrable (fun ω => ‖Rleft ω‖ + ‖Rright ω‖) μ)
    (hfirstQ : (∫ ω, ‖Q ω‖ ∂μ) ≤ δQ)
    (hfirstR :
      (∫ ω, ‖Rleft ω‖ + ‖Rright ω‖ ∂μ) ≤ δR) :
    μ.real
        (paperScaleParametrixGoodEvent
          Q Rleft Rright ε)ᶜ ≤
      δQ / (ε ^ (-14 : ℤ)) + δR / (ε ^ 28) := by
  have hqpos : 0 < ε ^ (-14 : ℤ) := zpow_pos hεpos _
  have hrpos : 0 < ε ^ 28 := pow_pos hεpos _
  have hQ :
      μ.real {ω | ε ^ (-14 : ℤ) ≤ ‖Q ω‖} ≤
        δQ / (ε ^ (-14 : ℤ)) :=
    measureReal_norm_ge_le_div_firstMoment
      μ Q _ δQ hqpos hintQ hfirstQ
  have hR :
      μ.real
          {ω | ε ^ 28 ≤
            ‖Rleft ω‖ + ‖Rright ω‖} ≤
        δR / (ε ^ 28) := by
    have hmark :=
      mul_meas_ge_le_integral_of_nonneg
        (μ := μ)
        (f := fun ω => ‖Rleft ω‖ + ‖Rright ω‖)
        (ae_of_all μ fun ω =>
          add_nonneg (norm_nonneg _) (norm_nonneg _))
        hintR (ε ^ 28)
    rw [le_div_iff₀ hrpos]
    simpa [mul_comm] using hmark.trans hfirstR
  have hsubset :
      (paperScaleParametrixGoodEvent
        Q Rleft Rright ε)ᶜ ⊆
        {ω | ε ^ (-14 : ℤ) ≤ ‖Q ω‖} ∪
          {ω | ε ^ 28 ≤
            ‖Rleft ω‖ + ‖Rright ω‖} := by
    intro ω
    change
      ¬ (‖Q ω‖ ≤ ε ^ (-14 : ℤ) ∧
        ‖Rleft ω‖ + ‖Rright ω‖ ≤ ε ^ 28) →
        ε ^ (-14 : ℤ) ≤ ‖Q ω‖ ∨
          ε ^ 28 ≤ ‖Rleft ω‖ + ‖Rright ω‖
    intro h
    by_cases hq : ‖Q ω‖ ≤ ε ^ (-14 : ℤ)
    · exact Or.inr (le_of_not_ge fun hr => h ⟨hq, hr⟩)
    · exact Or.inl (le_of_not_ge hq)
  exact
    (measureReal_mono hsubset).trans
      ((measureReal_union_le _ _).trans (add_le_add hQ hR))

/-- Substituting the two estimates in (3.32) gives the advertised
`O(ε²)` exceptional-event probability, with the explicit union-bound
constant `2`. -/
theorem measureReal_compl_paperScaleParametrixGoodEvent_le_two_mul_sq
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (Q Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (ε : ℝ)
    (hεpos : 0 < ε)
    (hintQ : Integrable (fun ω => ‖Q ω‖) μ)
    (hintR :
      Integrable (fun ω => ‖Rleft ω‖ + ‖Rright ω‖) μ)
    (hfirstQ :
      (∫ ω, ‖Q ω‖ ∂μ) ≤ ε ^ (-12 : ℤ))
    (hfirstR :
      (∫ ω, ‖Rleft ω‖ + ‖Rright ω‖ ∂μ) ≤ ε ^ 30) :
    μ.real
        (paperScaleParametrixGoodEvent
          Q Rleft Rright ε)ᶜ ≤
      2 * ε ^ 2 := by
  calc
    μ.real
        (paperScaleParametrixGoodEvent
          Q Rleft Rright ε)ᶜ ≤
        ε ^ (-12 : ℤ) / ε ^ (-14 : ℤ) +
          ε ^ 30 / ε ^ 28 :=
      measureReal_compl_paperScaleParametrixGoodEvent_le
        μ Q Rleft Rright ε
          (ε ^ (-12 : ℤ)) (ε ^ 30)
          hεpos hintQ hintR hfirstQ hfirstR
    _ = 2 * ε ^ 2 := by
      field_simp [ne_of_gt hεpos]
      ring

end

end Anderson4D
