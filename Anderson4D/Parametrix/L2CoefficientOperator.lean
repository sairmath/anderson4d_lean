import Anderson4D.Parametrix.L2LatticeSum
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Canonical `L²` operators from parametrix Fourier coefficients

An `ℓ²` matrix does not give an absolutely summable series of rank-one
operators.  This file instead proves a finite Hilbert--Schmidt bound and
uses the unconditional Cauchy criterion to sum the rank-one series in
operator norm.  The resulting bounded operator has exactly the prescribed
Fourier matrix coefficients.

The second half applies this construction to each random parametrix order.
P-3.5b and the lattice summation prove simultaneous square summability
almost surely, which is the correct probabilistic quantifier for the
canonical realization.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

def torusFourierRankOne (p : Z4 × Z4) :
    TorusL2 →L[ℂ] TorusL2 :=
  InnerProductSpace.rankOne ℂ
    (torusFourierBasis (-p.1))
    (torusFourierBasis p.2)

theorem torusFourierMatrixCoeff_rankOne
    (p : Z4 × Z4) (α β : Z4) :
    torusFourierMatrixCoeff (torusFourierRankOne p) α β =
      if p = (α, β) then 1 else 0 := by
  unfold torusFourierMatrixCoeff torusFourierRankOne
  rw [InnerProductSpace.inner_right_rankOne_apply]
  have hb :=
    orthonormal_iff_ite.mp torusFourierBasis.orthonormal
  rw [hb, hb]
  by_cases hp : p = (α, β)
  · subst p
    simp
  · rw [if_neg hp]
    by_cases hβ : p.2 = β
    · rw [if_pos hβ]
      have hneg : -α ≠ -p.1 := by
        intro hα
        apply hp
        apply Prod.ext
        · exact (neg_inj.mp hα).symm
        · exact hβ
      rw [if_neg hneg]
      simp
    · rw [if_neg hβ]
      simp

def finiteFourierMatrixOperator
    (a : Z4 × Z4 → ℂ)
    (s : Finset (Z4 × Z4)) :
    TorusL2 →L[ℂ] TorusL2 :=
  ∑ p ∈ s, a p • torusFourierRankOne p

theorem torusFourierMatrixCoeff_finiteFourierMatrixOperator
    (a : Z4 × Z4 → ℂ)
    (s : Finset (Z4 × Z4))
    (α β : Z4) :
    torusFourierMatrixCoeff (finiteFourierMatrixOperator a s) α β =
      if (α, β) ∈ s then a (α, β) else 0 := by
  calc
    torusFourierMatrixCoeff (finiteFourierMatrixOperator a s) α β =
        ∑ p ∈ s,
          a p * torusFourierMatrixCoeff
            (torusFourierRankOne p) α β := by
      unfold torusFourierMatrixCoeff finiteFourierMatrixOperator
      simp only [_root_.sum_apply, inner_sum,
        smul_apply, inner_smul_right]
    _ = if (α, β) ∈ s then a (α, β) else 0 := by
      simp_rw [torusFourierMatrixCoeff_rankOne]
      simp

theorem operatorNormSq_le_tsum_prod_fourierMatrixCoeff
    (A : TorusL2 →L[ℂ] TorusL2)
    (hsum :
      Summable fun p : Z4 × Z4 =>
        ‖torusFourierMatrixCoeff A p.1 p.2‖ ^ 2) :
    ‖A‖ ^ 2 ≤
      ∑' p : Z4 × Z4,
        ‖torusFourierMatrixCoeff A p.1 p.2‖ ^ 2 := by
  have hswap :
      Summable fun p : Z4 × Z4 =>
        ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2 := by
    exact ((Equiv.prodComm Z4 Z4).summable_iff).2 hsum
  calc
    ‖A‖ ^ 2 ≤
        ∑' β : Z4, ∑' α : Z4,
          ‖torusFourierMatrixCoeff A α β‖ ^ 2 :=
      operatorNormSq_le_tsum_tsum_fourierMatrixCoeff
        A hswap.prod
    _ = ∑' p : Z4 × Z4,
          ‖torusFourierMatrixCoeff A p.2 p.1‖ ^ 2 :=
      hswap.tsum_prod.symm
    _ = ∑' p : Z4 × Z4,
          ‖torusFourierMatrixCoeff A p.1 p.2‖ ^ 2 :=
      (Equiv.prodComm Z4 Z4).tsum_eq
        (fun p : Z4 × Z4 =>
          ‖torusFourierMatrixCoeff A p.1 p.2‖ ^ 2)

theorem normSq_finiteFourierMatrixOperator_le
    (a : Z4 × Z4 → ℂ)
    (s : Finset (Z4 × Z4)) :
    ‖finiteFourierMatrixOperator a s‖ ^ 2 ≤
      ∑ p ∈ s, ‖a p‖ ^ 2 := by
  let f : Z4 × Z4 → ℝ := fun p =>
    ‖torusFourierMatrixCoeff
      (finiteFourierMatrixOperator a s) p.1 p.2‖ ^ 2
  have hfzero :
      ∀ p ∉ s, f p = 0 := by
    intro p hp
    unfold f
    rw [torusFourierMatrixCoeff_finiteFourierMatrixOperator]
    simp [hp]
  have hfsum : Summable f :=
    (hasSum_sum_of_ne_finset_zero hfzero).summable
  calc
    ‖finiteFourierMatrixOperator a s‖ ^ 2 ≤ ∑' p, f p :=
      operatorNormSq_le_tsum_prod_fourierMatrixCoeff
        _ hfsum
    _ = ∑ p ∈ s, ‖a p‖ ^ 2 := by
      rw [tsum_eq_sum hfzero]
      apply Finset.sum_congr rfl
      intro p hp
      unfold f
      rw [torusFourierMatrixCoeff_finiteFourierMatrixOperator]
      simp [hp]

theorem summable_fourierMatrixSeries
    (a : Z4 × Z4 → ℂ)
    (hsq : Summable fun p : Z4 × Z4 => ‖a p‖ ^ 2) :
    Summable fun p : Z4 × Z4 =>
      a p • torusFourierRankOne p := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  rcases summable_iff_vanishing_norm.mp hsq
      (ε ^ 2) (sq_pos_of_pos hε) with
    ⟨s, hs⟩
  refine ⟨s, ?_⟩
  intro t hdisjoint
  have htail := hs t hdisjoint
  have hsum_nonneg :
      0 ≤ ∑ p ∈ t, ‖a p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum_lt :
      (∑ p ∈ t, ‖a p‖ ^ 2) < ε ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg] at htail
    exact htail
  have hop :
      ‖finiteFourierMatrixOperator a t‖ ^ 2 ≤
        ∑ p ∈ t, ‖a p‖ ^ 2 :=
    normSq_finiteFourierMatrixOperator_le a t
  change ‖finiteFourierMatrixOperator a t‖ < ε
  nlinarith [norm_nonneg (finiteFourierMatrixOperator a t)]

/-- The continuous functional extracting one signed Fourier matrix
coefficient from a bounded operator. -/
def torusFourierMatrixCoeffCLM
    (α β : Z4) :
    (TorusL2 →L[ℂ] TorusL2) →L[ℂ] ℂ :=
  (innerSL ℂ (torusFourierBasis (-α))).comp
    (ContinuousLinearMap.apply ℂ TorusL2
      (torusFourierBasis β))

@[simp]
theorem torusFourierMatrixCoeffCLM_apply
    (α β : Z4) (A : TorusL2 →L[ℂ] TorusL2) :
    torusFourierMatrixCoeffCLM α β A =
      torusFourierMatrixCoeff A α β :=
  rfl

/-- The canonical bounded operator associated with an `ℓ²` Fourier
matrix.  Square summability is used in the theorems below to prove
that the unconditional `tsum` has the intended value. -/
def squareSummableFourierOperator
    (a : Z4 × Z4 → ℂ) :
    TorusL2 →L[ℂ] TorusL2 :=
  ∑' p : Z4 × Z4, a p • torusFourierRankOne p

theorem torusFourierMatrixCoeff_smul_rankOne
    (a : Z4 × Z4 → ℂ)
    (p : Z4 × Z4) (α β : Z4) :
    torusFourierMatrixCoeff
        (a p • torusFourierRankOne p) α β =
      if p = (α, β) then a (α, β) else 0 := by
  calc
    torusFourierMatrixCoeff
        (a p • torusFourierRankOne p) α β =
        a p *
          torusFourierMatrixCoeff
            (torusFourierRankOne p) α β := by
      unfold torusFourierMatrixCoeff
      simp only [smul_apply, inner_smul_right]
    _ = if p = (α, β) then a (α, β) else 0 := by
      rw [torusFourierMatrixCoeff_rankOne]
      split_ifs with hp
      · subst p
        simp
      · simp

theorem torusFourierMatrixCoeff_squareSummableFourierOperator
    (a : Z4 × Z4 → ℂ)
    (hsq : Summable fun p : Z4 × Z4 => ‖a p‖ ^ 2)
    (α β : Z4) :
    torusFourierMatrixCoeff
        (squareSummableFourierOperator a) α β =
      a (α, β) := by
  have hop :
      Summable fun p : Z4 × Z4 =>
        a p • torusFourierRankOne p :=
    summable_fourierMatrixSeries a hsq
  have hmap :=
    hop.hasSum.mapL (torusFourierMatrixCoeffCLM α β)
  have hcoeff :
      HasSum
        (fun p : Z4 × Z4 =>
          if p = (α, β) then a (α, β) else 0)
        (torusFourierMatrixCoeff
          (squareSummableFourierOperator a) α β) := by
    simpa only [squareSummableFourierOperator,
      torusFourierMatrixCoeffCLM_apply,
      torusFourierMatrixCoeff_smul_rankOne] using hmap
  exact
    ((hasSum_ite_eq (α, β) (a (α, β))).unique hcoeff).symm

/-! ## Canonical random parametrix operators -/

/-- The probability-Haar Fourier matrix associated with the paper's
order-`m` coefficient. -/
def parametrixOrderFourierMatrix
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (m : ℕ) (ω : M.Ω)
    (p : Z4 × Z4) : ℂ :=
  (paperTorusVolume : ℂ)⁻¹ *
    pmCoeff M ρ lam ε m p.1 p.2 ω

/-- The raw, scaled P-3.5b coefficient has the measurable weighted
second-moment bound used in the Tonelli argument.  This is the
operator-free version of
`parametrixOrder_weightedCoeff_measurable_and_bound`. -/
theorem parametrixOrderFourierMatrix_weighted_measurable_and_bound
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ} {α β : Z4}
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
            (‖parametrixOrderFourierMatrix
                M ρ lam ε m ω (α, β)‖ ^ 2 *
              paperL2FourierWeight ε α β))
        (volume : Measure M.Ω) ∧
      (∫⁻ ω,
          ENNReal.ofReal
            (‖parametrixOrderFourierMatrix
                M ρ lam ε m ω (α, β)‖ ^ 2 *
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
  constructor
  · exact
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hscaled.aestronglyMeasurable.norm.aemeasurable.pow_const 2).mul_const _)
  · simpa only [parametrixOrderFourierMatrix,
      parametrixOrderL2WeightedMomentRHS, c] using
      (lintegral_ofReal_norm_sq_const_mul_le
        (volume : Measure M.Ω)
        (pmCoeff M ρ lam ε m α β)
        hpm.1 c
        (zero_le_one.trans
          (one_le_paperL2FourierWeight
            hε hεle α β))
        hpm.2)

/-- P-3.5b plus the explicit lattice majorant make the whole order-`m`
Fourier matrix square summable simultaneously, outside one null set. -/
theorem ae_summable_parametrixOrderFourierMatrix
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
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
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      Summable fun p : Z4 × Z4 =>
        ‖parametrixOrderFourierMatrix
            M ρ lam ε m ω p‖ ^ 2 := by
  let f : (Z4 × Z4) → M.Ω → ℝ :=
    fun p ω =>
      ‖parametrixOrderFourierMatrix
          M ρ lam ε m ω (p.2, p.1)‖ ^ 2 *
        paperL2FourierWeight ε p.2 p.1
  let B : (Z4 × Z4) → ℝ :=
    fun p =>
      parametrixOrderL2WeightedMomentRHS
        outerConstant powerConstant lam ε m p.2 p.1
  have hcoeff (p : Z4 × Z4) :=
    parametrixOrderFourierMatrix_weighted_measurable_and_bound
      (hfubini p.2 p.1) hwick
      (hdet p.2 p.1) hε hεle
  have hmeas :
      ∀ p : Z4 × Z4,
        AEMeasurable
          (fun ω => ENNReal.ofReal (f p ω))
          (volume : Measure M.Ω) := by
    intro p
    simpa only [f] using (hcoeff p).1
  have hterm :
      ∀ p : Z4 × Z4,
        (∫⁻ ω, ENNReal.ofReal (f p ω)
          ∂(volume : Measure M.Ω)) ≤
          ENNReal.ofReal (B p) := by
    intro p
    simpa only [f, B] using (hcoeff p).2
  have hBsum : Summable B := by
    simpa only [B] using
      (summable_parametrixOrderL2WeightedMomentRHS
        houter hpower hlam hε hεle)
  have hsumIntegrals :
      (∑' p : Z4 × Z4,
          (∫⁻ ω, ENNReal.ofReal (f p ω)
            ∂(volume : Measure M.Ω))) < ∞ := by
    exact lt_of_le_of_lt
      (ENNReal.tsum_le_tsum hterm)
      hBsum.tsum_ofReal_lt_top
  have hlintegral :
      (∫⁻ ω,
          ∑' p : Z4 × Z4,
            ENNReal.ofReal (f p ω)
          ∂(volume : Measure M.Ω)) < ∞ := by
    rw [lintegral_tsum hmeas]
    exact hsumIntegrals
  have hae :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        (∑' p : Z4 × Z4,
          ENNReal.ofReal (f p ω)) < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hmeas) hlintegral.ne
  filter_upwards [hae] with ω hω
  have hnn :
      Summable
        (ENNReal.toNNReal ∘
          fun p : Z4 × Z4 =>
            ENNReal.ofReal (f p ω)) :=
    ENNReal.summable_toNNReal_of_tsum_ne_top hω.ne
  have hrealSum :
      Summable fun p : Z4 × Z4 =>
        ((ENNReal.ofReal (f p ω)).toNNReal : ℝ) :=
    NNReal.summable_coe.mpr hnn
  have hweighted :
      Summable fun p : Z4 × Z4 => f p ω := by
    apply hrealSum.congr
    intro p
    have hfp : 0 ≤ f p ω := by
      dsimp [f]
      exact mul_nonneg (sq_nonneg _)
        (paperL2FourierWeight_nonneg ε p.2 p.1)
    simp only [ENNReal.ofReal, ENNReal.toNNReal_coe,
      Real.coe_toNNReal', max_eq_left hfp]
  have hplainSwap :
      Summable fun p : Z4 × Z4 =>
        ‖parametrixOrderFourierMatrix
            M ρ lam ε m ω (p.2, p.1)‖ ^ 2 := by
    apply hweighted.of_nonneg_of_le
    · intro p
      exact sq_nonneg _
    · intro p
      exact le_mul_of_one_le_right
        (sq_nonneg _)
        (one_le_paperL2FourierWeight
          hε hεle p.2 p.1)
  apply ((Equiv.prodComm Z4 Z4).summable_iff).mp
  apply hplainSwap.congr
  rintro ⟨α, β⟩
  rfl

/-- The canonical bounded operator for one random parametrix order.
The unconditional `tsum` is totalized by mathlib, while the preceding
theorem proves that it is the intended sum almost surely. -/
def canonicalParametrixOrderL2Operator
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (m : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  fun ω =>
    squareSummableFourierOperator
      (parametrixOrderFourierMatrix
        M ρ lam ε m ω)

/-- The canonical order operator realizes all Fourier coefficients
simultaneously almost surely. -/
theorem canonicalParametrixOrderL2Operator_realizes
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
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
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    ParametrixOrderL2CoeffRealization
      M ρ lam ε m
      (canonicalParametrixOrderL2Operator
        M ρ lam ε m) := by
  filter_upwards [
    ae_summable_parametrixOrderFourierMatrix
      hfubini hwick hdet
      houter hpower hlam hε hεle] with ω hω
  intro α β
  simpa only [canonicalParametrixOrderL2Operator,
    parametrixOrderFourierMatrix] using
    (torusFourierMatrixCoeff_squareSummableFourierOperator
      (parametrixOrderFourierMatrix
        M ρ lam ε m ω) hω α β)

/-- P-3.5b constructs, rather than assumes, an orderwise bounded
operator realization. -/
theorem nonempty_parametrixOrderL2CoeffRealization
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
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
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    Nonempty
      {A : M.Ω → TorusL2 →L[ℂ] TorusL2 //
        ParametrixOrderL2CoeffRealization
          M ρ lam ε m A} :=
  ⟨⟨canonicalParametrixOrderL2Operator
      M ρ lam ε m,
    canonicalParametrixOrderL2Operator_realizes
      hfubini hwick hdet
      houter hpower hlam hε hεle⟩⟩

/-- The closed orderwise P-L² estimate with no externally supplied
operator realization. -/
theorem lintegral_canonicalParametrixOrder_normSq_le_explicit
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
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
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    (∫⁻ ω,
        ENNReal.ofReal
          (‖canonicalParametrixOrderL2Operator
              M ρ lam ε m ω‖ ^ 2)
        ∂(volume : Measure M.Ω)) ≤
      ENNReal.ofReal
        (32768 *
          parametrixOrderL2Scalar
            outerConstant powerConstant lam ε m *
          ε⁻¹ ^ (20 : ℕ) *
          (∑' k : Z4,
            l2LatticeRadialWeight 5 k) ^ 2) := by
  exact lintegral_parametrixOrder_normSq_le_explicit
    (canonicalParametrixOrderL2Operator
      M ρ lam ε m)
    (canonicalParametrixOrderL2Operator_realizes
      hfubini hwick hdet
      houter hpower hlam hε hεle)
    hfubini hwick hdet
    houter hpower hlam hε hεle

/-- The positive-order part of the finite parametrix operator,
`∑_{m=1}^A P_m`, on `L²`.

Order zero is deliberately excluded: `P₀ = G` is bounded but is not
Hilbert--Schmidt in dimension four, so its Fourier matrix is not in
`ℓ² (Z4 × Z4)` and cannot pass through
`squareSummableFourierOperator`.  The full physical truncation adds
`greenL2Op` separately in `L2Quantitative.lean`. -/
def canonicalPositiveTruncatedParametrixL2Operator
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  fun ω =>
    ∑ n ∈ Finset.range A,
      canonicalParametrixOrderL2Operator
        M ρ lam ε (n + 1) ω

/-- Fourier coefficients commute with a finite operator sum. -/
theorem torusFourierMatrixCoeff_finsetSum
    {ι : Type*} (s : Finset ι)
    (F : ι → TorusL2 →L[ℂ] TorusL2)
    (α β : Z4) :
    torusFourierMatrixCoeff
        (∑ i ∈ s, F i) α β =
      ∑ i ∈ s,
        torusFourierMatrixCoeff (F i) α β := by
  unfold torusFourierMatrixCoeff
  simp only [_root_.sum_apply, inner_sum]

/-- If every positive canonical order has its P-3.5b realization, the
finite positive-order operator realizes the corresponding paper
coefficients on one common full-measure event. -/
theorem canonicalPositiveTruncatedParametrixL2Operator_coeff
    {M : NoiseModel} {ρ : SmoothCutoff}
    {lam ε : ℝ} {A : ℕ}
    (hreal :
      ∀ n ∈ Finset.range A,
        ParametrixOrderL2CoeffRealization
          M ρ lam ε (n + 1)
          (canonicalParametrixOrderL2Operator
            M ρ lam ε (n + 1))) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ α β,
      torusFourierMatrixCoeff
          (canonicalPositiveTruncatedParametrixL2Operator
            M ρ lam ε A ω) α β =
        (paperTorusVolume : ℂ)⁻¹ *
          ∑ n ∈ Finset.range A,
            pmCoeff M ρ lam ε (n + 1) α β ω := by
  have hall :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ∀ n ∈ Finset.range A, ∀ α β,
          torusFourierMatrixCoeff
              (canonicalParametrixOrderL2Operator
                M ρ lam ε (n + 1) ω) α β =
            (paperTorusVolume : ℂ)⁻¹ *
              pmCoeff M ρ lam ε (n + 1) α β ω :=
    (Filter.eventually_all_finset
      (Finset.range A)).2 hreal
  filter_upwards [hall] with ω hω
  intro α β
  calc
    torusFourierMatrixCoeff
        (canonicalPositiveTruncatedParametrixL2Operator
          M ρ lam ε A ω) α β =
        ∑ n ∈ Finset.range A,
          torusFourierMatrixCoeff
            (canonicalParametrixOrderL2Operator
              M ρ lam ε (n + 1) ω) α β := by
      exact torusFourierMatrixCoeff_finsetSum
        (Finset.range A)
        (fun n =>
          canonicalParametrixOrderL2Operator
            M ρ lam ε (n + 1) ω) α β
    _ = ∑ n ∈ Finset.range A,
          (paperTorusVolume : ℂ)⁻¹ *
            pmCoeff M ρ lam ε (n + 1) α β ω := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hω n hn α β
    _ = (paperTorusVolume : ℂ)⁻¹ *
          ∑ n ∈ Finset.range A,
            pmCoeff M ρ lam ε (n + 1) α β ω := by
      rw [Finset.mul_sum]

/-- Concrete construction of the positive-order coefficient identity
from P-3.5b data. -/
theorem canonicalPositiveTruncatedParametrixL2Operator_coeff_of_momentBounds
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
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ α β,
      torusFourierMatrixCoeff
          (canonicalPositiveTruncatedParametrixL2Operator
            M ρ lam ε A ω) α β =
        (paperTorusVolume : ℂ)⁻¹ *
          ∑ n ∈ Finset.range A,
            pmCoeff M ρ lam ε (n + 1) α β ω := by
  apply canonicalPositiveTruncatedParametrixL2Operator_coeff
  intro n hn
  have hnlt : n < A := Finset.mem_range.mp hn
  have hpos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hle : n + 1 ≤ A := by omega
  exact canonicalParametrixOrderL2Operator_realizes
    (hfubini (n + 1) hpos hle)
    (hwick (n + 1) hpos hle)
    (hdet (n + 1) hpos hle)
    houter hpower hlam hε hεle

end

end Anderson4D
