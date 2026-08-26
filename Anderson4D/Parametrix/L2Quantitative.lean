import Anderson4D.Parametrix.L2CoefficientOperator
import Anderson4D.Parametrix.L2ParametrixInverse

/-!
# Quantitative closure of the `L²` parametrix step

This file completes the probability and finite-sum part of P-L2 without
postulating an operator realization.  The canonical operators constructed
from the Fourier coefficients are strongly measurable almost everywhere.
Their finite sum `Q_A` satisfies the elementary but indispensable estimate

`E ‖Q_A‖² ≤ (A + 1) * ∑_{m=0}^A E ‖P_m‖²`.

The last section combines this estimate with an honest almost-everywhere
P-err input.  The validity of the two operator identities is included in
the good event; it is not silently strengthened to a pointwise hypothesis.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

/-! ## Measurability of the canonical coefficient operators -/

private theorem aestronglyMeasurable_finsetSum_apply
    {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    {μ : Measure Ω} (s : Finset ι)
    (F : ι → Ω → E)
    (hF : ∀ i ∈ s, AEStronglyMeasurable (F i) μ) :
    AEStronglyMeasurable
      (fun ω => ∑ i ∈ s, F i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (stronglyMeasurable_const :
          StronglyMeasurable (fun _ : Ω => (0 : E)))
          |>.aestronglyMeasurable
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

/-- The canonical order operator is almost everywhere strongly measurable.

The target operator space is not assumed separable.  We therefore do not
appeal to Borel measurability of an arbitrary operator-valued `tsum`.
Instead, finite Fourier sums are strongly measurable and converge in
operator norm almost surely by the square-summability theorem. -/
theorem aestronglyMeasurable_canonicalParametrixOrderL2Operator
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
    AEStronglyMeasurable
      (canonicalParametrixOrderL2Operator
        M ρ lam ε m)
      (volume : Measure M.Ω) := by
  let term :
      (Z4 × Z4) → M.Ω → (TorusL2 →L[ℂ] TorusL2) :=
    fun p ω =>
      parametrixOrderFourierMatrix
        M ρ lam ε m ω p • torusFourierRankOne p
  have hterm :
      ∀ p : Z4 × Z4,
        AEStronglyMeasurable
          (term p) (volume : Measure M.Ω) := by
    intro p
    have hcoeff :
        AEStronglyMeasurable
          (fun ω =>
            parametrixOrderFourierMatrix
              M ρ lam ε m ω p)
          (volume : Measure M.Ω) := by
      unfold parametrixOrderFourierMatrix
      exact
        ((hfubini p.1 p.2).memLp_pmCoeff
          |>.aestronglyMeasurable).const_mul
            (paperTorusVolume : ℂ)⁻¹
    exact hcoeff.smul
      (stronglyMeasurable_const.aestronglyMeasurable)
  refine aestronglyMeasurable_of_tendsto_ae
    (Filter.atTop :
      Filter (Finset (Z4 × Z4)))
    (f := fun s ω => ∑ p ∈ s, term p ω) ?_ ?_
  · intro s
    exact aestronglyMeasurable_finsetSum_apply
      s term fun p _hp => hterm p
  · filter_upwards [
      ae_summable_parametrixOrderFourierMatrix
        hfubini hwick hdet
        houter hpower hlam hε hεle] with ω hω
    have hseries :
        Summable fun p : Z4 × Z4 =>
          parametrixOrderFourierMatrix
              M ρ lam ε m ω p •
            torusFourierRankOne p :=
      summable_fourierMatrixSeries
        (parametrixOrderFourierMatrix
          M ρ lam ε m ω) hω
    change HasSum (fun p : Z4 × Z4 => term p ω)
      (canonicalParametrixOrderL2Operator M ρ lam ε m ω)
    simpa only [term, canonicalParametrixOrderL2Operator,
      squareSummableFourierOperator] using hseries.hasSum

/-! ## Explicit second-moment budgets -/

/-- The explicit right side of the orderwise `(3.31)` estimate. -/
def canonicalParametrixOrderL2SecondMomentBudget
    (outerConstant powerConstant lam ε : ℝ)
    (m : ℕ) : ℝ :=
  32768 *
    parametrixOrderL2Scalar
      outerConstant powerConstant lam ε m *
    ε⁻¹ ^ (20 : ℕ) *
    (∑' k : Z4, l2LatticeRadialWeight 5 k) ^ 2

theorem canonicalParametrixOrderL2SecondMomentBudget_nonneg
    {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    0 ≤ canonicalParametrixOrderL2SecondMomentBudget
      outerConstant powerConstant lam ε m := by
  unfold canonicalParametrixOrderL2SecondMomentBudget
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        (parametrixOrderL2Scalar_nonneg
          houter hpower hlam))
      (by positivity))
    (sq_nonneg _)

/-- Pointwise finite-sum estimate
`‖Σ A_m‖² ≤ card(s) Σ ‖A_m‖²`. -/
theorem normSq_finsetSum_le_card_mul_sum_normSq
    {ι H : Type*}
    [NormedAddCommGroup H]
    (s : Finset ι) (F : ι → H) :
    ‖∑ i ∈ s, F i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 := by
  calc
    ‖∑ i ∈ s, F i‖ ^ 2 ≤
        (∑ i ∈ s, ‖F i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_sum_le s F) 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖F i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq

/-- The canonical order operator has an integrable squared norm. -/
theorem integrable_normSq_canonicalParametrixOrderL2Operator
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
    Integrable
      (fun ω =>
        ‖canonicalParametrixOrderL2Operator
            M ρ lam ε m ω‖ ^ 2)
      (volume : Measure M.Ω) := by
  let Aop :=
    canonicalParametrixOrderL2Operator
      M ρ lam ε m
  have hmeasA :
      AEStronglyMeasurable Aop
        (volume : Measure M.Ω) :=
    aestronglyMeasurable_canonicalParametrixOrderL2Operator
      hfubini hwick hdet
      houter hpower hlam hε hεle
  have hlin :
      (∫⁻ ω,
          ENNReal.ofReal (‖Aop ω‖ ^ 2)
          ∂(volume : Measure M.Ω)) ≤
        ENNReal.ofReal
          (canonicalParametrixOrderL2SecondMomentBudget
            outerConstant powerConstant lam ε m) := by
    simpa only [Aop,
      canonicalParametrixOrderL2SecondMomentBudget] using
      (lintegral_canonicalParametrixOrder_normSq_le_explicit
        hfubini hwick hdet
        houter hpower hlam hε hεle)
  refine ⟨hmeasA.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun ω => sq_nonneg ‖Aop ω‖)]
  exact hlin.trans_lt ENNReal.ofReal_lt_top

/-- Real expectation form of the canonical orderwise `(3.31)` bound. -/
theorem integral_normSq_canonicalParametrixOrderL2Operator_le
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
    (∫ ω,
        ‖canonicalParametrixOrderL2Operator
            M ρ lam ε m ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
      canonicalParametrixOrderL2SecondMomentBudget
        outerConstant powerConstant lam ε m := by
  simpa only [canonicalParametrixOrderL2SecondMomentBudget] using
    (integral_parametrixOrder_normSq_le_explicit
      (canonicalParametrixOrderL2Operator
        M ρ lam ε m)
      (canonicalParametrixOrderL2Operator_realizes
        hfubini hwick hdet
        houter hpower hlam hε hεle)
      hfubini hwick hdet
      houter hpower hlam hε hεle
      (integrable_normSq_canonicalParametrixOrderL2Operator
        hfubini hwick hdet
        houter hpower hlam hε hεle))

/-! ## The physical truncation: deterministic order zero -/

/-- One piece of the physical truncation.  The zeroth piece is the
bounded Green multiplier itself.  Positive pieces use the canonical
square-summable coefficient construction.

This distinction is forced in dimension four: `G` is bounded but not
Hilbert--Schmidt, so its Fourier matrix must not be fed to
`squareSummableFourierOperator`. -/
def canonicalPhysicalParametrixL2Piece
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) {A : ℕ} (i : Fin (A + 1)) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  if i.val = 0 then
    fun _ => greenL2Op
  else
    canonicalParametrixOrderL2Operator
      M ρ lam ε i.val

/-- The actual finite physical parametrix
`P_ε = G + ∑_{m=1}^A P_m`. -/
def canonicalPhysicalTruncatedParametrixL2Operator
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  fun ω =>
    ∑ i : Fin (A + 1),
      canonicalPhysicalParametrixL2Piece
        M ρ lam ε i ω

/-- The orderwise budget, with the deterministic Green piece bounded
by one. -/
def canonicalPhysicalParametrixL2PieceSecondMomentBudget
    (outerConstant powerConstant lam ε : ℝ)
    {A : ℕ} (i : Fin (A + 1)) : ℝ :=
  if i.val = 0 then 1
  else
    canonicalParametrixOrderL2SecondMomentBudget
      outerConstant powerConstant lam ε i.val

/-- The finite physical budget.  The factor `A + 1` is exactly the
cardinality in `‖Σ A_m‖² ≤ (A+1) Σ ‖A_m‖²`. -/
def canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
    (outerConstant powerConstant lam ε : ℝ)
    (A : ℕ) : ℝ :=
  (A + 1 : ℝ) *
    ∑ i : Fin (A + 1),
      canonicalPhysicalParametrixL2PieceSecondMomentBudget
        outerConstant powerConstant lam ε i

theorem canonicalPhysicalParametrixL2PieceSecondMomentBudget_nonneg
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ} (i : Fin (A + 1))
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    0 ≤ canonicalPhysicalParametrixL2PieceSecondMomentBudget
      outerConstant powerConstant lam ε i := by
  unfold canonicalPhysicalParametrixL2PieceSecondMomentBudget
  split_ifs
  · norm_num
  · exact
      canonicalParametrixOrderL2SecondMomentBudget_nonneg
        houter hpower hlam

theorem canonicalPhysicalTruncatedParametrixL2SecondMomentBudget_nonneg
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    0 ≤ canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
      outerConstant powerConstant lam ε A := by
  unfold canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ =>
      canonicalPhysicalParametrixL2PieceSecondMomentBudget_nonneg
        i houter hpower hlam)

theorem aestronglyMeasurable_canonicalPhysicalParametrixL2Piece
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ} (i : Fin (A + 1))
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
    AEStronglyMeasurable
      (canonicalPhysicalParametrixL2Piece
        M ρ lam ε i)
      (volume : Measure M.Ω) := by
  classical
  unfold canonicalPhysicalParametrixL2Piece
  split_ifs with hi
  · exact stronglyMeasurable_const.aestronglyMeasurable
  · exact
      aestronglyMeasurable_canonicalParametrixOrderL2Operator
        (hfubini i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        (hwick i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        (hdet i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        houter hpower hlam hε hεle

theorem aestronglyMeasurable_canonicalPhysicalTruncatedParametrixL2Operator
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
    AEStronglyMeasurable
      (canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A)
      (volume : Measure M.Ω) := by
  unfold canonicalPhysicalTruncatedParametrixL2Operator
  exact aestronglyMeasurable_finsetSum_apply
    Finset.univ
    (canonicalPhysicalParametrixL2Piece
      M ρ lam ε)
    (fun i _ =>
      aestronglyMeasurable_canonicalPhysicalParametrixL2Piece
        i hfubini hwick hdet
        houter hpower hlam hε hεle)

theorem integrable_normSq_canonicalPhysicalParametrixL2Piece
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ} (i : Fin (A + 1))
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
    Integrable
      (fun ω =>
        ‖canonicalPhysicalParametrixL2Piece
            M ρ lam ε i ω‖ ^ 2)
      (volume : Measure M.Ω) := by
  classical
  unfold canonicalPhysicalParametrixL2Piece
  split_ifs with hi
  · exact integrable_const _
  · exact
      integrable_normSq_canonicalParametrixOrderL2Operator
        (hfubini i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        (hwick i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        (hdet i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        houter hpower hlam hε hεle

theorem integral_normSq_canonicalPhysicalParametrixL2Piece_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ} (i : Fin (A + 1))
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
    (∫ ω,
        ‖canonicalPhysicalParametrixL2Piece
            M ρ lam ε i ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
      canonicalPhysicalParametrixL2PieceSecondMomentBudget
        outerConstant powerConstant lam ε i := by
  classical
  unfold canonicalPhysicalParametrixL2Piece
  unfold canonicalPhysicalParametrixL2PieceSecondMomentBudget
  split_ifs with hi
  · rw [integral_const]
    rw [probReal_univ, one_smul]
    simpa using
      (pow_le_pow_left₀ (norm_nonneg greenL2Op)
        norm_greenL2Op_le_one 2)
  · exact
      integral_normSq_canonicalParametrixOrderL2Operator_le
        (hfubini i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        (hwick i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        (hdet i.val (Nat.one_le_iff_ne_zero.mpr hi)
          (Nat.le_of_lt_succ i.isLt))
        houter hpower hlam hε hεle

theorem integrable_normSq_canonicalPhysicalTruncatedParametrixL2Operator
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
    Integrable
      (fun ω =>
        ‖canonicalPhysicalTruncatedParametrixL2Operator
            M ρ lam ε A ω‖ ^ 2)
      (volume : Measure M.Ω) := by
  let piece :=
    canonicalPhysicalParametrixL2Piece
      M ρ lam ε (A := A)
  have hmajorant :
      Integrable
        (fun ω =>
          ((Finset.univ : Finset (Fin (A + 1))).card : ℝ) *
            ∑ i : Fin (A + 1), ‖piece i ω‖ ^ 2)
        (volume : Measure M.Ω) := by
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ fun i _ =>
      integrable_normSq_canonicalPhysicalParametrixL2Piece
        i hfubini hwick hdet
        houter hpower hlam hε hεle
  apply hmajorant.mono'
    ((aestronglyMeasurable_canonicalPhysicalTruncatedParametrixL2Operator
      hfubini hwick hdet
      houter hpower hlam hε hεle).norm.pow 2)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact normSq_finsetSum_le_card_mul_sum_normSq
    Finset.univ (fun i => piece i ω)

theorem integral_normSq_canonicalPhysicalTruncatedParametrixL2Operator_le
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
    (∫ ω,
        ‖canonicalPhysicalTruncatedParametrixL2Operator
            M ρ lam ε A ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
        outerConstant powerConstant lam ε A := by
  let piece :=
    canonicalPhysicalParametrixL2Piece
      M ρ lam ε (A := A)
  have hP :=
    integrable_normSq_canonicalPhysicalTruncatedParametrixL2Operator
      hfubini hwick hdet
      houter hpower hlam hε hεle
  have hpieces :
      ∀ i : Fin (A + 1),
        Integrable (fun ω => ‖piece i ω‖ ^ 2)
          (volume : Measure M.Ω) := fun i =>
    integrable_normSq_canonicalPhysicalParametrixL2Piece
      i hfubini hwick hdet
      houter hpower hlam hε hεle
  have hsum :
      Integrable
        (fun ω => ∑ i : Fin (A + 1), ‖piece i ω‖ ^ 2)
        (volume : Measure M.Ω) :=
    integrable_finsetSum Finset.univ fun i _ => hpieces i
  have hmajorant :
      Integrable
        (fun ω =>
          ((Finset.univ : Finset (Fin (A + 1))).card : ℝ) *
            ∑ i : Fin (A + 1), ‖piece i ω‖ ^ 2)
        (volume : Measure M.Ω) :=
    hsum.const_mul _
  calc
    (∫ ω,
        ‖canonicalPhysicalTruncatedParametrixL2Operator
            M ρ lam ε A ω‖ ^ 2
        ∂(volume : Measure M.Ω)) ≤
        ∫ ω,
          ((Finset.univ : Finset (Fin (A + 1))).card : ℝ) *
            ∑ i : Fin (A + 1), ‖piece i ω‖ ^ 2
          ∂(volume : Measure M.Ω) := by
      apply integral_mono_ae hP hmajorant
      filter_upwards with ω
      exact normSq_finsetSum_le_card_mul_sum_normSq
        Finset.univ (fun i => piece i ω)
    _ =
        ((Finset.univ : Finset (Fin (A + 1))).card : ℝ) *
          ∑ i : Fin (A + 1),
            ∫ ω, ‖piece i ω‖ ^ 2
              ∂(volume : Measure M.Ω) := by
      rw [integral_const_mul]
      congr 1
      exact integral_finsetSum Finset.univ
        (fun i _ => hpieces i)
    _ ≤
        ((Finset.univ : Finset (Fin (A + 1))).card : ℝ) *
          ∑ i : Fin (A + 1),
            canonicalPhysicalParametrixL2PieceSecondMomentBudget
              outerConstant powerConstant lam ε i := by
      gcongr with i
      exact
        integral_normSq_canonicalPhysicalParametrixL2Piece_le
          i hfubini hwick hdet
          houter hpower hlam hε hεle
    _ =
        canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε A := by
      simp only [canonicalPhysicalTruncatedParametrixL2SecondMomentBudget,
        Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]

/-! ## A mixed second/first-moment good event -/

/-- Second-moment Markov at an arbitrary positive operator-norm
threshold. -/
theorem measureReal_norm_ge_le_div_secondMoment
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure Ω)
    (F : Ω → H →L[ℂ] H)
    (r δ : ℝ) (hr : 0 < r)
    (hint : Integrable (fun ω => ‖F ω‖ ^ 2) μ)
    (hsecond : (∫ ω, ‖F ω‖ ^ 2 ∂μ) ≤ δ) :
    μ.real {ω | r ≤ ‖F ω‖} ≤ δ / r ^ 2 := by
  have hmark :=
    sq_mul_measureReal_operatorBadEvent_le
      μ F r hr.le hint
  rw [operatorBadEvent] at hmark
  rw [le_div_iff₀ (sq_pos_of_pos hr)]
  simpa [mul_comm] using hmark.trans hsecond

/-- The paper-scale event, augmented by an explicit validity predicate
for the operator identities and the physical/factorized bridge.

Keeping `valid` inside the event permits the identities to hold only
almost surely, as is natural for random kernels. -/
def quantitativeL2ParametrixGoodEvent
    {Ω : Type*}
    (P Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (valid : Ω → Prop) (ε : ℝ) : Set Ω :=
  {ω |
    ‖P ω‖ ≤ ε ^ (-14 : ℤ) ∧
      ‖Rleft ω‖ + ‖Rright ω‖ ≤ ε ^ 28 ∧
      valid ω}

/-- Mixed Chebyshev/Markov estimate: the parametrix uses its proved
second moment, while P-err supplies the paper's first-moment remainder
estimate.  An almost-sure identity/bridge input costs zero measure. -/
theorem measureReal_compl_quantitativeL2ParametrixGoodEvent_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (P Rleft Rright : Ω → TorusL2 →L[ℂ] TorusL2)
    (valid : Ω → Prop)
    (ε δP δR : ℝ)
    (hεpos : 0 < ε)
    (hintP : Integrable (fun ω => ‖P ω‖ ^ 2) μ)
    (hintR :
      Integrable (fun ω => ‖Rleft ω‖ + ‖Rright ω‖) μ)
    (hsecondP : (∫ ω, ‖P ω‖ ^ 2 ∂μ) ≤ δP)
    (hfirstR :
      (∫ ω, ‖Rleft ω‖ + ‖Rright ω‖ ∂μ) ≤ δR)
    (hvalid : ∀ᵐ ω ∂μ, valid ω) :
    μ.real
        (quantitativeL2ParametrixGoodEvent
          P Rleft Rright valid ε)ᶜ ≤
      δP / (ε ^ (-14 : ℤ)) ^ 2 +
        δR / ε ^ 28 := by
  let badP : Set Ω :=
    {ω | ε ^ (-14 : ℤ) ≤ ‖P ω‖}
  let badR : Set Ω :=
    {ω | ε ^ 28 ≤ ‖Rleft ω‖ + ‖Rright ω‖}
  let invalid : Set Ω := {ω | ¬ valid ω}
  have hrP : 0 < ε ^ (-14 : ℤ) :=
    zpow_pos hεpos _
  have hrR : 0 < ε ^ 28 :=
    pow_pos hεpos _
  have hP :
      μ.real badP ≤
        δP / (ε ^ (-14 : ℤ)) ^ 2 := by
    exact measureReal_norm_ge_le_div_secondMoment
      μ P _ δP hrP hintP hsecondP
  have hR :
      μ.real badR ≤ δR / ε ^ 28 := by
    have hmark :=
      mul_meas_ge_le_integral_of_nonneg
        (μ := μ)
        (f := fun ω => ‖Rleft ω‖ + ‖Rright ω‖)
        (ae_of_all μ fun ω =>
          add_nonneg (norm_nonneg _) (norm_nonneg _))
        hintR (ε ^ 28)
    rw [le_div_iff₀ hrR]
    simpa only [badR, Set.mem_setOf_eq, mul_comm] using
      hmark.trans hfirstR
  have hinvalid : μ.real invalid = 0 := by
    have hnull : μ invalid = 0 := by
      simpa only [invalid] using (ae_iff.mp hvalid)
    rw [measureReal_def, hnull]
    simp
  have hsubset :
      (quantitativeL2ParametrixGoodEvent
        P Rleft Rright valid ε)ᶜ ⊆
        badP ∪ badR ∪ invalid := by
    intro ω hω
    change
      ¬ (‖P ω‖ ≤ ε ^ (-14 : ℤ) ∧
        ‖Rleft ω‖ + ‖Rright ω‖ ≤ ε ^ 28 ∧
        valid ω) at hω
    by_cases hp : ‖P ω‖ ≤ ε ^ (-14 : ℤ)
    · by_cases hr :
          ‖Rleft ω‖ + ‖Rright ω‖ ≤ ε ^ 28
      · exact Or.inr (fun hv => hω ⟨hp, hr, hv⟩)
      · exact Or.inl (Or.inr (le_of_not_ge hr))
    · exact Or.inl (Or.inl (le_of_not_ge hp))
  calc
    μ.real
        (quantitativeL2ParametrixGoodEvent
          P Rleft Rright valid ε)ᶜ ≤
        μ.real (badP ∪ badR ∪ invalid) :=
      measureReal_mono hsubset
    _ ≤ μ.real badP + μ.real badR + μ.real invalid := by
      exact (measureReal_union_le (badP ∪ badR) invalid).trans
        (add_le_add (measureReal_union_le badP badR) le_rfl)
    _ ≤ δP / (ε ^ (-14 : ℤ)) ^ 2 +
          δR / ε ^ 28 + μ.real invalid := by
      gcongr
    _ = δP / (ε ^ (-14 : ℤ)) ^ 2 +
          δR / ε ^ 28 := by rw [hinvalid]; ring

/-! ## The exact remaining P-err/operator bridge -/

/-- The almost-sure predicate still required from P-err and the
physical-kernel/operator bridge.  It says both that the factorized
parametrix identities hold and that multiplying the factorized
parametrix by `G` gives the canonical physical operator constructed
from the coefficients.

This is a definition of the unresolved input, not an output predicate:
none of its fields contains a norm estimate or a desired conclusion. -/
def canonicalFactorizedParametrixValid
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft Rright :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (ω : M.Ω) : Prop :=
  AndersonParametrixData
      greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω)
      (Qfactor ω) (Rleft ω) (Rright ω) ∧
    Qfactor ω * greenL2Op =
      canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω

/-- The canonical paper-scale event.  Its norm threshold is imposed on
the physical parametrix `P_ε = Qfactor * G`, not on the auxiliary
factorized operator. -/
def canonicalL2ParametrixGoodEvent
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft Rright :
      M.Ω → TorusL2 →L[ℂ] TorusL2) :
    Set M.Ω :=
  quantitativeL2ParametrixGoodEvent
    (canonicalPhysicalTruncatedParametrixL2Operator
      M ρ lam ε A)
    Rleft Rright
    (canonicalFactorizedParametrixValid
      M ρ lam ε A Qfactor Rleft Rright)
    ε

/-- Fully instantiated probability bound for the canonical finite
parametrix.  The only unclosed hypotheses are exactly P-3.5b/Fubini,
P-wick, P-3.5b-det, and the P-err/physical-operator bridge plus its
first-moment remainder estimate. -/
theorem measureReal_compl_canonicalL2ParametrixGoodEvent_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (Qfactor Rleft Rright :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
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
    (hintR :
      Integrable
        (fun ω => ‖Rleft ω‖ + ‖Rright ω‖)
        (volume : Measure M.Ω))
    (δR : ℝ)
    (hfirstR :
      (∫ ω, ‖Rleft ω‖ + ‖Rright ω‖
        ∂(volume : Measure M.Ω)) ≤ δR)
    (hvalid :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        canonicalFactorizedParametrixValid
          M ρ lam ε A Qfactor Rleft Rright ω) :
    (volume : Measure M.Ω).real
        (canonicalL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft Rright)ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε A /
        (ε ^ (-14 : ℤ)) ^ 2 +
      δR / ε ^ 28 := by
  exact
    measureReal_compl_quantitativeL2ParametrixGoodEvent_le
      (volume : Measure M.Ω)
      (canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A)
      Rleft Rright
      (canonicalFactorizedParametrixValid
        M ρ lam ε A Qfactor Rleft Rright)
      ε
      (canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
        outerConstant powerConstant lam ε A)
      δR hε
      (integrable_normSq_canonicalPhysicalTruncatedParametrixL2Operator
        hfubini hwick hdet
        houter hpower hlam hε hεle)
      hintR
      (integral_normSq_canonicalPhysicalTruncatedParametrixL2Operator_le
        hfubini hwick hdet
        houter hpower hlam hε hεle)
      hfirstR hvalid

/-- If the finite-sum budget and the two remainders have the powers
used in paper (3.32), the exceptional set is at most `2 ε²`.
The explicit factor two records the union bound. -/
theorem measureReal_compl_canonicalL2ParametrixGoodEvent_le_two_mul_sq
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (Qfactor Rleft Rright :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
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
    (hbudget :
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε A ≤
        ε ^ (-24 : ℤ))
    (hintR :
      Integrable
        (fun ω => ‖Rleft ω‖ + ‖Rright ω‖)
        (volume : Measure M.Ω))
    (hfirstR :
      (∫ ω, ‖Rleft ω‖ + ‖Rright ω‖
        ∂(volume : Measure M.Ω)) ≤ ε ^ 30)
    (hvalid :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        canonicalFactorizedParametrixValid
          M ρ lam ε A Qfactor Rleft Rright ω) :
    (volume : Measure M.Ω).real
        (canonicalL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft Rright)ᶜ ≤
      2 * ε ^ 2 := by
  calc
    (volume : Measure M.Ω).real
        (canonicalL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft Rright)ᶜ ≤
        canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
            outerConstant powerConstant lam ε A /
          (ε ^ (-14 : ℤ)) ^ 2 +
        ε ^ 30 / ε ^ 28 :=
      measureReal_compl_canonicalL2ParametrixGoodEvent_le
        Qfactor Rleft Rright
        hfubini hwick hdet
        houter hpower hlam hε hεle
        hintR (ε ^ 30) hfirstR hvalid
    _ ≤ ε ^ (-24 : ℤ) /
          (ε ^ (-14 : ℤ)) ^ 2 +
        ε ^ 30 / ε ^ 28 := by
      gcongr
    _ = ε ^ 4 + ε ^ 2 := by
      field_simp [ne_of_gt hε]
    _ ≤ ε ^ 2 + ε ^ 2 := by
      exact add_le_add
        (pow_le_pow_of_le_one hε.le hεle (by norm_num))
        le_rfl
    _ = 2 * ε ^ 2 := by ring

/-! ## Inversion using the left correction -/

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

omit [Nontrivial H] in
/-- Left-corrected version of the inverse formula.  This orientation is
the one whose error is controlled by the norm of the physical
parametrix `Q * G`. -/
theorem inverseGreen_eq_correctedParametrixLeft_mul
    (G M Q Rleft Rright : H →L[ℂ] H)
    (hdata : AndersonParametrixData G M Q Rleft Rright)
    (hRleft : ‖Rleft‖ < 1)
    (hRright : ‖Rright‖ < 1) :
    inverseGreen G M
        (lopInvertible_of_parametrix_remainders
          G M Q Rleft Rright hdata hRleft hRright) =
      oneAddNeumannInverse Rleft hRleft * Q * G := by
  rw [inverseGreen_eq_correctedParametrix_mul
    G M Q Rleft Rright hdata hRleft hRright]
  rw [← correctedParametrixLeftInverse_eq_rightInverse
    (1 - Kop G M) Q Rleft Rright
    hdata.rightIdentity hdata.leftIdentity hRleft hRright]
  rfl

/-- Quantitative left-corrected error, depending on `‖QG‖` rather than
the auxiliary factorized norm `‖Q‖`. -/
theorem norm_inverseGreen_sub_parametrix_mul_le_two_left
    (G M Q Rleft Rright : H →L[ℂ] H)
    (hdata : AndersonParametrixData G M Q Rleft Rright)
    (hRleft : ‖Rleft‖ < 1 / 2)
    (hRright : ‖Rright‖ < 1 / 2) :
    ‖inverseGreen G M
        (lopInvertible_of_parametrix_remainders
          G M Q Rleft Rright hdata
            (hRleft.trans (by norm_num))
            (hRright.trans (by norm_num))) -
      Q * G‖ ≤
        2 * ‖Rleft‖ * ‖Q * G‖ := by
  let hRl : ‖Rleft‖ < 1 := hRleft.trans (by norm_num)
  let hRr : ‖Rright‖ < 1 := hRright.trans (by norm_num)
  rw [inverseGreen_eq_correctedParametrixLeft_mul
    G M Q Rleft Rright hdata hRl hRr]
  have hfactor :
      oneAddNeumannInverse Rleft hRl * Q * G - Q * G =
        (oneAddNeumannInverse Rleft hRl - 1) * (Q * G) := by
    rw [sub_mul, one_mul, mul_assoc]
  rw [hfactor]
  calc
    ‖(oneAddNeumannInverse Rleft hRl - 1) * (Q * G)‖ ≤
        ‖oneAddNeumannInverse Rleft hRl - 1‖ * ‖Q * G‖ :=
      norm_mul_le _ _
    _ ≤
        ((1 - ‖Rleft‖)⁻¹ * ‖Rleft‖) * ‖Q * G‖ := by
      gcongr
      exact norm_oneAddNeumannInverse_sub_one_le Rleft hRl
    _ ≤ (2 * ‖Rleft‖) * ‖Q * G‖ := by
      gcongr
      have hden : 0 < 1 - ‖Rleft‖ := sub_pos.mpr hRl
      rw [inv_le_iff_one_le_mul₀ hden]
      nlinarith
    _ = 2 * ‖Rleft‖ * ‖Q * G‖ := by ring

/-! ## Pointwise canonical inversion on the good event -/

theorem lopInvertible_on_canonicalL2ParametrixGoodEvent
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft Rright :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hεpow : ε ^ 28 < 1 / 2)
    {ω : M.Ω}
    (hω : ω ∈ canonicalL2ParametrixGoodEvent
      M ρ lam ε A Qfactor Rleft Rright) :
    LopInvertible greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω) := by
  change
    ‖canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω‖ ≤ ε ^ (-14 : ℤ) ∧
      ‖Rleft ω‖ + ‖Rright ω‖ ≤ ε ^ 28 ∧
      canonicalFactorizedParametrixValid
        M ρ lam ε A Qfactor Rleft Rright ω at hω
  rcases hω with ⟨hPbound, hRbound, hvalid⟩
  rcases hvalid with ⟨hdata, _hbridge⟩
  have hsmall :
      ω ∈ twoSidedParametrixGoodEvent Rleft Rright :=
    paperScaleParametrixGoodEvent_subset_twoSided
      (canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A)
      Rleft Rright ε hεpow ⟨hPbound, hRbound⟩
  exact lopInvertible_of_parametrix_remainders
    greenL2Op
    (mollifiedPotentialL2Op M ρ lam ε ω)
    (Qfactor ω) (Rleft ω) (Rright ω)
    hdata
    (hsmall.1.trans (by norm_num))
    (hsmall.2.trans (by norm_num))

/-- Paper (3.33), now attached to the canonical coefficient operator
and requiring P-err only through the validity conjunct of the event. -/
theorem norm_inverseGreen_sub_canonicalParametrix_on_goodEvent
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (A : ℕ)
    (Qfactor Rleft Rright :
      M.Ω → TorusL2 →L[ℂ] TorusL2)
    (hεpos : 0 < ε)
    (hεsmall : 2 * ε ^ 2 ≤ 1)
    (hεpow : ε ^ 28 < 1 / 2)
    {ω : M.Ω}
    (hω : ω ∈ canonicalL2ParametrixGoodEvent
      M ρ lam ε A Qfactor Rleft Rright) :
    ‖inverseGreen greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
        (lopInvertible_on_canonicalL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft Rright hεpow hω) -
      canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω‖ ≤
      ε ^ 12 := by
  letI : Nontrivial TorusL2 :=
    nontrivial_of_ne (torusFourierBasis (0 : Z4)) 0
      (torusFourierBasis.orthonormal.ne_zero 0)
  have hωcopy := hω
  change
    ‖canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω‖ ≤ ε ^ (-14 : ℤ) ∧
      ‖Rleft ω‖ + ‖Rright ω‖ ≤ ε ^ 28 ∧
      canonicalFactorizedParametrixValid
        M ρ lam ε A Qfactor Rleft Rright ω at hωcopy
  rcases hωcopy with ⟨hPbound, hRbound, hvalid⟩
  rcases hvalid with ⟨hdata, hbridge⟩
  have hsmall :
      ω ∈ twoSidedParametrixGoodEvent Rleft Rright :=
    paperScaleParametrixGoodEvent_subset_twoSided
      (canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A)
      Rleft Rright ε hεpow ⟨hPbound, hRbound⟩
  have hproof :
      lopInvertible_on_canonicalL2ParametrixGoodEvent
          M ρ lam ε A Qfactor Rleft Rright hεpow hω =
        lopInvertible_of_parametrix_remainders
          greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω)
          (Qfactor ω) (Rleft ω) (Rright ω)
          hdata
          (hsmall.1.trans (by norm_num))
          (hsmall.2.trans (by norm_num)) :=
    Subsingleton.elim _ _
  rw [hproof, ← hbridge]
  calc
    ‖inverseGreen greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω)
          (lopInvertible_of_parametrix_remainders
            greenL2Op
            (mollifiedPotentialL2Op M ρ lam ε ω)
            (Qfactor ω) (Rleft ω) (Rright ω)
            hdata
            (hsmall.1.trans (by norm_num))
            (hsmall.2.trans (by norm_num))) -
        Qfactor ω * greenL2Op‖ ≤
        2 * ‖Rleft ω‖ *
          ‖Qfactor ω * greenL2Op‖ :=
      norm_inverseGreen_sub_parametrix_mul_le_two_left
        greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)
        (Qfactor ω) (Rleft ω) (Rright ω)
        hdata hsmall.1 hsmall.2
    _ ≤ 2 * ε ^ 28 * ε ^ (-14 : ℤ) := by
      gcongr
      · exact
          (le_add_of_nonneg_right
            (norm_nonneg (Rright ω))).trans hRbound
      · rw [hbridge]
        exact hPbound
    _ = (2 * ε ^ 2) * ε ^ 12 := by
      field_simp [ne_of_gt hεpos]
    _ ≤ 1 * ε ^ 12 :=
      mul_le_mul_of_nonneg_right hεsmall
        (pow_nonneg hεpos.le 12)
    _ = ε ^ 12 := one_mul _

end

end Anderson4D
