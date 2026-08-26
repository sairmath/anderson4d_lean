import Anderson4D.DetParametrix.Core.Estimates
import Anderson4D.DetParametrix.Core.ReductionEndpoints
import Anderson4D.Continuum.CellSingular
import Anderson4D.Continuum.PrimitiveMajorantIntegral

/-!
# Final deterministic estimate ledgers

This file closes the numerical end of the deterministic reductions in
Deng--Shen, Sections 4.1--4.2.  It deliberately separates the two logically
different parts of R-322:

* `RenormReductionOutput` is the off-diagonal pointwise output (4.15)
  supplied by the interval reduction from Proposition 4.1;
* the theorems below integrate that output, justify every exchange of a
  finite sum and an integral, and absorb the remaining universal multiplier
  into the exponential constant.  Their conclusion has exactly the
  `ε⁻² |log ε|⁻¹ (C λ)^(2q)` shape of (3.22).

Thus no hypothesis merely restates (3.22).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The exact off-diagonal pointwise output of R-322 -/

/-- The output which paper (4.15) supplies after the Dyck-interval reduction.

The first field is the analytic side condition needed to exchange the finite
pairing sum and the spatial integral.  The second field is the exact
grouped form of (4.15): for each endpoint/Dyck signature one first sums over
the compatible primitive pairings, then takes the absolute value, and only
then sums over signatures.  This order is essential because Proposition 4.1
bounds the primitive-pairing sum rather than the sum of its termwise
absolute values.

The predicate packages iterative primitive-block removal and the three
Taylor/symmetry cases (4.10)--(4.12). The estimate is stated away from `z = 0`, matching
the inverse-square estimate in the paper; that single Haar-null point is
discarded only when the bound is integrated below. -/
def endpointFiberDetJSum
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (s : Finset (Fin (2 * q)) × Finset (Fin (2 * q)))
    (z : T4) : ℝ :=
  ∑ σ ∈ nonSplitPairings q with
      reductionEndpointSignature σ = s,
    detJ ρ lam ε q σ z 0

def groupedDetJAbsSum
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ) (z : T4) : ℝ :=
  ∑ s ∈ nonSplitReductionEndpointSignatures q,
    |endpointFiberDetJSum ρ lam ε q s z|

def RenormReductionOutput
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  (∀ σ ∈ nonSplitPairings q,
      Integrable (fun z : T4 => detJ ρ lam ε q σ z 0)
        paperMeasure) ∧
    ∀ z : T4, z ≠ 0 →
      groupedDetJAbsSum ρ lam ε q z ≤
        primitiveKernelMajorant primitiveConstant lam ε
          supportConstant q z

/-! ## Discharging the endpoint-signature count -/

/-- The exact fixed-signature analytic output left after Step 1 of the
R-322 reduction.  Unlike `RenormReductionOutput`, the pointwise bound is
required separately for each realized endpoint signature. -/
def RenormFiberReductionOutput
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  (∀ σ ∈ nonSplitPairings q,
      Integrable (fun z : T4 => detJ ρ lam ε q σ z 0)
        paperMeasure) ∧
    ∀ s ∈ nonSplitReductionEndpointSignatures q,
      ∀ z : T4, z ≠ 0 →
        |endpointFiberDetJSum ρ lam ε q s z| ≤
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z

/-- Summing the fixed-signature estimate costs exactly the coarse
`4^(2q)` factor from Step 1, which is absorbed by replacing the
primitive constant `C` with `4C`. -/
theorem RenormFiberReductionOutput.toRenormReductionOutput
    {ρ : SmoothCutoff} {lam ε : ℝ} {q : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (hred : RenormFiberReductionOutput ρ lam ε q
      primitiveConstant supportConstant) :
    RenormReductionOutput ρ lam ε q
      (4 * primitiveConstant) supportConstant := by
  refine ⟨hred.1, fun z hz => ?_⟩
  unfold groupedDetJAbsSum
  calc
    (∑ s ∈ nonSplitReductionEndpointSignatures q,
        |endpointFiberDetJSum ρ lam ε q s z|) ≤
        ∑ _s ∈ nonSplitReductionEndpointSignatures q,
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z :=
      Finset.sum_le_sum fun s hs => hred.2 s hs z hz
    _ =
        ((nonSplitReductionEndpointSignatures q).card : ℝ) *
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * q) *
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          card_nonSplitReductionEndpointSignatures_le q
      · exact primitiveKernelMajorant_nonneg hC hlam
    _ = primitiveKernelMajorant
          (4 * primitiveConstant) lam ε supportConstant q z := by
      unfold primitiveKernelMajorant
      rw [show (4 * primitiveConstant) * lam =
          4 * (primitiveConstant * lam) by ring,
        mul_pow]
      ring

/-- The off-diagonal pointwise R-322 output dominates the exact
renormalization constant after integration.  The proof preserves the
paper's order of operations:
regroup by endpoint signature, sum within each fiber, take absolute values,
then sum over signatures.  All finite-sum/integral interchanges are licensed
by the integrability field of `RenormReductionOutput`; the omitted point
`z = 0` is Haar-null. -/
theorem abs_renormC2q_le_integral_primitiveKernelMajorant
    {ρ : SmoothCutoff} {lam ε : ℝ} {q : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε)
    (hred : RenormReductionOutput ρ lam ε q
      primitiveConstant supportConstant) :
    |renormC2q ρ lam ε q| ≤
      ∫ z, primitiveKernelMajorant primitiveConstant lam ε
        supportConstant q z ∂paperMeasure := by
  let fiber :
      (Finset (Fin (2 * q)) × Finset (Fin (2 * q))) →
        T4 → ℝ :=
    fun s z =>
      endpointFiberDetJSum ρ lam ε q s z
  have hfiberInt :
      ∀ s ∈ nonSplitReductionEndpointSignatures q,
        Integrable (fiber s) paperMeasure := by
    intro s hs
    apply integrable_finsetSum
    intro σ hσ
    exact hred.1 σ (Finset.mem_filter.mp hσ).1
  have hfiberAbsInt :
      ∀ s ∈ nonSplitReductionEndpointSignatures q,
        Integrable (fun z => |fiber s z|) paperMeasure := by
    intro s hs
    simpa only [Real.norm_eq_abs] using
      (hfiberInt s hs).norm
  have hsumInt :
      Integrable
        (fun z : T4 =>
          ∑ s ∈ nonSplitReductionEndpointSignatures q,
            |fiber s z|)
        paperMeasure := by
    apply integrable_finsetSum
    intro s hs
    exact hfiberAbsInt s hs
  calc
    |renormC2q ρ lam ε q| =
        |∑ s ∈ nonSplitReductionEndpointSignatures q,
          ∑ σ ∈ nonSplitPairings q with
            reductionEndpointSignature σ = s,
            ∫ z, detJ ρ lam ε q σ z 0 ∂paperMeasure| := by
      rw [renormC2q_eq_sum]
      simp only [renormC2qTerm]
      rw [← sum_nonSplitPairings_by_endpointSignature]
    _ ≤ ∑ s ∈ nonSplitReductionEndpointSignatures q,
          |∑ σ ∈ nonSplitPairings q with
            reductionEndpointSignature σ = s,
            ∫ z, detJ ρ lam ε q σ z 0 ∂paperMeasure| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ nonSplitReductionEndpointSignatures q,
          ∫ z, |fiber s z| ∂paperMeasure := by
      apply Finset.sum_le_sum
      intro s hs
      have hfiberIntegral :
          (∑ σ ∈ nonSplitPairings q with
              reductionEndpointSignature σ = s,
              ∫ z, detJ ρ lam ε q σ z 0 ∂paperMeasure) =
            ∫ z, fiber s z ∂paperMeasure := by
        symm
        exact integral_finsetSum _ fun σ hσ =>
          hred.1 σ (Finset.mem_filter.mp hσ).1
      rw [hfiberIntegral]
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := paperMeasure) (fiber s))
    _ = ∫ z,
          ∑ s ∈ nonSplitReductionEndpointSignatures q,
            |fiber s z| ∂paperMeasure := by
      symm
      exact integral_finsetSum _ hfiberAbsInt
    _ ≤ ∫ z, primitiveKernelMajorant primitiveConstant lam ε
          supportConstant q z ∂paperMeasure := by
      apply integral_mono_ae hsumInt
        (integrable_primitiveKernelMajorant primitiveConstant lam ε
          supportConstant q hε)
      filter_upwards
          [compl_mem_ae_iff.mpr
            (paperMeasure_singleton (0 : T4))] with z hz
      apply hred.2 z
      intro hzero
      exact hz hzero

/-! ## Integration and absorption of universal constants -/

/-- Raw integrated form of (4.15).  The constants `Cball` and `Creg` are
chosen once and are independent of the cutoff support radius, scale,
coupling, perturbative order, and pointwise primitive constant. -/
theorem exists_abs_renormC2q_le_raw :
    ∃ Cball Creg : ℝ, 0 < Cball ∧ 0 < Creg ∧
      ∀ (ρ : SmoothCutoff) (primitiveConstant supportConstant lam ε : ℝ)
        (q : ℕ),
        0 < ε → 0 < supportConstant → 1 ≤ |Real.log ε| →
        RenormReductionOutput ρ lam ε q
          primitiveConstant supportConstant →
          |renormC2q ρ lam ε q| ≤
            (primitiveConstant * lam) ^ (2 * q) *
              ((Cball * supportConstant ^ 2 + Creg) *
                ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveKernelMajorant_le
  refine ⟨Cball, Creg, hCball, hCreg, ?_⟩
  intro ρ primitiveConstant supportConstant lam ε q hε hs hlog hred
  exact
    (abs_renormC2q_le_integral_primitiveKernelMajorant hε hred).trans
      (hmajorant primitiveConstant lam ε supportConstant q hε hs hlog)

/-- A nonnegative order-independent multiplier can be absorbed into the
base of an even power at every positive perturbative order. -/
theorem mul_constant_le_absorbed_even_pow
    {base K : ℝ} {q : ℕ}
    (hbase : 0 ≤ base) (hK : 0 ≤ K) (hq : 1 ≤ q) :
    base ^ (2 * q) * K ≤ (base * (K + 1)) ^ (2 * q) := by
  have hKone : 1 ≤ K + 1 := by linarith
  have hKsq : K ≤ (K + 1) ^ 2 := by
    nlinarith [sq_nonneg K]
  have hsqpow : (K + 1) ^ 2 ≤ (K + 1) ^ (2 * q) :=
    pow_le_pow_right₀ hKone (by omega)
  calc
    base ^ (2 * q) * K ≤
        base ^ (2 * q) * (K + 1) ^ (2 * q) :=
      mul_le_mul_of_nonneg_left (hKsq.trans hsqpow)
        (pow_nonneg hbase _)
    _ = (base * (K + 1)) ^ (2 * q) := by
      rw [mul_pow]

/-- **Numerical closure of R-322, paper (3.22).**

For a fixed cutoff support constant and primitive-estimate constant, the
universal integration constants are absorbed into one positive named
constant, chosen before `λ`, `ε`, and `q`.  The only remaining premise is
the genuinely off-diagonal pointwise reduction output (4.15), which is
sufficient because the numerical closure uses it only under an integral. -/
theorem exists_renormC_bound_of_reduction
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ Crenorm : ℝ, 0 < Crenorm ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ),
        0 ≤ lam → 0 < ε → 1 ≤ |Real.log ε| → 1 ≤ q →
        RenormReductionOutput ρ lam ε q
          primitiveConstant supportConstant →
          |renormC2q ρ lam ε q| ≤
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ (2 * q) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hraw⟩ :=
    exists_abs_renormC2q_le_raw
  let K : ℝ := Cball * supportConstant ^ 2 + Creg
  let Crenorm : ℝ := primitiveConstant * (K + 1)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hCrenorm : 0 < Crenorm := by
    dsimp only [Crenorm]
    positivity
  refine ⟨Crenorm, hCrenorm, ?_⟩
  intro ρ lam ε q hlam hε hlog hq hred
  have hraw' :=
    hraw ρ primitiveConstant supportConstant lam ε q
      hε hsupport hlog hred
  have hscale : 0 ≤ ε⁻¹ ^ (2 : ℕ) / |Real.log ε| := by
    positivity
  have habsorb :
      (primitiveConstant * lam) ^ (2 * q) * K ≤
        (Crenorm * lam) ^ (2 * q) := by
    have h :=
      mul_constant_le_absorbed_even_pow
        (base := primitiveConstant * lam) (K := K)
        (mul_nonneg hprimitive.le hlam) hK.le hq
    dsimp only [Crenorm]
    convert h using 1
    ring
  calc
    |renormC2q ρ lam ε q| ≤
        (primitiveConstant * lam) ^ (2 * q) *
          (K * ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) := by
      simpa only [K] using hraw'
    _ = ((primitiveConstant * lam) ^ (2 * q) * K) *
          (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) := by ring
    _ ≤ (Crenorm * lam) ^ (2 * q) *
          (ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) :=
      mul_le_mul_of_nonneg_right habsorb hscale
    _ = ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
          (Crenorm * lam) ^ (2 * q) := by ring

/-! ## R-324: exact frequency-decay ledger -/

/-- Embed a left-copy internal index into the doubled carrier used by the
deterministic Wick pairing sum. -/
def leftMomentIndex {m : ℕ} (i : Fin m) : Fin (2 * m) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Embed a right-copy internal index into the doubled carrier used by the
deterministic Wick pairing sum. -/
def rightMomentIndex {m : ℕ} (i : Fin m) : Fin (2 * m) :=
  ⟨m + i.val, by have := i.isLt; omega⟩

/-- The cross-covariance factors produced by a bijection between the
single indices of two partial pairings.  Together with the covariance
factors already present in the two `detIntegrand`s, this is the full
pairing of the doubled carrier described between (4.16) and (4.18). -/
def momentCrossCovarianceProduct
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∏ i : ↥κp.singles,
    ρ.etaEpsT4 ε
      (v (leftMomentIndex i.val) -
        v (rightMomentIndex (π i).val))

/-- One deterministic integrand in the second moment of the order-`m`
parametrix coefficient.

The four characters combine to
`exp(i α·(x-z) + i β·(y-w))` as in (4.18).  The two closed deterministic
profiles contain the within-copy pairing factors; `π` supplies exactly the
cross-copy Wick contractions. -/
def deterministicMomentIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  charT4 α x * charT4 β y * charT4 (-α) z * charT4 (-β) w *
    ((detIntegrand ρ ε m κp
        (assemble x y fun i => v (leftMomentIndex i)) *
      detIntegrand ρ ε m κm
        (assemble z w fun i => v (rightMomentIndex i)) *
      momentCrossCovarianceProduct ρ ε m κp κm π v : ℝ) : ℂ)

/-- **Concrete L3 deterministic pairing sum underlying (3.24).**

This is the result of the Wick reduction before probability is introduced:
sum over the two within-copy partial pairings and over every bijection of
their single sets, followed by the physical integral (4.18).  If the single
sets have different cardinalities the `Equiv` sum is empty, as required.
The global `λ_ε^(2m)` is kept exactly once outside the profiles.

The Wick reduction identifies the second moment of `pmCoeff` with this
quantity.  R-324 is the purely deterministic task of bounding its norm. -/
def deterministicMomentPairingSum
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) : ℂ :=
  (lamEps lam ε ^ (2 * m) : ℂ) *
    ∑ κp : PartialPairing (Fin m),
      ∑ κm : PartialPairing (Fin m),
        ∑ π : κp.singles ≃ κm.singles,
          ∫ x, ∫ y, ∫ z, ∫ w,
            ∫ v : Fin (2 * m) → T4,
              deterministicMomentIntegrand ρ ε m α β κp κm π
                x y z w v
              ∂(Measure.pi fun _ => paperMeasure)
            ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure

/-- Euclidean size of a Fourier mode in `ℤ⁴`. -/
def z4FrequencyNorm (k : Z4) : ℝ :=
  ‖fun i : Fin dim => (k i : ℝ)‖

theorem z4FrequencyNorm_nonneg (k : Z4) :
    0 ≤ z4FrequencyNorm k :=
  norm_nonneg _

/-- The endpoint multiplier `⟨k⟩⁻⁴` from (3.24), in a form avoiding
fractional real powers. -/
def fourthOrderModeDecay (k : Z4) : ℝ :=
  ((1 + z4FrequencyNorm k ^ 2) ^ 2)⁻¹

theorem fourthOrderModeDecay_nonneg (k : Z4) :
    0 ≤ fourthOrderModeDecay k := by
  unfold fourthOrderModeDecay
  positivity

theorem fourthOrderModeDecay_le_one (k : Z4) :
    fourthOrderModeDecay k ≤ 1 := by
  unfold fourthOrderModeDecay
  have hpos : 0 < (1 + z4FrequencyNorm k ^ 2) ^ 2 := by
    positivity
  rw [inv_le_one₀ hpos]
  nlinarith [sq_nonneg (z4FrequencyNorm k),
    sq_nonneg (1 + z4FrequencyNorm k ^ 2)]

/-- The complete decay branch printed in (3.24):
`ε⁻⁸ ⟨α⟩⁻⁴ ⟨β⟩⁻⁴ ⟨ε²(α+β)⟩⁻⁸`. -/
def deterministicMomentDecay
    (ε : ℝ) (α β : Z4) : ℝ :=
  ε⁻¹ ^ (8 : ℕ) *
    fourthOrderModeDecay α *
    fourthOrderModeDecay β *
    eighthOrderFrequencyDecay
      (ε ^ 2 * z4FrequencyNorm (α + β))

theorem deterministicMomentDecay_nonneg
    (ε : ℝ) (α β : Z4) :
    0 ≤ deterministicMomentDecay ε α β := by
  unfold deterministicMomentDecay
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by positivity) (fourthOrderModeDecay_nonneg α))
      (fourthOrderModeDecay_nonneg β))
    (eighthOrderFrequencyDecay_nonneg _)

/-- Exact deterministic right side underlying (3.24).  `outerConstant`
is the paper's leading absolute `C`, while `powerConstant` is the constant
inside `(Cλ)^(2m-2)`; keeping them distinct follows DESIGN §5.4's named
constant policy. -/
def deterministicMomentRHS
    (outerConstant powerConstant lam ε : ℝ) (m : ℕ)
    (α β : Z4) : ℝ :=
  lamEps lam ε ^ 2 * outerConstant *
    (powerConstant * lam) ^ (2 * m - 2) *
    min 1 (deterministicMomentDecay ε α β)

theorem deterministicMomentRHS_nonneg
    {outerConstant powerConstant lam ε : ℝ} {m : ℕ}
    {α β : Z4}
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam) :
    0 ≤ deterministicMomentRHS
      outerConstant powerConstant lam ε m α β := by
  unfold deterministicMomentRHS
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (sq_nonneg _) houter)
      (pow_nonneg (mul_nonneg hpower hlam) _))
    (le_min zero_le_one
      (deterministicMomentDecay_nonneg ε α β))

/-- The frequency-routing statement at the actual truncation length,
already converted to the exact eighth-order payoff in (3.24). -/
theorem exists_increment_with_eighth_order_payoff
    {E : Type*} [SeminormedAddCommGroup E]
    (N : ℕ) (hN : 0 < N) (δ : Fin N → E)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hNtrunc : N ≤ truncOrder ε) :
    ∃ i : Fin N,
      eighthOrderFrequencyDecay ‖δ i‖ ≤
        eighthOrderFrequencyDecay
          (ε ^ 2 * ‖∑ j, δ j‖) := by
  obtain ⟨i, hi⟩ :=
    exists_frequency_increment_at_truncation_scale
      N hN δ ε hε (hεsmall.trans (by norm_num)) hNtrunc
  refine ⟨i, ?_⟩
  exact truncation_routed_decay_le_eps_sq_decay
    hε hεsmall (norm_nonneg _) hi

/-- Frequency routing remains valid after multiplying by the two endpoint
decays and the explicit `ε⁻⁸` loss.  The equality premise is the algebraic
composition identity identifying the telescoping shift with `α+β`. -/
theorem exists_increment_with_full_moment_decay
    {E : Type*} [SeminormedAddCommGroup E]
    (N : ℕ) (hN : 0 < N) (δ : Fin N → E)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hNtrunc : N ≤ truncOrder ε)
    (α β : Z4)
    (htotal : ‖∑ j, δ j‖ = z4FrequencyNorm (α + β)) :
    ∃ i : Fin N,
      ε⁻¹ ^ (8 : ℕ) *
          fourthOrderModeDecay α *
          fourthOrderModeDecay β *
          eighthOrderFrequencyDecay ‖δ i‖ ≤
        deterministicMomentDecay ε α β := by
  obtain ⟨i, hi⟩ :=
    exists_increment_with_eighth_order_payoff
      N hN δ ε hε hεsmall hNtrunc
  refine ⟨i, ?_⟩
  unfold deterministicMomentDecay
  apply mul_le_mul_of_nonneg_left
  · simpa only [htotal] using hi
  · exact mul_nonneg
      (mul_nonneg (by positivity) (fourthOrderModeDecay_nonneg α))
      (fourthOrderModeDecay_nonneg β)

/-! ## Combining the two R-324 branches -/

/-- A uniform estimate and a frequency-decaying estimate combine to a
single `min` estimate.  This elementary but essential ledger prevents the
two separately proved branches of paper §4.2 from being accidentally
added (which would lose the stated decay). -/
theorem le_mul_min_of_le_of_le_mul
    {value amplitude decay : ℝ}
    (huniform : value ≤ amplitude)
    (hdecay : value ≤ amplitude * decay) :
    value ≤ amplitude * min 1 decay := by
  by_cases h : decay ≤ 1
  · rw [min_eq_right h]
    exact hdecay
  · rw [min_eq_left (le_of_not_ge h)]
    simpa using huniform

/-- **Numerical closure of the two deterministic branches in R-324.**

The premises are the outputs of Steps 1--3 (uniform branch) and Step 4
(frequency branch) for the *same concrete deterministic pairing sum*.
The conclusion is exactly the P-3.5b-det right side, including
`λ_ε² C(Cλ)^(2m-2)` and the minimum with the three decay factors.

This theorem quantifies over the value of the concrete sum so that the
numerical combination of the uniform and decay branches is independent of
its realization. -/
theorem deterministicMoment_bound_of_two_branches
    {value outerConstant powerConstant lam ε : ℝ}
    {m : ℕ} {α β : Z4}
    (huniform :
      value ≤ lamEps lam ε ^ 2 * outerConstant *
        (powerConstant * lam) ^ (2 * m - 2))
    (hdecay :
      value ≤
        (lamEps lam ε ^ 2 * outerConstant *
          (powerConstant * lam) ^ (2 * m - 2)) *
            deterministicMomentDecay ε α β) :
    value ≤ deterministicMomentRHS
      outerConstant powerConstant lam ε m α β := by
  unfold deterministicMomentRHS
  exact le_mul_min_of_le_of_le_mul huniform hdecay

/-- Concrete specialization of the two-branch ledger to the deterministic
pairing sum (4.18), combining its uniform and routed R-324 estimates. -/
theorem deterministicMomentPairingSum_bound_of_two_branches
    {ρ : SmoothCutoff} {outerConstant powerConstant lam ε : ℝ}
    {m : ℕ} {α β : Z4}
    (huniform :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        lamEps lam ε ^ 2 * outerConstant *
          (powerConstant * lam) ^ (2 * m - 2))
    (hdecay :
      ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        (lamEps lam ε ^ 2 * outerConstant *
          (powerConstant * lam) ^ (2 * m - 2)) *
            deterministicMomentDecay ε α β) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      deterministicMomentRHS
        outerConstant powerConstant lam ε m α β :=
  deterministicMoment_bound_of_two_branches huniform hdecay

end

end Anderson4D
