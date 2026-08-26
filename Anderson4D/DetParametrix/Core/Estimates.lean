import Anderson4D.DetParametrix.Core.Constants
import Anderson4D.Continuum.PrimitiveSymmetry
import Anderson4D.DetParametrix.Core.FrequencyRouting
import Anderson4D.DetParametrix.Core.ReductionIteration
import Anderson4D.DetParametrix.Core.ReductionSymmetry

/-!
# Deterministic estimate bookkeeping for Proposition 3.5

This file supplies deterministic bookkeeping for blueprint nodes R-322,
P-3.5a, R-324 and P-3.5b-det. The first section isolates two reductions used
by the analytic proofs:

* the non-splitting pairing class in (3.10) is named once;
* the absolute value of each finite renormalization sum is reduced to the
  sum of absolute values, both at fixed order and after the truncation
  sum (3.11).

These are genuine consequences of the frozen definitions, with no
analytic bound inserted as a hypothesis.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The finite class over which the order-`2q` renormalization constant
is summed in (3.10). -/
def nonSplitPairings (q : ℕ) :
    Finset (PartialPairing (Fin (2 * q))) :=
  Finset.univ.filter IsNonSplit

@[simp] theorem mem_nonSplitPairings
    {q : ℕ} {σ : PartialPairing (Fin (2 * q))} :
    σ ∈ nonSplitPairings q ↔ IsNonSplit σ := by
  simp [nonSplitPairings]

/-- The nonnegative absolute-value form of the closed `J` integrand.
Only the extracted difference factors can change sign: free Green
factors and covariance factors are nonnegative. -/
def detJAbsIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (xtJ : Fin (2 * q) → T4) : ℝ :=
  (∏ e : Fin (2 * q - 1),
      if e.val ∈ ((extract σ).map fun p => p.2.val) then 1
      else if h : e.val + 1 < 2 * q then
        greenFn (xtJ ⟨e.val, by omega⟩ - xtJ ⟨e.val + 1, h⟩)
      else 1) *
    ((extract σ).map (fun p => |diffFactorJ xtJ p|)).prod *
    ∏ i ∈ σ.pairSupport.filter (fun i => i < σ i),
      ρ.etaEpsT4 ε (xtJ i - xtJ (σ i))

theorem detJAbsIntegrand_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (xtJ : Fin (2 * q) → T4) :
    0 ≤ detJAbsIntegrand ρ ε q σ xtJ := by
  unfold detJAbsIntegrand
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro e he
      split
      · positivity
      · split
        · exact greenFn_nonneg _
        · positivity
    · apply List.prod_nonneg
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      exact abs_nonneg _
  · apply Finset.prod_nonneg
    intro i hi
    exact ρ.etaEpsT4_nonneg ε _

/-- Absolute value distributes through the closed formula exactly. -/
theorem abs_detJintegrand_eq_detJAbsIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (xtJ : Fin (2 * q) → T4) :
    |detJintegrand ρ ε q σ xtJ| =
      detJAbsIntegrand ρ ε q σ xtJ := by
  have hchain :
      0 ≤ ∏ e : Fin (2 * q - 1),
        if e.val ∈ ((extract σ).map fun p => p.2.val) then 1
        else if h : e.val + 1 < 2 * q then
          greenFn (xtJ ⟨e.val, by omega⟩ -
            xtJ ⟨e.val + 1, h⟩)
        else 1 := by
    apply Finset.prod_nonneg
    intro e he
    split
    · positivity
    · split
      · exact greenFn_nonneg _
      · positivity
  have hdiff :
      |((extract σ).map (diffFactorJ xtJ)).prod| =
        ((extract σ).map
          (fun p => |diffFactorJ xtJ p|)).prod := by
    calc
      |((extract σ).map (diffFactorJ xtJ)).prod| =
          ‖((extract σ).map (diffFactorJ xtJ)).prod‖ := by
            rw [Real.norm_eq_abs]
      _ = (((extract σ).map (diffFactorJ xtJ)).map norm).prod :=
        ((extract σ).map (diffFactorJ xtJ)).norm_prod
      _ = ((extract σ).map
          (fun p => |diffFactorJ xtJ p|)).prod := by
        rw [List.map_map]
        apply congrArg List.prod
        apply List.map_congr_left
        intro p hp
        exact Real.norm_eq_abs _
  have hcov :
      0 ≤ ∏ i ∈ σ.pairSupport.filter (fun i => i < σ i),
        ρ.etaEpsT4 ε (xtJ i - xtJ (σ i)) := by
    apply Finset.prod_nonneg
    intro i hi
    exact ρ.etaEpsT4_nonneg ε _
  unfold detJintegrand detJAbsIntegrand
  rw [abs_mul, abs_mul]
  rw [abs_of_nonneg hchain, hdiff, abs_of_nonneg hcov]

/-- One summand of the order-`2q` renormalization constant. -/
def renormC2qTerm (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q))) : ℝ :=
  ∫ z, detJ ρ lam ε q σ z 0 ∂paperMeasure

/-- Move the absolute value through the final spatial integral in one
renormalization summand. -/
theorem abs_renormC2qTerm_le_integral_abs
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q))) :
    |renormC2qTerm ρ lam ε q σ| ≤
      ∫ z, |detJ ρ lam ε q σ z 0| ∂paperMeasure := by
  simpa only [renormC2qTerm, Real.norm_eq_abs] using
    (norm_integral_le_integral_norm
      (μ := paperMeasure)
      (fun z => detJ ρ lam ε q σ z 0))

/-- Move absolute values through the internal `J` integral at positive
order.  The even coupling power is retained exactly; no coarse constant
is introduced at this bookkeeping stage. -/
theorem abs_detJ_succ_le_integral_abs
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1)))) (z w : T4) :
    |detJ ρ lam ε (q + 1) σ z w| ≤
      |lamEps lam ε| ^ (2 * (q + 1)) *
        ∫ v : Fin (2 * q) → T4,
          |detJintegrand ρ ε (q + 1) σ
            (fun j =>
              assemble z w v
                (Fin.cast
                  (by omega : 2 * (q + 1) = 2 * q + 2) j))|
          ∂(Measure.pi fun _ => paperMeasure) := by
  rw [detJ, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := Measure.pi fun _ : Fin (2 * q) => paperMeasure)
          (fun v =>
            detJintegrand ρ ε (q + 1) σ
              (fun j =>
                assemble z w v
                  (Fin.cast
                    (by omega : 2 * (q + 1) = 2 * q + 2) j)))))
    (pow_nonneg (abs_nonneg _) _)

/-- Positive-integrand version of `abs_detJ_succ_le_integral_abs`, ready
for the primitive-interval reduction. -/
theorem abs_detJ_succ_le_integral_detJAbs
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1)))) (z w : T4) :
    |detJ ρ lam ε (q + 1) σ z w| ≤
      |lamEps lam ε| ^ (2 * (q + 1)) *
        ∫ v : Fin (2 * q) → T4,
          detJAbsIntegrand ρ ε (q + 1) σ
            (fun j =>
              assemble z w v
                (Fin.cast
                  (by omega : 2 * (q + 1) = 2 * q + 2) j))
          ∂(Measure.pi fun _ => paperMeasure) := by
  calc
    |detJ ρ lam ε (q + 1) σ z w| ≤
        |lamEps lam ε| ^ (2 * (q + 1)) *
          ∫ v : Fin (2 * q) → T4,
            |detJintegrand ρ ε (q + 1) σ
              (fun j =>
                assemble z w v
                  (Fin.cast
                    (by omega : 2 * (q + 1) = 2 * q + 2) j))|
            ∂(Measure.pi fun _ => paperMeasure) :=
      abs_detJ_succ_le_integral_abs ρ lam ε q σ z w
    _ = |lamEps lam ε| ^ (2 * (q + 1)) *
        ∫ v : Fin (2 * q) → T4,
          detJAbsIntegrand ρ ε (q + 1) σ
            (fun j =>
              assemble z w v
                (Fin.cast
                  (by omega : 2 * (q + 1) = 2 * q + 2) j))
          ∂(Measure.pi fun _ => paperMeasure) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with v
      exact abs_detJintegrand_eq_detJAbsIntegrand ρ ε (q + 1) σ _

/-- The named pairing class and summand recover the frozen definition
of `renormC2q` definitionally. -/
theorem renormC2q_eq_sum (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ) :
    renormC2q ρ lam ε q =
      ∑ σ ∈ nonSplitPairings q, renormC2qTerm ρ lam ε q σ := by
  rfl

/-- Triangle-inequality reduction for (3.22) at one perturbative order. -/
theorem abs_renormC2q_le_sum_abs
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ) :
    |renormC2q ρ lam ε q| ≤
      ∑ σ ∈ nonSplitPairings q, |renormC2qTerm ρ lam ε q σ| := by
  rw [renormC2q_eq_sum]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Integral majorant for the complete order-`2q` constant.  This is the
entry point of the interval-reduction argument in paper §4.1. -/
theorem abs_renormC2q_le_sum_integral_abs
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ) :
    |renormC2q ρ lam ε q| ≤
      ∑ σ ∈ nonSplitPairings q,
        ∫ z, |detJ ρ lam ε q σ z 0| ∂paperMeasure := by
  calc
    |renormC2q ρ lam ε q| ≤
        ∑ σ ∈ nonSplitPairings q,
          |renormC2qTerm ρ lam ε q σ| :=
      abs_renormC2q_le_sum_abs ρ lam ε q
    _ ≤ ∑ σ ∈ nonSplitPairings q,
          ∫ z, |detJ ρ lam ε q σ z 0| ∂paperMeasure := by
      exact Finset.sum_le_sum fun σ hσ =>
        abs_renormC2qTerm_le_integral_abs ρ lam ε q σ

/-- Triangle-inequality reduction after summing the explicit constants
over `1 ≤ q ≤ A`.  This is the deterministic ledger used in the
parametrix remainder estimate (3.21). -/
theorem abs_renormCEps_le_sum_abs
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    |renormCEps ρ lam ε| ≤
      ∑ q ∈ Finset.Icc 1 (truncOrder ε),
        |renormC2q ρ lam ε q| := by
  unfold renormCEps
  exact Finset.abs_sum_le_sum_abs _ _

/-- Combining the two finite triangle inequalities reduces the whole
renormalization constant to absolute values of individual `J` terms. -/
theorem abs_renormCEps_le_sum_pairing_abs
    (ρ : SmoothCutoff) (lam ε : ℝ) :
    |renormCEps ρ lam ε| ≤
      ∑ q ∈ Finset.Icc 1 (truncOrder ε),
        ∑ σ ∈ nonSplitPairings q,
          |renormC2qTerm ρ lam ε q σ| := by
  calc
    |renormCEps ρ lam ε| ≤
        ∑ q ∈ Finset.Icc 1 (truncOrder ε),
          |renormC2q ρ lam ε q| :=
      abs_renormCEps_le_sum_abs ρ lam ε
    _ ≤ ∑ q ∈ Finset.Icc 1 (truncOrder ε),
          ∑ σ ∈ nonSplitPairings q,
            |renormC2qTerm ρ lam ε q σ| := by
      exact Finset.sum_le_sum fun q hq =>
        abs_renormC2q_le_sum_abs ρ lam ε q

end

end Anderson4D
