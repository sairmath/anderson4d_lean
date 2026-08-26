import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveIterationClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorCoreEstimate

/-!
# General-order peel interface for the R-324 uniform branch

The uniform-branch obligation `MomentRefinedIntegratedReductionOutputAt`
demands, for every residual-refined fibre at order `m`, the inserted
Proposition 4.1 majorant on the right-hand side.  This file isolates the
one genuinely analytic input of the general-`m` case as a scalar
logarithmic ledger for the refined fibre sums and proves that this ledger
*exactly* funds the majorant:

* `|λ_ε|^{2m} = λ^{2m}/|log ε|^m` supplies `m` inverse logarithms;
* a fibre obeying `‖·‖ ≤ K^m |log ε|^{m-1}` therefore lands at
  `K^m λ^{2m}/|log ε|`;
* the integrated inserted majorant is at least
  `(C₀ λ)^{2m}/|log ε|` at support constant `1`
  (`le_integral_primitiveInsertedMajorant`), so the geometric absorption
  `K^m ≤ (K+1)^{2m}` closes the estimate with the `m`-independent
  primitive constant `C₀ = K + 1`.

No triangle inequality across fibres and no factorial count appears:
the ledger is stated for the summed fibre, matching the
cancellation-preserving interface of `R324PrimitiveIterationClosure`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The general-order fibre ledger -/

/-- **The per-fibre logarithmic ledger at order `m`.**  Each
residual-refined fibre sum, taken before any norm is moved inside, is
bounded by `K^m |log ε|^{m-1}`: one geometric factor per order and one
logarithm per block beyond the first, exactly the paper Section 4.2
Step 2--3 output. -/
def R324GeneralPeelFibreLogBound
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (K : ℝ) : Prop :=
  ∀ s ∈ momentContractionSignatures m,
    ∀ r ∈ momentResidualChainSignaturesAt m s,
      ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
        K ^ m * |Real.log ε| ^ (m - 1)

/-- The coupling weight splits into `m` inverse logarithms. -/
theorem r324GeneralPeel_abs_lamEps_pow
    (lam : ℝ) {ε : ℝ} (hlog : 1 ≤ |Real.log ε|) (m : ℕ) :
    |lamEps lam ε| ^ (2 * m) =
      lam ^ (2 * m) / |Real.log ε| ^ m := by
  have hL0 : (0 : ℝ) < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  unfold lamEps
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_pow]
  congr 1
  · rw [← abs_pow]
    exact abs_of_nonneg ((even_two_mul m).pow_nonneg lam)
  · rw [pow_mul, Real.sq_sqrt hL0.le]

/-! ## The ledger funds the inserted majorant -/

/-- **The general-order uniform-branch bridge.**  At every order
`m ≥ 1`, the per-fibre logarithmic ledger discharges the integrated
residual-refined reduction obligation with the `m`-independent primitive
constant `K + 1` and support constant `1`.  The `m` inverse logarithms
of `|λ_ε|^{2m}` pay for the `m - 1` fibre logarithms, and the last
inverse logarithm is matched by the near-field mass of the inserted
majorant. -/
theorem momentRefinedIntegratedReductionOutputAt_of_generalPeelFibreLogBound
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4} {K : ℝ}
    (hm : 1 ≤ m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hK : 0 ≤ K)
    (h : R324GeneralPeelFibreLogBound ρ ε m α β K) :
    MomentRefinedIntegratedReductionOutputAt
      ρ lam ε m α β (K + 1) 1 := by
  set L : ℝ := |Real.log ε| with hLdef
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hlog
  have hlampow : (0 : ℝ) ≤ lam ^ (2 * m) :=
    (even_two_mul m).pow_nonneg lam
  have hmajorant :=
    le_integral_primitiveInsertedMajorant
      (K + 1) lam ε 1 m hε hε1 one_pos
  have hmajorant' :
      (K + 1) ^ (2 * m) * lam ^ (2 * m) * (1 / L) ≤
        ∫ z, primitiveInsertedMajorant (K + 1) lam ε 1 m z
          ∂paperMeasure := by
    refine le_trans (le_of_eq ?_) hmajorant
    rw [min_self, one_pow, one_pow, one_mul, mul_pow, ← hLdef]
  refine ⟨⟨?_⟩⟩
  intro s hs r hr
  have hfib := h s hs r hr
  have habs :
      K ^ m ≤ (K + 1) ^ (2 * m) := by
    have hsq : K ≤ (K + 1) ^ 2 := by nlinarith [sq_nonneg K]
    calc
      K ^ m ≤ ((K + 1) ^ 2) ^ m :=
        pow_le_pow_left₀ hK hsq m
      _ = (K + 1) ^ (2 * m) := by rw [← pow_mul]
  have hLsplit : L ^ m = L ^ (m - 1) * L := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  calc
    |lamEps lam ε| ^ (2 * m) *
        ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
        (lam ^ (2 * m) / L ^ m) * (K ^ m * L ^ (m - 1)) := by
      rw [r324GeneralPeel_abs_lamEps_pow lam hlog m, ← hLdef]
      exact mul_le_mul_of_nonneg_left hfib
        (div_nonneg hlampow (pow_nonneg hL0.le m))
    _ = K ^ m * lam ^ (2 * m) * (1 / L) := by
      rw [hLsplit]
      have hL1 : L ^ (m - 1) ≠ 0 := pow_ne_zero _ hL0.ne'
      field_simp
    _ ≤ (K + 1) ^ (2 * m) * lam ^ (2 * m) * (1 / L) := by
      have hrest : (0 : ℝ) ≤ lam ^ (2 * m) * (1 / L) := by
        positivity
      calc
        K ^ m * lam ^ (2 * m) * (1 / L) =
            K ^ m * (lam ^ (2 * m) * (1 / L)) := by ring
        _ ≤ (K + 1) ^ (2 * m) * (lam ^ (2 * m) * (1 / L)) :=
          mul_le_mul_of_nonneg_right habs hrest
        _ = (K + 1) ^ (2 * m) * lam ^ (2 * m) * (1 / L) := by
          ring
    _ ≤ ∫ z, primitiveInsertedMajorant (K + 1) lam ε 1 m z
          ∂paperMeasure := hmajorant'

/-! ## The uniform general-order ledger -/

/-- **The remaining general-order input, as one clean proposition.**
A single mollifier-dependent geometric constant funds the per-fibre
logarithmic ledger at every order and both external modes.  By
`momentRefinedIntegratedReductionOutputAt_of_generalPeelFibreLogBound`
this is precisely what separates the closed low orders from the full
uniform branch. -/
def R324GeneralPeelUniformLedger
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
      R324GeneralPeelFibreLogBound ρ ε m α β K

/-- **Strongest per-cutoff output form.**  One primitive constant,
chosen from the mollifier alone, discharges the uniform-branch
obligation at every order `m ≥ 1`, every coupling, every admissible
scale, and both external modes, at support constant `1`. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_of_uniformLedger
    (ρ : SmoothCutoff)
    (h : ∃ K : ℝ, 0 ≤ K ∧ R324GeneralPeelUniformLedger ρ K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε m α β C₀ 1 := by
  obtain ⟨K, hK, hled⟩ := h
  refine ⟨K + 1, by linarith, ?_⟩
  intro lam ε m α β hε hε1 hlog hm
  exact
    momentRefinedIntegratedReductionOutputAt_of_generalPeelFibreLogBound
      hm hε hε1 hlog hK (hled m α β hε hε1 hlog hm)

end

end Anderson4D
