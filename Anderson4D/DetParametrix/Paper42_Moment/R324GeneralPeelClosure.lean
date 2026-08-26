import Anderson4D.DetParametrix.Paper42_Moment.R324GeneralPeelInterface
import Anderson4D.DetParametrix.Paper42_Moment.R324GeneralPeelOrderOne
import Anderson4D.DetParametrix.Paper42_Moment.R324ComplementScheduleClosure

/-!
# Closure of the general peel ledger at the proved orders

This file instantiates the general peel interface:

* order one satisfies the fibre ledger unconditionally (no logarithm is
  spent), so `MomentRefinedIntegratedReductionOutputAt` holds at `m = 1`
  with a universal primitive constant;
* together with the proved unconditional order-two closure, both low
  orders hold at one common per-cutoff constant;
* consequently the *only* remaining uniform-branch obligation is the
  fibre ledger `R324GeneralPeelFibreLogBound` at orders `m ≥ 3`, and the
  final theorem turns any such ledger into the full uniform-branch
  output at every order `m ≥ 1` with one constant.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The order-one ledger -/

/-- **The order-one fibre ledger holds unconditionally.**  A refined
fibre contains at most the unique order-one contraction, whose term is
bounded by the paper volume; `K^1 |log ε|^0` demands no logarithm. -/
theorem r324GeneralPeel_fibreLogBound_one
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) :
    R324GeneralPeelFibreLogBound ρ ε 1 α β
      ((2 * Real.pi) ^ (dim : ℕ)) := by
  intro s _hs r _hr
  have hcard :
      ((momentRefinedContractionFiber 1 s r).card : ℝ) ≤ 1 := by
    have h :
        (momentRefinedContractionFiber 1 s r).card ≤ 1 := by
      calc
        (momentRefinedContractionFiber 1 s r).card ≤
            Fintype.card (MomentContraction 1) :=
          Finset.card_le_univ _
        _ = 1 := fintype_card_momentContraction_one
    exact_mod_cast h
  have hvol : (0 : ℝ) ≤ (2 * Real.pi) ^ (dim : ℕ) := by
    positivity
  calc
    ‖momentRefinedDeterministicTermSum ρ ε 1 α β s r‖ ≤
        ∑ e ∈ momentRefinedContractionFiber 1 s r,
          ‖deterministicMomentContractionTerm ρ ε 1 α β e‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _e ∈ momentRefinedContractionFiber 1 s r,
          (2 * Real.pi) ^ (dim : ℕ) :=
      Finset.sum_le_sum fun e _he =>
        norm_deterministicMomentContractionTerm_one_le
          ρ hε hε1 α β e
    _ = ((momentRefinedContractionFiber 1 s r).card : ℝ) *
          (2 * Real.pi) ^ (dim : ℕ) := by simp
    _ ≤ 1 * (2 * Real.pi) ^ (dim : ℕ) :=
      mul_le_mul_of_nonneg_right hcard hvol
    _ = ((2 * Real.pi) ^ (dim : ℕ)) ^ 1 *
          |Real.log ε| ^ (1 - 1) := by
      rw [pow_one, pow_zero, one_mul, mul_one]

/-- **The unconditional order-one uniform-branch output.** -/
theorem exists_momentRefinedIntegratedReductionOutputAt_one
    (ρ : SmoothCutoff) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε 1 α β C₀ 1 := by
  refine ⟨(2 * Real.pi) ^ (dim : ℕ) + 1, by positivity, ?_⟩
  intro lam ε α β hε hε1 hlog
  exact
    momentRefinedIntegratedReductionOutputAt_of_generalPeelFibreLogBound
      le_rfl hε hε1 hlog (by positivity)
      (r324GeneralPeel_fibreLogBound_one ρ hε hε1 α β)

/-! ## The order-two ledger -/

/-- The fibre ledger is monotone in its geometric constant. -/
theorem R324GeneralPeelFibreLogBound.mono
    {ρ : SmoothCutoff} {ε : ℝ} {m : ℕ} {α β : Z4}
    {K K' : ℝ} (hK : 0 ≤ K) (hKK' : K ≤ K')
    (hlog : 1 ≤ |Real.log ε|)
    (h : R324GeneralPeelFibreLogBound ρ ε m α β K) :
    R324GeneralPeelFibreLogBound ρ ε m α β K' := by
  intro s hs r hr
  refine (h s hs r hr).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hK hKK' m)
    (pow_nonneg (le_trans zero_le_one hlog) _)

/-- **The order-two fibre ledger holds unconditionally**: the
two-block fibre is the product of two uniformly bounded halves
(spending no logarithm), and every cross fibre spends its diagonal
window logarithm, matching `K^2 |log ε|^1` exactly.  This verifies
that the general peel normalization is the correct induction invariant
at both closed orders. -/
theorem exists_r324GeneralPeel_fibreLogBound_two
    (ρ : SmoothCutoff) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          R324GeneralPeelFibreLogBound ρ ε 2 α β K := by
  obtain ⟨Q, hQ, hhalf⟩ := exists_norm_r324TwoBlockHalfIntegral_le
  obtain ⟨CW, hCW, hcross⟩ := exists_norm_crossContractionTerm_le_log ρ
  refine ⟨Q + 3 * CW + 1, by positivity, ?_⟩
  intro ε α β hε hε1 hlog s hs r hr
  set L : ℝ := |Real.log ε| with hLdef
  have hL1 : (1 : ℝ) ≤ L := hlog
  set K : ℝ := Q + 3 * CW + 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]; linarith
  set p : R324RefinedScheduleIndex 2 := ⟨⟨s, hs⟩, ⟨r, hr⟩⟩
    with hpdef
  have hsum :
      momentRefinedDeterministicTermSum ρ ε 2 α β s r =
        r324RefinedPhysicalIntegral ρ ε 2 α β p := by
    rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
      ρ hε hε1 α β p]
    rfl
  have hpow : K ^ 2 * L ^ (2 - 1) = K ^ 2 * L := by
    norm_num
  by_cases hp : p = twoBlockScheduleIndex
  · rw [hsum, hp,
      r324RefinedPhysicalIntegral_twoBlock_eq ρ hε hε1 α β,
      norm_mul, hpow]
    calc
      ‖r324TwoBlockHalfIntegral ρ ε α β‖ *
          ‖r324TwoBlockHalfIntegral ρ ε (-α) (-β)‖ ≤
          Q * Q :=
        mul_le_mul (hhalf ρ hε hε1 α β)
          (hhalf ρ hε hε1 (-α) (-β)) (norm_nonneg _) hQ.le
      _ ≤ K * K := by
        have hQK : Q ≤ K := by rw [hKdef]; linarith
        exact mul_le_mul hQK hQK hQ.le (by linarith)
      _ = K ^ 2 * 1 := by ring
      _ ≤ K ^ 2 * L :=
        mul_le_mul_of_nonneg_left hL1 (by positivity)
  · rw [hsum, hpow]
    have hphys :
        ‖r324RefinedPhysicalIntegral ρ ε 2 α β p‖ ≤
          3 * (CW * L) := by
      rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
        ρ hε hε1 α β p]
      calc
        ‖∑ e ∈ momentRefinedContractionFiber 2 p.1.1 p.2.1,
            deterministicMomentContractionTerm ρ ε 2 α β e‖ ≤
            ∑ e ∈ momentRefinedContractionFiber 2 p.1.1 p.2.1,
              ‖deterministicMomentContractionTerm ρ ε 2 α β e‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _e ∈ momentRefinedContractionFiber 2 p.1.1 p.2.1,
              (CW * L) := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨π, rfl⟩ :=
            mem_momentRefinedContractionFiber_complement hp he
          exact hcross hε hε1 hlog α β π
        _ = ((momentRefinedContractionFiber 2
              p.1.1 p.2.1).card : ℝ) * (CW * L) := by
          simp
        _ ≤ 3 * (CW * L) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard :
              (momentRefinedContractionFiber 2
                p.1.1 p.2.1).card ≤ 3 := by
            calc
              (momentRefinedContractionFiber 2
                  p.1.1 p.2.1).card ≤
                  Fintype.card (MomentContraction 2) :=
                Finset.card_le_univ _
              _ = 3 := fintype_card_momentContraction_two
          exact_mod_cast hcard
    refine hphys.trans ?_
    have h3CW : 3 * CW ≤ K ^ 2 := by
      have hKK : K ≤ K ^ 2 := by
        nlinarith
      have h3K : 3 * CW ≤ K := by rw [hKdef]; linarith
      linarith
    calc
      3 * (CW * L) = (3 * CW) * L := by ring
      _ ≤ K ^ 2 * L :=
        mul_le_mul_of_nonneg_right h3CW (by linarith)

/-- **Both closed orders satisfy the ledger at one per-cutoff
constant.** -/
theorem exists_r324GeneralPeel_fibreLogBound_le_two
    (ρ : SmoothCutoff) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          1 ≤ m → m ≤ 2 →
          R324GeneralPeelFibreLogBound ρ ε m α β K := by
  obtain ⟨K₂, hK₂, h₂⟩ := exists_r324GeneralPeel_fibreLogBound_two ρ
  refine ⟨max ((2 * Real.pi) ^ (dim : ℕ)) K₂,
    lt_max_of_lt_right hK₂, ?_⟩
  intro ε m α β hε hε1 hlog hm1 hm2
  interval_cases m
  · exact
      (r324GeneralPeel_fibreLogBound_one ρ hε hε1 α β).mono
        (by positivity) (le_max_left _ _) hlog
  · exact
      (h₂ α β hε hε1 hlog).mono hK₂.le (le_max_right _ _) hlog

/-! ## Combining orders at one constant -/

/-- The uniform-branch output is monotone in the primitive constant. -/
theorem MomentRefinedIntegratedReductionOutputAt.mono_primitiveConstant
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {C C' : ℝ} (hC : 0 ≤ C) (hCC' : C ≤ C') (hε : 0 < ε)
    (h :
      MomentRefinedIntegratedReductionOutputAt
        ρ lam ε m α β C 1) :
    MomentRefinedIntegratedReductionOutputAt
      ρ lam ε m α β C' 1 := by
  obtain ⟨d⟩ := h
  exact
    ⟨⟨fun s hs r hr =>
      (d.refined_bound s hs r hr).trans
        (integral_primitiveInsertedMajorant_mono_const
          hC hCC' lam hε 1 m)⟩⟩

/-- **Both low orders at one per-cutoff constant.**  Order one is the
new unconditional output; order two is the proved unconditional
closure. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_le_two
    (ρ : SmoothCutoff) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          1 ≤ m → m ≤ 2 →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε m α β C₀ 1 := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_momentRefinedIntegratedReductionOutputAt_one ρ
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_momentRefinedIntegratedReductionOutputAt_two ρ
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro lam ε m α β hε hε1 hlog hm1 hm2
  interval_cases m
  · exact
      (h₁ lam α β hε hε1 hlog).mono_primitiveConstant
        hC₁.le (le_max_left _ _) hε
  · exact
      (h₂ lam α β hε hε1 hlog).mono_primitiveConstant
        hC₂.le (le_max_right _ _) hε

/-! ## The exact residual obligation -/

/-- **The single remaining uniform-branch obligation.**  One
per-cutoff geometric constant funds the fibre logarithmic ledger at
every order `m ≥ 3`.  Orders one and two are closed unconditionally
above; by the general peel bridge this proposition is all that
separates the project from the complete middle estimate. -/
def R324GeneralPeelLedgerFromThree
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
      R324GeneralPeelFibreLogBound ρ ε m α β K

/-- **Master closure of the uniform branch.**  Any ledger for the
orders `m ≥ 3` yields the complete uniform-branch output: one
per-cutoff primitive constant, every order `m ≥ 1`, every coupling,
every admissible scale, both external modes, support constant one. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_of_ledgerFromThree
    (ρ : SmoothCutoff)
    (h : ∃ K : ℝ, 0 ≤ K ∧ R324GeneralPeelLedgerFromThree ρ K) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (m : ℕ) (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε m α β C₀ 1 := by
  obtain ⟨K, hK, hled⟩ := h
  obtain ⟨Clow, hClow, hlow⟩ :=
    exists_momentRefinedIntegratedReductionOutputAt_le_two ρ
  refine ⟨max Clow (K + 1), lt_max_of_lt_left hClow, ?_⟩
  intro lam ε m α β hε hε1 hlog hm
  by_cases hm3 : 3 ≤ m
  · refine
      (momentRefinedIntegratedReductionOutputAt_of_generalPeelFibreLogBound
        hm hε hε1 hlog hK
        (hled m α β hε hε1 hlog hm3)).mono_primitiveConstant
        (by linarith) (le_max_right _ _) hε
  · exact
      (hlow lam m α β hε hε1 hlog hm
        (by omega)).mono_primitiveConstant
        hClow.le (le_max_left _ _) hε

end

end Anderson4D
