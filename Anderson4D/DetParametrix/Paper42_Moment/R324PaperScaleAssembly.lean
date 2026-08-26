import Anderson4D.DetParametrix.Paper42_Moment.R324HdetAssemblyFinal
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedQuadCompositionBridge

/-!
# Summation at the paper's central-frequency scale

Paper: R-324 — §4.2, Step 4 and the final summation

The central bracket produced in Step 4(B) is
`⟨ε²(α+β)⟩⁻⁸`.  This file sums the post-collapse refined-fibre bound at
exactly that scale.  It deliberately does not pass through
`R324HdetBracketLedgerBound`, whose `⟨ε(α+β)⟩⁻⁸` premise is stronger than
the statement proved in the paper.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The paper-scale post-collapse estimate, expressed on the residual
signature fibre used by the final finite summation. -/
theorem R324RefinedPostCollapsePaperBracketBound.refinedTermSum_le
    {ρ : SmoothCutoff} {K : ℝ}
    (h : R324RefinedPostCollapsePaperBracketBound ρ K)
    {ε : ℝ} (m : ℕ) (α β : Z4)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|) (hm2 : 2 ≤ m)
    (hmtrunc : m ≤ truncOrder ε)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hr : r ∈ momentResidualChainSignaturesAt m s) :
    ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
      (m : ℝ) ^ 8 * K ^ m * |Real.log ε| ^ (m - 1) *
        (r324EndpointLoss ε α β *
          eighthOrderFrequencyDecay
            (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)) := by
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  rw [momentRefinedDeterministicTermSum_eq_r324RefinedPhysicalIntegral
    ρ hε hε1 α β s hs r hr]
  exact h m α β hε hεsmall hlog hm2 hmtrunc
    (⟨⟨s, hs⟩, ⟨r, hr⟩⟩ : R324RefinedScheduleIndex m)

/-- The paper-scale bracket sums over residual schedules and contraction
signatures with the same finite counting cost as the existing final
assembly.  The conclusion retains `ε²` verbatim. -/
theorem r324PaperScale_pairingSum_le_of_postCollapseBracket
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (h : R324RefinedPostCollapsePaperBracketBound ρ K)
    (lam : ℝ) {ε : ℝ} {m : ℕ} (α β : Z4)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hlog : 1 ≤ |Real.log ε|)
    (hm2 : 2 ≤ m) (hmtrunc : m ≤ truncOrder ε) :
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
      lamEps lam ε ^ 2 * (65536 * K) ^ m * lam ^ (2 * m - 2) *
        (r324EndpointLoss ε α β *
          eighthOrderFrequencyDecay
            (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖)) := by
  have hL0 : (0 : ℝ) < |Real.log ε| :=
    lt_of_lt_of_le one_pos hlog
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  set L : ℝ := |Real.log ε| with hLdef
  set D : ℝ :=
    r324EndpointLoss ε α β *
      eighthOrderFrequencyDecay
        (ε ^ 2 * ‖z4EuclideanFrequency (α + β)‖) with hDdef
  have hD0 : 0 ≤ D :=
    mul_nonneg (r324EndpointLoss_nonneg ε α β)
      (eighthOrderFrequencyDecay_nonneg _)
  set B : ℝ := (m : ℝ) ^ 8 * K ^ m * L ^ (m - 1) * D with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hK m))
        (pow_nonneg (abs_nonneg _) _)) hD0
  have hper :
      ∀ s ∈ momentContractionSignatures m,
        ‖∑ e ∈ momentContractionFiber m s,
            deterministicMomentContractionTerm ρ ε m α β e‖ ≤
          (4 : ℝ) ^ (2 * m) * B := by
    intro s hs
    rw [← sum_momentRefinedDeterministicTermSum ρ ε m α β s]
    calc
      ‖∑ r ∈ momentResidualChainSignaturesAt m s,
          momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
          ∑ r ∈ momentResidualChainSignaturesAt m s,
            ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _r ∈ momentResidualChainSignaturesAt m s, B :=
        Finset.sum_le_sum fun r hr => by
          rw [hBdef, hLdef, hDdef]
          exact h.refinedTermSum_le m α β hε hεsmall hlog hm2
            hmtrunc s hs r hr
      _ = ((momentResidualChainSignaturesAt m s).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ (2 * m) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact_mod_cast card_momentResidualChainSignaturesAt_le m s
  have hgrouped :
      groupedDeterministicMomentTermNormSum ρ ε m α β ≤
        (4 : ℝ) ^ (2 * m) * ((4 : ℝ) ^ (2 * m) * B) := by
    unfold groupedDeterministicMomentTermNormSum
    calc
      (∑ s ∈ momentContractionSignatures m,
          ‖∑ e ∈ (Finset.univ : Finset (MomentContraction m)) with
            momentContractionSignature e = s,
            deterministicMomentContractionTerm ρ ε m α β e‖) ≤
          ∑ _s ∈ momentContractionSignatures m,
            (4 : ℝ) ^ (2 * m) * B :=
        Finset.sum_le_sum fun s hs => hper s hs
      _ = ((momentContractionSignatures m).card : ℝ) *
            ((4 : ℝ) ^ (2 * m) * B) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (4 : ℝ) ^ (2 * m) * ((4 : ℝ) ^ (2 * m) * B) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (by positivity) hB0)
        exact_mod_cast card_momentContractionSignatures_le m
  have hid :
      |lamEps lam ε| ^ (2 * m) * L ^ (m - 1) =
        lamEps lam ε ^ 2 * lam ^ (2 * m - 2) := by
    rw [abs_lamEps_even_pow m hL0, lamEps_sq hL0, ← hLdef]
    have hLm : L ^ m = L * L ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hlam2 : lam ^ (2 * m) = lam ^ 2 * lam ^ (2 * m - 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hLm, hlam2]
    field_simp
  have hcoeff :
      (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
          ((m : ℝ) ^ 8 * K ^ m) ≤
        (65536 * K) ^ m := by
    have hm8 : (m : ℝ) ^ 8 ≤ (256 : ℝ) ^ m := by
      have h2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by
        exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
      calc
        (m : ℝ) ^ 8 ≤ ((2 : ℝ) ^ m) ^ 8 := by
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
          exact pow_le_pow_left₀ hm0 h2 8
        _ = (256 : ℝ) ^ m := by
          rw [← pow_mul, mul_comm m 8, pow_mul]
          norm_num
    calc
      (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
          ((m : ℝ) ^ 8 * K ^ m) ≤
          (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
            ((256 : ℝ) ^ m * K ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hm8 (pow_nonneg hK m)
      _ = (65536 * K) ^ m := by
        have h4 : (4 : ℝ) ^ (2 * m) = (16 : ℝ) ^ m := by
          rw [pow_mul]
          norm_num
        rw [h4, ← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        ring
  calc
    ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
        |lamEps lam ε| ^ (2 * m) *
          groupedDeterministicMomentTermNormSum ρ ε m α β :=
      deterministicMomentPairingSum_le_groupedSignatures ρ lam ε m α β
    _ ≤ |lamEps lam ε| ^ (2 * m) *
          ((4 : ℝ) ^ (2 * m) * ((4 : ℝ) ^ (2 * m) * B)) :=
      mul_le_mul_of_nonneg_left hgrouped
        (pow_nonneg (abs_nonneg _) _)
    _ = (4 : ℝ) ^ (2 * m) * (4 : ℝ) ^ (2 * m) *
          ((m : ℝ) ^ 8 * K ^ m) *
          (|lamEps lam ε| ^ (2 * m) * L ^ (m - 1)) * D := by
      rw [hBdef]
      ring
    _ ≤ (65536 * K) ^ m *
          (|lamEps lam ε| ^ (2 * m) * L ^ (m - 1)) * D := by
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (by positivity)) hD0
    _ = lamEps lam ε ^ 2 * (65536 * K) ^ m *
          lam ^ (2 * m - 2) * D := by
      rw [hid]
      ring

end

end Anderson4D
