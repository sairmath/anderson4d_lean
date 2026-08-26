import Anderson4D.DetParametrix.Paper42_Moment.R324BracketCoreFourier

/-!
# Clause B: the bulk region is already clause A

`R324CappedBracketDensityLedger` (clause B) grades its right-hand side
by `r324CMBracketWeight ε α β = ε⁻⁸ ⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε‖α+β‖⟩⁻⁸`.  This
weight is **not** small everywhere: the endpoint loss `ε⁻⁸` is large,
and for every `(α, β)` in the *bulk region*

`(1 + |α|²)(1 + |β|²) ≤ ε⁻⁴/4`  and  `ε‖freq(α+β)‖ ≤ 1`

the weight is at least `1` (`one_le_r324CMBracketWeight_of_bulk`).  On
that region clause B is a strictly weaker statement than clause A, and
is proved here outright from it
(`r324Bracket_norm_sum_le_of_one_le_weight`): the modulus route is
legitimate exactly where the weight has no decay to supply.

What survives is the **tail region** `r324CMBracketWeight ε α β ≤ 1`,
where the mode grading is real and, by `r324CMFlatDensity_modes_indep`,
must come from the oscillation of the four external characters.  That
residue is isolated as `R324BracketTailLedger`, and clause B is proved
from clause A plus it (`R324CappedBracketDensityLedger_of_tail`).

Note the tail region is genuinely a *high-frequency* region: it forces
`(1+|α|²)²(1+|β|²)²(1+ε²‖α+β‖²)⁴ ≥ ε⁻⁸`, i.e. either an external mode
of size `≳ ε⁻¹` or a conserved mode `α+β` of size `≫ ε⁻¹`.  This is the
same split the paper makes in §4.2.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The modulus route, valid exactly where the weight is `≥ 1` -/

/-- **Clause A gives clause B wherever the weight has no decay to
supply.**  The Bochner triangle inequality plus mode independence of the
flat density; no oscillation is used, and none is needed because the
weight is `≥ 1`. -/
theorem r324Bracket_norm_sum_le_of_one_le_weight
    {ρ : SmoothCutoff} {K : ℝ}
    (hA : R324CappedDensityLedger ρ K)
    {ε : ℝ} (m : ℕ) (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (hm2 : 2 ≤ m) (hcap : m ≤ truncOrder ε)
    (hW : 1 ≤ r324CMBracketWeight ε α β)
    (F : Finset (MomentContraction m)) :
    ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
      K ^ m * |Real.log ε| ^ (m - 1) * r324CMBracketWeight ε α β := by
  have hbase : ‖∑ e ∈ F,
      deterministicMomentContractionTerm ρ ε m α β e‖ ≤
        K ^ m * |Real.log ε| ^ (m - 1) := by
    calc
      ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
          ∫ p, r324CMFlatDensity ρ ε m α β F p
            ∂(r324PhysicalMeasure m) :=
        r324CM_norm_sum_le_integral_flatDensity ρ hε hε1 α β F
      _ = ∫ p, r324CMFlatDensity ρ ε m 0 0 F p
            ∂(r324PhysicalMeasure m) :=
        integral_congr_ae (Filter.Eventually.of_forall fun p =>
          r324CMFlatDensity_modes_indep ρ ε m α β 0 0 F p)
      _ ≤ K ^ m * |Real.log ε| ^ (m - 1) := hA m hε hε1 hlog hm2 hcap F
  have hKL : (0 : ℝ) ≤ K ^ m * |Real.log ε| ^ (m - 1) :=
    le_trans (norm_nonneg _) hbase
  calc
    ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
        K ^ m * |Real.log ε| ^ (m - 1) := hbase
    _ = K ^ m * |Real.log ε| ^ (m - 1) * 1 := (mul_one _).symm
    _ ≤ K ^ m * |Real.log ε| ^ (m - 1) * r324CMBracketWeight ε α β :=
      mul_le_mul_of_nonneg_left hW hKL

/-! ## The bulk region -/

/-- **The bulk region carries no decay.**  If the conserved mode `α+β`
is below the cutoff scale and the two external modes are not too large,
the endpoint loss `ε⁻⁸` dominates every decay factor and the bracket
weight is at least one. -/
theorem one_le_r324CMBracketWeight_of_bulk
    {ε : ℝ} (hε : 0 < ε) (α β : Z4)
    (hcentral : ε * ‖z4EuclideanFrequency (α + β)‖ ≤ 1)
    (hmodes :
      (1 + paperModeNormSq α) * (1 + paperModeNormSq β) ≤
        ε⁻¹ ^ (4 : ℕ) / 4) :
    1 ≤ r324CMBracketWeight ε α β := by
  set A : ℝ := 1 + paperModeNormSq α with hA
  set B : ℝ := 1 + paperModeNormSq β with hB
  have hApos : 0 < A := by
    have : 0 ≤ paperModeNormSq α := by
      unfold paperModeNormSq
      positivity
    simpa [hA] using (by linarith : (0 : ℝ) < 1 + paperModeNormSq α)
  have hBpos : 0 < B := by
    have : 0 ≤ paperModeNormSq β := by
      unfold paperModeNormSq
      positivity
    simpa [hB] using (by linarith : (0 : ℝ) < 1 + paperModeNormSq β)
  have hinvpos : 0 < ε⁻¹ := inv_pos.mpr hε
  -- the central bracket is at least `1/16`
  have hNn : (0 : ℝ) ≤ ε * ‖z4EuclideanFrequency (α + β)‖ := by
    positivity
  have hcen : (1 : ℝ) / 16 ≤
      eighthOrderFrequencyDecay (ε * ‖z4EuclideanFrequency (α + β)‖) := by
    unfold eighthOrderFrequencyDecay
    have hle2 : 1 + (ε * ‖z4EuclideanFrequency (α + β)‖) ^ 2 ≤ 2 := by
      nlinarith
    have h16 : (1 + (ε * ‖z4EuclideanFrequency (α + β)‖) ^ 2) ^ (4 : ℕ) ≤
        16 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
        1 + (ε * ‖z4EuclideanFrequency (α + β)‖) ^ 2) hle2 4
      norm_num at this ⊢
      linarith
    have hpos : (0 : ℝ) <
        (1 + (ε * ‖z4EuclideanFrequency (α + β)‖) ^ 2) ^ (4 : ℕ) := by
      positivity
    simpa [one_div] using one_div_le_one_div_of_le hpos h16
  -- the endpoint factor is at least `16`
  have hAB : A * B ≤ ε⁻¹ ^ (4 : ℕ) / 4 := hmodes
  have hABpos : 0 < A * B := mul_pos hApos hBpos
  have hend : (16 : ℝ) ≤
      ε⁻¹ ^ (8 : ℕ) * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β := by
    have hval : paperFourthOrderModeDecay α * paperFourthOrderModeDecay β
        = ((A * B) ^ (2 : ℕ))⁻¹ := by
      unfold paperFourthOrderModeDecay
      rw [← hA, ← hB]
      field_simp
    have h4 : 4 * (A * B) ≤ ε⁻¹ ^ (4 : ℕ) := by linarith
    have hsq : (4 * (A * B)) ^ (2 : ℕ) ≤ (ε⁻¹ ^ (4 : ℕ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) h4 2
    have hkey : (16 : ℝ) * (A * B) ^ (2 : ℕ) ≤ ε⁻¹ ^ (8 : ℕ) := by
      have hrw : (ε⁻¹ ^ (4 : ℕ)) ^ (2 : ℕ) = ε⁻¹ ^ (8 : ℕ) := by ring
      rw [hrw] at hsq
      nlinarith [hsq]
    have hsqpos : (0 : ℝ) < (A * B) ^ (2 : ℕ) := by positivity
    calc
      (16 : ℝ) = 16 * (A * B) ^ (2 : ℕ) * ((A * B) ^ (2 : ℕ))⁻¹ := by
        field_simp
      _ ≤ ε⁻¹ ^ (8 : ℕ) * ((A * B) ^ (2 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = ε⁻¹ ^ (8 : ℕ) * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β := by
        rw [mul_assoc, hval]
  have hendpos : (0 : ℝ) ≤
      ε⁻¹ ^ (8 : ℕ) * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β := by linarith
  unfold r324CMBracketWeight r324EndpointLoss
  have := mul_le_mul hend hcen (by norm_num) hendpos
  linarith [this]

/-! ## The tail residue and clause B -/

/-- **The tail ledger.**  Clause B restricted to the region where the
bracket weight really does carry decay.  This is the only part of
clause B that needs the oscillation of the four external characters:
by `r324CMFlatDensity_modes_indep` no modulus bound can reach it. -/
def R324BracketTailLedger (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        r324CMBracketWeight ε α β ≤ 1 →
          ∀ F : Finset (MomentContraction m),
            ‖∑ e ∈ F,
                deterministicMomentContractionTerm ρ ε m α β e‖ ≤
              K ^ m * |Real.log ε| ^ (m - 1) *
                r324CMBracketWeight ε α β

/-- **Clause B from clause A and the tail residue.** -/
theorem R324CappedBracketDensityLedger_of_tail
    {ρ : SmoothCutoff} {K : ℝ}
    (hA : R324CappedDensityLedger ρ K)
    (hT : R324BracketTailLedger ρ K) :
    R324CappedBracketDensityLedger ρ K := by
  intro ε m α β hε hε1 hlog hm2 hcap F
  rcases le_or_gt (r324CMBracketWeight ε α β) 1 with hW | hW
  · exact hT m α β hε hε1 hlog hm2 hcap hW F
  · exact r324Bracket_norm_sum_le_of_one_le_weight hA m α β hε hε1 hlog
      hm2 hcap hW.le F

/-- **The strong capped ledger from clause A and the tail residue.** -/
theorem R324CappedCrossLedgerStrong_of_tail
    {ρ : SmoothCutoff} {K : ℝ}
    (hA : R324CappedDensityLedger ρ K)
    (hT : R324BracketTailLedger ρ K) :
    R324CappedCrossLedgerStrong ρ K :=
  ⟨hA, R324CappedBracketDensityLedger_of_tail hA hT⟩

end

end Anderson4D
