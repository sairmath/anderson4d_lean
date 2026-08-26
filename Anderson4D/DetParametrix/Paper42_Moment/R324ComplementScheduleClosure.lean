import Anderson4D.DetParametrix.Paper42_Moment.R324ComplementScheduleCore
import Anderson4D.DetParametrix.Paper42_Moment.R324DifferenceRetainingEstimate

/-!
# Closure of the order-two complement schedules

The difference-retaining estimate discharges the two-block schedule (the
unique order-two witness of the interior-core nonexistence theorem) and reduces
the order-two uniform branch to the complement schedules.  This file
closes that complement and composes the unconditional order-two
uniform-branch output.

* `momentContraction_two_classify` — an order-two contraction is the
  two-block full swap or a cross matching
  `⟨idPairingFinTwo, idPairingFinTwo, π⟩`; consequently every
  complement refined fibre consists of cross contractions only
  (`mem_momentRefinedContractionFiber_complement`);
* `exists_r324ComplementSchedule_insertedMajorantBound` — the
  complement middle estimate: on every schedule other than the
  two-block one, the weighted refined physical integral obeys the
  paper-scale inserted-majorant bound.  Ledger:
  `|λ_ε|⁴ · 3·C_W·|log ε| = 3 C_W λ⁴/|log ε|` against the majorant's
  `(C₀λ)⁴/|log ε|`: the diagonal window `Σ_k ‖ρ̂(εk)‖⁴⟨k⟩⁻⁴ ≲ |log ε|`
  spends exactly the one logarithm that `λ_ε⁴ = λ⁴/log²ε` affords;
* `exists_r324RefinedInsertedMajorantBound_two`,
  `exists_momentRefinedIntegratedReductionOutputAt_two` — the
  **unconditional** order-two middle estimate and uniform-branch
  output, combining the proved difference-retaining two-block
  estimate with the complement bound at a common primitive constant.

The primitive constant depends on the mollifier `ρ` (quantifier order
`∀ ρ, ∃ C₀`): the complement window is supported on
`|k| ≲ (radius·ε)⁻¹`, so its logarithm degrades like `|log radius|`
as the mollifier concentrates; a `ρ`-uniform constant is impossible
for the cross-cut fibres, in contrast with the two-block estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Order-two contraction classification -/

/-- An order-two contraction entity is the two-block full swap or a
trivial-pairing cross matching. -/
theorem momentContraction_two_classify (e : MomentContraction 2) :
    e = twoBlockContraction ∨
      ∃ π : idPairingFinTwo.singles ≃ idPairingFinTwo.singles,
        e = ⟨idPairingFinTwo, ⟨idPairingFinTwo, π⟩⟩ := by
  obtain ⟨κp, κm, π⟩ := e
  rcases partialPairing_finTwo_classify κp with rfl | rfl <;>
    rcases partialPairing_finTwo_classify κm with rfl | rfl
  · left
    have hπ : π = Equiv.refl _ := Subsingleton.elim _ _
    rw [hπ]
    rfl
  · exact (IsEmpty.false (π.symm idSingleZero)).elim
  · exact (IsEmpty.false (π idSingleZero)).elim
  · right
    exact ⟨π, rfl⟩

/-- Every contraction in a complement refined fibre is a cross
matching: the two-block entity forces its schedule index. -/
theorem mem_momentRefinedContractionFiber_complement
    {p : R324RefinedScheduleIndex 2}
    (hp : p ≠ twoBlockScheduleIndex)
    {e : MomentContraction 2}
    (he : e ∈ momentRefinedContractionFiber 2 p.1.1 p.2.1) :
    ∃ π : idPairingFinTwo.singles ≃ idPairingFinTwo.singles,
      e = ⟨idPairingFinTwo, ⟨idPairingFinTwo, π⟩⟩ := by
  rcases momentContraction_two_classify e with rfl | hcross
  · exfalso
    apply hp
    obtain ⟨⟨s, hs⟩, ⟨r, hr⟩⟩ := p
    obtain ⟨hsig, hres⟩ := mem_momentRefinedContractionFiber.mp he
    simp only at hsig hres
    subst hsig
    subst hres
    rfl
  · exact hcross

/-! ## The complement middle estimate -/

/-- The order-two contraction entities number exactly three. -/
theorem fintype_card_momentContraction_two :
    Fintype.card (MomentContraction 2) = 3 := by decide

/-- **The complement middle estimate.**  On every refined schedule
other than the two-block one, the weighted physical integral obeys
the paper-scale inserted-majorant bound: the cross fibres carry no
extraction and no difference factor, and their diagonal window spends
one logarithm against the two afforded by `λ_ε⁴`. -/
theorem exists_r324ComplementSchedule_insertedMajorantBound
    (ρ : SmoothCutoff) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (lam : ℝ) {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        ∀ p : R324RefinedScheduleIndex 2,
          p ≠ twoBlockScheduleIndex →
            |lamEps lam ε| ^ (2 * 2) *
                ‖r324RefinedPhysicalIntegral ρ ε 2 α β p‖ ≤
              ∫ z, primitiveInsertedMajorant C₁ lam ε 1 2 z
                ∂paperMeasure := by
  obtain ⟨CW, hCW, hcross⟩ := exists_norm_crossContractionTerm_le_log ρ
  refine ⟨3 * CW + 1, by positivity, ?_⟩
  intro lam ε α β hε hε1 hlog p hp
  set L : ℝ := |Real.log ε| with hLdef
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hlog
  have hlamEps : |lamEps lam ε| ^ (2 * 2) = lam ^ 4 / L ^ 2 := by
    unfold lamEps
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), ← hLdef]
    rw [div_pow]
    congr 1
    · rw [show (2 * 2 : ℕ) = 4 from rfl, ← abs_pow]
      exact abs_of_nonneg (by positivity)
    · rw [show (2 * 2 : ℕ) = 4 from rfl,
        show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
        Real.sq_sqrt hL0.le]
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
      _ = ((momentRefinedContractionFiber 2 p.1.1 p.2.1).card : ℝ) *
            (CW * L) := by
        simp
      _ ≤ 3 * (CW * L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcard :
            (momentRefinedContractionFiber 2 p.1.1 p.2.1).card ≤ 3 := by
          calc
            (momentRefinedContractionFiber 2 p.1.1 p.2.1).card ≤
                Fintype.card (MomentContraction 2) :=
              Finset.card_le_univ _
            _ = 3 := fintype_card_momentContraction_two
        exact_mod_cast hcard
  have hmajorant :=
    le_integral_primitiveInsertedMajorant
      (3 * CW + 1) lam ε 1 2 hε hε1 one_pos
  have hmajorant' :
      (3 * CW + 1) ^ 4 * lam ^ 4 * (1 / L) ≤
        ∫ z, primitiveInsertedMajorant (3 * CW + 1) lam ε 1 2 z
          ∂paperMeasure := by
    refine le_trans (le_of_eq ?_) hmajorant
    rw [min_self, mul_pow, ← hLdef]
    norm_num
  refine le_trans ?_ hmajorant'
  rw [hlamEps]
  have hkey : 3 * CW ≤ (3 * CW + 1) ^ 4 := by
    have hbase : (1 : ℝ) ≤ 3 * CW + 1 := by linarith
    calc
      3 * CW ≤ 3 * CW + 1 := by linarith
      _ ≤ (3 * CW + 1) ^ 4 :=
        le_self_pow₀ hbase (by norm_num)
  calc
    lam ^ 4 / L ^ 2 *
        ‖r324RefinedPhysicalIntegral ρ ε 2 α β p‖ ≤
        lam ^ 4 / L ^ 2 * (3 * (CW * L)) :=
      mul_le_mul_of_nonneg_left hphys (by positivity)
    _ = (3 * CW) * lam ^ 4 * (1 / L) := by
      field_simp
    _ ≤ (3 * CW + 1) ^ 4 * lam ^ 4 * (1 / L) := by
      have h4 : (0 : ℝ) ≤ lam ^ 4 * (1 / L) := by positivity
      calc
        (3 * CW) * lam ^ 4 * (1 / L) =
            (3 * CW) * (lam ^ 4 * (1 / L)) := by ring
        _ ≤ (3 * CW + 1) ^ 4 * (lam ^ 4 * (1 / L)) :=
          mul_le_mul_of_nonneg_right hkey h4
        _ = (3 * CW + 1) ^ 4 * lam ^ 4 * (1 / L) := by ring

/-! ## Majorant monotonicity in the primitive constant -/

theorem primitiveInsertedMajorant_mono_const
    {C C' : ℝ} (hC : 0 ≤ C) (hCC' : C ≤ C')
    (lam ε supportConstant : ℝ) (n : ℕ) (z : T4) :
    primitiveInsertedMajorant C lam ε supportConstant n z ≤
      primitiveInsertedMajorant C' lam ε supportConstant n z := by
  unfold primitiveInsertedMajorant
  have hbracket :
      0 ≤ ((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
          primitiveSupportIndicator supportConstant ε z +
        (1 / |Real.log ε| ^ 2) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z)
    · apply mul_nonneg (by positivity)
      have := torusDistSq_nonneg z
      positivity
  apply mul_le_mul_of_nonneg_right _ hbracket
  calc
    (C * lam) ^ (2 * n) = C ^ (2 * n) * lam ^ (2 * n) := by
      rw [mul_pow]
    _ ≤ C' ^ (2 * n) * lam ^ (2 * n) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hC hCC' (2 * n))
      rw [show 2 * n = n * 2 by ring, pow_mul]
      positivity
    _ = (C' * lam) ^ (2 * n) := by rw [mul_pow]

theorem integral_primitiveInsertedMajorant_mono_const
    {C C' : ℝ} (hC : 0 ≤ C) (hCC' : C ≤ C')
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε)
    (supportConstant : ℝ) (n : ℕ) :
    (∫ z, primitiveInsertedMajorant C lam ε supportConstant n z
        ∂paperMeasure) ≤
      ∫ z, primitiveInsertedMajorant C' lam ε supportConstant n z
        ∂paperMeasure := by
  apply integral_mono_ae
  · exact integrable_primitiveInsertedMajorant C lam ε
      supportConstant n hε
  · exact integrable_primitiveInsertedMajorant C' lam ε
      supportConstant n hε
  · filter_upwards with z
    exact primitiveInsertedMajorant_mono_const hC hCC'
      lam ε supportConstant n z

/-! ## The unconditional order-two middle estimate -/

/-- **The unconditional order-two middle estimate.**  The two-block
schedule is discharged by the proved difference-retaining estimate
and every complement schedule by the cross-cut window bound, at the
common primitive constant `max`. -/
theorem exists_r324RefinedInsertedMajorantBound_two
    (ρ : SmoothCutoff) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          R324RefinedInsertedMajorantBound ρ lam ε 2 α β C₀ 1 := by
  obtain ⟨C₂, hC₂, htwo⟩ := exists_r324TwoBlock_insertedMajorantBound
  obtain ⟨C₁, hC₁, hcompl⟩ :=
    exists_r324ComplementSchedule_insertedMajorantBound ρ
  refine ⟨max C₂ C₁, lt_max_of_lt_left hC₂, ?_⟩
  intro lam ε α β hε hε1 hlog p
  by_cases hp : p = twoBlockScheduleIndex
  · subst hp
    refine le_trans (htwo ρ lam α β hε hε1 hlog) ?_
    exact integral_primitiveInsertedMajorant_mono_const
      hC₂.le (le_max_left _ _) lam hε 1 2
  · refine le_trans (hcompl lam α β hε hε1 hlog p hp) ?_
    exact integral_primitiveInsertedMajorant_mono_const
      hC₁.le (le_max_right _ _) lam hε 1 2

/-- **The unconditional order-two uniform-branch output.**  The property
`MomentRefinedIntegratedReductionOutputAt` holds at order two, with a primitive
constant depending only on the mollifier — no complement hypothesis
remains. -/
theorem exists_momentRefinedIntegratedReductionOutputAt_two
    (ρ : SmoothCutoff) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (lam : ℝ) {ε : ℝ} (α β : Z4),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          MomentRefinedIntegratedReductionOutputAt
            ρ lam ε 2 α β C₀ 1 := by
  obtain ⟨C₀, hC₀, hmiddle⟩ :=
    exists_r324RefinedInsertedMajorantBound_two ρ
  refine ⟨C₀, hC₀, ?_⟩
  intro lam ε α β hε hε1 hlog
  exact
    momentRefinedIntegratedReductionOutputAt_of_insertedMajorantBound
      hε hε1 (hmiddle lam α β hε hε1 hlog)

end

end Anderson4D
