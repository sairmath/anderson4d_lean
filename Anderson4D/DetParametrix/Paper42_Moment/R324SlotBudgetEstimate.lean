import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorCoreEstimate

/-!
# The routed slot budget for R-324 (INEQ 2) and the capstone assembly

The second residual input of the final R-324 assembly is the routed
slot budget: at every marked slot the countable signed route weight is
dominated by the integrated inserted majorant.  As with the interior
estimate, the coupling power `|λ_ε|^{2m} = λ^{2m}/|log ε|^m` factors
out of the slot series exactly, so the budget reduces to a coupling-free
logarithmic inequality `R324SlotLogBudget` on the grouped-core slot
series.

The capstone theorem
`exists_deterministicMoment_paper_bound_of_logBudgets` then produces
the paper bound (3.24) from the two logarithmic budgets alone: every
Fourier-mode layer, endpoint case split, routing datum, and majorant
integral is discharged unconditionally.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- **The residual slot budget (INEQ 2, reduced form).**  At every
marked slot, the `|log ε|`-weighted countable slot series of grouped
interior `L¹` masses against reciprocal routed costs is controlled by
`C^{2m} |log ε|^m`.  Like the interior budget, it mentions no coupling,
no Fourier mode, no majorant integral, and no support constant. -/
def R324SlotLogBudget
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m)
    (ε primitiveConstant : ℝ) : Prop :=
  ∀ i : Fin m,
    |Real.log ε| *
        (∑' p : R324RefinedScheduleIndex m × ℕ,
          ρ.r324GroupedRefinedCoreL1 hm ε p *
            SmoothCutoff.r324GroupedIncrementCost hm p.2 i) ≤
      primitiveConstant ^ (2 * m) * |Real.log ε| ^ m

/-- The signed route slot weight is the coupling power times the
coupling-free grouped slot term. -/
theorem r324SignedRouteSlotWeight_eq_pow_mul
    (ρ : SmoothCutoff) (lam : ℝ) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (i : Fin m)
    (p : R324RefinedScheduleIndex m × ℕ) :
    ρ.r324SignedRouteSlotWeight lam hm ε i p =
      |lamEps lam ε| ^ (2 * m) *
        (ρ.r324GroupedRefinedCoreL1 hm ε p *
          SmoothCutoff.r324GroupedIncrementCost hm p.2 i) := by
  unfold SmoothCutoff.r324SignedRouteSlotWeight
  ring

/-- **The logarithmic slot budget discharges the routed slot budget.**
Same arithmetic as the interior bridge: the coupling power factors out
of the slot series, the leftover `|log ε|^{m-1}` is absorbed by the
majorant's near-field mass, and the support-constant distortion
`min(c,1)²/c ≤ 1` is paid inside the budget's constant. -/
theorem slot_tsum_le_integral_insertedMajorant_of_logBudget
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hlam : 0 ≤ lam)
    (hsupport : 0 < supportConstant)
    (budget :
      R324SlotLogBudget ρ hm ε
        (min supportConstant 1 ^ 2 / supportConstant *
          primitiveConstant)) :
    ∀ i : Fin m,
      (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324SignedRouteSlotWeight lam hm ε i p) ≤
        ∫ z,
          primitiveInsertedMajorant
            primitiveConstant lam ε supportConstant m z
          ∂paperMeasure := by
  intro i
  set c₂ : ℝ := min supportConstant 1 ^ 2 / supportConstant
    with hc₂def
  have hmin0 : 0 < min supportConstant 1 :=
    lt_min hsupport one_pos
  have hc₂0 : 0 < c₂ := by
    rw [hc₂def]
    positivity
  have hc₂1 : c₂ ≤ 1 := by
    rw [hc₂def, div_le_one hsupport]
    rcases le_total supportConstant 1 with h | h
    · rw [min_eq_left h]
      nlinarith
    · rw [min_eq_right h]
      nlinarith
  set L : ℝ := |Real.log ε| with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hlog
  set T : ℝ :=
    ∑' p : R324RefinedScheduleIndex m × ℕ,
      ρ.r324GroupedRefinedCoreL1 hm ε p *
        SmoothCutoff.r324GroupedIncrementCost hm p.2 i
    with hTdef
  have hrw :
      (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324SignedRouteSlotWeight lam hm ε i p) =
        |lamEps lam ε| ^ (2 * m) * T := by
    rw [hTdef, ← tsum_mul_left]
    exact tsum_congr fun p =>
      r324SignedRouteSlotWeight_eq_pow_mul ρ lam hm ε i p
  have hbud : L * T ≤
      (c₂ * primitiveConstant) ^ (2 * m) * L ^ m :=
    budget i
  have hfactor : (0 : ℝ) ≤ lam ^ (2 * m) / L ^ (m + 1) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hbud hfactor
  have hLne : L ≠ 0 := hL0.ne'
  have heqL :
      lam ^ (2 * m) / L ^ (m + 1) * (L * T) =
        lam ^ (2 * m) / L ^ m * T := by
    field_simp
    ring
  have heqR :
      lam ^ (2 * m) / L ^ (m + 1) *
          ((c₂ * primitiveConstant) ^ (2 * m) * L ^ m) =
        c₂ ^ (2 * m) *
          ((primitiveConstant * lam) ^ (2 * m) / L) := by
    field_simp
    ring
  rw [heqL, heqR] at hmul
  have hpow0 : (0 : ℝ) ≤ (primitiveConstant * lam) ^ (2 * m) :=
    (even_two_mul m).pow_nonneg _
  have hstep :
      c₂ ^ (2 * m) *
          ((primitiveConstant * lam) ^ (2 * m) / L) ≤
        c₂ ^ 2 *
          ((primitiveConstant * lam) ^ (2 * m) / L) := by
    refine mul_le_mul_of_nonneg_right ?_
      (div_nonneg hpow0 hL0.le)
    exact pow_le_pow_of_le_one hc₂0.le hc₂1 (by omega)
  have hfinal :
      c₂ ^ 2 * ((primitiveConstant * lam) ^ (2 * m) / L) =
        (primitiveConstant * lam) ^ (2 * m) *
          (min supportConstant 1 ^ 4 /
            (supportConstant ^ 2 * L)) := by
    rw [hc₂def]
    field_simp
  calc
    (∑' p : R324RefinedScheduleIndex m × ℕ,
        ρ.r324SignedRouteSlotWeight lam hm ε i p) =
        |lamEps lam ε| ^ (2 * m) * T := hrw
    _ = lam ^ (2 * m) / L ^ m * T := by
      rw [abs_lamEps_pow_two_mul hlam]
    _ ≤ c₂ ^ (2 * m) *
          ((primitiveConstant * lam) ^ (2 * m) / L) := hmul
    _ ≤ c₂ ^ 2 *
          ((primitiveConstant * lam) ^ (2 * m) / L) := hstep
    _ = (primitiveConstant * lam) ^ (2 * m) *
          (min supportConstant 1 ^ 4 /
            (supportConstant ^ 2 * L)) := hfinal
    _ ≤ ∫ z,
          primitiveInsertedMajorant
            primitiveConstant lam ε supportConstant m z
          ∂paperMeasure :=
      le_integral_primitiveInsertedMajorant
        primitiveConstant lam ε supportConstant m hε hε1 hsupport

/-! ## The slot budget dominates the interior budget -/

/-- Every reciprocal routed cost is at least one. -/
theorem one_le_r324GroupedIncrementCost
    {m : ℕ} (hm : 0 < m) (b : ℕ) (i : Fin m) :
    1 ≤ SmoothCutoff.r324GroupedIncrementCost hm b i := by
  unfold SmoothCutoff.r324GroupedIncrementCost
  exact one_le_pow₀ (le_add_of_nonneg_right (sq_nonneg _))

/-- Coupling-free summability of the grouped slot series, extracted
from the proved signed-route summability at coupling `1`. -/
theorem summable_groupedCoreL1_mul_cost
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hlog : 1 ≤ |Real.log ε|) (i : Fin m) :
    Summable (fun p : R324RefinedScheduleIndex m × ℕ =>
      ρ.r324GroupedRefinedCoreL1 hm ε p *
        SmoothCutoff.r324GroupedIncrementCost hm p.2 i) := by
  have hL0 : 0 < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  have hlamEps : lamEps 1 ε ≠ 0 := by
    unfold lamEps
    exact (div_pos one_pos (Real.sqrt_pos.mpr hL0)).ne'
  have ha : |lamEps 1 ε| ^ (2 * m) ≠ 0 :=
    pow_ne_zero _ (abs_ne_zero.mpr hlamEps)
  have hsum := ρ.summable_r324SignedRouteSlotWeight 1 hm hε i
  refine (hsum.mul_left (|lamEps 1 ε| ^ (2 * m))⁻¹).congr fun p => ?_
  rw [r324SignedRouteSlotWeight_eq_pow_mul, ← mul_assoc,
    inv_mul_cancel₀ ha, one_mul]

/-- **Blockwise triangle comparison.**  The interior `L¹` mass of one
refined fibre is dominated by the `ℕ`-series of its grouped-core `L¹`
masses: the common-increment groups reassemble the fibre exactly
(`tsum_r324KeyGroupedRefinedEndpointCore`), and the norm passes inside
the countable regrouping by Tonelli. -/
theorem r324RefinedInteriorCoreIntegral_le_tsum_groupedCoreL1
    (ρ : SmoothCutoff) {m : ℕ} (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m)
    (hsum : Summable fun b : ℕ =>
      ρ.r324GroupedRefinedCoreL1 hm ε (p, b)) :
    r324RefinedInteriorCoreIntegral ρ ε m p ≤
      ∑' b : ℕ, ρ.r324GroupedRefinedCoreL1 hm ε (p, b) := by
  have hmeas :
      AEStronglyMeasurable
        (fun v : Fin (2 * m) → T4 =>
          ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
            (r324RefinedScheduleRepresentative p) v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    ((measurable_r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
      (r324RefinedScheduleRepresentative p)).norm).aestronglyMeasurable
  have hint := fun b : ℕ =>
    ρ.integrable_norm_r324KeyGroupedRefinedEndpointCore hm hε p b
  have hCoreL1_nonneg : ∀ b : ℕ,
      0 ≤ ρ.r324GroupedRefinedCoreL1 hm ε (p, b) := fun b =>
    ρ.r324GroupedRefinedCoreL1_nonneg hm ε (p, b)
  have hpoint : ∀ v : Fin (2 * m) → T4,
      ENNReal.ofReal
          ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
            (r324RefinedScheduleRepresentative p) v‖ ≤
        ∑' b : ℕ,
          ENNReal.ofReal
            ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖ := by
    intro v
    have hsummable :=
      ρ.summable_r324KeyGroupedRefinedEndpointCore hm hε p v
    have hnorm : Summable fun b : ℕ =>
        ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖ :=
      summable_norm_iff.mpr hsummable
    calc
      ENNReal.ofReal
          ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
            (r324RefinedScheduleRepresentative p) v‖ =
          ENNReal.ofReal
            ‖∑' b : ℕ,
              ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖ := by
        rw [ρ.tsum_r324KeyGroupedRefinedEndpointCore hm hε p v]
      _ ≤ ENNReal.ofReal
            (∑' b : ℕ,
              ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖) :=
        ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm hnorm)
      _ = ∑' b : ℕ,
            ENNReal.ofReal
              ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖ :=
        ENNReal.ofReal_tsum_of_nonneg
          (fun b => norm_nonneg _) hnorm
  have hkey :
      (∫⁻ v : Fin (2 * m) → T4,
          ENNReal.ofReal
            ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
              (r324RefinedScheduleRepresentative p) v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
        ENNReal.ofReal
          (∑' b : ℕ, ρ.r324GroupedRefinedCoreL1 hm ε (p, b)) := by
    calc
      (∫⁻ v : Fin (2 * m) → T4,
          ENNReal.ofReal
            ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
              (r324RefinedScheduleRepresentative p) v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) ≤
          ∫⁻ v : Fin (2 * m) → T4,
            ∑' b : ℕ,
              ENNReal.ofReal
                ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
        lintegral_mono hpoint
      _ = ∑' b : ℕ,
            ∫⁻ v : Fin (2 * m) → T4,
              ENNReal.ofReal
                ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖
              ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
        lintegral_tsum fun b =>
          (ENNReal.measurable_ofReal.comp_aemeasurable
            (hint b).aestronglyMeasurable.aemeasurable)
      _ = ∑' b : ℕ,
            ENNReal.ofReal (ρ.r324GroupedRefinedCoreL1 hm ε (p, b)) :=
        tsum_congr fun b =>
          (ofReal_integral_eq_lintegral_ofReal (hint b)
            (Filter.Eventually.of_forall fun v => norm_nonneg _)).symm
      _ = ENNReal.ofReal
            (∑' b : ℕ, ρ.r324GroupedRefinedCoreL1 hm ε (p, b)) :=
        (ENNReal.ofReal_tsum_of_nonneg hCoreL1_nonneg hsum).symm
  have hrw :
      r324RefinedInteriorCoreIntegral ρ ε m p =
        (∫⁻ v : Fin (2 * m) → T4,
          ENNReal.ofReal
            ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
              (r324RefinedScheduleRepresentative p) v‖
          ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)).toReal := by
    unfold r324RefinedInteriorCoreIntegral
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun v => norm_nonneg _) hmeas
  rw [hrw]
  calc
    (∫⁻ v : Fin (2 * m) → T4,
        ENNReal.ofReal
          ‖r324RefinedEndpointCore ρ ε m p.1.1 p.2.1
            (r324RefinedScheduleRepresentative p) v‖
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)).toReal ≤
        (ENNReal.ofReal
          (∑' b : ℕ, ρ.r324GroupedRefinedCoreL1 hm ε (p, b))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
    _ = ∑' b : ℕ, ρ.r324GroupedRefinedCoreL1 hm ε (p, b) :=
      ENNReal.toReal_ofReal (tsum_nonneg hCoreL1_nonneg)

/-- **The slot budget dominates the interior budget.**  For every
refined fibre, at the marked slot `0`: the fibre's interior `L¹` mass
is at most its own grouped slot series (triangle comparison, cost
`≥ 1`), which is a nonnegative sub-series of the full slot series.
The factor `16` is absorbed by `C ↦ 4C` since `16 ≤ 16^m`. -/
theorem r324InteriorCoreLogBudget_of_slotLogBudget
    {ρ : SmoothCutoff} {ε : ℝ} {m : ℕ}
    {primitiveConstant : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hlog : 1 ≤ |Real.log ε|)
    (budget : R324SlotLogBudget ρ hm ε primitiveConstant) :
    R324InteriorCoreLogBudget ρ ε m (4 * primitiveConstant) := by
  intro p
  set i₀ : Fin m := ⟨0, hm⟩ with hi₀
  have hL0 : 0 < |Real.log ε| := lt_of_lt_of_le one_pos hlog
  have hsumBig := summable_groupedCoreL1_mul_cost ρ hm hε hlog i₀
  have hsumFiber : Summable fun b : ℕ =>
      ρ.r324GroupedRefinedCoreL1 hm ε (p, b) *
        SmoothCutoff.r324GroupedIncrementCost hm b i₀ :=
    hsumBig.prod_factor p
  have hterm : ∀ b : ℕ,
      ρ.r324GroupedRefinedCoreL1 hm ε (p, b) ≤
        ρ.r324GroupedRefinedCoreL1 hm ε (p, b) *
          SmoothCutoff.r324GroupedIncrementCost hm b i₀ := fun b =>
    le_mul_of_one_le_right
      (ρ.r324GroupedRefinedCoreL1_nonneg hm ε (p, b))
      (one_le_r324GroupedIncrementCost hm b i₀)
  have hsumCore : Summable fun b : ℕ =>
      ρ.r324GroupedRefinedCoreL1 hm ε (p, b) :=
    hsumFiber.of_nonneg_of_le
      (fun b => ρ.r324GroupedRefinedCoreL1_nonneg hm ε (p, b))
      hterm
  have h1 :=
    r324RefinedInteriorCoreIntegral_le_tsum_groupedCoreL1
      ρ hm hε p hsumCore
  have h2 : (∑' b : ℕ, ρ.r324GroupedRefinedCoreL1 hm ε (p, b)) ≤
      ∑' b : ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε (p, b) *
          SmoothCutoff.r324GroupedIncrementCost hm b i₀ :=
    Summable.tsum_le_tsum hterm hsumCore hsumFiber
  have h3 : (∑' b : ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε (p, b) *
          SmoothCutoff.r324GroupedIncrementCost hm b i₀) ≤
      ∑' q : R324RefinedScheduleIndex m × ℕ,
        ρ.r324GroupedRefinedCoreL1 hm ε q *
          SmoothCutoff.r324GroupedIncrementCost hm q.2 i₀ := by
    refine Summable.tsum_le_tsum_of_inj (fun b : ℕ => (p, b))
      (fun a b hab => (Prod.mk.injEq _ _ _ _).mp hab |>.2)
      (fun q _ => mul_nonneg
        (ρ.r324GroupedRefinedCoreL1_nonneg hm ε q)
        (SmoothCutoff.r324GroupedIncrementCost_pos hm q.2 i₀).le)
      (fun b => le_rfl) hsumFiber hsumBig
  have hCoreT :
      r324RefinedInteriorCoreIntegral ρ ε m p ≤
        ∑' q : R324RefinedScheduleIndex m × ℕ,
          ρ.r324GroupedRefinedCoreL1 hm ε q *
            SmoothCutoff.r324GroupedIncrementCost hm q.2 i₀ :=
    h1.trans (h2.trans h3)
  have hbud := budget i₀
  have hchain :
      16 * (|Real.log ε| * r324RefinedInteriorCoreIntegral ρ ε m p) ≤
        16 * (primitiveConstant ^ (2 * m) * |Real.log ε| ^ m) := by
    have hstep :
        |Real.log ε| * r324RefinedInteriorCoreIntegral ρ ε m p ≤
          primitiveConstant ^ (2 * m) * |Real.log ε| ^ m :=
      le_trans (mul_le_mul_of_nonneg_left hCoreT hL0.le) hbud
    linarith
  refine hchain.trans ?_
  have hpow : (16 : ℝ) * primitiveConstant ^ (2 * m) ≤
      (4 * primitiveConstant) ^ (2 * m) := by
    rw [mul_pow, show (4 : ℝ) ^ (2 * m) = 16 ^ m by
      rw [pow_mul]; norm_num]
    have h16 : (16 : ℝ) ≤ 16 ^ m := by
      calc (16 : ℝ) = 16 ^ 1 := (pow_one _).symm
        _ ≤ 16 ^ m := pow_le_pow_right₀ (by norm_num) hm
    have hC2 : (0 : ℝ) ≤ primitiveConstant ^ (2 * m) :=
      (even_two_mul m).pow_nonneg _
    nlinarith
  calc
    16 * (primitiveConstant ^ (2 * m) * |Real.log ε| ^ m) =
        (16 * primitiveConstant ^ (2 * m)) * |Real.log ε| ^ m := by
      ring
    _ ≤ (4 * primitiveConstant) ^ (2 * m) * |Real.log ε| ^ m :=
      mul_le_mul_of_nonneg_right hpow (pow_nonneg (abs_nonneg _) m)

/-! ## The capstone assembly -/

/-- **The R-324 deterministic moment paper bound from the two
logarithmic budgets.**  Both inputs of the P-3.5b-det chain are consumed
in their reduced, coupling-free logarithmic form (at the
support constant `1`): the interior-core budget discharges the middle
estimate at every Fourier mode, and the slot budget discharges the
signed routed collapse datum.  Everything else — the direct Fourier
evaluation of the four endpoint legs, the countable regrouping of the
route series, the majorant integrations, and the mode-decay bracket of
(3.24) — is unconditional. -/
theorem exists_deterministicMoment_paper_bound_of_logBudgets
    {primitiveConstant : ℝ}
    (hprimitive : 0 < primitiveConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324InteriorCoreLogBudget ρ ε m primitiveConstant →
        R324SlotLogBudget ρ hm ε primitiveConstant →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (16 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_interiorCore_and_slotBudget
      (primitiveConstant := primitiveConstant)
      (supportConstant := 1) hprimitive one_pos
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
    hcore hslot
  have hε1 : ε ≤ 1 := hεsmall.trans (by norm_num)
  have hconst :
      min (1 : ℝ) 1 ^ 2 / 1 * primitiveConstant =
        primitiveConstant := by
    norm_num
  exact
    h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
      (r324InteriorCoreMajorantBound_of_logBudget
        hm hε hε1 hlog hlam one_pos
        (by rw [hconst]; exact hcore))
      (slot_tsum_le_integral_insertedMajorant_of_logBudget
        hm hε hε1 hlog hlam one_pos
        (by rw [hconst]; exact hslot))

/-- Literal decay form of the estimate: the `min` bracket of
`paperDeterministicMomentRHS` is bounded by the P-3.5b-det
decay `ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴⟨ε²(α+β)⟩⁻⁸`. -/
theorem exists_deterministicMoment_decay_bound_of_logBudgets
    {primitiveConstant : ℝ}
    (hprimitive : 0 < primitiveConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324InteriorCoreLogBudget ρ ε m primitiveConstant →
        R324SlotLogBudget ρ hm ε primitiveConstant →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((16 * primitiveConstant) * lam) ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_logBudgets hprimitive
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
    hcore hslot
  refine
    (h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc
      hcore hslot).trans ?_
  exact
    paperDeterministicMomentRHS_le_decayBracket
      outerConstant (16 * primitiveConstant) lam ε m α β
      houter.le
      (mul_nonneg (by positivity) hlam)

/-! ## The single-residual capstone -/

/-- The slot budget is monotone in its constant. -/
theorem R324SlotLogBudget.mono
    {ρ : SmoothCutoff} {m : ℕ} {hm : 0 < m} {ε : ℝ}
    {primitiveConstant primitiveConstant' : ℝ}
    (hC : 0 ≤ primitiveConstant)
    (hle : primitiveConstant ≤ primitiveConstant')
    (budget : R324SlotLogBudget ρ hm ε primitiveConstant) :
    R324SlotLogBudget ρ hm ε primitiveConstant' := by
  intro i
  refine (budget i).trans ?_
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hC hle (2 * m))
    (pow_nonneg (abs_nonneg _) m)

/-- **The R-324 deterministic moment paper bound from the slot budget
alone.**  The interior-core budget is *derived* from the slot budget by
the blockwise triangle comparison, so a single residual scalar
inequality — the `|log ε|`-weighted slot series against
`C^{2m}|log ε|^m` — yields the complete paper bound (3.24) with power
constant `64C`. -/
theorem exists_deterministicMoment_paper_bound_of_slotBudget
    {primitiveConstant : ℝ}
    (hprimitive : 0 < primitiveConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324SlotLogBudget ρ hm ε primitiveConstant →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          paperDeterministicMomentRHS outerConstant
            (64 * primitiveConstant) lam ε m α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_logBudgets
      (primitiveConstant := 4 * primitiveConstant)
      (by positivity)
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc hslot
  have hcore :
      R324InteriorCoreLogBudget ρ ε m (4 * primitiveConstant) :=
    r324InteriorCoreLogBudget_of_slotLogBudget hm hε hlog hslot
  have hslot' :
      R324SlotLogBudget ρ hm ε (4 * primitiveConstant) :=
    hslot.mono hprimitive.le
      (by nlinarith)
  have hbound :=
    h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc hcore hslot'
  have hconst : (16 : ℝ) * (4 * primitiveConstant) =
      64 * primitiveConstant := by ring
  rwa [hconst] at hbound

/-- Literal decay form of the single-residual capstone. -/
theorem exists_deterministicMoment_decay_bound_of_slotBudget
    {primitiveConstant : ℝ}
    (hprimitive : 0 < primitiveConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 →
        1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        R324SlotLogBudget ρ hm ε primitiveConstant →
        ‖deterministicMomentPairingSum ρ lam ε m α β‖ ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((64 * primitiveConstant) * lam) ^ (2 * m - 2) *
            paperDeterministicMomentDecay ε α β := by
  obtain ⟨outerConstant, houter, h⟩ :=
    exists_deterministicMoment_paper_bound_of_slotBudget hprimitive
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc hslot
  refine
    (h ρ lam ε m hm α β hlam hε hεsmall hlog hmtrunc hslot).trans ?_
  exact
    paperDeterministicMomentRHS_le_decayBracket
      outerConstant (64 * primitiveConstant) lam ε m α β
      houter.le
      (mul_nonneg (by positivity) hlam)

end

end Anderson4D
