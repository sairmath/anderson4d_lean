import Anderson4D.DetParametrix.Paper42_Moment.R324InsertedMajorantBridge

/-!
# The interior-core reduction of the R-324 middle estimate (INEQ 1)

This file quantifies the right-hand side of the mode-free interior
estimate `R324InteriorCoreMajorantBound` and reduces the estimate to a
single logarithmic-scale budget on the interior `L¹` mass which is free
of the coupling `λ`, the support constant, and the majorant integral:

* `le_integral_primitiveInsertedMajorant` — the integrated inserted
  Proposition 4.1 majorant is bounded *below* by
  `(Cλ)^{2n} · min(c,1)⁴/(c² |log ε|)`, coming from the near-field term
  `ε⁻²/|log ε| · |z|⁻² 1_{|z| ≤ cε}` alone: on the ball `|z| ≤ r`,
  `r = min (cε) 1`, the kernel is at least `(cε)⁻²` and the ball has
  `paperMeasure` at least `r⁴`;

* `R324InteriorCoreLogBudget` — the residual scalar inequality
  `16 |log ε| · (interior L¹ mass) ≤ C^{2m} |log ε|^m`;

* `r324InteriorCoreMajorantBound_of_logBudget` — the budget implies
  `R324InteriorCoreMajorantBound` for every coupling `λ ≥ 0`, because
  `|λ_ε|^{2m} = λ^{2m}/|log ε|^m` matches the coupling power of the
  inserted majorant exactly.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Explicit `paperMeasure` mass of small boxes -/

/-- The closed per-coordinate box of radius `r/2` lies in the closed
`torusDistSq`-ball of radius `r`. -/
theorem box_subset_torusDistSq_le (r : ℝ) :
    (Set.univ.pi fun _ : Fin dim =>
        Metric.closedBall (0 : AddCircle (2 * Real.pi)) (r / 2)) ⊆
      {z : T4 | torusDistSq z ≤ r ^ 2} := by
  intro z hz
  rw [Set.mem_pi] at hz
  have hcoord : ∀ i : Fin dim, ‖z i‖ ≤ r / 2 := by
    intro i
    have := hz i (Set.mem_univ i)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hsum : torusDistSq z ≤ ∑ _i : Fin dim, (r / 2) ^ 2 := by
    rw [torusDistSq_eq_sum_norm_sq]
    refine Finset.sum_le_sum fun i _ => ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
  refine Set.mem_setOf_eq ▸ hsum.trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  nlinarith [sq_nonneg r]

/-- One coordinate factor: the probability Haar mass of the closed arc
of radius `r/2` is `r/(2π)` (as long as `r ≤ 2π`), stated
multiplicatively. -/
theorem two_pi_mul_haarAddCircle_closedBall
    (r : ℝ) (hr1 : r ≤ 1) :
    ENNReal.ofReal (2 * Real.pi) *
        AddCircle.haarAddCircle
          (Metric.closedBall (0 : AddCircle (2 * Real.pi)) (r / 2)) =
      ENNReal.ofReal r := by
  have hvol :=
    AddCircle.volume_closedBall (2 * Real.pi)
      (x := (0 : AddCircle (2 * Real.pi))) (r / 2)
  rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply,
    smul_eq_mul] at hvol
  rw [hvol]
  congr 1
  rw [min_eq_right]
  · ring
  · have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith

/-- The box of per-coordinate radius `r/2` has `paperMeasure` exactly
`r⁴`, for `0 ≤ r ≤ 1`. -/
theorem paperMeasure_box (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    paperMeasure
        (Set.univ.pi fun _ : Fin dim =>
          Metric.closedBall (0 : AddCircle (2 * Real.pi)) (r / 2)) =
      ENNReal.ofReal (r ^ 4) := by
  unfold paperMeasure haarT4
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  have hprod :
      (∏ _i : Fin dim,
        AddCircle.haarAddCircle
          (Metric.closedBall (0 : AddCircle (2 * Real.pi)) (r / 2))) =
      AddCircle.haarAddCircle
          (Metric.closedBall (0 : AddCircle (2 * Real.pi)) (r / 2)) ^
        (4 : ℕ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod]
  have hofReal :
      ENNReal.ofReal ((2 * Real.pi) ^ (dim : ℕ)) =
        ENNReal.ofReal (2 * Real.pi) ^ (4 : ℕ) := by
    rw [ENNReal.ofReal_pow (by positivity)]
  rw [hofReal, ← mul_pow, two_pi_mul_haarAddCircle_closedBall r hr1,
    ← ENNReal.ofReal_pow hr0]

/-! ## Lower bound for the integrated inserted majorant -/

/-- The inserted majorant is nonnegative with no sign hypotheses on the
coupling: the common exponent `2n` is even. -/
theorem primitiveInsertedMajorant_nonneg'
    (C lam ε supportConstant : ℝ) (n : ℕ) (z : T4) :
    0 ≤ primitiveInsertedMajorant C lam ε supportConstant n z := by
  unfold primitiveInsertedMajorant
  apply mul_nonneg ((even_two_mul n).pow_nonneg (C * lam))
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
        (invSqKer_nonneg z))
      (primitiveSupportIndicator_nonneg supportConstant ε z)
  · exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
      (pow_nonneg
        (inv_nonneg.mpr
          (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 2)

/-- **Quantitative lower bound for the integrated inserted majorant.**
The near-field term alone contributes
`(Cλ)^{2n} · min(c,1)⁴/(c²|log ε|)`, where `c` is the support constant:
on the punctured box of radius `min (cε) 1` the kernel factor is at
least `(cε)⁻²` and the box has `paperMeasure` mass `min (cε) 1 ^ 4`. -/
theorem le_integral_primitiveInsertedMajorant
    (C lam ε supportConstant : ℝ) (n : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hsupport : 0 < supportConstant) :
    (C * lam) ^ (2 * n) *
        (min supportConstant 1 ^ 4 /
          (supportConstant ^ 2 * |Real.log ε|)) ≤
      ∫ z, primitiveInsertedMajorant C lam ε supportConstant n z
        ∂paperMeasure := by
  set r : ℝ := min (supportConstant * ε) 1 with hrdef
  have hr0 : 0 < r := lt_min (by positivity) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hrsupp : r ≤ supportConstant * ε := min_le_left _ _
  set box : Set T4 :=
    Set.univ.pi fun _ : Fin dim =>
      Metric.closedBall (0 : AddCircle (2 * Real.pi)) (r / 2)
    with hboxdef
  set S : Set T4 := box \ {0} with hSdef
  have hboxmeas : MeasurableSet box :=
    MeasurableSet.univ_pi fun _ => measurableSet_closedBall
  have hSmeas : MeasurableSet S :=
    hboxmeas.diff (measurableSet_singleton 0)
  have hμS : paperMeasure S = ENNReal.ofReal (r ^ 4) := by
    rw [hSdef, measure_sdiff_null (paperMeasure_singleton 0)]
    exact paperMeasure_box r hr0.le hr1
  set κ : ℝ :=
    (C * lam) ^ (2 * n) *
      ((ε⁻¹ ^ 2 / |Real.log ε|) * ((supportConstant * ε) ^ 2)⁻¹)
    with hκdef
  have hpow0 : (0 : ℝ) ≤ (C * lam) ^ (2 * n) :=
    (even_two_mul n).pow_nonneg (C * lam)
  have hκ0 : 0 ≤ κ := by
    refine mul_nonneg hpow0 ?_
    positivity
  have hpoint : ∀ z ∈ S,
      κ ≤ primitiveInsertedMajorant C lam ε supportConstant n z := by
    intro z hz
    obtain ⟨hzbox, hz0⟩ := hz
    rw [Set.mem_singleton_iff] at hz0
    have htds_pos : 0 < torusDistSq z :=
      (torusDistSq_nonneg z).lt_of_ne
        (fun h => hz0 ((torusDistSq_eq_zero_iff z).mp h.symm))
    have htds_le : torusDistSq z ≤ (supportConstant * ε) ^ 2 :=
      (box_subset_torusDistSq_le r hzbox).trans
        (pow_le_pow_left₀ hr0.le hrsupp 2)
    have hind : primitiveSupportIndicator supportConstant ε z = 1 :=
      primitiveSupportIndicator_eq_one htds_le
    have hker : ((supportConstant * ε) ^ 2)⁻¹ ≤ invSqKer z := by
      unfold invSqKer
      exact inv_anti₀ htds_pos htds_le
    have hfirst :
        (ε⁻¹ ^ 2 / |Real.log ε|) * ((supportConstant * ε) ^ 2)⁻¹ ≤
          (ε⁻¹ ^ 2 / |Real.log ε|) * invSqKer z *
            primitiveSupportIndicator supportConstant ε z := by
      rw [hind, mul_one]
      exact mul_le_mul_of_nonneg_left hker
        (div_nonneg (by positivity) (abs_nonneg _))
    have hsecond :
        0 ≤ (1 / |Real.log ε| ^ 2) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 2 := by
      positivity
    unfold primitiveInsertedMajorant
    rw [hκdef]
    exact mul_le_mul_of_nonneg_left (by linarith) hpow0
  have hmajint :=
    integrable_primitiveInsertedMajorant C lam ε supportConstant n hε
  have hμStop : paperMeasure S ≠ ⊤ := by
    rw [hμS]
    exact ENNReal.ofReal_ne_top
  calc
    (C * lam) ^ (2 * n) *
        (min supportConstant 1 ^ 4 /
          (supportConstant ^ 2 * |Real.log ε|)) ≤ κ * r ^ 4 := by
      rw [hκdef]
      have hrmin : min supportConstant 1 * ε ≤ r := by
        rw [hrdef]
        calc
          min supportConstant 1 * ε =
              min (supportConstant * ε) (1 * ε) :=
            min_mul_of_nonneg _ _ hε.le
          _ ≤ min (supportConstant * ε) 1 := by
            rw [one_mul]
            exact min_le_min (le_refl _) hε1
      have hkey : min supportConstant 1 ^ 4 * ε ^ 4 ≤ r ^ 4 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hrmin 4
      have hXeq :
          min supportConstant 1 ^ 4 / supportConstant ^ 2 =
            ε⁻¹ ^ 2 * ((supportConstant * ε) ^ 2)⁻¹ *
              (min supportConstant 1 ^ 4 * ε ^ 4) := by
        field_simp
      have hmid :
          ε⁻¹ ^ 2 * ((supportConstant * ε) ^ 2)⁻¹ *
              (min supportConstant 1 ^ 4 * ε ^ 4) ≤
            ε⁻¹ ^ 2 * ((supportConstant * ε) ^ 2)⁻¹ * r ^ 4 :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      have hscalar :
          min supportConstant 1 ^ 4 /
              (supportConstant ^ 2 * |Real.log ε|) ≤
            (ε⁻¹ ^ 2 / |Real.log ε|) *
              ((supportConstant * ε) ^ 2)⁻¹ * r ^ 4 := by
        have hL : (0 : ℝ) ≤ |Real.log ε|⁻¹ :=
          inv_nonneg.mpr (abs_nonneg _)
        calc
          min supportConstant 1 ^ 4 /
              (supportConstant ^ 2 * |Real.log ε|) =
              (min supportConstant 1 ^ 4 / supportConstant ^ 2) *
                |Real.log ε|⁻¹ := by
            rw [div_mul_eq_div_div, div_eq_mul_inv]
          _ ≤ (ε⁻¹ ^ 2 * ((supportConstant * ε) ^ 2)⁻¹ * r ^ 4) *
                |Real.log ε|⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ hL
            rw [hXeq]
            exact hmid
          _ = (ε⁻¹ ^ 2 / |Real.log ε|) *
                ((supportConstant * ε) ^ 2)⁻¹ * r ^ 4 := by
            ring
      calc
        (C * lam) ^ (2 * n) *
            (min supportConstant 1 ^ 4 /
              (supportConstant ^ 2 * |Real.log ε|)) ≤
            (C * lam) ^ (2 * n) *
              ((ε⁻¹ ^ 2 / |Real.log ε|) *
                ((supportConstant * ε) ^ 2)⁻¹ * r ^ 4) :=
          mul_le_mul_of_nonneg_left hscalar hpow0
        _ = (C * lam) ^ (2 * n) *
              ((ε⁻¹ ^ 2 / |Real.log ε|) *
                ((supportConstant * ε) ^ 2)⁻¹) * r ^ 4 := by
          ring
    _ = ∫ _z in S, κ ∂paperMeasure := by
      rw [setIntegral_const, measureReal_def, hμS,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm]
    _ ≤ ∫ z in S,
          primitiveInsertedMajorant C lam ε supportConstant n z
          ∂paperMeasure := by
      refine setIntegral_mono_on ?_ hmajint.integrableOn hSmeas hpoint
      exact integrableOn_const hμStop
    _ ≤ ∫ z, primitiveInsertedMajorant C lam ε supportConstant n z
          ∂paperMeasure :=
      setIntegral_le_integral hmajint
        (Filter.Eventually.of_forall
          (primitiveInsertedMajorant_nonneg' C lam ε supportConstant n))

/-! ## The residual logarithmic budget -/

/-- The doubled coupling power factors through the logarithmic window:
`|λ_ε|^{2m} = λ^{2m}/|log ε|^m`. -/
theorem abs_lamEps_pow_two_mul
    {lam : ℝ} (hlam : 0 ≤ lam) (ε : ℝ) (m : ℕ) :
    |lamEps lam ε| ^ (2 * m) =
      lam ^ (2 * m) / |Real.log ε| ^ m := by
  unfold lamEps
  rw [abs_div, abs_of_nonneg hlam,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow]
  congr 1
  rw [pow_mul, Real.sq_sqrt (abs_nonneg _)]

/-- **The residual interior-core budget (INEQ 1, reduced form).**  A
single scalar inequality at the logarithmic scale: the interior `L¹`
mass of every refined fibre, once weighted by one power of `|log ε|`,
is controlled by `C^{2m} |log ε|^m`.  This is the iterated
Proposition 4.1 content of the middle estimate; it mentions no coupling
`λ`, no Fourier mode, no majorant integral, and no support constant. -/
def R324InteriorCoreLogBudget
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (primitiveConstant : ℝ) : Prop :=
  ∀ p : R324RefinedScheduleIndex m,
    16 * (|Real.log ε| * r324RefinedInteriorCoreIntegral ρ ε m p) ≤
      primitiveConstant ^ (2 * m) * |Real.log ε| ^ m

/-- **The logarithmic budget discharges the mode-free interior
estimate.**  The coupling powers match exactly:
`|λ_ε|^{2m} = λ^{2m}/|log ε|^m` on the left, `(Cλ)^{2m}` inside the
integrated majorant on the right; the leftover `|log ε|^{m-1}` of the
budget is absorbed by the `1/|log ε|` of the majorant's near-field
mass.  The support-constant distortion `min(c,1)²/c ≤ 1` is paid inside
the budget's constant. -/
theorem r324InteriorCoreMajorantBound_of_logBudget
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|) (hlam : 0 ≤ lam)
    (hsupport : 0 < supportConstant)
    (budget :
      R324InteriorCoreLogBudget ρ ε m
        (min supportConstant 1 ^ 2 / supportConstant *
          primitiveConstant)) :
    R324InteriorCoreMajorantBound ρ lam ε m
      primitiveConstant supportConstant := by
  intro p
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
  have hLne : L ≠ 0 := hL0.ne'
  set Core : ℝ := r324RefinedInteriorCoreIntegral ρ ε m p
    with hCoredef
  have hbud : 16 * (L * Core) ≤
      (c₂ * primitiveConstant) ^ (2 * m) * L ^ m :=
    budget p
  have hfactor : (0 : ℝ) ≤ lam ^ (2 * m) / L ^ (m + 1) := by
    positivity
  have hmul :=
    mul_le_mul_of_nonneg_left hbud hfactor
  have heqL :
      lam ^ (2 * m) / L ^ (m + 1) * (16 * (L * Core)) =
        16 * (lam ^ (2 * m) / L ^ m * Core) := by
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
    16 * (|lamEps lam ε| ^ (2 * m) * Core) =
        16 * (lam ^ (2 * m) / L ^ m * Core) := by
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

end

end Anderson4D
