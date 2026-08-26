import Anderson4D.Continuum.Discretization

/-!
# Singular-chain bounds on individual cells

This file supplies the analytic interface between the torus singular kernel
and the lattice cells of paper §5.1.  The main ingredients are:

* a translation-uniform `O(r²)` bound for one inverse-square kernel on a
  torus ball;
* the corresponding bound on a lattice-cell neighbourhood;
* a far-cell pointwise estimate, with the scale and centre separation kept
  explicit.

These are genuine consequences of `setIntegral_invSqKer_ball_le` and the
cell geometry.  In particular, none of the statements below assumes the
desired `(5.3)` cell integral as a hypothesis.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-! ## Translated ball estimates -/

/-- The inverse-square kernel integrated on a metric ball centred at its
singularity. -/
def invSqKerBallIntegral (x : T4) (r : ℝ) : ℝ :=
  ∫ z in Metric.ball x r, invSqKer (x - z) ∂paperMeasure

theorem measurableSet_torusDistSq_sub_le (x : T4) (r : ℝ) :
    MeasurableSet {z : T4 | torusDistSq (x - z) ≤ r ^ 2} :=
  (measurable_torusDistSq.comp
    (measurable_const.sub measurable_id)) measurableSet_Iic

/-- Translation of the centred `torusDistSq` ball does not change the
inverse-square integral. -/
theorem setIntegral_invSqKer_sub_torusDistSq_le
    (x : T4) (r : ℝ) :
    (∫ z in {z : T4 | torusDistSq (x - z) ≤ r ^ 2},
        invSqKer (x - z) ∂paperMeasure) =
      ∫ z in {z : T4 | torusDistSq z ≤ r ^ 2},
        invSqKer z ∂paperMeasure := by
  let F : T4 → ℝ :=
    {z : T4 | torusDistSq z ≤ r ^ 2}.indicator invSqKer
  have hF : Measurable F := by
    exact measurable_invSqKer.indicator
      (measurable_torusDistSq measurableSet_Iic)
  have hshift :
      (∫ z, F (z - x) ∂paperMeasure) = ∫ z, F z ∂paperMeasure := by
    have hmap := integral_map
      (μ := paperMeasure) (φ := fun z : T4 => z - x)
      (measurePreserving_sub_paper x).measurable.aemeasurable
      hF.aestronglyMeasurable
    rw [(measurePreserving_sub_paper x).map_eq] at hmap
    exact hmap.symm
  have hleft :
      (∫ z in {z : T4 | torusDistSq (x - z) ≤ r ^ 2},
          invSqKer (x - z) ∂paperMeasure) =
        ∫ z, F (z - x) ∂paperMeasure := by
    rw [← integral_indicator (measurableSet_torusDistSq_sub_le x r)]
    apply integral_congr_ae
    filter_upwards with z
    simp only [F]
    have hdist :
        torusDistSq (x - z) = torusDistSq (z - x) := by
      rw [show x - z = -(z - x) by abel, torusDistSq_neg]
    by_cases hz :
        torusDistSq (x - z) ≤ r ^ 2
    · have hz' : torusDistSq (z - x) ≤ r ^ 2 := by
        rwa [← hdist]
      have hmem :
          z ∈ {u : T4 | torusDistSq (x - u) ≤ r ^ 2} := hz
      have hmem' :
          z - x ∈ {u : T4 | torusDistSq u ≤ r ^ 2} := hz'
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem',
        invSqKer_sub_comm]
    · have hz' : ¬torusDistSq (z - x) ≤ r ^ 2 := by
        rwa [← hdist]
      have hmem :
          z ∉ {u : T4 | torusDistSq (x - u) ≤ r ^ 2} := hz
      have hmem' :
          z - x ∉ {u : T4 | torusDistSq u ≤ r ^ 2} := hz'
      rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
  have hright :
      (∫ z in {z : T4 | torusDistSq z ≤ r ^ 2},
          invSqKer z ∂paperMeasure) =
        ∫ z, F z ∂paperMeasure := by
    exact (integral_indicator
      (measurable_torusDistSq measurableSet_Iic)).symm
  rw [hleft, hright]
  exact hshift

/-- **Uniform local mass.**  A translated metric ball of radius `r` carries
at most `C r²` inverse-square mass.  The factor `4` converting the product
sup norm to `torusDistSq` is absorbed into the named constant. -/
theorem invSqKerBallIntegral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : T4) (r : ℝ), 0 < r →
      invSqKerBallIntegral x r ≤ C * r ^ 2 := by
  obtain ⟨C, hC, hball⟩ := setIntegral_invSqKer_ball_le
  refine ⟨4 * C, by positivity, fun x r hr => ?_⟩
  have hmeasMetric : MeasurableSet (Metric.ball x r) :=
    measurableSet_ball
  have hmeasBig :
      MeasurableSet {z : T4 | torusDistSq (x - z) ≤ (2 * r) ^ 2} :=
    measurableSet_torusDistSq_sub_le x (2 * r)
  have hsubset :
      Metric.ball x r ⊆
        {z : T4 | torusDistSq (x - z) ≤ (2 * r) ^ 2} := by
    intro z hz
    have hnorm : ‖x - z‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
    calc
      torusDistSq (x - z) ≤ 4 * ‖x - z‖ ^ 2 :=
        torusDistSq_le_four_mul_sq_norm _
      _ ≤ 4 * r ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hnorm.le 2) (by norm_num)
      _ = (2 * r) ^ 2 := by ring
  unfold invSqKerBallIntegral
  calc
    (∫ z in Metric.ball x r, invSqKer (x - z) ∂paperMeasure)
        ≤ ∫ z in {z : T4 | torusDistSq (x - z) ≤ (2 * r) ^ 2},
            invSqKer (x - z) ∂paperMeasure := by
          exact setIntegral_mono_set
            ((integrable_invSqKer_sub_left x).integrableOn)
            (Filter.Eventually.of_forall fun z => invSqKer_nonneg _)
            (Filter.Eventually.of_forall hsubset)
    _ = ∫ z in {z : T4 | torusDistSq z ≤ (2 * r) ^ 2},
          invSqKer z ∂paperMeasure :=
        setIntegral_invSqKer_sub_torusDistSq_le x (2 * r)
    _ ≤ C * (2 * r) ^ 2 := hball (2 * r) (by positivity)
    _ = (4 * C) * r ^ 2 := by ring

/-- A singleton in one circle factor has zero volume. -/
private theorem volume_singleton_addCircle_cell
    (a : AddCircle (2 * Real.pi)) :
    (volume : Measure (AddCircle (2 * Real.pi))) {a} = 0 := by
  obtain ⟨x₀, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← (AddCircle.measurePreserving_mk
    (2 * Real.pi) (-Real.pi)).measure_preimage
      (measurableSet_singleton _).nullMeasurableSet]
  have hcount : (((↑) : ℝ → AddCircle (2 * Real.pi)) ⁻¹'
      {((x₀ : ℝ) : AddCircle (2 * Real.pi))}).Countable := by
    have hsub : (((↑) : ℝ → AddCircle (2 * Real.pi)) ⁻¹'
        {((x₀ : ℝ) : AddCircle (2 * Real.pi))})
        ⊆ Set.range fun k : ℤ => x₀ + k • (2 * Real.pi) := by
      intro y hy
      have h1 : (y : AddCircle (2 * Real.pi)) = (x₀ : ℝ) := hy
      have h2 : y - x₀ ∈ AddSubgroup.zmultiples (2 * Real.pi) :=
        QuotientAddGroup.eq_iff_sub_mem.mp h1
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
      exact ⟨k, by
        show x₀ + k • (2 * Real.pi) = y
        linarith [hk]⟩
    exact (Set.countable_range _).mono hsub
  rw [Measure.restrict_apply
    (AddCircle.measurable_mk' (measurableSet_singleton _))]
  exact measure_mono_null Set.inter_subset_left
    (hcount.measure_zero volume)

theorem paperMeasure_singleton (x : T4) :
    paperMeasure {x} = 0 := by
  rw [paperMeasure_eq_volume, volume_pi]
  refine measure_mono_null (fun z hz => ?_)
    (Measure.pi_eval_preimage_null (i := (0 : Fin dim))
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (volume_singleton_addCircle_cell (x 0)))
  rw [Set.mem_singleton_iff] at hz
  subst z
  rfl

/-- Metric balls on the paper torus have the expected four-dimensional
volume growth.  This is derived from the inverse-square ball estimate:
away from the null centre, `1 ≤ 4r² |x-z|⁻²` on `B(x,r)`. -/
theorem paperMeasure_ball_toReal_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : T4) (r : ℝ), 0 < r →
      (paperMeasure (Metric.ball x r)).toReal ≤ C * r ^ 4 := by
  obtain ⟨C, hC, hlocal⟩ := invSqKerBallIntegral_le
  refine ⟨4 * C, by positivity, fun x r hr => ?_⟩
  have hmeas : MeasurableSet (Metric.ball x r) := measurableSet_ball
  have hne : ∀ᵐ z ∂paperMeasure, z ≠ x := by
    filter_upwards [compl_mem_ae_iff.mpr
      (paperMeasure_singleton x)] with z hz
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_true]
      using hz
  have hae :
      ∀ᵐ z ∂paperMeasure.restrict (Metric.ball x r),
        (1 : ℝ) ≤ 4 * r ^ 2 * invSqKer (x - z) := by
    filter_upwards [ae_restrict_mem hmeas,
      ae_mono (Measure.restrict_le_self) hne] with z hz hzx
    have hnorm : ‖x - z‖ < r := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
    have hupper : torusDistSq (x - z) ≤ 4 * r ^ 2 := by
      calc
        torusDistSq (x - z) ≤ 4 * ‖x - z‖ ^ 2 :=
          torusDistSq_le_four_mul_sq_norm _
        _ ≤ 4 * r ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hnorm.le 2) (by norm_num)
    have hsub : x - z ≠ 0 := sub_ne_zero.mpr hzx.symm
    have hdist : 0 < torusDistSq (x - z) :=
      (torusDistSq_nonneg _).lt_of_ne
        (fun h => hsub ((torusDistSq_eq_zero_iff _).mp h.symm))
    unfold invSqKer
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hdist).mpr (by simpa using hupper)
  calc
    (paperMeasure (Metric.ball x r)).toReal =
        ∫ _z in Metric.ball x r, (1 : ℝ) ∂paperMeasure := by
          rw [setIntegral_const]
          simp only [smul_eq_mul, mul_one, measureReal_def]
    _ ≤ ∫ z in Metric.ball x r,
          4 * r ^ 2 * invSqKer (x - z) ∂paperMeasure :=
        integral_mono_ae integrableOn_const
          ((integrable_invSqKer_sub_left x).const_mul _).integrableOn hae
    _ = 4 * r ^ 2 * invSqKerBallIntegral x r := by
        unfold invSqKerBallIntegral
        rw [integral_const_mul]
    _ ≤ 4 * r ^ 2 * (C * r ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hlocal x r hr)
          (mul_nonneg (by norm_num) (sq_nonneg r))
    _ = (4 * C) * r ^ 4 := by ring

/-! ## A scale-sensitive one-edge estimate -/

/-- Public norm comparison for the model inverse-square kernel. -/
theorem invSqKer_le_inv_sq_norm_cell (w : T4) :
    invSqKer w ≤ (‖w‖ ^ 2)⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 : torusDistSq (0 : T4) = 0 :=
      (torusDistSq_eq_zero_iff 0).mpr rfl
    unfold invSqKer
    rw [h0]
    simp
  · exact inv_anti₀ (pow_pos (norm_pos_iff.mpr hw) 2)
      (sq_norm_le_torusDistSq w)

/-- If two radius-`r` cells have centres at distance at least `4r`, the
kernel between any two points in the cells is controlled by the inverse
square centre distance. -/
theorem invSqKer_sub_le_of_mem_balls_of_far
    {c d x z : T4} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ Metric.ball c r) (hz : z ∈ Metric.ball d r)
    (hfar : 4 * r ≤ dist c d) :
    invSqKer (x - z) ≤ 4 * (dist c d ^ 2)⁻¹ := by
  rw [Metric.mem_ball] at hx hz
  have hpath : dist c d ≤ dist c x + dist x z + dist z d := by
    calc
      dist c d ≤ dist c x + dist x d := dist_triangle _ _ _
      _ ≤ dist c x + (dist x z + dist z d) :=
        by linarith [dist_triangle x z d]
      _ = dist c x + dist x z + dist z d := by ring
  have hhalf : dist c d / 2 < dist x z := by
    rw [dist_comm c x] at hpath
    linarith
  have hdist : 0 < dist c d := lt_of_lt_of_le (by positivity) hfar
  have hnorm : dist x z = ‖x - z‖ := dist_eq_norm _ _
  have hsquare :
      (dist c d / 2) ^ 2 ≤ ‖x - z‖ ^ 2 := by
    exact pow_le_pow_left₀ (by positivity)
      (by simpa only [hnorm] using hhalf.le) 2
  calc
    invSqKer (x - z) ≤ (‖x - z‖ ^ 2)⁻¹ :=
      invSqKer_le_inv_sq_norm_cell _
    _ ≤ ((dist c d / 2) ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos (by positivity) 2) hsquare
    _ = 4 * (dist c d ^ 2)⁻¹ := by
      field_simp [ne_of_gt hdist]
      ring

/-- The scale-sensitive edge weight generated by integrating one
inverse-square factor over a radius-`r` cell. -/
def metricCellEdgeWeight (r : ℝ) (c d : T4) : ℝ :=
  r ^ 4 / (r ^ 2 + dist c d ^ 2)

theorem metricCellEdgeWeight_nonneg (r : ℝ) (c d : T4) :
    0 ≤ metricCellEdgeWeight r c d := by
  unfold metricCellEdgeWeight
  positivity

/-- **One-cell edge bound.**  Uniformly for `x ∈ B(c,r)`,

`∫_{B(d,r)} |x-z|⁻² dz ≲ r⁴ / (r² + dist(c,d)²)`.

This combines the local `O(r²)` singular mass with the far-cell pointwise
bound and four-dimensional cell volume. -/
theorem invSqKer_cellEdge_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℝ) (_hr : 0 < r) (c d x : T4),
        x ∈ Metric.ball c r →
        (∫ z in Metric.ball d r,
            invSqKer (x - z) ∂paperMeasure) ≤
          C * metricCellEdgeWeight r c d := by
  obtain ⟨Clocal, hClocal, hlocal⟩ := invSqKerBallIntegral_le
  obtain ⟨Cvol, hCvol, hvol⟩ := paperMeasure_ball_toReal_le
  let C := 612 * Clocal + 8 * Cvol
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun r hr c d x hx => ?_⟩
  by_cases hnear : dist c d ≤ 4 * r
  · have hsubset : Metric.ball d r ⊆ Metric.ball x (6 * r) := by
      intro z hz
      rw [Metric.mem_ball] at hx hz ⊢
      have hpath : dist z x ≤ dist z d + dist d c + dist c x := by
        calc
          dist z x ≤ dist z d + dist d x := dist_triangle _ _ _
          _ ≤ dist z d + (dist d c + dist c x) :=
            by linarith [dist_triangle d c x]
          _ = dist z d + dist d c + dist c x := by ring
      rw [dist_comm d c, dist_comm c x] at hpath
      linarith
    have hraw :
        (∫ z in Metric.ball d r,
            invSqKer (x - z) ∂paperMeasure) ≤
          36 * Clocal * r ^ 2 := by
      calc
        (∫ z in Metric.ball d r,
            invSqKer (x - z) ∂paperMeasure)
            ≤ invSqKerBallIntegral x (6 * r) := by
              unfold invSqKerBallIntegral
              exact setIntegral_mono_set
                ((integrable_invSqKer_sub_left x).integrableOn)
                (Filter.Eventually.of_forall fun z =>
                  invSqKer_nonneg _)
                (Filter.Eventually.of_forall hsubset)
        _ ≤ Clocal * (6 * r) ^ 2 :=
          hlocal x (6 * r) (by positivity)
        _ = 36 * Clocal * r ^ 2 := by ring
    have hden :
        r ^ 2 + dist c d ^ 2 ≤ 17 * r ^ 2 := by
      have hsquare :
          dist c d ^ 2 ≤ (4 * r) ^ 2 :=
        pow_le_pow_left₀ (dist_nonneg) hnear 2
      nlinarith
    have hweight :
        r ^ 2 ≤ 17 * metricCellEdgeWeight r c d := by
      have hdenpos : 0 < r ^ 2 + dist c d ^ 2 := by positivity
      unfold metricCellEdgeWeight
      rw [show 17 * (r ^ 4 / (r ^ 2 + dist c d ^ 2)) =
          (17 * r ^ 4) / (r ^ 2 + dist c d ^ 2) by ring]
      apply (le_div_iff₀ hdenpos).mpr
      nlinarith [sq_nonneg r,
        mul_le_mul_of_nonneg_left hden (sq_nonneg r)]
    calc
      (∫ z in Metric.ball d r,
          invSqKer (x - z) ∂paperMeasure)
          ≤ 36 * Clocal * r ^ 2 := hraw
      _ ≤ 612 * Clocal * metricCellEdgeWeight r c d := by
        calc
          36 * Clocal * r ^ 2 =
              (36 * Clocal) * r ^ 2 := by ring
          _ ≤ (36 * Clocal) *
              (17 * metricCellEdgeWeight r c d) :=
            mul_le_mul_of_nonneg_left hweight (by positivity)
          _ = 612 * Clocal * metricCellEdgeWeight r c d := by ring
      _ ≤ C * metricCellEdgeWeight r c d := by
        apply mul_le_mul_of_nonneg_right
          (show 612 * Clocal ≤ C by
            dsimp [C]
            linarith)
          (metricCellEdgeWeight_nonneg r c d)
  · have hfar : 4 * r ≤ dist c d := le_of_not_ge hnear
    have hdist : 0 < dist c d :=
      lt_of_lt_of_le (by positivity) hfar
    have hae :
        ∀ᵐ z ∂paperMeasure.restrict (Metric.ball d r),
          invSqKer (x - z) ≤ 4 * (dist c d ^ 2)⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact invSqKer_sub_le_of_mem_balls_of_far hr hx hz hfar
    have hraw :
        (∫ z in Metric.ball d r,
            invSqKer (x - z) ∂paperMeasure) ≤
          4 * Cvol * r ^ 4 * (dist c d ^ 2)⁻¹ := by
      calc
        (∫ z in Metric.ball d r,
            invSqKer (x - z) ∂paperMeasure)
            ≤ ∫ _z in Metric.ball d r,
                4 * (dist c d ^ 2)⁻¹ ∂paperMeasure :=
              integral_mono_ae
                ((integrable_invSqKer_sub_left x).integrableOn)
                integrableOn_const hae
        _ = (paperMeasure (Metric.ball d r)).toReal *
              (4 * (dist c d ^ 2)⁻¹) := by
              rw [setIntegral_const]
              simp only [smul_eq_mul, measureReal_def]
        _ ≤ (Cvol * r ^ 4) *
              (4 * (dist c d ^ 2)⁻¹) := by
              exact mul_le_mul_of_nonneg_right (hvol d r hr)
                (mul_nonneg (by norm_num) (inv_nonneg.mpr (sq_nonneg _)))
        _ = 4 * Cvol * r ^ 4 * (dist c d ^ 2)⁻¹ := by ring
    have hrle : r ≤ dist c d := by linarith
    have hsquare : r ^ 2 ≤ dist c d ^ 2 :=
      pow_le_pow_left₀ hr.le hrle 2
    have hden :
        r ^ 2 + dist c d ^ 2 ≤ 2 * dist c d ^ 2 := by
      linarith
    have hweight :
        r ^ 4 * (dist c d ^ 2)⁻¹ ≤
          2 * metricCellEdgeWeight r c d := by
      have hdenpos : 0 < r ^ 2 + dist c d ^ 2 := by positivity
      have hdistSq : 0 < dist c d ^ 2 := pow_pos hdist 2
      unfold metricCellEdgeWeight
      rw [show r ^ 4 * (dist c d ^ 2)⁻¹ =
          r ^ 4 / dist c d ^ 2 by rw [div_eq_mul_inv]]
      apply (div_le_iff₀ hdistSq).mpr
      rw [show 2 * (r ^ 4 / (r ^ 2 + dist c d ^ 2)) *
          dist c d ^ 2 =
          r ^ 4 * (2 * dist c d ^ 2 /
            (r ^ 2 + dist c d ^ 2)) by ring]
      have hratio :
          1 ≤ 2 * dist c d ^ 2 /
            (r ^ 2 + dist c d ^ 2) :=
        (le_div_iff₀ hdenpos).mpr (by simpa using hden)
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hratio
          (show 0 ≤ r ^ 4 by positivity))
    calc
      (∫ z in Metric.ball d r,
          invSqKer (x - z) ∂paperMeasure)
          ≤ 4 * Cvol * r ^ 4 * (dist c d ^ 2)⁻¹ := hraw
      _ ≤ 8 * Cvol * metricCellEdgeWeight r c d := by
        calc
          4 * Cvol * r ^ 4 * (dist c d ^ 2)⁻¹ =
              (4 * Cvol) *
                (r ^ 4 * (dist c d ^ 2)⁻¹) := by ring
          _ ≤ (4 * Cvol) *
              (2 * metricCellEdgeWeight r c d) :=
            mul_le_mul_of_nonneg_left hweight (by positivity)
          _ = 8 * Cvol * metricCellEdgeWeight r c d := by ring
      _ ≤ C * metricCellEdgeWeight r c d := by
        apply mul_le_mul_of_nonneg_right
          (show 8 * Cvol ≤ C by
            dsimp [C]
            linarith)
          (metricCellEdgeWeight_nonneg r c d)

/-! ## Non-cyclic chains with every target cell integrated -/

/-- A left-to-right chain in which every vertex listed in `centres` is
integrated over its radius-`r` cell.  The empty chain has value `1`. -/
def integratedCellChain (r : ℝ) (x : T4) : List T4 → ℝ
  | [] => 1
  | d :: ds =>
      ∫ z in Metric.ball d r,
        invSqKer (x - z) * integratedCellChain r z ds
          ∂paperMeasure

/-- Product of the scale-sensitive edge weights along the same path of
cell centres. -/
def metricCellPathWeight (r : ℝ) (c : T4) : List T4 → ℝ
  | [] => 1
  | d :: ds =>
      metricCellEdgeWeight r c d * metricCellPathWeight r d ds

theorem metricCellPathWeight_nonneg (r : ℝ) (c : T4)
    (centres : List T4) :
    0 ≤ metricCellPathWeight r c centres := by
  induction centres generalizing c with
  | nil => simp [metricCellPathWeight]
  | cons d ds ih =>
      exact mul_nonneg (metricCellEdgeWeight_nonneg r c d)
        (ih d)

theorem integratedCellChain_nonneg (r : ℝ) (x : T4)
    (centres : List T4) :
    0 ≤ integratedCellChain r x centres := by
  induction centres generalizing x with
  | nil => simp [integratedCellChain]
  | cons d ds ih =>
      rw [integratedCellChain]
      exact integral_nonneg fun z =>
        mul_nonneg (invSqKer_nonneg _) (ih z)

/-- **Iterated non-cyclic cell collapse.**  Each integrated vertex costs
one factor `C · r⁴/(r²+d²)`.  This is the exact induction used on either
side of a pivot edge in the large-separation branch of paper (5.3). -/
theorem integratedCellChain_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℝ) (_hr : 0 < r) (c x : T4) (centres : List T4),
        x ∈ Metric.ball c r →
        integratedCellChain r x centres ≤
          C ^ centres.length * metricCellPathWeight r c centres := by
  obtain ⟨C, hC, hedge⟩ := invSqKer_cellEdge_le
  refine ⟨C, hC, fun r hr c x centres hx => ?_⟩
  induction centres generalizing c x with
  | nil =>
      simp [integratedCellChain, metricCellPathWeight]
  | cons d ds ih =>
      let K : ℝ :=
        C ^ ds.length * metricCellPathWeight r d ds
      have hK : 0 ≤ K :=
        mul_nonneg (by positivity)
          (metricCellPathWeight_nonneg r d ds)
      have hmono :
          integratedCellChain r x (d :: ds) ≤
            ∫ z in Metric.ball d r,
              invSqKer (x - z) * K ∂paperMeasure := by
        rw [integratedCellChain]
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            mul_nonneg (invSqKer_nonneg _)
              (integratedCellChain_nonneg r z ds))
          ((integrable_invSqKer_sub_left x).mul_const K).integrableOn
          (by
            filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
            exact mul_le_mul_of_nonneg_left
              (ih d z hz) (invSqKer_nonneg _))
      have hedge' :
          (∫ z in Metric.ball d r,
              invSqKer (x - z) ∂paperMeasure) ≤
            C * metricCellEdgeWeight r c d :=
        hedge r hr c d x hx
      calc
        integratedCellChain r x (d :: ds)
            ≤ ∫ z in Metric.ball d r,
                invSqKer (x - z) * K ∂paperMeasure := hmono
        _ = K * (∫ z in Metric.ball d r,
              invSqKer (x - z) ∂paperMeasure) := by
              rw [integral_mul_const]
              ring
        _ ≤ K * (C * metricCellEdgeWeight r c d) :=
          mul_le_mul_of_nonneg_left hedge' hK
        _ = C ^ (d :: ds).length *
              metricCellPathWeight r c (d :: ds) := by
              simp only [List.length_cons, metricCellPathWeight, K,
                pow_succ]
              ring

/-! ## A fixed terminal vertex and a far pivot edge -/

/-- A non-cyclic chain whose final vertex `y` is fixed rather than
integrated. -/
def terminalCellChain (r : ℝ) (x y : T4) : List T4 → ℝ
  | [] => invSqKer (x - y)
  | d :: ds =>
      ∫ z in Metric.ball d r,
        invSqKer (x - z) * terminalCellChain r z y ds
          ∂paperMeasure

/-- The final edge of the path is separated by at least `4r`. -/
def TerminalEdgeFar (r : ℝ) (c e : T4) : List T4 → Prop
  | [] => 4 * r ≤ dist c e
  | d :: ds => TerminalEdgeFar r d e ds

/-- Product of integrated edge weights, followed by the pointwise
inverse-square weight of the fixed terminal edge. -/
def metricTerminalPathWeight (r : ℝ) (c e : T4) : List T4 → ℝ
  | [] => 4 * (dist c e ^ 2)⁻¹
  | d :: ds =>
      metricCellEdgeWeight r c d *
        metricTerminalPathWeight r d e ds

theorem metricTerminalPathWeight_nonneg (r : ℝ) (c e : T4)
    (centres : List T4) :
    0 ≤ metricTerminalPathWeight r c e centres := by
  induction centres generalizing c with
  | nil =>
      simp only [metricTerminalPathWeight]
      positivity
  | cons d ds ih =>
      exact mul_nonneg (metricCellEdgeWeight_nonneg r c d)
        (ih d)

theorem terminalCellChain_nonneg (r : ℝ) (x y : T4)
    (centres : List T4) :
    0 ≤ terminalCellChain r x y centres := by
  induction centres generalizing x with
  | nil =>
      exact invSqKer_nonneg _
  | cons d ds ih =>
      rw [terminalCellChain]
      exact integral_nonneg fun z =>
        mul_nonneg (invSqKer_nonneg _) (ih z)

/-- **Far-pivot chain bound.**  If the last edge of a non-cyclic cell path
is `4r`-separated, all preceding vertices can be integrated successively.
For `k` integrated vertices this has scale `r^(2k) · d_pivot⁻²`. -/
theorem terminalCellChain_le_of_far :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℝ) (_hr : 0 < r) (c e x y : T4)
        (centres : List T4),
        x ∈ Metric.ball c r →
        y ∈ Metric.ball e r →
        TerminalEdgeFar r c e centres →
        terminalCellChain r x y centres ≤
          C ^ centres.length *
            metricTerminalPathWeight r c e centres := by
  obtain ⟨C, hC, hedge⟩ := invSqKer_cellEdge_le
  refine ⟨C, hC, fun r hr c e x y centres hx hy hfar => ?_⟩
  induction centres generalizing c x with
  | nil =>
      simp only [terminalCellChain, List.length_nil, pow_zero, one_mul,
        metricTerminalPathWeight]
      exact invSqKer_sub_le_of_mem_balls_of_far hr hx hy hfar
  | cons d ds ih =>
      let K : ℝ :=
        C ^ ds.length * metricTerminalPathWeight r d e ds
      have hK : 0 ≤ K :=
        mul_nonneg (by positivity)
          (metricTerminalPathWeight_nonneg r d e ds)
      have hmono :
          terminalCellChain r x y (d :: ds) ≤
            ∫ z in Metric.ball d r,
              invSqKer (x - z) * K ∂paperMeasure := by
        rw [terminalCellChain]
        exact integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z =>
            mul_nonneg (invSqKer_nonneg _)
              (terminalCellChain_nonneg r z y ds))
          ((integrable_invSqKer_sub_left x).mul_const K).integrableOn
          (by
            filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
            exact mul_le_mul_of_nonneg_left
              (ih d z hz hfar) (invSqKer_nonneg _))
      have hedge' :
          (∫ z in Metric.ball d r,
              invSqKer (x - z) ∂paperMeasure) ≤
            C * metricCellEdgeWeight r c d :=
        hedge r hr c d x hx
      calc
        terminalCellChain r x y (d :: ds)
            ≤ ∫ z in Metric.ball d r,
                invSqKer (x - z) * K ∂paperMeasure := hmono
        _ = K * (∫ z in Metric.ball d r,
              invSqKer (x - z) ∂paperMeasure) := by
              rw [integral_mul_const]
              ring
        _ ≤ K * (C * metricCellEdgeWeight r c d) :=
          mul_le_mul_of_nonneg_left hedge' hK
        _ = C ^ (d :: ds).length *
              metricTerminalPathWeight r c e (d :: ds) := by
              simp only [List.length_cons, metricTerminalPathWeight, K,
                pow_succ]
              ring

/-! ## The isolated all-near scaling lemma -/

/-- The three-edge, two-variable cell integral left after stripping all
outer edges in the all-near branch of (5.4). -/
def localTripleCellIntegral (r : ℝ) (c₁ c₂ x y : T4) : ℝ :=
  ∫ z₁ in Metric.ball c₁ r,
    ∫ z₂ in Metric.ball c₂ r,
      invSqKer (x - z₁) * invSqKer (z₁ - z₂) *
        invSqKer (z₂ - y) ∂paperMeasure ∂paperMeasure

/-- Exact remaining scale-covariant analytic input for the all-near case.
Unlike a hypothesis restating (5.3), this is only the three-edge local
convolution isolated by the proved path-collapse lemmas above.  The global
unscaled analogue is `triple_conv_invSqKer_le`; closing this predicate
requires a torus-to-Euclidean dilation/periodization lemma. -/
def LocalTripleCellScaleBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (c₀ c₁ c₂ c₃ x y : T4),
      x ∈ Metric.ball c₀ r →
      y ∈ Metric.ball c₃ r →
      dist c₀ c₁ ≤ 4 * r →
      dist c₁ c₂ ≤ 4 * r →
      dist c₂ c₃ ≤ 4 * r →
      localTripleCellIntegral r c₁ c₂ x y ≤ C * r ^ 2

/-! ## Lattice-centred cell neighbourhoods -/

/-- The torus point represented by the Euclidean lattice centre `εy`. -/
def latticeTorusCenter (ε : ℝ) (y : Z4) : T4 :=
  periodizeR4 (cellRepresentative ε y)

/-- An `Rε`-neighbourhood of the lattice centre.  The paper uses a fixed
absolute `R`; keeping it explicit records the cutoff-support dependence. -/
def latticeCellNeighborhood (ε R : ℝ) (y : Z4) : Set T4 :=
  Metric.ball (latticeTorusCenter ε y) (R * ε)

theorem measurableSet_latticeCellNeighborhood (ε R : ℝ) (y : Z4) :
    MeasurableSet (latticeCellNeighborhood ε R y) :=
  measurableSet_ball

theorem invSqKer_integral_latticeCellNeighborhood_le :
  ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R) (y : Z4) (x : T4),
        x ∈ latticeCellNeighborhood ε R y →
        (∫ z in latticeCellNeighborhood ε R y,
            invSqKer (x - z) ∂paperMeasure) ≤
          C * R ^ 2 * ε ^ 2 := by
  obtain ⟨C, hC, hlocal⟩ := invSqKerBallIntegral_le
  refine ⟨4 * C, by positivity, fun ε R hε hR y x hx => ?_⟩
  have hradius : 0 < R * ε := mul_pos hR hε
  have hsubset :
      latticeCellNeighborhood ε R y ⊆ Metric.ball x (2 * (R * ε)) := by
    intro z hz
    unfold latticeCellNeighborhood at hz hx
    rw [Metric.mem_ball] at hz hx
    rw [dist_comm] at hx
    calc
      dist z x ≤ dist z (latticeTorusCenter ε y) +
          dist (latticeTorusCenter ε y) x :=
        dist_triangle _ _ _
      _ < 2 * (R * ε) := by
        linarith
  calc
    (∫ z in latticeCellNeighborhood ε R y,
        invSqKer (x - z) ∂paperMeasure)
        ≤ invSqKerBallIntegral x (2 * (R * ε)) := by
          unfold invSqKerBallIntegral
          exact setIntegral_mono_set
            ((integrable_invSqKer_sub_left x).integrableOn)
            (Filter.Eventually.of_forall fun z => invSqKer_nonneg _)
            (Filter.Eventually.of_forall hsubset)
    _ ≤ C * (2 * (R * ε)) ^ 2 :=
      hlocal x (2 * (R * ε)) (mul_pos (by norm_num) hradius)
    _ = (4 * C) * R ^ 2 * ε ^ 2 := by ring

/-- On a pair of cells whose chosen Euclidean representatives do not wrap
around the torus, the metric cell weight is bounded by the exact lattice
edge weight from (5.3).  The explicit equality hypothesis is precisely the
periodic-boundary interface; no analytic estimate is hidden in it. -/
theorem metricCellEdgeWeight_lattice_le
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (y y' : Z4)
    (hcenter :
      dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
        ε * znorm (y - y')) :
    metricCellEdgeWeight (R * ε)
        (latticeTorusCenter ε y) (latticeTorusCenter ε y') ≤
      (R ^ 2 + R ^ 4) * ε ^ 2 * latticeEdgeWeight y y' := by
  let D : ℝ := znorm (y - y')
  have hD : 0 ≤ D := znorm_nonneg _
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hden₁ : 0 < R ^ 2 + D ^ 2 := by positivity
  have hden₂ : 0 < 1 + D ^ 2 := by positivity
  have hscale :
      metricCellEdgeWeight (R * ε)
          (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
        ε ^ 2 * (R ^ 4 / (R ^ 2 + D ^ 2)) := by
    unfold metricCellEdgeWeight
    rw [hcenter]
    dsimp [D]
    field_simp [hεne]
  have hratio :
      R ^ 4 / (R ^ 2 + D ^ 2) ≤
        (R ^ 2 + R ^ 4) / (1 + D ^ 2) := by
    apply (div_le_div_iff₀ hden₁ hden₂).mpr
    have hnonneg :
        0 ≤ R ^ 2 * (R ^ 4 + D ^ 2) :=
      mul_nonneg (sq_nonneg R)
        (add_nonneg (by positivity) (sq_nonneg D))
    nlinarith
  rw [hscale]
  unfold latticeEdgeWeight
  change ε ^ 2 * (R ^ 4 / (R ^ 2 + D ^ 2)) ≤
    (R ^ 2 + R ^ 4) * ε ^ 2 * (1 + D ^ 2)⁻¹
  calc
    ε ^ 2 * (R ^ 4 / (R ^ 2 + D ^ 2))
        ≤ ε ^ 2 * ((R ^ 2 + R ^ 4) / (1 + D ^ 2)) :=
      mul_le_mul_of_nonneg_left hratio (sq_nonneg ε)
    _ = (R ^ 2 + R ^ 4) * ε ^ 2 * (1 + D ^ 2)⁻¹ := by
      rw [div_eq_mul_inv]
      ring

/-- Lattice specialization of `invSqKer_cellEdge_le`.  It proves the
single-step factor `ε²⟨y-y'⟩⁻²` used when integrating a non-pivot edge in
paper (5.3), with the support-radius dependence explicit. -/
theorem invSqKer_latticeCellEdge_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y y' : Z4) (x : T4),
        dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
          ε * znorm (y - y') →
        x ∈ latticeCellNeighborhood ε R y →
        (∫ z in latticeCellNeighborhood ε R y',
            invSqKer (x - z) ∂paperMeasure) ≤
          C * (R ^ 2 + R ^ 4) * ε ^ 2 *
            latticeEdgeWeight y y' := by
  obtain ⟨C, hC, hedge⟩ := invSqKer_cellEdge_le
  refine ⟨C, hC, fun ε R hε hR y y' x hcenter hx => ?_⟩
  have hr : 0 < R * ε := mul_pos hR hε
  have hmetric := hedge (R * ε) hr
    (latticeTorusCenter ε y) (latticeTorusCenter ε y') x
    (by simpa only [latticeCellNeighborhood] using hx)
  calc
    (∫ z in latticeCellNeighborhood ε R y',
        invSqKer (x - z) ∂paperMeasure)
        ≤ C * metricCellEdgeWeight (R * ε)
            (latticeTorusCenter ε y)
            (latticeTorusCenter ε y') := by
          simpa only [latticeCellNeighborhood] using hmetric
    _ ≤ C * ((R ^ 2 + R ^ 4) * ε ^ 2 *
          latticeEdgeWeight y y') :=
      mul_le_mul_of_nonneg_left
        (metricCellEdgeWeight_lattice_le hε hR y y' hcenter)
        hC.le
    _ = C * (R ^ 2 + R ^ 4) * ε ^ 2 *
          latticeEdgeWeight y y' := by ring

/-! ## Lattice paths and the explicit `ε` ledger -/

/-- Product of the paper's lattice edge weights along a finite path. -/
def latticeCellPathWeight (y : Z4) : List Z4 → ℝ
  | [] => 1
  | y' :: ys =>
      latticeEdgeWeight y y' * latticeCellPathWeight y' ys

theorem latticeCellPathWeight_nonneg (y : Z4) (ys : List Z4) :
    0 ≤ latticeCellPathWeight y ys := by
  induction ys generalizing y with
  | nil => simp [latticeCellPathWeight]
  | cons y' ys ih =>
      apply mul_nonneg
      · unfold latticeEdgeWeight
        positivity
      · exact ih y'

/-- No periodic wrapping along a path of chosen Euclidean cell
representatives.  This is the sole geometric interface needed to identify
torus centre distance with `ε · znorm`; it is not an analytic bound. -/
def LatticeCellPathNoWrap (ε : ℝ) (y : Z4) : List Z4 → Prop
  | [] => True
  | y' :: ys =>
      dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
          ε * znorm (y - y') ∧
        LatticeCellPathNoWrap ε y' ys

theorem metricCellPathWeight_lattice_le
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (y : Z4) (ys : List Z4)
    (hnowrap : LatticeCellPathNoWrap ε y ys) :
    metricCellPathWeight (R * ε) (latticeTorusCenter ε y)
        (ys.map (latticeTorusCenter ε)) ≤
      ((R ^ 2 + R ^ 4) * ε ^ 2) ^ ys.length *
        latticeCellPathWeight y ys := by
  induction ys generalizing y with
  | nil =>
      simp [metricCellPathWeight, latticeCellPathWeight]
  | cons y' ys ih =>
      rcases hnowrap with ⟨hcenter, htail⟩
      have hedge := metricCellEdgeWeight_lattice_le
        hε hR y y' hcenter
      have htail' := ih y' htail
      have hmetricTail :
          0 ≤ metricCellPathWeight (R * ε)
            (latticeTorusCenter ε y')
            (ys.map (latticeTorusCenter ε)) :=
        metricCellPathWeight_nonneg _ _ _
      have hlatticeEdge : 0 ≤ latticeEdgeWeight y y' := by
        unfold latticeEdgeWeight
        positivity
      calc
        metricCellPathWeight (R * ε) (latticeTorusCenter ε y)
            ((y' :: ys).map (latticeTorusCenter ε))
            = metricCellEdgeWeight (R * ε)
                (latticeTorusCenter ε y) (latticeTorusCenter ε y') *
              metricCellPathWeight (R * ε)
                (latticeTorusCenter ε y')
                (ys.map (latticeTorusCenter ε)) := by
                  rfl
        _ ≤ ((R ^ 2 + R ^ 4) * ε ^ 2 *
              latticeEdgeWeight y y') *
            (((R ^ 2 + R ^ 4) * ε ^ 2) ^ ys.length *
              latticeCellPathWeight y' ys) :=
          mul_le_mul hedge htail'
            hmetricTail
            (mul_nonneg
              (mul_nonneg
                (add_nonneg (sq_nonneg R) (by positivity))
                (sq_nonneg ε))
              hlatticeEdge)
        _ = ((R ^ 2 + R ^ 4) * ε ^ 2) ^ (y' :: ys).length *
              latticeCellPathWeight y (y' :: ys) := by
                simp only [List.length_cons, latticeCellPathWeight, pow_succ]
                ring

/-- **Explicit non-cyclic `ε` scaling.**  Integrating `k` consecutive
vertices over their `Rε` cells gives

`(C(R²+R⁴))ᵏ ε^(2k) ∏⟨Δy⟩⁻²`.

For the `2n-2` internal vertices of (5.3), this supplies the complete
`ε^(4n-4)` ledger away from the single pivot edge.  A far pivot contributes
the remaining `ε⁻²`; the all-near pivot is exactly the local triple-
convolution branch of (5.4). -/
theorem integratedLatticeCellChain_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y : Z4) (ys : List Z4) (x : T4),
        LatticeCellPathNoWrap ε y ys →
        x ∈ latticeCellNeighborhood ε R y →
        integratedCellChain (R * ε) x
            (ys.map (latticeTorusCenter ε)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ ys.length *
            ε ^ (2 * ys.length) * latticeCellPathWeight y ys := by
  obtain ⟨C, hC, hchain⟩ := integratedCellChain_le
  refine ⟨C, hC, fun ε R hε hR y ys x hnowrap hx => ?_⟩
  have hr : 0 < R * ε := mul_pos hR hε
  have hchain' := hchain (R * ε) hr
    (latticeTorusCenter ε y) x
    (ys.map (latticeTorusCenter ε))
    (by simpa only [latticeCellNeighborhood] using hx)
  have hpath := metricCellPathWeight_lattice_le
    hε hR y ys hnowrap
  calc
    integratedCellChain (R * ε) x
        (ys.map (latticeTorusCenter ε))
        ≤ C ^ (ys.map (latticeTorusCenter ε)).length *
            metricCellPathWeight (R * ε) (latticeTorusCenter ε y)
              (ys.map (latticeTorusCenter ε)) := hchain'
    _ ≤ C ^ ys.length *
          (((R ^ 2 + R ^ 4) * ε ^ 2) ^ ys.length *
            latticeCellPathWeight y ys) := by
          rw [List.length_map]
          exact mul_le_mul_of_nonneg_left hpath (by positivity)
    _ = (C * (R ^ 2 + R ^ 4)) ^ ys.length *
          ε ^ (2 * ys.length) * latticeCellPathWeight y ys := by
          rw [mul_pow, mul_pow, ← pow_mul]
          ring

/-! ## Fixed terminal lattice path: the `ε^(4n-6)` branch of (5.3) -/

/-- Lattice product including the fixed terminal edge. -/
def latticeTerminalPathWeight (y e : Z4) : List Z4 → ℝ
  | [] => latticeEdgeWeight y e
  | y' :: ys =>
      latticeEdgeWeight y y' * latticeTerminalPathWeight y' e ys

theorem latticeTerminalPathWeight_nonneg (y e : Z4) (ys : List Z4) :
    0 ≤ latticeTerminalPathWeight y e ys := by
  induction ys generalizing y with
  | nil =>
      unfold latticeTerminalPathWeight latticeEdgeWeight
      positivity
  | cons y' ys ih =>
      exact mul_nonneg (by
        unfold latticeEdgeWeight
        positivity) (ih y')

/-- Along every integrated edge the chosen representatives do not wrap;
the final edge additionally has lattice separation at least `4R`. -/
def LatticeTerminalPathFar
    (ε R : ℝ) (y e : Z4) : List Z4 → Prop
  | [] =>
      dist (latticeTorusCenter ε y) (latticeTorusCenter ε e) =
          ε * znorm (y - e) ∧
        4 * R ≤ znorm (y - e)
  | y' :: ys =>
      dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
          ε * znorm (y - y') ∧
        LatticeTerminalPathFar ε R y' e ys

theorem LatticeTerminalPathFar.terminalEdgeFar
    {ε R : ℝ} (hε : 0 < ε) {y e : Z4} {ys : List Z4}
    (h : LatticeTerminalPathFar ε R y e ys) :
    TerminalEdgeFar (R * ε) (latticeTorusCenter ε y)
      (latticeTorusCenter ε e)
      (ys.map (latticeTorusCenter ε)) := by
  induction ys generalizing y with
  | nil =>
      rcases h with ⟨hcenter, hfar⟩
      simp only [List.map_nil, TerminalEdgeFar]
      rw [hcenter]
      have := mul_le_mul_of_nonneg_right hfar hε.le
      nlinarith
  | cons y' ys ih =>
      rcases h with ⟨_hcenter, htail⟩
      simpa only [List.map_cons, TerminalEdgeFar] using ih htail

/-- Radius-dependent harmless constant for the terminal far edge. -/
def terminalRadiusFactor (R : ℝ) : ℝ :=
  4 * (1 + ((4 * R) ^ 2)⁻¹)

theorem terminalRadiusFactor_pos {R : ℝ} (hR : 0 < R) :
    0 < terminalRadiusFactor R := by
  unfold terminalRadiusFactor
  positivity

/-- The pointwise far terminal edge contributes exactly one `ε⁻²`
lattice edge weight. -/
theorem metricTerminalEdgeWeight_lattice_le
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (y e : Z4)
    (hcenter :
      dist (latticeTorusCenter ε y) (latticeTorusCenter ε e) =
        ε * znorm (y - e))
    (hfar : 4 * R ≤ znorm (y - e)) :
    4 * (dist (latticeTorusCenter ε y)
          (latticeTorusCenter ε e) ^ 2)⁻¹ ≤
      terminalRadiusFactor R * (ε ^ 2)⁻¹ *
        latticeEdgeWeight y e := by
  let D : ℝ := znorm (y - e)
  have hD : 0 < D := lt_of_lt_of_le (by positivity) hfar
  have hfourR : 0 < 4 * R := by positivity
  have hsquare : (4 * R) ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ hfourR.le hfar 2
  have hinv : (D ^ 2)⁻¹ ≤ ((4 * R) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hfourR 2) hsquare
  have hid :
      (D ^ 2)⁻¹ =
        (1 + D ^ 2)⁻¹ * (1 + (D ^ 2)⁻¹) := by
    field_simp [ne_of_gt hD]
    ring
  have hbracket :
      (D ^ 2)⁻¹ ≤
        (1 + ((4 * R) ^ 2)⁻¹) * (1 + D ^ 2)⁻¹ := by
    rw [hid]
    calc
      (1 + D ^ 2)⁻¹ * (1 + (D ^ 2)⁻¹)
          ≤ (1 + D ^ 2)⁻¹ *
              (1 + ((4 * R) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (inv_nonneg.mpr (by positivity))
      _ = (1 + ((4 * R) ^ 2)⁻¹) *
            (1 + D ^ 2)⁻¹ := by ring
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hscale :
      (dist (latticeTorusCenter ε y)
        (latticeTorusCenter ε e) ^ 2)⁻¹ =
        (ε ^ 2)⁻¹ * (D ^ 2)⁻¹ := by
    rw [hcenter]
    change ((ε * D) ^ 2)⁻¹ = (ε ^ 2)⁻¹ * (D ^ 2)⁻¹
    field_simp [hεne, ne_of_gt hD]
  rw [hscale]
  unfold terminalRadiusFactor latticeEdgeWeight
  change 4 * ((ε ^ 2)⁻¹ * (D ^ 2)⁻¹) ≤
    4 * (1 + ((4 * R) ^ 2)⁻¹) * (ε ^ 2)⁻¹ *
      (1 + D ^ 2)⁻¹
  calc
    4 * ((ε ^ 2)⁻¹ * (D ^ 2)⁻¹)
        ≤ 4 * ((ε ^ 2)⁻¹ *
          ((1 + ((4 * R) ^ 2)⁻¹) * (1 + D ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbracket
          (inv_nonneg.mpr (sq_nonneg ε))) (by norm_num)
    _ = 4 * (1 + ((4 * R) ^ 2)⁻¹) * (ε ^ 2)⁻¹ *
          (1 + D ^ 2)⁻¹ := by ring

/-- Metric-to-lattice comparison for the entire far-terminal path. -/
theorem metricTerminalPathWeight_lattice_le
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (y e : Z4) (ys : List Z4)
    (hpath : LatticeTerminalPathFar ε R y e ys) :
    metricTerminalPathWeight (R * ε)
        (latticeTorusCenter ε y) (latticeTorusCenter ε e)
        (ys.map (latticeTorusCenter ε)) ≤
      ((R ^ 2 + R ^ 4) * ε ^ 2) ^ ys.length *
        (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
        latticeTerminalPathWeight y e ys := by
  induction ys generalizing y with
  | nil =>
      rcases hpath with ⟨hcenter, hfar⟩
      simpa only [List.map_nil, List.length_nil, pow_zero, one_mul,
        metricTerminalPathWeight, latticeTerminalPathWeight] using
        metricTerminalEdgeWeight_lattice_le
          hε hR y e hcenter hfar
  | cons y' ys ih =>
      rcases hpath with ⟨hcenter, htail⟩
      have hedge := metricCellEdgeWeight_lattice_le
        hε hR y y' hcenter
      have htail' := ih y' htail
      have hmetricTail :
          0 ≤ metricTerminalPathWeight (R * ε)
            (latticeTorusCenter ε y') (latticeTorusCenter ε e)
            (ys.map (latticeTorusCenter ε)) :=
        metricTerminalPathWeight_nonneg _ _ _ _
      have hedgeNonneg : 0 ≤
          (R ^ 2 + R ^ 4) * ε ^ 2 *
            latticeEdgeWeight y y' := by
        apply mul_nonneg
        · exact mul_nonneg
            (add_nonneg (sq_nonneg R) (by positivity))
            (sq_nonneg ε)
        · unfold latticeEdgeWeight
          positivity
      calc
        metricTerminalPathWeight (R * ε)
            (latticeTorusCenter ε y) (latticeTorusCenter ε e)
            ((y' :: ys).map (latticeTorusCenter ε))
            = metricCellEdgeWeight (R * ε)
                (latticeTorusCenter ε y) (latticeTorusCenter ε y') *
              metricTerminalPathWeight (R * ε)
                (latticeTorusCenter ε y') (latticeTorusCenter ε e)
                (ys.map (latticeTorusCenter ε)) := rfl
        _ ≤ ((R ^ 2 + R ^ 4) * ε ^ 2 *
              latticeEdgeWeight y y') *
            (((R ^ 2 + R ^ 4) * ε ^ 2) ^ ys.length *
              (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
              latticeTerminalPathWeight y' e ys) :=
          mul_le_mul hedge htail' hmetricTail hedgeNonneg
        _ = ((R ^ 2 + R ^ 4) * ε ^ 2) ^
              (y' :: ys).length *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
            latticeTerminalPathWeight y e (y' :: ys) := by
              simp only [List.length_cons, latticeTerminalPathWeight,
                pow_succ]
              ring

/-- Far-terminal lattice chain with all powers exposed. -/
theorem terminalLatticeCellChain_le_of_far :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (ys : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTerminalPathFar ε R y e ys →
        terminalCellChain (R * ε) x z
            (ys.map (latticeTorusCenter ε)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ ys.length *
            ε ^ (2 * ys.length) *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
            latticeTerminalPathWeight y e ys := by
  obtain ⟨C, hC, hchain⟩ := terminalCellChain_le_of_far
  refine ⟨C, hC, fun ε R hε hR y e ys x z hx hz hpath => ?_⟩
  have hr : 0 < R * ε := mul_pos hR hε
  have hfar := hpath.terminalEdgeFar hε
  have hchain' := hchain (R * ε) hr
    (latticeTorusCenter ε y) (latticeTorusCenter ε e)
    x z (ys.map (latticeTorusCenter ε))
    (by simpa only [latticeCellNeighborhood] using hx)
    (by simpa only [latticeCellNeighborhood] using hz)
    hfar
  have hmetric := metricTerminalPathWeight_lattice_le
    hε hR y e ys hpath
  calc
    terminalCellChain (R * ε) x z
        (ys.map (latticeTorusCenter ε))
        ≤ C ^ (ys.map (latticeTorusCenter ε)).length *
            metricTerminalPathWeight (R * ε)
              (latticeTorusCenter ε y) (latticeTorusCenter ε e)
              (ys.map (latticeTorusCenter ε)) := hchain'
    _ ≤ C ^ ys.length *
          (((R ^ 2 + R ^ 4) * ε ^ 2) ^ ys.length *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
            latticeTerminalPathWeight y e ys) := by
          rw [List.length_map]
          exact mul_le_mul_of_nonneg_left hmetric (by positivity)
    _ = (C * (R ^ 2 + R ^ 4)) ^ ys.length *
          ε ^ (2 * ys.length) *
          (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
          latticeTerminalPathWeight y e ys := by
          rw [mul_pow, mul_pow, ← pow_mul]
          ring

theorem pow_two_mul_mul_inv_sq
    {ε : ℝ} (hε : ε ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    ε ^ (2 * k) * (ε ^ 2)⁻¹ = ε ^ (2 * k - 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 2 * (1 + t) = 2 * t + 2 by omega]
  rw [pow_add, show 2 * t + 2 - 2 = 2 * t by omega]
  field_simp [hε]

/-- Paper-order specialization of the far-terminal branch.  With exactly
`2n-2` internal vertices, the scale in the previous theorem simplifies
to the advertised `ε^(4n-6)` in (5.3). -/
theorem terminalLatticeCellChain_order_le_of_far :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (_hn : 2 ≤ n) (ε R : ℝ)
        (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (ys : List Z4) (x z : T4),
        ys.length = 2 * n - 2 →
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTerminalPathFar ε R y e ys →
        terminalCellChain (R * ε) x z
            (ys.map (latticeTorusCenter ε)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
            terminalRadiusFactor R * ε ^ (4 * n - 6) *
            latticeTerminalPathWeight y e ys := by
  obtain ⟨C, hC, hchain⟩ := terminalLatticeCellChain_le_of_far
  refine ⟨C, hC,
    fun n hn ε R hε hR y e ys x z hlen hx hz hpath => ?_⟩
  have hbase := hchain ε R hε hR y e ys x z hx hz hpath
  have hk : 1 ≤ 2 * n - 2 := by omega
  have hp := pow_two_mul_mul_inv_sq (ne_of_gt hε) (2 * n - 2) hk
  rw [show 2 * (2 * n - 2) - 2 = 4 * n - 6 by omega] at hp
  calc
    terminalCellChain (R * ε) x z
        (ys.map (latticeTorusCenter ε))
        ≤ (C * (R ^ 2 + R ^ 4)) ^ ys.length *
            ε ^ (2 * ys.length) *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
            latticeTerminalPathWeight y e ys := hbase
    _ = (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R *
          (ε ^ (2 * (2 * n - 2)) * (ε ^ 2)⁻¹) *
          latticeTerminalPathWeight y e ys := by
          rw [hlen]
          ring
    _ = (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * ε ^ (4 * n - 6) *
          latticeTerminalPathWeight y e ys := by
          rw [hp]

end

end Anderson4D
