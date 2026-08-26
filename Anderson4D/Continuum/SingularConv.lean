import Anderson4D.Continuum.GreenFunction

/-!
# Singular-kernel toolkit on the torus (paper §5.1, blueprint node I-singconv)

Paper: I-singconv — (5.3)–(5.4) — the chain-convolution toolkit

The abstract integrability/convolution machinery behind the paper's
(5.3)–(5.4) chain reductions, stated for the model kernel `|z|⁻²` on `𝕋⁴`
(`invSqKer`). Contents:

* `torusDistSq z = ∑ i (z̃ i)²`, the squared Euclidean length of the
  canonical lift `z̃ = torusLift z ∈ [-π,π)⁴`, and the bridge
  `torusDistSq_eq_sum_norm_sq` identifying it with `∑ i ‖z i‖²` for the
  quotient norm on `AddCircle (2π)` — the canonical representative of a
  point of `ℝ/2πℤ` has absolute value `≤ π`, hence realizes the norm;
* `invSqKer z = (torusDistSq z)⁻¹`, junk-totalized per DESIGN §5.7:
  at `z = 0` the value is `0⁻¹ = 0` (mathlib's junk value), and all
  estimates below are one-sided bounds unaffected by this branch;
* the measure dictionary `paperMeasure_eq_volume : paperMeasure = volume`
  (the pi `MeasureSpace` structure on `𝕋⁴` built from mathlib's
  `AddCircle` volume, which is Haar of total mass `2π` per coordinate);
* the crux integrability `integrable_invSqKer` (`|z|⁻²` is integrable in
  dimension `4 > 2`), proved by transporting to the cube `(-π,π]⁴` along
  `AddCircle.measurePreserving_mk` (componentwise, via
  `measurePreserving_pi`) and applying
  `MeasureTheory.integrableOn_ball_of_norm_le_rpow` on `ℝ⁴`;
* translation invariance `integrable_invSqKer_sub`.

Stage 2 (ball, annulus, triple-convolution bounds) builds on the same
cube transport.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-! ## The model kernel -/

/-- Squared Euclidean distance of `z ∈ 𝕋⁴` to `0`, computed on the canonical
componentwise lift to `[-π, π)⁴`. -/
def torusDistSq (z : T4) : ℝ := ∑ i, torusLift z i ^ 2

/-- The model singular kernel `|z|⁻²` on the torus. Junk-totalized: the
value at `z = 0` is `0⁻¹ = 0`. -/
def invSqKer (z : T4) : ℝ := (torusDistSq z)⁻¹

/-! ## The lift and the `AddCircle` norm -/

/-- The canonical lift lies in `[-π, π)` in each coordinate. -/
lemma torusLift_mem_Ico (z : T4) (i : Fin dim) :
    torusLift z i ∈ Ico (-Real.pi) Real.pi := by
  have h : torusLift z i ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) :=
    ((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) (z i)).2
  exact ⟨h.1, by have := h.2; linarith⟩

/-- The canonical representative realizes the quotient norm on
`ℝ/2πℤ`: `‖z i‖ = |torusLift z i|` (its absolute value is `≤ π`, half the
period). -/
lemma norm_eq_abs_torusLift (z : T4) (i : Fin dim) :
    ‖z i‖ = |torusLift z i| := by
  obtain ⟨h₁, h₂⟩ := torusLift_mem_Ico z i
  have habs : |torusLift z i| ≤ |2 * Real.pi| / 2 := by
    rw [abs_of_pos Real.two_pi_pos, abs_le]
    constructor <;> linarith
  have hcoe : ((torusLift z i : ℝ) : AddCircle (2 * Real.pi)) = z i :=
    AddCircle.coe_equivIco
  rw [← hcoe]
  exact (AddCircle.norm_coe_eq_abs_iff (p := 2 * Real.pi) (by positivity)).mpr habs

/-- `torusDistSq` as a sum of squared `AddCircle` norms; the geometric
workhorse (symmetry, triangle-type estimates come from norm axioms). -/
lemma torusDistSq_eq_sum_norm_sq (z : T4) : torusDistSq z = ∑ i, ‖z i‖ ^ 2 := by
  unfold torusDistSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_eq_abs_torusLift, sq_abs]

lemma torusDistSq_nonneg (z : T4) : 0 ≤ torusDistSq z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The torus has finite extent: `torusDistSq ≤ 4π²`. -/
lemma torusDistSq_le (z : T4) : torusDistSq z ≤ 4 * Real.pi ^ 2 := by
  have h : ∀ i ∈ Finset.univ, torusLift z i ^ 2 ≤ Real.pi ^ 2 := by
    intro i _
    obtain ⟨h₁, h₂⟩ := torusLift_mem_Ico z i
    rw [← sq_abs]
    have : |torusLift z i| ≤ Real.pi := abs_le.mpr ⟨h₁, h₂.le⟩
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc torusDistSq z ≤ ∑ _i : Fin dim, Real.pi ^ 2 := Finset.sum_le_sum h
    _ = 4 * Real.pi ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

theorem torusDistSq_eq_zero_iff (z : T4) : torusDistSq z = 0 ↔ z = 0 := by
  rw [torusDistSq_eq_sum_norm_sq]
  constructor
  · intro h
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖z j‖).mp h i
      (Finset.mem_univ i)
    have : ‖z i‖ = 0 := by
      have := sq_eq_zero_iff.mp hi
      simpa using this
    simpa using norm_eq_zero.mp this
  · rintro rfl; simp

/-- Symmetry of the kernel geometry (via norms — note the *lift* itself is
not odd on the boundary, but its absolute value is even). -/
lemma torusDistSq_neg (z : T4) : torusDistSq (-z) = torusDistSq z := by
  rw [torusDistSq_eq_sum_norm_sq, torusDistSq_eq_sum_norm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (-z) i = -(z i) := rfl
  rw [this, norm_neg]

lemma invSqKer_nonneg (z : T4) : 0 ≤ invSqKer z :=
  inv_nonneg.mpr (torusDistSq_nonneg z)

lemma invSqKer_neg (z : T4) : invSqKer (-z) = invSqKer z := by
  unfold invSqKer; rw [torusDistSq_neg]

/-- The kernel is symmetric in the difference variable. -/
lemma invSqKer_sub_comm (x y : T4) : invSqKer (x - y) = invSqKer (y - x) := by
  rw [← invSqKer_neg (x - y), neg_sub]

/-! ## Measurability -/

lemma measurable_torusLift : Measurable torusLift := by
  apply measurable_pi_lambda
  intro i
  have h : Measurable fun u : AddCircle (2 * Real.pi) =>
      ((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) u : ℝ) :=
    measurable_subtype_coe.comp
      (AddCircle.measurableEquivIco (2 * Real.pi) (-Real.pi)).measurable
  exact h.comp (measurable_pi_apply i)

lemma measurable_torusDistSq : Measurable torusDistSq :=
  Finset.measurable_sum Finset.univ fun i _ =>
    ((measurable_pi_apply i).comp measurable_torusLift).pow_const 2

lemma measurable_invSqKer : Measurable invSqKer :=
  measurable_torusDistSq.inv

/-! ## The measure dictionary: `paperMeasure` is the pi volume -/

/-- Product measures scale multiplicatively: a finite scalar on each of the
four factors comes out as its fourth power. -/
private lemma pi_smul_measure (c : ℝ≥0∞) (hc : c ≠ ∞)
    (μ : Measure (AddCircle (2 * Real.pi))) [IsFiniteMeasure μ] :
    (Measure.pi fun _ : Fin dim => c • μ) =
      c ^ (dim : ℕ) • Measure.pi fun _ : Fin dim => μ := by
  haveI : IsFiniteMeasure (c • μ) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top μ _)⟩
  refine Measure.pi_eq (μ := fun _ : Fin dim => c • μ) fun s hs => ?_
  simp only [Measure.smul_apply, smul_eq_mul, Measure.pi_pi,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The normalization-ledger identity: the paper's reference measure on
`𝕋⁴` is mathlib's pi volume (per coordinate, `AddCircle` volume is Haar
of total mass `2π`). -/
theorem paperMeasure_eq_volume : paperMeasure = (volume : Measure T4) := by
  have h1 : (volume : Measure T4) =
      Measure.pi fun _ : Fin dim => (volume : Measure (AddCircle (2 * Real.pi))) := rfl
  rw [h1]
  simp only [AddCircle.volume_eq_smul_haarAddCircle]
  rw [pi_smul_measure _ ENNReal.ofReal_ne_top]
  unfold paperMeasure haarT4
  congr 1
  rw [ENNReal.ofReal_pow (by positivity)]

/-! ## Transport to the cube `(-π, π]⁴` -/

/-- The componentwise quotient map `ℝ⁴ → 𝕋⁴`. -/
private def mkT4 (x : R4) : T4 := fun i => (x i : AddCircle (2 * Real.pi))

/-- The half-open fundamental cube for the componentwise quotient. -/
private def boxIoc : Set R4 := Set.univ.pi fun _ : Fin dim => Ioc (-Real.pi) Real.pi

private lemma measurableSet_boxIoc : MeasurableSet boxIoc :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- The quotient map from the fundamental cube (with Lebesgue measure) to
the torus (with `paperMeasure`) is measure preserving. -/
private lemma measurePreserving_mkT4 :
    MeasurePreserving mkT4 (volume.restrict boxIoc) paperMeasure := by
  rw [paperMeasure_eq_volume]
  have h := measurePreserving_pi
    (fun _ : Fin dim => volume.restrict (Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)))
    (fun _ : Fin dim => (volume : Measure (AddCircle (2 * Real.pi))))
    (fun _ => AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi))
  have hIoc : Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) = Ioc (-Real.pi) Real.pi := by
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]
  rw [hIoc] at h
  have hsrc : (Measure.pi fun _ : Fin dim => volume.restrict (Ioc (-Real.pi) Real.pi)) =
      volume.restrict boxIoc := by
    rw [← Measure.restrict_pi_pi]; rfl
  rwa [hsrc] at h

/-! ## Integrability of the model kernel (the crux: `2 < 4 = dim`) -/

/-- The cube-side kernel `(∑ xᵢ²)⁻¹` on `ℝ⁴`. -/
private def cubeKer (x : R4) : ℝ := (∑ i, x i ^ 2)⁻¹

private lemma measurable_cubeKer : Measurable cubeKer :=
  (Finset.measurable_sum Finset.univ fun i _ =>
    (measurable_pi_apply i).pow_const 2).inv

/-- Sup-norm comparison on the pi space `ℝ⁴`: `‖x‖² ≤ ∑ xᵢ²`. -/
private lemma sq_norm_le_sum (x : R4) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    calc |x i| = Real.sqrt (x i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, x j ^ 2) :=
        Real.sqrt_le_sqrt
          (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, x i ^ 2 := Real.sq_sqrt hs

/-- Pointwise domination `|cubeKer| ≤ ‖x‖⁻²` feeding the mathlib radial
integrability criterion (both sides junk-vanish at `x = 0`). -/
private lemma cubeKer_le_rpow (x : R4) : ‖cubeKer x‖ ≤ 1 * ‖x‖ ^ (-(2 : ℝ)) := by
  rw [one_mul]
  by_cases hx : x = 0
  · subst hx
    have h0 : cubeKer (0 : R4) = 0 := by unfold cubeKer; simp
    rw [h0, norm_zero, norm_zero, Real.zero_rpow (by norm_num)]
  · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h2 : ‖x‖ ^ (-(2 : ℝ)) = (‖x‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg (norm_nonneg _),
        show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hknn : 0 ≤ cubeKer x :=
      inv_nonneg.mpr (Finset.sum_nonneg fun i _ => sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hknn, h2]
    exact inv_anti₀ (by positivity) (sq_norm_le_sum x)

private lemma integrableOn_cubeKer_ball :
    IntegrableOn cubeKer (Metric.ball (0 : R4) 5) volume := by
  have hd : 1 ≤ Module.finrank ℝ R4 := by rw [Module.finrank_pi]; simp
  have hα : (2 : ℝ) < Module.finrank ℝ R4 := by
    rw [Module.finrank_pi]; simp; norm_num
  exact integrableOn_ball_of_norm_le_rpow hd hα
    (ae_of_all _ cubeKer_le_rpow) measurable_cubeKer.aestronglyMeasurable

private lemma boxIoc_subset_ball : boxIoc ⊆ Metric.ball (0 : R4) 5 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  have hb : ‖x‖ ≤ Real.pi := by
    refine (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i => ?_
    have h := hx i (mem_univ i)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨h.1.le, h.2⟩
  have := Real.pi_le_four
  linarith

private lemma integrableOn_cubeKer_box : IntegrableOn cubeKer boxIoc volume :=
  integrableOn_cubeKer_ball.mono_set boxIoc_subset_ball

/-- On the (a.e. of the) fundamental cube the canonical lift undoes the
quotient map. -/
private lemma torusLift_mkT4 {x : R4} (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    torusLift (mkT4 x) = x := by
  funext i
  have hmem : x i ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) :=
    ⟨(hx i).1, by have := (hx i).2; linarith⟩
  show ((AddCircle.equivIco (2 * Real.pi) (-Real.pi))
    ((x i : ℝ) : AddCircle (2 * Real.pi)) : ℝ) = x i
  rw [AddCircle.equivIco_coe_eq hmem]

/-- Almost every point of the fundamental cube is a *good* point: all
coordinates in `[-π, π)` (the exceptional set — some coordinate equal to
`π`, whose lift is `-π` — is a finite union of null hyperplanes). -/
private lemma ae_box :
    ∀ᵐ x ∂volume.restrict boxIoc, ∀ i, x i ∈ Ico (-Real.pi) Real.pi := by
  have hbad : volume (⋃ i : Fin dim, {x : R4 | x i = Real.pi}) = 0 :=
    measure_iUnion_null fun i => Measure.pi_hyperplane _ i _
  have h1 : ∀ᵐ x ∂volume.restrict boxIoc, x ∈ boxIoc :=
    ae_restrict_mem measurableSet_boxIoc
  have h2 : ∀ᵐ x ∂volume.restrict boxIoc,
      x ∈ (⋃ i : Fin dim, {x : R4 | x i = Real.pi})ᶜ :=
    ae_restrict_of_ae (compl_mem_ae_iff.mpr hbad)
  filter_upwards [h1, h2] with x hxbox hxbad
  intro i
  have h3 := hxbox i (mem_univ i)
  have h4 : x i ≠ Real.pi := fun he => hxbad (mem_iUnion.mpr ⟨i, he⟩)
  exact ⟨h3.1.le, lt_of_le_of_ne h3.2 h4⟩

/-- At good points the quotient of the squared distance is the cube one. -/
private lemma torusDistSq_mkT4 {x : R4}
    (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    torusDistSq (mkT4 x) = ∑ i, x i ^ 2 := by
  unfold torusDistSq
  rw [torusLift_mkT4 hx]

private lemma invSqKer_mkT4 {x : R4} (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    invSqKer (mkT4 x) = cubeKer x := by
  unfold invSqKer cubeKer
  rw [torusDistSq_mkT4 hx]

/-- At good points the quotient map preserves the sup norm. -/
private lemma norm_mkT4 {x : R4} (hx : ∀ i, x i ∈ Ico (-Real.pi) Real.pi) :
    ‖mkT4 x‖ = ‖x‖ := by
  have hcomp : ∀ i, ‖mkT4 x i‖ = ‖x i‖ := by
    intro i
    rw [norm_eq_abs_torusLift (mkT4 x) i, torusLift_mkT4 hx, Real.norm_eq_abs]
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => ?_
    rw [hcomp i]; exact norm_le_pi_norm x i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg (mkT4 x))).mpr fun i => ?_
    rw [← hcomp i]; exact norm_le_pi_norm (mkT4 x) i

/-- The transported kernel agrees a.e. on the cube with the cube kernel. -/
private lemma cubeKer_ae_eq :
    (fun x => invSqKer (mkT4 x)) =ᵐ[volume.restrict boxIoc] cubeKer := by
  filter_upwards [ae_box] with x hx
  exact invSqKer_mkT4 hx

/-- **Integrability of the model kernel** `|z|⁻²` on `𝕋⁴` (blueprint
I-singconv; the dimension count is `2 < 4`). -/
theorem integrable_invSqKer : Integrable invSqKer paperMeasure := by
  have h := measurePreserving_mkT4.integrable_comp
    measurable_invSqKer.aestronglyMeasurable
  rw [← h]
  exact integrableOn_cubeKer_box.congr cubeKer_ae_eq.symm

/-! ## Translation invariance -/

/-- Translation invariance of the reference measure, packaged for the
kernel-shift arguments of §5.1. -/
theorem measurePreserving_sub_paper (w : T4) :
    MeasurePreserving (fun z : T4 => z - w) paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  exact measurePreserving_sub_right volume w

/-- Shifted kernels `z ↦ |z - w|⁻²` are integrable (uniformly in the
shift, by translation invariance of Haar measure). -/
theorem integrable_invSqKer_sub (w : T4) :
    Integrable (fun z => invSqKer (z - w)) paperMeasure :=
  ((measurePreserving_sub_paper w).integrable_comp
    measurable_invSqKer.aestronglyMeasurable).mpr integrable_invSqKer

/-! ## Stage 2: comparison of `torusDistSq` with the sup norm on `𝕋⁴`

`T4` carries the pi (sup) norm built from the `AddCircle` quotient norm;
`torusDistSq` is squeezed between `‖z‖²` and `4‖z‖²`, and the sup norm
has an honest triangle inequality — all region arguments below use it. -/

lemma sq_norm_le_torusDistSq (z : T4) : ‖z‖ ^ 2 ≤ torusDistSq z := by
  rw [torusDistSq_eq_sum_norm_sq]
  have hs : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖z‖ ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    calc ‖z i‖ = Real.sqrt (‖z i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) :=
        Real.sqrt_le_sqrt
          (Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ i, ‖z i‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖z i‖ ^ 2 := Real.sq_sqrt hs

lemma torusDistSq_le_four_mul_sq_norm (z : T4) : torusDistSq z ≤ 4 * ‖z‖ ^ 2 := by
  rw [torusDistSq_eq_sum_norm_sq]
  calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin dim, ‖z‖ ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2
    _ = 4 * ‖z‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-! ## Stage 2: radial computations on the cube -/

/-- Volume of the unit sup-norm ball of `ℝ⁴` (`= 16`; only positivity and
finiteness are used). -/
private def vB : ℝ := volume.real (Metric.ball (0 : R4) 1)

private lemma vB_pos : 0 < vB :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne'
    measure_ball_lt_top.ne

private lemma finrank_R4 : Module.finrank ℝ R4 = 4 := by
  rw [Module.finrank_pi]; simp

/-- Polar decomposition of radial integrals on `ℝ⁴`
(`MeasureTheory.integral_fun_norm_addHaar` specialized). -/
private lemma radial4 (g : ℝ → ℝ) :
    ∫ x : R4, g ‖x‖ ∂volume = 4 * vB * ∫ y in Ioi (0 : ℝ), y ^ (3 : ℕ) * g y := by
  have h := integral_fun_norm_addHaar (volume : Measure R4) g
  rw [finrank_R4] at h
  simpa [vB, smul_eq_mul, mul_assoc] using h

/-- Exact value of the model ball integral on the cube side:
`∫_{‖x‖<r} ‖x‖⁻² = 2·vB·r²` in `ℝ⁴`. -/
private lemma cube_ball_value (r : ℝ) (hr : 0 < r) :
    ∫ x in Metric.ball (0 : R4) r, ‖x‖ ^ (-(2 : ℝ)) ∂volume = 2 * vB * r ^ 2 := by
  have hind : ∀ x : R4, (Iio r).indicator (fun y : ℝ => y ^ (-(2 : ℝ))) ‖x‖ =
      (Metric.ball (0 : R4) r).indicator (fun x : R4 => ‖x‖ ^ (-(2 : ℝ))) x := by
    intro x
    by_cases h : ‖x‖ < r
    · rw [Set.indicator_of_mem (show ‖x‖ ∈ Iio r from h),
        Set.indicator_of_mem (show x ∈ Metric.ball (0 : R4) r by
          simpa [Metric.mem_ball, dist_zero_right] using h)]
    · rw [Set.indicator_of_notMem (show ‖x‖ ∉ Iio r from h),
        Set.indicator_of_notMem (show x ∉ Metric.ball (0 : R4) r by
          simpa [Metric.mem_ball, dist_zero_right] using h)]
  have h1 := radial4 ((Iio r).indicator fun y : ℝ => y ^ (-(2 : ℝ)))
  have h2 : ∫ x : R4, (Iio r).indicator (fun y : ℝ => y ^ (-(2 : ℝ))) ‖x‖ ∂volume
      = ∫ x in Metric.ball (0 : R4) r, ‖x‖ ^ (-(2 : ℝ)) ∂volume := by
    rw [← integral_indicator measurableSet_ball]
    exact integral_congr_ae (.of_forall hind)
  have h3 : ∫ y in Ioi (0 : ℝ), y ^ (3 : ℕ) * (Iio r).indicator (fun y : ℝ => y ^ (-(2 : ℝ))) y
      = ∫ y in Ioo (0 : ℝ) r, y := by
    have e1 : ∀ y : ℝ, y ^ (3 : ℕ) * (Iio r).indicator (fun y : ℝ => y ^ (-(2 : ℝ))) y
        = (Iio r).indicator (fun y : ℝ => y ^ (3 : ℕ) * y ^ (-(2 : ℝ))) y := by
      intro y; simp only [Set.indicator_apply]; split <;> simp
    simp only [e1]
    rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
    refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    rw [← Real.rpow_natCast y 3, ← Real.rpow_add hy.1]
    norm_num
  rw [h2] at h1
  rw [h1, h3, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
    integral_id]
  ring

/-- Exact value of the model annulus integral on the cube side:
`∫_{a ≤ ‖x‖ < b} ‖x‖⁻⁴ = 4·vB·(log b − log a)` in `ℝ⁴`. -/
private lemma cube_annulus_value {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in {x : R4 | ‖x‖ ∈ Ico a b}, ‖x‖ ^ (-(4 : ℝ)) ∂volume
      = 4 * vB * (Real.log b - Real.log a) := by
  have hmeas : MeasurableSet {x : R4 | ‖x‖ ∈ Ico a b} :=
    measurable_norm measurableSet_Ico
  have hind : ∀ x : R4, (Ico a b).indicator (fun y : ℝ => y ^ (-(4 : ℝ))) ‖x‖ =
      {x : R4 | ‖x‖ ∈ Ico a b}.indicator (fun x : R4 => ‖x‖ ^ (-(4 : ℝ))) x := by
    intro x
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have h1 := radial4 ((Ico a b).indicator fun y : ℝ => y ^ (-(4 : ℝ)))
  have h2 : ∫ x : R4, (Ico a b).indicator (fun y : ℝ => y ^ (-(4 : ℝ))) ‖x‖ ∂volume
      = ∫ x in {x : R4 | ‖x‖ ∈ Ico a b}, ‖x‖ ^ (-(4 : ℝ)) ∂volume := by
    rw [← integral_indicator hmeas]
    exact integral_congr_ae (.of_forall hind)
  have h3 : ∫ y in Ioi (0 : ℝ), y ^ (3 : ℕ) * (Ico a b).indicator (fun y : ℝ => y ^ (-(4 : ℝ))) y
      = ∫ y in Ico a b, 1 / y := by
    have e1 : ∀ y : ℝ, y ^ (3 : ℕ) * (Ico a b).indicator (fun y : ℝ => y ^ (-(4 : ℝ))) y
        = (Ico a b).indicator (fun y : ℝ => y ^ (3 : ℕ) * y ^ (-(4 : ℝ))) y := by
      intro y; simp only [Set.indicator_apply]; split <;> simp
    simp only [e1]
    have hsub : Ioi (0 : ℝ) ∩ Ico a b = Ico a b :=
      Set.inter_eq_self_of_subset_right fun y (hy : y ∈ Ico a b) =>
        lt_of_lt_of_le ha hy.1
    rw [setIntegral_indicator measurableSet_Ico, hsub]
    refine setIntegral_congr_fun measurableSet_Ico fun y hy => ?_
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le ha hy.1
    rw [← Real.rpow_natCast y 3, ← Real.rpow_add hy0, one_div, ← Real.rpow_neg_one y]
    norm_num
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact fun h => absurd h.1 (not_le.mpr ha)
  rw [h2] at h1
  rw [h1, h3, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_one_div h0, Real.log_div (lt_of_lt_of_le ha hab).ne' ha.ne']

/-! ## Stage 2: transporting integral bounds to the torus -/

instance : IsFiniteMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]; infer_instance

private lemma measurable_mkT4 : Measurable mkT4 :=
  measurable_pi_lambda _ fun i =>
    AddCircle.measurable_mk'.comp (measurable_pi_apply i)

/-- Integrals over `(𝕋⁴, paperMeasure)` compute over the fundamental cube. -/
private lemma torus_integral_eq_cube {g : T4 → ℝ}
    (hg : AEStronglyMeasurable g paperMeasure) :
    ∫ z, g z ∂paperMeasure = ∫ x in boxIoc, g (mkT4 x) ∂volume := by
  rw [← measurePreserving_mkT4.map_eq] at hg
  rw [← measurePreserving_mkT4.map_eq, integral_map measurable_mkT4.aemeasurable hg]

/-- Points of the fundamental cube have sup norm at most `π`. -/
private lemma box_norm_le {x : R4} (hx : x ∈ boxIoc) : ‖x‖ ≤ Real.pi := by
  refine (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun i => ?_
  have h := hx i (mem_univ i)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨h.1.le, h.2⟩

private lemma cubeKer_le (x : R4) : cubeKer x ≤ ‖x‖ ^ (-(2 : ℝ)) :=
  (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using cubeKer_le_rpow x)

/-- Negative powers are antitone in the base. -/
private lemma rpow_neg_anti {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) {p : ℝ}
    (hp : 0 ≤ p) : d ^ (-p) ≤ c ^ (-p) := by
  rw [Real.rpow_neg (hc.trans_le hcd).le, Real.rpow_neg hc.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hc p) (Real.rpow_le_rpow hc.le hcd hp)

/-- Negative powers of the norm below the critical exponent `4` are
integrable on balls of `ℝ⁴`. -/
private lemma integrableOn_rpow_ball {p : ℝ} (hp4 : p < 4) (R : ℝ) :
    IntegrableOn (fun x : R4 => ‖x‖ ^ (-p)) (Metric.ball (0 : R4) R) volume := by
  have hd : 1 ≤ Module.finrank ℝ R4 := by rw [finrank_R4]; norm_num
  have hα : p < (Module.finrank ℝ R4 : ℝ) := by
    rw [finrank_R4]; exact_mod_cast hp4
  refine integrableOn_ball_of_norm_le_rpow (C := 1) hd hα
    (.of_forall fun x => ?_) (Measurable.aestronglyMeasurable (by fun_prop))
  rw [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

/-! ## Stage 2 (a): the ball bound -/

/-- Primary (sup-norm ball) form of the ball bound. -/
private lemma indicator_ball_invSqKer_le (s : ℝ) (hs : 0 < s) :
    ∫ z, ({z : T4 | ‖z‖ ≤ s}.indicator invSqKer) z ∂paperMeasure
      ≤ 8 * vB * s ^ 2 := by
  have hmeasS : MeasurableSet {z : T4 | ‖z‖ ≤ s} :=
    measurable_norm measurableSet_Iic
  rw [torus_integral_eq_cube
    (measurable_invSqKer.indicator hmeasS).aestronglyMeasurable]
  set m : R4 → ℝ :=
    (Metric.ball (0 : R4) (2 * s)).indicator fun x => ‖x‖ ^ (-(2 : ℝ)) with hm
  have hmnn : ∀ x, 0 ≤ m x := fun x =>
    Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hmi : Integrable m volume := by
    rw [hm, integrable_indicator_iff measurableSet_ball]
    exact integrableOn_rpow_ball (by norm_num) _
  have hb : ∫ x in boxIoc, ({z : T4 | ‖z‖ ≤ s}.indicator invSqKer) (mkT4 x) ∂volume
      ≤ ∫ x in boxIoc, m x ∂volume := by
    refine integral_mono_of_nonneg
      (.of_forall fun x => Set.indicator_nonneg (fun z _ => invSqKer_nonneg z) _)
      hmi.restrict ?_
    filter_upwards [ae_box] with x hx
    by_cases hmem : mkT4 x ∈ {z : T4 | ‖z‖ ≤ s}
    · rw [Set.indicator_of_mem hmem]
      have h2 : x ∈ Metric.ball (0 : R4) (2 * s) := by
        rw [Metric.mem_ball, dist_zero_right, ← norm_mkT4 hx]
        exact lt_of_le_of_lt hmem (by linarith)
      rw [hm, Set.indicator_of_mem h2, invSqKer_mkT4 hx]
      exact cubeKer_le x
    · rw [Set.indicator_of_notMem hmem]
      exact hmnn x
  refine hb.trans ?_
  calc ∫ x in boxIoc, m x ∂volume
      ≤ ∫ x, m x ∂volume := setIntegral_le_integral hmi (.of_forall hmnn)
    _ = 2 * vB * (2 * s) ^ 2 := by
        rw [hm, integral_indicator measurableSet_ball]
        exact cube_ball_value _ (by positivity)
    _ = 8 * vB * s ^ 2 := by ring

/-- **Ball bound** (paper §5.1 machinery): the model kernel integrates to
`O(r²)` over balls of radius `r`, uniformly. -/
theorem setIntegral_invSqKer_ball_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∫ z in {z : T4 | torusDistSq z ≤ r ^ 2}, invSqKer z ∂paperMeasure
        ≤ C * r ^ 2 := by
  refine ⟨8 * vB, by have := vB_pos; positivity, fun r hr => ?_⟩
  have hmeasS : MeasurableSet {z : T4 | torusDistSq z ≤ r ^ 2} :=
    measurable_torusDistSq measurableSet_Iic
  rw [← integral_indicator hmeasS]
  refine le_trans (integral_mono_of_nonneg
    (.of_forall fun z => Set.indicator_nonneg (fun w _ => invSqKer_nonneg w) _)
    (integrable_invSqKer.indicator (measurable_norm measurableSet_Iic))
    (.of_forall fun z => ?_)) (indicator_ball_invSqKer_le r hr)
  refine Set.indicator_le_indicator_of_subset ?_ invSqKer_nonneg z
  intro w hw
  have h1 : ‖w‖ ^ 2 ≤ r ^ 2 := (sq_norm_le_torusDistSq w).trans hw
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hr.le] at h2

/-! ## Stage 2 (b): the annulus bound -/

/-- Primary (sup-norm) form of the annulus bound for the *square* of the
model kernel (the critical, log-divergent power in `d = 4`). -/
private lemma indicator_annulus_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫ z, ({z : T4 | r / 2 ≤ ‖z‖}.indicator fun z => invSqKer z ^ 2) z ∂paperMeasure
      ≤ 4 * vB * (Real.log 5 - Real.log (r / 2)) := by
  have hmeasS : MeasurableSet {z : T4 | r / 2 ≤ ‖z‖} :=
    measurable_norm measurableSet_Ici
  rw [torus_integral_eq_cube
    ((measurable_invSqKer.pow_const 2).indicator hmeasS).aestronglyMeasurable]
  have hmeasA : MeasurableSet {x : R4 | ‖x‖ ∈ Ico (r / 2) 5} :=
    measurable_norm measurableSet_Ico
  set m : R4 → ℝ :=
    {x : R4 | ‖x‖ ∈ Ico (r / 2) 5}.indicator fun x => ‖x‖ ^ (-(4 : ℝ)) with hm
  have hmnn : ∀ x, 0 ≤ m x := fun x =>
    Set.indicator_nonneg (fun y _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hmi : Integrable m volume := by
    rw [hm, integrable_indicator_iff hmeasA]
    have hsub : {x : R4 | ‖x‖ ∈ Ico (r / 2) 5} ⊆ Metric.ball (0 : R4) 5 := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right]
      exact hx.2
    have hvol : volume {x : R4 | ‖x‖ ∈ Ico (r / 2) 5} ≠ ∞ :=
      (lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top).ne
    refine Integrable.mono' (g := fun _ => (r / 2) ^ (-(4 : ℝ)))
      (integrableOn_const hvol)
      (Measurable.aestronglyMeasurable (by fun_prop)).restrict
      ?_
    filter_upwards [ae_restrict_mem hmeasA] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact rpow_neg_anti (by positivity) hx.1 (by norm_num)
  have hb : ∫ x in boxIoc,
      ({z : T4 | r / 2 ≤ ‖z‖}.indicator fun z => invSqKer z ^ 2) (mkT4 x) ∂volume
      ≤ ∫ x in boxIoc, m x ∂volume := by
    refine integral_mono_of_nonneg
      (.of_forall fun x => Set.indicator_nonneg (fun z _ => sq_nonneg _) _)
      hmi.restrict ?_
    filter_upwards [ae_box, ae_restrict_mem measurableSet_boxIoc] with x hx hxbox
    by_cases hmem : mkT4 x ∈ {z : T4 | r / 2 ≤ ‖z‖}
    · rw [Set.indicator_of_mem hmem]
      have hxnorm : ‖x‖ ∈ Ico (r / 2) 5 := by
        constructor
        · rw [← norm_mkT4 hx]; exact hmem
        · exact lt_of_le_of_lt (box_norm_le hxbox)
            (by linarith [Real.pi_le_four])
      rw [hm, Set.indicator_of_mem
        (show x ∈ {x : R4 | ‖x‖ ∈ Ico (r / 2) 5} from hxnorm), invSqKer_mkT4 hx]
      have hknn : 0 ≤ cubeKer x :=
        inv_nonneg.mpr (Finset.sum_nonneg fun i _ => sq_nonneg _)
      calc cubeKer x ^ 2 ≤ (‖x‖ ^ (-(2 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ hknn (cubeKer_le x) 2
        _ = ‖x‖ ^ (-(4 : ℝ)) := by
            rw [← Real.rpow_natCast (‖x‖ ^ (-(2 : ℝ))) 2,
              ← Real.rpow_mul (norm_nonneg _)]
            norm_num
    · rw [Set.indicator_of_notMem hmem]
      exact hmnn x
  refine hb.trans ?_
  calc ∫ x in boxIoc, m x ∂volume
      ≤ ∫ x, m x ∂volume := setIntegral_le_integral hmi (.of_forall hmnn)
    _ = 4 * vB * (Real.log 5 - Real.log (r / 2)) := by
        rw [hm, integral_indicator hmeasA]
        exact cube_annulus_value (by positivity) (by linarith)

/-- **Annulus bound** ((4.11)-adjacent): the square of the model kernel —
critical in `d = 4` — integrates to `O(1 + |log r|)` outside a ball of
radius `r ≤ 1`. -/
theorem setIntegral_invSqKer_sq_annulus_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫ z in {z : T4 | r ^ 2 ≤ torusDistSq z}, invSqKer z ^ 2 ∂paperMeasure
        ≤ C * (1 + |Real.log r|) := by
  refine ⟨20 * vB, by have := vB_pos; positivity, fun r hr hr1 => ?_⟩
  have hmeasS : MeasurableSet {z : T4 | r ^ 2 ≤ torusDistSq z} :=
    measurable_torusDistSq measurableSet_Ici
  rw [← integral_indicator hmeasS]
  have hint : Integrable
      ({z : T4 | r / 2 ≤ ‖z‖}.indicator fun z => invSqKer z ^ 2) paperMeasure := by
    refine Integrable.mono' (g := fun _ : T4 => (((r / 2) ^ 2)⁻¹) ^ 2)
      (integrable_const _)
      ((measurable_invSqKer.pow_const 2).indicator
        (measurable_norm measurableSet_Ici)).aestronglyMeasurable
      (.of_forall fun z => ?_)
    by_cases hmem : z ∈ {z : T4 | r / 2 ≤ ‖z‖}
    · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (invSqKer_nonneg z) 2)]
      refine pow_le_pow_left₀ (invSqKer_nonneg z) ?_ 2
      refine inv_anti₀ (by positivity) ?_
      calc (r / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hmem 2
        _ ≤ torusDistSq z := sq_norm_le_torusDistSq z
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      positivity
  have step1 : ∫ z,
      ({z : T4 | r ^ 2 ≤ torusDistSq z}.indicator fun z => invSqKer z ^ 2) z
        ∂paperMeasure ≤ 4 * vB * (Real.log 5 - Real.log (r / 2)) := by
    refine le_trans (integral_mono_of_nonneg
      (.of_forall fun z => Set.indicator_nonneg (fun w _ => sq_nonneg _) _)
      hint (.of_forall fun z => ?_)) (indicator_annulus_le r hr hr1)
    refine Set.indicator_le_indicator_of_subset ?_ (fun w => sq_nonneg _) z
    intro w hw
    have h1 : (r / 2) ^ 2 ≤ ‖w‖ ^ 2 := by
      have h2 := le_trans hw (torusDistSq_le_four_mul_sq_norm w)
      nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h2
  refine step1.trans ?_
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlog5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
  have hsplit : Real.log (r / 2) = Real.log r - Real.log 2 :=
    Real.log_div hr.ne' (by norm_num)
  have hvB := vB_pos
  have habs := neg_le_abs (Real.log r)
  have habs0 : (0 : ℝ) ≤ |Real.log r| := abs_nonneg _
  rw [hsplit]
  nlinarith

/-! ## Stage 2 (c): auxiliary kernel family `d(z)^{-b}` -/

/-- Auxiliary kernel family `torusDistSq z ^ (-b)`; subcritical for
`b < 2` (i.e. `|z|^{-2b}` with `2b < 4`). `powKer 1 = invSqKer`. -/
private def powKer (b : ℝ) (z : T4) : ℝ := torusDistSq z ^ (-b)

private lemma powKer_nonneg (b : ℝ) (z : T4) : 0 ≤ powKer b z :=
  Real.rpow_nonneg (torusDistSq_nonneg z) _

private lemma measurable_powKer (b : ℝ) : Measurable (powKer b) :=
  measurable_torusDistSq.pow_const _

private lemma invSqKer_eq_powKer_one : invSqKer = powKer 1 := by
  funext z
  unfold invSqKer powKer
  rw [Real.rpow_neg_one]

private lemma powKer_neg (b : ℝ) (z : T4) : powKer b (-z) = powKer b z := by
  unfold powKer
  rw [torusDistSq_neg]

private lemma powKer_sub_comm (b : ℝ) (x y : T4) :
    powKer b (x - y) = powKer b (y - x) := by
  rw [← powKer_neg b (x - y), neg_sub]

/-- Splitting of exponents (both branches, including the junk value at the
singularity, agree). -/
private lemma powKer_add {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (z : T4) :
    powKer (b + c) z = powKer b z * powKer c z := by
  unfold powKer
  rcases (torusDistSq_nonneg z).eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (neg_ne_zero.mpr (by positivity : (0:ℝ) < b + c).ne'),
      Real.zero_rpow (neg_ne_zero.mpr hb.ne'), zero_mul]
  · rw [neg_add, Real.rpow_add h]

private lemma integrable_powKer {b : ℝ} (hb : 0 < b) (hb2 : b < 2) :
    Integrable (powKer b) paperMeasure := by
  have h := measurePreserving_mkT4.integrable_comp
    (measurable_powKer b).aestronglyMeasurable
  rw [← h]
  refine Integrable.mono' (g := fun x : R4 => ‖x‖ ^ (-(2 * b)))
    ((integrableOn_rpow_ball (by linarith) 5).mono_set boxIoc_subset_ball)
    ((measurable_powKer b).comp measurable_mkT4).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_box] with x hx
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (powKer_nonneg b _)]
  show powKer b (mkT4 x) ≤ ‖x‖ ^ (-(2 * b))
  unfold powKer
  rw [torusDistSq_mkT4 hx]
  have h1 : ((‖x‖ ^ (2 : ℕ) : ℝ)) ^ (-b) = ‖x‖ ^ (-(2 * b)) := by
    rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [← h1]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [Real.zero_rpow (neg_ne_zero.mpr hb.ne')]
  · exact rpow_neg_anti (pow_pos (norm_pos_iff.mpr hx0) 2)
      (sq_norm_le_sum x) hb.le

private lemma integral_shift (h : T4 → ℝ) (hm : Measurable h) (a : T4) :
    ∫ z, h (z - a) ∂paperMeasure = ∫ z, h z ∂paperMeasure := by
  have h1 := integral_map (μ := paperMeasure) (φ := fun z : T4 => z - a)
    (measurePreserving_sub_paper a).measurable.aemeasurable
    (f := h) hm.aestronglyMeasurable
  rw [(measurePreserving_sub_paper a).map_eq] at h1
  exact h1.symm

private lemma integrable_powKer_shift {b : ℝ} (hb : 0 < b) (hb2 : b < 2)
    (a : T4) : Integrable (fun z => powKer b (z - a)) paperMeasure :=
  ((measurePreserving_sub_paper a).integrable_comp
    (measurable_powKer b).aestronglyMeasurable).mpr (integrable_powKer hb hb2)

private lemma integral_powKer_shift (b : ℝ) (a : T4) :
    ∫ z, powKer b (z - a) ∂paperMeasure = ∫ z, powKer b z ∂paperMeasure :=
  integral_shift (powKer b) (measurable_powKer b) a

/-! ## Stage 2 (c): a.e. positivity of the distance -/

/-- Singletons of the circle factor are null (the fiber of the quotient
map over a point is a countable coset). -/
private lemma volume_singleton_addCircle (a : AddCircle (2 * Real.pi)) :
    (volume : Measure (AddCircle (2 * Real.pi))) {a} = 0 := by
  obtain ⟨x₀, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [← (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).measure_preimage
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
      exact ⟨k, by show x₀ + k • (2 * Real.pi) = y; linarith [hk]⟩
    exact (Set.countable_range _).mono hsub
  rw [Measure.restrict_apply
    (AddCircle.measurable_mk' (measurableSet_singleton _))]
  exact measure_mono_null Set.inter_subset_left (hcount.measure_zero volume)

/-- Almost every point of the torus is away from the singularity. -/
private lemma ae_torusDistSq_pos : ∀ᵐ z ∂paperMeasure, 0 < torusDistSq z := by
  have h0 : paperMeasure {(0 : T4)} = 0 := by
    rw [paperMeasure_eq_volume, volume_pi]
    refine measure_mono_null (fun z hz => ?_)
      (Measure.pi_eval_preimage_null (i := (0 : Fin dim))
        (fun _ : Fin dim => (volume : Measure (AddCircle (2 * Real.pi))))
        (volume_singleton_addCircle 0))
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rfl
  filter_upwards [compl_mem_ae_iff.mpr h0] with z hz
  rcases (torusDistSq_nonneg z).eq_or_lt with h | h
  · exact absurd (Set.mem_singleton_iff.mpr
      ((torusDistSq_eq_zero_iff z).mp h.symm)) hz
  · exact h

/-! ## Stage 2 (c): pointwise region estimates -/

private lemma invSqKer_le_inv_sq_norm (w : T4) : invSqKer w ≤ (‖w‖ ^ 2)⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 : torusDistSq (0 : T4) = 0 := (torusDistSq_eq_zero_iff 0).mpr rfl
    unfold invSqKer
    rw [h0]
    simp
  · exact inv_anti₀ (pow_pos (norm_pos_iff.mpr hw) 2) (sq_norm_le_torusDistSq w)

private lemma invSqKer_sq_eq_powKer_two (w : T4) :
    invSqKer w ^ 2 = powKer 2 w := by
  unfold invSqKer powKer
  rw [inv_pow, Real.rpow_neg (torusDistSq_nonneg w), Real.rpow_two]

/-- Far-region pointwise bound: away from both singularities, the product
of kernels splits into integrable `d^{-7/4}` weights at the cost of a
`(|z₁|/2)^{-1/2}` factor (the `ab ≤ (a²+b²)/2` trick plus an exponent
split `2 = 7/4 + 1/4`). -/
private lemma far_pointwise {z₁ z₂ : T4} (h1 : ‖z₁‖ / 2 < ‖z₂‖)
    (h2 : ‖z₁‖ / 2 < ‖z₂ - z₁‖) (hn : 0 < ‖z₁‖) :
    invSqKer (z₁ - z₂) * invSqKer z₂ ≤
      ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) / 2 *
        (powKer (7/4) (z₁ - z₂) + powKer (7/4) z₂) := by
  set c := ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) with hc
  have key : ∀ w : T4, ‖z₁‖ / 2 < ‖w‖ → invSqKer w ^ 2 ≤ c * powKer (7/4) w := by
    intro w hw
    rw [invSqKer_sq_eq_powKer_two w, show (2 : ℝ) = 7/4 + 1/4 by norm_num,
      powKer_add (by norm_num) (by norm_num), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (powKer_nonneg _ _)
    refine rpow_neg_anti (by positivity) ?_ (by norm_num)
    exact le_trans (pow_le_pow_left₀ (by positivity) hw.le 2)
      (sq_norm_le_torusDistSq w)
  have hab : invSqKer (z₁ - z₂) * invSqKer z₂
      ≤ (invSqKer (z₁ - z₂) ^ 2 + invSqKer z₂ ^ 2) / 2 := by
    nlinarith [sq_nonneg (invSqKer (z₁ - z₂) - invSqKer z₂)]
  refine hab.trans ?_
  have hk1 : invSqKer (z₁ - z₂) ^ 2 ≤ c * powKer (7/4) (z₁ - z₂) := by
    refine key _ ?_
    rwa [norm_sub_rev]
  have hk2 := key z₂ h1
  calc (invSqKer (z₁ - z₂) ^ 2 + invSqKer z₂ ^ 2) / 2
      ≤ (c * powKer (7/4) (z₁ - z₂) + c * powKer (7/4) z₂) / 2 := by linarith
    _ = c / 2 * (powKer (7/4) (z₁ - z₂) + powKer (7/4) z₂) := by ring

/-- Outer pointwise bound: a product of singularities at two centers is
dominated by the sum of the concentrated ones (exponent `1 + 1/4 = 5/4`,
subcritical). -/
private lemma outer_pointwise (x z₁ : T4) :
    invSqKer (x - z₁) * powKer (1/4) z₁ ≤
      powKer (5/4) (x - z₁) + powKer (5/4) z₁ := by
  have h54 : powKer (5/4) = powKer (1 + 1/4) := by norm_num
  rcases le_total (torusDistSq (x - z₁)) (torusDistSq z₁) with h | h
  · rcases (torusDistSq_nonneg (x - z₁)).eq_or_lt with h0 | h0
    · have hz : invSqKer (x - z₁) = 0 := by
        unfold invSqKer
        rw [← h0, inv_zero]
      rw [hz, zero_mul]
      exact add_nonneg (powKer_nonneg _ _) (powKer_nonneg _ _)
    · refine le_add_of_le_of_nonneg ?_ (powKer_nonneg _ _)
      rw [h54, powKer_add one_pos (by norm_num), ← invSqKer_eq_powKer_one]
      refine mul_le_mul_of_nonneg_left ?_ (invSqKer_nonneg _)
      exact rpow_neg_anti h0 h (by norm_num)
  · rcases (torusDistSq_nonneg z₁).eq_or_lt with h0 | h0
    · have hz : powKer (1/4) z₁ = 0 := by
        unfold powKer
        rw [← h0, Real.zero_rpow (by norm_num)]
      rw [hz, mul_zero]
      exact add_nonneg (powKer_nonneg _ _) (powKer_nonneg _ _)
    · refine le_add_of_nonneg_of_le (powKer_nonneg _ _) ?_
      rw [h54, powKer_add one_pos (by norm_num)]
      refine mul_le_mul_of_nonneg_right ?_ (powKer_nonneg _ _)
      rw [invSqKer_eq_powKer_one]
      exact rpow_neg_anti h0 h (by norm_num)

/-! ## Stage 2 (c): the convolution bounds -/

private def I74 : ℝ := ∫ z, powKer (7/4) z ∂paperMeasure

private lemma I74_nonneg : 0 ≤ I74 := integral_nonneg (powKer_nonneg _)

private def I54 : ℝ := ∫ z, powKer (5/4) z ∂paperMeasure

private lemma I54_nonneg : 0 ≤ I54 := integral_nonneg (powKer_nonneg _)

private def I1 : ℝ := ∫ z, invSqKer z ∂paperMeasure

private lemma I1_nonneg : 0 ≤ I1 := integral_nonneg invSqKer_nonneg

/-- Shifted form of the primary ball bound. -/
private lemma indicator_ball_shift_le (s : ℝ) (hs : 0 < s) (a : T4) :
    ∫ z, ({z : T4 | ‖z - a‖ ≤ s}.indicator fun z => invSqKer (z - a)) z
      ∂paperMeasure ≤ 8 * vB * s ^ 2 := by
  have he : (fun z => ({z : T4 | ‖z - a‖ ≤ s}.indicator
      fun z => invSqKer (z - a)) z)
      = fun z => ({w : T4 | ‖w‖ ≤ s}.indicator invSqKer) (z - a) := by
    funext z
    by_cases h : ‖z - a‖ ≤ s
    · rw [Set.indicator_of_mem (show z ∈ {z : T4 | ‖z - a‖ ≤ s} from h),
        Set.indicator_of_mem (show z - a ∈ {w : T4 | ‖w‖ ≤ s} from h)]
    · rw [Set.indicator_of_notMem (show z ∉ {z : T4 | ‖z - a‖ ≤ s} from h),
        Set.indicator_of_notMem (show z - a ∉ {w : T4 | ‖w‖ ≤ s} from h)]
  rw [he, integral_shift ({w : T4 | ‖w‖ ≤ s}.indicator invSqKer)
    (measurable_invSqKer.indicator (measurable_norm measurableSet_Iic)) a]
  exact indicator_ball_invSqKer_le s hs

/-- Arithmetic core of the near-region bounds: on `|z₂|`-scale `|z₁|/2`,
the complementary kernel is `≤ 16/d(z₁)`. -/
private lemma inv_half_sq_le {z₁ : T4} (hd : 0 < torusDistSq z₁) :
    ((‖z₁‖ / 2) ^ 2)⁻¹ ≤ 16 / torusDistSq z₁ := by
  have h4 : torusDistSq z₁ ≤ 16 * (‖z₁‖ / 2) ^ 2 := by
    have := torusDistSq_le_four_mul_sq_norm z₁
    nlinarith
  have hnpos : 0 < (‖z₁‖ / 2) ^ 2 := by
    rcases eq_or_ne z₁ 0 with rfl | hz
    · exact absurd ((torusDistSq_eq_zero_iff 0).mpr rfl) hd.ne'
    · have := norm_pos_iff.mpr hz
      positivity
  have hne : ‖z₁‖ ≠ 0 := by
    intro h
    rw [h] at hnpos
    norm_num at hnpos
  rw [le_div_iff₀ hd]
  calc ((‖z₁‖ / 2) ^ 2)⁻¹ * torusDistSq z₁
      ≤ ((‖z₁‖ / 2) ^ 2)⁻¹ * (16 * (‖z₁‖ / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 16 := by field_simp

/-- The far-region weight is controlled by `powKer (1/4)`. -/
private lemma quarter_weight_le {z₁ : T4} (hd : 0 < torusDistSq z₁) :
    ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) ≤ 2 * powKer (1/4) z₁ := by
  have hq : torusDistSq z₁ / 16 ≤ (‖z₁‖ / 2) ^ 2 := by
    have := torusDistSq_le_four_mul_sq_norm z₁
    nlinarith
  refine (rpow_neg_anti (by positivity) hq (by norm_num)).trans ?_
  have h16 : ((16 : ℝ)⁻¹) ^ (-(1/4 : ℝ)) = 2 := by
    rw [Real.inv_rpow (by norm_num : (0:ℝ) ≤ 16),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 16), inv_inv,
      show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast 2 4,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  unfold powKer
  rw [div_eq_mul_inv, Real.mul_rpow hd.le (by norm_num), h16, mul_comm]

/-- Pointwise three-region decomposition of the binary product of kernels:
near either singularity the complementary kernel is `≲ d(z₁)⁻¹` (regions
covered by balls of radius `|z₁|/2`), and in the far region the
`ab ≤ (a²+b²)/2` split applies. -/
private lemma inner_pointwise {z₁ : T4} (hd : 0 < torusDistSq z₁) (z₂ : T4) :
    invSqKer (z₁ - z₂) * invSqKer z₂ ≤
      16 / torusDistSq z₁ * ({z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}.indicator invSqKer) z₂
      + 16 / torusDistSq z₁ *
          ({z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}.indicator fun w => invSqKer (w - z₁)) z₂
      + ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) / 2 *
          (powKer (7/4) (z₁ - z₂) + powKer (7/4) z₂) := by
  have hn : 0 < ‖z₁‖ := by
    rcases eq_or_ne z₁ 0 with rfl | hz
    · exact absurd ((torusDistSq_eq_zero_iff 0).mpr rfl) hd.ne'
    · exact norm_pos_iff.mpr hz
  have hkey := inv_half_sq_le hd
  have ht1 : 0 ≤ 16 / torusDistSq z₁ *
      ({z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}.indicator invSqKer) z₂ :=
    mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun w _ => invSqKer_nonneg w) _)
  have ht2 : 0 ≤ 16 / torusDistSq z₁ *
      ({z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}.indicator fun w => invSqKer (w - z₁)) z₂ :=
    mul_nonneg (by positivity)
      (Set.indicator_nonneg (fun w _ => invSqKer_nonneg _) _)
  have ht3 : 0 ≤ ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) / 2 *
      (powKer (7/4) (z₁ - z₂) + powKer (7/4) z₂) :=
    mul_nonneg (by positivity)
      (add_nonneg (powKer_nonneg _ _) (powKer_nonneg _ _))
  by_cases hz1 : z₂ ∈ {z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}
  · have hstep : invSqKer (z₁ - z₂) * invSqKer z₂ ≤
        16 / torusDistSq z₁ *
          ({z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}.indicator invSqKer) z₂ := by
      rw [Set.indicator_of_mem hz1]
      refine mul_le_mul_of_nonneg_right ?_ (invSqKer_nonneg _)
      have hfar : ‖z₁‖ / 2 ≤ ‖z₁ - z₂‖ := by
        have h := norm_sub_norm_le z₁ z₂
        have h2 : ‖z₂‖ ≤ ‖z₁‖ / 2 := hz1
        linarith
      calc invSqKer (z₁ - z₂) ≤ (‖z₁ - z₂‖ ^ 2)⁻¹ := invSqKer_le_inv_sq_norm _
        _ ≤ ((‖z₁‖ / 2) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hfar 2)
        _ ≤ 16 / torusDistSq z₁ := hkey
    linarith
  · by_cases hz2 : z₂ ∈ {z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}
    · have hstep : invSqKer (z₁ - z₂) * invSqKer z₂ ≤
          16 / torusDistSq z₁ *
            ({z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}.indicator
              fun w => invSqKer (w - z₁)) z₂ := by
        rw [Set.indicator_of_mem hz2, invSqKer_sub_comm z₂ z₁,
          mul_comm (invSqKer (z₁ - z₂))]
        refine mul_le_mul_of_nonneg_right ?_ (invSqKer_nonneg _)
        have hfar : ‖z₁‖ / 2 ≤ ‖z₂‖ := by
          have ht : ‖z₁‖ ≤ ‖z₁ - z₂‖ + ‖z₂‖ := by
            calc ‖z₁‖ = ‖z₁ - z₂ + z₂‖ := by rw [sub_add_cancel]
              _ ≤ ‖z₁ - z₂‖ + ‖z₂‖ := norm_add_le _ _
          have hr : ‖z₁ - z₂‖ ≤ ‖z₁‖ / 2 := by
            rw [norm_sub_rev]
            exact hz2
          linarith
        calc invSqKer z₂ ≤ (‖z₂‖ ^ 2)⁻¹ := invSqKer_le_inv_sq_norm _
          _ ≤ ((‖z₁‖ / 2) ^ 2)⁻¹ :=
              inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hfar 2)
          _ ≤ 16 / torusDistSq z₁ := hkey
      linarith
    · have hstep := far_pointwise (not_le.mp hz1) (not_le.mp hz2) hn
      linarith

/-- A binary inverse-square convolution is genuinely integrable away
from the coincident-endpoint diagonal.  This is the fixed-endpoint
counterpart of the joint Green-path integrability theorem; the
restriction is sharp in dimension four. -/
theorem integrable_invSqKer_sub_mul_invSqKer_of_ne
    {z₁ : T4} (hz₁ : z₁ ≠ 0) :
    Integrable
      (fun z₂ : T4 =>
        invSqKer (z₁ - z₂) * invSqKer z₂)
      paperMeasure := by
  have hd : 0 < torusDistSq z₁ := by
    have hne : torusDistSq z₁ ≠ 0 := by
      intro hzero
      exact hz₁ ((torusDistSq_eq_zero_iff z₁).mp hzero)
    exact lt_of_le_of_ne
      (torusDistSq_nonneg z₁) (Ne.symm hne)
  have hS1m :
      MeasurableSet {z : T4 | ‖z‖ ≤ ‖z₁‖ / 2} :=
    measurable_norm measurableSet_Iic
  have hS2m :
      MeasurableSet
        {z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2} :=
    ((measurePreserving_sub_paper z₁).measurable.norm)
      measurableSet_Iic
  let g₁ : T4 → ℝ := fun z₂ =>
    16 / torusDistSq z₁ *
      ({z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}.indicator
        invSqKer) z₂
  let g₂ : T4 → ℝ := fun z₂ =>
    16 / torusDistSq z₁ *
      ({z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}.indicator
        (fun w => invSqKer (w - z₁))) z₂
  let g₃ : T4 → ℝ := fun z₂ =>
    ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) / 2 *
      (powKer (7/4) (z₁ - z₂) +
        powKer (7/4) z₂)
  have hg₁ : Integrable g₁ paperMeasure := by
    exact
      (integrable_invSqKer.indicator hS1m).const_mul _
  have hg₂ : Integrable g₂ paperMeasure := by
    exact
      ((integrable_invSqKer_sub z₁).indicator hS2m).const_mul _
  have hshift74 :
      Integrable
        (fun z₂ : T4 => powKer (7/4) (z₁ - z₂))
        paperMeasure := by
    rw [show
      (fun z₂ : T4 => powKer (7/4) (z₁ - z₂)) =
        fun z₂ => powKer (7/4) (z₂ - z₁) from
          funext fun w => powKer_sub_comm _ _ _]
    exact integrable_powKer_shift
      (by norm_num) (by norm_num) z₁
  have hi74 :
      Integrable (powKer (7/4)) paperMeasure :=
    integrable_powKer (by norm_num) (by norm_num)
  have hg₃ : Integrable g₃ paperMeasure := by
    exact (hshift74.add hi74).const_mul _
  refine Integrable.mono' ((hg₁.add hg₂).add hg₃) ?_ ?_
  · exact
      ((measurable_invSqKer.comp
          (measurable_const.sub measurable_id)).mul
        measurable_invSqKer).aestronglyMeasurable
  · filter_upwards with z₂
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg
          (invSqKer_nonneg _)
          (invSqKer_nonneg _))]
    exact inner_pointwise hd z₂

/-- Translation-invariant two-centre form of
`integrable_invSqKer_sub_mul_invSqKer_of_ne`. -/
theorem integrable_invSqKer_two_center_of_ne
    {x y : T4} (hxy : x ≠ y) :
    Integrable
      (fun z : T4 =>
        invSqKer (x - z) * invSqKer (z - y))
      paperMeasure := by
  let f : T4 → ℝ := fun w =>
    invSqKer ((x - y) - w) * invSqKer w
  have hf : Integrable f paperMeasure := by
    exact
      integrable_invSqKer_sub_mul_invSqKer_of_ne
        (sub_ne_zero.mpr hxy)
  have hcomp :=
    ((measurePreserving_sub_paper y).integrable_comp
      hf.aestronglyMeasurable).mpr hf
  convert hcomp using 1
  funext z
  unfold f
  apply congrArg₂ (· * ·)
  · apply congrArg invSqKer
    module
  · rfl

/-- The (weakened, log-free) binary convolution bound:
`(|·|⁻² ⊛ |·|⁻²)(z₁) ≤ C (1 + d(z₁)^{-1/4})`. -/
private lemma inner_bound {z₁ : T4} (hd : 0 < torusDistSq z₁) :
    (∫ z₂, invSqKer (z₁ - z₂) * invSqKer z₂ ∂paperMeasure)
      ≤ 64 * vB + 2 * I74 * powKer (1/4) z₁ := by
  have hn : 0 < ‖z₁‖ := by
    rcases eq_or_ne z₁ 0 with rfl | hz
    · exact absurd ((torusDistSq_eq_zero_iff 0).mpr rfl) hd.ne'
    · exact norm_pos_iff.mpr hz
  have hS1m : MeasurableSet {z : T4 | ‖z‖ ≤ ‖z₁‖ / 2} :=
    measurable_norm measurableSet_Iic
  have hS2m : MeasurableSet {z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2} :=
    ((measurePreserving_sub_paper z₁).measurable.norm) measurableSet_Iic
  have hi1 : Integrable (fun z₂ => 16 / torusDistSq z₁ *
      ({z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}.indicator invSqKer) z₂) paperMeasure :=
    (integrable_invSqKer.indicator hS1m).const_mul _
  have hi2 : Integrable (fun z₂ => 16 / torusDistSq z₁ *
      ({z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}.indicator
        fun w => invSqKer (w - z₁)) z₂) paperMeasure :=
    ((integrable_invSqKer_sub z₁).indicator hS2m).const_mul _
  have hshift74 : Integrable (fun z₂ : T4 => powKer (7/4) (z₁ - z₂))
      paperMeasure := by
    rw [show (fun z₂ : T4 => powKer (7/4) (z₁ - z₂))
      = fun z₂ => powKer (7/4) (z₂ - z₁) from funext fun w => powKer_sub_comm _ _ _]
    exact integrable_powKer_shift (by norm_num) (by norm_num) z₁
  have hi74 : Integrable (powKer (7/4)) paperMeasure :=
    integrable_powKer (by norm_num) (by norm_num)
  have hi3 : Integrable (fun z₂ => ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) / 2 *
      (powKer (7/4) (z₁ - z₂) + powKer (7/4) z₂)) paperMeasure :=
    (hshift74.add hi74).const_mul _
  refine (integral_mono_of_nonneg
    (.of_forall fun z₂ => mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _))
    ((hi1.add hi2).add hi3) (.of_forall (inner_pointwise hd))).trans ?_
  simp only [Pi.add_apply]
  have hi12 : Integrable (fun z₂ =>
      16 / torusDistSq z₁ * ({z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}.indicator invSqKer) z₂
      + 16 / torusDistSq z₁ * ({z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}.indicator
          fun w => invSqKer (w - z₁)) z₂) paperMeasure := hi1.add hi2
  rw [integral_add hi12 hi3, integral_add hi1 hi2,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have hb1 : 16 / torusDistSq z₁ *
      ∫ z₂, ({z : T4 | ‖z‖ ≤ ‖z₁‖ / 2}.indicator invSqKer) z₂ ∂paperMeasure
      ≤ 32 * vB := by
    have hball := indicator_ball_invSqKer_le (‖z₁‖ / 2) (by positivity)
    have hn2 : ‖z₁‖ ^ 2 ≤ torusDistSq z₁ := sq_norm_le_torusDistSq z₁
    refine le_trans (mul_le_mul_of_nonneg_left hball (by positivity)) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith [vB_pos]
  have hb2 : 16 / torusDistSq z₁ *
      ∫ z₂, ({z : T4 | ‖z - z₁‖ ≤ ‖z₁‖ / 2}.indicator
        fun w => invSqKer (w - z₁)) z₂ ∂paperMeasure ≤ 32 * vB := by
    have hball := indicator_ball_shift_le (‖z₁‖ / 2) (by positivity) z₁
    have hn2 : ‖z₁‖ ^ 2 ≤ torusDistSq z₁ := sq_norm_le_torusDistSq z₁
    refine le_trans (mul_le_mul_of_nonneg_left hball (by positivity)) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith [vB_pos]
  have hb3 : ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) / 2 *
      ∫ z₂, (powKer (7/4) (z₁ - z₂) + powKer (7/4) z₂) ∂paperMeasure
      ≤ 2 * I74 * powKer (1/4) z₁ := by
    have hv : ∫ z₂, (powKer (7/4) (z₁ - z₂) + powKer (7/4) z₂) ∂paperMeasure
        = 2 * I74 := by
      rw [integral_add hshift74 hi74]
      have hv1 : ∫ z₂, powKer (7/4) (z₁ - z₂) ∂paperMeasure = I74 := by
        rw [show (fun z₂ : T4 => powKer (7/4) (z₁ - z₂))
          = fun z₂ => powKer (7/4) (z₂ - z₁) from
            funext fun w => powKer_sub_comm _ _ _]
        exact integral_powKer_shift (7/4) z₁
      rw [hv1]
      show I74 + I74 = 2 * I74
      ring
    rw [hv]
    have hq := quarter_weight_le hd
    calc ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) / 2 * (2 * I74)
        = ((‖z₁‖ / 2) ^ 2) ^ (-(1/4 : ℝ)) * I74 := by ring
      _ ≤ 2 * powKer (1/4) z₁ * I74 :=
          mul_le_mul_of_nonneg_right hq I74_nonneg
      _ = 2 * I74 * powKer (1/4) z₁ := by ring
  linarith

/-- A binary inverse-square convolution preserves the off-diagonal
inverse-square majorant.  The deliberately coarse power `d⁻¹/⁴` in
`inner_bound` is still dominated by `1 + d⁻¹`; compactness of the torus
then absorbs the constant term into `d⁻¹`. -/
theorem binary_conv_invSqKer_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : T4, x ≠ 0 →
      (∫ z, invSqKer (x - z) * invSqKer z
          ∂paperMeasure) ≤
        C * invSqKer x := by
  let B : ℝ := 64 * vB + 2 * I74
  let D : ℝ := 4 * Real.pi ^ 2
  let C : ℝ := B * (D + 1) + 1
  have hB : 0 < B := by
    dsimp only [B]
    have := vB_pos
    have := I74_nonneg
    positivity
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun x hx => ?_⟩
  have hdne : torusDistSq x ≠ 0 := by
    intro hzero
    exact hx ((torusDistSq_eq_zero_iff x).mp hzero)
  have hd : 0 < torusDistSq x :=
    lt_of_le_of_ne (torusDistSq_nonneg x) hdne.symm
  have hquarter :
      powKer (1 / 4) x ≤ 1 + invSqKer x := by
    unfold powKer invSqKer
    by_cases hsmall : torusDistSq x ≤ 1
    · have hpow :
          torusDistSq x ^ (-(1 / 4 : ℝ)) ≤
            torusDistSq x ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge
          hd hsmall (by norm_num)
      rw [Real.rpow_neg_one] at hpow
      exact hpow.trans (le_add_of_nonneg_left zero_le_one)
    · have hone : 1 ≤ torusDistSq x := le_of_not_ge hsmall
      have hpow :
          torusDistSq x ^ (-(1 / 4 : ℝ)) ≤
            torusDistSq x ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          hone (by norm_num)
      rw [Real.rpow_zero] at hpow
      exact hpow.trans
        (le_add_of_nonneg_right
          (inv_nonneg.mpr (torusDistSq_nonneg x)))
  have honeInv :
      1 ≤ D * invSqKer x := by
    unfold D invSqKer
    rw [le_mul_inv_iff₀ hd]
    simpa only [one_mul] using torusDistSq_le x
  have hinner := inner_bound hd
  calc
    (∫ z, invSqKer (x - z) * invSqKer z
        ∂paperMeasure) ≤
        64 * vB + 2 * I74 * powKer (1 / 4) x :=
      hinner
    _ ≤ B * (1 + invSqKer x) := by
      dsimp only [B]
      have hscaled :
          2 * I74 * powKer (1 / 4) x ≤
            2 * I74 * (1 + invSqKer x) :=
        mul_le_mul_of_nonneg_left hquarter
          (mul_nonneg (by norm_num) I74_nonneg)
      have hvterm :
          0 ≤ 64 * vB * invSqKer x :=
        mul_nonneg
          (mul_nonneg (by norm_num) vB_pos.le)
          (invSqKer_nonneg x)
      nlinarith
    _ ≤ B * ((D + 1) * invSqKer x) := by
      apply mul_le_mul_of_nonneg_left _ hB.le
      nlinarith [invSqKer_nonneg x]
    _ ≤ C * invSqKer x := by
      dsimp only [C]
      nlinarith [invSqKer_nonneg x]

/-- Integrability of the square kernel after deleting a positive
neighbourhood of its singularity.  This is the Bochner-integrability
certificate used by the sharp logarithmic binary-convolution estimate
below. -/
private theorem integrable_invSqKer_sq_norm_annulus
    (r : ℝ) (hr : 0 < r) :
    Integrable
      ({z : T4 | r / 2 ≤ ‖z‖}.indicator
        fun z => invSqKer z ^ 2)
      paperMeasure := by
  let B : ℝ := (((r / 2) ^ 2)⁻¹) ^ (2 : ℕ)
  have hconst : Integrable (fun _ : T4 => B) paperMeasure :=
    integrable_const B
  refine Integrable.mono' hconst
    ((measurable_invSqKer.pow_const 2).indicator
      (measurable_norm measurableSet_Ici)).aestronglyMeasurable
    (.of_forall fun z => ?_)
  by_cases hz : r / 2 ≤ ‖z‖
  · rw [Set.indicator_of_mem
        (show z ∈ {w : T4 | r / 2 ≤ ‖w‖} from hz),
      Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    dsimp only [B]
    apply pow_le_pow_left₀ (invSqKer_nonneg z)
    unfold invSqKer
    exact inv_anti₀ (by positivity)
      ((pow_le_pow_left₀ (by positivity) hz 2).trans
        (sq_norm_le_torusDistSq z))
  · rw [Set.indicator_of_notMem
        (show z ∉ {w : T4 | r / 2 ≤ ‖w‖} from hz),
      norm_zero]
    positivity

/-- The binary inverse-square convolution has its sharp critical
logarithmic singularity.  Unlike the deliberately coarse public
`binary_conv_invSqKer_le`, this form retains the logarithm needed when
the convolution is averaged against an `ε`-scale inserted kernel. -/
theorem binary_conv_invSqKer_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : T4, x ≠ 0 →
      (∫ z, invSqKer (x - z) * invSqKer z
          ∂paperMeasure) ≤
        C * (1 + |Real.log ‖x‖|) := by
  let B : ℝ := 64 * vB + 2 * I74
  let C : ℝ := 84 * vB + B + 1
  have hB : 0 < B := by
    dsimp only [B]
    have := vB_pos
    have := I74_nonneg
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [vB_pos]
  refine ⟨C, hC, fun x hx => ?_⟩
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hd : 0 < torusDistSq x := by
    have hne : torusDistSq x ≠ 0 := by
      intro hzero
      exact hx ((torusDistSq_eq_zero_iff x).mp hzero)
    exact lt_of_le_of_ne (torusDistSq_nonneg x) hne.symm
  by_cases hr1 : ‖x‖ ≤ 1
  · let S₀ : Set T4 := {z | ‖z‖ ≤ ‖x‖ / 2}
    let Sx : Set T4 := {z | ‖z - x‖ ≤ ‖x‖ / 2}
    let A₀ : Set T4 := {z | ‖x‖ / 2 ≤ ‖z‖}
    let Ax : Set T4 := {z | ‖x‖ / 2 ≤ ‖z - x‖}
    let g₀ : T4 → ℝ := fun z =>
      16 / torusDistSq x * S₀.indicator invSqKer z
    let gx : T4 → ℝ := fun z =>
      16 / torusDistSq x *
        Sx.indicator (fun w => invSqKer (w - x)) z
    let a₀ : T4 → ℝ := fun z =>
      (1 / 2 : ℝ) * A₀.indicator (fun w => invSqKer w ^ 2) z
    let ax : T4 → ℝ := fun z =>
      (1 / 2 : ℝ) *
        Ax.indicator (fun w => invSqKer (w - x) ^ 2) z
    have hS₀ : MeasurableSet S₀ :=
      measurable_norm measurableSet_Iic
    have hSx : MeasurableSet Sx :=
      ((measurePreserving_sub_paper x).measurable.norm)
        measurableSet_Iic
    have hA₀ : MeasurableSet A₀ :=
      measurable_norm measurableSet_Ici
    have hAx : MeasurableSet Ax :=
      ((measurePreserving_sub_paper x).measurable.norm)
        measurableSet_Ici
    have hg₀ : Integrable g₀ paperMeasure :=
      (integrable_invSqKer.indicator hS₀).const_mul _
    have hgx : Integrable gx paperMeasure :=
      ((integrable_invSqKer_sub x).indicator hSx).const_mul _
    have ha₀ : Integrable a₀ paperMeasure := by
      exact
        (integrable_invSqKer_sq_norm_annulus ‖x‖ hr).const_mul _
    have haxBase :
        Integrable
          ({z : T4 | ‖x‖ / 2 ≤ ‖z‖}.indicator
            fun z => invSqKer z ^ 2)
          paperMeasure :=
      integrable_invSqKer_sq_norm_annulus ‖x‖ hr
    have haxCore :
        Integrable
          (fun z =>
            ({w : T4 | ‖x‖ / 2 ≤ ‖w‖}.indicator
              fun w => invSqKer w ^ 2) (z - x))
          paperMeasure :=
      ((measurePreserving_sub_paper x).integrable_comp
        ((measurable_invSqKer.pow_const 2).indicator
          (measurable_norm measurableSet_Ici)).aestronglyMeasurable).mpr
        haxBase
    have hax : Integrable ax paperMeasure := by
      apply Integrable.const_mul
      convert haxCore using 1
      funext z
      rfl
    have hmajorant :
        Integrable (fun z => g₀ z + gx z + a₀ z + ax z)
          paperMeasure :=
      ((hg₀.add hgx).add ha₀).add hax
    have hpoint : ∀ z,
        invSqKer (x - z) * invSqKer z ≤
          g₀ z + gx z + a₀ z + ax z := by
      intro z
      by_cases hz₀ : z ∈ S₀
      · have hfar : ‖x‖ / 2 ≤ ‖x - z‖ := by
          have h := norm_sub_norm_le x z
          have hzle : ‖z‖ ≤ ‖x‖ / 2 := hz₀
          linarith
        have hker :
            invSqKer (x - z) ≤ 16 / torusDistSq x := by
          calc
            invSqKer (x - z) ≤ (‖x - z‖ ^ 2)⁻¹ :=
              invSqKer_le_inv_sq_norm _
            _ ≤ ((‖x‖ / 2) ^ 2)⁻¹ :=
              inv_anti₀ (by positivity)
                (pow_le_pow_left₀ (by positivity) hfar 2)
            _ ≤ 16 / torusDistSq x := inv_half_sq_le hd
        have hmain :
            invSqKer (x - z) * invSqKer z ≤ g₀ z := by
          dsimp only [g₀]
          rw [Set.indicator_of_mem hz₀]
          exact mul_le_mul_of_nonneg_right hker
            (invSqKer_nonneg z)
        have hgxnn : 0 ≤ gx z := by
          dsimp only [gx]
          exact mul_nonneg (by positivity)
            (Set.indicator_nonneg
              (fun w _ => invSqKer_nonneg (w - x)) z)
        have ha₀nn : 0 ≤ a₀ z := by
          dsimp only [a₀]
          exact mul_nonneg (by norm_num)
            (Set.indicator_nonneg
              (fun w _ => sq_nonneg (invSqKer w)) z)
        have haxnn : 0 ≤ ax z := by
          dsimp only [ax]
          exact mul_nonneg (by norm_num)
            (Set.indicator_nonneg
              (fun w _ => sq_nonneg (invSqKer (w - x))) z)
        linarith
      · by_cases hzx : z ∈ Sx
        · have hfar : ‖x‖ / 2 ≤ ‖z‖ := by
            have ht : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
              calc
                ‖x‖ = ‖x - z + z‖ := by rw [sub_add_cancel]
                _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
            have hnear : ‖x - z‖ ≤ ‖x‖ / 2 := by
              rw [norm_sub_rev]
              exact (show ‖z - x‖ ≤ ‖x‖ / 2 from hzx)
            linarith
          have hker :
              invSqKer z ≤ 16 / torusDistSq x := by
            calc
              invSqKer z ≤ (‖z‖ ^ 2)⁻¹ :=
                invSqKer_le_inv_sq_norm _
              _ ≤ ((‖x‖ / 2) ^ 2)⁻¹ :=
                inv_anti₀ (by positivity)
                  (pow_le_pow_left₀ (by positivity) hfar 2)
              _ ≤ 16 / torusDistSq x := inv_half_sq_le hd
          have hmain :
              invSqKer (x - z) * invSqKer z ≤ gx z := by
            dsimp only [gx]
            rw [Set.indicator_of_mem hzx,
              invSqKer_sub_comm z x]
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right hker
              (invSqKer_nonneg (x - z))
          have hg₀nn : 0 ≤ g₀ z := by
            dsimp only [g₀]
            exact mul_nonneg (by positivity)
              (Set.indicator_nonneg
                (fun w _ => invSqKer_nonneg w) z)
          have ha₀nn : 0 ≤ a₀ z := by
            dsimp only [a₀]
            exact mul_nonneg (by norm_num)
              (Set.indicator_nonneg
                (fun w _ => sq_nonneg (invSqKer w)) z)
          have haxnn : 0 ≤ ax z := by
            dsimp only [ax]
            exact mul_nonneg (by norm_num)
              (Set.indicator_nonneg
                (fun w _ => sq_nonneg (invSqKer (w - x))) z)
          linarith
        · have hzA₀ : z ∈ A₀ := by
            change ‖x‖ / 2 ≤ ‖z‖
            exact le_of_not_ge hz₀
          have hzAx : z ∈ Ax := by
            change ‖x‖ / 2 ≤ ‖z - x‖
            exact le_of_not_ge hzx
          have hab :
              invSqKer (x - z) * invSqKer z ≤
                (1 / 2 : ℝ) * invSqKer z ^ 2 +
                  (1 / 2 : ℝ) * invSqKer (z - x) ^ 2 := by
            rw [invSqKer_sub_comm x z]
            nlinarith [sq_nonneg
              (invSqKer z - invSqKer (z - x))]
          have hfarTerms :
              a₀ z + ax z =
                (1 / 2 : ℝ) * invSqKer z ^ 2 +
                  (1 / 2 : ℝ) * invSqKer (z - x) ^ 2 := by
            dsimp only [a₀, ax]
            rw [Set.indicator_of_mem hzA₀,
              Set.indicator_of_mem hzAx]
          rw [← hfarTerms] at hab
          have hg₀nn : 0 ≤ g₀ z := by
            dsimp only [g₀]
            exact mul_nonneg (by positivity)
              (Set.indicator_nonneg
                (fun w _ => invSqKer_nonneg w) z)
          have hgxnn : 0 ≤ gx z := by
            dsimp only [gx]
            exact mul_nonneg (by positivity)
              (Set.indicator_nonneg
                (fun w _ => invSqKer_nonneg (w - x)) z)
          linarith
    have hraw :
        (∫ z, invSqKer (x - z) * invSqKer z
            ∂paperMeasure) ≤
          ∫ z, g₀ z + gx z + a₀ z + ax z
            ∂paperMeasure :=
      integral_mono
        (integrable_invSqKer_sub_mul_invSqKer_of_ne hx)
        hmajorant hpoint
    have hnear₀ :
        (∫ z, g₀ z ∂paperMeasure) ≤ 32 * vB := by
      dsimp only [g₀, S₀]
      rw [integral_const_mul]
      have hb :=
        indicator_ball_invSqKer_le (‖x‖ / 2) (by positivity)
      calc
        16 / torusDistSq x *
              ∫ z,
                ({z : T4 | ‖z‖ ≤ ‖x‖ / 2}.indicator
                  invSqKer) z ∂paperMeasure ≤
            16 / torusDistSq x *
              (8 * vB * (‖x‖ / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ 32 * vB := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hd]
          nlinarith [vB_pos, sq_norm_le_torusDistSq x]
    have hnearx :
        (∫ z, gx z ∂paperMeasure) ≤ 32 * vB := by
      dsimp only [gx, Sx]
      rw [integral_const_mul]
      have hb :=
        indicator_ball_shift_le (‖x‖ / 2) (by positivity) x
      calc
        16 / torusDistSq x *
              ∫ z,
                ({z : T4 | ‖z - x‖ ≤ ‖x‖ / 2}.indicator
                  fun w => invSqKer (w - x)) z ∂paperMeasure ≤
            16 / torusDistSq x *
              (8 * vB * (‖x‖ / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ 32 * vB := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hd]
          nlinarith [vB_pos, sq_norm_le_torusDistSq x]
    have hfar₀ :
        (∫ z, a₀ z ∂paperMeasure) ≤
          2 * vB *
            (Real.log 5 - Real.log (‖x‖ / 2)) := by
      dsimp only [a₀, A₀]
      rw [integral_const_mul]
      have h :=
        indicator_annulus_le ‖x‖ hr hr1
      linarith
    have hfarx :
        (∫ z, ax z ∂paperMeasure) ≤
          2 * vB *
            (Real.log 5 - Real.log (‖x‖ / 2)) := by
      let F : T4 → ℝ :=
        ({z : T4 | ‖x‖ / 2 ≤ ‖z‖}.indicator
          fun z => invSqKer z ^ 2)
      have hFmeas : Measurable F :=
        (measurable_invSqKer.pow_const 2).indicator
          (measurable_norm measurableSet_Ici)
      have hshift :
          (∫ z, F (z - x) ∂paperMeasure) =
            ∫ z, F z ∂paperMeasure := by
        exact integral_shift F hFmeas x
      have hbase :=
        indicator_annulus_le ‖x‖ hr hr1
      dsimp only [ax, Ax]
      rw [integral_const_mul]
      change
        (1 / 2 : ℝ) * (∫ z, F (z - x) ∂paperMeasure) ≤ _
      rw [hshift]
      dsimp only [F]
      linarith
    have hsum :
        (∫ z, g₀ z + gx z + a₀ z + ax z
            ∂paperMeasure) =
          (∫ z, g₀ z ∂paperMeasure) +
          (∫ z, gx z ∂paperMeasure) +
          (∫ z, a₀ z ∂paperMeasure) +
          (∫ z, ax z ∂paperMeasure) := by
      have h01 :
          (∫ z, g₀ z + gx z ∂paperMeasure) =
            (∫ z, g₀ z ∂paperMeasure) +
              ∫ z, gx z ∂paperMeasure :=
        integral_add hg₀ hgx
      have h012 :
          (∫ z, (g₀ z + gx z) + a₀ z ∂paperMeasure) =
            (∫ z, g₀ z + gx z ∂paperMeasure) +
              ∫ z, a₀ z ∂paperMeasure :=
        integral_add (hg₀.add hgx) ha₀
      have h0123 :
          (∫ z, ((g₀ z + gx z) + a₀ z) + ax z
              ∂paperMeasure) =
            (∫ z, (g₀ z + gx z) + a₀ z
              ∂paperMeasure) +
              ∫ z, ax z ∂paperMeasure :=
        integral_add ((hg₀.add hgx).add ha₀) hax
      calc
        (∫ z, g₀ z + gx z + a₀ z + ax z
            ∂paperMeasure) =
            (∫ z, ((g₀ z + gx z) + a₀ z) + ax z
              ∂paperMeasure) := rfl
        _ =
            (∫ z, (g₀ z + gx z) + a₀ z
              ∂paperMeasure) +
              ∫ z, ax z ∂paperMeasure := h0123
        _ =
            ((∫ z, g₀ z + gx z ∂paperMeasure) +
              ∫ z, a₀ z ∂paperMeasure) +
              ∫ z, ax z ∂paperMeasure := by
          rw [h012]
        _ =
            (∫ z, g₀ z ∂paperMeasure) +
            (∫ z, gx z ∂paperMeasure) +
            (∫ z, a₀ z ∂paperMeasure) +
            (∫ z, ax z ∂paperMeasure) := by
          rw [h01]
    have hlog2 : Real.log 2 ≤ 1 := by
      have h :=
        Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hlog5 : Real.log 5 ≤ 4 := by
      have h :=
        Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 5 by norm_num)
      linarith
    have hsplit :
        Real.log (‖x‖ / 2) =
          Real.log ‖x‖ - Real.log 2 :=
      Real.log_div hr.ne' (by norm_num)
    rw [hsum] at hraw
    have hlogNonneg : 0 ≤ |Real.log ‖x‖| := abs_nonneg _
    have hsmall :
        (∫ z, invSqKer (x - z) * invSqKer z
            ∂paperMeasure) ≤
          84 * vB * (1 + |Real.log ‖x‖|) := by
      rw [hsplit] at hfar₀ hfarx
      have habs := neg_le_abs (Real.log ‖x‖)
      nlinarith [vB_pos]
    exact hsmall.trans (by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C, B]
        nlinarith [vB_pos, I74_nonneg]
      · linarith)
  · have hnorm : 1 < ‖x‖ := lt_of_not_ge hr1
    have hquarter :
        powKer (1 / 4) x ≤ 1 := by
      unfold powKer
      have hd1 : 1 ≤ torusDistSq x := by
        have := sq_norm_le_torusDistSq x
        nlinarith
      exact
        (Real.rpow_le_rpow_of_exponent_le
          hd1 (by norm_num)).trans_eq
          (Real.rpow_zero _)
    have hcoarse := inner_bound hd
    have hbound :
        (∫ z, invSqKer (x - z) * invSqKer z
            ∂paperMeasure) ≤ B := by
      dsimp only [B]
      nlinarith [I74_nonneg]
    calc
      (∫ z, invSqKer (x - z) * invSqKer z
          ∂paperMeasure) ≤ B := hbound
      _ ≤ C * (1 + |Real.log ‖x‖|) := by
        have hfactor : 1 ≤ 1 + |Real.log ‖x‖| := by
          linarith [abs_nonneg (Real.log ‖x‖)]
        have hBC : B ≤ C := by
          dsimp only [C]
          nlinarith [vB_pos]
        exact hBC.trans
          (le_mul_of_one_le_right hC.le hfactor)

/-- **Triple convolution bound** (paper (5.3)–(5.4) machinery): the
threefold convolution of the model kernel `|·|⁻²` on `𝕋⁴` is uniformly
bounded — the exponent count `3·(−2) + 2·4 = 2 > 0` is strictly
subcritical, unlike the binary (log-critical) convolution. -/
theorem triple_conv_invSqKer_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : T4,
      (∫ z₁, (∫ z₂, invSqKer (x - z₁) * invSqKer (z₁ - z₂) * invSqKer z₂
        ∂paperMeasure) ∂paperMeasure) ≤ C := by
  refine ⟨64 * vB * I1 + 4 * I74 * I54 + 1, ?_, fun x => ?_⟩
  · have h1 := vB_pos
    have h2 := I1_nonneg
    have h3 := I74_nonneg
    have h4 := I54_nonneg
    positivity
  have hpull : ∀ z₁ : T4,
      (∫ z₂, invSqKer (x - z₁) * invSqKer (z₁ - z₂) * invSqKer z₂ ∂paperMeasure)
      = invSqKer (x - z₁) *
          ∫ z₂, invSqKer (z₁ - z₂) * invSqKer z₂ ∂paperMeasure := by
    intro z₁
    rw [← integral_const_mul]
    congr 1
    funext z₂
    ring
  have hshift1 : Integrable (fun z₁ : T4 => invSqKer (x - z₁)) paperMeasure := by
    rw [show (fun z₁ : T4 => invSqKer (x - z₁)) = fun z₁ => invSqKer (z₁ - x)
      from funext fun w => invSqKer_sub_comm x w]
    exact integrable_invSqKer_sub x
  have hshift54 : Integrable (fun z₁ : T4 => powKer (5/4) (x - z₁))
      paperMeasure := by
    rw [show (fun z₁ : T4 => powKer (5/4) (x - z₁))
      = fun z₁ => powKer (5/4) (z₁ - x) from funext fun w => powKer_sub_comm _ _ _]
    exact integrable_powKer_shift (by norm_num) (by norm_num) x
  have hi54 : Integrable (powKer (5/4)) paperMeasure :=
    integrable_powKer (by norm_num) (by norm_num)
  have hM : Integrable (fun z₁ => 64 * vB * invSqKer (x - z₁)
      + 2 * I74 * (powKer (5/4) (x - z₁) + powKer (5/4) z₁)) paperMeasure :=
    (hshift1.const_mul _).add ((hshift54.add hi54).const_mul _)
  have hae : ∀ᵐ z₁ ∂paperMeasure,
      (∫ z₂, invSqKer (x - z₁) * invSqKer (z₁ - z₂) * invSqKer z₂ ∂paperMeasure)
      ≤ 64 * vB * invSqKer (x - z₁)
        + 2 * I74 * (powKer (5/4) (x - z₁) + powKer (5/4) z₁) := by
    filter_upwards [ae_torusDistSq_pos] with z₁ hd
    rw [hpull z₁]
    calc invSqKer (x - z₁) *
          ∫ z₂, invSqKer (z₁ - z₂) * invSqKer z₂ ∂paperMeasure
        ≤ invSqKer (x - z₁) * (64 * vB + 2 * I74 * powKer (1/4) z₁) :=
          mul_le_mul_of_nonneg_left (inner_bound hd) (invSqKer_nonneg _)
      _ = 64 * vB * invSqKer (x - z₁)
          + 2 * I74 * (invSqKer (x - z₁) * powKer (1/4) z₁) := by ring
      _ ≤ 64 * vB * invSqKer (x - z₁)
          + 2 * I74 * (powKer (5/4) (x - z₁) + powKer (5/4) z₁) := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (outer_pointwise x z₁) ?_)
          linarith [I74_nonneg]
  have hnn : ∀ z₁ : T4, 0 ≤
      ∫ z₂, invSqKer (x - z₁) * invSqKer (z₁ - z₂) * invSqKer z₂ ∂paperMeasure :=
    fun z₁ => integral_nonneg fun z₂ =>
      mul_nonneg (mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _))
        (invSqKer_nonneg _)
  refine (integral_mono_of_nonneg (.of_forall hnn) hM hae).trans ?_
  have hMa : Integrable (fun z₁ : T4 => 64 * vB * invSqKer (x - z₁))
      paperMeasure := hshift1.const_mul _
  have hMb : Integrable (fun z₁ : T4 =>
      2 * I74 * (powKer (5/4) (x - z₁) + powKer (5/4) z₁)) paperMeasure :=
    (hshift54.add hi54).const_mul _
  rw [integral_add hMa hMb, integral_const_mul, integral_const_mul,
    integral_add hshift54 hi54]
  have hv1 : ∫ z₁, invSqKer (x - z₁) ∂paperMeasure = I1 := by
    rw [show (fun z₁ : T4 => invSqKer (x - z₁)) = fun z₁ => invSqKer (z₁ - x)
      from funext fun w => invSqKer_sub_comm x w]
    exact integral_shift invSqKer measurable_invSqKer x
  have hv2 : ∫ z₁, powKer (5/4) (x - z₁) ∂paperMeasure = I54 := by
    rw [show (fun z₁ : T4 => powKer (5/4) (x - z₁))
      = fun z₁ => powKer (5/4) (z₁ - x) from funext fun w => powKer_sub_comm _ _ _]
    exact integral_powKer_shift (5/4) x
  rw [hv1, hv2]
  show 64 * vB * I1 + 2 * I74 * (I54 + I54) ≤ 64 * vB * I1 + 4 * I74 * I54 + 1
  nlinarith [I74_nonneg, I54_nonneg]

/-! ## Stage 3: the regularized cubic singularity

The second summand in the primitive-kernel majorant is
`(torusDistSq z + ε²)⁻³`.  Its four-dimensional integral has the
subcritical scale `ε⁻²`.  The proof below keeps the dimensional scaling
explicit: transport to the fundamental cube, dominate by the corresponding
integral on `ℝ⁴`, and rescale.
-/

private def radialRegularizedCube (y : ℝ) : ℝ :=
  y ^ (3 : ℕ) * ((y ^ 2 + 1)⁻¹) ^ (3 : ℕ)

private lemma integrableOn_radialRegularizedCube :
    IntegrableOn radialRegularizedCube (Ioi (0 : ℝ)) volume := by
  have hc : Continuous radialRegularizedCube := by
    unfold radialRegularizedCube
    exact (by fun_prop : Continuous fun y : ℝ => y ^ (3 : ℕ)).mul
      ((Continuous.inv₀ (by fun_prop) fun y : ℝ => by positivity).pow 3)
  have hnear : IntegrableOn radialRegularizedCube (Ioc (0 : ℝ) 1) volume :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfarPow :
      IntegrableOn (fun y : ℝ => y ^ (-(3 : ℝ))) (Ioi (1 : ℝ)) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hfar : IntegrableOn radialRegularizedCube (Ioi (1 : ℝ)) volume := by
    refine Integrable.mono' hfarPow hc.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := zero_lt_one.trans hy
    have hbase : y ^ 2 ≤ y ^ 2 + 1 := by linarith
    have hp : y ^ (6 : ℕ) ≤ (y ^ 2 + 1) ^ (3 : ℕ) := by
      calc
        y ^ (6 : ℕ) = (y ^ 2) ^ (3 : ℕ) := by ring
        _ ≤ (y ^ 2 + 1) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (sq_nonneg y) hbase 3
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · rw [Real.rpow_neg hy0.le,
        show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      unfold radialRegularizedCube
      rw [inv_pow, ← div_eq_mul_inv, ← one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      rw [show y ^ 3 * y ^ 3 = y ^ 6 by ring]
      simpa using hp
    · unfold radialRegularizedCube
      positivity
  have hcover : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := by ext y; simp
  rw [hcover, integrableOn_union]
  exact ⟨hnear, hfar⟩

private def normRegularizedCube (x : R4) : ℝ :=
  ((‖x‖ ^ 2 + 1)⁻¹) ^ (3 : ℕ)

private lemma integrable_normRegularizedCube :
    Integrable normRegularizedCube (volume : Measure R4) := by
  have h := (integrable_fun_norm_addHaar (volume : Measure R4)
    (f := fun y : ℝ => ((y ^ 2 + 1)⁻¹) ^ (3 : ℕ))).2
      (by
        have hir := integrableOn_radialRegularizedCube
        unfold radialRegularizedCube at hir
        simpa [Module.finrank_pi, smul_eq_mul, inv_pow] using hir)
  unfold normRegularizedCube
  simpa only [Function.comp_apply] using h

private def cubeRegularized (x : R4) : ℝ :=
  ((∑ i, x i ^ 2) + 1)⁻¹ ^ (3 : ℕ)

private lemma cubeRegularized_nonneg (x : R4) :
    0 ≤ cubeRegularized x := by
  unfold cubeRegularized
  positivity

private lemma measurable_cubeRegularized : Measurable cubeRegularized := by
  unfold cubeRegularized
  fun_prop

private lemma cubeRegularized_le_normRegularizedCube (x : R4) :
    cubeRegularized x ≤ normRegularizedCube x := by
  unfold cubeRegularized normRegularizedCube
  refine pow_le_pow_left₀ (inv_nonneg.mpr ?_) (inv_anti₀ (by positivity) ?_) 3
  · positivity
  · linarith [sq_norm_le_sum x]

private lemma integrable_cubeRegularized :
    Integrable cubeRegularized (volume : Measure R4) := by
  refine Integrable.mono' integrable_normRegularizedCube
    measurable_cubeRegularized.aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (cubeRegularized_nonneg x)]
  exact cubeRegularized_le_normRegularizedCube x

/-- The cube-side regularized singularity at scale `ε`. -/
private def cubeRegularizedAt (ε : ℝ) (x : R4) : ℝ :=
  ((∑ i, x i ^ 2) + ε ^ 2)⁻¹ ^ (3 : ℕ)

private lemma cubeRegularizedAt_nonneg (ε : ℝ) (x : R4) :
    0 ≤ cubeRegularizedAt ε x := by
  unfold cubeRegularizedAt
  positivity

private lemma cubeRegularizedAt_eq (ε : ℝ) (hε : 0 < ε) (x : R4) :
    cubeRegularizedAt ε x =
      ε⁻¹ ^ (6 : ℕ) * cubeRegularized (ε⁻¹ • x) := by
  unfold cubeRegularizedAt cubeRegularized
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hsum :
      (∑ i, ε⁻¹ ^ 2 * x i ^ 2) = ε⁻¹ ^ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
  rw [hsum]
  simp only [inv_pow]
  field_simp [hε0]

private lemma integrable_cubeRegularizedAt (ε : ℝ) (hε : 0 < ε) :
    Integrable (cubeRegularizedAt ε) (volume : Measure R4) := by
  have hcomp : Integrable (fun x : R4 => cubeRegularized (ε⁻¹ • x)) volume :=
    integrable_cubeRegularized.comp_smul (inv_ne_zero (ne_of_gt hε))
  exact (hcomp.const_mul (ε⁻¹ ^ (6 : ℕ))).congr
    (.of_forall fun x => (cubeRegularizedAt_eq ε hε x).symm)

private lemma integral_cubeRegularizedAt (ε : ℝ) (hε : 0 < ε) :
    ∫ x : R4, cubeRegularizedAt ε x ∂volume =
      ε⁻¹ ^ (2 : ℕ) * ∫ x : R4, cubeRegularized x ∂volume := by
  rw [integral_congr_ae (.of_forall fun x => cubeRegularizedAt_eq ε hε x)]
  rw [integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg (volume : Measure R4)
    cubeRegularized hε.le]
  rw [Module.finrank_pi]
  simp only [Fintype.card_fin]
  field_simp [ne_of_gt hε]
  ring

/-- The regularized cubic singularity used in the primitive-kernel
majorant. -/
def regularizedInvCube (ε : ℝ) (z : T4) : ℝ :=
  (torusDistSq z + ε ^ 2)⁻¹ ^ (3 : ℕ)

lemma regularizedInvCube_nonneg (ε : ℝ) (z : T4) :
    0 ≤ regularizedInvCube ε z := by
  unfold regularizedInvCube
  exact pow_nonneg (inv_nonneg.mpr
    (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 3

lemma measurable_regularizedInvCube (ε : ℝ) :
    Measurable (regularizedInvCube ε) := by
  unfold regularizedInvCube
  exact (measurable_torusDistSq.add measurable_const).inv.pow_const 3

/-- The regularized cubic singularity is integrable at every positive
scale.  This is recorded separately from its quantitative bound so that
later integral algebra never relies on the Bochner integral's junk value. -/
theorem integrable_regularizedInvCube (ε : ℝ) (hε : 0 < ε) :
    Integrable (regularizedInvCube ε) paperMeasure := by
  have htransport := measurePreserving_mkT4.integrable_comp
    (measurable_regularizedInvCube ε).aestronglyMeasurable
  rw [← htransport]
  have hcube :
      (fun x => regularizedInvCube ε (mkT4 x)) =ᵐ[volume.restrict boxIoc]
        cubeRegularizedAt ε := by
    filter_upwards [ae_box] with x hx
    unfold regularizedInvCube cubeRegularizedAt
    rw [torusDistSq_mkT4 hx]
  exact (integrable_cubeRegularizedAt ε hε).restrict.congr hcube.symm

/-- **Regularized cubic integral bound** (the second term in the
R-3.22 primitive majorant): in four dimensions its integral is
`O(ε⁻²)`. -/
theorem integral_regularizedInvCube_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∫ z, regularizedInvCube ε z ∂paperMeasure ≤ C * ε⁻¹ ^ (2 : ℕ) := by
  let I : ℝ := ∫ x : R4, cubeRegularized x ∂volume
  have hInn : 0 ≤ I := integral_nonneg cubeRegularized_nonneg
  refine ⟨I + 1, by dsimp [I]; linarith, fun ε hε => ?_⟩
  rw [torus_integral_eq_cube
    (measurable_regularizedInvCube ε).aestronglyMeasurable]
  have hcube :
      (fun x => regularizedInvCube ε (mkT4 x)) =ᵐ[volume.restrict boxIoc]
        cubeRegularizedAt ε := by
    filter_upwards [ae_box] with x hx
    unfold regularizedInvCube cubeRegularizedAt
    rw [torusDistSq_mkT4 hx]
  rw [integral_congr_ae hcube]
  calc
    ∫ x in boxIoc, cubeRegularizedAt ε x ∂volume
        ≤ ∫ x, cubeRegularizedAt ε x ∂volume :=
      setIntegral_le_integral (integrable_cubeRegularizedAt ε hε)
        (.of_forall (cubeRegularizedAt_nonneg ε))
    _ = ε⁻¹ ^ (2 : ℕ) * I := integral_cubeRegularizedAt ε hε
    _ ≤ (I + 1) * ε⁻¹ ^ (2 : ℕ) := by
      have he : 0 ≤ ε⁻¹ ^ (2 : ℕ) := sq_nonneg _
      nlinarith
    _ = (I + 1) * ε⁻¹ ^ (2 : ℕ) := rfl

end

end Anderson4D
