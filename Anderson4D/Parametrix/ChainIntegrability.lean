import Anderson4D.Parametrix.L2KernelBridge
import Anderson4D.Continuum.GreenLiftIntegrability
import Anderson4D.Continuum.CellSingular

/-!
# Integrability of boundedly weighted Green paths

The parametrix and physical Neumann expansions repeatedly use a chain of
four-dimensional Green kernels with bounded vertex weights.  Pointwise
integrability at fixed endpoints is false on exceptional diagonals
(`G²` has the borderline singularity `|x|⁻⁴`).  The correct reusable
statement is joint integrability after the left endpoint and all path
vertices are integrated.  Fubini then supplies the required section
integrability almost everywhere.

This file proves that statement for an arbitrary finite family of
continuous vertex weights.  It is the analytic base for the a.e. Fubini
ledgers in Proposition 3.4 and for flattening the `L²` Neumann action.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The critical two-edge Green chain is integrable precisely away
from coincident fixed endpoints. -/
theorem integrable_greenFn_two_center_of_ne
    {x y : T4} (hxy : x ≠ y) :
    Integrable
      (fun z : T4 =>
        (greenFn (x - z) : ℂ) *
          (greenFn (z - y) : ℂ))
      paperMeasure := by
  obtain ⟨C, hC, hgreen⟩ := greenFn_le
  have hmajor :
      Integrable
        (fun z : T4 =>
          C ^ 2 *
            (invSqKer (x - z) *
              invSqKer (z - y)))
        paperMeasure :=
    (integrable_invSqKer_two_center_of_ne hxy).const_mul _
  refine Integrable.mono' hmajor ?_ ?_
  · exact Measurable.aestronglyMeasurable
      ((measurable_greenFn.comp
          (measurable_const.sub measurable_id)).complex_ofReal.mul
        (measurable_greenFn.comp
          (measurable_id.sub measurable_const)).complex_ofReal)
  · filter_upwards
      [compl_mem_ae_iff.mpr (paperMeasure_singleton x),
        compl_mem_ae_iff.mpr (paperMeasure_singleton y)] with
        z hzx hzy
    have hzx' : z ≠ x := by
      simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using hzx
    have hzy' : z ≠ y := by
      simpa only [Set.mem_compl_iff,
        Set.mem_singleton_iff] using hzy
    have hxdist : torusDistSq (x - z) ≠ 0 := by
      intro hzero
      exact hzx'
        (sub_eq_zero.mp
          ((torusDistSq_eq_zero_iff (x - z)).mp hzero)).symm
    have hydist : torusDistSq (z - y) ≠ 0 := by
      intro hzero
      exact hzy'
        (sub_eq_zero.mp
          ((torusDistSq_eq_zero_iff (z - y)).mp hzero))
    have hxgreen :
        greenFn (x - z) ≤
          C * invSqKer (x - z) := by
      simpa only [invSqKer, div_eq_mul_inv] using
        hgreen (x - z) hxdist
    have hygreen :
        greenFn (z - y) ≤
          C * invSqKer (z - y) := by
      simpa only [invSqKer, div_eq_mul_inv] using
        hgreen (z - y) hydist
    rw [norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs,
      abs_of_nonneg (greenFn_nonneg _),
      abs_of_nonneg (greenFn_nonneg _)]
    calc
      greenFn (x - z) * greenFn (z - y) ≤
          (C * invSqKer (x - z)) *
            (C * invSqKer (z - y)) := by
        exact mul_le_mul hxgreen hygreen
          (greenFn_nonneg _) (mul_nonneg hC.le
            (invSqKer_nonneg _))
      _ =
          C ^ 2 *
            (invSqKer (x - z) *
              invSqKer (z - y)) := by
        ring

/-- A recursively written Green path.  The `i`-th vertex contributes
`weight i`; there is one Green edge from the fixed left endpoint to the
first vertex and between every two successive vertices. -/
def weightedGreenPath :
    {n : ℕ} → (Fin n → C(T4, ℂ)) →
      T4 → (Fin n → T4) → ℂ
  | 0, _, _, _ => 1
  | n + 1, weight, x, v =>
      (greenFn (x - v 0) : ℂ) * weight 0 (v 0) *
        weightedGreenPath
          (fun i : Fin n => weight i.succ)
          (v 0) (Fin.tail v)

@[simp]
theorem weightedGreenPath_zero
    (weight : Fin 0 → C(T4, ℂ))
    (x : T4) (v : Fin 0 → T4) :
    weightedGreenPath weight x v = 1 :=
  rfl

@[simp]
theorem weightedGreenPath_succ
    {n : ℕ} (weight : Fin (n + 1) → C(T4, ℂ))
    (x : T4) (v : Fin (n + 1) → T4) :
    weightedGreenPath weight x v =
      (greenFn (x - v 0) : ℂ) * weight 0 (v 0) *
        weightedGreenPath
          (fun i : Fin n => weight i.succ)
          (v 0) (Fin.tail v) :=
  rfl

private def pathHeadTailEquiv
    (n : ℕ) :
    (Fin (n + 1) → T4) ≃ᵐ
      T4 × (Fin n → T4) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => T4) 0

@[simp]
private theorem pathHeadTailEquiv_symm_apply
    (n : ℕ) (z : T4) (v : Fin n → T4) :
    (pathHeadTailEquiv n).symm (z, v) =
      Fin.cons z v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pathHeadTailEquiv]
  · simp [pathHeadTailEquiv]

private def pathJointHeadTailEquiv
    (n : ℕ) :
    (T4 × (Fin (n + 1) → T4)) ≃ᵐ
      T4 × (T4 × (Fin n → T4)) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl T4)
    (pathHeadTailEquiv n)

private theorem measurePreserving_pathHeadTailEquiv
    (n : ℕ) :
    MeasurePreserving
      (pathHeadTailEquiv n)
      (Measure.pi fun _ : Fin (n + 1) =>
        paperMeasure)
      (paperMeasure.prod
        (Measure.pi fun _ : Fin n =>
          paperMeasure)) := by
  simpa only [pathHeadTailEquiv] using
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => paperMeasure)
      (0 : Fin (n + 1)))

private theorem measurePreserving_pathJointHeadTailEquiv
    (n : ℕ) :
    MeasurePreserving
      (pathJointHeadTailEquiv n)
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n =>
            paperMeasure))) := by
  let htail :=
    measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => paperMeasure)
      (0 : Fin (n + 1))
  let hprod :=
    (MeasurePreserving.id paperMeasure).prod htail
  exact hprod.congr
    (pathJointHeadTailEquiv n).measurable
    (Filter.Eventually.of_forall fun p => by
      rfl)

/-- Fubini after separating the first vertex of a finite path from all
remaining vertices.  The explicit integrability hypothesis is essential:
fixed-endpoint Green paths can fail to be integrable on exceptional
diagonals in four dimensions. -/
theorem integral_pathHeadTail
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (n : ℕ) (f : (Fin (n + 1) → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure)) :
    (∫ u : Fin (n + 1) → T4,
        f u ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ z : T4, ∫ v : Fin n → T4,
        f (Fin.cons z v)
        ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure := by
  let e := pathHeadTailEquiv n
  let μold :=
    Measure.pi fun _ : Fin (n + 1) =>
      paperMeasure
  let μtail :=
    Measure.pi fun _ : Fin n =>
      paperMeasure
  let μtarget := paperMeasure.prod μtail
  have hp : MeasurePreserving e μold μtarget := by
    simpa only [e, μold, μtarget, μtail] using
      measurePreserving_pathHeadTailEquiv n
  have hf' :
      Integrable (fun p => f (e.symm p))
        μtarget := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext u
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  calc
    (∫ u, f u ∂μold) =
        ∫ p, f (e.symm p) ∂μtarget := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp'
          (fun p => f (e.symm p))
    _ =
        ∫ z : T4, ∫ v : Fin n → T4,
          f (e.symm (z, v))
          ∂μtail ∂paperMeasure :=
      integral_prod _ hf'
    _ = _ := by
      simp_rw [e, pathHeadTailEquiv_symm_apply]
      rfl

private def pathLastInitEquiv
    (n : ℕ) :
    (Fin (n + 1) → T4) ≃ᵐ
      T4 × (Fin n → T4) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => T4) (Fin.last n)

@[simp]
private theorem pathLastInitEquiv_symm_apply
    (n : ℕ) (y : T4) (v : Fin n → T4) :
    (pathLastInitEquiv n).symm (y, v) =
      Fin.snoc v y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [pathLastInitEquiv]
  · simp [pathLastInitEquiv]

private theorem measurePreserving_pathLastInitEquiv
    (n : ℕ) :
    MeasurePreserving
      (pathLastInitEquiv n)
      (Measure.pi fun _ : Fin (n + 1) =>
        paperMeasure)
      (paperMeasure.prod
        (Measure.pi fun _ : Fin n =>
          paperMeasure)) := by
  simpa only [pathLastInitEquiv,
    Fin.succAbove_last] using
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => paperMeasure)
      (Fin.last n))

/-- Fubini after separating the terminal vertex from the preceding
vertices.  This is the product-measure order used by the physical
Neumann kernel: terminal point outside, internal chain variables inside. -/
theorem integral_pathLast
    {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (n : ℕ) (f : (Fin (n + 1) → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure)) :
    (∫ u : Fin (n + 1) → T4,
        f u ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ y : T4, ∫ v : Fin n → T4,
        f (Fin.snoc v y)
        ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure := by
  let e := pathLastInitEquiv n
  let μold :=
    Measure.pi fun _ : Fin (n + 1) =>
      paperMeasure
  let μinit :=
    Measure.pi fun _ : Fin n =>
      paperMeasure
  let μtarget := paperMeasure.prod μinit
  have hp : MeasurePreserving e μold μtarget := by
    simpa only [e, μold, μtarget, μinit] using
      measurePreserving_pathLastInitEquiv n
  have hf' :
      Integrable (fun p => f (e.symm p))
        μtarget := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext u
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  calc
    (∫ u, f u ∂μold) =
        ∫ p, f (e.symm p) ∂μtarget := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp'
          (fun p => f (e.symm p))
    _ =
        ∫ y : T4, ∫ v : Fin n → T4,
          f (e.symm (y, v))
          ∂μinit ∂paperMeasure :=
      integral_prod _ hf'
    _ = _ := by
      simp_rw [e, pathLastInitEquiv_symm_apply]
      rfl

/-- Joint integrability of every finite Green path with continuous vertex
weights.  In particular, Fubini gives integrability of the path variables
for almost every left endpoint. -/
theorem integrable_weightedGreenPath_joint
    {n : ℕ} (weight : Fin n → C(T4, ℂ)) :
    Integrable
      (fun p : T4 × (Fin n → T4) =>
        weightedGreenPath weight p.1 p.2)
      (paperMeasure.prod
        (Measure.pi fun _ : Fin n =>
          paperMeasure)) := by
  induction n with
  | zero =>
      simpa only [weightedGreenPath_zero] using
        (integrable_const (μ :=
          paperMeasure.prod
            (Measure.pi fun _ : Fin 0 =>
              paperMeasure)) (1 : ℂ))
  | succ n ih =>
      let tailWeight : Fin n → C(T4, ℂ) :=
        fun i => weight i.succ
      let μtail :=
        Measure.pi fun _ : Fin n => paperMeasure
      let Y := T4 × (Fin n → T4)
      let ν : Measure Y := paperMeasure.prod μtail
      let tail : Y → ℂ :=
        fun p =>
          weightedGreenPath tailWeight p.1 p.2
      have htail : Integrable tail ν := by
        simpa only [tail, ν, Y, μtail, tailWeight] using
          ih tailWeight
      let weightedTail : Y → ℂ :=
        fun p => weight 0 p.1 * tail p
      have hweightMeas :
          AEStronglyMeasurable
            (fun p : Y => weight 0 p.1) ν :=
        Measurable.aestronglyMeasurable
          ((weight 0).continuous.measurable.comp measurable_fst)
      have hweightBound :
          ∀ᵐ p : Y ∂ν,
            ‖weight 0 p.1‖ ≤ ‖weight 0‖ :=
        Filter.Eventually.of_forall fun p =>
          ContinuousMap.norm_coe_le_norm (weight 0) p.1
      have hweightedTail :
          Integrable weightedTail ν := by
        exact htail.bdd_mul hweightMeas hweightBound
      let target : T4 × Y → ℂ :=
        fun p =>
          (greenFn (p.1 - p.2.1) : ℂ) *
            weightedTail p.2
      have htarget :
          Integrable target (paperMeasure.prod ν) := by
        exact integrable_greenFn_sub_mul_lift
          weightedTail Prod.fst hweightedTail measurable_fst
      let e := pathJointHeadTailEquiv n
      have hp :=
        measurePreserving_pathJointHeadTailEquiv n
      have hcomp :
          Integrable (target ∘ e)
            (paperMeasure.prod
              (Measure.pi fun _ : Fin (n + 1) =>
                paperMeasure)) := by
        exact
          (hp.integrable_comp_emb e.measurableEmbedding).mpr
            (by simpa only [target, ν, Y, μtail] using htarget)
      convert hcomp using 1
      funext p
      rcases p with ⟨x, v⟩
      change
        weightedGreenPath weight x v =
          target (e (x, v))
      have hev :
          e (x, v) =
            (x, (v 0, Fin.tail v)) := by
        have htail :
            pathHeadTailEquiv n v =
              (v 0, Fin.tail v) := by
          apply (pathHeadTailEquiv n).symm.injective
          calc
            (pathHeadTailEquiv n).symm
                (pathHeadTailEquiv n v) =
              v :=
                MeasurableEquiv.symm_apply_apply
                  (pathHeadTailEquiv n) v
            _ = Fin.cons (v 0) (Fin.tail v) :=
              (Fin.cons_self_tail v).symm
            _ =
                (pathHeadTailEquiv n).symm
                  (v 0, Fin.tail v) :=
              (pathHeadTailEquiv_symm_apply
                n (v 0) (Fin.tail v)).symm
        apply Prod.ext
        · rfl
        · exact htail
      rw [hev]
      simp only [weightedGreenPath_succ, target,
        weightedTail, tail, tailWeight]
      ring

/-- The section form used by Fubini: all path variables are integrable
for almost every value of the left endpoint. -/
theorem ae_integrable_weightedGreenPath
    {n : ℕ} (weight : Fin n → C(T4, ℂ)) :
    ∀ᵐ x ∂paperMeasure,
      Integrable
        (weightedGreenPath weight x)
        (Measure.pi fun _ : Fin n =>
          paperMeasure) :=
  (integrable_weightedGreenPath_joint weight).prod_right_ae

end

end Anderson4D
