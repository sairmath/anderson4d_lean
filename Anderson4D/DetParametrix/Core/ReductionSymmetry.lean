import Anderson4D.Continuum.GreenBounds
import Anderson4D.Continuum.SingularChain

/-!
# Symmetry and local analytic interfaces for the reduction in paper §4.1

This file isolates the analytic mechanisms used in (4.8)--(4.12).

* `coordinateFlipT4` preserves the paper measure.
* If `J ∈ 𝓔`, every coordinate of its first moment (using the canonical
  torus lift) vanishes.  The boundary ambiguity of the lift at `-π` is
  handled as an almost-everywhere statement, not silently ignored.
* `quadratic_remainder_of_lipschitz_fderiv` supplies a reusable,
  genuinely differentiable version of the second-order Taylor estimate
  in (4.9).
* `taylor_cancellation_bound` removes the linear term and retains only
  the quadratic majorant.
* The three measurable regions from (4.10)--(4.12) are bounded by the
  already-proved three-kernel convolution estimate.  Product
  integrability is explicit, so no result relies on Lean's junk value
  for a non-integrable Bochner integral.

The remaining `ε`/`|log ε|` radial bookkeeping for the primitive kernel
belongs to the final R-322 assembly, not to these interfaces.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory Set

/-! ## Coordinate flips and odd first moments -/

/-- Flip one coordinate of the four-dimensional torus. -/
def coordinateFlipT4 (i : Fin dim) (x : T4) : T4 :=
  Function.update x i (-(x i))

/-- The coordinate flip, bundled as a measurable involution. -/
def coordinateFlipMeasurableEquiv (i : Fin dim) : T4 ≃ᵐ T4 where
  toEquiv := Function.Involutive.toPerm (coordinateFlipT4 i) fun x => by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [coordinateFlipT4]
    · simp [coordinateFlipT4, Function.update_of_ne hj]
  measurable_toFun := by
    change Measurable (coordinateFlipT4 i)
    unfold coordinateFlipT4
    fun_prop
  measurable_invFun := by
    change Measurable (coordinateFlipT4 i)
    unfold coordinateFlipT4
    fun_prop

@[simp]
lemma coordinateFlipMeasurableEquiv_apply (i : Fin dim) (x : T4) :
    coordinateFlipMeasurableEquiv i x = coordinateFlipT4 i x := rfl

/-- A single-coordinate sign flip preserves the paper's Lebesgue
normalization on `𝕋⁴`. -/
theorem measurePreserving_coordinateFlipT4 (i : Fin dim) :
    MeasurePreserving (coordinateFlipMeasurableEquiv i) paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  have hpi : MeasurePreserving
      (fun x : T4 => fun j => if j = i then -(x j) else x j)
      (volume : Measure T4) (volume : Measure T4) := by
    refine measurePreserving_pi
      (fun _ : Fin dim => (volume : Measure (AddCircle (2 * Real.pi))))
      (fun _ : Fin dim => (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun j x => if j = i then -x else x) fun j => ?_
    by_cases hji : j = i
    · subst j
      simp only [if_pos]
      exact Measure.measurePreserving_neg _
    · simp only [if_neg hji]
      exact MeasurePreserving.id _
  change MeasurePreserving (coordinateFlipT4 i)
    (volume : Measure T4) (volume : Measure T4)
  have hfun : coordinateFlipT4 i =
      fun x : T4 => fun j => if j = i then -(x j) else x j := by
    funext x j
    by_cases hji : j = i
    · subst j
      simp [coordinateFlipT4]
    · rw [coordinateFlipT4, Function.update_of_ne hji]
      simp [hji]
  rw [hfun]
  exact hpi

private lemma coe_torusLift_reduction (x : T4) (i : Fin dim) :
    ((torusLift x i : ℝ) : AddCircle (2 * Real.pi)) = x i :=
  AddCircle.coe_equivIco

private lemma equivIco_neg_reduction {w : AddCircle (2 * Real.pi)}
    (h : ((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) w : ℝ) ≠ -Real.pi) :
    ((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) (-w) : ℝ) =
      -((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) w : ℝ) := by
  set a := ((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) w : ℝ)
  have hmem : a ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) :=
    ((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) w).2
  have hw : ((a : ℝ) : AddCircle (2 * Real.pi)) = w :=
    AddCircle.coe_equivIco
  have hneg : -w = ((-a : ℝ) : AddCircle (2 * Real.pi)) := by
    rw [AddCircle.coe_neg, hw]
  rw [hneg]
  have hlt : -Real.pi < a := lt_of_le_of_ne hmem.1 (Ne.symm h)
  have hneg_mem : -a ∈ Ico (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    constructor
    · have := hmem.2
      linarith
    · linarith
  exact AddCircle.equivIco_coe_of_mem hneg_mem

private lemma volume_singleton_addCircle_reduction
    (a : AddCircle (2 * Real.pi)) :
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
      exact ⟨k, by
        show x₀ + k • (2 * Real.pi) = y
        linarith [hk]⟩
    exact (Set.countable_range _).mono hsub
  rw [Measure.restrict_apply
    (AddCircle.measurable_mk' (measurableSet_singleton _))]
  exact measure_mono_null Set.inter_subset_left (hcount.measure_zero volume)

private lemma boundary_preimage_null (i : Fin dim) :
    paperMeasure {x : T4 |
      x i = ((-Real.pi : ℝ) : AddCircle (2 * Real.pi))} = 0 := by
  rw [paperMeasure_eq_volume, volume_pi]
  exact Measure.pi_eval_preimage_null
    (i := i)
    (fun _ : Fin dim => (volume : Measure (AddCircle (2 * Real.pi))))
    (volume_singleton_addCircle_reduction
      ((-Real.pi : ℝ) : AddCircle (2 * Real.pi)))

/-- The canonical lift is odd under a coordinate flip away from the
measure-zero boundary of the half-open fundamental domain. -/
theorem ae_torusLift_coordinateFlip (i : Fin dim) :
    ∀ᵐ x ∂paperMeasure,
      torusLift (coordinateFlipT4 i x) i = -(torusLift x i) := by
  filter_upwards [compl_mem_ae_iff.mpr (boundary_preimage_null i)] with x hx
  have hboundary : torusLift x i ≠ -Real.pi := by
    intro h
    apply hx
    change x i = ((-Real.pi : ℝ) : AddCircle (2 * Real.pi))
    rw [← coe_torusLift_reduction x i, h]
  change
    ((AddCircle.equivIco (2 * Real.pi) (-Real.pi))
      (Function.update x i (-(x i)) i) : ℝ) = _
  rw [Function.update_self]
  exact equivIco_neg_reduction hboundary

/-- The `i`-th first moment of an `𝓔`-symmetric kernel vanishes.

The integrability hypothesis is deliberate: without it, the Bochner
integral is junk-totalized to zero and the statement would not certify
the analytic cancellation used in (4.9). -/
theorem eClass_coordinate_moment_eq_zero {J : T4 → ℝ}
    (hJ : MemEClassT4 J) (i : Fin dim)
    (_hint : Integrable (fun u => J u * torusLift u i) paperMeasure) :
    ∫ u, J u * torusLift u i ∂paperMeasure = 0 := by
  let F : T4 → ℝ := fun u => J u * torusLift u i
  have hchange :
      (∫ u, F (coordinateFlipMeasurableEquiv i u) ∂paperMeasure) =
        ∫ u, F u ∂paperMeasure :=
    (measurePreserving_coordinateFlipT4 i).integral_comp' F
  have hodd : ∀ᵐ u ∂paperMeasure,
      F (coordinateFlipMeasurableEquiv i u) = -F u := by
    filter_upwards [ae_torusLift_coordinateFlip i] with u hu
    change J (coordinateFlipT4 i u) *
        torusLift (coordinateFlipT4 i u) i = -(J u * torusLift u i)
    rw [show coordinateFlipT4 i u =
      Function.update u i (-(u i)) from rfl, hJ.even_coord i u]
    have hu' : torusLift (Function.update u i (-(u i))) i =
        -(torusLift u i) := by
      simpa only [coordinateFlipT4] using hu
    rw [hu']
    ring
  have hneg :
      (∫ u, F (coordinateFlipMeasurableEquiv i u) ∂paperMeasure) =
        -(∫ u, F u ∂paperMeasure) := by
    calc
      (∫ u, F (coordinateFlipMeasurableEquiv i u) ∂paperMeasure)
          = ∫ u, -F u ∂paperMeasure := integral_congr_ae hodd
      _ = -(∫ u, F u ∂paperMeasure) := integral_neg F
  linarith

/-- The linear form in (4.9), evaluated on the canonical lift. -/
def torusLinearTerm (D : R4 →L[ℝ] ℝ) (u : T4) : ℝ :=
  D (torusLift u)

private lemma torusLinearTerm_eq_sum (D : R4 →L[ℝ] ℝ) (u : T4) :
    torusLinearTerm D u =
      ∑ i : Fin dim, torusLift u i * D (Pi.single i 1) := by
  classical
  have hlift : torusLift u =
      ∑ i : Fin dim, (torusLift u i) • Pi.single i (1 : ℝ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · simp
  calc
    torusLinearTerm D u = D (torusLift u) := rfl
    _ = D (∑ i : Fin dim, (torusLift u i) • Pi.single i (1 : ℝ)) := by
      exact congrArg D hlift
    _ = ∑ i : Fin dim, D ((torusLift u i) • Pi.single i (1 : ℝ)) := by
      exact map_sum D (fun i : Fin dim =>
        (torusLift u i) • Pi.single i (1 : ℝ)) Finset.univ
    _ = ∑ i : Fin dim, torusLift u i * D (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp [smul_eq_mul]

/-- Every linear first moment of an `𝓔`-symmetric kernel vanishes. -/
theorem eClass_linear_moment_eq_zero {J : T4 → ℝ}
    (hJ : MemEClassT4 J) (D : R4 →L[ℝ] ℝ)
    (hint : ∀ i : Fin dim,
      Integrable (fun u => J u * torusLift u i) paperMeasure) :
    ∫ u, J u * torusLinearTerm D u ∂paperMeasure = 0 := by
  have hfun : (fun u => J u * torusLinearTerm D u) =
      fun u => ∑ i : Fin dim,
        D (Pi.single i 1) * (J u * torusLift u i) := by
    funext u
    rw [torusLinearTerm_eq_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul,
      eClass_coordinate_moment_eq_zero hJ i (hint i), mul_zero]
  · intro i _
    exact (hint i).const_mul _

/-! ## A genuine second-order Taylor interface -/

/-- A Lipschitz bound on the Fréchet derivative along a segment gives
the quadratic Taylor remainder needed in (4.9). -/
theorem quadratic_remainder_of_lipschitz_fderiv
    {f : R4 → ℝ} {df : R4 → R4 →L[ℝ] ℝ} {a b : R4} {M : ℝ}
    (hM : 0 ≤ M)
    (hderiv : ∀ x ∈ segment ℝ a b,
      HasFDerivWithinAt f (df x) (segment ℝ a b) x)
    (hLip : ∀ x ∈ segment ℝ a b,
      ‖df x - df a‖ ≤ M * ‖x - a‖) :
    |f b - f a - df a (b - a)| ≤ M * ‖b - a‖ ^ 2 := by
  have hbound : ∀ x ∈ segment ℝ a b,
      ‖df x - df a‖ ≤ (M * ‖b - a‖) := by
    intro x hx
    calc
      ‖df x - df a‖ ≤ M * ‖x - a‖ := hLip x hx
      _ ≤ M * ‖b - a‖ := by
        gcongr
        exact norm_sub_le_of_mem_segment hx
  have hmv :=
    (convex_segment a b).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      hderiv hbound (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  rw [Real.norm_eq_abs] at hmv
  calc
    |f b - f a - df a (b - a)| ≤ (M * ‖b - a‖) * ‖b - a‖ := hmv
    _ = M * ‖b - a‖ ^ 2 := by ring

/-- Integrated Taylor cancellation: if `δ` is a linear term plus a
quadratic remainder, `𝓔`-symmetry removes the linear contribution and
the integral is controlled only by the quadratic majorant. -/
theorem taylor_cancellation_bound
    {J δ remainder : T4 → ℝ} (hJ : MemEClassT4 J)
    (D : R4 →L[ℝ] ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hmoment : ∀ i : Fin dim,
      Integrable (fun u => J u * torusLift u i) paperMeasure)
    (hexpand : ∀ u, δ u = -torusLinearTerm D u + remainder u)
    (hremainder : ∀ u, |remainder u| ≤ C * torusDistSq u)
    (hintR : Integrable (fun u => J u * remainder u) paperMeasure)
    (hintMajorant :
      Integrable (fun u => |J u| * (C * torusDistSq u)) paperMeasure) :
    |∫ u, J u * δ u ∂paperMeasure| ≤
      ∫ u, |J u| * (C * torusDistSq u) ∂paperMeasure := by
  have hintLinear :
      Integrable (fun u => J u * torusLinearTerm D u) paperMeasure := by
    rw [show (fun u => J u * torusLinearTerm D u) =
      fun u => ∑ i : Fin dim,
        D (Pi.single i 1) * (J u * torusLift u i) by
          funext u
          rw [torusLinearTerm_eq_sum]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring]
    exact integrable_finsetSum _ fun i _ => (hmoment i).const_mul _
  have hintegral :
      (∫ u, J u * δ u ∂paperMeasure) =
        ∫ u, J u * remainder u ∂paperMeasure := by
    calc
      (∫ u, J u * δ u ∂paperMeasure)
          = ∫ u, (-(J u * torusLinearTerm D u) +
              J u * remainder u) ∂paperMeasure := by
              apply integral_congr_ae
              filter_upwards with u
              rw [hexpand]
              ring
      _ = -(∫ u, J u * torusLinearTerm D u ∂paperMeasure) +
            ∫ u, J u * remainder u ∂paperMeasure := by
              calc
                (∫ u, (-(J u * torusLinearTerm D u) +
                    J u * remainder u) ∂paperMeasure)
                    = (∫ u, -(J u * torusLinearTerm D u) ∂paperMeasure) +
                        ∫ u, J u * remainder u ∂paperMeasure := by
                          exact integral_add hintLinear.neg hintR
                _ = -(∫ u, J u * torusLinearTerm D u ∂paperMeasure) +
                      ∫ u, J u * remainder u ∂paperMeasure := by
                        rw [integral_neg]
      _ = ∫ u, J u * remainder u ∂paperMeasure := by
              rw [eClass_linear_moment_eq_zero hJ D hmoment]
              simp
  rw [hintegral]
  calc
    |∫ u, J u * remainder u ∂paperMeasure|
        ≤ ∫ u, |J u * remainder u| ∂paperMeasure := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm
              (μ := paperMeasure) (fun u => J u * remainder u))
    _ ≤ ∫ u, |J u| * (C * torusDistSq u) ∂paperMeasure := by
      refine integral_mono_of_nonneg
        (.of_forall fun u => abs_nonneg (J u * remainder u))
        hintMajorant (.of_forall fun u => ?_)
      change |J u * remainder u| ≤ |J u| * (C * torusDistSq u)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hremainder u) (abs_nonneg _)

/-! ## Three local regions from (4.10)--(4.12) -/

/-- The nonnegative three-kernel majorant after translating `y` to the
origin.  The pair is `(z,w)`. -/
def reductionTripleKernel (x : T4) (p : T4 × T4) : ℝ :=
  invSqKer (x - p.1) * invSqKer (p.1 - p.2) * invSqKer p.2

theorem reductionTripleKernel_nonneg (x : T4) (p : T4 × T4) :
    0 ≤ reductionTripleKernel x p :=
  mul_nonneg
    (mul_nonneg (invSqKer_nonneg _) (invSqKer_nonneg _))
    (invSqKer_nonneg _)

/-- Case (4.10): the increment `z-w` is small compared with `z-y`
(with `y` translated to zero). -/
def reductionRegion₁ : Set (T4 × T4) :=
  {p | 2 * ‖p.1 - p.2‖ ≤ ‖p.1‖}

/-- Case (4.11): `z-y` is no larger than the increment and
`z-w` is comparable with `w-y`. -/
def reductionRegion₂ : Set (T4 × T4) :=
  {p | ‖p.1‖ ≤ 2 * ‖p.1 - p.2‖ ∧
    ‖p.1 - p.2‖ ≤ 2 * ‖p.2‖ ∧ ‖p.2‖ ≤ 2 * ‖p.1 - p.2‖}

/-- Case (4.12): `w-y` is no larger than the increment and
`z-w` is comparable with `z-y`. -/
def reductionRegion₃ : Set (T4 × T4) :=
  {p | ‖p.2‖ ≤ 2 * ‖p.1 - p.2‖ ∧
    ‖p.1 - p.2‖ ≤ 2 * ‖p.1‖ ∧ ‖p.1‖ ≤ 2 * ‖p.1 - p.2‖}

theorem measurableSet_reductionRegion₁ : MeasurableSet reductionRegion₁ := by
  unfold reductionRegion₁
  have hsub : Measurable (fun p : T4 × T4 => ‖p.1 - p.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  have hfst : Measurable (fun p : T4 × T4 => ‖p.1‖) :=
    measurable_fst.norm
  exact measurableSet_le
    (measurable_const.mul hsub) hfst

theorem measurableSet_reductionRegion₂ : MeasurableSet reductionRegion₂ := by
  unfold reductionRegion₂
  have hsub : Measurable (fun p : T4 × T4 => ‖p.1 - p.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  have hfst : Measurable (fun p : T4 × T4 => ‖p.1‖) :=
    measurable_fst.norm
  have hsnd : Measurable (fun p : T4 × T4 => ‖p.2‖) :=
    measurable_snd.norm
  exact (measurableSet_le hfst (measurable_const.mul hsub)).inter
    ((measurableSet_le hsub (measurable_const.mul hsnd)).inter
      (measurableSet_le hsnd (measurable_const.mul hsub)))

theorem measurableSet_reductionRegion₃ : MeasurableSet reductionRegion₃ := by
  unfold reductionRegion₃
  have hsub : Measurable (fun p : T4 × T4 => ‖p.1 - p.2‖) :=
    (measurable_fst.sub measurable_snd).norm
  have hfst : Measurable (fun p : T4 × T4 => ‖p.1‖) :=
    measurable_fst.norm
  have hsnd : Measurable (fun p : T4 × T4 => ‖p.2‖) :=
    measurable_snd.norm
  exact (measurableSet_le hsnd (measurable_const.mul hsub)).inter
    ((measurableSet_le hsub (measurable_const.mul hfst)).inter
      (measurableSet_le hfst (measurable_const.mul hsub)))

private theorem local_reduction_integral_le {S : Set (T4 × T4)} (x : T4)
    (hint : Integrable (reductionTripleKernel x)
      (paperMeasure.prod paperMeasure)) :
    ∫ p in S, reductionTripleKernel x p ∂(paperMeasure.prod paperMeasure) ≤
      ∫ p, reductionTripleKernel x p ∂(paperMeasure.prod paperMeasure) := by
  exact setIntegral_le_integral hint
    (.of_forall (reductionTripleKernel_nonneg x))

/-- The three local integrals corresponding to (4.10)--(4.12) are
uniformly bounded by the same absolute constant as the unrestricted
threefold singular convolution.

The joint `Integrable` premise is exposed because it is precisely what
licenses Fubini and prevents a junk-totalized integral.  In the R-322
assembly it is discharged by the primitive-kernel radial bounds. -/
theorem reduction_three_local_integrals_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : T4,
      Integrable (reductionTripleKernel x) (paperMeasure.prod paperMeasure) →
      (∫ p in reductionRegion₁, reductionTripleKernel x p
          ∂(paperMeasure.prod paperMeasure) ≤ C) ∧
      (∫ p in reductionRegion₂, reductionTripleKernel x p
          ∂(paperMeasure.prod paperMeasure) ≤ C) ∧
      (∫ p in reductionRegion₃, reductionTripleKernel x p
          ∂(paperMeasure.prod paperMeasure) ≤ C) := by
  obtain ⟨C, hC, hfull⟩ := triple_conv_invSqKer_le
  refine ⟨C, hC, fun x hint => ?_⟩
  have hproduct :
      (∫ p, reductionTripleKernel x p ∂(paperMeasure.prod paperMeasure)) ≤ C := by
    rw [integral_prod _ hint]
    exact hfull x
  exact ⟨
    (local_reduction_integral_le x hint).trans hproduct,
    (local_reduction_integral_le x hint).trans hproduct,
    (local_reduction_integral_le x hint).trans hproduct⟩

end

end Anderson4D
