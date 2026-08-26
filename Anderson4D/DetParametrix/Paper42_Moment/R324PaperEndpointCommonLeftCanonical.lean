import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointCommonLeftFourier
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightRouteExactAllCases
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Canonical route packages for the common-left Fourier move

Paper: R-324 — §4.2 Step 4(B), canonical common-left route package

This file contains only the route-independent seams needed after the four
literal endpoint operations have finished.  It retains evaluation linearity
on the right package, exposes the exact common-translation character carried
by the completed left half, and identifies translation of the terminal cross
coefficient with translation of its doubled residual root.

No norm or estimate is taken here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {alpha beta : Z4}
    {p : R324RefinedScheduleIndex m}
    {e0 : MomentContraction m}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.1 alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) e0.2.1 (-alpha)}
    {leftRoute : R324PaperHalfEndpointRoute leftProviders}
    {rightRoute : R324PaperHalfEndpointRoute rightProviders}

/-! ## The common-left projection on the extra Haar parameter -/

/-- Joint measurability of the map which translates the whole left terminal
tuple and then forgets the translation parameter. -/
theorem measurable_r324CommonLeftProjection
    (I J : Type*) [Fintype I] [Fintype J] :
    Measurable
      (fun q : T4 × ((I → T4) × (J → T4)) =>
        (r324CommonTranslate q.1 q.2.1, q.2.2)) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact
      ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd)).add measurable_fst
  · exact measurable_snd.comp measurable_snd

/-- At a fixed common-left parameter, translation of the left tuple and the
identity on the right tuple form a measurable equivalence of the completed
terminal carrier. -/
def r324CommonLeftProjectionSectionMeasurableEquiv
    (I J : Type*) [Fintype I] (a : T4) :
    ((I → T4) × (J → T4)) ≃ᵐ ((I → T4) × (J → T4)) :=
  MeasurableEquiv.prodCongr
    (r324CommonTranslateMeasurableEquiv I a)
    (MeasurableEquiv.refl (J → T4))

@[simp]
theorem r324CommonLeftProjectionSectionMeasurableEquiv_apply
    (I J : Type*) [Fintype I] (a : T4)
    (p : (I → T4) × (J → T4)) :
    r324CommonLeftProjectionSectionMeasurableEquiv I J a p =
      (r324CommonTranslate a p.1, p.2) := by
  rfl

/-- Every fixed common-left section preserves the product Haar measure.
The outer Haar variable is deliberately handled by Tonelli below: since the
paper measure is not normalized, forgetting it is not measure-preserving. -/
theorem measurePreserving_r324CommonLeftProjectionSection
    (I J : Type*) [Fintype I] [Fintype J] (a : T4) :
    MeasurePreserving
      (r324CommonLeftProjectionSectionMeasurableEquiv I J a)
      ((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure))
      ((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure)) := by
  exact
    (measurePreserving_r324CommonTranslate I a).prod
      (MeasurePreserving.id
        (Measure.pi fun _ : J => paperMeasure))

/-- The joint projection is nonsingular.  This is the precise replacement
for the false measure-preserving claim one would get by forgetting the
finite-mass outer Haar variable: null sets pull back to null sets because
every fixed common-left section preserves terminal product Haar. -/
theorem quasiMeasurePreserving_r324CommonLeftProjection
    (I J : Type*) [Fintype I] [Fintype J] :
    Measure.QuasiMeasurePreserving
      (fun q : T4 × ((I → T4) × (J → T4)) ↦
        (r324CommonTranslate q.1 q.2.1, q.2.2))
      (paperMeasure.prod
        ((Measure.pi fun _ : I ↦ paperMeasure).prod
          (Measure.pi fun _ : J ↦ paperMeasure)))
      ((Measure.pi fun _ : I ↦ paperMeasure).prod
        (Measure.pi fun _ : J ↦ paperMeasure)) := by
  let terminalMeasure :=
    (Measure.pi fun _ : I ↦ paperMeasure).prod
      (Measure.pi fun _ : J ↦ paperMeasure)
  let projection : T4 × ((I → T4) × (J → T4)) →
      (I → T4) × (J → T4) :=
    fun q ↦ (r324CommonTranslate q.1 q.2.1, q.2.2)
  have hprojection : Measurable projection :=
    measurable_r324CommonLeftProjection I J
  refine ⟨hprojection, Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_⟩
  rw [Measure.map_apply hprojection hs]
  apply Measure.measure_prod_null_of_ae_null (hprojection hs)
  filter_upwards with a
  have hsection := measurePreserving_r324CommonLeftProjectionSection I J a
  calc
    terminalMeasure ((fun p ↦ projection (a, p)) ⁻¹' s) =
        (Measure.map
          (r324CommonLeftProjectionSectionMeasurableEquiv I J a)
          terminalMeasure) s := by
      rw [Measure.map_apply hsection.measurable hs]
      rfl
    _ = terminalMeasure s := by rw [hsection.map_eq]
    _ = 0 := hs0

namespace R324PaperRightRouteExactPackage

/-- The completed right route already contains exactly the two evaluation
laws required by the common-left coefficient factorization. -/
def toLinear
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactPackage left rightRoute) :
    R324PaperRightRouteExactLinearPackage left rightRoute where
  package := right
  densityEvaluationLinear := {
    mul := right.density_mul
    congr_at := right.density_congr_at }

/-- Literal four-case producer for the right linear package. -/
theorem exists_linear_of_route
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (hsingles : e0.2.1.singles.Nonempty)
    (route : R324PaperHalfEndpointRoute rightProviders) :
    Nonempty (R324PaperRightRouteExactLinearPackage left route) :=
  (exists_of_route left hsingles route).map (toLinear left)

end R324PaperRightRouteExactPackage

namespace R324PaperLeftRouteExactPackage

/-- The common-translation covariance stored by every completed left route,
in the exact form consumed by the abstract Haar-averaging theorem. -/
theorem unitDensity_commonTranslate
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (a : T4)
    (v : left.bound.carrier.SurvivingCoordinate → T4) :
    left.bound.density (fun _ => 1) beta (r324CommonTranslate a v) =
      charT4 (alpha + beta) a *
        left.bound.density (fun _ => 1) beta v := by
  exact left.unit_commonTranslate a v

/-- Translating every surviving coordinate of the completed left carrier
is exactly translation of the left half of the doubled residual root.  The
primitive sum is compared only on `momentResidualActive`, its genuine
support. -/
theorem crossCoefficient_commonTranslate_eq_leftInternalTranslate
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactLinearPackage left rightRoute)
    (leftPost : left.bound.carrier.SurvivingCoordinate → T4)
    (rightPost : right.package.bound.carrier.SurvivingCoordinate → T4)
    (a : T4) :
    left.bound.crossCoefficient right.package.bound e0.2.2
        (r324CommonTranslate a leftPost) rightPost =
      (r324ResidualPrimitiveSumProduct rho eps e0.1 e0.2.1 e0.2.2
        (r324LeftInternalTranslateMeasurableEquiv m a
          (r324TwoHalfRootDoubledReconstruct
            left.bound.carrier right.package.bound.carrier
            (leftPost, rightPost))) : Complex) := by
  unfold R324PaperHalfEndpointUniformBound.crossCoefficient
  congr 1
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hleft : q.val < m
  · obtain ⟨i, hi, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hleft
    have hiCarrier : i ∈ left.bound.carrier.state.active := by
      rw [left.bound.carrier.active_eq_finalActive_of_processed_eq_schedule
        left.bound.carrier_processed]
      exact hi
    have hiLeft : (leftMomentIndex i).val < m := by
      simp only [leftMomentIndex]
      exact i.isLt
    unfold r324TwoHalfRootDoubledReconstruct
    simp only [momentDoubleFinEquiv_symm_leftMomentIndex,
      r324LeftInternalTranslateMeasurableEquiv_apply,
      if_pos hiLeft]
    exact left.bound.carrier.reconstruct_commonTranslate_of_active
      leftPost a i hiCarrier
  · obtain ⟨i, hi, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq (by omega)
    have hiRight : ¬ (rightMomentIndex i).val < m := by
      simp only [rightMomentIndex]
      omega
    unfold r324TwoHalfRootDoubledReconstruct
    simp only [momentDoubleFinEquiv_symm_rightMomentIndex,
      r324LeftInternalTranslateMeasurableEquiv_apply,
      if_neg hiRight]

/-- The extra common-left Haar parameter is jointly integrable for the
genuine residual cross coefficient.  Pointwise, the displayed integrand is
the already-integrable completed endpoint density composed with the
common-left projection above. -/
theorem integrable_commonLeft_crossCoefficient
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactLinearPackage left rightRoute) :
    Integrable
      (fun q : T4 ×
          ((left.bound.carrier.SurvivingCoordinate → T4) ×
            (right.package.bound.carrier.SurvivingCoordinate → T4)) =>
        (charT4 (alpha + beta) q.1 *
          left.bound.crossCoefficient right.package.bound e0.2.2
            (r324CommonTranslate q.1 q.2.1) q.2.2) *
          (left.bound.density (fun _ => 1) beta q.2.1 *
            right.package.bound.density (fun _ => 1) (-beta) q.2.2))
      (paperMeasure.prod
        ((Measure.pi fun _ : left.bound.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ :
            right.package.bound.carrier.SurvivingCoordinate =>
              paperMeasure))) := by
  let routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders := {
    left := leftRoute
    right := rightRoute }
  let projection :
      T4 ×
          ((left.bound.carrier.SurvivingCoordinate → T4) ×
            (right.package.bound.carrier.SurvivingCoordinate → T4)) →
        (left.bound.carrier.SurvivingCoordinate → T4) ×
          (right.package.bound.carrier.SurvivingCoordinate → T4) :=
    fun q => (r324CommonTranslate q.1 q.2.1, q.2.2)
  let terminalMeasure :=
    (Measure.pi fun _ : left.bound.carrier.SurvivingCoordinate =>
      paperMeasure).prod
    (Measure.pi fun _ :
      right.package.bound.carrier.SurvivingCoordinate => paperMeasure)
  let baseDensity :=
    left.bound.endpointProductDensity right.package.bound beta e0.2.2
  have hmeas : AEStronglyMeasurable
      (fun q : T4 ×
          ((left.bound.carrier.SurvivingCoordinate → T4) ×
            (right.package.bound.carrier.SurvivingCoordinate → T4)) =>
        baseDensity (projection q))
      (paperMeasure.prod terminalMeasure) :=
    right.package.endpoint_integrable.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_r324CommonLeftProjection
        left.bound.carrier.SurvivingCoordinate
        right.package.bound.carrier.SurvivingCoordinate)
  have hcomposed : Integrable
      (fun q => baseDensity (projection q))
      (paperMeasure.prod terminalMeasure) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · filter_upwards with a
      rw [← memLp_one_iff_integrable]
      exact
        (memLp_one_iff_integrable.mpr
          right.package.endpoint_integrable).comp_measurePreserving
            (measurePreserving_r324CommonLeftProjectionSection
              left.bound.carrier.SurvivingCoordinate
              right.package.bound.carrier.SurvivingCoordinate a)
    · have hnorm : ∀ a : T4,
          (∫ p, ‖baseDensity (projection (a, p))‖ ∂terminalMeasure) =
            ∫ p, ‖baseDensity p‖ ∂terminalMeasure := by
        intro a
        exact
          (measurePreserving_r324CommonLeftProjectionSection
            left.bound.carrier.SurvivingCoordinate
            right.package.bound.carrier.SurvivingCoordinate a).integral_comp'
              (fun p => ‖baseDensity p‖)
      simp_rw [hnorm]
      exact integrable_const _
  apply hcomposed.congr
  filter_upwards with q
  have hfactor :=
    left.bound.endpointProductDensityWithCoefficient_eq_coefficient_mul_unit
      (routes := routes) right.package.bound
      left.densityEvaluationLinear right.densityEvaluationLinear beta
      (left.bound.crossCoefficient right.package.bound e0.2.2)
      (r324CommonTranslate q.1 q.2.1, q.2.2)
  calc
    left.bound.endpointProductDensity right.package.bound beta e0.2.2
        (projection q) =
        left.bound.crossCoefficient right.package.bound e0.2.2
            (r324CommonTranslate q.1 q.2.1) q.2.2 *
          left.bound.endpointUnitProductDensity right.package.bound beta
            (r324CommonTranslate q.1 q.2.1, q.2.2) := by
      exact hfactor
    _ = (charT4 (alpha + beta) q.1 *
          left.bound.crossCoefficient right.package.bound e0.2.2
            (r324CommonTranslate q.1 q.2.1) q.2.2) *
          (left.bound.density (fun _ => 1) beta q.2.1 *
            right.package.bound.density (fun _ => 1) (-beta) q.2.2) := by
      unfold R324PaperHalfEndpointUniformBound.endpointUnitProductDensity
      rw [left.unitDensity_commonTranslate]
      ring

/-- Canonical signed common-left Fourier identity on the initial nested
carrier.  All four endpoint operations and the exact two-half collapse have
already happened before this equality; no absolute value occurs. -/
theorem integral_nestedEndpointProductDensity_eq_commonLeftFourier
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactLinearPackage left rightRoute) :
    (∫ v, left.bound.nestedEndpointProductDensity
        right.package.bound beta e0.2.2 v
      ∂Measure.pi fun _ :
        (left.bound.twoHalfTerminal right.package.bound).NestedCoordinate
          e0.2.2 => paperMeasure) =
      ∫ v,
        left.bound.nestedEndpointProductDensityWithCoefficient
          (routes := { left := leftRoute, right := rightRoute })
          right.package.bound beta e0.2.2
          (r324CommonLeftFourierCoefficient
            (I := left.bound.carrier.SurvivingCoordinate)
            (J := right.package.bound.carrier.SurvivingCoordinate)
            (alpha + beta)
            (left.bound.crossCoefficient right.package.bound e0.2.2)) v
        ∂Measure.pi fun _ :
          (left.bound.twoHalfTerminal right.package.bound).NestedCoordinate
            e0.2.2 => paperMeasure := by
  let routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders := {
    left := leftRoute
    right := rightRoute }
  have h :=
    left.bound.integral_nestedEndpointProductDensityWithCoefficient_eq_commonLeftFourier
      (routes := routes) right.package.bound
      left.densityEvaluationLinear right.densityEvaluationLinear beta e0.2.2
      (left.bound.crossCoefficient right.package.bound e0.2.2)
      left.unitDensity_commonTranslate
      (left.integrable_commonLeft_crossCoefficient right)
  exact h

end R324PaperLeftRouteExactPackage

end R324WithinHalfResidualPrefix

end

end Anderson4D
