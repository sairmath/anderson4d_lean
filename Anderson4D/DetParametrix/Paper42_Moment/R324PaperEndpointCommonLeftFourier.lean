import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfCoefficientParametric
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperRightRouteExactPackage
import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyConservation

/-!
# Common-left Fourier averaging after the endpoint collapse

Paper: R-324 — §4.2 Step 4(B), common-left Fourier averaging

Paper Step 4(B) takes its common translation only after all four endpoint
operations have been completed.  This file isolates the two formal facts
needed at that point:

* a coefficient-parametric endpoint density factors pointwise through the
  value of the coefficient at the surviving terminal tuple, provided the two
  already-completed half densities have their literal evaluation-linearity;
* a common translation of a finite torus tuple preserves product Haar, and a
  covariant unit density may consequently be averaged into the corresponding
  common-left Fourier coefficient.

The statements are deliberately independent of the sixteen endpoint cases.
Canonical route packages can supply the small evaluation-law wrapper from
their existing `density_mul` and `density_congr_at` proofs.  No norm is taken
in this file.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-! ## Common translation on a finite terminal carrier -/

/-- Translate every coordinate of a finite torus tuple by the same point. -/
def r324CommonTranslate {I : Type*} (a : T4) (v : I -> T4) : I -> T4 :=
  fun i => v i + a

@[simp] theorem r324CommonTranslate_apply
    {I : Type*} (a : T4) (v : I -> T4) (i : I) :
    r324CommonTranslate a v i = v i + a :=
  rfl

/-- The common translation as a measurable equivalence. -/
def r324CommonTranslateMeasurableEquiv
    (I : Type*) (a : T4) : (I -> T4) ≃ᵐ (I -> T4) :=
  MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.addRight a

@[simp] theorem r324CommonTranslateMeasurableEquiv_apply
    {I : Type*} (a : T4) (v : I -> T4) :
    r324CommonTranslateMeasurableEquiv I a v =
      r324CommonTranslate a v := by
  rfl

/-- Product Haar is invariant under a common translation of all coordinates.
The finite hypothesis is exactly the one available on every terminal
surviving-coordinate type. -/
theorem measurePreserving_r324CommonTranslate
    (I : Type*) [Fintype I] (a : T4) :
    MeasurePreserving
      (r324CommonTranslate a : (I -> T4) -> (I -> T4))
      (Measure.pi fun _ : I => paperMeasure)
      (Measure.pi fun _ : I => paperMeasure) := by
  change MeasurePreserving (fun v i => v i + a)
    (Measure.pi fun _ : I => paperMeasure)
    (Measure.pi fun _ : I => paperMeasure)
  exact measurePreserving_pi
    (fun _ : I => paperMeasure)
    (fun _ : I => paperMeasure)
    (fun _ => by
      rw [paperMeasure_eq_volume]
      exact measurePreserving_add_right (volume : Measure T4) a)

/-! ## Evaluation-linearity of a completed half density -/

/-- The only two algebraic laws used after a one-half endpoint route has
finished.  They are pointwise laws, not continuity or positivity data. -/
structure R324EndpointDensityEvaluationLinear
    {I : Type*}
    (density : ((I -> T4) -> Complex) -> Z4 -> (I -> T4) -> Complex) : Prop
    where
  mul : forall (a : Complex) (coefficient : (I -> T4) -> Complex)
      (mode : Z4) (v : I -> T4),
    density (fun u => a * coefficient u) mode v =
      a * density coefficient mode v
  congr_at : forall
      (leftCoefficient rightCoefficient : (I -> T4) -> Complex)
      (mode : Z4) (v : I -> T4),
    leftCoefficient v = rightCoefficient v ->
      density leftCoefficient mode v =
        density rightCoefficient mode v

namespace R324EndpointDensityEvaluationLinear

variable {I : Type*}
    {density : ((I -> T4) -> Complex) -> Z4 -> (I -> T4) -> Complex}

/-- At a fixed terminal tuple, a completed endpoint density only sees the
value of its coefficient there. -/
theorem density_eq_value_mul_unit
    (law : R324EndpointDensityEvaluationLinear density)
    (coefficient : (I -> T4) -> Complex)
    (mode : Z4) (v : I -> T4) :
    density coefficient mode v =
      coefficient v * density (fun _ => 1) mode v := by
  calc
    density coefficient mode v =
        density (fun _ => coefficient v) mode v :=
      law.congr_at coefficient (fun _ => coefficient v) mode v rfl
    _ = coefficient v * density (fun _ => 1) mode v := by
      simpa only [mul_one] using
        law.mul (coefficient v) (fun _ => 1) mode v

end R324EndpointDensityEvaluationLinear

/-! The exact left route package already stores precisely these two laws. -/

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

/-- Evaluation-linearity of the left density, repackaged without changing
the existing exact-route structure. -/
theorem R324PaperLeftRouteExactPackage.densityEvaluationLinear
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta) :
    R324EndpointDensityEvaluationLinear left.bound.density where
  mul := left.density_mul
  congr_at := left.density_congr_at

/-- A non-rippling wrapper for a right exact package that retains the two
pointwise evaluation laws.  Canonical route constructors can populate this
wrapper while the old exact package, and hence its exact collapse theorem,
remain unchanged. -/
structure R324PaperRightRouteExactLinearPackage
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (rightRoute : R324PaperHalfEndpointRoute rightProviders) where
  package : R324PaperRightRouteExactPackage left rightRoute
  densityEvaluationLinear :
    R324EndpointDensityEvaluationLinear package.bound.density

namespace R324PaperRightRouteExactLinearPackage

/-- The old exact collapse is inherited verbatim by the linear wrapper. -/
theorem exactCollapse_to_nested
    (left : R324PaperLeftRouteExactPackage p e0 leftRoute beta)
    (right : R324PaperRightRouteExactLinearPackage left rightRoute) :
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps e0.1).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.2.1).remainingOrder)) *
        r324RefinedPhysicalIntegral rho eps m alpha beta p =
      ∫ v,
        left.bound.nestedEndpointProductDensity
          right.package.bound beta e0.2.2 v
        ∂Measure.pi fun _ :
          (left.bound.twoHalfTerminal right.package.bound).NestedCoordinate
            e0.2.2 => paperMeasure :=
  R324PaperRightRouteExactPackage.exactCollapse_to_nested
    left right.package

end R324PaperRightRouteExactLinearPackage

namespace R324PaperHalfEndpointUniformBound

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {alpha beta : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM (-alpha)}
    {routes : R324PaperTwoHalfEndpointRoutes leftProviders rightProviders}

/-- The unit endpoint product retained after all four endpoint operations. -/
def endpointUnitProductDensity
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (beta : Z4)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) : Complex :=
  left.density (fun _ => 1) beta p.1 *
    right.density (fun _ => 1) (-beta) p.2

/-- Exact pointwise factorization of the coefficient-parametric endpoint
density.  In particular, the complete signed coefficient is not split before
the endpoint operations have finished. -/
theorem endpointProductDensityWithCoefficient_eq_coefficient_mul_unit
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (leftLaw : R324EndpointDensityEvaluationLinear left.density)
    (rightLaw : R324EndpointDensityEvaluationLinear right.density)
    (beta : Z4)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (p :
      (left.carrier.SurvivingCoordinate -> T4) ×
        (right.carrier.SurvivingCoordinate -> T4)) :
    left.endpointProductDensityWithCoefficient right beta coefficient p =
      coefficient p.1 p.2 *
        left.endpointUnitProductDensity right beta p := by
  let leftSection :
      (right.carrier.SurvivingCoordinate -> T4) -> Complex :=
    fun rightPost =>
      left.density (fun _ => coefficient p.1 rightPost) beta p.1
  calc
    left.endpointProductDensityWithCoefficient right beta coefficient p =
        right.density leftSection (-beta) p.2 := by
      rfl
    _ = leftSection p.2 *
          right.density (fun _ => 1) (-beta) p.2 :=
      rightLaw.density_eq_value_mul_unit leftSection (-beta) p.2
    _ = (coefficient p.1 p.2 *
          left.density (fun _ => 1) beta p.1) *
          right.density (fun _ => 1) (-beta) p.2 := by
      rw [show leftSection p.2 =
          coefficient p.1 p.2 *
            left.density (fun _ => 1) beta p.1 by
        exact leftLaw.density_eq_value_mul_unit
          (fun _ => coefficient p.1 p.2) beta p.1]
    _ = coefficient p.1 p.2 *
          left.endpointUnitProductDensity right beta p := by
      unfold endpointUnitProductDensity
      ring

end R324PaperHalfEndpointUniformBound

/-! ## Abstract common-left Fourier averaging -/

/-- The common-left Fourier coefficient of a two-terminal coefficient.  The
right terminal tuple is held fixed. -/
def r324CommonLeftFourierCoefficient
    {I J : Type*}
    (mode : Z4)
    (coefficient : (I -> T4) -> (J -> T4) -> Complex)
    (left : I -> T4) (right : J -> T4) : Complex :=
  (r324PaperTorusMass : Complex)⁻¹ *
    ∫ a : T4,
      charT4 mode a *
        coefficient (r324CommonTranslate a left) right
      ∂paperMeasure

/-- Haar averaging at a covariant unit density.  This is the exact abstract
form of the common-left Fourier move in paper Step 4(B).  The only analytic
input is joint integrability before the Fubini exchange. -/
theorem integral_coefficient_mul_covariantUnit_eq_commonLeftFourier
    {I J : Type*} [Fintype I] [Fintype J]
    (mode : Z4)
    (leftUnit : (I -> T4) -> Complex)
    (rightUnit : (J -> T4) -> Complex)
    (coefficient : (I -> T4) -> (J -> T4) -> Complex)
    (hcov : forall (a : T4) (v : I -> T4),
      leftUnit (r324CommonTranslate a v) =
        charT4 mode a * leftUnit v)
    (hjoint : Integrable
      (fun q : T4 × ((I -> T4) × (J -> T4)) =>
        (charT4 mode q.1 *
          coefficient (r324CommonTranslate q.1 q.2.1) q.2.2) *
          (leftUnit q.2.1 * rightUnit q.2.2))
      (paperMeasure.prod
        ((Measure.pi fun _ : I => paperMeasure).prod
          (Measure.pi fun _ : J => paperMeasure)))) :
    (∫ p : (I -> T4) × (J -> T4),
        coefficient p.1 p.2 * (leftUnit p.1 * rightUnit p.2)
      ∂((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure))) =
      ∫ p : (I -> T4) × (J -> T4),
        r324CommonLeftFourierCoefficient mode coefficient p.1 p.2 *
          (leftUnit p.1 * rightUnit p.2)
      ∂((Measure.pi fun _ : I => paperMeasure).prod
        (Measure.pi fun _ : J => paperMeasure)) := by
  let muLeft := Measure.pi fun _ : I => paperMeasure
  let muRight := Measure.pi fun _ : J => paperMeasure
  let muProduct := muLeft.prod muRight
  let base : ((I -> T4) × (J -> T4)) -> Complex := fun p =>
    coefficient p.1 p.2 * (leftUnit p.1 * rightUnit p.2)
  let shifted : T4 -> ((I -> T4) × (J -> T4)) -> Complex := fun a p =>
    (r324PaperTorusMass : Complex)⁻¹ *
      ((charT4 mode a *
        coefficient (r324CommonTranslate a p.1) p.2) *
        (leftUnit p.1 * rightUnit p.2))
  have hshift (a : T4) :
      (∫ p, shifted a p ∂muProduct) =
        (r324PaperTorusMass : Complex)⁻¹ *
          ∫ p, base p ∂muProduct := by
    have hpLeft := measurePreserving_r324CommonTranslate I a
    let shiftProduct :
        ((I -> T4) × (J -> T4)) ≃ᵐ ((I -> T4) × (J -> T4)) :=
      MeasurableEquiv.prodCongr
        (r324CommonTranslateMeasurableEquiv I a)
        (MeasurableEquiv.refl (J -> T4))
    have hp : MeasurePreserving
        shiftProduct
        muProduct muProduct := by
      change MeasurePreserving
        (fun p : (I -> T4) × (J -> T4) =>
          (r324CommonTranslate a p.1, p.2))
        muProduct muProduct
      exact hpLeft.prod (MeasurePreserving.id muRight)
    calc
      (∫ p, shifted a p ∂muProduct) =
          (r324PaperTorusMass : Complex)⁻¹ *
            ∫ p, base (shiftProduct p) ∂muProduct := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with p
        have hshiftProduct :
            shiftProduct p = (r324CommonTranslate a p.1, p.2) := by
          rfl
        rw [hshiftProduct]
        unfold shifted base
        rw [hcov]
        ring
      _ = (r324PaperTorusMass : Complex)⁻¹ *
          ∫ p, base p ∂muProduct := by
        rw [hp.integral_comp' base]
  have hvolume :
      (ENNReal.ofReal ((2 * Real.pi) ^ (dim : Nat))).toReal =
        r324PaperTorusMass := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hvolumeNe : (r324PaperTorusMass : Complex) ≠ 0 := by
    exact_mod_cast r324PaperTorusMass_pos.ne'
  have hjointShifted : Integrable
      (fun q : T4 × ((I -> T4) × (J -> T4)) => shifted q.1 q.2)
      (paperMeasure.prod muProduct) := by
    simpa only [shifted, muProduct, muLeft, muRight] using
      hjoint.const_mul (r324PaperTorusMass : Complex)⁻¹
  have hconstant :
      (∫ _a : T4,
          (r324PaperTorusMass : Complex)⁻¹ *
            ∫ p, base p ∂muProduct ∂paperMeasure) =
        ∫ p, base p ∂muProduct := by
    rw [integral_const, measureReal_def, paperMeasure_univ,
      hvolume]
    change (r324PaperTorusMass : Complex) *
        ((r324PaperTorusMass : Complex)⁻¹ *
          ∫ p, base p ∂muProduct) =
      ∫ p, base p ∂muProduct
    field_simp [hvolumeNe]
  calc
    (∫ p, coefficient p.1 p.2 *
          (leftUnit p.1 * rightUnit p.2) ∂muProduct) =
        ∫ _a : T4,
          (r324PaperTorusMass : Complex)⁻¹ *
            ∫ p, base p ∂muProduct ∂paperMeasure := by
      rw [hconstant]
    _ = ∫ a : T4, (∫ p, shifted a p ∂muProduct)
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with a
      exact (hshift a).symm
    _ = ∫ p, (∫ a : T4, shifted a p ∂paperMeasure)
          ∂muProduct := by
      exact (integral_prod _ hjointShifted).symm.trans
        (integral_prod_symm _ hjointShifted)
    _ = ∫ p,
          r324CommonLeftFourierCoefficient mode coefficient p.1 p.2 *
            (leftUnit p.1 * rightUnit p.2) ∂muProduct := by
      apply integral_congr_ae
      filter_upwards with p
      unfold shifted r324CommonLeftFourierCoefficient
      rw [show
          (∫ a : T4,
            (r324PaperTorusMass : Complex)⁻¹ *
              ((charT4 mode a *
                coefficient (r324CommonTranslate a p.1) p.2) *
                (leftUnit p.1 * rightUnit p.2)) ∂paperMeasure) =
            ∫ a : T4,
              ((r324PaperTorusMass : Complex)⁻¹ *
                (charT4 mode a *
                  coefficient (r324CommonTranslate a p.1) p.2)) *
                (leftUnit p.1 * rightUnit p.2)
              ∂paperMeasure by
        apply integral_congr_ae
        filter_upwards with a
        ring,
        integral_mul_const, integral_const_mul]
    _ = _ := rfl

namespace R324PaperHalfEndpointUniformBound

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {alpha beta : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM (-alpha)}
    {routes : R324PaperTwoHalfEndpointRoutes leftProviders rightProviders}

/-- Replace the complete coefficient of the already-completed endpoint
product by its common-left Fourier coefficient.  This is a signed identity;
the first norm may be taken only after this theorem. -/
theorem integral_endpointProductDensityWithCoefficient_eq_commonLeftFourier
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (leftLaw : R324EndpointDensityEvaluationLinear left.density)
    (rightLaw : R324EndpointDensityEvaluationLinear right.density)
    (beta : Z4)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (hcov : forall
      (a : T4) (v : left.carrier.SurvivingCoordinate -> T4),
      left.density (fun _ => 1) beta (r324CommonTranslate a v) =
        charT4 (alpha + beta) a *
          left.density (fun _ => 1) beta v)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        (charT4 (alpha + beta) q.1 *
          coefficient (r324CommonTranslate q.1 q.2.1) q.2.2) *
          (left.density (fun _ => 1) beta q.2.1 *
            right.density (fun _ => 1) (-beta) q.2.2))
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    (∫ p, left.endpointProductDensityWithCoefficient
        right beta coefficient p
      ∂((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
          paperMeasure))) =
      ∫ p, left.endpointProductDensityWithCoefficient right beta
        (r324CommonLeftFourierCoefficient (alpha + beta) coefficient) p
      ∂((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
          paperMeasure).prod
        (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
          paperMeasure)) := by
  let muProduct :=
    (Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
      paperMeasure).prod
    (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
      paperMeasure)
  calc
    (∫ p, left.endpointProductDensityWithCoefficient
          right beta coefficient p ∂muProduct) =
        ∫ p, coefficient p.1 p.2 *
          left.endpointUnitProductDensity right beta p ∂muProduct := by
      apply integral_congr_ae
      filter_upwards with p
      exact left.endpointProductDensityWithCoefficient_eq_coefficient_mul_unit
        right leftLaw rightLaw beta coefficient p
    _ = ∫ p,
          r324CommonLeftFourierCoefficient
              (alpha + beta) coefficient p.1 p.2 *
            left.endpointUnitProductDensity right beta p ∂muProduct := by
      exact integral_coefficient_mul_covariantUnit_eq_commonLeftFourier
        (alpha + beta)
        (left.density (fun _ => 1) beta)
        (right.density (fun _ => 1) (-beta))
        coefficient hcov hjoint
    _ = ∫ p, left.endpointProductDensityWithCoefficient right beta
          (r324CommonLeftFourierCoefficient
            (alpha + beta) coefficient) p ∂muProduct := by
      apply integral_congr_ae
      filter_upwards with p
      exact (left.endpointProductDensityWithCoefficient_eq_coefficient_mul_unit
        right leftLaw rightLaw beta
        (r324CommonLeftFourierCoefficient
          (alpha + beta) coefficient) p).symm
    _ = _ := rfl

/-- The same common-left Fourier identity on the literal initial nested
carrier used by the exact R-324 collapse. -/
theorem integral_nestedEndpointProductDensityWithCoefficient_eq_commonLeftFourier
    (left : R324PaperHalfEndpointUniformBound
      routes.left.completedRoute)
    (right : R324PaperHalfEndpointUniformBound
      routes.right.completedRoute)
    (leftLaw : R324EndpointDensityEvaluationLinear left.density)
    (rightLaw : R324EndpointDensityEvaluationLinear right.density)
    (beta : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (coefficient :
      (left.carrier.SurvivingCoordinate -> T4) ->
        (right.carrier.SurvivingCoordinate -> T4) -> Complex)
    (hcov : forall
      (a : T4) (v : left.carrier.SurvivingCoordinate -> T4),
      left.density (fun _ => 1) beta (r324CommonTranslate a v) =
        charT4 (alpha + beta) a *
          left.density (fun _ => 1) beta v)
    (hjoint : Integrable
      (fun q : T4 ×
          ((left.carrier.SurvivingCoordinate -> T4) ×
            (right.carrier.SurvivingCoordinate -> T4)) =>
        (charT4 (alpha + beta) q.1 *
          coefficient (r324CommonTranslate q.1 q.2.1) q.2.2) *
          (left.density (fun _ => 1) beta q.2.1 *
            right.density (fun _ => 1) (-beta) q.2.2))
      (paperMeasure.prod
        ((Measure.pi fun _ : left.carrier.SurvivingCoordinate =>
            paperMeasure).prod
          (Measure.pi fun _ : right.carrier.SurvivingCoordinate =>
            paperMeasure)))) :
    (∫ v, left.nestedEndpointProductDensityWithCoefficient
        right beta pi coefficient v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure) =
      ∫ v, left.nestedEndpointProductDensityWithCoefficient right beta pi
        (r324CommonLeftFourierCoefficient (alpha + beta) coefficient) v
      ∂Measure.pi fun _ :
        (left.twoHalfTerminal right).NestedCoordinate pi => paperMeasure := by
  unfold nestedEndpointProductDensityWithCoefficient
  rw [← (left.twoHalfTerminal right)
      |>.integral_terminalProduct_eq_integral_initialNestedPullback
        pi (left.endpointProductDensityWithCoefficient
          right beta coefficient),
    ← (left.twoHalfTerminal right)
      |>.integral_terminalProduct_eq_integral_initialNestedPullback
        pi (left.endpointProductDensityWithCoefficient right beta
          (r324CommonLeftFourierCoefficient
            (alpha + beta) coefficient))]
  exact left.integral_endpointProductDensityWithCoefficient_eq_commonLeftFourier
    right leftLaw rightLaw beta coefficient hcov hjoint

end R324PaperHalfEndpointUniformBound

end R324WithinHalfResidualPrefix

end

end Anderson4D
