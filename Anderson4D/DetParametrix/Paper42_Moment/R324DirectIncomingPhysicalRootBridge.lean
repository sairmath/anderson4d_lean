import Anderson4D.DetParametrix.Paper42_Moment.R324DirectIncomingInitialFourier
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalPhysicalRootBridge
import Anderson4D.DetParametrix.Paper42_Moment.R324DriverClosure

/-!
# The genuine refined root after the direct incoming Fourier operation

This is the product-space version of the first endpoint operation in paper
Step 4(A).  The physical root is regrouped so that the incoming endpoint is
the last variable.  Joint integrability is inherited from the genuine
refined physical fibre; only then is the one-variable Fourier identity from
`R324DirectIncomingInitialFourier` applied sectionwise.

No norm or endpoint estimate occurs here.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {lam eps : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}

/-! ## Root regrouping -/

/-- Move the physical incoming endpoint behind the two initial residual
carriers:
`(x,y,z,w,v) ↦ ((((y,z,w),v₋),v₊),x)`.

The first component before the last `x` is exactly the parameter order used
by the direct-incoming source of the one-half transform. -/
def r324DirectIncomingRootMeasurableEquiv
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaP kappaM : PartialPairing (Fin m)) :
    R324PhysicalPoint m ≃ᵐ
      ((R324IncomingExceptionalRootParameter
          rho lam eps kappaM) ×
        ((R324WithinHalfResidualPrefix.initial
          rho lam eps kappaP).SurvivingCoordinate → T4)) × T4 :=
  let Left :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4
  let Right :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate → T4
  let Rest := T4 × (T4 × T4)
  let root :=
    r324IncomingExceptionalRootMeasurableEquiv
      rho lam eps kappaP kappaM
  let exposeRight :
      (T4 × (Rest × Right)) × Left ≃ᵐ
        ((T4 × Rest) × Right) × Left :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := Rest) (γ := Right)).symm
      (MeasurableEquiv.refl Left)
  let regroup :
      ((T4 × Rest) × Right) × Left ≃ᵐ
        (Rest × Right) × (T4 × Left) :=
    r324DriverTerminalRegroupMeasurableEquiv
      T4 Rest Right Left
  let swapLast :
      (Rest × Right) × (T4 × Left) ≃ᵐ
        (Rest × Right) × (Left × T4) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (Rest × Right))
      (MeasurableEquiv.prodComm : T4 × Left ≃ᵐ Left × T4)
  let close :
      (Rest × Right) × (Left × T4) ≃ᵐ
        ((Rest × Right) × Left) × T4 :=
    (MeasurableEquiv.prodAssoc
      (α := Rest × Right) (β := Left) (γ := T4)).symm
  root.trans (exposeRight.trans (regroup.trans (swapLast.trans close)))

@[simp]
theorem r324DirectIncomingRootMeasurableEquiv_apply
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaP kappaM : PartialPairing (Fin m))
    (q : R324PhysicalPoint m) :
    r324DirectIncomingRootMeasurableEquiv
        rho lam eps kappaP kappaM q =
      ((((q.2.1, (q.2.2.1, q.2.2.2.1)),
          (r324InitialTwoHalfProductPiMeasurableEquiv
            rho lam eps kappaP kappaM).symm q.2.2.2.2 |>.2),
        (r324InitialTwoHalfProductPiMeasurableEquiv
          rho lam eps kappaP kappaM).symm q.2.2.2.2 |>.1),
        q.1) := by
  rfl

/-- The direct-incoming root regrouping preserves the literal product Haar
measure. -/
theorem measurePreserving_r324DirectIncomingRootMeasurableEquiv
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaP kappaM : PartialPairing (Fin m)) :
    MeasurePreserving
      (r324DirectIncomingRootMeasurableEquiv
        rho lam eps kappaP kappaM)
      (r324PhysicalMeasure m)
      (((r324IncomingExceptionalRootParameterMeasure
          rho lam eps kappaM).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaP).SurvivingCoordinate => paperMeasure)).prod
        paperMeasure) := by
  let Left :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4
  let Right :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate → T4
  let Rest := T4 × (T4 × T4)
  let muLeft : Measure Left := Measure.pi fun _ => paperMeasure
  let muRight : Measure Right := Measure.pi fun _ => paperMeasure
  let muRest : Measure Rest :=
    paperMeasure.prod (paperMeasure.prod paperMeasure)
  let muParameter : Measure (Rest × Right) := muRest.prod muRight
  let root :=
    r324IncomingExceptionalRootMeasurableEquiv
      rho lam eps kappaP kappaM
  let exposeRight :
      (T4 × (Rest × Right)) × Left ≃ᵐ
        ((T4 × Rest) × Right) × Left :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodAssoc
        (α := T4) (β := Rest) (γ := Right)).symm
      (MeasurableEquiv.refl Left)
  let regroup :
      ((T4 × Rest) × Right) × Left ≃ᵐ
        (Rest × Right) × (T4 × Left) :=
    r324DriverTerminalRegroupMeasurableEquiv
      T4 Rest Right Left
  let swapLast :
      (Rest × Right) × (T4 × Left) ≃ᵐ
        (Rest × Right) × (Left × T4) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl (Rest × Right))
      (MeasurableEquiv.prodComm : T4 × Left ≃ᵐ Left × T4)
  let close :
      (Rest × Right) × (Left × T4) ≃ᵐ
        ((Rest × Right) × Left) × T4 :=
    (MeasurableEquiv.prodAssoc
      (α := Rest × Right) (β := Left) (γ := T4)).symm
  have hroot :
      MeasurePreserving root
        (r324PhysicalMeasure m)
        ((paperMeasure.prod muParameter).prod muLeft) := by
    simpa only [root, muParameter, muRest, muRight,
      r324IncomingExceptionalRootParameterMeasure] using
      measurePreserving_r324IncomingExceptionalRootMeasurableEquiv
        rho lam eps kappaP kappaM
  have hexpose :
      MeasurePreserving exposeRight
        ((paperMeasure.prod muParameter).prod muLeft)
        (((paperMeasure.prod muRest).prod muRight).prod muLeft) := by
    exact
      ((measurePreserving_prodAssoc
        paperMeasure muRest muRight).symm.prod
          (MeasurePreserving.id muLeft))
  have hregroup :
      MeasurePreserving regroup
        (((paperMeasure.prod muRest).prod muRight).prod muLeft)
        (muParameter.prod (paperMeasure.prod muLeft)) := by
    simpa only [regroup, muParameter] using
      measurePreserving_r324DriverTerminalRegroupMeasurableEquiv
        paperMeasure muRest muRight muLeft
  have hswap :
      MeasurePreserving swapLast
        (muParameter.prod (paperMeasure.prod muLeft))
        (muParameter.prod (muLeft.prod paperMeasure)) := by
    exact
      (MeasurePreserving.id muParameter).prod
        (Measure.measurePreserving_swap
          (μ := paperMeasure) (ν := muLeft))
  have hclose :
      MeasurePreserving close
        (muParameter.prod (muLeft.prod paperMeasure))
        ((muParameter.prod muLeft).prod paperMeasure) := by
    exact
      (measurePreserving_prodAssoc
        muParameter muLeft paperMeasure).symm
  change MeasurePreserving
    (root.trans
      (exposeRight.trans (regroup.trans (swapLast.trans close))))
    (r324PhysicalMeasure m)
    ((muParameter.prod muLeft).prod paperMeasure)
  exact hclose.comp (hswap.comp (hregroup.comp (hexpose.comp hroot)))

/-! ## The direct source on the regrouped root -/

/-- All factors of a refined root other than the incoming left character
and incoming left Green leg. -/
def directIncomingRefinedRootOuter
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaP kappaM : PartialPairing (Fin m))
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (omega : R324IncomingExceptionalRootParameter
      rho lam eps kappaM)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).SurvivingCoordinate → T4) : Complex :=
  charT4 beta omega.1.1 *
    charT4 (-alpha) omega.1.2.1 *
    charT4 (-beta) omega.1.2.2 *
    (((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).residualIntegrand
      rho eps omega.1.2.1 omega.1.2.2
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).reconstruct omega.2) : Complex) *
      (r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaP)
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (v, omega.2)) : Complex))

/-- The regrouped genuine refined density is the raw initial left residual
times the untouched root outer factor. -/
theorem r324Flatten_momentRefinedPhysicalIntegrand_eq_directIncoming_reindex
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    (alpha beta : Z4)
    (q : R324PhysicalPoint m) :
    r324Flatten
        (momentRefinedPhysicalIntegrand
          rho eps m alpha beta p.1.1 p.2.1) q =
      charT4 alpha q.1 *
        (((R324WithinHalfResidualPrefix.initial
            rho lam eps e0.1).residualIntegrand
          rho eps q.1 q.2.1
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps e0.1).reconstruct
            ((r324InitialTwoHalfProductPiMeasurableEquiv
              rho lam eps e0.1 e0.2.1).symm q.2.2.2.2 |>.1)) : Complex) *
          directIncomingRefinedRootOuter
            rho lam eps e0.1 e0.2.1 alpha beta e0.2.2
            (((q.2.1, (q.2.2.1, q.2.2.2.1)),
              (r324InitialTwoHalfProductPiMeasurableEquiv
                rho lam eps e0.1 e0.2.1).symm q.2.2.2.2 |>.2))
            ((r324InitialTwoHalfProductPiMeasurableEquiv
              rho lam eps e0.1 e0.2.1).symm q.2.2.2.2 |>.1)) := by
  let splitInternal :=
    r324InitialTwoHalfProductPiMeasurableEquiv
      rho lam eps e0.1 e0.2.1
  let halves := splitInternal.symm q.2.2.2.2
  have hroot :
      r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial rho lam eps e0.1)
          (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1)
          halves = q.2.2.2.2 := by
    calc
      _ = splitInternal halves := by
        exact
          (r324InitialTwoHalfProductPiMeasurableEquiv_apply
            rho lam eps e0.1 e0.2.1 halves).symm
      _ = q.2.2.2.2 := splitInternal.apply_symm_apply q.2.2.2.2
  have hleftCoordinates :
      (R324WithinHalfResidualPrefix.initial
          rho lam eps e0.1).reconstruct halves.1 =
        fun i => q.2.2.2.2 (leftMomentIndex i) := by
    funext i
    calc
      _ = r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial rho lam eps e0.1)
          (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1)
          halves (leftMomentIndex i) := by
        rw [r324TwoHalfRootDoubledReconstruct,
          momentDoubleFinEquiv_symm_leftMomentIndex]
      _ = _ := congrFun hroot (leftMomentIndex i)
  have hrightCoordinates :
      (R324WithinHalfResidualPrefix.initial
          rho lam eps e0.2.1).reconstruct halves.2 =
        fun i => q.2.2.2.2 (rightMomentIndex i) := by
    funext i
    calc
      _ = r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial rho lam eps e0.1)
          (R324WithinHalfResidualPrefix.initial rho lam eps e0.2.1)
          halves (rightMomentIndex i) := by
        rw [r324TwoHalfRootDoubledReconstruct,
          momentDoubleFinEquiv_symm_rightMomentIndex]
      _ = _ := congrFun hroot (rightMomentIndex i)
  unfold r324Flatten
  rw [momentRefinedPhysicalIntegrand_eq_twoInitialResiduals_mul_cross
    rho lam eps m alpha beta p.1.1 p.2.1 e0 he0
    q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2]
  change
    momentFourierPhase alpha beta
        q.1 q.2.1 q.2.2.1 q.2.2.2.1 *
      ((R324WithinHalfResidualPrefix.initial
          rho lam eps e0.1).residualIntegrand
        rho eps q.1 q.2.1
        (fun i => q.2.2.2.2 (leftMomentIndex i)) : Complex) *
      ((R324WithinHalfResidualPrefix.initial
          rho lam eps e0.2.1).residualIntegrand
        rho eps q.2.2.1 q.2.2.2.1
        (fun i => q.2.2.2.2 (rightMomentIndex i)) : Complex) *
      (r324ResidualPrimitiveSumProduct
        rho eps e0.1 e0.2.1 e0.2.2 q.2.2.2.2 : Complex) = _
  dsimp only [halves, splitInternal] at hroot hleftCoordinates hrightCoordinates
  unfold directIncomingRefinedRootOuter
  rw [hleftCoordinates, hrightCoordinates, hroot]
  unfold momentFourierPhase
  dsimp only [splitInternal, halves]
  ring

/-- The exact direct-incoming source density on the root parameter and
initial left carrier. -/
def directIncomingRefinedInitialSourceDensity
    (rho : SmoothCutoff) (lam eps : Real) {m : Nat}
    (kappaP kappaM : PartialPairing (Fin m))
    (alpha beta : Z4) (pi : kappaP.singles ≃ kappaM.singles)
    (q : R324IncomingExceptionalRootParameter rho lam eps kappaM ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaP).SurvivingCoordinate → T4)) : Complex :=
  (R324WithinHalfResidualPrefix.initial rho lam eps kappaP
    |>.incomingPhasedResidualDensity
      ((paperSecondOrderModeDecay alpha : Complex) *
        directIncomingRefinedRootOuter
          rho lam eps kappaP kappaM alpha beta pi q.1 q.2)
      alpha rho eps 0 q.1.1.1 q.2)

/-- The direct incoming operation on the genuine refined root.  It returns
both the integrability license required by the one-half transform and the
exact signed integral identity. -/
theorem integrable_and_r324RefinedPhysicalIntegral_eq_directIncomingSource
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (alpha beta : Z4) :
    Integrable
        (directIncomingRefinedInitialSourceDensity
          rho lam eps e0.1 e0.2.1 alpha beta e0.2.2)
        ((r324IncomingExceptionalRootParameterMeasure
          rho lam eps e0.2.1).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps e0.1).SurvivingCoordinate => paperMeasure)) ∧
      r324RefinedPhysicalIntegral rho eps m alpha beta p =
        ∫ q,
          directIncomingRefinedInitialSourceDensity
            rho lam eps e0.1 e0.2.1 alpha beta e0.2.2 q
          ∂((r324IncomingExceptionalRootParameterMeasure
            rho lam eps e0.2.1).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps e0.1).SurvivingCoordinate => paperMeasure)) := by
  let muParameter :=
    r324IncomingExceptionalRootParameterMeasure
      rho lam eps e0.2.1
  let muLeft :=
    Measure.pi fun _ :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps e0.1).SurvivingCoordinate => paperMeasure
  let regroup :=
    r324DirectIncomingRootMeasurableEquiv
      rho lam eps e0.1 e0.2.1
  let F :
      ((R324IncomingExceptionalRootParameter
          rho lam eps e0.2.1 ×
        ((R324WithinHalfResidualPrefix.initial
          rho lam eps e0.1).SurvivingCoordinate → T4)) × T4) → Complex :=
    fun q =>
      charT4 alpha q.2 *
        (((R324WithinHalfResidualPrefix.initial
            rho lam eps e0.1).residualIntegrand
          rho eps q.2 q.1.1.1.1
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps e0.1).reconstruct q.1.2) : Complex) *
          directIncomingRefinedRootOuter
            rho lam eps e0.1 e0.2.1 alpha beta e0.2.2 q.1.1 q.1.2)
  let G :=
    directIncomingRefinedInitialSourceDensity
      rho lam eps e0.1 e0.2.1 alpha beta e0.2.2
  have hregroup :
      MeasurePreserving regroup
        (r324PhysicalMeasure m)
        ((muParameter.prod muLeft).prod paperMeasure) := by
    simpa only [regroup, muParameter, muLeft] using
      measurePreserving_r324DirectIncomingRootMeasurableEquiv
        rho lam eps e0.1 e0.2.1
  have hpoint (q : R324PhysicalPoint m) :
      r324Flatten
          (momentRefinedPhysicalIntegrand
            rho eps m alpha beta p.1.1 p.2.1) q =
        F (regroup q) := by
    rw [r324Flatten_momentRefinedPhysicalIntegrand_eq_directIncoming_reindex
      (rho := rho) (lam := lam) (eps := eps)
      p e0 he0 alpha beta q]
    simp only [F, regroup, r324DirectIncomingRootMeasurableEquiv_apply]
  have hF : Integrable F
      ((muParameter.prod muLeft).prod paperMeasure) := by
    have hsource :=
      integrable_r324RefinedPhysicalIntegrand
        rho heps heps1 alpha beta p
    have hcomp : Integrable (F ∘ regroup)
        (r324PhysicalMeasure m) := by
      apply hsource.congr
      filter_upwards with q
      exact hpoint q
    exact
      (hregroup.integrable_comp_emb regroup.measurableEmbedding).mp hcomp
  have hsection (q :
      R324IncomingExceptionalRootParameter rho lam eps e0.2.1 ×
        ((R324WithinHalfResidualPrefix.initial
          rho lam eps e0.1).SurvivingCoordinate → T4)) :
      (∫ x, F (q, x) ∂paperMeasure) = G q := by
    simpa only [F, G, directIncomingRefinedInitialSourceDensity] using
      integral_charT4_mul_initialResidual_mul_const_eq_incomingPhased
        rho lam eps e0.1
        (directIncomingRefinedRootOuter
          rho lam eps e0.1 e0.2.1 alpha beta e0.2.2 q.1 q.2)
        alpha q.1.1.1 q.2
  have hG : Integrable G (muParameter.prod muLeft) := by
    apply hF.integral_prod_left.congr
    filter_upwards with q
    exact hsection q
  refine ⟨by simpa only [G, muParameter, muLeft] using hG, ?_⟩
  unfold r324RefinedPhysicalIntegral
  calc
    (∫ q,
        r324Flatten
          (momentRefinedPhysicalIntegrand
            rho eps m alpha beta p.1.1 p.2.1) q
        ∂(r324PhysicalMeasure m)) =
        ∫ q, F (regroup q) ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      filter_upwards with q
      exact hpoint q
    _ = ∫ q, F q ∂((muParameter.prod muLeft).prod paperMeasure) :=
      hregroup.integral_comp regroup.measurableEmbedding F
    _ = ∫ q, ∫ x, F (q, x) ∂paperMeasure
          ∂(muParameter.prod muLeft) := by
      rw [integral_prod _ hF]
    _ = ∫ q, G q ∂(muParameter.prod muLeft) := by
      apply integral_congr_ae
      filter_upwards with q
      exact hsection q
    _ = _ := by
      rfl

end R324WithinHalfResidualPrefix

end

end Anderson4D
