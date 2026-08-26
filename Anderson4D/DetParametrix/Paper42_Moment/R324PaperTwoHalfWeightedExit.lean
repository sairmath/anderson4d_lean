import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfUniformMajorant
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEEEEWeightedMajorant

/-!
# Common weighted exit for the actual two-half endpoint table

The four endpoint routes have already been evaluated, composed, and then
estimated before this file is used.  The only extra scalar in their common
majorant is the fixed, route-independent endpoint-mass compensation.  This
file absorbs that scalar into the primitive base and invokes the existing
complete-run exit; it introduces no new spatial or combinatorial carrier.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff

namespace R324WithinHalfResidualPrefix
namespace R324PaperTwoHalfEndpointRoutes

variable {rho : SmoothCutoff} {C K A B lam eps supportConstant : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode}

/-- Complete-run base after absorbing the single fixed scalar shared by all
sixteen literal endpoint patterns. -/
def twoHalfEndpointCompleteAbsorbedBase (A C K B : Real) : Real :=
  R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation *
    r324TwoHalfCompleteAbsorbedBase A C K B

theorem twoHalfEndpointCompleteAbsorbedBase_pos (A C K B : Real) :
    0 < twoHalfEndpointCompleteAbsorbedBase A C K B := by
  unfold twoHalfEndpointCompleteAbsorbedBase
  exact mul_pos
    (zero_lt_one.trans_le
      R324PaperHalfEndpointUniformBound.one_le_twoHalfEndpointMassCompensation)
    (r324TwoHalfCompleteAbsorbedBase_pos A C K B)

private theorem uniformCompensation_mul_primitiveInsertedMajorant_le
    (B lam eps supportConstant : Real) {n : Nat}
    (hn : 1 <= n) (z : T4) :
    R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation *
        primitiveInsertedMajorant B lam eps supportConstant n z <=
      primitiveInsertedMajorant
        (R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation * B)
        lam eps supportConstant n z := by
  let q :=
    R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation
  have hq : 1 <= q :=
    R324PaperHalfEndpointUniformBound.one_le_twoHalfEndpointMassCompensation
  have hqpow : q <= q ^ (2 * n) := by
    have h := pow_le_pow_right₀ hq (show 1 <= 2 * n by omega)
    simpa only [pow_one] using h
  have hcoefficient :
      q * (B * lam) ^ (2 * n) <= ((q * B) * lam) ^ (2 * n) := by
    calc
      _ <= q ^ (2 * n) * (B * lam) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right hqpow ((even_two_mul n).pow_nonneg _)
      _ = _ := by
        rw [show (q * B) * lam = q * (B * lam) by ring]
        exact (mul_pow q (B * lam) (2 * n)).symm
  have hbracket :
      0 <= ((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
          primitiveSupportIndicator supportConstant eps z +
        (1 / |Real.log eps| ^ 2) *
          (torusDistSq z + eps ^ 2)⁻¹ ^ 2 := by
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant eps z)
    · exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg eps))) 2)
  unfold primitiveInsertedMajorant
  change q * ((B * lam) ^ (2 * n) * _) <=
    ((q * B) * lam) ^ (2 * n) * _
  calc
    q * ((B * lam) ^ (2 * n) *
        (((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
            primitiveSupportIndicator supportConstant eps z +
          (1 / |Real.log eps| ^ 2) *
            (torusDistSq z + eps ^ 2)⁻¹ ^ 2)) =
        (q * (B * lam) ^ (2 * n)) *
          (((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
              primitiveSupportIndicator supportConstant eps z +
            (1 / |Real.log eps| ^ 2) *
              (torusDistSq z + eps ^ 2)⁻¹ ^ 2) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right hcoefficient hbracket

private theorem uniformCompensation_mul_integral_completeAbsorbed_le
    (A C K B lam : Real) {eps : Real} (heps : 0 < eps)
    (supportConstant : Real) {m : Nat} (hm : 1 <= m) :
    R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation *
        (∫ z : T4,
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure) <=
      ∫ z : T4,
        primitiveInsertedMajorant
          (twoHalfEndpointCompleteAbsorbedBase A C K B)
          lam eps supportConstant m z
        ∂paperMeasure := by
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_primitiveInsertedMajorant
      (r324TwoHalfCompleteAbsorbedBase A C K B)
      lam eps supportConstant m heps).const_mul _
  · exact integrable_primitiveInsertedMajorant
      (twoHalfEndpointCompleteAbsorbedBase A C K B)
      lam eps supportConstant m heps
  · filter_upwards with z
    simpa only [twoHalfEndpointCompleteAbsorbedBase] using
      uniformCompensation_mul_primitiveInsertedMajorant_le
        (r324TwoHalfCompleteAbsorbedBase A C K B)
        lam eps supportConstant hm z

/-- Numerical Step 4(A) exit for the common route-independent endpoint
compensation.  The endpoint density is already the result of all four
signed operations, so this theorem is the first place where its norm is
used. -/
theorem weighted_norm_le_endpointPatternAmbientMajorant_of_grouped_uniform
    (routes : R324PaperTwoHalfEndpointRoutes
      leftProviders rightProviders)
    (hA : 0 <= A) (hC : 0 <= C) (hK : 0 <= K)
    (hB : 0 <= B) (hlam : 0 < lam)
    (hleft : routes.terminal.left.state.active.Nonempty)
    (hright : routes.terminal.right.state.active.Nonempty)
    (pi : kappaP.singles ≃ kappaM.singles)
    (head : R324NestedCrossBlock kappaP kappaM pi)
    (tail : List (R324NestedCrossBlock kappaP kappaM pi))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial kappaP kappaM pi).remaining =
        head :: tail)
    (alpha beta : Z4)
    (physical : Complex)
    (endpointDensity :
      (routes.terminal.NestedCoordinate pi -> T4) -> Complex)
    (hendpoint :
      (fun v => ‖endpointDensity v‖) ≤ᵐ[
        Measure.pi fun _ : routes.terminal.NestedCoordinate pi =>
          paperMeasure]
        fun v =>
          (R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation *
            ((paperFourthOrderModeDecay alpha *
                paperFourthOrderModeDecay beta) *
              r324EndpointPrimitiveSacrificeProduct eps routes.cases)) *
            routes.terminal.initialNestedEndpointIntegratedGroupedMajorant
              routes.left.completedRoute.terminalScale
              routes.right.completedRoute.terminalScale
              hleft hright pi v)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hlog : 1 <= abs (Real.log eps))
    (hm : 1 <= m) (hmtrunc : m <= truncOrder eps)
    (hrunBound :
      let step :=
        r324InitialNestedCrossStepContext
          kappaP kappaM pi head tail hremaining
      let hleftInitial :
          (r324LeftHalfPullback step.residual.activeCarrier).Nonempty := by
        change (r324LeftHalfPullback
          (R324NestedCrossResidualPrefix.initial
            kappaP kappaM pi).activeCarrier).Nonempty
        rw [R324TwoHalfTerminalData.initial_leftHalfPullback_eq_terminalActive
          routes.terminal pi]
        exact hleft
      let hrightInitial :
          (r324RightHalfPullback step.residual.activeCarrier).Nonempty := by
        change (r324RightHalfPullback
          (R324NestedCrossResidualPrefix.initial
            kappaP kappaM pi).activeCarrier).Nonempty
        rw [R324TwoHalfTerminalData.initial_rightHalfPullback_eq_terminalActive
          routes.terminal pi]
        exact hright
      (∫ v : step.SurvivingCoordinate -> T4,
          routes.terminal.completeNestedRunDensity
            step hleftInitial hrightInitial v
          ∂Measure.pi fun _ : step.SurvivingCoordinate => paperMeasure) <=
        ∫ z : T4,
          primitiveInsertedMajorant B lam eps supportConstant
            step.residual.remainingOrder z
          ∂paperMeasure)
    (horder :
      (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaP).remainingOrder +
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).remainingOrder +
        (R324NestedCrossResidualPrefix.initial
          kappaP kappaM pi).remainingOrder = m)
    (hcollapse :
      (lamEps lam eps : Complex) ^
            (2 *
              ((R324WithinHalfResidualPrefix.initial
                    rho lam eps kappaP).remainingOrder +
                (R324WithinHalfResidualPrefix.initial
                    rho lam eps kappaM).remainingOrder)) *
          physical =
        ∫ v, endpointDensity v
          ∂Measure.pi fun _ : routes.terminal.NestedCoordinate pi =>
            paperMeasure) :
    abs (lamEps lam eps) ^ (2 * m) * ‖physical‖ <=
      (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (r324EndpointPrimitiveSacrificeProduct eps routes.cases *
          ∫ z : T4,
            primitiveInsertedMajorant
              (twoHalfEndpointCompleteAbsorbedBase A C K B)
              lam eps supportConstant m z
            ∂paperMeasure) := by
  let paperWeight : Real :=
    (paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta) *
      r324EndpointPrimitiveSacrificeProduct eps routes.cases
  let endpointWeight : Real :=
    R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation *
      paperWeight
  have hpaperWeight : 0 <= paperWeight := by
    exact mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (r324EndpointPrimitiveSacrificeProduct_nonneg eps routes.cases)
  have hendpointWeight : 0 <= endpointWeight :=
    mul_nonneg
      (zero_le_one.trans
        R324PaperHalfEndpointUniformBound.one_le_twoHalfEndpointMassCompensation)
      hpaperWeight
  have hendpointIntegral :=
    routes.terminal
      |>.integral_coupling_mul_norm_endpointDensity_le_ambientMajorant_of_grouped
        hA hC hK hB hlam
        routes.left.completedRoute.terminalScale
        routes.right.completedRoute.terminalScale
        routes.left.completedRoute.terminalReachable
        routes.right.completedRoute.terminalReachable
        routes.left.completedRoute.terminalCertificate
        routes.right.completedRoute.terminalCertificate
        hleft hright pi head tail hremaining
        endpointWeight hendpointWeight endpointDensity
        (by simpa only [endpointWeight, paperWeight] using hendpoint)
        heps heps1 hlog hm hmtrunc hrunBound
  have hweighted :=
    weighted_norm_le_of_collapsed_endpointIntegral
      (lam := lam) (ε := eps) (m := m)
      (leftOrder :=
        (R324WithinHalfResidualPrefix.initial
          rho lam eps kappaP).remainingOrder)
      (rightOrder :=
        (R324WithinHalfResidualPrefix.initial
          rho lam eps kappaM).remainingOrder)
      (crossOrder :=
        (R324NestedCrossResidualPrefix.initial
          kappaP kappaM pi).remainingOrder)
      horder physical endpointDensity hcollapse hendpointIntegral
  have hinflate := uniformCompensation_mul_integral_completeAbsorbed_le
    A C K B lam heps supportConstant hm
  calc
    _ <= endpointWeight *
        (∫ z : T4,
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure) := hweighted
    _ = paperWeight *
        (R324PaperHalfEndpointUniformBound.twoHalfEndpointMassCompensation *
          (∫ z : T4,
            primitiveInsertedMajorant
              (r324TwoHalfCompleteAbsorbedBase A C K B)
              lam eps supportConstant m z
            ∂paperMeasure)) := by
      dsimp only [endpointWeight]
      ring
    _ <= paperWeight *
        (∫ z : T4,
          primitiveInsertedMajorant
            (twoHalfEndpointCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left hinflate hpaperWeight
    _ = _ := by
      dsimp only [paperWeight]
      ring

end R324PaperTwoHalfEndpointRoutes
end R324WithinHalfResidualPrefix

end

end Anderson4D
