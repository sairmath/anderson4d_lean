import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfRouteAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedRoutedEndpointBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324InitialEndpointGroupedToCompleteRun

/-!
# The common weighted-majorant exit for the EE x EE endpoint branch

The signed endpoint calculation is branch-dependent, but its numerical
exit is not.  Once the two endpoint operations have produced a density on
the completed two-half carrier, the grouped Step 3 majorant, the complete
run, and the ambient-order scale absorption are exactly the same for all
sixteen endpoint patterns.

This file packages that common exit before specializing it to the literal
`EE x EE` signed density.  In particular, no endpoint norm is introduced
here: the caller supplies the pointwise estimate obtained only after its
four signed endpoint operations are complete.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff

namespace R324WithinHalfResidualPrefix

namespace R324IncomingExceptionalStopTraceAssembly

variable {rho : SmoothCutoff} {C lam eps K : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) -> Real}

/-- Projecting a right residual carrier to an endpoint stop does not change
the cross primitive factor.  This is the endpoint-stop analogue of the
alternating-transport projection lemma already used by the `ED` branch. -/
theorem r324ResidualPrimitiveSumProduct_eq_rightEndpointStopProjection
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    {right : R324WithinHalfResidualPrefix rho lam eps kappaM}
    {terminal : R322ExtractionStep m}
    (endpoint : R324WithinHalfEndpointStopAtTerminal terminal right)
    (pi : kappaP.singles ≃ kappaM.singles)
    (u : left.SurvivingCoordinate -> T4)
    (v : right.SurvivingCoordinate -> T4) :
    r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct left right (u, v)) =
      r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left endpoint.stop (u, endpoint.projection v)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
  · have hqRight : m <= q.val := by omega
    obtain ⟨i, hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq hqRight
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]
    exact endpoint.reconstruct_projection v
      ⟨i, endpoint.finalActive_subset_stop_active hiFinal⟩

/-- Right-half mirror of
`r324ResidualPrimitiveSumProduct_eq_leftOutgoingTerminalPost`.  Consuming
the retained right terminal leaves the cross-cut primitive factor unchanged,
because that factor sees only residual singles and all of those coordinates
survive in `terminalPost`. -/
theorem r324ResidualPrimitiveSumProduct_eq_rightOutgoingTerminalPost
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM initialScale)
    (outgoing :
      R324PaperOutgoingEndpointTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (u : left.SurvivingCoordinate -> T4)
    (v : outgoing.endpoint.stop.SurvivingCoordinate -> T4) :
    r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left outgoing.endpoint.stop (u, v)) =
      r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left outgoing.terminalPost
          (u,
            (outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining v).2)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
  · have hqRight : m <= q.val := by omega
    obtain ⟨i, hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq hqRight
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]
    have hiPost : i ∈ outgoing.terminalPost.state.active := by
      rw [outgoing.terminalPost_active_eq_finalActive]
      exact hiFinal
    let iPost : outgoing.terminalPost.SurvivingCoordinate :=
      ⟨i, hiPost⟩
    let iStop : outgoing.endpoint.stop.SurvivingCoordinate :=
      outgoing.endpoint.stop.postSurvivingCoordinate
        outgoing.terminalData.terminal []
        outgoing.endpoint.stop_remaining iPost
    calc
      outgoing.endpoint.stop.reconstruct v i = v iStop := by
        exact outgoing.endpoint.stop.reconstruct_surviving v iStop
      _ =
          (outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining v).2 iPost := by
        exact
          (outgoing.endpoint.stop
            |>.splitSurvivingPiMeasurableEquiv_apply_snd
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining v iPost).symm
      _ = outgoing.terminalPost.reconstruct
          ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            outgoing.terminalData.terminal []
            outgoing.endpoint.stop_remaining v).2) i := by
        exact
          (outgoing.terminalPost.reconstruct_surviving
            ((outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining v).2) iPost).symm

/-- Complete right-half projection from the initial residual carrier through
its exceptional incoming stop and the retained outgoing terminal.  It is the
coordinate identity needed when the completed left `EE` half is used as the
untouched parameter of the right parameterized `EE` theorem. -/
theorem r324ResidualPrimitiveSumProduct_eq_rightIncomingOutgoingPost
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM initialScale)
    (outgoing :
      R324PaperOutgoingEndpointTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (u : left.SurvivingCoordinate -> T4)
    (v : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate -> T4) :
    r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (u, v)) =
      r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left outgoing.terminalPost
          (u,
            (outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
              outgoing.terminalData.terminal []
              outgoing.endpoint.stop_remaining
              (outgoing.endpoint.projection
                ((data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  (data.trace.stopProjection v)).2))).2)) := by
  let after :=
    data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let afterCoordinates : after.SurvivingCoordinate -> T4 :=
    (data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
      (data.trace.stopProjection v)).2
  calc
    r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (u, v)) =
      r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left after (u, afterCoordinates)) :=
      data.r324ResidualPrimitiveSumProduct_eq_rightAfterHeadProjection
        left pi u v
    _ = r324ResidualPrimitiveSumProduct
        rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left outgoing.endpoint.stop
          (u, outgoing.endpoint.projection afterCoordinates)) :=
      r324ResidualPrimitiveSumProduct_eq_rightEndpointStopProjection
        left outgoing.endpoint pi u afterCoordinates
    _ = _ := by
      simpa only [after, afterCoordinates] using
        data.r324ResidualPrimitiveSumProduct_eq_rightOutgoingTerminalPost
          left outgoing pi u
            (outgoing.endpoint.projection afterCoordinates)

/-! The last Fubini move in the `EE x EE` branch.  It swaps the left free
outgoing variable past the completed right residual carrier, after all four
signed endpoint operations have already been performed. -/

/-- `(((left, firstLeft), right), firstRight)` regrouped as
`((left, right), (firstLeft, firstRight))`. -/
def r324EEEEEndpointRegroupMeasurableEquiv
    (L R : Type*) [MeasurableSpace L] [MeasurableSpace R] :
    (((L × T4) × R) × T4) ≃ᵐ ((L × R) × (T4 × T4)) :=
  (MeasurableEquiv.prodCongr
      ((MeasurableEquiv.prodAssoc
          (α := L) (β := T4) (γ := R)).trans
        ((MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl L)
            (MeasurableEquiv.prodComm : T4 × R ≃ᵐ R × T4)).trans
          (MeasurableEquiv.prodAssoc
            (α := L) (β := R) (γ := T4)).symm))
      (MeasurableEquiv.refl T4)).trans
    (MeasurableEquiv.prodAssoc
      (α := L × R) (β := T4) (γ := T4))

@[simp]
theorem r324EEEEEndpointRegroupMeasurableEquiv_apply
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (q : (((L × T4) × R) × T4)) :
    r324EEEEEndpointRegroupMeasurableEquiv L R q =
      ((q.1.1.1, q.1.2), (q.1.1.2, q.2)) :=
  rfl

@[simp]
theorem r324EEEEEndpointRegroupMeasurableEquiv_symm_apply
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (q : ((L × R) × (T4 × T4))) :
    (r324EEEEEndpointRegroupMeasurableEquiv L R).symm q =
      (((q.1.1, q.2.1), q.1.2), q.2.2) :=
  rfl

theorem measurePreserving_r324EEEEEndpointRegroupMeasurableEquiv
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (muL : Measure L) (muR : Measure R)
    [SFinite muL] [SFinite muR] :
    MeasurePreserving
      (r324EEEEEndpointRegroupMeasurableEquiv L R)
      ((((muL.prod paperMeasure).prod muR).prod paperMeasure))
      (((muL.prod muR).prod (paperMeasure.prod paperMeasure))) := by
  let middle : (L × T4) × R ≃ᵐ (L × R) × T4 :=
    (MeasurableEquiv.prodAssoc
        (α := L) (β := T4) (γ := R)).trans
      ((MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl L)
          (MeasurableEquiv.prodComm : T4 × R ≃ᵐ R × T4)).trans
        (MeasurableEquiv.prodAssoc
          (α := L) (β := R) (γ := T4)).symm)
  have hmiddle :
      MeasurePreserving middle
        ((muL.prod paperMeasure).prod muR)
        ((muL.prod muR).prod paperMeasure) := by
    exact
      (measurePreserving_prodAssoc muL muR paperMeasure).symm.comp
        (((MeasurePreserving.id muL).prod
            (Measure.measurePreserving_swap
              (μ := paperMeasure) (ν := muR))).comp
          (measurePreserving_prodAssoc muL paperMeasure muR))
  exact
    (measurePreserving_prodAssoc
      (muL.prod muR) paperMeasure paperMeasure).comp
      (hmiddle.prod (MeasurePreserving.id paperMeasure))

/-- Fubini in the only order used by the `EE x EE` branch.  The hypothesis
is joint integrability of the already completed signed four-endpoint
density, so this swap occurs strictly after all interval removals. -/
theorem integral_eeeeEndpoint_regroup
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (muL : Measure L) (muR : Measure R)
    [SFinite muL] [SFinite muR]
    (F : (((L × T4) × R) × T4) -> Complex)
    (hF : Integrable F
      (((muL.prod paperMeasure).prod muR).prod paperMeasure)) :
    (∫ u : L × T4, ∫ v : R, ∫ first : T4,
        F ((u, v), first) ∂paperMeasure ∂muR
      ∂(muL.prod paperMeasure)) =
      ∫ p : L × R, ∫ firstLeft : T4, ∫ firstRight : T4,
        F (((p.1, firstLeft), p.2), firstRight)
        ∂paperMeasure ∂paperMeasure ∂(muL.prod muR) := by
  let sigma := r324EEEEEndpointRegroupMeasurableEquiv L R
  have hsigma :
      MeasurePreserving sigma
        (((muL.prod paperMeasure).prod muR).prod paperMeasure)
        ((muL.prod muR).prod (paperMeasure.prod paperMeasure)) :=
    measurePreserving_r324EEEEEndpointRegroupMeasurableEquiv muL muR
  let G : ((L × R) × (T4 × T4)) -> Complex :=
    fun q => F (sigma.symm q)
  have hG : Integrable G
      ((muL.prod muR).prod (paperMeasure.prod paperMeasure)) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hF.congr
    filter_upwards with q
    show F q = G (sigma q)
    unfold G
    rw [MeasurableEquiv.symm_apply_apply]
  have hcombined :
      (∫ q, F q
          ∂(((muL.prod paperMeasure).prod muR).prod paperMeasure)) =
        ∫ q, G q
          ∂((muL.prod muR).prod (paperMeasure.prod paperMeasure)) := by
    rw [← hsigma.integral_comp' G]
    apply integral_congr_ae
    filter_upwards with q
    simp only [G, MeasurableEquiv.symm_apply_apply]
  have hfirstMarginal :
      Integrable
        (fun q : (L × T4) × R =>
          ∫ first : T4, F (q, first) ∂paperMeasure)
        ((muL.prod paperMeasure).prod muR) :=
    hF.integral_prod_left
  calc
    (∫ u : L × T4, ∫ v : R, ∫ first : T4,
        F ((u, v), first) ∂paperMeasure ∂muR
      ∂(muL.prod paperMeasure)) =
        ∫ q, F q
          ∂(((muL.prod paperMeasure).prod muR).prod paperMeasure) := by
      rw [integral_prod _ hF,
        integral_prod _ hfirstMarginal]
    _ = ∫ q, G q
          ∂((muL.prod muR).prod (paperMeasure.prod paperMeasure)) :=
      hcombined
    _ = ∫ p : L × R, ∫ firstLeft : T4, ∫ firstRight : T4,
          F (((p.1, firstLeft), p.2), firstRight)
          ∂paperMeasure ∂paperMeasure ∂(muL.prod muR) := by
      rw [integral_prod _ hG]
      apply integral_congr_ae
      filter_upwards [hG.prod_right_ae] with p hp
      rw [integral_prod _ hp]
      simp only [G, sigma,
        r324EEEEEndpointRegroupMeasurableEquiv_symm_apply]

/-! ## The first exceptional charge in the outgoing-stop budget -/

namespace R324IncomingExceptionalBudgetedStopTraceAssembly

/-- The complete after-head budget contains the first exceptional scale
together with its local block constant.  This is the exact scalar form
needed when the retained outgoing endpoint is estimated after the signed
incoming collapse. -/
theorem firstExceptionalScale_mul_K_le_afterHeadBudgetScale
    {A : Real}
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) kappaP)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) (hA : 1 <= A) :
    pack.firstExceptionalScale * K <= pack.afterHeadBudgetScale 0 := by
  let stopCtx : R324WithinHalfStepContext kappaP :=
    pack.data.trace.stopPrefix.headContext
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
  let p : Nat := residualBlockOrder pack.data.terminal.2
  let internalScale : Real :=
    r324WithinHalfInternalEdgeScaleProduct stopCtx pack.data.stopScale
  let budgetInternalScale : Real :=
    r324WithinHalfInternalEdgeScaleProduct stopCtx pack.stopBudgetScale
  have hout : pack.stopBudgetScale stopCtx.outgoingSlot = A := by
    exact pack.budgetReachable.outgoingScale_eq_base
      pack.data.trace.stopPrefix rfl pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
  have hafterEq : pack.afterHeadBudgetScale 0 =
      A * (budgetInternalScale * A) * (C * lam) ^ (2 * p) * K := by
    dsimp only [R324IncomingExceptionalBudgetedStopTraceAssembly.afterHeadBudgetScale,
      budgetInternalScale, stopCtx, p] at hout ⊢
    rw [← pack.data.stop_predecessorSlot_eq_zero,
      pack.data.trace.stopPrefix.budgetUpdatedEdgeScale_predecessor,
      pack.data.trace.stopPrefix.headBlockScaleProduct_eq_internal_mul_outgoing]
    rw [pack.data.stop_predecessorSlot_eq_zero,
      pack.stopBudget_zero_eq_base, hout]
  have hinternalLe : internalScale <= budgetInternalScale := by
    dsimp only [internalScale, budgetInternalScale,
      r324WithinHalfInternalEdgeScaleProduct, stopCtx]
    apply Finset.prod_le_prod
    · intro j _hj
      exact pack.data.trace.stopCertificate.scale_pos
        (pack.data.stopContext.internalSlot j) |>.le
    · intro j _hj
      exact pack.stopScale_le (pack.data.stopContext.internalSlot j)
  have hcoreNonneg :
      0 <= budgetInternalScale * (C * lam) ^ (2 * p) * K := by
    exact mul_nonneg
      (mul_nonneg
        pack.budgetCertificate.internalEdgeScaleProduct_pos.le
        (pow_nonneg (mul_nonneg hC hlam) _))
      hK
  have hAA : 1 <= A * A := by
    calc
      1 <= A := hA
      _ = A * 1 := by ring
      _ <= A * A :=
        mul_le_mul_of_nonneg_left hA (zero_le_one.trans hA)
  change internalScale * (C * lam) ^ (2 * p) * K <=
    pack.afterHeadBudgetScale 0
  calc
    internalScale * (C * lam) ^ (2 * p) * K <=
        budgetInternalScale * (C * lam) ^ (2 * p) * K :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinternalLe
          (pow_nonneg (mul_nonneg hC hlam) _)) hK
    _ = (budgetInternalScale * (C * lam) ^ (2 * p) * K) * 1 := by
      ring
    _ <= (budgetInternalScale * (C * lam) ^ (2 * p) * K) *
        (A * A) :=
      mul_le_mul_of_nonneg_left hAA hcoreNonneg
    _ = A * (budgetInternalScale * A) *
        (C * lam) ^ (2 * p) * K := by
      ring
    _ = pack.afterHeadBudgetScale 0 := hafterEq.symm

/-- After the first signed exceptional collapse, the one remaining Fourier
decay is explicit and the complete endpoint-stop budget pays the multiplier
and the primitive defect. -/
theorem norm_multiplier_mul_squaredDecay_defect_le_stopBudget
    {A : Real} {terminal : R322ExtractionStep m} {mode : Z4}
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) kappaP)
    (endpoint : R324BudgetedEndpointStopAtTerminal
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) terminal
      (pack.data.trace.stopPrefix.afterHead
        pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq)
      pack.afterHeadBudgetScale mode)
    (headBudget : R324WithinHalfInsertedExceptionalHeadBudget
      rho C lam eps K kappaP mode)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 0 <= K) (hA : 1 <= A) :
    ‖endpoint.endpoint.multiplier mode *
        ((paperSecondOrderModeDecay mode : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder pack.data.terminal.2)
            pack.data.stopContext.one_le_blockOrder
            pack.data.stopContext.internalEdges mode)‖ <=
      paperSecondOrderModeDecay mode * endpoint.stopBudgetScale 0 := by
  have hhead :=
    headBudget pack.data.trace.stopPrefix pack.data.terminal
      pack.data.suffix pack.data.trace.stopPrefix_remaining_eq
      pack.data.stopScale pack.data.trace.stopCertificate
  have hhead' :
      ‖pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
          pack.data.terminal pack.data.suffix
          pack.data.trace.stopPrefix_remaining_eq mode‖ <=
        pack.firstExceptionalScale * K := by
    simpa only [R324IncomingExceptionalBudgetedStopTraceAssembly.firstExceptionalScale,
      R324IncomingExceptionalStopTraceAssembly.stopContext,
      R324WithinHalfResidualPrefix.headContext, mul_assoc] using hhead
  have hfirstK :=
    pack.firstExceptionalScale_mul_K_le_afterHeadBudgetScale
      hC hlam hK hA
  have hheadBudget :
      ‖pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
          pack.data.terminal pack.data.suffix
          pack.data.trace.stopPrefix_remaining_eq mode‖ <=
        pack.afterHeadBudgetScale 0 :=
    hhead'.trans hfirstK
  have hmultiplied :
      ‖endpoint.endpoint.multiplier mode‖ *
          ‖pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
            pack.data.terminal pack.data.suffix
            pack.data.trace.stopPrefix_remaining_eq mode‖ <=
        endpoint.stopBudgetScale 0 := by
    exact (mul_le_mul_of_nonneg_left hheadBudget
      (norm_nonneg _)).trans endpoint.multiplier_budget
  have hdecay : 0 <= paperSecondOrderModeDecay mode :=
    paperSecondOrderModeDecay_nonneg mode
  calc
    ‖endpoint.endpoint.multiplier mode *
        ((paperSecondOrderModeDecay mode : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder pack.data.terminal.2)
            pack.data.stopContext.one_le_blockOrder
            pack.data.stopContext.internalEdges mode)‖ =
        paperSecondOrderModeDecay mode *
          (‖endpoint.endpoint.multiplier mode‖ *
            ‖pack.data.trace.stopPrefix.incomingExceptionalHeadCollapseFactor
              pack.data.terminal pack.data.suffix
              pack.data.trace.stopPrefix_remaining_eq mode‖) := by
      unfold R324WithinHalfResidualPrefix.incomingExceptionalHeadCollapseFactor
      simp only [R324IncomingExceptionalStopTraceAssembly.stopContext,
        norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hdecay]
      ring
    _ <= paperSecondOrderModeDecay mode * endpoint.stopBudgetScale 0 :=
      mul_le_mul_of_nonneg_left hmultiplied hdecay

end R324IncomingExceptionalBudgetedStopTraceAssembly

/-! ## The literal signed `EE x EE` carrier -/

variable {leftScale rightScale : Fin (m + 1) -> Real}

/-- Everything produced by the completed left `EE` endpoint operation
except the untouched right residual core and the cross primitive factor.
The outgoing primitive and its external Fourier variable are still kept as
one signed density; no norm occurs in this definition. -/
def eeeeLeftEndpointFactor
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (alpha beta : Z4)
    (v : leftOutgoing.terminalPost.SurvivingCoordinate -> T4)
    (first : T4) : Complex :=
  leftOutgoing.outgoingEndpointDefectDensity
    (fun _ =>
      leftOutgoing.endpoint.multiplier alpha *
        ((paperSecondOrderModeDecay alpha : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder leftData.terminal.2)
            leftData.stopContext.one_le_blockOrder
            leftData.stopContext.internalEdges alpha))
    alpha beta 0 v first

/-- Coefficient left untouched while the right `EE` endpoint operation is
performed.  Its only dependence on the right post-terminal coordinates is
the complete grouped cross primitive factor. -/
def eeeeRightPostCoefficient
    {rightResidual : R324WithinHalfResidualPrefix rho lam eps kappaM}
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal rightResidual)
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4)
    (u :
      (leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4)
    (v : rightOutgoing.terminalPost.SurvivingCoordinate -> T4) : Complex :=
  leftData.eeeeLeftEndpointFactor leftOutgoing alpha beta u.1 u.2 *
    (r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        leftOutgoing.terminalPost rightOutgoing.terminalPost (u.1, v)) :
      Complex)

/-- The exact right initial-source density after the completed left `EE`
carrier has been moved into the parameter slot. -/
def eeeeRightInitialSourceDensity
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4) :
    ((T4 ×
        (T4 ×
          ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4))) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate -> T4)) -> Complex :=
  rightData.incomingExceptionalInitialSourceDensity
    (-alpha)
    (fun omega : T4 ×
        ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) =>
      omega.1)
    (fun omega post =>
      charT4 (-beta) omega.1 *
        leftData.eeeeRightPostCoefficient
          leftOutgoing rightOutgoing pi alpha beta omega.2
          ((rightOutgoing.endpoint.stop
            |>.splitSurvivingPiMeasurableEquiv
              rightOutgoing.terminalData.terminal []
              rightOutgoing.endpoint.stop_remaining
              (rightOutgoing.endpoint.projection post)).2))

/-- The corresponding right stop-source density.  It differs from the
previous definition only by the residual carrier on which the signed trace
is evaluated. -/
def eeeeRightStopSourceDensity
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4) :
    ((T4 ×
        (T4 ×
          ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4))) ×
      (rightData.trace.stopPrefix.SurvivingCoordinate -> T4)) -> Complex :=
  rightData.incomingExceptionalStopSourceDensity
    (-alpha)
    (fun omega : T4 ×
        ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) =>
      omega.1)
    (fun omega post =>
      charT4 (-beta) omega.1 *
        leftData.eeeeRightPostCoefficient
          leftOutgoing rightOutgoing pi alpha beta omega.2
          ((rightOutgoing.endpoint.stop
            |>.splitSurvivingPiMeasurableEquiv
              rightOutgoing.terminalData.terminal []
              rightOutgoing.endpoint.stop_remaining
              (rightOutgoing.endpoint.projection post)).2))

/-- Signed right endpoint-stop density after the right exceptional head and
all proper-prefix intervals have been removed. -/
def eeeeRightEndpointIntegrand
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4) :
    ((T4 ×
        ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4)) ×
      (rightOutgoing.endpoint.stop.SurvivingCoordinate -> T4)) -> Complex :=
  fun q =>
    rightOutgoing.endpoint.stop.incomingPhasedResidualDensity
      (rightOutgoing.endpoint.multiplier (-alpha) *
        ((paperSecondOrderModeDecay (-alpha) : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder rightData.terminal.2)
            rightData.stopContext.one_le_blockOrder
            rightData.stopContext.internalEdges (-alpha) *
          leftData.eeeeRightPostCoefficient
            leftOutgoing rightOutgoing pi alpha beta q.1.2
            ((rightOutgoing.endpoint.stop
              |>.splitSurvivingPiMeasurableEquiv
                rightOutgoing.terminalData.terminal []
                rightOutgoing.endpoint.stop_remaining q.2).2)))
      (-alpha) rho eps 0 q.1.1 q.2

/-- Literal signed terminal density after all four exceptional endpoint
operations.  The two free outgoing variables are still integrated outside
this function; no absolute value has been taken. -/
def eeeeFinalRawEndpointDensity
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4)
    (u : (leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4)
    (v : rightOutgoing.terminalPost.SurvivingCoordinate -> T4)
    (first : T4) : Complex :=
  rightOutgoing.outgoingEndpointDefectDensity
    (fun post =>
      rightOutgoing.endpoint.multiplier (-alpha) *
        ((paperSecondOrderModeDecay (-alpha) : Complex) ^ 2 *
          incomingExceptionalPrimitiveDefect rho lam eps
            (residualBlockOrder rightData.terminal.2)
            rightData.stopContext.one_le_blockOrder
            rightData.stopContext.internalEdges (-alpha) *
          leftData.eeeeRightPostCoefficient
            leftOutgoing rightOutgoing pi alpha beta u post))
    (-alpha) (-beta) 0 v first

/-- The literal completed two-half carrier produced by the two retained
outgoing exceptional terminals. -/
def eeeeTerminalData
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq)) :
    R324TwoHalfTerminalData rho lam eps kappaP kappaM where
  left := leftOutgoing.terminalPost
  right := rightOutgoing.terminalPost
  left_remaining := leftOutgoing.terminalPost_remaining
  right_remaining := rightOutgoing.terminalPost_remaining
  left_processed := leftOutgoing.terminalPost_processed_eq_schedule
  right_processed := rightOutgoing.terminalPost_processed_eq_schedule

/-- Joint product measure for the already completed four-endpoint signed
density, in paper order `left post, left free endpoint, right post, right
free endpoint`. -/
def eeeeFinalRawEndpointMeasure
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq)) :
    Measure
      ((((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ×
          (rightOutgoing.terminalPost.SurvivingCoordinate -> T4)) × T4) :=
  ((((Measure.pi fun _ :
        leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
      paperMeasure).prod
    (Measure.pi fun _ :
      rightOutgoing.terminalPost.SurvivingCoordinate => paperMeasure)).prod
    paperMeasure)

/-- The four signed endpoint operations, with their two free outgoing
variables integrated, reindexed onto the literal initial nested carrier. -/
def eeeeNestedEndpointDensity
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4)
    (v : (leftData.eeeeTerminalData leftOutgoing
      rightData rightOutgoing).NestedCoordinate pi -> T4) : Complex :=
  let terminal :=
    leftData.eeeeTerminalData leftOutgoing rightData rightOutgoing
  let p := (terminal.terminalProductPiMeasurableEquivNested pi).symm v
  ∫ firstLeft : T4, ∫ firstRight : T4,
    leftData.eeeeFinalRawEndpointDensity leftOutgoing
      rightData rightOutgoing pi alpha beta (p.1, firstLeft) p.2 firstRight
    ∂paperMeasure ∂paperMeasure

/-- Exact final Fubini/reindexing bridge from the parameterized right `EE`
output to the nested endpoint carrier consumed by the grouped Step 3
majorant. -/
theorem integral_eeeeFinalRaw_eq_integral_nestedEndpointDensity
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4)
    (hraw :
      Integrable
        (fun q :
            ((((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ×
                (rightOutgoing.terminalPost.SurvivingCoordinate -> T4)) ×
              T4) =>
          leftData.eeeeFinalRawEndpointDensity leftOutgoing
            rightData rightOutgoing pi alpha beta q.1.1 q.1.2 q.2)
        (leftData.eeeeFinalRawEndpointMeasure leftOutgoing
          rightData rightOutgoing)) :
    (∫ u :
          (leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4,
        ∫ v : rightOutgoing.terminalPost.SurvivingCoordinate -> T4,
          ∫ first : T4,
            leftData.eeeeFinalRawEndpointDensity leftOutgoing
              rightData rightOutgoing pi alpha beta u v first
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure
        ∂((Measure.pi fun _ => paperMeasure).prod paperMeasure)) =
      ∫ v : (leftData.eeeeTerminalData leftOutgoing
          rightData rightOutgoing).NestedCoordinate pi -> T4,
        leftData.eeeeNestedEndpointDensity leftOutgoing
          rightData rightOutgoing pi alpha beta v
        ∂Measure.pi fun _ => paperMeasure := by
  let terminal :=
    leftData.eeeeTerminalData leftOutgoing rightData rightOutgoing
  let muLeft :=
    Measure.pi fun _ :
      leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure
  let muRight :=
    Measure.pi fun _ :
      rightOutgoing.terminalPost.SurvivingCoordinate => paperMeasure
  let F :
      ((((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ×
          (rightOutgoing.terminalPost.SurvivingCoordinate -> T4)) × T4) ->
        Complex :=
    fun q =>
      leftData.eeeeFinalRawEndpointDensity leftOutgoing
        rightData rightOutgoing pi alpha beta q.1.1 q.1.2 q.2
  let productDensity :
      ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) ×
        (rightOutgoing.terminalPost.SurvivingCoordinate -> T4)) -> Complex :=
    fun p =>
      ∫ firstLeft : T4, ∫ firstRight : T4,
        F (((p.1, firstLeft), p.2), firstRight)
        ∂paperMeasure ∂paperMeasure
  have hreorder := integral_eeeeEndpoint_regroup muLeft muRight F hraw
  have hp := terminal.measurePreserving_terminalProductPiMeasurableEquivNested pi
  have hnested :
      (∫ p, productDensity p ∂(muLeft.prod muRight)) =
        ∫ v : terminal.NestedCoordinate pi -> T4,
          leftData.eeeeNestedEndpointDensity leftOutgoing
            rightData rightOutgoing pi alpha beta v
          ∂Measure.pi fun _ => paperMeasure := by
    rw [← hp.integral_comp'
      (leftData.eeeeNestedEndpointDensity leftOutgoing
        rightData rightOutgoing pi alpha beta)]
    apply integral_congr_ae
    filter_upwards with p
    simp only [eeeeNestedEndpointDensity, terminal,
      MeasurableEquiv.symm_apply_apply, productDensity, F]
  exact hreorder.trans hnested

/-- After the left `EE` operation, reassociating
`((right endpoints, right initial coordinates), left post, left first)`
produces exactly the initial-source density consumed by the parameterized
right `EE` theorem.  The cross factor is moved to the right post-terminal
carrier only by the two exact projection lemmas above. -/
theorem outgoingEndpointDefectDensity_eq_rightExceptionalInitialSource
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4)
    (s : (T4 × T4) ×
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate -> T4))
    (v : leftOutgoing.terminalPost.SurvivingCoordinate -> T4)
    (first : T4) :
    leftOutgoing.outgoingEndpointDefectDensity
        (leftData.incomingExceptionalRefinedRootOutgoingPostCoefficient
          leftOutgoing alpha beta pi s)
        alpha beta 0 v first =
      rightData.incomingExceptionalInitialSourceDensity
        (-alpha)
        (fun omega : T4 ×
          ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) =>
            omega.1)
        (fun omega post =>
          charT4 (-beta) omega.1 *
            leftData.eeeeRightPostCoefficient
              leftOutgoing rightOutgoing pi alpha beta omega.2
              ((rightOutgoing.endpoint.stop
                |>.splitSurvivingPiMeasurableEquiv
                  rightOutgoing.terminalData.terminal []
                  rightOutgoing.endpoint.stop_remaining
                  (rightOutgoing.endpoint.projection post)).2))
        ((s.1.1, (s.1.2, (v, first))), s.2) := by
  have hcross :=
    rightData.r324ResidualPrimitiveSumProduct_eq_rightIncomingOutgoingPost
      leftOutgoing.terminalPost rightOutgoing pi v s.2
  unfold eeeeRightPostCoefficient eeeeLeftEndpointFactor
    incomingExceptionalRefinedRootOutgoingPostCoefficient
    R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
    R324PaperOutgoingEndpointTerminal.terminalSplitOuter
    incomingExceptionalInitialSourceDensity
  dsimp only
  rw [hcross]
  ring

/-- The completed left exceptional endpoint carrier is exactly the
untouched parameter carrier required by the right parameterized `EE`
theorem.  This is only a reassociation of product measure, followed by the
pointwise signed identity above; in particular, it takes no norm and loses
no cancellation. -/
theorem
    integrable_and_integral_leftExceptional_eq_rightExceptionalInitialSource
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4)
    (hleftIntegrable :
      Integrable
        (fun q :
            (((T4 × T4) ×
                ((R324WithinHalfResidualPrefix.initial
                  rho lam eps kappaM).SurvivingCoordinate -> T4)) ×
              ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) ×
                T4)) =>
          leftOutgoing.outgoingEndpointDefectDensity
            (leftData.incomingExceptionalRefinedRootOutgoingPostCoefficient
              leftOutgoing alpha beta pi q.1)
            alpha beta 0 q.2.1 q.2.2)
        ((((paperMeasure.prod paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate => paperMeasure)).prod
          ((Measure.pi fun _ :
              leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
            paperMeasure)))) :
    let muLeft :=
      Measure.pi fun _ :
        leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure
    let muU := muLeft.prod paperMeasure
    let muRight :=
      Measure.pi fun _ :
        (R324WithinHalfResidualPrefix.initial
          rho lam eps kappaM).SurvivingCoordinate => paperMeasure
    Integrable
        (rightData.incomingExceptionalInitialSourceDensity
          (-alpha)
          (fun omega : T4 ×
              ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) =>
            omega.1)
          (fun omega post =>
            charT4 (-beta) omega.1 *
              leftData.eeeeRightPostCoefficient
                leftOutgoing rightOutgoing pi alpha beta omega.2
                ((rightOutgoing.endpoint.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    rightOutgoing.terminalData.terminal []
                    rightOutgoing.endpoint.stop_remaining
                    (rightOutgoing.endpoint.projection post)).2)))
        ((paperMeasure.prod (paperMeasure.prod muU)).prod muRight) ∧
      (   (∫ s : (T4 × T4) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate -> T4),
              ∫ v : leftOutgoing.terminalPost.SurvivingCoordinate -> T4,
                ∫ first : T4,
                  leftOutgoing.outgoingEndpointDefectDensity
                    (leftData
                      |>.incomingExceptionalRefinedRootOutgoingPostCoefficient
                        leftOutgoing alpha beta pi s)
                    alpha beta 0 v first
                  ∂paperMeasure
                ∂muLeft
              ∂((paperMeasure.prod paperMeasure).prod muRight)) =
          ∫ p,
            rightData.incomingExceptionalInitialSourceDensity
              (-alpha)
              (fun omega : T4 ×
                  ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) =>
                omega.1)
              (fun omega post =>
                charT4 (-beta) omega.1 *
                  leftData.eeeeRightPostCoefficient
                    leftOutgoing rightOutgoing pi alpha beta omega.2
                    ((rightOutgoing.endpoint.stop
                      |>.splitSurvivingPiMeasurableEquiv
                        rightOutgoing.terminalData.terminal []
                        rightOutgoing.endpoint.stop_remaining
                        (rightOutgoing.endpoint.projection post)).2)) p
            ∂((paperMeasure.prod (paperMeasure.prod muU)).prod muRight)) := by
  dsimp only
  let muLeft :=
    Measure.pi fun _ :
      leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure
  let muU := muLeft.prod paperMeasure
  let muRight :=
    Measure.pi fun _ :
      (R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate => paperMeasure
  let muOuter := (paperMeasure.prod paperMeasure).prod muRight
  let leftF :
      (((T4 × T4) ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).SurvivingCoordinate -> T4)) ×
        ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4)) ->
          Complex :=
    fun q =>
      leftOutgoing.outgoingEndpointDefectDensity
        (leftData.incomingExceptionalRefinedRootOutgoingPostCoefficient
          leftOutgoing alpha beta pi q.1)
        alpha beta 0 q.2.1 q.2.2
  let rightF :
      ((T4 ×
          (T4 ×
            ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4))) ×
        ((R324WithinHalfResidualPrefix.initial
          rho lam eps kappaM).SurvivingCoordinate -> T4)) -> Complex :=
    fun p =>
      rightData.incomingExceptionalInitialSourceDensity
        (-alpha)
        (fun omega : T4 ×
            ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) =>
          omega.1)
        (fun omega post =>
          charT4 (-beta) omega.1 *
            leftData.eeeeRightPostCoefficient
              leftOutgoing rightOutgoing pi alpha beta omega.2
              ((rightOutgoing.endpoint.stop
                |>.splitSurvivingPiMeasurableEquiv
                  rightOutgoing.terminalData.terminal []
                  rightOutgoing.endpoint.stop_remaining
                  (rightOutgoing.endpoint.projection post)).2)) p
  let sigma :=
    r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
      T4 T4
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps kappaM).SurvivingCoordinate -> T4)
      ((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4)
  have hsigma :
      MeasurePreserving sigma
        (muOuter.prod muU)
        ((paperMeasure.prod (paperMeasure.prod muU)).prod muRight) :=
    measurePreserving_r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
      paperMeasure paperMeasure muRight muU
  have hpoint : ∀ q, leftF q = rightF (sigma q) := by
    intro q
    exact
      leftData.outgoingEndpointDefectDensity_eq_rightExceptionalInitialSource
        leftOutgoing rightData rightOutgoing pi alpha beta
        q.1 q.2.1 q.2.2
  have hright :
      Integrable rightF
        ((paperMeasure.prod (paperMeasure.prod muU)).prod muRight) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hleftIntegrable.congr
    filter_upwards with q
    exact hpoint q
  refine ⟨hright, ?_⟩
  calc
    (∫ s : (T4 × T4) ×
          ((R324WithinHalfResidualPrefix.initial
            rho lam eps kappaM).SurvivingCoordinate -> T4),
        ∫ v : leftOutgoing.terminalPost.SurvivingCoordinate -> T4,
          ∫ first : T4,
            leftOutgoing.outgoingEndpointDefectDensity
              (leftData.incomingExceptionalRefinedRootOutgoingPostCoefficient
                leftOutgoing alpha beta pi s)
              alpha beta 0 v first
            ∂paperMeasure
          ∂muLeft
        ∂muOuter) =
      ∫ s, ∫ u, leftF (s, u) ∂muU ∂muOuter := by
        apply integral_congr_ae
        filter_upwards [hleftIntegrable.prod_right_ae] with s hs
        simpa only [muLeft, muU, leftF] using (integral_prod _ hs).symm
    _ = ∫ q, leftF q ∂(muOuter.prod muU) := by
      exact (integral_prod _ hleftIntegrable).symm
    _ = ∫ p, rightF p
          ∂((paperMeasure.prod (paperMeasure.prod muU)).prod muRight) := by
      rw [← hsigma.integral_comp' rightF]
      exact integral_congr_ae
        (Filter.Eventually.of_forall hpoint)

/-- Second half of the exact `EE x EE` splice.  The first-half collapse and
the product-measure reassociation are summarized by `hleftCollapse`; the
right parameterized `EE` theorem is then applied literally with modes
`-alpha,-beta`.  This is the paper's four signed endpoint operations, with
the norm still postponed. -/
theorem lamEps_pow_twoHalfPhysical_eq_eeeeFinalRaw_of_regroupedCollapse
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4) (physical : Complex)
    (hm : 0 < m)
    (hG : ∀ j, MemEClassT4 (rightData.stopContext.internalEdges j))
    (hincoming :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder rightData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder rightData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder rightData.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder rightData.terminal.2)
              kappaB.1 rightData.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder rightData.terminal.2)
                rightData.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hcurrent :
      Integrable
        (leftData.eeeeRightInitialSourceDensity
          leftOutgoing rightData rightOutgoing pi alpha beta)
        ((paperMeasure.prod
          (paperMeasure.prod
            ((Measure.pi fun _ :
                leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
              paperMeasure))).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaM).SurvivingCoordinate => paperMeasure)))
    (hsource :
      Integrable
        (leftData.eeeeRightStopSourceDensity
          leftOutgoing rightData rightOutgoing pi alpha beta)
        ((paperMeasure.prod
          (paperMeasure.prod
            ((Measure.pi fun _ :
                leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
              paperMeasure))).prod
          (Measure.pi fun _ :
            rightData.trace.stopPrefix.SurvivingCoordinate => paperMeasure)))
    (hpred :
      r324WithinHalfPredecessorSlot rightOutgoing.endpoint.stop.state
          rightOutgoing.terminalData.terminal ≠ 0)
    (hactive : rightOutgoing.terminalPost.state.active.Nonempty)
    (hendpoint :
      Integrable
        (leftData.eeeeRightEndpointIntegrand
          leftOutgoing rightData rightOutgoing pi alpha beta)
        ((paperMeasure.prod
          ((Measure.pi fun _ :
              leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
            paperMeasure)).prod
          (Measure.pi fun _ :
            rightOutgoing.endpoint.stop.SurvivingCoordinate => paperMeasure)))
    (houtgoing :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder
                rightOutgoing.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder rightOutgoing.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              rightOutgoing.terminalData.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder
                rightOutgoing.terminalData.terminal.2)
              kappaB.1 rightOutgoing.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder rightOutgoing.terminalData.terminal.2)
                rightOutgoing.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure))
    (hleftCollapse :
      (lamEps lam eps : Complex) ^
            (2 * (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaP).remainingOrder) * physical =
        ∫ p,
          leftData.eeeeRightInitialSourceDensity
            leftOutgoing rightData rightOutgoing pi alpha beta p
          ∂((paperMeasure.prod
            (paperMeasure.prod
              ((Measure.pi fun _ :
                  leftOutgoing.terminalPost.SurvivingCoordinate =>
                    paperMeasure).prod paperMeasure))).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate => paperMeasure))) :
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * physical =
      ∫ u :
          (leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4,
        ∫ v : rightOutgoing.terminalPost.SurvivingCoordinate -> T4,
          ∫ first : T4,
            leftData.eeeeFinalRawEndpointDensity leftOutgoing
              rightData rightOutgoing pi alpha beta u v first
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure
        ∂((Measure.pi fun _ => paperMeasure).prod paperMeasure) := by
  let muLeft :=
    Measure.pi fun _ :
      leftOutgoing.terminalPost.SurvivingCoordinate => paperMeasure
  let muU := muLeft.prod paperMeasure
  have hright :=
    rightData
      |>.lamEps_pow_integral_initialResidual_eq_singleParameter_incomingExceptional_outgoingExceptional
        rightOutgoing muU
        (leftData.eeeeRightPostCoefficient
          leftOutgoing rightOutgoing pi alpha beta)
        (-alpha) (-beta) hm hG hincoming
        (by
          simpa only [eeeeRightInitialSourceDensity, muU, muLeft] using hcurrent)
        (by
          simpa only [eeeeRightStopSourceDensity, muU, muLeft] using hsource)
        hpred hactive
        (by
          change Integrable
            (leftData.eeeeRightEndpointIntegrand
              leftOutgoing rightData rightOutgoing pi alpha beta)
            ((paperMeasure.prod muU).prod
              (Measure.pi fun _ :
                rightOutgoing.endpoint.stop.SurvivingCoordinate =>
                  paperMeasure))
          simpa only [muU, muLeft] using hendpoint)
        houtgoing
  let leftOrder :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaP).remainingOrder
  let rightOrder :=
    (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).remainingOrder
  calc
    (lamEps lam eps : Complex) ^ (2 * (leftOrder + rightOrder)) * physical =
        (lamEps lam eps : Complex) ^ (2 * rightOrder) *
          ((lamEps lam eps : Complex) ^ (2 * leftOrder) * physical) := by
      rw [Nat.mul_add, pow_add]
      ring
    _ = (lamEps lam eps : Complex) ^ (2 * rightOrder) *
        (∫ p,
          leftData.eeeeRightInitialSourceDensity
            leftOutgoing rightData rightOutgoing pi alpha beta p
          ∂((paperMeasure.prod (paperMeasure.prod muU)).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate => paperMeasure))) := by
      rw [hleftCollapse]
    _ = _ := by
      simpa only [eeeeRightInitialSourceDensity,
        eeeeFinalRawEndpointDensity, leftOrder, rightOrder, muU, muLeft]
        using hright

/-- Package the exact four-endpoint output on the nested carrier expected by
the common weighted-majorant exit. -/
theorem lamEps_pow_twoHalfPhysical_eq_eeeeNested_of_raw
    (leftData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaP leftScale)
    (leftOutgoing :
      R324PaperOutgoingEndpointTerminal
        (leftData.trace.stopPrefix.afterHead
          leftData.terminal leftData.suffix
          leftData.trace.stopPrefix_remaining_eq))
    (rightData :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappaM rightScale)
    (rightOutgoing :
      R324PaperOutgoingEndpointTerminal
        (rightData.trace.stopPrefix.afterHead
          rightData.terminal rightData.suffix
          rightData.trace.stopPrefix_remaining_eq))
    (pi : kappaP.singles ≃ kappaM.singles)
    (alpha beta : Z4) (physical : Complex)
    (hrawCollapse :
      (lamEps lam eps : Complex) ^
            (2 *
              ((R324WithinHalfResidualPrefix.initial
                  rho lam eps kappaP).remainingOrder +
                (R324WithinHalfResidualPrefix.initial
                  rho lam eps kappaM).remainingOrder)) * physical =
        ∫ u :
            (leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4,
          ∫ v : rightOutgoing.terminalPost.SurvivingCoordinate -> T4,
            ∫ first : T4,
              leftData.eeeeFinalRawEndpointDensity leftOutgoing
                rightData rightOutgoing pi alpha beta u v first
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure
          ∂((Measure.pi fun _ => paperMeasure).prod paperMeasure))
    (hraw :
      Integrable
        (fun q :
            ((((leftOutgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ×
                (rightOutgoing.terminalPost.SurvivingCoordinate -> T4)) ×
              T4) =>
          leftData.eeeeFinalRawEndpointDensity leftOutgoing
            rightData rightOutgoing pi alpha beta q.1.1 q.1.2 q.2)
        (leftData.eeeeFinalRawEndpointMeasure leftOutgoing
          rightData rightOutgoing)) :
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * physical =
      ∫ v : (leftData.eeeeTerminalData leftOutgoing
          rightData rightOutgoing).NestedCoordinate pi -> T4,
        leftData.eeeeNestedEndpointDensity leftOutgoing
          rightData rightOutgoing pi alpha beta v
        ∂Measure.pi fun _ => paperMeasure :=
  hrawCollapse.trans
    (leftData.integral_eeeeFinalRaw_eq_integral_nestedEndpointDensity
      leftOutgoing rightData rightOutgoing pi alpha beta hraw)

end R324IncomingExceptionalStopTraceAssembly

namespace R324PaperHalfExceptionalExceptionalRoute

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}

/-- A surviving single is the literal post-terminal interior of an `EE`
half.  This just exposes the geometric fact already used by the route
constructor. -/
theorem terminalPost_active_of_singles
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hsingles : pairing.singles.Nonempty) :
    data.outgoing.terminalPost.state.active.Nonempty :=
  data.outgoing.terminalPost_active_nonempty_of_singles hsingles

/-- The retained outgoing exceptional block has a genuine internal
predecessor whenever the half has a surviving single. -/
theorem predecessor_ne_zero_of_singles
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hsingles : pairing.singles.Nonempty) :
    r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
        data.outgoing.terminalData.terminal ≠ 0 := by
  obtain ⟨i, hiSingle⟩ := hsingles
  have hiFinal : i ∈ finalActive pairing :=
    singles_subset_finalActive pairing hiSingle
  have hiPost : i ∈ data.outgoing.terminalPost.state.active := by
    rw [data.outgoing.terminalPost_active_eq_finalActive]
    exact hiFinal
  exact predecessorSlot_ne_zero_of_finalActive_lt
    data.outgoing.endpoint.stop data.outgoing.terminalData.terminal []
    data.outgoing.endpoint.stop_remaining i hiFinal
    (data.outgoing.terminalPost_active_lt_terminal_left hiPost)

/-- The synchronized pre-terminal budget is the certificate used by the
retained exceptional outgoing estimate. -/
theorem stopBudgetCertificate
    (data : R324PaperHalfExceptionalExceptionalRoute providers) :
    R324WithinHalfEdgeCertificate
      data.outgoing.terminalContext.state data.endpoint.stopBudgetScale := by
  rw [data.outgoing_eq]
  exact data.endpoint.stopCertificate

/-- Proposition 4.1 specialized to the retained outgoing block of an
exceptional/exceptional half. -/
theorem outgoingProp41
    (data : R324PaperHalfExceptionalExceptionalRoute providers) :
    forall (H : Fin (2 * residualBlockOrder
          data.outgoing.terminalData.terminal.2 - 1) -> T4 -> Real),
      IsAdmissiblePrimitiveInput
          (residualBlockOrder data.outgoing.terminalData.terminal.2) H ->
        MemEClassT4
            (primitiveKernelDiff rho lam eps
              (residualBlockOrder data.outgoing.terminalData.terminal.2)
              data.outgoing.terminalContext.one_le_blockOrder H) /\
          MemEClassT4
            (primitiveKernelInsertedDiff rho lam eps
              (residualBlockOrder data.outgoing.terminalData.terminal.2)
              data.outgoing.terminalContext.one_le_blockOrder H) /\
          PrimitiveKernelBounds rho lam eps
            (residualBlockOrder data.outgoing.terminalData.terminal.2)
            data.outgoing.terminalContext.one_le_blockOrder H
            providers.supportConstant C := by
  rw [data.outgoing_eq]
  intro H hH
  exact providers.prop41Provider
    data.endpoint.endpoint.stop data.terminalData.terminal []
    data.endpoint.endpoint.stop_remaining H hH

/-- On the completed `EE` half, the outer chain left by the retained
terminal is exactly the endpoint-erased post-terminal chain. -/
theorem incomingErasedHeadOuterFactor_eq_terminalPost_endpointErasedSignedChain
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0)
    (hactive : data.outgoing.terminalPost.state.active.Nonempty)
    (x y : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    data.outgoing.endpoint.stop.incomingErasedHeadOuterFactor
        data.outgoing.terminalData.terminal []
        data.outgoing.endpoint.stop_remaining rho eps x y v =
      data.outgoing.terminalPost.endpointErasedSignedChain
        hactive x y (data.outgoing.terminalPost.reconstruct v) := by
  have hpredOut :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal =
        data.outgoing.terminalPost.terminalOutgoingEdgeSlot hactive :=
    data.outgoing.predecessorSlot_eq_terminalPost_outgoing hpred hactive
  unfold R324WithinHalfResidualPrefix.incomingErasedHeadOuterFactor
  rw [data.outgoing.terminalPost.residualDifferenceProduct_of_remaining_nil
        data.outgoing.terminalPost_remaining x y,
    data.outgoing.terminalPost.residualPrimitiveProduct_of_remaining_nil
      data.outgoing.terminalPost_remaining rho eps]
  simp only [mul_one]
  unfold R324WithinHalfResidualPrefix.incomingErasedHeadOuterChainProductAfter
    R324WithinHalfResidualPrefix.endpointErasedSignedChain
  symm
  apply Finset.prod_subset
  · intro edge hedge
    have hedgeOut := (Finset.mem_erase.mp hedge).1
    have hedgeZero := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hedge).2).1
    have hedgeActive := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hedge).2).2
    apply Finset.mem_erase.mpr
    refine ⟨hedgeZero, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [R324WithinHalfResidualPrefix.headChainSlots,
      Finset.mem_union, Finset.mem_singleton]
    push Not
    constructor
    · intro hedgePred
      apply hedgeOut
      exact hedgePred.trans hpredOut
    · intro hedgeInternal
      have hpostSlots := data.outgoing.endpoint.stop.afterHead_activeEdgeSlots
        data.outgoing.terminalData.terminal []
        data.outgoing.endpoint.stop_remaining
      rw [hpostSlots] at hedgeActive
      exact (Finset.mem_sdiff.mp hedgeActive).2
        (Finset.mem_union_left _ hedgeInternal)
  · intro edge hedgeOuter hedgeNotEndpoint
    have hedgeZero := (Finset.mem_erase.mp hedgeOuter).1
    have hedgeNotHead := (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hedgeOuter).2).2
    by_cases hedgeActive : edge ∈ data.outgoing.terminalPost.activeEdgeSlots
    · have hedgeOut : edge =
          data.outgoing.terminalPost.terminalOutgoingEdgeSlot hactive := by
        by_contra hne
        apply hedgeNotEndpoint
        exact Finset.mem_erase.mpr
          ⟨hne, Finset.mem_erase.mpr ⟨hedgeZero, hedgeActive⟩⟩
      exfalso
      apply hedgeNotHead
      rw [R324WithinHalfResidualPrefix.headChainSlots,
        Finset.mem_union, Finset.mem_singleton]
      left
      exact hedgeOut.trans hpredOut.symm
    · rw [data.outgoing.terminalPost.residualChainEdgeFactor_of_remaining_nil
          data.outgoing.terminalPost_remaining,
        if_neg hedgeActive]

/-- The literal complete-budget scale after consuming the retained outgoing
terminal. -/
def postBudgetScale
    (data : R324PaperHalfExceptionalExceptionalRoute providers) :
    Fin (m + 1) -> Real :=
  data.endpoint.endpoint.stop.budgetUpdatedEdgeScale
    data.terminalData.terminal [] data.endpoint.endpoint.stop_remaining
    data.endpoint.stopBudgetScale C lam K

theorem postBudgetReachable
    (data : R324PaperHalfExceptionalExceptionalRoute providers) :
    R324WithinHalfBudgetScaleReachable pairing rho C lam eps K A
      data.outgoing.terminalPost.state data.postBudgetScale := by
  obtain ⟨_bound, reachable, _certificate⟩ :=
    providers.budgetProvider data.endpoint.endpoint.stop
      data.terminalData.terminal [] data.endpoint.endpoint.stop_remaining
      data.endpoint.stopBudgetScale data.endpoint.stopReachable
      data.endpoint.stopCertificate
  rw [data.outgoing_eq]
  simpa only [postBudgetScale,
    R324PaperOutgoingEndpointTerminal.terminalPost] using reachable

theorem postBudgetCertificate
    (data : R324PaperHalfExceptionalExceptionalRoute providers) :
    R324WithinHalfEdgeCertificate
      data.outgoing.terminalPost.state data.postBudgetScale := by
  obtain ⟨_bound, _reachable, certificate⟩ :=
    providers.budgetProvider data.endpoint.endpoint.stop
      data.terminalData.terminal [] data.endpoint.endpoint.stop_remaining
      data.endpoint.stopBudgetScale data.endpoint.stopReachable
      data.endpoint.stopCertificate
  rw [data.outgoing_eq]
  simpa only [postBudgetScale,
    R324PaperOutgoingEndpointTerminal.terminalPost] using certificate

/-- Any completed route scale and the literal outgoing update have the same
active product, since both are complete budget histories on the same final
paper state. -/
theorem postBudget_activeProduct_eq_route
    (data : R324PaperHalfExceptionalExceptionalRoute providers) :
    (∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
        data.postBudgetScale edge) =
      ∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
        data.route.terminalScale edge := by
  have hpost := data.postBudgetReachable.activeEdgeScaleProduct_eq
  have hroute := data.route.terminalReachable.activeEdgeScaleProduct_eq
  rw [data.route_final] at hroute
  exact hpost.trans hroute.symm

theorem postBudgetScale_zero_eq_stopBudget
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0) :
    data.postBudgetScale 0 = data.endpoint.stopBudgetScale 0 := by
  rw [data.outgoing_eq] at hpred
  unfold postBudgetScale
  rw [data.endpoint.endpoint.stop.budgetUpdatedEdgeScale_of_ne]
  exact Ne.symm hpred

/-- The outgoing local block charge is one boundary scale of the completed
post-terminal budget. -/
theorem outgoingBudgetCore_le_postBudget_outgoingScale
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0)
    (hactive : data.outgoing.terminalPost.state.active.Nonempty) :
    data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) *
        r324WithinHalfInternalEdgeScaleProduct
          data.outgoing.terminalContext data.endpoint.stopBudgetScale *
        (C * lam) ^
          (2 * residualBlockOrder
            data.outgoing.terminalData.terminal.2) * K <=
      data.postBudgetScale
        (data.outgoing.terminalPost.terminalOutgoingEdgeSlot hactive) := by
  have hpredOut :=
    data.outgoing.predecessorSlot_eq_terminalPost_outgoing hpred hactive
  let ctx := data.endpoint.endpoint.stop.headContext
    data.terminalData.terminal [] data.endpoint.endpoint.stop_remaining
  have hout :
      data.endpoint.stopBudgetScale ctx.outgoingSlot = A := by
    exact data.endpoint.stopReachable.outgoingScale_eq_base
      data.endpoint.endpoint.stop rfl data.terminalData.terminal []
      data.endpoint.endpoint.stop_remaining
  have hcore :
      data.endpoint.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.endpoint.endpoint.stop.state data.terminalData.terminal) *
          r324WithinHalfInternalEdgeScaleProduct
            ctx data.endpoint.stopBudgetScale *
          (C * lam) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) * K <=
        data.postBudgetScale
          (r324WithinHalfPredecessorSlot
            data.endpoint.endpoint.stop.state data.terminalData.terminal) := by
    unfold postBudgetScale
    rw [data.endpoint.endpoint.stop.budgetUpdatedEdgeScale_predecessor,
      data.endpoint.endpoint.stop.headBlockScaleProduct_eq_internal_mul_outgoing]
    change
      data.endpoint.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.endpoint.endpoint.stop.state data.terminalData.terminal) *
          r324WithinHalfInternalEdgeScaleProduct
            ctx data.endpoint.stopBudgetScale *
          (C * lam) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) * K <=
        data.endpoint.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.endpoint.endpoint.stop.state data.terminalData.terminal) *
          (r324WithinHalfInternalEdgeScaleProduct
              ctx data.endpoint.stopBudgetScale *
            data.endpoint.stopBudgetScale ctx.outgoingSlot) *
          (C * lam) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) * K
    rw [hout]
    have hpredScale := data.endpoint.stopCertificate.scale_pos
      (r324WithinHalfPredecessorSlot
        data.endpoint.endpoint.stop.state data.terminalData.terminal) |>.le
    have hinternal :
        0 <= r324WithinHalfInternalEdgeScaleProduct
          ctx data.endpoint.stopBudgetScale :=
      (data.endpoint.stopCertificate.internalEdgeScaleProduct_pos
        (ctx := ctx)).le
    have hpow :
        0 <= (C * lam) ^
          (2 * residualBlockOrder data.terminalData.terminal.2) := by
      exact (even_two_mul
        (residualBlockOrder data.terminalData.terminal.2)).pow_nonneg _
    have hK0 : 0 <= K := zero_le_one.trans providers.hK
    calc
      _ =
          (data.endpoint.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.endpoint.endpoint.stop.state data.terminalData.terminal) *
            r324WithinHalfInternalEdgeScaleProduct
              ctx data.endpoint.stopBudgetScale *
            (C * lam) ^
              (2 * residualBlockOrder data.terminalData.terminal.2) * K) * 1 := by
          ring
      _ <=
          (data.endpoint.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.endpoint.endpoint.stop.state data.terminalData.terminal) *
            r324WithinHalfInternalEdgeScaleProduct
              ctx data.endpoint.stopBudgetScale *
            (C * lam) ^
              (2 * residualBlockOrder data.terminalData.terminal.2) * K) * A :=
        mul_le_mul_of_nonneg_left providers.hA
          (mul_nonneg (mul_nonneg (mul_nonneg hpredScale hinternal) hpow) hK0)
      _ = _ := by ring
  calc
    _ = data.endpoint.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.endpoint.endpoint.stop.state data.terminalData.terminal) *
          r324WithinHalfInternalEdgeScaleProduct
            ctx data.endpoint.stopBudgetScale *
          (C * lam) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) * K := by
      rw [data.outgoing_eq]
      rfl
    _ <= data.postBudgetScale
        (r324WithinHalfPredecessorSlot
          data.endpoint.endpoint.stop.state data.terminalData.terminal) := hcore
    _ = _ := by
      have hpredEq :
          r324WithinHalfPredecessorSlot
              data.endpoint.endpoint.stop.state data.terminalData.terminal =
            r324WithinHalfPredecessorSlot
              data.outgoing.endpoint.stop.state
              data.outgoing.terminalData.terminal := by
        rw [data.outgoing_eq]
      exact congrArg data.postBudgetScale (hpredEq.trans hpredOut)

/-- The two boundary charges and the erased post chain fit inside the full
completed route scale product. -/
theorem boundaryCore_mul_endpointErasedScale_le_routeActiveProduct
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0)
    (hactive : data.outgoing.terminalPost.state.active.Nonempty) :
    data.endpoint.stopBudgetScale 0 *
        (data.endpoint.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.outgoing.terminalContext.state
              data.outgoing.terminalContext.step) *
          r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          (C * lam) ^
            (2 * residualBlockOrder
              data.outgoing.terminalData.terminal.2) * K) *
        data.outgoing.terminalPost.endpointErasedScaleProduct
          hactive data.postBudgetScale <=
      ∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
        data.route.terminalScale edge := by
  have hout := data.outgoingBudgetCore_le_postBudget_outgoingScale
    hpred hactive
  have hzero := data.postBudgetScale_zero_eq_stopBudget hpred
  have herased :
      0 <= data.outgoing.terminalPost.endpointErasedScaleProduct
        hactive data.postBudgetScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (data.postBudgetCertificate.scale_pos edge).le
  calc
    data.endpoint.stopBudgetScale 0 *
          (data.endpoint.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.outgoing.terminalContext.state
                data.outgoing.terminalContext.step) *
            r324WithinHalfInternalEdgeScaleProduct
              data.outgoing.terminalContext data.endpoint.stopBudgetScale *
            (C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K) *
          data.outgoing.terminalPost.endpointErasedScaleProduct
            hactive data.postBudgetScale <=
        data.postBudgetScale 0 *
          data.postBudgetScale
            (data.outgoing.terminalPost.terminalOutgoingEdgeSlot hactive) *
          data.outgoing.terminalPost.endpointErasedScaleProduct
            hactive data.postBudgetScale := by
      rw [hzero]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hout
          (data.endpoint.stopCertificate.scale_pos 0).le) herased
    _ = ∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
          data.postBudgetScale edge := by
      rw [data.outgoing.terminalPost
        |>.activeEdgeScaleProduct_eq_boundary_mul_endpointErased]
    _ = _ := data.postBudget_activeProduct_eq_route

/-- The post-terminal erased chain is bounded by the literal updated budget
scale on every off-diagonal configuration. -/
theorem norm_terminalSplitOuter_le_postBudgetMajorant
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0)
    (hactive : data.outgoing.terminalPost.state.active.Nonempty)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (hne : ∀ edge ∈
        data.outgoing.terminalPost.endpointErasedActiveEdgeSlots hactive,
      data.outgoing.terminalPost.edgeDisplacement 0 0
        (data.outgoing.terminalPost.reconstruct v) edge ≠ 0) :
    ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ <=
      ‖coefficient v‖ *
        (data.outgoing.terminalPost.endpointErasedScaleProduct
            hactive data.postBudgetScale *
          data.outgoing.terminalPost.endpointErasedInvSqChainProduct
            hactive v) := by
  have hchain :=
    data.outgoing.terminalPost.abs_endpointErasedSignedChain_le
      hactive data.postBudgetCertificate
      data.outgoing.terminalPost_remaining 0 0
      (data.outgoing.terminalPost.reconstruct v) hne
  unfold R324PaperOutgoingEndpointTerminal.terminalSplitOuter
  rw [data.incomingErasedHeadOuterFactor_eq_terminalPost_endpointErasedSignedChain
      hpred hactive x 0 v,
    data.outgoing.terminalPost.endpointErasedSignedChain_eq_zeroEndpoints
      hactive x 0]
  simp only [norm_mul, norm_charT4, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [R324WithinHalfResidualPrefix.endpointErasedInvSqChainProduct]
      using hchain)
    (norm_nonneg _)

/-- Literal exceptional outgoing estimate, still in the pre-terminal
budget currency and with exactly one endpoint sacrifice. -/
theorem norm_integral_outgoingEndpointDefectDensity_le_inserted
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    ‖∫ first : T4,
        data.outgoing.outgoingEndpointDefectDensity coefficient
          incomingMode outgoingMode x v first
        ∂paperMeasure‖ <=
      (data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) *
          invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ∫ gap : T4,
              primitiveInsertedMajorant C lam eps
                providers.supportConstant
                (residualBlockOrder
                  data.outgoing.terminalData.terminal.2) gap
              ∂paperMeasure)) *
        ‖data.outgoing.terminalSplitOuter
          coefficient incomingMode x v‖ := by
  exact data.outgoing
    |>.norm_integral_outgoingEndpointDefectDensity_le_inserted_of_certificate
      data.endpoint.stopBudgetScale data.stopBudgetCertificate coefficient
      incomingMode outgoingMode x v providers.heps providers.hC
      providers.hlam data.outgoingProp41

/-- Pay the inserted outgoing integral with the same complete local block
constant `K`.  The endpoint sacrifice remains explicit. -/
theorem norm_integral_outgoingEndpointDefectDensity_le_budgeted
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    ‖∫ first : T4,
        data.outgoing.outgoingEndpointDefectDensity coefficient
          incomingMode outgoingMode x v first
        ∂paperMeasure‖ <=
      (data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) *
          invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        ‖data.outgoing.terminalSplitOuter
          coefficient incomingMode x v‖ := by
  refine
    (data.norm_integral_outgoingEndpointDefectDensity_le_inserted
      coefficient outgoingMode x v).trans ?_
  have hcharge := providers.outgoingInsertedBudget
    (residualBlockOrder data.outgoing.terminalData.terminal.2)
    data.outgoing.terminalContext.one_le_blockOrder
  have hfront :
      0 <=
        (data.endpoint.stopBudgetScale
            (r324WithinHalfPredecessorSlot
              data.outgoing.terminalContext.state
              data.outgoing.terminalContext.step) * invSqKerMass) *
          paperSecondOrderModeDecay outgoingMode := by
    exact mul_nonneg
      (mul_nonneg (data.stopBudgetCertificate.scale_pos _).le
        invSqKerMass_nonneg)
      (paperSecondOrderModeDecay_nonneg outgoingMode)
  have hinternal :
      0 <= r324WithinHalfInternalEdgeScaleProduct
        data.outgoing.terminalContext data.endpoint.stopBudgetScale :=
    data.stopBudgetCertificate.internalEdgeScaleProduct_pos.le
  have hsac :
      0 <= r324EndpointPrimitiveSacrifice eps .insertedSacrifice :=
    r324EndpointPrimitiveSacrifice_nonneg eps _
  have houter :
      0 <= ‖data.outgoing.terminalSplitOuter
        coefficient incomingMode x v‖ := norm_nonneg _
  calc
    (data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ∫ gap : T4,
              primitiveInsertedMajorant C lam eps
                providers.supportConstant
                (residualBlockOrder
                  data.outgoing.terminalData.terminal.2) gap
              ∂paperMeasure)) *
        ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ =
      ((data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode) *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
          (2 * ∫ gap : T4,
            primitiveInsertedMajorant C lam eps
              providers.supportConstant
              (residualBlockOrder
                data.outgoing.terminalData.terminal.2) gap
            ∂paperMeasure)) *
        ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ := by
      ring
    _ <=
      ((data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode) *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
          ((C * lam) ^
            (2 * residualBlockOrder
              data.outgoing.terminalData.terminal.2) * K)) *
        ‖data.outgoing.terminalSplitOuter coefficient incomingMode x v‖ := by
      gcongr
    _ = _ := by ring

/-- The already-collapsed exceptional incoming endpoint, with an arbitrary
post-terminal coefficient still attached. -/
def incomingEndpointCoefficient
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) : Complex :=
  data.endpoint.endpoint.multiplier incomingMode *
    ((paperSecondOrderModeDecay incomingMode : Complex) ^ 2 *
      incomingExceptionalPrimitiveDefect rho lam eps
        (residualBlockOrder data.pack.data.terminal.2)
        data.pack.data.stopContext.one_le_blockOrder
        data.pack.data.stopContext.internalEdges incomingMode *
      coefficient v)

theorem norm_incomingEndpointCoefficient_le
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    ‖data.incomingEndpointCoefficient coefficient v‖ <=
      paperSecondOrderModeDecay incomingMode *
        data.endpoint.stopBudgetScale 0 * ‖coefficient v‖ := by
  have hfactor :=
    data.pack.norm_multiplier_mul_squaredDecay_defect_le_stopBudget
      data.endpoint providers.headBudget providers.hC providers.hlam
      (zero_le_one.trans providers.hK) providers.hA
  unfold incomingEndpointCoefficient
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)

/-- One complete exceptional/exceptional half after both signed endpoint
operations, before any norm. -/
def endpointDensity
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) : Complex :=
  ∫ first : T4,
    data.outgoing.outgoingEndpointDefectDensity
      (data.incomingEndpointCoefficient coefficient)
      incomingMode outgoingMode x v first
    ∂paperMeasure

/-- Pointwise numerical exit of one literal `EE` half.  Both signed
endpoint operations have already been completed.  The incoming endpoint
sacrifice is introduced only as the final case-ledger enlargement. -/
theorem norm_endpointDensity_le
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (hpred :
      r324WithinHalfPredecessorSlot data.outgoing.endpoint.stop.state
          data.outgoing.terminalData.terminal ≠ 0)
    (hactive : data.outgoing.terminalPost.state.active.Nonempty)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4) (x : T4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (hne : ∀ edge ∈
        data.outgoing.terminalPost.endpointErasedActiveEdgeSlots hactive,
      data.outgoing.terminalPost.edgeDisplacement 0 0
        (data.outgoing.terminalPost.reconstruct v) edge ≠ 0) :
    ‖data.endpointDensity coefficient outgoingMode x v‖ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
          r324EndpointPrimitiveSacrifice eps .insertedSacrifice) *
        ((∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
            data.route.terminalScale edge) * invSqKerMass) *
        data.outgoing.terminalPost.endpointErasedInvSqChainProduct
          hactive v * ‖coefficient v‖ := by
  have hout :=
    data.norm_integral_outgoingEndpointDefectDensity_le_budgeted
      (data.incomingEndpointCoefficient coefficient) outgoingMode x v
  have houter := data.norm_terminalSplitOuter_le_postBudgetMajorant
    hpred hactive (data.incomingEndpointCoefficient coefficient) x v hne
  have hincoming := data.norm_incomingEndpointCoefficient_le coefficient v
  have hboundary :=
    data.boundaryCore_mul_endpointErasedScale_le_routeActiveProduct
      hpred hactive
  have hdin := paperSecondOrderModeDecay_nonneg incomingMode
  have hdout := paperSecondOrderModeDecay_nonneg outgoingMode
  have hsac0 :=
    r324EndpointPrimitiveSacrifice_nonneg eps
      R324EndpointReductionCase.insertedSacrifice
  have hsac1 := one_le_r324EndpointPrimitiveSacrifice
    providers.heps providers.heps1
      R324EndpointReductionCase.insertedSacrifice
  have hmass := invSqKerMass_nonneg
  have hpath :=
    data.outgoing.terminalPost.endpointErasedInvSqChainProduct_nonneg
      hactive v
  have hcoef := norm_nonneg (coefficient v)
  have hprefix :
      0 <=
        (data.endpoint.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.outgoing.terminalContext.state
                data.outgoing.terminalContext.step) * invSqKerMass) *
          paperSecondOrderModeDecay outgoingMode *
          (r324WithinHalfInternalEdgeScaleProduct
              data.outgoing.terminalContext data.endpoint.stopBudgetScale *
            (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
              ((C * lam) ^
                (2 * residualBlockOrder
                  data.outgoing.terminalData.terminal.2) * K))) := by
    have hpredecessor :=
      (data.stopBudgetCertificate.scale_pos
        (r324WithinHalfPredecessorSlot
          data.outgoing.terminalContext.state
          data.outgoing.terminalContext.step)).le
    have hinternal :=
      data.stopBudgetCertificate.internalEdgeScaleProduct_pos.le
    have hpow :
        0 <= (C * lam) ^
          (2 * residualBlockOrder
            data.outgoing.terminalData.terminal.2) :=
      (even_two_mul _).pow_nonneg _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hpredecessor hmass) hdout)
      (mul_nonneg hinternal
        (mul_nonneg hsac0 (mul_nonneg hpow providers.hK_nonneg)))
  have hpostFactor :
      0 <=
        data.outgoing.terminalPost.endpointErasedScaleProduct
            hactive data.postBudgetScale *
          data.outgoing.terminalPost.endpointErasedInvSqChainProduct
            hactive v := by
    have hpostScale :
        0 <= data.outgoing.terminalPost.endpointErasedScaleProduct
          hactive data.postBudgetScale := by
      unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
      exact Finset.prod_nonneg fun edge _ =>
        (data.postBudgetCertificate.scale_pos edge).le
    exact mul_nonneg hpostScale hpath
  refine hout.trans ?_
  calc
    (data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        ‖data.outgoing.terminalSplitOuter
          (data.incomingEndpointCoefficient coefficient)
          incomingMode x v‖ <=
      (data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        (‖data.incomingEndpointCoefficient coefficient v‖ *
          (data.outgoing.terminalPost.endpointErasedScaleProduct
              hactive data.postBudgetScale *
            data.outgoing.terminalPost.endpointErasedInvSqChainProduct
              hactive v)) := by
        exact mul_le_mul_of_nonneg_left houter hprefix
    _ <=
      (data.endpoint.stopBudgetScale
          (r324WithinHalfPredecessorSlot
            data.outgoing.terminalContext.state
            data.outgoing.terminalContext.step) * invSqKerMass) *
        paperSecondOrderModeDecay outgoingMode *
        (r324WithinHalfInternalEdgeScaleProduct
            data.outgoing.terminalContext data.endpoint.stopBudgetScale *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K))) *
        ((paperSecondOrderModeDecay incomingMode *
            data.endpoint.stopBudgetScale 0 * ‖coefficient v‖) *
          (data.outgoing.terminalPost.endpointErasedScaleProduct
              hactive data.postBudgetScale *
            data.outgoing.terminalPost.endpointErasedInvSqChainProduct
              hactive v)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hincoming hpostFactor) hprefix
    _ =
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        invSqKerMass *
        (data.endpoint.stopBudgetScale 0 *
          (data.endpoint.stopBudgetScale
              (r324WithinHalfPredecessorSlot
                data.outgoing.terminalContext.state
                data.outgoing.terminalContext.step) *
            r324WithinHalfInternalEdgeScaleProduct
              data.outgoing.terminalContext data.endpoint.stopBudgetScale *
            (C * lam) ^
              (2 * residualBlockOrder
                data.outgoing.terminalData.terminal.2) * K) *
          data.outgoing.terminalPost.endpointErasedScaleProduct
            hactive data.postBudgetScale) *
        data.outgoing.terminalPost.endpointErasedInvSqChainProduct
          hactive v * ‖coefficient v‖ := by
      ring
    _ <=
      (paperSecondOrderModeDecay incomingMode *
          paperSecondOrderModeDecay outgoingMode) *
        r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
        invSqKerMass *
        (∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
          data.route.terminalScale edge) *
        data.outgoing.terminalPost.endpointErasedInvSqChainProduct
          hactive v * ‖coefficient v‖ := by
      gcongr
    _ <= _ := by
      have hfront :
          0 <=
            (paperSecondOrderModeDecay incomingMode *
                paperSecondOrderModeDecay outgoingMode) *
              r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
              invSqKerMass *
              (∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
                data.route.terminalScale edge) *
              data.outgoing.terminalPost.endpointErasedInvSqChainProduct
                hactive v * ‖coefficient v‖ := by
        have hrouteProduct :
            0 <= ∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
              data.route.terminalScale edge := by
          exact Finset.prod_nonneg fun edge _ =>
            (data.route.terminalCertificate.scale_pos edge).le
        positivity
      calc
        _ = 1 *
            ((paperSecondOrderModeDecay incomingMode *
                paperSecondOrderModeDecay outgoingMode) *
              r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
              invSqKerMass *
              (∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
                data.route.terminalScale edge) *
              data.outgoing.terminalPost.endpointErasedInvSqChainProduct
                hactive v * ‖coefficient v‖) := by ring
        _ <= r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            ((paperSecondOrderModeDecay incomingMode *
                paperSecondOrderModeDecay outgoingMode) *
              r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
              invSqKerMass *
              (∏ edge ∈ data.outgoing.terminalPost.activeEdgeSlots,
                data.route.terminalScale edge) *
              data.outgoing.terminalPost.endpointErasedInvSqChainProduct
                hactive v * ‖coefficient v‖) :=
          mul_le_mul_of_nonneg_right hsac1 hfront
        _ = _ := by ring

end R324PaperHalfExceptionalExceptionalRoute

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

/-! ### Literal `EE × EE` factorization after all four endpoint operations -/

variable {alpha beta : Z4}
    {leftEEProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP alpha}
    {rightEEProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM (-alpha)}

/-- The cross primitive sum left untouched by the four endpoint Fourier
operations. -/
def eeeeCrossCoefficient
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftEEProviders)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightEEProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (leftPost : leftEE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (rightPost : rightEE.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    Complex :=
  (r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
    (r324TwoHalfRootDoubledReconstruct
      leftEE.outgoing.terminalPost rightEE.outgoing.terminalPost
      (leftPost, rightPost)) : Complex)

/-- Pointwise, before taking any norm, the final raw four-endpoint density
is the product of the two completed signed half densities. -/
theorem eeeeFinalRawEndpointDensity_eq_endpointFactors
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftEEProviders)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightEEProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (leftPost : leftEE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (firstLeft : T4)
    (rightPost : rightEE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (firstRight : T4) :
    leftEE.pack.data.eeeeFinalRawEndpointDensity leftEE.outgoing
        rightEE.pack.data rightEE.outgoing pi alpha beta
        (leftPost, firstLeft) rightPost firstRight =
      leftEE.outgoing.outgoingEndpointDefectDensity
          (leftEE.incomingEndpointCoefficient (fun _ => 1))
          alpha beta 0 leftPost firstLeft *
        rightEE.outgoing.outgoingEndpointDefectDensity
          (rightEE.incomingEndpointCoefficient
            (eeeeCrossCoefficient leftEE rightEE pi leftPost))
          (-alpha) (-beta) 0 rightPost firstRight := by
  have hleftMultiplier :
      leftEE.outgoing.endpoint.multiplier alpha =
        leftEE.endpoint.endpoint.multiplier alpha := by
    simpa using congrArg
      (fun out => out.endpoint.multiplier alpha) leftEE.outgoing_eq
  have hrightMultiplier :
      rightEE.outgoing.endpoint.multiplier (-alpha) =
        rightEE.endpoint.endpoint.multiplier (-alpha) := by
    simpa using congrArg
      (fun out => out.endpoint.multiplier (-alpha)) rightEE.outgoing_eq
  unfold R324IncomingExceptionalStopTraceAssembly.eeeeFinalRawEndpointDensity
    R324IncomingExceptionalStopTraceAssembly.eeeeRightPostCoefficient
    R324IncomingExceptionalStopTraceAssembly.eeeeLeftEndpointFactor
    R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
    R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
    R324PaperOutgoingEndpointTerminal.terminalSplitOuter
    eeeeCrossCoefficient
  rw [hleftMultiplier, hrightMultiplier]
  ring

/-- Exact Fubini factorization on the common nested carrier.  This is the
paper's instruction to finish all interval removals and endpoint operations
before taking absolute values, written literally. -/
theorem eeeeNestedEndpointDensity_eq_endpointDensity_mul
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftEEProviders)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightEEProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (v : (leftEE.pack.data.eeeeTerminalData leftEE.outgoing
      rightEE.pack.data rightEE.outgoing).NestedCoordinate pi -> T4) :
    let terminal := leftEE.pack.data.eeeeTerminalData leftEE.outgoing
      rightEE.pack.data rightEE.outgoing
    let p := (terminal.terminalProductPiMeasurableEquivNested pi).symm v
    leftEE.pack.data.eeeeNestedEndpointDensity leftEE.outgoing
        rightEE.pack.data rightEE.outgoing pi alpha beta v =
      leftEE.endpointDensity (fun _ => 1) beta 0 p.1 *
        rightEE.endpointDensity
          (eeeeCrossCoefficient leftEE rightEE pi p.1) (-beta) 0 p.2 := by
  dsimp only
  unfold R324IncomingExceptionalStopTraceAssembly.eeeeNestedEndpointDensity
    R324PaperHalfExceptionalExceptionalRoute.endpointDensity
  dsimp only
  calc
    (∫ firstLeft : T4, ∫ firstRight : T4,
        leftEE.pack.data.eeeeFinalRawEndpointDensity leftEE.outgoing
          rightEE.pack.data rightEE.outgoing pi alpha beta
          (((leftEE.pack.data.eeeeTerminalData leftEE.outgoing
              rightEE.pack.data rightEE.outgoing
              |>.terminalProductPiMeasurableEquivNested pi).symm v).1,
            firstLeft)
          ((leftEE.pack.data.eeeeTerminalData leftEE.outgoing
              rightEE.pack.data rightEE.outgoing
              |>.terminalProductPiMeasurableEquivNested pi).symm v).2
          firstRight
        ∂paperMeasure ∂paperMeasure) =
      ∫ firstLeft : T4,
        leftEE.outgoing.outgoingEndpointDefectDensity
            (leftEE.incomingEndpointCoefficient (fun _ => 1))
            alpha beta 0
            ((leftEE.pack.data.eeeeTerminalData leftEE.outgoing
                rightEE.pack.data rightEE.outgoing
                |>.terminalProductPiMeasurableEquivNested pi).symm v).1
            firstLeft *
          (∫ firstRight : T4,
            rightEE.outgoing.outgoingEndpointDefectDensity
              (rightEE.incomingEndpointCoefficient
                (eeeeCrossCoefficient leftEE rightEE pi
                  ((leftEE.pack.data.eeeeTerminalData leftEE.outgoing
                    rightEE.pack.data rightEE.outgoing
                    |>.terminalProductPiMeasurableEquivNested pi).symm v).1))
              (-alpha) (-beta) 0
              ((leftEE.pack.data.eeeeTerminalData leftEE.outgoing
                  rightEE.pack.data rightEE.outgoing
                  |>.terminalProductPiMeasurableEquivNested pi).symm v).2
              firstRight ∂paperMeasure)
        ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with firstLeft
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with firstRight
      exact eeeeFinalRawEndpointDensity_eq_endpointFactors
        leftEE rightEE pi _ firstLeft _ firstRight
    _ = _ := by rw [integral_mul_const]

/-- Pointwise numerical form of the literal `EE × EE` factorization.
The four endpoint operations contribute the two fourth-order mode decays,
four inserted-primitive sacrifices, and two explicit inverse-square masses.
No norm was taken before the exact factorization above. -/
theorem norm_endpointDensity_mul_endpointDensity_le_massTwoGrouped
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftEEProviders)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightEEProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hleftPred :
      r324WithinHalfPredecessorSlot
        leftEE.outgoing.endpoint.stop.state
        leftEE.outgoing.terminalData.terminal ≠ 0)
    (hrightPred :
      r324WithinHalfPredecessorSlot
        rightEE.outgoing.endpoint.stop.state
        rightEE.outgoing.terminalData.terminal ≠ 0)
    (hleft : leftEE.outgoing.terminalPost.state.active.Nonempty)
    (hright : rightEE.outgoing.terminalPost.state.active.Nonempty)
    (leftPost : leftEE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (rightPost : rightEE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (hneLeft : ∀ edge ∈
        leftEE.outgoing.terminalPost.endpointErasedActiveEdgeSlots hleft,
      leftEE.outgoing.terminalPost.edgeDisplacement 0 0
        (leftEE.outgoing.terminalPost.reconstruct leftPost) edge ≠ 0)
    (hneRight : ∀ edge ∈
        rightEE.outgoing.terminalPost.endpointErasedActiveEdgeSlots hright,
      rightEE.outgoing.terminalPost.edgeDisplacement 0 0
        (rightEE.outgoing.terminalPost.reconstruct rightPost) edge ≠ 0) :
    ‖leftEE.endpointDensity (fun _ => 1) beta 0 leftPost *
        rightEE.endpointDensity
          (eeeeCrossCoefficient leftEE rightEE pi leftPost)
          (-beta) 0 rightPost‖ <=
      ((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps
          (fun _ => R324EndpointReductionCase.insertedSacrifice)) *
        ((((∏ edge ∈ leftEE.outgoing.terminalPost.activeEdgeSlots,
              leftEE.route.terminalScale edge) *
            (∏ edge ∈ rightEE.outgoing.terminalPost.activeEdgeSlots,
              rightEE.route.terminalScale edge)) *
          invSqKerMass ^ (2 : Nat)) *
        leftEE.outgoing.terminalPost.endpointErasedInvSqChainProduct
          hleft leftPost *
        rightEE.outgoing.terminalPost.endpointErasedInvSqChainProduct
          hright rightPost *
        r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            leftEE.outgoing.terminalPost rightEE.outgoing.terminalPost
            (leftPost, rightPost))) := by
  have hleftBound := leftEE.norm_endpointDensity_le
    hleftPred hleft (fun _ => 1) beta 0 leftPost hneLeft
  have hrightBound := rightEE.norm_endpointDensity_le
    hrightPred hright
      (eeeeCrossCoefficient leftEE rightEE pi leftPost)
      (-beta) 0 rightPost hneRight
  have hleftUpperNonneg :=
    (norm_nonneg
      (leftEE.endpointDensity (fun _ => 1) beta 0 leftPost)).trans
      hleftBound
  have hmul := mul_le_mul hleftBound hrightBound
    (norm_nonneg
      (rightEE.endpointDensity
        (eeeeCrossCoefficient leftEE rightEE pi leftPost)
        (-beta) 0 rightPost))
    hleftUpperNonneg
  have hcrossNonneg :=
    r324ResidualPrimitiveSumProduct_nonneg
      rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        leftEE.outgoing.terminalPost rightEE.outgoing.terminalPost
        (leftPost, rightPost))
  have hcrossNorm :
      ‖eeeeCrossCoefficient leftEE rightEE pi leftPost rightPost‖ =
        r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
          (r324TwoHalfRootDoubledReconstruct
            leftEE.outgoing.terminalPost rightEE.outgoing.terminalPost
            (leftPost, rightPost)) := by
    unfold eeeeCrossCoefficient
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcrossNonneg]
  rw [← norm_mul] at hmul
  calc
    _ <=
        ((paperSecondOrderModeDecay alpha *
            paperSecondOrderModeDecay beta) *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            r324EndpointPrimitiveSacrifice eps .insertedSacrifice) *
          ((∏ edge ∈ leftEE.outgoing.terminalPost.activeEdgeSlots,
              leftEE.route.terminalScale edge) * invSqKerMass) *
          leftEE.outgoing.terminalPost.endpointErasedInvSqChainProduct
            hleft leftPost * ‖1‖) *
        ((paperSecondOrderModeDecay (-alpha) *
            paperSecondOrderModeDecay (-beta)) *
          (r324EndpointPrimitiveSacrifice eps .insertedSacrifice *
            r324EndpointPrimitiveSacrifice eps .insertedSacrifice) *
          ((∏ edge ∈ rightEE.outgoing.terminalPost.activeEdgeSlots,
              rightEE.route.terminalScale edge) * invSqKerMass) *
          rightEE.outgoing.terminalPost.endpointErasedInvSqChainProduct
            hright rightPost *
          ‖eeeeCrossCoefficient leftEE rightEE pi leftPost rightPost‖) :=
      hmul
    _ = _ := by
      rw [paperSecondOrderModeDecay_neg alpha,
        paperSecondOrderModeDecay_neg beta,
        paperFourthOrderModeDecay_eq_sq alpha,
        paperFourthOrderModeDecay_eq_sq beta, hcrossNorm]
      unfold r324EndpointPrimitiveSacrificeProduct
      rw [Fin.prod_univ_four]
      simp only [norm_one]
      ring

/-- Fixed compensation for the two artificial inverse-square masses in the
common grouped Step 3 carrier that are not produced by a literal `EE × EE`
endpoint calculation.  This is an order-independent paper constant. -/
def eeeeEndpointMassCompensation : Real :=
  max 1 (invSqKerMass⁻¹ ^ (2 : Nat))

theorem one_le_eeeeEndpointMassCompensation :
    1 <= eeeeEndpointMassCompensation := by
  exact le_max_left _ _

theorem invSqKerMass_sq_le_compensation_mul_pow_four :
    invSqKerMass ^ (2 : Nat) <=
      eeeeEndpointMassCompensation * invSqKerMass ^ (4 : Nat) := by
  have hinv :
      invSqKerMass⁻¹ ^ (2 : Nat) <= eeeeEndpointMassCompensation := by
    exact le_max_right _ _
  calc
    invSqKerMass ^ (2 : Nat) =
        invSqKerMass⁻¹ ^ (2 : Nat) *
          invSqKerMass ^ (4 : Nat) := by
      field_simp [r324_invSqKerMass_pos.ne']
    _ <= eeeeEndpointMassCompensation * invSqKerMass ^ (4 : Nat) :=
      mul_le_mul_of_nonneg_right hinv (pow_nonneg invSqKerMass_nonneg _)

/-- The literal `EE × EE` estimate in the common grouped Step 3
currency.  The sole conversion is the fixed mass compensation above. -/
theorem norm_endpointDensity_mul_endpointDensity_le_compensatedGrouped
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftEEProviders)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightEEProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hleftPred :
      r324WithinHalfPredecessorSlot
        leftEE.outgoing.endpoint.stop.state
        leftEE.outgoing.terminalData.terminal ≠ 0)
    (hrightPred :
      r324WithinHalfPredecessorSlot
        rightEE.outgoing.endpoint.stop.state
        rightEE.outgoing.terminalData.terminal ≠ 0)
    (hleft : leftEE.outgoing.terminalPost.state.active.Nonempty)
    (hright : rightEE.outgoing.terminalPost.state.active.Nonempty)
    (leftPost : leftEE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (rightPost : rightEE.outgoing.terminalPost.SurvivingCoordinate -> T4)
    (hneLeft : ∀ edge ∈
        leftEE.outgoing.terminalPost.endpointErasedActiveEdgeSlots hleft,
      leftEE.outgoing.terminalPost.edgeDisplacement 0 0
        (leftEE.outgoing.terminalPost.reconstruct leftPost) edge ≠ 0)
    (hneRight : ∀ edge ∈
        rightEE.outgoing.terminalPost.endpointErasedActiveEdgeSlots hright,
      rightEE.outgoing.terminalPost.edgeDisplacement 0 0
        (rightEE.outgoing.terminalPost.reconstruct rightPost) edge ≠ 0) :
    ‖leftEE.endpointDensity (fun _ => 1) beta 0 leftPost *
        rightEE.endpointDensity
          (eeeeCrossCoefficient leftEE rightEE pi leftPost)
          (-beta) 0 rightPost‖ <=
      (eeeeEndpointMassCompensation *
        ((paperFourthOrderModeDecay alpha *
            paperFourthOrderModeDecay beta) *
          r324EndpointPrimitiveSacrificeProduct eps
            (fun _ => R324EndpointReductionCase.insertedSacrifice))) *
        (leftEE.pack.data.eeeeTerminalData leftEE.outgoing
          rightEE.pack.data rightEE.outgoing
          |>.endpointIntegratedGroupedMajorant
            leftEE.route.terminalScale rightEE.route.terminalScale
            hleft hright pi (leftPost, rightPost)) := by
  have hraw :=
    norm_endpointDensity_mul_endpointDensity_le_massTwoGrouped
      (alpha := alpha) (beta := beta)
      leftEE rightEE pi hleftPred hrightPred hleft hright
      leftPost rightPost hneLeft hneRight
  have hleftScale :
      0 <= ∏ edge ∈ leftEE.outgoing.terminalPost.activeEdgeSlots,
        leftEE.route.terminalScale edge := by
    exact Finset.prod_nonneg fun edge _ =>
      (leftEE.route.terminalCertificate.scale_pos edge).le
  have hrightScale :
      0 <= ∏ edge ∈ rightEE.outgoing.terminalPost.activeEdgeSlots,
        rightEE.route.terminalScale edge := by
    exact Finset.prod_nonneg fun edge _ =>
      (rightEE.route.terminalCertificate.scale_pos edge).le
  have hleftPath :=
    leftEE.outgoing.terminalPost.endpointErasedInvSqChainProduct_nonneg
      hleft leftPost
  have hrightPath :=
    rightEE.outgoing.terminalPost.endpointErasedInvSqChainProduct_nonneg
      hright rightPost
  have hresidual :=
    r324ResidualPrimitiveSumProduct_nonneg rho eps kappaP kappaM pi
      (r324TwoHalfRootDoubledReconstruct
        leftEE.outgoing.terminalPost rightEE.outgoing.terminalPost
        (leftPost, rightPost))
  have hscalePair := mul_nonneg hleftScale hrightScale
  have hmassScaled := mul_le_mul_of_nonneg_left
    invSqKerMass_sq_le_compensation_mul_pow_four hscalePair
  have hleftScaled := mul_le_mul_of_nonneg_right hmassScaled hleftPath
  have hrightScaled := mul_le_mul_of_nonneg_right hleftScaled hrightPath
  have hspatial := mul_le_mul_of_nonneg_right hrightScaled hresidual
  have hweight :
      0 <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps
          (fun _ => R324EndpointReductionCase.insertedSacrifice) :=
    mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (r324EndpointPrimitiveSacrificeProduct_nonneg eps _)
  have hreconstruct :
      r324TwoHalfRootDoubledReconstruct
          leftEE.outgoing.terminalPost rightEE.outgoing.terminalPost
          (leftPost, rightPost) =
        (leftEE.pack.data.eeeeTerminalData leftEE.outgoing
          rightEE.pack.data rightEE.outgoing).terminalDoubledReconstruct
            (leftPost, rightPost) := by
    funext k
    unfold r324TwoHalfRootDoubledReconstruct
      R324TwoHalfTerminalData.terminalDoubledReconstruct
      R324IncomingExceptionalStopTraceAssembly.eeeeTerminalData
    rfl
  have hweighted := mul_le_mul_of_nonneg_left hspatial hweight
  exact hraw.trans (hweighted.trans_eq (by
    unfold R324TwoHalfTerminalData.endpointIntegratedGroupedMajorant
    rw [← hreconstruct]
    unfold R324IncomingExceptionalStopTraceAssembly.eeeeTerminalData
    ring))

/-- Product-Haar and initial-nested form of the completed literal
`EE × EE` endpoint estimate. -/
theorem ae_norm_eeeeNestedEndpointDensity_le_compensatedGrouped
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftEEProviders)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightEEProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hleftPred :
      r324WithinHalfPredecessorSlot
        leftEE.outgoing.endpoint.stop.state
        leftEE.outgoing.terminalData.terminal ≠ 0)
    (hrightPred :
      r324WithinHalfPredecessorSlot
        rightEE.outgoing.endpoint.stop.state
        rightEE.outgoing.terminalData.terminal ≠ 0)
    (hleft : leftEE.outgoing.terminalPost.state.active.Nonempty)
    (hright : rightEE.outgoing.terminalPost.state.active.Nonempty) :
    let terminal := leftEE.pack.data.eeeeTerminalData leftEE.outgoing
      rightEE.pack.data rightEE.outgoing
    (fun v =>
      ‖leftEE.pack.data.eeeeNestedEndpointDensity leftEE.outgoing
        rightEE.pack.data rightEE.outgoing pi alpha beta v‖) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate pi => paperMeasure]
      fun v =>
        (eeeeEndpointMassCompensation *
          ((paperFourthOrderModeDecay alpha *
              paperFourthOrderModeDecay beta) *
            r324EndpointPrimitiveSacrificeProduct eps
              (fun _ => R324EndpointReductionCase.insertedSacrifice))) *
          terminal.initialNestedEndpointIntegratedGroupedMajorant
            leftEE.route.terminalScale rightEE.route.terminalScale
            hleft hright pi v := by
  dsimp only
  let terminal := leftEE.pack.data.eeeeTerminalData leftEE.outgoing
    rightEE.pack.data rightEE.outgoing
  let density :
      (leftEE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
        (rightEE.outgoing.terminalPost.SurvivingCoordinate -> T4) ->
          Complex :=
    fun p =>
      leftEE.endpointDensity (fun _ => 1) beta 0 p.1 *
        rightEE.endpointDensity
          (eeeeCrossCoefficient leftEE rightEE pi p.1) (-beta) 0 p.2
  let endpointWeight : Real :=
    eeeeEndpointMassCompensation *
      ((paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        r324EndpointPrimitiveSacrificeProduct eps
          (fun _ => R324EndpointReductionCase.insertedSacrifice))
  let majorant :
      (leftEE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
        (rightEE.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Real :=
    fun p => endpointWeight *
      terminal.endpointIntegratedGroupedMajorant
        leftEE.route.terminalScale rightEE.route.terminalScale
        hleft hright pi p
  have hleftOff :=
    leftEE.outgoing.terminalPost
      |>.ae_endpointErased_edgeDisplacement_ne_zero hleft
  have hrightOff :=
    rightEE.outgoing.terminalPost
      |>.ae_endpointErased_edgeDisplacement_ne_zero hright
  have hleftProduct :=
    (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi fun _ :
        leftEE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightEE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure))
      |>.tendsto_ae hleftOff
  have hrightProduct :=
    (Measure.quasiMeasurePreserving_snd
      (μ := Measure.pi fun _ :
        leftEE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightEE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure))
      |>.tendsto_ae hrightOff
  have hproduct :
      (fun p => ‖density p‖) ≤ᵐ[
        (Measure.pi fun _ :
          leftEE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          rightEE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure)]
        majorant := by
    filter_upwards [hleftProduct, hrightProduct] with p hp hq
    simpa only [density, majorant, endpointWeight, terminal, Prod.eta] using
      norm_endpointDensity_mul_endpointDensity_le_compensatedGrouped
        leftEE rightEE pi hleftPred hrightPred hleft hright p.1 p.2 hp hq
  have hpull := terminal.ae_norm_initialNestedPullback_le
    pi density majorant hproduct
  filter_upwards [hpull] with v hv
  rw [eeeeNestedEndpointDensity_eq_endpointDensity_mul
    leftEE rightEE pi v]
  simpa only [R324TwoHalfTerminalData.initialNestedPullback,
    R324TwoHalfTerminalData.initialNestedEndpointIntegratedGroupedMajorant,
    density, majorant, endpointWeight, terminal] using hv

/-- Final complete-run base for the `EE × EE` branch.  It differs from
the common two-half base only by the fixed endpoint-mass compensation. -/
def eeeeEndpointCompleteAbsorbedBase (A C K B : Real) : Real :=
  eeeeEndpointMassCompensation *
    r324TwoHalfCompleteAbsorbedBase A C K B

theorem eeeeEndpointCompleteAbsorbedBase_pos (A C K B : Real) :
    0 < eeeeEndpointCompleteAbsorbedBase A C K B := by
  unfold eeeeEndpointCompleteAbsorbedBase
  exact mul_pos (zero_lt_one.trans_le one_le_eeeeEndpointMassCompensation)
    (r324TwoHalfCompleteAbsorbedBase_pos A C K B)

/-- At every positive perturbative order, the fixed mass compensation is
absorbed by multiplying the primitive base once. -/
theorem compensation_mul_primitiveInsertedMajorant_le
    (B lam eps supportConstant : Real) {n : Nat}
    (hn : 1 <= n) (z : T4) :
    eeeeEndpointMassCompensation *
        primitiveInsertedMajorant B lam eps supportConstant n z <=
      primitiveInsertedMajorant
        (eeeeEndpointMassCompensation * B)
        lam eps supportConstant n z := by
  have hqpow :
      eeeeEndpointMassCompensation <=
        eeeeEndpointMassCompensation ^ (2 * n) := by
    have h := pow_le_pow_right₀ one_le_eeeeEndpointMassCompensation
      (show 1 <= 2 * n by omega)
    simpa only [pow_one] using h
  have hcoefficient :
      eeeeEndpointMassCompensation * (B * lam) ^ (2 * n) <=
        ((eeeeEndpointMassCompensation * B) * lam) ^ (2 * n) := by
    calc
      _ <= eeeeEndpointMassCompensation ^ (2 * n) *
          (B * lam) ^ (2 * n) :=
        mul_le_mul_of_nonneg_right hqpow
          ((even_two_mul n).pow_nonneg _)
      _ = _ := by
        rw [show (eeeeEndpointMassCompensation * B) * lam =
          eeeeEndpointMassCompensation * (B * lam) by ring]
        exact (mul_pow eeeeEndpointMassCompensation (B * lam) (2 * n)).symm
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
  calc
    _ = (eeeeEndpointMassCompensation * (B * lam) ^ (2 * n)) *
        (((eps⁻¹) ^ 2 / |Real.log eps|) * invSqKer z *
            primitiveSupportIndicator supportConstant eps z +
          (1 / |Real.log eps| ^ 2) *
            (torusDistSq z + eps ^ 2)⁻¹ ^ 2) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right hcoefficient hbracket

theorem compensation_mul_integral_primitiveInsertedMajorant_le
    (B lam : Real) {eps : Real} (heps : 0 < eps)
    (supportConstant : Real) {n : Nat} (hn : 1 <= n) :
    eeeeEndpointMassCompensation *
        (∫ z : T4,
          primitiveInsertedMajorant B lam eps supportConstant n z
          ∂paperMeasure) <=
      ∫ z : T4,
        primitiveInsertedMajorant
          (eeeeEndpointMassCompensation * B)
          lam eps supportConstant n z
        ∂paperMeasure := by
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact (integrable_primitiveInsertedMajorant
      B lam eps supportConstant n heps).const_mul _
  · exact integrable_primitiveInsertedMajorant
      (eeeeEndpointMassCompensation * B)
      lam eps supportConstant n heps
  · filter_upwards with z
    exact compensation_mul_primitiveInsertedMajorant_le
      B lam eps supportConstant hn z

theorem compensation_mul_integral_completeAbsorbed_le
    (A C K B lam : Real) {eps : Real} (heps : 0 < eps)
    (supportConstant : Real) {m : Nat} (hm : 1 <= m) :
    eeeeEndpointMassCompensation *
        (∫ z : T4,
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure) <=
      ∫ z : T4,
        primitiveInsertedMajorant
          (eeeeEndpointCompleteAbsorbedBase A C K B)
          lam eps supportConstant m z
        ∂paperMeasure := by
  simpa only [eeeeEndpointCompleteAbsorbedBase] using
    compensation_mul_integral_primitiveInsertedMajorant_le
      (r324TwoHalfCompleteAbsorbedBase A C K B)
      lam heps supportConstant hm

/-- In the literal `EE x EE` constructor branch, the common route terminal
is exactly the two post-terminal carriers used by the signed splice above.
This is the dependent-type seam between branch data and the common grouped
majorant. -/
theorem terminal_exceptionalExceptional_exceptionalExceptional_eq_eeeeTerminalData
    (hleftFirst : (⟨0, leftProviders.hm⟩ : Fin m) ∉ finalActive kappaP)
    (hleftOutgoing : Fin.last m ∈ extractedRightEdges kappaP)
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftProviders)
    (hrightFirst : (⟨0, rightProviders.hm⟩ : Fin m) ∉ finalActive kappaM)
    (hrightOutgoing : Fin.last m ∈ extractedRightEdges kappaM)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightProviders) :
    (R324PaperTwoHalfEndpointRoutes.terminal
      ({ left := .exceptionalExceptional
            hleftFirst hleftOutgoing leftEE
         right := .exceptionalExceptional
            hrightFirst hrightOutgoing rightEE } :
        R324PaperTwoHalfEndpointRoutes leftProviders rightProviders)) =
      leftEE.pack.data.eeeeTerminalData leftEE.outgoing
        rightEE.pack.data rightEE.outgoing := by
  unfold R324PaperTwoHalfEndpointRoutes.terminal
    R324PaperHalfEndpointRoute.completedRoute
    R324PaperHalfCompletedRoute.twoHalfTerminal
    R324IncomingExceptionalStopTraceAssembly.eeeeTerminalData
  rw [R324TwoHalfTerminalData.mk.injEq]
  exact ⟨leftEE.route_final, rightEE.route_final⟩

@[simp]
theorem cases_exceptionalExceptional_exceptionalExceptional
    (hleftFirst : (⟨0, leftProviders.hm⟩ : Fin m) ∉ finalActive kappaP)
    (hleftOutgoing : Fin.last m ∈ extractedRightEdges kappaP)
    (leftEE : R324PaperHalfExceptionalExceptionalRoute leftProviders)
    (hrightFirst : (⟨0, rightProviders.hm⟩ : Fin m) ∉ finalActive kappaM)
    (hrightOutgoing : Fin.last m ∈ extractedRightEdges kappaM)
    (rightEE : R324PaperHalfExceptionalExceptionalRoute rightProviders) :
    (R324PaperTwoHalfEndpointRoutes.cases
      ({ left := .exceptionalExceptional
            hleftFirst hleftOutgoing leftEE
         right := .exceptionalExceptional
            hrightFirst hrightOutgoing rightEE } :
        R324PaperTwoHalfEndpointRoutes leftProviders rightProviders)) =
      (fun _ => R324EndpointReductionCase.insertedSacrifice) := by
  unfold R324PaperTwoHalfEndpointRoutes.cases
    R324PaperHalfEndpointRoute.completedRoute
    R324PaperHalfCompletedRoute.combinedCases
  rw [leftEE.route_cases, rightEE.route_cases]
  funext i
  fin_cases i <;> rfl

/-- Common numerical exit for any two literal endpoint routes.  The only
branch-specific inputs are the exact signed collapse `hcollapse` and the
post-endpoint grouped domination `hendpoint`.  All scale products, the
remaining coupling power, and the complete nested run are consumed here.

This is deliberately stated for an arbitrary completed endpoint density;
the `EE x EE` branch supplies that density by applying
`lamEps_pow_integral_initialResidual_eq_singleParameter_incomingExceptional_outgoingExceptional`
to the two halves in succession. -/
theorem weighted_norm_le_endpointPatternAmbientMajorant_of_grouped
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
          ((paperFourthOrderModeDecay alpha *
                paperFourthOrderModeDecay beta) *
              r324EndpointPrimitiveSacrificeProduct eps routes.cases) *
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
              (r324TwoHalfCompleteAbsorbedBase A C K B)
              lam eps supportConstant m z
            ∂paperMeasure) := by
  let endpointWeight : Real :=
    (paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta) *
      r324EndpointPrimitiveSacrificeProduct eps routes.cases
  have hendpointWeight : 0 <= endpointWeight := by
    exact mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (r324EndpointPrimitiveSacrificeProduct_nonneg eps routes.cases)
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
        (by simpa only [endpointWeight] using hendpoint)
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
  simpa only [endpointWeight, mul_assoc] using hweighted

/-- Common numerical exit when an endpoint branch reaches the grouped
carrier with the fixed `EE × EE` mass compensation.  The compensation is
immediately absorbed into the final primitive base. -/
theorem weighted_norm_le_endpointPatternAmbientMajorant_of_grouped_compensated
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
          (eeeeEndpointMassCompensation *
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
              (eeeeEndpointCompleteAbsorbedBase A C K B)
              lam eps supportConstant m z
            ∂paperMeasure) := by
  let paperWeight : Real :=
    (paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta) *
      r324EndpointPrimitiveSacrificeProduct eps routes.cases
  let endpointWeight : Real :=
    eeeeEndpointMassCompensation * paperWeight
  have hpaperWeight : 0 <= paperWeight := by
    exact mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (r324EndpointPrimitiveSacrificeProduct_nonneg eps routes.cases)
  have hendpointWeight : 0 <= endpointWeight :=
    mul_nonneg
      (zero_le_one.trans one_le_eeeeEndpointMassCompensation)
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
  have hinflate := compensation_mul_integral_completeAbsorbed_le
    A C K B lam heps supportConstant hm
  calc
    _ <= endpointWeight *
        (∫ z : T4,
          primitiveInsertedMajorant
            (r324TwoHalfCompleteAbsorbedBase A C K B)
            lam eps supportConstant m z
          ∂paperMeasure) := hweighted
    _ = paperWeight *
        (eeeeEndpointMassCompensation *
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
            (eeeeEndpointCompleteAbsorbedBase A C K B)
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
