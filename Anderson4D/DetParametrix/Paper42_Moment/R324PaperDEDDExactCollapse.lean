import Anderson4D.DetParametrix.Paper42_Moment.R324PaperDEDDWeightedMajorant

/-!
# Exact signed `DE x DD` composition for paper Step 4(A)

The left retained terminal has already been evaluated by the ordinary-`J`
identity.  Its completed carrier and free endpoint are then kept as one
untouched parameter while the right direct/direct half is transported and
Fourier-integrated.  No norm or pointwise majorant occurs in this file.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-! ## The one-free-endpoint Fubini regroup -/

/-- Regroup `((left, firstLeft), right)` as
`((left, right), firstLeft)`. -/
def r324DEDDEndpointRegroupMeasurableEquiv
    (L R : Type*) [MeasurableSpace L] [MeasurableSpace R] :
    ((L × T4) × R) ≃ᵐ ((L × R) × T4) :=
  (MeasurableEquiv.prodAssoc
      (α := L) (β := T4) (γ := R)).trans
    ((MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl L)
        (MeasurableEquiv.prodComm : T4 × R ≃ᵐ R × T4)).trans
      (MeasurableEquiv.prodAssoc
        (α := L) (β := R) (γ := T4)).symm)

@[simp]
theorem r324DEDDEndpointRegroupMeasurableEquiv_apply
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (q : (L × T4) × R) :
    r324DEDDEndpointRegroupMeasurableEquiv L R q =
      ((q.1.1, q.2), q.1.2) :=
  rfl

@[simp]
theorem r324DEDDEndpointRegroupMeasurableEquiv_symm_apply
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (q : (L × R) × T4) :
    (r324DEDDEndpointRegroupMeasurableEquiv L R).symm q =
      ((q.1.1, q.2), q.1.2) :=
  rfl

theorem measurePreserving_r324DEDDEndpointRegroupMeasurableEquiv
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (muL : Measure L) (muR : Measure R)
    [SFinite muL] [SFinite muR] :
    MeasurePreserving
      (r324DEDDEndpointRegroupMeasurableEquiv L R)
      ((muL.prod paperMeasure).prod muR)
      ((muL.prod muR).prod paperMeasure) := by
  exact
    (measurePreserving_prodAssoc muL muR paperMeasure).symm.comp
      (((MeasurePreserving.id muL).prod
          (Measure.measurePreserving_swap
            (μ := paperMeasure) (ν := muR))).comp
        (measurePreserving_prodAssoc muL paperMeasure muR))

/-- Fubini is used only on the jointly integrable density after the left
ordinary-`J` operation and the right direct Fourier operation are both
complete. -/
theorem integral_deddEndpoint_regroup
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (muL : Measure L) (muR : Measure R)
    [SFinite muL] [SFinite muR]
    (F : ((L × T4) × R) -> Complex)
    (hF : Integrable F ((muL.prod paperMeasure).prod muR)) :
    (∫ u : L × T4, ∫ v : R, F (u, v) ∂muR
      ∂(muL.prod paperMeasure)) =
      ∫ p : L × R, ∫ firstLeft : T4,
        F ((p.1, firstLeft), p.2) ∂paperMeasure
      ∂(muL.prod muR) := by
  let sigma := r324DEDDEndpointRegroupMeasurableEquiv L R
  have hsigma :
      MeasurePreserving sigma
        ((muL.prod paperMeasure).prod muR)
        ((muL.prod muR).prod paperMeasure) :=
    measurePreserving_r324DEDDEndpointRegroupMeasurableEquiv muL muR
  let G : (L × R) × T4 -> Complex := fun q => F (sigma.symm q)
  have hG : Integrable G ((muL.prod muR).prod paperMeasure) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hF.congr
    filter_upwards with q
    show F q = G (sigma q)
    unfold G
    rw [MeasurableEquiv.symm_apply_apply]
  have hcombined :
      (∫ q, F q ∂((muL.prod paperMeasure).prod muR)) =
        ∫ q, G q ∂((muL.prod muR).prod paperMeasure) := by
    rw [← hsigma.integral_comp' G]
    apply integral_congr_ae
    filter_upwards with q
    simp only [G, MeasurableEquiv.symm_apply_apply]
  calc
    (∫ u : L × T4, ∫ v : R, F (u, v) ∂muR
        ∂(muL.prod paperMeasure)) =
      ∫ q, F q ∂((muL.prod paperMeasure).prod muR) := by
        rw [integral_prod _ hF]
    _ = ∫ q, G q ∂((muL.prod muR).prod paperMeasure) := hcombined
    _ = ∫ p : L × R, ∫ firstLeft : T4,
          F ((p.1, firstLeft), p.2) ∂paperMeasure
        ∂(muL.prod muR) := by
      rw [integral_prod _ hG]
      apply integral_congr_ae
      filter_upwards with p
      simp only [G, sigma,
        r324DEDDEndpointRegroupMeasurableEquiv_symm_apply]

namespace R324PaperHalfDirectExceptionalRoute

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    {leftProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode}

/-- The literal signed density after the left `DE` operation and the right
`DD` operation have both finished.  The left free endpoint is part of the
parameter `u`; the right direct outgoing endpoint has already been Fourier
integrated. -/
def deddFinalRawEndpointDensity
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (red :
      ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ->
        (rightDD.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (rightIncomingMode rightOutgoingMode : Z4)
    (u : (leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4)
    (v : rightDD.transport.final.SurvivingCoordinate -> T4) : Complex :=
  (rightDD.transport.multiplier rightIncomingMode * red u v) *
    charT4 rightIncomingMode
      (rightDD.transport.final.terminalIncomingAnchor
        (rightDD.transport.final.reconstruct v)) *
    ((rightDD.transport.final.endpointErasedSignedChain
      hactive 0 0
      (rightDD.transport.final.reconstruct v) : Real) : Complex) *
    translatedGreenMode rightOutgoingMode
      (rightDD.transport.final.terminalOutgoingAnchor
        hactive
        (rightDD.transport.final.reconstruct v))

/-- Algebraic composition of a completed left `DE` collapse with the
parameterized right `DD` theorem.  `hleftCollapse` is precisely the signed
output of the left retained-terminal identity after the harmless product
reassociation that places the right initial carrier last. -/
theorem lamEps_pow_twoHalfPhysical_eq_deddFinalRaw_of_rightDirect
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (physical : Complex)
    (red :
      ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ->
        (rightDD.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (rightIncomingMode rightOutgoingMode : Z4)
    (hleftCollapse :
      (lamEps lam eps : Complex) ^
            (2 * (R324WithinHalfResidualPrefix.initial
              rho lam eps kappaP).remainingOrder) * physical =
        ∫ q :
            (T4 ×
              ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
                T4)) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate -> T4),
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM
            |>.incomingPhasedResidualDensity
              (charT4 rightOutgoingMode q.1.1 *
                red q.1.2 (rightDD.transport.projection q.2))
              rightIncomingMode rho eps 0 q.1.1 q.2)
          ∂((paperMeasure.prod
            ((Measure.pi fun _ :
                leftDE.outgoing.terminalPost.SurvivingCoordinate =>
              paperMeasure).prod paperMeasure)).prod
            (Measure.pi fun _ => paperMeasure)))
    (hcurrent :
      Integrable
        (fun q :
            (T4 ×
              ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
                T4)) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate -> T4) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM
            |>.incomingPhasedResidualDensity
              (charT4 rightOutgoingMode q.1.1 *
                red q.1.2 (rightDD.transport.projection q.2))
              rightIncomingMode rho eps 0 q.1.1 q.2))
        ((paperMeasure.prod
          ((Measure.pi fun _ :
              leftDE.outgoing.terminalPost.SurvivingCoordinate =>
            paperMeasure).prod paperMeasure)).prod
          (Measure.pi fun _ => paperMeasure)))
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (hedge :
      rightDD.transport.final.state.edges
          (rightDD.transport.final.terminalOutgoingEdgeSlot hactive) =
        greenFn)
    (hterminal :
      Integrable
        (fun q :
            (T4 ×
              ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
                T4)) ×
              (rightDD.transport.final.SurvivingCoordinate -> T4) =>
          rightDD.transport.final.incomingPhasedResidualDensity
            (charT4 rightOutgoingMode q.1.1 *
              (rightDD.transport.multiplier rightIncomingMode *
                red q.1.2 q.2))
            rightIncomingMode rho eps 0 q.1.1 q.2)
        ((paperMeasure.prod
          ((Measure.pi fun _ :
              leftDE.outgoing.terminalPost.SurvivingCoordinate =>
            paperMeasure).prod paperMeasure)).prod
          (Measure.pi fun _ => paperMeasure))) :
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * physical =
      ∫ u :
          (leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4,
        ∫ v : rightDD.transport.final.SurvivingCoordinate -> T4,
          deddFinalRawEndpointDensity leftDE rightDD red hactive
            rightIncomingMode rightOutgoingMode u v
          ∂Measure.pi fun _ => paperMeasure
        ∂((Measure.pi fun _ => paperMeasure).prod paperMeasure) := by
  let muLeft :=
    (Measure.pi fun _ :
      leftDE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure).prod
      paperMeasure
  have hright :=
    rightDD.transport
      |>.lamEps_pow_integral_initialResidual_eq_singleParameter_directDirect
        muLeft red rightIncomingMode rightOutgoingMode
        (by simpa only [muLeft] using hcurrent) hactive hedge
        (by simpa only [muLeft] using hterminal)
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
        (∫ q :
            (T4 ×
              ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
                T4)) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).SurvivingCoordinate -> T4),
          (R324WithinHalfResidualPrefix.initial rho lam eps kappaM
            |>.incomingPhasedResidualDensity
              (charT4 rightOutgoingMode q.1.1 *
                red q.1.2 (rightDD.transport.projection q.2))
              rightIncomingMode rho eps 0 q.1.1 q.2)
          ∂((paperMeasure.prod muLeft).prod
            (Measure.pi fun _ => paperMeasure))) := by
      rw [hleftCollapse]
    _ = _ := by
      simpa only [deddFinalRawEndpointDensity, leftOrder, rightOrder, muLeft]
        using hright

/-- Reindex the completed `DE x DD` density onto the literal nested carrier
used by the common Step-3/Step-4 numerical exit. -/
def deddNestedEndpointDensity
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (red :
      ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ->
        (rightDD.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (rightIncomingMode rightOutgoingMode : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (v :
      (R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
        leftDE rightDD).NestedCoordinate pi -> T4) : Complex :=
  let terminal :=
    R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
      leftDE rightDD
  let p := (terminal.terminalProductPiMeasurableEquivNested pi).symm v
  ∫ firstLeft : T4,
    deddFinalRawEndpointDensity leftDE rightDD red hactive
      rightIncomingMode rightOutgoingMode (p.1, firstLeft) p.2
    ∂paperMeasure

/-- Final Fubini/reindexing after both endpoint operations. -/
theorem integral_deddFinalRaw_eq_integral_nestedEndpointDensity
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (red :
      ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ->
        (rightDD.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (rightIncomingMode rightOutgoingMode : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hraw :
      Integrable
        (fun q :
            ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
                T4) ×
              (rightDD.transport.final.SurvivingCoordinate -> T4) =>
          deddFinalRawEndpointDensity leftDE rightDD red hactive
            rightIncomingMode rightOutgoingMode q.1 q.2)
        (((Measure.pi fun _ :
              leftDE.outgoing.terminalPost.SurvivingCoordinate =>
            paperMeasure).prod paperMeasure).prod
          (Measure.pi fun _ :
            rightDD.transport.final.SurvivingCoordinate =>
              paperMeasure))) :
    (∫ u :
          (leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4,
        ∫ v : rightDD.transport.final.SurvivingCoordinate -> T4,
          deddFinalRawEndpointDensity leftDE rightDD red hactive
            rightIncomingMode rightOutgoingMode u v
          ∂Measure.pi fun _ => paperMeasure
        ∂((Measure.pi fun _ => paperMeasure).prod paperMeasure)) =
      ∫ v :
          (R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
            leftDE rightDD).NestedCoordinate pi -> T4,
        deddNestedEndpointDensity leftDE rightDD red hactive
          rightIncomingMode rightOutgoingMode pi v
        ∂Measure.pi fun _ => paperMeasure := by
  let terminal :=
    R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
      leftDE rightDD
  let muLeft :=
    Measure.pi fun _ :
      leftDE.outgoing.terminalPost.SurvivingCoordinate => paperMeasure
  let muRight :=
    Measure.pi fun _ :
      rightDD.transport.final.SurvivingCoordinate => paperMeasure
  let F :
      (((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ×
        (rightDD.transport.final.SurvivingCoordinate -> T4)) -> Complex :=
    fun q => deddFinalRawEndpointDensity leftDE rightDD red hactive
      rightIncomingMode rightOutgoingMode q.1 q.2
  let productDensity :
      ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
        (rightDD.transport.final.SurvivingCoordinate -> T4)) -> Complex :=
    fun p => ∫ firstLeft : T4,
      F ((p.1, firstLeft), p.2) ∂paperMeasure
  have hreorder := integral_deddEndpoint_regroup muLeft muRight F
    (by simpa only [F, muLeft, muRight] using hraw)
  have hp :=
    terminal.measurePreserving_terminalProductPiMeasurableEquivNested pi
  have hnested :
      (∫ p, productDensity p ∂(muLeft.prod muRight)) =
        ∫ v : terminal.NestedCoordinate pi -> T4,
          deddNestedEndpointDensity leftDE rightDD red hactive
            rightIncomingMode rightOutgoingMode pi v
          ∂Measure.pi fun _ => paperMeasure := by
    rw [← hp.integral_comp'
      (deddNestedEndpointDensity leftDE rightDD red hactive
        rightIncomingMode rightOutgoingMode pi)]
    apply integral_congr_ae
    filter_upwards with p
    simp only [deddNestedEndpointDensity, terminal,
      MeasurableEquiv.symm_apply_apply, productDensity, F]
  exact hreorder.trans hnested

/-- Consumer form: any exact product-carrier `DE x DD` collapse is carried
without loss to the common nested endpoint density. -/
theorem lamEps_pow_twoHalfPhysical_eq_deddNested_of_raw
    (leftDE : R324PaperHalfDirectExceptionalRoute leftProviders)
    (rightDD : R324PaperHalfDirectDirectRoute rightProviders)
    (physical : Complex)
    (red :
      ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4) ->
        (rightDD.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (hactive : rightDD.transport.final.state.active.Nonempty)
    (rightIncomingMode rightOutgoingMode : Z4)
    (pi : kappaP.singles ≃ kappaM.singles)
    (hrawCollapse :
      (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * physical =
        ∫ u :
            (leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) × T4,
          ∫ v : rightDD.transport.final.SurvivingCoordinate -> T4,
            deddFinalRawEndpointDensity leftDE rightDD red hactive
              rightIncomingMode rightOutgoingMode u v
            ∂Measure.pi fun _ => paperMeasure
          ∂((Measure.pi fun _ => paperMeasure).prod paperMeasure))
    (hraw :
      Integrable
        (fun q :
            ((leftDE.outgoing.terminalPost.SurvivingCoordinate -> T4) ×
                T4) ×
              (rightDD.transport.final.SurvivingCoordinate -> T4) =>
          deddFinalRawEndpointDensity leftDE rightDD red hactive
            rightIncomingMode rightOutgoingMode q.1 q.2)
        (((Measure.pi fun _ :
              leftDE.outgoing.terminalPost.SurvivingCoordinate =>
            paperMeasure).prod paperMeasure).prod
          (Measure.pi fun _ :
            rightDD.transport.final.SurvivingCoordinate =>
              paperMeasure))) :
    (lamEps lam eps : Complex) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                rho lam eps kappaP).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappaM).remainingOrder)) * physical =
      ∫ v :
          (R324PaperTwoHalfEndpointRoutes.directExceptionalDirectDirectTerminalData
            leftDE rightDD).NestedCoordinate pi -> T4,
        deddNestedEndpointDensity leftDE rightDD red hactive
          rightIncomingMode rightOutgoingMode pi v
        ∂Measure.pi fun _ => paperMeasure :=
  hrawCollapse.trans
    (integral_deddFinalRaw_eq_integral_nestedEndpointDensity
      leftDE rightDD red hactive rightIncomingMode rightOutgoingMode pi hraw)

end R324PaperHalfDirectExceptionalRoute
end R324WithinHalfResidualPrefix

end

end Anderson4D
