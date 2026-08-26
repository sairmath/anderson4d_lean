import Anderson4D.DetParametrix.Paper42_Moment.R324DirectIncomingInitialFourier
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointTwoHalfSplice
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointTransformEE
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTwoHalfEndpointProduct

/-!
# The right direct-incoming source after the completed left half

This is the single Fubini/Fourier move used at the interface between the
two endpoint halves in paper Step 4(A).  The completed left carrier is kept
as an untouched parameter, the four factors remain signed, and only then is
the right incoming endpoint integrated by the exact initial Green Fourier
identity.

No endpoint estimate and no absolute value occurs in this file.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-! ## Literal coefficient linearity of the four canonical left routes -/

namespace R324PaperHalfEndpointUniformBound

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}
    {incomingMode : Z4}
    {providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode}

/-- Coefficient linearity for the literal `DD` density. -/
theorem density_mul_ofDirectDirect
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (data : R324PaperHalfDirectDirectRoute providers)
    (a : Complex)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.transport.final.SurvivingCoordinate -> T4) :
    (R324PaperHalfEndpointUniformBound.ofDirectDirect houtgoing data).density
        (fun u => a * coefficient u) outgoingMode v =
      a *
        (R324PaperHalfEndpointUniformBound.ofDirectDirect houtgoing data).density
          coefficient outgoingMode v := by
  change data.transportEndpointDensity _ (fun u => a * coefficient u)
      outgoingMode v =
    a * data.transportEndpointDensity _ coefficient outgoingMode v
  unfold R324PaperHalfDirectDirectRoute.transportEndpointDensity
    R324PaperHalfDirectDirectRoute.directIncomingCoefficient
  ring

/-- Coefficient linearity for the literal `DE` density. -/
theorem density_mul_ofDirectExceptional
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (a : Complex)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    (R324PaperHalfEndpointUniformBound.ofDirectExceptional data).density
        (fun u => a * coefficient u) outgoingMode v =
      a *
        (R324PaperHalfEndpointUniformBound.ofDirectExceptional data).density
          coefficient outgoingMode v := by
  change data.endpointDensity (fun u => a * coefficient u)
      outgoingMode 0 v =
    a * data.endpointDensity coefficient outgoingMode 0 v
  unfold R324PaperHalfDirectExceptionalRoute.endpointDensity
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with first
  unfold R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
    R324PaperOutgoingEndpointTerminal.terminalSplitOuter
    R324PaperHalfDirectExceptionalRoute.directIncomingEndpointCoefficient
  ring

/-- Coefficient linearity for the literal `ED` density. -/
theorem density_mul_ofExceptionalDirect
    (houtgoing : Fin.last m ∉ extractedRightEdges pairing)
    (data : R324PaperHalfExceptionalDirectRoute providers)
    (a : Complex)
    (coefficient :
      (data.transport.final.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.transport.final.SurvivingCoordinate -> T4) :
    (R324PaperHalfEndpointUniformBound.ofExceptionalDirect houtgoing data).density
        (fun u => a * coefficient u) outgoingMode v =
      a *
        (R324PaperHalfEndpointUniformBound.ofExceptionalDirect houtgoing data).density
          coefficient outgoingMode v := by
  change data.endpointDensity _ (fun u => a * coefficient u)
      outgoingMode v =
    a * data.endpointDensity _ coefficient outgoingMode v
  unfold R324PaperHalfExceptionalDirectRoute.endpointDensity
    R324PaperHalfExceptionalDirectRoute.incomingEndpointCoefficient
  ring

/-- Coefficient linearity for the literal `EE` density. -/
theorem density_mul_ofExceptionalExceptional
    (hsingles : pairing.singles.Nonempty)
    (data : R324PaperHalfExceptionalExceptionalRoute providers)
    (a : Complex)
    (coefficient :
      (data.outgoing.terminalPost.SurvivingCoordinate -> T4) -> Complex)
    (outgoingMode : Z4)
    (v : data.outgoing.terminalPost.SurvivingCoordinate -> T4) :
    (R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
        hsingles data).density
        (fun u => a * coefficient u) outgoingMode v =
      a *
        (R324PaperHalfEndpointUniformBound.ofExceptionalExceptional
          hsingles data).density coefficient outgoingMode v := by
  change data.endpointDensity (fun u => a * coefficient u)
      outgoingMode 0 v =
    a * data.endpointDensity coefficient outgoingMode 0 v
  unfold R324PaperHalfExceptionalExceptionalRoute.endpointDensity
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with first
  unfold R324PaperOutgoingEndpointTerminal.outgoingEndpointDefectDensity
    R324PaperOutgoingEndpointTerminal.terminalSplitOuter
    R324PaperHalfExceptionalExceptionalRoute.incomingEndpointCoefficient
  ring

end R324PaperHalfEndpointUniformBound

/-! ## Cross-factor projection for a direct right incoming route -/

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {kappaP kappaM : PartialPairing (Fin m)}
    {rightMode : Z4}
    {rightProviders : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode}

/-- A direct right half transported through the full alternating schedule
does not change the cross primitive factor. -/
theorem r324ResidualPrimitiveSumProduct_eq_rightDirectTransportProjection
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    (data : R324PaperHalfDirectDirectRoute rightProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (vl : left.SurvivingCoordinate -> T4)
    (vr : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate -> T4) :
    r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (vl, vr)) =
      r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left data.transport.final
          (vl, data.transport.projection vr)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
  · have hqRight : m ≤ q.val := by omega
    obtain ⟨i, hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq hqRight
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]
    let iFinal : data.transport.final.SurvivingCoordinate :=
      ⟨i, by
        rw [data.transport.final_active_eq_finalActive]
        exact hiFinal⟩
    exact data.transport.reconstruct_projection vr iFinal

/-- The direct right half with a retained outgoing terminal likewise reads
the cross factor on its post-terminal carrier. -/
theorem r324ResidualPrimitiveSumProduct_eq_rightDirectOutgoingTerminalPost
    (left : R324WithinHalfResidualPrefix rho lam eps kappaP)
    (data : R324PaperHalfDirectExceptionalRoute rightProviders)
    (pi : kappaP.singles ≃ kappaM.singles)
    (vl : left.SurvivingCoordinate -> T4)
    (vr : (R324WithinHalfResidualPrefix.initial
      rho lam eps kappaM).SurvivingCoordinate -> T4) :
    r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left (R324WithinHalfResidualPrefix.initial rho lam eps kappaM)
          (vl, vr)) =
      r324ResidualPrimitiveSumProduct rho eps kappaP kappaM pi
        (r324TwoHalfRootDoubledReconstruct
          left data.outgoing.terminalPost
          (vl,
            (data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
              data.outgoing.terminalData.terminal []
              data.outgoing.endpoint.stop_remaining
              (data.outgoing.endpoint.projection vr)).2)) := by
  apply r324ResidualPrimitiveSumProduct_congr_on_active
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, _hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive hq hqLeft
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
  · have hqRight : m ≤ q.val := by omega
    obtain ⟨i, hiFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive hq hqRight
    simp only [r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]
    have hiPost : i ∈ data.outgoing.terminalPost.state.active := by
      rw [data.outgoing.terminalPost_active_eq_finalActive]
      exact hiFinal
    let iPost : data.outgoing.terminalPost.SurvivingCoordinate :=
      ⟨i, hiPost⟩
    let iStop : data.outgoing.endpoint.stop.SurvivingCoordinate :=
      data.outgoing.endpoint.stop.postSurvivingCoordinate
        data.outgoing.terminalData.terminal []
        data.outgoing.endpoint.stop_remaining iPost
    calc
      (R324WithinHalfResidualPrefix.initial rho lam eps kappaM).reconstruct
          vr i =
        data.outgoing.endpoint.stop.reconstruct
          (data.outgoing.endpoint.projection vr) i := by
            exact data.outgoing.endpoint.reconstruct_projection vr
              ⟨i, data.outgoing.endpoint.finalActive_subset_stop_active
                hiFinal⟩
      _ = data.outgoing.endpoint.projection vr iStop := by
        exact data.outgoing.endpoint.stop.reconstruct_surviving
          (data.outgoing.endpoint.projection vr) iStop
      _ =
          (data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            data.outgoing.terminalData.terminal []
            data.outgoing.endpoint.stop_remaining
            (data.outgoing.endpoint.projection vr)).2 iPost := by
        exact
          (data.outgoing.endpoint.stop
            |>.splitSurvivingPiMeasurableEquiv_apply_snd
              data.outgoing.terminalData.terminal []
              data.outgoing.endpoint.stop_remaining
              (data.outgoing.endpoint.projection vr) iPost).symm
      _ = data.outgoing.terminalPost.reconstruct
          ((data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
            data.outgoing.terminalData.terminal []
            data.outgoing.endpoint.stop_remaining
            (data.outgoing.endpoint.projection vr)).2) i := by
        exact
          (data.outgoing.terminalPost.reconstruct_surviving
            ((data.outgoing.endpoint.stop.splitSurvivingPiMeasurableEquiv
              data.outgoing.terminalData.terminal []
              data.outgoing.endpoint.stop_remaining
              (data.outgoing.endpoint.projection vr)).2) iPost).symm

/-! ## The paper's right-incoming regroup -/

/-- Reorder `(((z,w),vR),vL)` as `(((w,vL),vR),z)`.  Thus the incoming
right endpoint `z` is the last variable, while `(w,vL,vR)` is exactly the
parameter carrier of the right initial phased density. -/
def r324RightDirectIncomingFourierRegroupMeasurableEquiv
    (Z W R L : Type*) [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace R] [MeasurableSpace L] :
    (((Z × W) × R) × L) ≃ᵐ (((W × L) × R) × Z) :=
  (r324TwoHalfRightInitialSourceRegroupMeasurableEquiv Z W R L).trans
    ((MeasurableEquiv.prodAssoc
      (α := Z) (β := W × L) (γ := R)).trans
      (MeasurableEquiv.prodComm :
        Z × ((W × L) × R) ≃ᵐ ((W × L) × R) × Z))

@[simp]
theorem r324RightDirectIncomingFourierRegroupMeasurableEquiv_apply
    {Z W R L : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace R] [MeasurableSpace L]
    (q : ((Z × W) × R) × L) :
    r324RightDirectIncomingFourierRegroupMeasurableEquiv Z W R L q =
      (((q.1.1.2, q.2), q.1.2), q.1.1.1) :=
  rfl

@[simp]
theorem r324RightDirectIncomingFourierRegroupMeasurableEquiv_symm_apply
    {Z W R L : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace R] [MeasurableSpace L]
    (q : ((W × L) × R) × Z) :
    (r324RightDirectIncomingFourierRegroupMeasurableEquiv Z W R L).symm q =
      (((q.2, q.1.1.1), q.1.2), q.1.1.2) :=
  rfl

/-- The regroup preserves the literal four-factor product measure. -/
theorem measurePreserving_r324RightDirectIncomingFourierRegroupMeasurableEquiv
    {Z W R L : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSpace R] [MeasurableSpace L]
    (muZ : Measure Z) (muW : Measure W)
    (muR : Measure R) (muL : Measure L)
    [SFinite muZ] [SFinite muW] [SFinite muR] [SFinite muL] :
    MeasurePreserving
      (r324RightDirectIncomingFourierRegroupMeasurableEquiv Z W R L)
      (((muZ.prod muW).prod muR).prod muL)
      (((muW.prod muL).prod muR).prod muZ) := by
  let first :=
    r324TwoHalfRightInitialSourceRegroupMeasurableEquiv Z W R L
  have hfirst : MeasurePreserving first
      (((muZ.prod muW).prod muR).prod muL)
      ((muZ.prod (muW.prod muL)).prod muR) :=
    measurePreserving_r324TwoHalfRightInitialSourceRegroupMeasurableEquiv
      muZ muW muR muL
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc
        (α := Z) (β := W × L) (γ := R))
      ((muZ.prod (muW.prod muL)).prod muR)
      (muZ.prod ((muW.prod muL).prod muR)) :=
    measurePreserving_prodAssoc muZ (muW.prod muL) muR
  have hswap : MeasurePreserving
      (MeasurableEquiv.prodComm :
        Z × ((W × L) × R) ≃ᵐ ((W × L) × R) × Z)
      (muZ.prod ((muW.prod muL).prod muR))
      (((muW.prod muL).prod muR).prod muZ) :=
    Measure.measurePreserving_swap
      (μ := muZ) (ν := (muW.prod muL).prod muR)
  exact hswap.comp (hassoc.comp hfirst)

/-! ## Signed parameterized incoming Fourier collapse -/

/-- The completed left carrier may occur in an arbitrary signed scalar
`coefficient`.  Joint integrability of the genuine pre-Fourier density is
the only Fubini premise.  The conclusion supplies both the integrability
of the right initial source and its exact equality with the regrouped left
integral.

The four canonical left endpoint densities are plugged into `coefficient`
by small pointwise adapters; this theorem deliberately does not assume a
new abstract linearity field on the common endpoint interface. -/
theorem integrable_and_integral_rightDirectIncomingSource
    (rho : SmoothCutoff) (lam eps : Real)
    {m : Nat} (pairing : PartialPairing (Fin m))
    {L : Type*} [MeasurableSpace L]
    (muL : Measure L) [SFinite muL]
    (coefficient : T4 ->
      ((R324WithinHalfResidualPrefix.initial
        rho lam eps pairing).SurvivingCoordinate -> T4) -> L -> Complex)
    (incomingMode : Z4)
    (hraw :
      Integrable
        (fun q :
            (((T4 × T4) ×
                ((R324WithinHalfResidualPrefix.initial
                  rho lam eps pairing).SurvivingCoordinate -> T4)) × L) =>
          charT4 incomingMode q.1.1.1 *
            (((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).residualIntegrand
              rho eps q.1.1.1 q.1.1.2
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).reconstruct q.1.2) : Complex) *
              coefficient q.1.1.2 q.1.2 q.2))
        ((((paperMeasure.prod paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate => paperMeasure)).prod
          muL))) :
    Integrable
        (fun q : (T4 × L) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4) =>
          (R324WithinHalfResidualPrefix.initial rho lam eps pairing
            |>.incomingPhasedResidualDensity
              ((paperSecondOrderModeDecay incomingMode : Complex) *
                coefficient q.1.1 q.2 q.1.2)
              incomingMode rho eps 0 q.1.1 q.2))
        ((paperMeasure.prod muL).prod
          (Measure.pi fun _ :
            (R324WithinHalfResidualPrefix.initial
              rho lam eps pairing).SurvivingCoordinate => paperMeasure)) ∧
      (   (∫ s : (T4 × T4) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4),
              ∫ u : L,
                charT4 incomingMode s.1.1 *
                  (((R324WithinHalfResidualPrefix.initial
                      rho lam eps pairing).residualIntegrand
                    rho eps s.1.1 s.1.2
                    ((R324WithinHalfResidualPrefix.initial
                      rho lam eps pairing).reconstruct s.2) : Complex) *
                    coefficient s.1.2 s.2 u)
                ∂muL
              ∂((paperMeasure.prod paperMeasure).prod
                (Measure.pi fun _ => paperMeasure))) =
          ∫ q : (T4 × L) ×
              ((R324WithinHalfResidualPrefix.initial
                rho lam eps pairing).SurvivingCoordinate -> T4),
            (R324WithinHalfResidualPrefix.initial rho lam eps pairing
              |>.incomingPhasedResidualDensity
                ((paperSecondOrderModeDecay incomingMode : Complex) *
                  coefficient q.1.1 q.2 q.1.2)
                incomingMode rho eps 0 q.1.1 q.2)
            ∂((paperMeasure.prod muL).prod
              (Measure.pi fun _ => paperMeasure))) := by
  let initial :=
    R324WithinHalfResidualPrefix.initial rho lam eps pairing
  let muR := Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure
  let muRest := (paperMeasure.prod muL).prod muR
  let sigma :=
    r324RightDirectIncomingFourierRegroupMeasurableEquiv
      T4 T4 (initial.SurvivingCoordinate -> T4) L
  let F : ((((T4 × T4) ×
      (initial.SurvivingCoordinate -> T4)) × L)) -> Complex :=
    fun q =>
      charT4 incomingMode q.1.1.1 *
        ((initial.residualIntegrand rho eps q.1.1.1 q.1.1.2
          (initial.reconstruct q.1.2) : Complex) *
          coefficient q.1.1.2 q.1.2 q.2)
  let G : ((((T4 × L) ×
      (initial.SurvivingCoordinate -> T4)) × T4)) -> Complex :=
    fun q => F (sigma.symm q)
  let H : ((T4 × L) ×
      (initial.SurvivingCoordinate -> T4)) -> Complex :=
    fun q => initial.incomingPhasedResidualDensity
      ((paperSecondOrderModeDecay incomingMode : Complex) *
        coefficient q.1.1 q.2 q.1.2)
      incomingMode rho eps 0 q.1.1 q.2
  have hsigma : MeasurePreserving sigma
      ((((paperMeasure.prod paperMeasure).prod muR).prod muL))
      (muRest.prod paperMeasure) := by
    simpa only [sigma, muR, muRest] using
      measurePreserving_r324RightDirectIncomingFourierRegroupMeasurableEquiv
        paperMeasure paperMeasure muR muL
  have hpoint (q : ((T4 × T4) ×
      (initial.SurvivingCoordinate -> T4)) × L) :
      F q = G (sigma q) := by
    unfold G
    rw [MeasurableEquiv.symm_apply_apply]
  have hG : Integrable G (muRest.prod paperMeasure) := by
    refine (hsigma.integrable_comp_emb sigma.measurableEmbedding).mp ?_
    apply hraw.congr
    filter_upwards with q
    exact hpoint q
  have hsection (q : (T4 × L) ×
      (initial.SurvivingCoordinate -> T4)) :
      (∫ z, G (q, z) ∂paperMeasure) = H q := by
    simpa only [G, F, H, sigma,
      r324RightDirectIncomingFourierRegroupMeasurableEquiv_symm_apply,
      initial] using
      integral_charT4_mul_initialResidual_mul_const_eq_incomingPhased
        rho lam eps pairing
        (coefficient q.1.1 q.2 q.1.2)
        incomingMode q.1.1 q.2
  have hH : Integrable H muRest := by
    apply hG.integral_prod_left.congr
    filter_upwards with q
    exact hsection q
  refine ⟨by simpa only [H, muRest, muR, initial] using hH, ?_⟩
  calc
    (∫ s : (T4 × T4) ×
          (initial.SurvivingCoordinate -> T4),
        ∫ u : L, F (s, u) ∂muL
        ∂((paperMeasure.prod paperMeasure).prod muR)) =
        ∫ q, F q
          ∂((((paperMeasure.prod paperMeasure).prod muR).prod muL)) := by
      exact
        (integral_prod _
          (by simpa only [F, initial, muR] using hraw)).symm
    _ = ∫ q, G (sigma q)
          ∂((((paperMeasure.prod paperMeasure).prod muR).prod muL)) := by
      apply integral_congr_ae
      filter_upwards with q
      exact hpoint q
    _ = ∫ q, G q ∂(muRest.prod paperMeasure) :=
      hsigma.integral_comp sigma.measurableEmbedding G
    _ = ∫ q, ∫ z, G (q, z) ∂paperMeasure ∂muRest := by
      rw [integral_prod _ hG]
    _ = ∫ q, H q ∂muRest := by
      apply integral_congr_ae
      filter_upwards with q
      exact hsection q
    _ = _ := by
      rfl

/-! Branch-specific source equalities are assembled at their call sites
from the generic theorem above and the four strict-green density-linearity
lemmas.  Keeping a second wrapper here only duplicated elaboration. -/

end R324WithinHalfResidualPrefix

end

end Anderson4D
