import Anderson4D.DetParametrix.Paper42_Moment.R324PaperLeftDirectExactTransform
import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalJointIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperOutgoingEndpointTargetIntegrability

/-!
# Closed direct-left exact transforms for paper Step 4(A)

The direct incoming Fourier identity leaves the opposite half untouched.
For a direct outgoing endpoint the only premise not already carried by the
physical-root entrance is joint integrability on the completed left carrier.
This file supplies exactly that premise from the two existing paper facts:

* the completed left Green chain is jointly `L¹` under its terminal edge
  certificate; and
* the untouched right initial residual is jointly `L¹`.

The complete residual primitive sum is kept as one bounded measurable
factor.  No norm is taken before either within-half removal.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-! ## The terminal-left / initial-right product regroup -/

/-- Reorder `((y, (zw, vr)), u)` as `((y, u), (zw, vr))`.
This is the literal parameter order needed to multiply the completed left
chain with the untouched right initial residual. -/
def r324PaperLeftTerminalRightInitialMeasurableEquiv
    (Y Rest U : Type*) [MeasurableSpace Y]
    [MeasurableSpace Rest] [MeasurableSpace U] :
    (Y × Rest) × U ≃ᵐ (Y × U) × Rest :=
  (MeasurableEquiv.prodAssoc
      (α := Y) (β := Rest) (γ := U)).trans
    ((r324MoveMiddleMeasurableEquiv Y Rest U).trans
      (MeasurableEquiv.prodComm :
        Rest × (Y × U) ≃ᵐ (Y × U) × Rest))

@[simp]
theorem r324PaperLeftTerminalRightInitialMeasurableEquiv_apply
    {Y Rest U : Type*} [MeasurableSpace Y]
    [MeasurableSpace Rest] [MeasurableSpace U]
    (q : (Y × Rest) × U) :
    r324PaperLeftTerminalRightInitialMeasurableEquiv Y Rest U q =
      ((q.1.1, q.2), q.1.2) :=
  rfl

/-- The regroup preserves the corresponding product measures. -/
theorem measurePreserving_r324PaperLeftTerminalRightInitialMeasurableEquiv
    {Y Rest U : Type*} [MeasurableSpace Y]
    [MeasurableSpace Rest] [MeasurableSpace U]
    (muY : Measure Y) (muRest : Measure Rest) (muU : Measure U)
    [SFinite muY] [SFinite muRest] [SFinite muU] :
    MeasurePreserving
      (r324PaperLeftTerminalRightInitialMeasurableEquiv Y Rest U)
      ((muY.prod muRest).prod muU)
      ((muY.prod muU).prod muRest) := by
  exact
    (Measure.measurePreserving_swap
        (μ := muRest) (ν := muY.prod muU)).comp
      ((measurePreserving_r324MoveMiddleMeasurableEquiv
          muY muRest muU).comp
        (measurePreserving_prodAssoc muY muRest muU))

variable {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {α β : Z4}

/-! ## Joint integrability of the completed direct-left density -/

/-- The exact terminal density required by the direct/direct left transform
is integrable.  The proof multiplies the two already established half-chain
`L¹` facts and only then attaches the still-grouped bounded covariance sum
and the unit-modulus Fourier characters. -/
theorem integrable_leftDirectTerminalCanonicalDensity
    (left : R324WithinHalfResidualPrefix ρ lam ε κp)
    (hleftRemaining : left.remaining = [])
    (leftScale : Fin (m + 1) → ℝ)
    (hleftCertificate :
      R324WithinHalfEdgeCertificate left.state leftScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (multiplier : ℂ)
    (π : κp.singles ≃ κm.singles) :
    Integrable
      (fun q :
          (T4 × R324PaperLeftOuterParameter ρ lam ε κm) ×
            (left.SurvivingCoordinate → T4) =>
        left.incomingPhasedResidualDensity
          (charT4 β q.1.1 *
            (multiplier *
              ((paperSecondOrderModeDecay α : ℂ) *
                r324PaperLeftCanonicalCoefficient left
                  α β π q.1.2 q.2)))
          α ρ ε 0 q.1.1 q.2)
      ((paperMeasure.prod
        (r324PaperLeftOuterParameterMeasure ρ lam ε κm)).prod
        (Measure.pi fun _ : left.SurvivingCoordinate => paperMeasure)) := by
  let muLeft : Measure (left.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let right := R324WithinHalfResidualPrefix.initial ρ lam ε κm
  let muRight : Measure (right.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let Rest := (T4 × T4) × (right.SurvivingCoordinate → T4)
  let muRest : Measure Rest :=
    (paperMeasure.prod paperMeasure).prod muRight
  have hleftRaw : Integrable
      (fun p : T4 × (left.SurvivingCoordinate → T4) =>
        (left.incomingErasedResidualIntegrand
          ρ ε 0 p.1 (left.reconstruct p.2) : ℂ))
      (paperMeasure.prod muLeft) := by
    exact
      (left.integrable_terminal_incomingErasedResidualIntegrand
        hleftRemaining ρ ε leftScale hleftCertificate).ofReal
  have hrightRaw : Integrable
      (fun p : (T4 × T4) × (right.SurvivingCoordinate → T4) =>
        ((right.residualIntegrand
          ρ ε p.1.1 p.1.2 (right.reconstruct p.2) : ℝ) : ℂ))
      muRest := by
    convert
      (integrable_initial_residualIntegrand_pair
        ρ lam hε hε1 κm).ofReal using 1
    funext p
    rfl
  have hproduct : Integrable
      (fun p :
          (T4 × (left.SurvivingCoordinate → T4)) × Rest =>
        (left.incomingErasedResidualIntegrand
          ρ ε 0 p.1.1 (left.reconstruct p.1.2) : ℂ) *
        (right.residualIntegrand
          ρ ε p.2.1.1 p.2.1.2
            (right.reconstruct p.2.2) : ℂ))
      ((paperMeasure.prod muLeft).prod muRest) :=
    hleftRaw.mul_prod hrightRaw
  let e :=
    r324PaperLeftTerminalRightInitialMeasurableEquiv
      T4 Rest (left.SurvivingCoordinate → T4)
  have he : MeasurePreserving e
      ((paperMeasure.prod muRest).prod muLeft)
      ((paperMeasure.prod muLeft).prod muRest) := by
    exact
      measurePreserving_r324PaperLeftTerminalRightInitialMeasurableEquiv
        paperMeasure muRest muLeft
  let bare :
      ((T4 × Rest) × (left.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      (left.incomingErasedResidualIntegrand
        ρ ε 0 q.1.1 (left.reconstruct q.2) : ℂ) *
      (right.residualIntegrand
        ρ ε q.1.2.1.1 q.1.2.1.2
          (right.reconstruct q.1.2.2) : ℂ)
  have hbare : Integrable bare ((paperMeasure.prod muRest).prod muLeft) := by
    have hcomp : Integrable
        ((fun p :
            (T4 × (left.SurvivingCoordinate → T4)) × Rest =>
          (left.incomingErasedResidualIntegrand
            ρ ε 0 p.1.1 (left.reconstruct p.1.2) : ℂ) *
          (right.residualIntegrand
            ρ ε p.2.1.1 p.2.1.2
              (right.reconstruct p.2.2) : ℂ)) ∘ e)
        ((paperMeasure.prod muRest).prod muLeft) :=
      (he.integrable_comp_emb e.measurableEmbedding).mpr hproduct
    apply hcomp.congr
    filter_upwards with q
    rfl
  let cross :
      ((T4 × Rest) × (left.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      (r324ResidualPrimitiveSumProduct ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct left right
          (q.2, q.1.2.2)) : ℂ)
  have hcrossMeas : Measurable cross := by
    apply Complex.measurable_ofReal.comp
    apply (ρ.measurable_r324ResidualPrimitiveSumProduct
      ε κp κm π).comp
    apply (measurable_r324TwoHalfRootDoubledReconstruct
      left right).comp
    exact measurable_snd.prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  obtain ⟨crossBound, _hcrossBound0, hcrossBound⟩ :=
    ρ.exists_norm_r324ResidualPrimitiveSumProduct_le
      hε hε1 κp κm π
  have hwithCross :=
    hbare.mul_bdd hcrossMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by
        simpa only [cross, Complex.norm_real] using
          hcrossBound
            (r324TwoHalfRootDoubledReconstruct left right
              (q.2, q.1.2.2)))
  let phase :
      ((T4 × Rest) × (left.SurvivingCoordinate → T4)) → ℂ :=
    fun q =>
      charT4 β q.1.1 *
        (multiplier *
          ((paperSecondOrderModeDecay α : ℂ) *
            (charT4 (-α) q.1.2.1.1 *
              charT4 (-β) q.1.2.1.2))) *
        charT4 α (left.incomingPhaseAnchor 0 q.1.1 q.2)
  have hphaseMeas : Measurable phase := by
    have hyMeas : Measurable
        (fun q : ((T4 × Rest) ×
            (left.SurvivingCoordinate → T4)) => q.1.1) :=
      measurable_fst.comp measurable_fst
    have hzwMeas : Measurable
        (fun q : ((T4 × Rest) ×
            (left.SurvivingCoordinate → T4)) => q.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hanchorMeas : Measurable
        (fun q : ((T4 × Rest) ×
            (left.SurvivingCoordinate → T4)) =>
          left.incomingPhaseAnchor 0 q.1.1 q.2) := by
      have hassembleMeas : Measurable
          (fun q : ((T4 × Rest) ×
              (left.SurvivingCoordinate → T4)) =>
            assemble (0 : T4) q.1.1 (left.reconstruct q.2)) :=
        (measurable_assemble_prod m).comp
          (measurable_const.prodMk
            (hyMeas.prodMk
              (left.measurable_reconstruct.comp measurable_snd)))
      exact
        (measurable_pi_apply (left.edgeSuccessor 0)).comp hassembleMeas
    unfold phase
    exact
      (((continuous_charT4 β).measurable.comp hyMeas).mul
        (measurable_const.mul
          (measurable_const.mul
            (((continuous_charT4 (-α)).measurable.comp
                (measurable_fst.comp hzwMeas)).mul
              ((continuous_charT4 (-β)).measurable.comp
                (measurable_snd.comp hzwMeas)))))).mul
        ((continuous_charT4 α).measurable.comp hanchorMeas)
  have hphaseBound : ∀ q, ‖phase q‖ ≤
      ‖multiplier * (paperSecondOrderModeDecay α : ℂ)‖ := by
    intro q
    unfold phase
    simp only [norm_mul, norm_charT4, one_mul, mul_one]
    ring_nf
    exact le_rfl
  have hfull :=
    hwithCross.bdd_mul hphaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hphaseBound)
  apply hfull.congr
  filter_upwards with q
  unfold bare cross phase r324PaperLeftCanonicalCoefficient
    R324WithinHalfResidualPrefix.incomingPhasedResidualDensity
  dsimp only [Rest, right]
  ring

/-! ## Closed direct/direct physical transform -/

/-- The direct/direct left transform with every analytic premise discharged
from the physical entrance and the two paper `L¹` producers above. -/
theorem leftDirectDirect_exactTransform_and_source_eq_physical_closed
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    {providers : R324PaperHalfRouteProviders
      (rho := ρ) (C := C) (lam := lam) (eps := ε)
      (K := K) (A := A) e0.1 α}
    (houtgoing : Fin.last m ∉ extractedRightEdges e0.1)
    (data : R324PaperHalfDirectDirectRoute providers)
    (β : Z4) :
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofDirectDirect
          houtgoing data).ExactTransform
          (r324PaperLeftOuterParameterMeasure ρ lam ε e0.2.1)
          (fun s v =>
            r324PaperLeftCanonicalCoefficient data.transport.final
              α β e0.2.2 s v)
          β,
      transform.source =
        r324RefinedPhysicalIntegral ρ ε m α β p := by
  obtain ⟨hleft, hphysical⟩ :=
    integrable_and_r324RefinedPhysicalIntegral_eq_leftDirectInitial
      (rho := ρ) (lam := lam) (eps := ε)
      p e0 he0 providers.heps providers.heps1 α β
  have hterminalCertificate :
      R324WithinHalfEdgeCertificate
        data.transport.final.state data.route.terminalScale := by
    rw [← data.route_final]
    exact data.route.terminalCertificate
  have hterminal :=
    integrable_leftDirectTerminalCanonicalDensity
      (α := α) (β := β)
      data.transport.final data.transport.final_remaining
      data.route.terminalScale hterminalCertificate
      providers.heps providers.heps1
      (data.transport.multiplier α) e0.2.2
  exact
    leftDirectDirect_exactTransform_and_source_eq_physical
      houtgoing data β e0.2.2
      (r324RefinedPhysicalIntegral ρ ε m α β p)
      hleft hphysical hterminal

/-! ## Closed direct/exceptional physical transform -/

/-- The direct/exceptional left transform with its three analytic premises
discharged from the physical entrance and the parameter-carrying endpoint
transport.  The Fourier character at the untouched endpoint is removed by
its inverse before the endpoint operation; no absolute value is taken. -/
theorem leftDirectExceptional_exactTransform_and_source_eq_physical_closed_with_targetIntegrable
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    {providers : R324PaperHalfRouteProviders
      (rho := ρ) (C := C) (lam := lam) (eps := ε)
      (K := K) (A := A) e0.1 α}
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (β : Z4) :
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofDirectExceptional data)
          |>.ExactTransform
            (r324PaperLeftOuterParameterMeasure ρ lam ε e0.2.1)
            (fun s v =>
              r324PaperLeftCanonicalCoefficient
                data.outgoing.terminalPost α β e0.2.2 s v)
            β,
      transform.source =
          r324RefinedPhysicalIntegral ρ ε m α β p ∧
        Integrable
          (fun q :
              R324PaperLeftOuterParameter ρ lam ε e0.2.1 ×
                (data.outgoing.terminalPost.SurvivingCoordinate → T4) =>
            (R324PaperHalfEndpointUniformBound.ofDirectExceptional data)
              |>.density
                (fun v =>
                  r324PaperLeftCanonicalCoefficient
                    data.outgoing.terminalPost α β e0.2.2 q.1 v)
                β q.2)
          ((r324PaperLeftOuterParameterMeasure ρ lam ε e0.2.1).prod
            (Measure.pi fun _ :
              data.outgoing.terminalPost.SurvivingCoordinate =>
                paperMeasure)) := by
  obtain ⟨hleft, hphysical⟩ :=
    integrable_and_r324RefinedPhysicalIntegral_eq_leftDirectInitial
      (rho := ρ) (lam := lam) (eps := ε)
      p e0 he0 providers.heps providers.heps1 α β
  let Outer := R324PaperLeftOuterParameter ρ lam ε e0.2.1
  let Initial :=
    (R324WithinHalfResidualPrefix.initial
      ρ lam ε e0.1).SurvivingCoordinate → T4
  let Stop := data.endpoint.stop.SurvivingCoordinate → T4
  let muOuter : Measure Outer :=
    r324PaperLeftOuterParameterMeasure ρ lam ε e0.2.1
  let muInitial : Measure Initial := Measure.pi fun _ => paperMeasure
  let muStop : Measure Stop := Measure.pi fun _ => paperMeasure
  let coefficient := fun
      (s : Outer)
      (v : data.outgoing.terminalPost.SurvivingCoordinate → T4) =>
    r324PaperLeftCanonicalCoefficient
      data.outgoing.terminalPost α β e0.2.2 s v
  let regroup :=
    r324SingleParameterTerminalRegroupMeasurableEquiv
      T4 Outer Initial
  have hpRegroup : MeasurePreserving regroup
      ((paperMeasure.prod muOuter).prod muInitial)
      (muOuter.prod (paperMeasure.prod muInitial)) := by
    exact
      measurePreserving_r324SingleParameterTerminalRegroupMeasurableEquiv
        paperMeasure muOuter muInitial
  let current : Outer × (T4 × Initial) → ℂ := fun q =>
    (R324WithinHalfResidualPrefix.initial ρ lam ε e0.1
      |>.incomingPhasedResidualDensity
        (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
          data coefficient q.1
            ((data.geometry.transport.stop
              |>.splitSurvivingPiMeasurableEquiv
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton
                (data.geometry.transport.projection q.2.2)).2))
        α ρ ε 0 q.2.1 q.2.2)
  let withPhase : Outer × (T4 × Initial) → ℂ := fun q =>
    charT4 β q.2.1 * current q
  have hpoint (q : (T4 × Outer) × Initial) :
      r324PaperLeftDirectInitialSourceDensity
          (rho := ρ) (lam := lam) (eps := ε)
          (kappaP := e0.1) (kappaM := e0.2.1)
          α β e0.2.2 q = withPhase (regroup q) := by
    simp only [regroup,
      r324SingleParameterTerminalRegroupMeasurableEquiv_apply]
    unfold r324PaperLeftDirectInitialSourceDensity withPhase current coefficient
    rw [r324PaperLeftCanonicalCoefficient_eq_directOutgoing
      data.outgoing β e0.2.2 q.1.2 q.2]
    rw [directExceptionalGeometryCoefficient_initialProjection data
      (fun s v =>
        r324PaperLeftCanonicalCoefficient
          data.outgoing.terminalPost α β e0.2.2 s v)
      q.1.2 q.2]
    unfold R324PaperHalfDirectExceptionalRoute.directIncomingEndpointCoefficient
    exact
      (R324WithinHalfResidualPrefix.initial ρ lam ε e0.1
        |>.incomingPhasedResidualDensity_const_mul
          (charT4 β q.1.1)
          ((paperSecondOrderModeDecay α : ℂ) *
            r324PaperLeftCanonicalCoefficient
              data.outgoing.terminalPost α β e0.2.2 q.1.2
              ((data.outgoing.endpoint.stop
                |>.splitSurvivingPiMeasurableEquiv
                  data.outgoing.terminalData.terminal []
                  data.outgoing.endpoint.stop_remaining
                  (data.outgoing.endpoint.projection q.2)).2))
          α ρ ε 0 q.1.1 q.2)
  have hphaseOnSource : Integrable
      (withPhase ∘ regroup)
      ((paperMeasure.prod muOuter).prod muInitial) := by
    apply hleft.congr
    filter_upwards with q
    exact hpoint q
  have hwithPhase : Integrable withPhase
      (muOuter.prod (paperMeasure.prod muInitial)) :=
    (hpRegroup.integrable_comp_emb regroup.measurableEmbedding).mp
      hphaseOnSource
  let inversePhase : Outer × (T4 × Initial) → ℂ := fun q =>
    charT4 (-β) q.2.1
  have hinversePhaseMeas : Measurable inversePhase :=
    (continuous_charT4 (-β)).measurable.comp
      (measurable_fst.comp measurable_snd)
  have hinversePhaseBound : ∀ q, ‖inversePhase q‖ ≤ 1 := by
    intro q
    unfold inversePhase
    rw [norm_charT4]
  have hcurrentWithInverse :=
    hwithPhase.mul_bdd hinversePhaseMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hinversePhaseBound)
  have hcurrent : Integrable current
      (muOuter.prod (paperMeasure.prod muInitial)) := by
    apply hcurrentWithInverse.congr
    filter_upwards with q
    unfold withPhase inversePhase
    calc
      (charT4 β q.2.1 * current q) * charT4 (-β) q.2.1 =
          (charT4 β q.2.1 * charT4 (-β) q.2.1) * current q := by
        ring
      _ = current q := by
        rw [charT4_mul_charT4_neg_self, one_mul]
  let assocInitial : (Outer × T4) × Initial ≃ᵐ
      Outer × (T4 × Initial) :=
    MeasurableEquiv.prodAssoc
  have hpAssocInitial : MeasurePreserving assocInitial
      ((muOuter.prod paperMeasure).prod muInitial)
      (muOuter.prod (paperMeasure.prod muInitial)) := by
    exact measurePreserving_prodAssoc muOuter paperMeasure muInitial
  have hcurrentAssoc : Integrable
      (fun q : (Outer × T4) × Initial => current (assocInitial q))
      ((muOuter.prod paperMeasure).prod muInitial) :=
    (hpAssocInitial.integrable_comp_emb
      assocInitial.measurableEmbedding).mpr hcurrent
  have hendpointInput : Integrable
      (fun p : (Outer × T4) × Initial =>
        (R324WithinHalfResidualPrefix.initial ρ lam ε e0.1
          |>.incomingPhasedResidualDensity
            (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data coefficient p.1.1
                ((data.endpoint.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.terminalData.terminal []
                    data.endpoint.stop_remaining
                    (data.endpoint.projection p.2)).2))
            α ρ ε 0 p.1.2 p.2))
      ((muOuter.prod paperMeasure).prod muInitial) := by
    convert hcurrentAssoc using 1
    funext p
    rfl
  have hstopAssoc :=
    data.endpoint.integrable_joint
      (muOuter.prod paperMeasure)
      (fun _ : Outer × T4 => 0)
      (fun q : Outer × T4 => q.2) α
      (fun q u =>
        R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
          data coefficient q.1
            ((data.geometry.transport.stop
              |>.splitSurvivingPiMeasurableEquiv
                data.geometry.terminalData.terminal []
                data.geometry.stop_remaining_eq_singleton u).2))
      hendpointInput
  let assocStop : (Outer × T4) × Stop ≃ᵐ
      Outer × (T4 × Stop) :=
    MeasurableEquiv.prodAssoc
  have hpAssocStop : MeasurePreserving assocStop
      ((muOuter.prod paperMeasure).prod muStop)
      (muOuter.prod (paperMeasure.prod muStop)) := by
    exact measurePreserving_prodAssoc muOuter paperMeasure muStop
  have hstop : Integrable
      (fun q : Outer × (T4 × Stop) =>
        data.geometry.transport.stop.incomingPhasedResidualDensity
          (data.geometry.transport.multiplier α *
            R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data coefficient q.1
                ((data.geometry.transport.stop
                  |>.splitSurvivingPiMeasurableEquiv
                    data.geometry.terminalData.terminal []
                    data.geometry.stop_remaining_eq_singleton q.2.2).2))
          α ρ ε 0 q.2.1 q.2.2)
      (muOuter.prod (paperMeasure.prod muStop)) := by
    refine (hpAssocStop.integrable_comp_emb
      assocStop.measurableEmbedding).mp ?_
    convert hstopAssoc using 1
    funext p
    rfl
  have hint :
      ∀ (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.geometry.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.geometry.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder
                data.geometry.terminalData.terminal.2)
              kappaB.1
              data.geometry.paperOutgoingTerminal.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.geometry.terminalData.terminal.2)
                data.geometry.paperOutgoingTerminal.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure) := by
    have hcertificate :
        R324WithinHalfEdgeCertificate
          data.geometry.paperOutgoingTerminal.terminalContext.state
          data.stopBudgetScale := by
      rw [data.geometry_paperOutgoingTerminal]
      exact data.stopBudgetCertificate
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := data.geometry.paperOutgoingTerminal.terminalContext)
        hcertificate providers.heps providers.heps1
        kappaB first (first - gap)
  have hmultiplier : data.geometry.transport.multiplier α = 1 := by
    simpa only [R324PaperHalfDirectExceptionalRoute.geometry] using
      data.endpoint_multiplier_eq_one α
  have hpredGeometry :
      r324WithinHalfPredecessorSlot
          data.geometry.paperOutgoingTerminal.endpoint.stop.state
          data.geometry.paperOutgoingTerminal.terminalData.terminal ≠ 0 := by
    change r324WithinHalfPredecessorSlot
        data.endpoint.stop.state data.terminalData.terminal ≠ 0
    exact data.predecessor_ne_zero
  have hactiveGeometry :
      data.geometry.paperOutgoingTerminal.terminalPost.state.active.Nonempty := by
    rw [data.geometry_paperOutgoingTerminal]
    exact data.terminalPost_active
  have htargetGeometry :=
    R324PaperOutgoingEndpointTerminal.integrable_parameter_outgoingEndpointDefectDensity
        data.geometry.paperOutgoingTerminal
        hpredGeometry hactiveGeometry
        muOuter
        (fun s v =>
          data.geometry.transport.multiplier α *
            R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data coefficient s v)
        α β (fun _ => 0)
        (by
          dsimp only [Outer, Stop, muOuter, muStop, coefficient,
            R324WithinHalfEndpointTerminalGeometry.paperOutgoingTerminal,
            R324PaperHalfDirectExceptionalRoute.geometry]
          convert hstop using 1 <;> rfl)
        hint
  have htargetGeometry' : Integrable
      (fun q : Outer ×
          (data.geometry.paperOutgoingTerminal.terminalPost.SurvivingCoordinate →
            T4) =>
        ∫ first : T4,
          data.geometry.paperOutgoingTerminal.outgoingEndpointDefectDensity
            (R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient
              data coefficient q.1)
            α β 0 q.2 first
          ∂paperMeasure)
      (muOuter.prod (Measure.pi fun _ :
        data.geometry.paperOutgoingTerminal.terminalPost.SurvivingCoordinate =>
          paperMeasure)) := by
    apply htargetGeometry.congr
    filter_upwards with q
    apply integral_congr_ae
    filter_upwards with first
    apply congrArg
      (fun c =>
        data.geometry.paperOutgoingTerminal.outgoingEndpointDefectDensity
          c α β 0 q.2 first)
    funext v
    rw [hmultiplier, one_mul]
  have htarget : Integrable
      (fun q : Outer ×
          (data.outgoing.terminalPost.SurvivingCoordinate → T4) =>
        data.endpointDensity (coefficient q.1) β 0 q.2)
      (muOuter.prod (Measure.pi fun _ :
        data.outgoing.terminalPost.SurvivingCoordinate => paperMeasure)) := by
    unfold R324PaperHalfDirectExceptionalRoute.endpointDensity
    exact
      R324PaperOutgoingEndpointTerminal.integrable_parameter_outgoingEndpointDefectDensity_transport
        data.geometry_paperOutgoingTerminal muOuter
          (fun s => data.directIncomingEndpointCoefficient (coefficient s))
          α β (fun _ => 0)
          (by
            simpa only [
              R324PaperHalfEndpointUniformBound.ExactTransform.directExceptionalGeometryCoefficient]
              using htargetGeometry')
  obtain ⟨transform, htransform⟩ :=
    leftDirectExceptional_exactTransform_and_source_eq_physical
      data β e0.2.2
      (r324RefinedPhysicalIntegral ρ ε m α β p)
      hphysical
      (by simpa only [Outer, Initial, muOuter, muInitial,
        coefficient, current] using hcurrent)
      (by
        dsimp only [Outer, Stop, muOuter, muStop, coefficient,
          R324PaperHalfDirectExceptionalRoute.geometry]
        convert hstop using 1 <;> rfl)
      hint
  refine ⟨transform, htransform, ?_⟩
  simpa only [Outer, muOuter, coefficient,
    R324PaperHalfEndpointUniformBound.ofDirectExceptional] using htarget

/-- Compatibility wrapper retaining the original exact-transform API. -/
theorem leftDirectExceptional_exactTransform_and_source_eq_physical_closed
    (p : R324RefinedScheduleIndex m)
    (e0 : MomentContraction m)
    (he0 : e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    {providers : R324PaperHalfRouteProviders
      (rho := ρ) (C := C) (lam := lam) (eps := ε)
      (K := K) (A := A) e0.1 α}
    (data : R324PaperHalfDirectExceptionalRoute providers)
    (β : Z4) :
    ∃ transform :
        (R324PaperHalfEndpointUniformBound.ofDirectExceptional data)
          |>.ExactTransform
            (r324PaperLeftOuterParameterMeasure ρ lam ε e0.2.1)
            (fun s v =>
              r324PaperLeftCanonicalCoefficient
                data.outgoing.terminalPost α β e0.2.2 s v)
            β,
      transform.source =
        r324RefinedPhysicalIntegral ρ ε m α β p := by
  obtain ⟨transform, hsource, _⟩ :=
    leftDirectExceptional_exactTransform_and_source_eq_physical_closed_with_targetIntegrable
      p e0 he0 data β
  exact ⟨transform, hsource⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
