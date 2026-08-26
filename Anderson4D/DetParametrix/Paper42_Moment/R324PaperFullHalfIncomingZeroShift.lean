import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullStep1ReductionProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324DriverRootInstantiation

/-!
# The full-pairing half in incoming-first paper order

For the zero conserved-shift part of paper Section 4.2 Step 4(A), a
complete half is most efficiently evaluated from the exceptional incoming
block.  This is not a new analytic argument: the certified incoming-stop
Fubini seam and the alternating driver already perform all interval
removals in the required order.  The small adapters below identify their
generic initial source with the existing complete endpoint-fibre sum.

No norm is taken in this file before the whole half has reached the empty
terminal carrier.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {rho : SmoothCutoff} {C lam eps K : Real}
    {q : Nat} {kappa : PartialPairing (Fin (2 * q))}
    {initialScale : Fin (2 * q + 1) -> Real}

/-- The untouched outgoing endpoint character of one complete half. -/
def fullHalfOutgoingPostOuter
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (beta : Z4) (y : T4)
    (_v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate -> T4) :
    Complex :=
  charT4 beta y

/-- Joint integrability of the literal complete-half source.  This is just
the already-proved joint `L1` theorem for the initial residual, multiplied
by two unimodular endpoint characters. -/
theorem integrable_fullHalfIncomingInitialSource
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (alpha beta : Z4) :
    Integrable
      (data.incomingExceptionalInitialSourceDensity
        alpha (fun y : T4 => y)
        (data.fullHalfOutgoingPostOuter beta))
      ((paperMeasure.prod paperMeasure).prod
        (Measure.pi fun _ :
          (R324WithinHalfResidualPrefix.initial
            rho lam eps kappa).SurvivingCoordinate => paperMeasure)) := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps kappa
  let phase :
      (T4 × T4) × (initial.SurvivingCoordinate -> T4) -> Complex :=
    fun p => charT4 alpha p.1.1 * charT4 beta p.1.2
  have hraw :
      Integrable
        (fun p : (T4 × T4) × (initial.SurvivingCoordinate -> T4) =>
          ((initial.residualIntegrand rho eps p.1.1 p.1.2
            (initial.reconstruct p.2) : Real) : Complex))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure)) :=
    (integrable_initial_residualIntegrand_pair
      rho lam heps heps1 kappa).ofReal
  have hphase : Measurable phase := by
    dsimp only [phase]
    exact
      ((continuous_charT4 alpha).measurable.comp
        (measurable_fst.comp measurable_fst)).mul
      ((continuous_charT4 beta).measurable.comp
        (measurable_snd.comp measurable_fst))
  have hproduct := hraw.mul_bdd hphase.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by
      dsimp only [phase]
      simp only [norm_mul, norm_charT4, one_mul]
      exact le_rfl)
  apply hproduct.congr
  filter_upwards with p
  unfold incomingExceptionalInitialSourceDensity
    fullHalfOutgoingPostOuter
  dsimp only [initial, phase]

/-- The generic exceptional-stop initial source is exactly the weighted
complete endpoint-fibre half.  The only work is the standard initial
sparse-carrier reindex and product reassociation. -/
theorem lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfIncomingSource
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (hkappa : kappa.IsFull)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (alpha beta : Z4) :
    (lamEps lam eps : Complex) ^ (2 * q) *
        (Finset.univ.sum fun tau : ReductionEndpointFiberAt kappa =>
          deterministicFullHalfIntegral
            rho eps (2 * q) alpha beta tau.1) =
      (lamEps lam eps : Complex) ^ (2 * q) *
        (∫ p,
          data.incomingExceptionalInitialSourceDensity
            alpha (fun y : T4 => y)
            (data.fullHalfOutgoingPostOuter beta) p
          ∂((paperMeasure.prod paperMeasure).prod
            (Measure.pi fun _ :
              (R324WithinHalfResidualPrefix.initial
                rho lam eps kappa).SurvivingCoordinate => paperMeasure))) := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps kappa
  let eInternal := initialPiMeasurableEquiv rho lam eps kappa
  let e :
      ((T4 × T4) × (initial.SurvivingCoordinate -> T4)) ≃ᵐ
        T4 × (T4 × (Fin (2 * q) -> T4)) :=
    MeasurableEquiv.prodAssoc.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl T4) eInternal))
  have heInternal :
      MeasurePreserving eInternal
        (Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure)
        (Measure.pi fun _ : Fin (2 * q) => paperMeasure) := by
    simpa only [initial, eInternal] using
      measurePreserving_initialPiMeasurableEquiv rho lam eps kappa
  have he :
      MeasurePreserving e
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin (2 * q) => paperMeasure))) := by
    exact
      ((MeasurePreserving.id paperMeasure).prod
        ((MeasurePreserving.id paperMeasure).prod heInternal)).comp
      (measurePreserving_prodAssoc paperMeasure paperMeasure
        (Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure))
  let target : T4 × (T4 × (Fin (2 * q) -> T4)) -> Complex :=
    fun p => charT4 alpha p.1 * charT4 beta p.2.1 *
      ((initial.residualIntegrand rho eps p.1 p.2.1 p.2.2 : Real) : Complex)
  have hpoint :
      (fun p : (T4 × T4) × (initial.SurvivingCoordinate -> T4) =>
        data.incomingExceptionalInitialSourceDensity
          alpha (fun y : T4 => y)
          (data.fullHalfOutgoingPostOuter beta) p) =
        fun p => target (e p) := by
    funext p
    have heval :
        e p = (p.1.1, p.1.2,
          initialPiMeasurableEquiv rho lam eps kappa p.2) := by
      rfl
    rw [heval]
    unfold incomingExceptionalInitialSourceDensity
      fullHalfOutgoingPostOuter
    dsimp only [target]
    rw [initial_reconstruct_eq rho lam eps kappa]
    ring
  have hreindex :
      (∫ p,
          data.incomingExceptionalInitialSourceDensity
            alpha (fun y : T4 => y)
            (data.fullHalfOutgoingPostOuter beta) p
          ∂((paperMeasure.prod paperMeasure).prod
            (Measure.pi fun _ : initial.SurvivingCoordinate => paperMeasure))) =
        ∫ p, target p
          ∂(paperMeasure.prod
            (paperMeasure.prod
              (Measure.pi fun _ : Fin (2 * q) => paperMeasure))) := by
    rw [hpoint]
    exact he.integral_comp e.measurableEmbedding target
  rw [hreindex]
  congr 1
  simpa only [target, initial] using
    sum_deterministicFullHalfIntegral_eq_integral_initialGroupedResidual
      rho heps heps1 lam q alpha beta kappa hkappa

/-- The incoming head coefficient of a complete half.  The outgoing
character is the only dependence on the outer endpoint, and there is no
dependence on any surviving internal coordinate. -/
def fullHalfIncomingCoefficient
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (alpha beta : Z4) (y : T4) : Complex :=
  (paperSecondOrderModeDecay alpha : Complex) ^ 2 *
    incomingExceptionalPrimitiveDefect rho lam eps
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges alpha *
    charT4 beta y

/-- Specialization of the generic post coefficient to a complete half. -/
theorem incomingExceptionalPostCoefficient_fullHalf
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (alpha beta : Z4) (y : T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate -> T4) :
    data.incomingExceptionalPostCoefficient alpha
        (data.fullHalfOutgoingPostOuter beta) y v =
      data.fullHalfIncomingCoefficient alpha beta y := by
  rfl

/-- The initial source license transported to the certified stop. -/
theorem integrable_fullHalfIncomingStopSource
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (alpha beta : Z4) :
    Integrable
      (data.incomingExceptionalStopSourceDensity
        alpha (fun y : T4 => y)
        (data.fullHalfOutgoingPostOuter beta))
      ((paperMeasure.prod paperMeasure).prod
        (Measure.pi fun _ : data.trace.stopPrefix.SurvivingCoordinate =>
          paperMeasure)) := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps kappa
  let split :=
    data.trace.stopPrefix.splitSurvivingPiMeasurableEquiv
      data.terminal data.suffix data.trace.stopPrefix_remaining_eq
  let stopOuter :
      T4 × T4 ->
        (data.trace.stopPrefix.SurvivingCoordinate -> T4) -> Complex :=
    fun ep w => charT4 alpha ep.1 *
      data.fullHalfOutgoingPostOuter beta ep.2 (split w).2
  have hcurrent :=
    data.integrable_fullHalfIncomingInitialSource heps heps1 alpha beta
  exact
    data.trace.integrable_joint_residualIntegrand_mul_stopOuter_stopPrefix
      (paperMeasure.prod paperMeasure)
      (fun ep : T4 × T4 => ep.1)
      (fun ep : T4 × T4 => ep.2)
      stopOuter hcurrent

/-- Exact paper-ordered collapse of the incoming exceptional head of a
complete half.  All prefix removals and the head Fourier calculation are
finished before the displayed primitive defect appears. -/
theorem lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfAfterHead
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (hkappa : kappa.IsFull) (hq : 1 <= q)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hG : forall j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (alpha beta : Z4) :
    (lamEps lam eps : Complex) ^ (2 * q) *
        (∑ tau : ReductionEndpointFiberAt kappa,
          deterministicFullHalfIntegral
            rho eps (2 * q) alpha beta tau.1) =
      (lamEps lam eps : Complex) ^
          (2 *
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).remainingOrder) *
        (∫ p,
          data.incomingExceptionalAfterHeadPhasedIntegrand
            alpha (fun y : T4 => y)
            (data.fullHalfOutgoingPostOuter beta) p
          ∂(paperMeasure.prod
            (Measure.pi fun _ :
              (data.trace.stopPrefix.afterHead
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                  paperMeasure))) := by
  have hcurrent :=
    data.integrable_fullHalfIncomingInitialSource heps heps1 alpha beta
  have hstop :=
    data.integrable_fullHalfIncomingStopSource heps heps1 alpha beta
  have htoStop :=
    data.lamEps_pow_integral_initialResidual_eq_incomingExceptionalStopFourier
      paperMeasure (by omega : 0 < 2 * q) alpha (fun y : T4 => y)
      (data.fullHalfOutgoingPostOuter beta) hcurrent
  have hcollapse :=
    data.lamEps_pow_integral_incomingExceptionalStopFourierDensity_eq_afterHead
      paperMeasure (by omega : 0 < 2 * q) alpha (fun y : T4 => y)
      (data.fullHalfOutgoingPostOuter beta) hstop hG hint
  calc
    (lamEps lam eps : Complex) ^ (2 * q) *
          (∑ tau : ReductionEndpointFiberAt kappa,
            deterministicFullHalfIntegral
              rho eps (2 * q) alpha beta tau.1) =
        (lamEps lam eps : Complex) ^ (2 * q) *
          (∫ p,
            data.incomingExceptionalInitialSourceDensity
              alpha (fun y : T4 => y)
              (data.fullHalfOutgoingPostOuter beta) p
            ∂((paperMeasure.prod paperMeasure).prod
              (Measure.pi fun _ :
                (R324WithinHalfResidualPrefix.initial
                  rho lam eps kappa).SurvivingCoordinate => paperMeasure))) :=
      data.lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfIncomingSource
        hkappa heps heps1 alpha beta
    _ = (lamEps lam eps : Complex) ^
          (2 * data.trace.stopPrefix.remainingOrder) *
        (∫ p,
          data.incomingExceptionalStopFourierDensity
            alpha (fun y : T4 => y)
            (data.fullHalfOutgoingPostOuter beta) p
          ∂(paperMeasure.prod
            ((Measure.pi fun _ :
                Fin (2 * residualBlockOrder data.terminal.2) => paperMeasure).prod
              (Measure.pi fun _ :
                (data.trace.stopPrefix.afterHead
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq).SurvivingCoordinate =>
                    paperMeasure)))) := by
      rw [R324FullPairingBudgetTerminalAdapter.initial_remainingOrder_eq
        (ρ := rho) (lam := lam) (ε := eps) hkappa] at htoStop
      exact htoStop
    _ = _ := hcollapse

/-- The remaining suffix is consumed by the already-proved alternating
driver.  The norm is still not taken: the result is an exact integral over
the outgoing endpoint and the terminal carrier. -/
theorem lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfDriverTerminal
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (transport :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hkappa : kappa.IsFull) (hq : 1 <= q)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hG : forall j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (alpha beta : Z4) :
    (lamEps lam eps : Complex) ^ (2 * q) *
        (∑ tau : ReductionEndpointFiberAt kappa,
          deterministicFullHalfIntegral
            rho eps (2 * q) alpha beta tau.1) =
      ∫ y : T4,
        transport.multiplier alpha *
          (∫ u : transport.final.SurvivingCoordinate -> T4,
            transport.final.incomingPhasedResidualDensity
              (data.fullHalfIncomingCoefficient alpha beta y)
              alpha rho eps 0 y u
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure := by
  have hstop :=
    data.integrable_fullHalfIncomingStopSource heps heps1 alpha beta
  have hafter :=
    data.integrable_incomingExceptionalAfterHeadPhasedIntegrand
      paperMeasure (by omega : 0 < 2 * q) alpha (fun y : T4 => y)
      (data.fullHalfOutgoingPostOuter beta) hstop hG hint
  refine
    (data.lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfAfterHead
      hkappa hq heps heps1 hG hint alpha beta).trans ?_
  rw [integral_prod _ hafter, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hafter.prod_right_ae] with y hy
  have hsection :
      (fun v :
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).SurvivingCoordinate -> T4 =>
        data.incomingExceptionalAfterHeadPhasedIntegrand
          alpha (fun y' : T4 => y')
          (data.fullHalfOutgoingPostOuter beta) (y, v)) =
        fun v =>
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
              (data.fullHalfIncomingCoefficient alpha beta y)
              alpha rho eps 0 y v := by
    funext v
    unfold incomingExceptionalAfterHeadPhasedIntegrand
    rw [data.incomingExceptionalPostCoefficient_fullHalf alpha beta y v]
  rw [hsection] at hy ⊢
  exact
    transport.lamEps_pow_integral_incomingPhasedResidualDensity_eq_multiplier_mul_final
      0 y alpha (fun _ => data.fullHalfIncomingCoefficient alpha beta y) hy

/-- On a full pairing the driver terminal carrier is empty.  At zero
conserved shift its remaining endpoint integral is exactly the paper torus
mass.  Thus one complete half contributes the fourth-order incoming-mode
factor before any absolute value is taken. -/
theorem lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfZeroShift
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := rho) (C := C) (lam := lam)
        (ε := eps) (K := K) kappa initialScale)
    (transport :
      R324WithinHalfAlternatingTransport
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hkappa : kappa.IsFull) (hq : 1 <= q)
    (heps : 0 < eps) (heps1 : eps <= 1)
    (hG : forall j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminal.2)
              kappaB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (alpha beta : Z4) (hshift : alpha + beta = 0) :
    (lamEps lam eps : Complex) ^ (2 * q) *
        (∑ tau : ReductionEndpointFiberAt kappa,
          deterministicFullHalfIntegral
            rho eps (2 * q) alpha beta tau.1) =
      transport.multiplier alpha *
        ((r324PaperTorusMass : Complex) *
          ((paperSecondOrderModeDecay alpha : Complex) ^ 2 *
            incomingExceptionalPrimitiveDefect rho lam eps
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder
              data.stopContext.internalEdges alpha)) := by
  have hempty : transport.final.state.active = ∅ :=
    transport.final_active_eq_finalActive.trans
      (finalActive_eq_empty_of_full hkappa)
  letI : IsEmpty transport.final.SurvivingCoordinate :=
    ⟨fun i => by
      have hi : i.1 ∈ (∅ : Finset (Fin (2 * q))) := by
        simpa only [hempty] using i.2
      simp at hi⟩
  have hinter (y : T4) :
      (∫ u : transport.final.SurvivingCoordinate -> T4,
        transport.final.incomingPhasedResidualDensity
          (data.fullHalfIncomingCoefficient alpha beta y)
          alpha rho eps 0 y u
        ∂Measure.pi fun _ => paperMeasure) =
      data.fullHalfIncomingCoefficient alpha beta y * charT4 alpha y := by
    rw [show
      (fun u : transport.final.SurvivingCoordinate -> T4 =>
        transport.final.incomingPhasedResidualDensity
          (data.fullHalfIncomingCoefficient alpha beta y)
          alpha rho eps 0 y u) =
        fun _ => data.fullHalfIncomingCoefficient alpha beta y *
          charT4 alpha y by
      funext u
      exact transport.final.terminal_incomingPhasedResidualDensity_eq_of_active_empty
        transport.final_remaining hempty
        (data.fullHalfIncomingCoefficient alpha beta y)
        alpha rho eps 0 y u]
    rw [integral_const, measureReal_def, Measure.pi_empty_univ,
      ENNReal.toReal_one, one_smul]
  rw [data.lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfDriverTerminal
    transport hkappa hq heps heps1 hG hint alpha beta]
  simp_rw [hinter]
  have hshift' : beta + alpha = 0 := by
    simpa only [add_comm] using hshift
  have hfun :
      (fun y : T4 =>
        transport.multiplier alpha *
          (data.fullHalfIncomingCoefficient alpha beta y *
            charT4 alpha y)) =
        fun y =>
          (transport.multiplier alpha *
            ((paperSecondOrderModeDecay alpha : Complex) ^ 2 *
              incomingExceptionalPrimitiveDefect rho lam eps
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                data.stopContext.internalEdges alpha)) *
            charT4 (beta + alpha) y := by
    funext y
    unfold fullHalfIncomingCoefficient
    rw [charT4_add]
    ring
  rw [hfun, integral_const_mul, integral_charT4_paper, if_pos hshift']
  unfold r324PaperTorusMass
  ring


end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
