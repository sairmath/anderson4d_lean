import Anderson4D.DetParametrix.Paper42_Moment.R324PaperBudgetedAlternatingTransport
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperFullHalfIncomingZeroShift
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointCaseAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324TwoHalfTraceScaleLedger
import Anderson4D.DetParametrix.Paper42_Moment.R324CertificateScaledPrimitiveDefect
import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedBlockProductClosure

/-!
# Paper Step 4(A): complete full/full zero-shift producer

This file is the numerical closure of the exact paper-ordered identities
already proved upstream.  The first incoming primitive defect pays the one
ordinary-majorant endpoint loss.  Every later exceptional head is absorbed
by the synchronized complete budget, so no second endpoint loss is charged
inside either half.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {q : Nat} {kappa : PartialPairing (Fin (2 * q))}

/-- Exact terminal slot-zero ledger for a complete full-pairing half. -/
theorem terminalBudgetScale_zero_eq_closedForm_of_full
    {res : R324WithinHalfResidualPrefix rho lam eps kappa}
    (transport : R324WithinHalfAlternatingTransport res)
    (terminalBudgetScale : Fin (2 * q + 1) -> Real)
    (terminalReachable :
      R324WithinHalfBudgetScaleReachable
        kappa rho C lam eps K A
        transport.final.state terminalBudgetScale)
    (hkappa : kappa.IsFull) :
    terminalBudgetScale 0 =
      A ^ (2 * q + 1) * (C * lam) ^ (2 * q) *
        K ^ transport.final.state.processed.length := by
  have hclosed := terminalReachable.activeEdgeScaleProduct_eq
  have hempty : transport.final.state.active = ∅ :=
    transport.final_active_eq_finalActive.trans
      (finalActive_eq_empty_of_full hkappa)
  have horder :
      r324WithinHalfProcessedOrder transport.final.state = q := by
    unfold r324WithinHalfProcessedOrder
    rw [transport.final_processed_eq_schedule]
    exact
      R324FullPairingBudgetTerminalAdapter.initial_remainingOrder_eq
        (ρ := rho) (lam := lam) (ε := eps) hkappa
  rw [hempty, horder,
    r324InitialActiveScaleProduct_eq_pow rho lam eps kappa A] at hclosed
  simpa using hclosed

/-! ## One complete half, with the endpoint loss paid once -/

/-- Paper Step 4(A), complete full-pairing half at zero conserved shift.
All exact interval removals precede the norm.  The displayed `eps^-2` is
the sole ordinary-majorant loss of this half. -/
theorem exists_fullPairing_half_endpointZeroShift_bound
    (rho : SmoothCutoff) :
    exists Cdet : Real, 0 < Cdet /\
      forall (lam eps : Real) (q : Nat)
        (kappa : PartialPairing (Fin (2 * q))),
        0 < lam -> 0 < eps -> eps <= 1 ->
        1 <= abs (Real.log eps) -> q <= truncOrder eps ->
        1 <= q -> kappa.IsFull ->
        forall alpha beta : Z4, alpha + beta = 0 ->
          ‖(lamEps lam eps : Complex) ^ (2 * q) *
              (Finset.univ.sum fun tau : ReductionEndpointFiberAt kappa =>
                deterministicFullHalfIntegral
                  rho eps (2 * q) alpha beta tau.1)‖ <=
            paperFourthOrderModeDecay alpha *
              (eps⁻¹ ^ (2 : Nat) *
                ((Cdet * lam) ^ (2 * q) / abs (Real.log eps))) := by
  obtain ⟨supportConstant, primitiveConstant,
      hsupport, hprimitive, hprop⟩ :=
    proposition41_at_truncation rho
  obtain ⟨K0, hK0, hlocal⟩ :=
    exists_r324WithinHalf_localBlockClosure hsupport
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  obtain ⟨CballInserted, CregInserted,
      hCballInserted, hCregInserted, hInsertedIntegral⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  obtain ⟨CballOrdinary, CregOrdinary,
      hCballOrdinary, hCregOrdinary, hOrdinaryIntegral⟩ :=
    exists_integral_primitiveKernelMajorant_le
  let Q : Real := (1 / 2 : Real) * max 1 (supportConstant ^ 2)
  let insertedMass : Real :=
    CballInserted * supportConstant ^ 2 + 2 * CregInserted
  let K : Real := max 1 (max K0 (Q * insertedMass))
  let ordinaryMass : Real :=
    CballOrdinary * supportConstant ^ 2 + CregOrdinary
  let D : Real := 2 * r324PaperTorusMass * ordinaryMass
  let multiplier : Real := A ^ 2 * max 1 K * (D + 1)
  let Cdet : Real := primitiveConstant * multiplier
  have hQ : 0 <= Q := by
    dsimp only [Q]
    positivity
  have hInsertedMass : 0 < insertedMass := by
    dsimp only [insertedMass]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    exact zero_lt_one.trans_le (le_max_left _ _)
  have hKone : 1 <= K := by
    dsimp only [K]
    exact le_max_left _ _
  have hK0K : K0 <= K := by
    dsimp only [K]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hQInsertedK : Q * insertedMass <= K := by
    dsimp only [K]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hOrdinaryMass : 0 < ordinaryMass := by
    dsimp only [ordinaryMass]
    positivity
  have hD : 0 <= D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg (by norm_num) r324PaperTorusMass_pos.le)
      hOrdinaryMass.le
  have hmultiplier : 0 < multiplier := by
    dsimp only [multiplier]
    have hApos : 0 < A := zero_lt_one.trans_le hA
    have hKmax : 0 < max 1 K :=
      zero_lt_one.trans_le (le_max_left _ _)
    positivity
  have hCdet : 0 < Cdet := by
    dsimp only [Cdet]
    exact mul_pos hprimitive hmultiplier
  refine ⟨Cdet, hCdet, ?_⟩
  intro lam eps q kappa hlam heps heps1 hlog htrunc hq hkappa alpha beta hshift
  let propProvider :
      R324WithinHalfProp41Provider
        rho primitiveConstant lam eps supportConstant kappa := by
    intro res head tail hremaining H hH
    have hheadSchedule : head ∈ r322AnalyticSchedule kappa :=
      (res.headContext head tail hremaining).step_mem_schedule
    have hheadMapped :
        head.2 ∈ (r322AnalyticSchedule kappa).map Prod.snd :=
      List.mem_map.mpr ⟨head, hheadSchedule, rfl⟩
    have hheadExtraction : head.2 ∈ extractionBlocks kappa :=
      (r322AnalyticSchedule_blocks_perm_extractionBlocks kappa).mem_iff.mp
        hheadMapped
    exact hprop lam eps (residualBlockOrder head.2)
      (res.headContext head tail hremaining).one_le_blockOrder H
      hlam heps heps1
      (extractionBlockOrder_le_truncOrder
        kappa hkappa hheadExtraction eps htrunc) hH
  let localProvider0 :
      R324WithinHalfLocalBlockProvider
        rho primitiveConstant lam eps K0 kappa := by
    intro res head tail hremaining scale certificate
    exact hlocal rho primitiveConstant lam eps (2 * q) kappa
      res head tail hremaining scale certificate
      hprimitive hlam heps heps1 hlog
      (fun H hH => propProvider res head tail hremaining H hH)
  let localProvider :
      R324WithinHalfLocalBlockProvider
        rho primitiveConstant lam eps K kappa :=
    R324WithinHalfLocalBlockProvider.mono_K
      hprimitive.le hlam.le hK0K localProvider0
  let budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho primitiveConstant lam eps K A kappa :=
    r324WithinHalfBudgetLocalBlockProvider_of_localBlockProvider
      hA localProvider
  have hcharge : forall n : Nat, 1 <= n ->
      Q *
          (∫ z : T4,
            primitiveInsertedMajorant primitiveConstant lam eps
              supportConstant n z ∂paperMeasure) <=
        (primitiveConstant * lam) ^ (2 * n) * K := by
    intro n hn
    have hI := hInsertedIntegral primitiveConstant lam eps
      supportConstant n heps heps1 hsupport hlog
    have hpow :
        0 <= (primitiveConstant * lam) ^ (2 * n) := by
      positivity
    have hlogPos : 0 < abs (Real.log eps) :=
      zero_lt_one.trans_le hlog
    have hmassDiv : insertedMass / abs (Real.log eps) <= insertedMass := by
      exact div_le_self hInsertedMass.le hlog
    calc
      Q * (∫ z : T4,
          primitiveInsertedMajorant primitiveConstant lam eps
            supportConstant n z ∂paperMeasure) <=
          Q * ((primitiveConstant * lam) ^ (2 * n) *
            (insertedMass / abs (Real.log eps))) :=
        mul_le_mul_of_nonneg_left (by simpa only [insertedMass] using hI) hQ
      _ <= Q * ((primitiveConstant * lam) ^ (2 * n) * insertedMass) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmassDiv hpow) hQ
      _ = (primitiveConstant * lam) ^ (2 * n) *
          (Q * insertedMass) := by ring
      _ <= (primitiveConstant * lam) ^ (2 * n) * K :=
        mul_le_mul_of_nonneg_left hQInsertedK hpow
  let headBudget :
      R324WithinHalfInsertedExceptionalHeadBudget
        rho primitiveConstant lam eps K kappa alpha :=
    r324WithinHalfInsertedExceptionalHeadBudget_of_prop41
      heps supportConstant primitiveConstant hprimitive.le hlam.le
      (fun res head tail hremaining H hH =>
        propProvider res head tail hremaining H hH)
      (by
        intro n hn
        simpa only [Q, mul_assoc] using hcharge n hn) alpha
  have hremoved :
      (⟨0, by omega⟩ : Fin (2 * q)) ∉ finalActive kappa := by
    rw [finalActive_eq_empty_of_full hkappa]
    simp
  obtain ⟨pack⟩ :=
    R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_of_initial_certificate
      (rho := rho) (C := primitiveConstant) (lam := lam)
      (eps := eps) (K := K) (A := A) (pairing := kappa)
      (by omega : 0 < 2 * q) hremoved heps heps1
      hprimitive.le hlam.le hK.le hA localProvider budgetProvider
      (hinitial (2 * q))
  obtain ⟨transport, terminalBudgetScale,
      terminalReachable, _terminalCertificate, htransport⟩ :=
    pack.exists_budgetSynchronizedAlternatingTransport_afterHead
      heps heps1 hprimitive.le hlam.le hK.le hA
      localProvider budgetProvider alpha headBudget
  have hG : forall j, MemEClassT4 (pack.data.stopContext.internalEdges j) := by
    intro j
    exact pack.data.trace.stopCertificate.memE
      (pack.data.stopContext.internalSlot j)
  have hint :
      forall (gap first : T4)
        (kappaB :
          {kappaB : PartialPairing
              (Fin (2 * residualBlockOrder pack.data.terminal.2)) //
            kappaB ∈ primitiveFullPairings
              (residualBlockOrder pack.data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder pack.data.terminal.2 - 2) -> T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder pack.data.terminal.2)
              kappaB.1 pack.data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder pack.data.terminal.2)
                pack.data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure) := by
    intro gap first kappaB
    exact
      R324WithinHalfEdgeCertificate.integrable_stepClosedIntegrand_section
        (ctx := pack.data.stopContext) pack.data.trace.stopCertificate
        heps heps1 kappaB first (first + gap)
  have hexact :=
    pack.data.lamEps_pow_sum_deterministicFullHalfIntegral_eq_fullHalfZeroShift
      transport hkappa hq heps heps1 hG hint alpha beta hshift
  let p : Nat := residualBlockOrder pack.data.terminal.2
  let stopCtx : R324WithinHalfStepContext kappa :=
    pack.data.trace.stopPrefix.headContext
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
  let internalScale : Real :=
    r324WithinHalfInternalEdgeScaleProduct
      stopCtx pack.data.stopScale
  let budgetInternalScale : Real :=
    r324WithinHalfInternalEdgeScaleProduct
      stopCtx pack.stopBudgetScale
  have hp : 1 <= p := pack.data.stopContext.one_le_blockOrder
  have hout :
      pack.stopBudgetScale stopCtx.outgoingSlot = A :=
    pack.budgetReachable.outgoingScale_eq_base
      pack.data.trace.stopPrefix rfl pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
  have hafterEq : pack.afterHeadBudgetScale 0 =
      A * (budgetInternalScale * A) *
        (primitiveConstant * lam) ^ (2 * p) * K := by
    dsimp only [R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.afterHeadBudgetScale,
      budgetInternalScale, stopCtx, p] at hout ⊢
    rw [← pack.data.stop_predecessorSlot_eq_zero,
      pack.data.trace.stopPrefix.budgetUpdatedEdgeScale_predecessor,
      pack.data.trace.stopPrefix.headBlockScaleProduct_eq_internal_mul_outgoing]
    rw [pack.data.stop_predecessorSlot_eq_zero,
      pack.stopBudget_zero_eq_base, hout]
  have hinternal : 0 <= internalScale := by
    dsimp only [internalScale, stopCtx]
    exact pack.data.trace.stopCertificate.internalEdgeScaleProduct_pos.le
  have hbudgetInternal : 0 <= budgetInternalScale := by
    dsimp only [budgetInternalScale, stopCtx]
    exact pack.budgetCertificate.internalEdgeScaleProduct_pos.le
  have hinternalLe : internalScale <= budgetInternalScale := by
    dsimp only [internalScale, budgetInternalScale,
      r324WithinHalfInternalEdgeScaleProduct]
    apply Finset.prod_le_prod
    · intro j _hj
      exact pack.data.trace.stopCertificate.scale_pos
        (stopCtx.internalSlot j) |>.le
    · intro j _hj
      exact pack.stopScale_le (stopCtx.internalSlot j)
  have hbudgetCoreNonneg : 0 <=
      budgetInternalScale * (primitiveConstant * lam) ^ (2 * p) := by
    positivity
  have hAA : 1 <= A * A := by
    calc
      1 <= A := hA
      _ = A * 1 := by ring
      _ <= A * A :=
        mul_le_mul_of_nonneg_left hA (zero_le_one.trans hA)
  have hAAK : 1 <= (A * A) * K :=
    hAA.trans (le_mul_of_one_le_right (zero_le_one.trans hAA) hKone)
  have hcoreAfter :
      internalScale * (primitiveConstant * lam) ^ (2 * p) <=
        pack.afterHeadBudgetScale 0 := by
    calc
      internalScale * (primitiveConstant * lam) ^ (2 * p) <=
          budgetInternalScale * (primitiveConstant * lam) ^ (2 * p) :=
        mul_le_mul_of_nonneg_right hinternalLe (by positivity)
      _ = (budgetInternalScale *
          (primitiveConstant * lam) ^ (2 * p)) * 1 := by
        ring
      _ <= (budgetInternalScale * (primitiveConstant * lam) ^ (2 * p)) *
          ((A * A) * K) :=
        mul_le_mul_of_nonneg_left hAAK hbudgetCoreNonneg
      _ = A * (budgetInternalScale * A) *
          (primitiveConstant * lam) ^ (2 * p) * K := by ring
      _ = pack.afterHeadBudgetScale 0 := hafterEq.symm
  have hbudgetCore :
      ‖transport.multiplier alpha‖ *
          (internalScale * (primitiveConstant * lam) ^ (2 * p)) <=
        terminalBudgetScale 0 := by
    exact (mul_le_mul_of_nonneg_left hcoreAfter (norm_nonneg _)).trans htransport
  have hdefect :=
    norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
      pack.data.stopContext pack.data.stopScale
      pack.data.trace.stopCertificate heps hprimitive.le hlam.le
      (fun H hH =>
        propProvider pack.data.trace.stopPrefix pack.data.terminal
          pack.data.suffix pack.data.trace.stopPrefix_remaining_eq H hH)
      alpha
  have hIordinary :=
    hOrdinaryIntegral primitiveConstant lam eps supportConstant p
      heps hsupport hlog
  have hlogPos : 0 < abs (Real.log eps) :=
    zero_lt_one.trans_le hlog
  have hendpointFactor : 0 <=
      2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) / abs (Real.log eps) := by
    positivity
  have hdefectBound :
      ‖incomingExceptionalPrimitiveDefect rho lam eps p hp
          pack.data.stopContext.internalEdges alpha‖ <=
        (internalScale * (primitiveConstant * lam) ^ (2 * p)) *
          (2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) /
            abs (Real.log eps)) := by
    calc
      _ <= 2 * internalScale *
          (∫ u : T4,
            primitiveKernelMajorant primitiveConstant lam eps
              supportConstant p u ∂paperMeasure) := by
        simpa only [p, internalScale, stopCtx,
          R324IncomingExceptionalStopTraceAssembly.stopContext,
          R324WithinHalfResidualPrefix.headContext] using hdefect
      _ <= 2 * internalScale *
          ((primitiveConstant * lam) ^ (2 * p) *
            (ordinaryMass * eps⁻¹ ^ (2 : Nat) /
              abs (Real.log eps))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [ordinaryMass] using hIordinary)
          (mul_nonneg (by norm_num) hinternal)
      _ = (internalScale * (primitiveConstant * lam) ^ (2 * p)) *
          (2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) /
            abs (Real.log eps)) := by ring
  have hmultDefect :
      ‖transport.multiplier alpha‖ *
          ‖incomingExceptionalPrimitiveDefect rho lam eps p hp
            pack.data.stopContext.internalEdges alpha‖ <=
        terminalBudgetScale 0 *
          (2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) /
            abs (Real.log eps)) := by
    calc
      _ <= ‖transport.multiplier alpha‖ *
          ((internalScale * (primitiveConstant * lam) ^ (2 * p)) *
            (2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) /
              abs (Real.log eps))) :=
        mul_le_mul_of_nonneg_left hdefectBound (norm_nonneg _)
      _ = (‖transport.multiplier alpha‖ *
          (internalScale * (primitiveConstant * lam) ^ (2 * p))) *
            (2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) /
              abs (Real.log eps)) := by ring
      _ <= terminalBudgetScale 0 *
          (2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) /
            abs (Real.log eps)) :=
        mul_le_mul_of_nonneg_right hbudgetCore hendpointFactor
  have hterminalEq :=
    terminalBudgetScale_zero_eq_closedForm_of_full
      transport terminalBudgetScale terminalReachable hkappa
  have hell : transport.final.state.processed.length <= q := by
    rw [transport.final_processed_eq_schedule]
    exact (r322AnalyticSchedule_length_le_orderSum kappa).trans_eq
      (R324FullPairingBudgetTerminalAdapter.initial_remainingOrder_eq
        (ρ := rho) (lam := lam) (ε := eps) hkappa)
  have hscalar :=
    R324FullPairingBudgetTerminalAdapter.terminalBudgetMultiplier_le_finalEvenPower_reusable
      hq hell hA hK hD
  have hterminalD : terminalBudgetScale 0 * D <=
      (primitiveConstant * multiplier * lam) ^ (2 * q) := by
    rw [hterminalEq]
    calc
      (A ^ (2 * q + 1) * (primitiveConstant * lam) ^ (2 * q) *
          K ^ transport.final.state.processed.length) * D =
        (primitiveConstant * lam) ^ (2 * q) *
          (A ^ (2 * q + 1) *
            K ^ transport.final.state.processed.length * D) := by ring
      _ <= (primitiveConstant * lam) ^ (2 * q) *
          multiplier ^ (2 * q) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ = (primitiveConstant * multiplier * lam) ^ (2 * q) := by
        rw [← mul_pow]
        congr 1
        ring
  have hnormEq :
      ‖(lamEps lam eps : Complex) ^ (2 * q) *
          (Finset.univ.sum fun tau : ReductionEndpointFiberAt kappa =>
            deterministicFullHalfIntegral
              rho eps (2 * q) alpha beta tau.1)‖ =
        paperFourthOrderModeDecay alpha * r324PaperTorusMass *
          (‖transport.multiplier alpha‖ *
            ‖incomingExceptionalPrimitiveDefect rho lam eps p hp
              pack.data.stopContext.internalEdges alpha‖) := by
    rw [hexact]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg r324PaperTorusMass_pos.le,
      abs_of_nonneg (paperSecondOrderModeDecay_nonneg alpha), norm_pow]
    rw [paperSecondOrderModeDecay_sq]
    ring
  rw [hnormEq]
  have hdecay : 0 <= paperFourthOrderModeDecay alpha :=
    paperFourthOrderModeDecay_nonneg alpha
  calc
    paperFourthOrderModeDecay alpha * r324PaperTorusMass *
          (‖transport.multiplier alpha‖ *
            ‖incomingExceptionalPrimitiveDefect rho lam eps p hp
              pack.data.stopContext.internalEdges alpha‖) <=
        paperFourthOrderModeDecay alpha * r324PaperTorusMass *
          (terminalBudgetScale 0 *
            (2 * ordinaryMass * eps⁻¹ ^ (2 : Nat) /
              abs (Real.log eps))) :=
      mul_le_mul_of_nonneg_left hmultDefect
        (mul_nonneg hdecay r324PaperTorusMass_pos.le)
    _ = paperFourthOrderModeDecay alpha *
          ((terminalBudgetScale 0 * D) *
            (eps⁻¹ ^ (2 : Nat) / abs (Real.log eps))) := by
      dsimp only [D]
      ring
    _ <= paperFourthOrderModeDecay alpha *
          ((primitiveConstant * multiplier * lam) ^ (2 * q) *
            (eps⁻¹ ^ (2 : Nat) / abs (Real.log eps))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hterminalD (by positivity)) hdecay
    _ = paperFourthOrderModeDecay alpha *
          (eps⁻¹ ^ (2 : Nat) *
            ((Cdet * lam) ^ (2 * q) / abs (Real.log eps))) := by
      dsimp only [Cdet]
      ring

end R324WithinHalfResidualPrefix

/-! ## Two complete halves and the actual refined physical fibre -/

/-- **Paper Step 4(A), full/full zero-shift producer.**  The two complete
half estimates are joined by the existing exact finite-fibre product.  The
support-radius loss in the final inserted-majorant lower bound is absorbed
once into the order-independent primitive constant. -/
theorem exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound
    (rho : SmoothCutoff) {supportConstant : Real}
    (hsupport : 0 < supportConstant) :
    exists primitiveConstant : Real, 0 < primitiveConstant /\
      R324PaperFullEndpointZeroShiftWeightedMajorantBound
        rho primitiveConstant supportConstant := by
  obtain ⟨Cdet, hCdet, hhalf⟩ :=
    R324WithinHalfResidualPrefix.exists_fullPairing_half_endpointZeroShift_bound
      rho
  let supportLoss : Real :=
    supportConstant ^ 2 / min supportConstant 1 ^ 4
  have hsupportLossOne : 1 <= supportLoss := by
    dsimp only [supportLoss]
    rcases le_total supportConstant 1 with hs | hs
    · rw [min_eq_left hs, one_le_div (pow_pos hsupport 4)]
      have hs2 : supportConstant ^ 2 <= 1 := by
        nlinarith [sq_nonneg supportConstant,
          mul_self_le_mul_self (le_of_lt hsupport) hs]
      calc
        supportConstant ^ 4 =
            supportConstant ^ 2 * supportConstant ^ 2 := by ring
        _ <= supportConstant ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hs2 (sq_nonneg supportConstant)
        _ = supportConstant ^ 2 := by ring
    · rw [min_eq_right hs, one_pow, div_one]
      exact one_le_pow₀ hs
  have hsupportLoss : 0 < supportLoss :=
    one_pos.trans_le hsupportLossOne
  let primitiveConstant : Real := Cdet * supportLoss
  have hprimitive : 0 < primitiveConstant := by
    dsimp only [primitiveConstant]
    exact mul_pos hCdet hsupportLoss
  refine ⟨primitiveConstant, hprimitive, ?_⟩
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hshift p hfibre
  have hepsilonOne : epsilon <= 1 :=
    hepsilonSmall.trans (by norm_num)
  let e0 : MomentContraction m :=
    r324RefinedContractionRepresentative m p.1.1 p.2.1
  have he0 :
      e0 ∈ momentRefinedContractionFiber m p.1.1 p.2.1 := by
    exact r324RefinedContractionRepresentative_mem p.2.2
  have hfull : e0.1.IsFull /\ e0.2.1.IsFull := hfibre e0 he0
  obtain ⟨q, hmq⟩ := hfull.1.exists_fin_order_eq_two_mul
  subst m
  have hq : 1 <= q := by omega
  have hqtrunc : q <= truncOrder epsilon := by omega
  let leftHalf : Complex :=
    Finset.univ.sum fun kp : ReductionEndpointFiberAt e0.1 =>
      deterministicFullHalfIntegral
        rho epsilon (2 * q) alpha beta kp.1
  let rightHalf : Complex :=
    Finset.univ.sum fun km : ReductionEndpointFiberAt e0.2.1 =>
      deterministicFullHalfIntegral
        rho epsilon (2 * q) (-alpha) (-beta) km.1
  have hrightShift : (-alpha) + (-beta) = 0 := by
    rw [← neg_add, hshift, neg_zero]
  have hleft :
      ‖(lamEps 1 epsilon : Complex) ^ (2 * q) * leftHalf‖ <=
        paperFourthOrderModeDecay alpha *
          (epsilon⁻¹ ^ (2 : Nat) *
            (Cdet ^ (2 * q) / abs (Real.log epsilon))) := by
    simpa only [leftHalf, mul_one] using
      hhalf 1 epsilon q e0.1 (by norm_num) hepsilon hepsilonOne
        hlog hqtrunc hq hfull.1 alpha beta hshift
  have hright :
      ‖(lamEps 1 epsilon : Complex) ^ (2 * q) * rightHalf‖ <=
        paperFourthOrderModeDecay (-alpha) *
          (epsilon⁻¹ ^ (2 : Nat) *
            (Cdet ^ (2 * q) / abs (Real.log epsilon))) := by
    simpa only [rightHalf, mul_one] using
      hhalf 1 epsilon q e0.2.1 (by norm_num) hepsilon hepsilonOne
        hlog hqtrunc hq hfull.2 (-alpha) (-beta) hrightShift
  have hbeta : beta = -alpha := eq_neg_of_add_eq_zero_right hshift
  have hdecayNeg :
      paperFourthOrderModeDecay (-alpha) =
        paperFourthOrderModeDecay beta := by
    rw [hbeta]
  let B : Real :=
    epsilon⁻¹ ^ (2 : Nat) *
      (Cdet ^ (2 * q) / abs (Real.log epsilon))
  have hB : 0 <= B := by
    dsimp only [B]
    positivity
  have hleftRhs :
      0 <= paperFourthOrderModeDecay alpha * B :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg alpha) hB
  have hproduct :
      ‖(lamEps 1 epsilon : Complex) ^ (2 * q) * leftHalf‖ *
          ‖(lamEps 1 epsilon : Complex) ^ (2 * q) * rightHalf‖ <=
        (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) * B ^ 2 := by
    calc
      _ <= (paperFourthOrderModeDecay alpha * B) *
          (paperFourthOrderModeDecay (-alpha) * B) :=
        mul_le_mul hleft hright (norm_nonneg _) hleftRhs
      _ = (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) * B ^ 2 := by
        rw [hdecayNeg]
        ring
  have hlogPos : 0 < abs (Real.log epsilon) :=
    one_pos.trans_le hlog
  have hsquareToSingle :
      (Cdet ^ (2 * q) / abs (Real.log epsilon)) ^ 2 <=
        Cdet ^ (2 * (2 * q)) / abs (Real.log epsilon) := by
    have hpow :
        (Cdet ^ (2 * q)) ^ 2 = Cdet ^ (2 * (2 * q)) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [div_pow, hpow]
    have hlogSq :
        abs (Real.log epsilon) <= abs (Real.log epsilon) ^ 2 := by
      nlinarith [hlog]
    exact div_le_div_of_nonneg_left
      (pow_nonneg hCdet.le (2 * (2 * q))) hlogPos hlogSq
  have hepsilonInv : 1 <= epsilon⁻¹ :=
    (one_le_inv₀ hepsilon).2 hepsilonOne
  have hepsilonPower :
      (epsilon⁻¹ ^ (2 : Nat)) ^ 2 <= epsilon⁻¹ ^ (8 : Nat) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hepsilonInv (by omega)
  have hBsquare : B ^ 2 <=
      epsilon⁻¹ ^ (8 : Nat) *
        (Cdet ^ (2 * (2 * q)) / abs (Real.log epsilon)) := by
    dsimp only [B]
    rw [mul_pow]
    exact mul_le_mul hepsilonPower hsquareToSingle
      (sq_nonneg _) (by positivity)
  have hLossPow :
      supportLoss <= supportLoss ^ (2 * (2 * q)) := by
    calc
      supportLoss = supportLoss ^ (1 : Nat) := (pow_one _).symm
      _ <= supportLoss ^ (2 * (2 * q)) :=
        pow_le_pow_right₀ hsupportLossOne (by omega)
  have hweightedLoss :
      Cdet ^ (2 * (2 * q)) * supportLoss <=
        primitiveConstant ^ (2 * (2 * q)) := by
    calc
      Cdet ^ (2 * (2 * q)) * supportLoss <=
          Cdet ^ (2 * (2 * q)) *
            supportLoss ^ (2 * (2 * q)) :=
        mul_le_mul_of_nonneg_left hLossPow
          (pow_nonneg hCdet.le _)
      _ = primitiveConstant ^ (2 * (2 * q)) := by
        dsimp only [primitiveConstant]
        rw [← mul_pow]
  have hscalarToSupport :
      Cdet ^ (2 * (2 * q)) / abs (Real.log epsilon) <=
        primitiveConstant ^ (2 * (2 * q)) *
          (min supportConstant 1 ^ 4 /
            (supportConstant ^ 2 * abs (Real.log epsilon))) := by
    have hden : 0 < supportLoss * abs (Real.log epsilon) :=
      mul_pos hsupportLoss hlogPos
    have hdiv := div_le_div_of_nonneg_right hweightedLoss hden.le
    have hsupportNe : supportConstant ≠ 0 := hsupport.ne'
    have hminPos : 0 < min supportConstant 1 :=
      lt_min hsupport one_pos
    have hminNe : min supportConstant 1 ≠ 0 := hminPos.ne'
    have hleftEq :
        (Cdet ^ (2 * (2 * q)) * supportLoss) /
            (supportLoss * abs (Real.log epsilon)) =
          Cdet ^ (2 * (2 * q)) / abs (Real.log epsilon) := by
      field_simp [hsupportLoss.ne', hlogPos.ne']
    have hrightEq :
        primitiveConstant ^ (2 * (2 * q)) /
            (supportLoss * abs (Real.log epsilon)) =
          primitiveConstant ^ (2 * (2 * q)) *
            (min supportConstant 1 ^ 4 /
              (supportConstant ^ 2 * abs (Real.log epsilon))) := by
      dsimp only [supportLoss]
      field_simp [hsupportNe, hminNe, hlogPos.ne']
    rwa [hleftEq, hrightEq] at hdiv
  have hlower :=
    le_integral_primitiveInsertedMajorant
      primitiveConstant 1 epsilon supportConstant (2 * q)
      hepsilon hepsilonOne hsupport
  have hlower' :
      primitiveConstant ^ (2 * (2 * q)) *
          (min supportConstant 1 ^ 4 /
            (supportConstant ^ 2 * abs (Real.log epsilon))) <=
        ∫ z, primitiveInsertedMajorant
          primitiveConstant 1 epsilon supportConstant (2 * q) z
          ∂paperMeasure := by
    simpa only [mul_one] using hlower
  have hweightedExact :
      abs (lamEps 1 epsilon) ^ (2 * (2 * q)) *
          ‖r324RefinedPhysicalIntegral
            rho epsilon (2 * q) alpha beta p‖ =
        ‖(lamEps 1 epsilon : Complex) ^ (2 * q) * leftHalf‖ *
          ‖(lamEps 1 epsilon : Complex) ^ (2 * q) * rightHalf‖ := by
    rw [← momentRefinedDeterministicTermSum_eq_r324RefinedPhysicalIntegral
      rho hepsilon hepsilonOne alpha beta p.1.1 p.1.2 p.2.1 p.2.2]
    simpa only [leftHalf, rightHalf] using
      norm_weighted_momentRefinedDeterministicTermSum_eq_fullFull_product
        rho hepsilon hepsilonOne 1 (2 * q) alpha beta e0 he0
        hfull.1 hfull.2
  rw [hweightedExact]
  have hdecays :
      0 <= paperFourthOrderModeDecay alpha *
        paperFourthOrderModeDecay beta :=
    mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)
  calc
    _ <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) * B ^ 2 := hproduct
    _ <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (epsilon⁻¹ ^ (8 : Nat) *
          (Cdet ^ (2 * (2 * q)) / abs (Real.log epsilon))) :=
      mul_le_mul_of_nonneg_left hBsquare hdecays
    _ <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (epsilon⁻¹ ^ (8 : Nat) *
          (primitiveConstant ^ (2 * (2 * q)) *
            (min supportConstant 1 ^ 4 /
              (supportConstant ^ 2 * abs (Real.log epsilon))))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hscalarToSupport (by positivity))
        hdecays
    _ <= (paperFourthOrderModeDecay alpha *
          paperFourthOrderModeDecay beta) *
        (epsilon⁻¹ ^ (8 : Nat) *
          ∫ z, primitiveInsertedMajorant
            primitiveConstant 1 epsilon supportConstant (2 * q) z
            ∂paperMeasure) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlower' (by positivity)) hdecays

end

end Anderson4D
