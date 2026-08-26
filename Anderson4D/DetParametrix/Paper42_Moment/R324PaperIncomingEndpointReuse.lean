import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingExceptionalSeam
import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfEndpointStopAtTerminal
import Anderson4D.DetParametrix.Paper42_Moment.R324CertificateScaledPrimitiveDefect

/-!
# Paper Step 4(A): reuse of the paired incoming endpoint

The exceptional-incoming machinery already performs the paper-ordered
operation: all earlier signed interval removals, incoming Fourier
integration, and the complete primitive-head integration are exact before
the ordinary primitive defect is exposed.  To reuse that result with the
endpoint-stop driver, only a coordinate statement is missing: the untouched
refined outer functional factors through the driver's stop projection.

This file supplies precisely that projection adapter and composes it with
the existing exact refined-root identity.  It contains no norm estimate.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix
namespace R324WithinHalfEndpointStopAtTerminal

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {terminal : R322ExtractionStep m}
    {res : R324WithinHalfResidualPrefix ρ lam ε pairing}

/-- Reconstruction at a coordinate surviving to the endpoint stop commutes
with the endpoint-stop projection. -/
theorem reconstruct_projection
    (data : R324WithinHalfEndpointStopAtTerminal terminal res)
    (v : res.SurvivingCoordinate → T4)
    (i : data.stop.SurvivingCoordinate) :
    res.reconstruct v i.1 =
      data.stop.reconstruct (data.projection v) i.1 := by
  calc
    res.reconstruct v i.1 =
        res.reconstruct v (data.embedding i).1 := by
      exact congrArg (res.reconstruct v) (data.embedding_val i).symm
    _ = v (data.embedding i) :=
      res.reconstruct_surviving v (data.embedding i)
    _ = data.projection v i :=
      (data.projection_apply v i).symm
    _ = data.stop.reconstruct (data.projection v) i.1 :=
      (data.stop.reconstruct_surviving (data.projection v) i).symm

/-- Every final residual vertex is still present immediately before the
retained endpoint terminal. -/
theorem finalActive_subset_stop_active
    (data : R324WithinHalfEndpointStopAtTerminal terminal res) :
    finalActive pairing ⊆ data.stop.state.active := by
  intro i hiFinal
  apply
    (mem_r322AnalyticActiveCarrier_iff
      data.stop.state.processed i).mpr
  intro step hstep hiStep
  have hstepSchedule : step ∈ r322AnalyticSchedule pairing := by
    rw [← data.stop_processed_append_terminal_eq_schedule]
    exact List.mem_append_left [terminal] hstep
  have hblock : step.2 ∈ extractionBlocks pairing := by
    apply
      (r322AnalyticSchedule_blocks_perm_extractionBlocks
        pairing).mem_iff.mp
    exact List.mem_map.mpr ⟨step, hstepSchedule, rfl⟩
  have hiRemoved :
      i ∈ finsetUnionList (extractionBlocks pairing) :=
    (mem_finsetUnionList_iff (extractionBlocks pairing)).mpr
      ⟨step.2, hblock, hiStep⟩
  exact
    (Finset.disjoint_left.mp
      (extractionBlocks_disjoint_finalActive pairing))
      hiRemoved hiFinal

end R324WithinHalfEndpointStopAtTerminal

namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}
    {outgoingTerminal : R322ExtractionStep m}

/-- In the distinct paired-endpoint branch, the outgoing shortcut is the
last step of the suffix left after the incoming exceptional head.  The
existing endpoint-stop driver can therefore start directly from that
after-head residual prefix.  Its initial certificate is exactly the one
already produced while absorbing the incoming head. -/
theorem exists_incomingEndpointStopAtOutgoingTerminal_of_suffix_eq
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (provider :
      R324WithinHalfLocalBlockProvider ρ C lam ε K κp)
    (middle : List (R322ExtractionStep m))
    (hdistinct : data.terminal ≠ outgoingTerminal)
    (hsuffix : data.suffix = middle ++ [outgoingTerminal]) :
    Nonempty
      (R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq)) := by
  have _hbranch : data.terminal ∉ [outgoingTerminal] := by
    simpa using hdistinct
  let afterHead :=
    data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq
  let nextScale :=
    r324WithinHalfUpdatedEdgeScale
      data.stopContext data.stopScale C lam K
  have nextCertificate :
      R324WithinHalfEdgeCertificate afterHead.state nextScale := by
    dsimp only [afterHead, nextScale]
    exact
      (provider data.trace.stopPrefix
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq
        data.stopScale data.stopCertificate).2
  exact
    R324WithinHalfEndpointStopAtTerminal.exists_r324WithinHalfEndpointStopAtTerminal
      hε hε1 provider afterHead nextScale nextCertificate
      outgoingTerminal middle (by
        dsimp only [afterHead]
        rw [R324WithinHalfResidualPrefix.afterHead_remaining]
        exact hsuffix)

/-- The untouched refined outer functional, read on the carrier immediately
before the retained outgoing endpoint terminal. -/
def incomingExceptionalRefinedRootEndpointPostOuter
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω : R324IncomingExceptionalRootParameter ρ lam ε κm)
    (u : endpoint.stop.SurvivingCoordinate → T4) : ℂ :=
  charT4 β ω.1.1 *
    charT4 (-α) ω.1.2.1 *
    charT4 (-β) ω.1.2.2 *
    (((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).residualIntegrand
      ρ ε ω.1.2.1 ω.1.2.2
      ((R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).reconstruct ω.2) : ℂ) *
      (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          endpoint.stop
          (R324WithinHalfResidualPrefix.initial ρ lam ε κm)
          (u, ω.2)) : ℂ))

/-- The refined-root outer functional sees only final residual coordinates,
so it factors exactly through an endpoint-stop projection. -/
theorem incomingExceptionalRefinedRootPostOuter_eq_endpointProjection
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω : R324IncomingExceptionalRootParameter ρ lam ε κm)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) :
    data.incomingExceptionalRefinedRootPostOuter α β π ω v =
      data.incomingExceptionalRefinedRootEndpointPostOuter
        endpoint α β π ω (endpoint.projection v) := by
  have hsum :
      r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (r324TwoHalfRootDoubledReconstruct
            (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq)
            (R324WithinHalfResidualPrefix.initial ρ lam ε κm)
            (v, ω.2)) =
        r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (r324TwoHalfRootDoubledReconstruct
            endpoint.stop
            (R324WithinHalfResidualPrefix.initial ρ lam ε κm)
            (endpoint.projection v, ω.2)) := by
    apply r324ResidualPrimitiveSumProduct_congr_on_active
    intro j hj
    by_cases hleft : j.val < m
    · obtain ⟨i, hi, hji⟩ :=
        exists_leftMomentIndex_of_mem_momentResidualActive hj hleft
      subst j
      let iStop : endpoint.stop.SurvivingCoordinate :=
        ⟨i, endpoint.finalActive_subset_stop_active hi⟩
      unfold r324TwoHalfRootDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_leftMomentIndex]
      exact endpoint.reconstruct_projection v iStop
    · obtain ⟨i, hi, hji⟩ :=
        exists_rightMomentIndex_of_mem_momentResidualActive
          hj (by omega)
      subst j
      unfold r324TwoHalfRootDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_rightMomentIndex]
  unfold incomingExceptionalRefinedRootPostOuter
    incomingExceptionalRefinedRootEndpointPostOuter
  rw [hsum]

/-- The already-collapsed paired incoming endpoint coefficient, now read on
the endpoint-stop carrier.  The primitive defect is the existing signed
ordinary-`J` defect; it is not estimated here. -/
def incomingExceptionalRefinedRootEndpointCoefficient
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω : R324IncomingExceptionalRootParameter ρ lam ε κm)
    (u : endpoint.stop.SurvivingCoordinate → T4) : ℂ :=
  (paperSecondOrderModeDecay α : ℂ) ^ 2 *
    incomingExceptionalPrimitiveDefect ρ lam ε
      (residualBlockOrder data.terminal.2)
      data.stopContext.one_le_blockOrder
      data.stopContext.internalEdges α *
    data.incomingExceptionalRefinedRootEndpointPostOuter
      endpoint α β π ω u

/-- Quantitative form of the already-collapsed paired incoming endpoint.
The exact incoming Fourier operation has already produced the square of
the second-order multiplier; only the resulting ordinary primitive defect
is bounded here, using the certificate transported to the genuine stop.
No norm is moved through an earlier interval removal. -/
theorem norm_incomingExceptionalRefinedRootEndpointCoefficient_le_scaled
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω : R324IncomingExceptionalRootParameter ρ lam ε κm)
    (u : endpoint.stop.SurvivingCoordinate → T4)
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε) (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (hprop :
      ∀ (H :
          Fin (2 * residualBlockOrder data.terminal.2 - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput
            (residualBlockOrder data.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder data.terminal.2)
              data.stopContext.one_le_blockOrder H
              supportConstant primitiveConstant) :
    ‖data.incomingExceptionalRefinedRootEndpointCoefficient
        endpoint α β π ω u‖ ≤
      paperFourthOrderModeDecay α *
        (2 * r324WithinHalfInternalEdgeScaleProduct
            data.stopContext data.stopScale *
          ∫ z : T4,
            primitiveKernelMajorant primitiveConstant lam ε
              supportConstant (residualBlockOrder data.terminal.2) z
            ∂paperMeasure) *
        ‖data.incomingExceptionalRefinedRootEndpointPostOuter
          endpoint α β π ω u‖ := by
  have hcertificate :
      R324WithinHalfEdgeCertificate data.stopContext.state data.stopScale := by
    change
      R324WithinHalfEdgeCertificate
        data.trace.stopPrefix.state data.stopScale
    exact data.stopCertificate
  have hdefect :
      ‖incomingExceptionalPrimitiveDefect ρ lam ε
          (residualBlockOrder data.terminal.2)
          data.stopContext.one_le_blockOrder
          data.stopContext.internalEdges α‖ ≤
        2 * r324WithinHalfInternalEdgeScaleProduct
            data.stopContext data.stopScale *
          ∫ z : T4,
            primitiveKernelMajorant primitiveConstant lam ε
              supportConstant (residualBlockOrder data.terminal.2) z
            ∂paperMeasure := by
    have hraw :=
      norm_incomingExceptionalPrimitiveDefect_le_scaled_of_certificate
        data.stopContext data.stopScale hcertificate hε hprimitive hlam
        hprop α
    simpa [R324IncomingExceptionalStopTraceAssembly.stopContext,
      R324WithinHalfResidualPrefix.headContext] using hraw
  have hdecay :
      paperSecondOrderModeDecay α ^ 2 =
        paperFourthOrderModeDecay α := by
    unfold paperSecondOrderModeDecay paperFourthOrderModeDecay
    rw [inv_pow]
  unfold incomingExceptionalRefinedRootEndpointCoefficient
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (paperSecondOrderModeDecay_nonneg α),
    hdecay]
  calc
    paperFourthOrderModeDecay α *
          ‖incomingExceptionalPrimitiveDefect ρ lam ε
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges α‖ *
          ‖data.incomingExceptionalRefinedRootEndpointPostOuter
            endpoint α β π ω u‖ =
        paperFourthOrderModeDecay α *
          (‖incomingExceptionalPrimitiveDefect ρ lam ε
            (residualBlockOrder data.terminal.2)
            data.stopContext.one_le_blockOrder
            data.stopContext.internalEdges α‖ *
          ‖data.incomingExceptionalRefinedRootEndpointPostOuter
            endpoint α β π ω u‖) := by ring
    _ ≤ paperFourthOrderModeDecay α *
          ((2 * r324WithinHalfInternalEdgeScaleProduct
              data.stopContext data.stopScale *
            ∫ z : T4,
              primitiveKernelMajorant primitiveConstant lam ε
                supportConstant (residualBlockOrder data.terminal.2) z
              ∂paperMeasure) *
          ‖data.incomingExceptionalRefinedRootEndpointPostOuter
            endpoint α β π ω u‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdefect
          (norm_nonneg
            (data.incomingExceptionalRefinedRootEndpointPostOuter
              endpoint α β π ω u)))
        (paperFourthOrderModeDecay_nonneg α)
    _ = paperFourthOrderModeDecay α *
          (2 * r324WithinHalfInternalEdgeScaleProduct
              data.stopContext data.stopScale *
            ∫ z : T4,
              primitiveKernelMajorant primitiveConstant lam ε
                supportConstant (residualBlockOrder data.terminal.2) z
              ∂paperMeasure) *
          ‖data.incomingExceptionalRefinedRootEndpointPostOuter
            endpoint α β π ω u‖ := by ring

/-- The incoming exceptional coefficient factors through the endpoint-stop
projection without moving a norm across any interval removal. -/
theorem incomingExceptionalPostCoefficient_refinedRoot_eq_endpointProjection
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω : R324IncomingExceptionalRootParameter ρ lam ε κm)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) :
    data.incomingExceptionalPostCoefficient
        α (data.incomingExceptionalRefinedRootPostOuter α β π) ω v =
      data.incomingExceptionalRefinedRootEndpointCoefficient
        endpoint α β π ω (endpoint.projection v) := by
  unfold incomingExceptionalPostCoefficient
    incomingExceptionalRefinedRootEndpointCoefficient
  rw [data.incomingExceptionalRefinedRootPostOuter_eq_endpointProjection
    endpoint α β π ω v]

/-- Section form consumed directly by `endpoint.transport`. -/
theorem incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_endpoint_section_eq
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (α β : Z4)
    (π : κp.singles ≃ κm.singles)
    (ω : R324IncomingExceptionalRootParameter ρ lam ε κm) :
    (fun v :
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4 =>
      data.incomingExceptionalAfterHeadPhasedIntegrand
        α
        (fun ω' : R324IncomingExceptionalRootParameter ρ lam ε κm =>
          ω'.1.1)
        (data.incomingExceptionalRefinedRootPostOuter α β π)
        (ω, v)) =
      fun v =>
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
          (data.incomingExceptionalRefinedRootEndpointCoefficient
            endpoint α β π ω (endpoint.projection v))
          α ρ ε 0 ω.1.1 v := by
  funext v
  show
    (data.trace.stopPrefix.afterHead
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq).incomingPhasedResidualDensity
        (data.incomingExceptionalPostCoefficient
          α (data.incomingExceptionalRefinedRootPostOuter α β π) ω v)
        α ρ ε 0 ω.1.1 v = _
  rw [data.incomingExceptionalPostCoefficient_refinedRoot_eq_endpointProjection
    endpoint α β π ω v]

/-- Exact root-to-endpoint-stop identity for the paired incoming branch.
All earlier interval removals and the incoming primitive collapse are
completed before the endpoint-stop transport is invoked. -/
theorem lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingEndpointStop
    (p : R324RefinedScheduleIndex m)
    (e₀ : MomentContraction m)
    (he₀ :
      e₀ ∈ momentRefinedContractionFiber m p.1.1 p.2.1)
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) e₀.1 initialScale)
    (endpoint :
      R324WithinHalfEndpointStopAtTerminal outgoingTerminal
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq))
    (hm : 0 < m)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hG : ∀ j, MemEClassT4 (data.stopContext.internalEdges j))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder data.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminal.2)}),
        Integrable
          (fun r :
              Fin (2 * residualBlockOrder data.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder data.terminal.2)
              κB.1 data.stopContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminal.2)
                data.stopContext.one_le_blockOrder
                first (first + gap) r))
          (Measure.pi fun _ => paperMeasure))
    (α β : Z4) :
    (lamEps lam ε : ℂ) ^
          (2 *
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder) *
        r324RefinedPhysicalIntegral ρ ε m α β p =
      ∫ ω : R324IncomingExceptionalRootParameter ρ lam ε e₀.2.1,
        (lamEps lam ε : ℂ) ^ (2 * endpoint.stop.remainingOrder) *
          (∫ u : endpoint.stop.SurvivingCoordinate → T4,
            endpoint.stop.incomingPhasedResidualDensity
              (endpoint.multiplier α *
                data.incomingExceptionalRefinedRootEndpointCoefficient
                  endpoint α β e₀.2.2 ω u)
              α ρ ε 0 ω.1.1 u
            ∂Measure.pi fun _ => paperMeasure)
        ∂r324IncomingExceptionalRootParameterMeasure
          ρ lam ε e₀.2.1 := by
  have hjoint :=
    data.integrable_incomingExceptionalRefinedRootAfterHeadPhasedIntegrand
      p e₀ he₀ hm hε hε1 hG hint α β
  refine
    (data.lamEps_pow_r324RefinedPhysicalIntegral_eq_incomingExceptionalAfterHead
      p e₀ he₀ hm hε hε1 hG hint α β).trans ?_
  rw [integral_prod _ hjoint, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hjoint.prod_right_ae] with ω hω
  rw [data.incomingExceptionalAfterHeadPhasedIntegrand_refinedRoot_endpoint_section_eq
    endpoint α β e₀.2.2 ω] at hω ⊢
  exact endpoint.transport 0 ω.1.1 α
    (data.incomingExceptionalRefinedRootEndpointCoefficient
      endpoint α β e₀.2.2 ω) hω

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
