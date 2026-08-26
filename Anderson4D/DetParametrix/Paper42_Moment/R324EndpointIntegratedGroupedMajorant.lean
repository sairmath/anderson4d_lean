import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointIntegratedUniformBoundary
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperChainBound

/-!
# Grouped majorant after the four endpoint integrations

The four external Fourier variables have already been integrated in
`endpointIntegratedResidualDensity`.  This file bounds the two resulting
boundary coefficients by their stored terminal edge scales and bounds only
the two signed endpoint-erased Green chains.  The complete residual
primitive-pairing sum remains grouped throughout.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

private theorem ae_pi_eval_ne_eval_fintype
    {ι : Type*} [Fintype ι]
    (i j : ι) (hij : i ≠ j) :
    ∀ᵐ v : ι → T4 ∂(Measure.pi fun _ => paperMeasure),
      v i ≠ v j := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hcard : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨i⟩
  have heij : e i ≠ e j := by
    intro h
    exact hij (e.injective h)
  have hfin :=
    ae_pi_eval_ne_eval_of_pos hcard (e i) (e j) heij
  have hp :=
    measurePreserving_piCongrLeft
      (fun _ : Fin (Fintype.card ι) => paperMeasure) e
  have hpull := hp.quasiMeasurePreserving.tendsto_ae hfin
  filter_upwards [hpull] with v hv
  change
    (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card ι) => T4) e v) (e i) ≠
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (Fintype.card ι) => T4) e v) (e j) at hv
  simpa only [MeasurableEquiv.piCongrLeft_apply_apply] using hv

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

private theorem exists_sourceSurvivingCoordinate_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {edge : Fin (m + 1)}
    (hedge : edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    ∃ i : res.SurvivingCoordinate,
      edge.castSucc = varIdx i.1 := by
  have hedgeActive :=
    res.mem_activeEdgeSlots_of_mem_endpointErased hactive hedge
  have hedgeZero :=
    res.ne_zero_of_mem_endpointErased hactive hedge
  rw [activeEdgeSlots] at hedgeActive
  rcases Finset.mem_union.mp hedgeActive with hincoming | hinternal
  · have hedgeEq : edge = 0 := by
      simpa only [Finset.mem_singleton] using hincoming
    exact (hedgeZero hedgeEq).elim
  · obtain ⟨i, hiActive, hiEdge⟩ :=
      Finset.mem_image.mp hinternal
    refine ⟨⟨i, hiActive⟩, ?_⟩
    rw [← hiEdge]
    rfl

private theorem exists_targetSurvivingCoordinate_of_mem_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {edge : Fin (m + 1)}
    (hedge : edge ∈ res.endpointErasedActiveEdgeSlots hactive) :
    ∃ i : res.SurvivingCoordinate,
      res.edgeSuccessor edge = varIdx i.1 := by
  obtain ⟨i, hi⟩ :=
    res.exists_targetInternalIndex_of_mem_endpointErased hactive hedge
  have hmem := res.edgeSuccessor_mem_candidates edge
  rw [edgeSuccessorCandidates] at hmem
  rcases Finset.mem_union.mp hmem with hlast | hinternal
  · have hlastEq :
        res.edgeSuccessor edge = Fin.last (m + 1) := by
      simpa only [Finset.mem_singleton] using hlast
    have himpossible : varIdx i = Fin.last (m + 1) :=
      hi.symm.trans hlastEq
    have hval := congrArg Fin.val himpossible
    simp only [varIdx_val, Fin.val_last] at hval
    have hiLt := i.isLt
    omega
  · obtain ⟨j, hj, hjEq⟩ := Finset.mem_image.mp hinternal
    have hjActive := (Finset.mem_filter.mp hj).1
    have hji : j = i := by
      apply Fin.ext
      have hval := congrArg Fin.val (hjEq.trans hi)
      simp only [varIdx_val] at hval
      omega
    refine ⟨⟨i, ?_⟩, hi⟩
    simpa only [hji] using hjActive

/-- Every endpoint-erased terminal edge is off-diagonal almost everywhere
on the surviving-coordinate product. -/
theorem ae_endpointErased_edgeDisplacement_ne_zero
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    ∀ᵐ v : res.SurvivingCoordinate → T4
        ∂(Measure.pi fun _ => paperMeasure),
      ∀ edge ∈ res.endpointErasedActiveEdgeSlots hactive,
        res.edgeDisplacement 0 0 (res.reconstruct v) edge ≠ 0 := by
  apply Filter.eventually_all.2
  intro edge
  by_cases hedge : edge ∈ res.endpointErasedActiveEdgeSlots hactive
  · obtain ⟨source, hsource⟩ :=
      res.exists_sourceSurvivingCoordinate_of_mem_endpointErased
        hactive hedge
    obtain ⟨target, htarget⟩ :=
      res.exists_targetSurvivingCoordinate_of_mem_endpointErased
        hactive hedge
    have hlt := res.edge_lt_edgeSuccessor edge
    rw [hsource, htarget] at hlt
    have hsourceTarget : source ≠ target := by
      intro heq
      exact
        (ne_of_lt hlt)
          (congrArg
            (fun i : res.SurvivingCoordinate => varIdx i.1) heq)
    filter_upwards
        [ae_pi_eval_ne_eval_fintype source target hsourceTarget] with v hv
    intro _hedge
    unfold edgeDisplacement
    rw [hsource, htarget, assemble_varIdx, assemble_varIdx,
      res.reconstruct_surviving v source,
      res.reconstruct_surviving v target]
    exact sub_ne_zero.mpr hv
  · exact Filter.Eventually.of_forall fun _ hmem =>
      (hedge hmem).elim

/-- The endpoint-erased inverse-square path on one terminal half. -/
def endpointErasedInvSqChainProduct
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (v : res.SurvivingCoordinate → T4) : ℝ :=
  ∏ edge ∈ res.endpointErasedActiveEdgeSlots hactive,
    invSqKer (res.edgeDisplacement 0 0 (res.reconstruct v) edge)

theorem endpointErasedInvSqChainProduct_nonneg
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (v : res.SurvivingCoordinate → T4) :
    0 ≤ res.endpointErasedInvSqChainProduct hactive v := by
  unfold endpointErasedInvSqChainProduct
  exact Finset.prod_nonneg fun edge _ => invSqKer_nonneg _

end R324WithinHalfResidualPrefix

private theorem r324PrimitivePartitionBlockSum_nonneg
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (B : Finset (Fin (2 * m)))
    (v : Fin (2 * m) → T4) :
    0 ≤ r324PrimitivePartitionBlockSum ρ ε κp κm π B v := by
  unfold r324PrimitivePartitionBlockSum
  split_ifs with hB
  · exact Finset.sum_nonneg fun σ _ =>
      primitiveCovarianceProduct_nonneg ρ ε
        (residualBlockOrder B) σ.1 _
  · exact zero_le_one

/-- The complete residual primitive-pairing sum is nonnegative.  This
allows its complex norm to be removed without splitting the finite sum. -/
theorem r324ResidualPrimitiveSumProduct_nonneg
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    0 ≤ r324ResidualPrimitiveSumProduct ρ ε κp κm π v := by
  unfold r324ResidualPrimitiveSumProduct
  apply List.prod_nonneg
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨B, hB, rfl⟩ := ha
  exact r324PrimitivePartitionBlockSum_nonneg ρ ε κp κm π B v

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}

/-- The grouped positive majorant after the four external Fourier
integrations.  It contains every certified active-edge scale, four copies
of the inverse-square mass, the two endpoint-erased inverse-square paths,
and the complete residual primitive sum as one factor. -/
def endpointIntegratedGroupedMajorant
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (leftScale rightScale : Fin (m + 1) → ℝ)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (π : κp.singles ≃ κm.singles)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) : ℝ :=
  ((∏ edge ∈ terminal.left.activeEdgeSlots, leftScale edge) *
      (∏ edge ∈ terminal.right.activeEdgeSlots, rightScale edge)) *
    invSqKerMass ^ 4 *
    terminal.left.endpointErasedInvSqChainProduct hleft p.1 *
    terminal.right.endpointErasedInvSqChainProduct hright p.2 *
    r324ResidualPrimitiveSumProduct ρ ε κp κm π
      (terminal.terminalDoubledReconstruct p)

/-- Pointwise grouped bound under the literal off-diagonal hypotheses for
the two endpoint-erased paths. -/
theorem norm_endpointIntegratedResidualDensity_le_groupedMajorant_of_offDiagonal
    {leftRes : R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes : R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (p :
      (leftTrace.terminalPrefix.SurvivingCoordinate → T4) ×
        (rightTrace.terminalPrefix.SurvivingCoordinate → T4))
    (hneLeft :
      ∀ edge ∈ leftTrace.terminalPrefix.endpointErasedActiveEdgeSlots hleft,
        leftTrace.terminalPrefix.edgeDisplacement 0 0
          (leftTrace.terminalPrefix.reconstruct p.1) edge ≠ 0)
    (hneRight :
      ∀ edge ∈ rightTrace.terminalPrefix.endpointErasedActiveEdgeSlots hright,
        rightTrace.terminalPrefix.edgeDisplacement 0 0
          (rightTrace.terminalPrefix.reconstruct p.2) edge ≠ 0) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    ‖terminal.endpointIntegratedResidualDensity
        π hleft hright α β p‖ ≤
      terminal.endpointIntegratedGroupedMajorant
        leftTrace.terminalScale rightTrace.terminalScale
        hleft hright π p := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  have hleftBoundary :=
    norm_leftBoundaryModeCoefficient_le_storedTerminalScale
      leftTrace rightTrace hleft α β p.1
  have hrightBoundary :=
    norm_rightBoundaryModeCoefficient_le_storedTerminalScale
      leftTrace rightTrace hright α β p.2
  have hleftChain :=
    leftTrace.terminalPrefix.abs_endpointErasedSignedChain_le
      hleft leftTrace.terminalCertificate
      leftTrace.terminalPrefix_remaining_eq_nil
      0 0 (leftTrace.terminalPrefix.reconstruct p.1) hneLeft
  have hrightChain :=
    rightTrace.terminalPrefix.abs_endpointErasedSignedChain_le
      hright rightTrace.terminalCertificate
      rightTrace.terminalPrefix_remaining_eq_nil
      0 0 (rightTrace.terminalPrefix.reconstruct p.2) hneRight
  have hresidual :
      0 ≤ r324ResidualPrimitiveSumProduct ρ ε κp κm π
        (terminal.terminalDoubledReconstruct p) :=
    r324ResidualPrimitiveSumProduct_nonneg ρ ε κp κm π _
  have hleftPath :
      0 ≤ leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
        hleft p.1 :=
    leftTrace.terminalPrefix.endpointErasedInvSqChainProduct_nonneg
      hleft p.1
  have hrightPath :
      0 ≤ rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
        hright p.2 :=
    rightTrace.terminalPrefix.endpointErasedInvSqChainProduct_nonneg
      hright p.2
  have hleftScale :
      0 ≤ leftTrace.terminalPrefix.endpointErasedScaleProduct
        hleft leftTrace.terminalScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (leftTrace.terminalCertificate.scale_pos edge).le
  have hrightScale :
      0 ≤ rightTrace.terminalPrefix.endpointErasedScaleProduct
        hright rightTrace.terminalScale := by
    unfold R324WithinHalfResidualPrefix.endpointErasedScaleProduct
    exact Finset.prod_nonneg fun edge _ =>
      (rightTrace.terminalCertificate.scale_pos edge).le
  have hcore :
      ‖terminal.endpointErasedResidualSumTerminalCore
          π hleft hright p‖ ≤
        (leftTrace.terminalPrefix.endpointErasedScaleProduct
            hleft leftTrace.terminalScale *
          leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
            hleft p.1) *
        (rightTrace.terminalPrefix.endpointErasedScaleProduct
            hright rightTrace.terminalScale *
          rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
            hright p.2) *
        r324ResidualPrimitiveSumProduct ρ ε κp κm π
          (terminal.terminalDoubledReconstruct p) := by
    have hchains :
        |leftTrace.terminalPrefix.endpointErasedSignedChain
              hleft 0 0 (leftTrace.terminalPrefix.reconstruct p.1)| *
            |rightTrace.terminalPrefix.endpointErasedSignedChain
              hright 0 0 (rightTrace.terminalPrefix.reconstruct p.2)| ≤
          (leftTrace.terminalPrefix.endpointErasedScaleProduct
              hleft leftTrace.terminalScale *
            leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hleft p.1) *
          (rightTrace.terminalPrefix.endpointErasedScaleProduct
              hright rightTrace.terminalScale *
            rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hright p.2) := by
      calc
        _ ≤
            (leftTrace.terminalPrefix.endpointErasedScaleProduct
                hleft leftTrace.terminalScale *
              leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
                hleft p.1) *
              |rightTrace.terminalPrefix.endpointErasedSignedChain
                hright 0 0
                  (rightTrace.terminalPrefix.reconstruct p.2)| :=
          mul_le_mul_of_nonneg_right hleftChain (abs_nonneg _)
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left hrightChain
            (mul_nonneg hleftScale hleftPath)
    unfold endpointErasedResidualSumTerminalCore
      endpointErasedSignedTerminalCoreOfActive residualSumCrossFactor
    dsimp only [terminal, R324TwoHalfTerminalData.ofCertifiedTraces]
    dsimp only [terminal, R324TwoHalfTerminalData.ofCertifiedTraces] at hresidual
    have hpeta : (p.1, p.2) = p := Prod.eta p
    rw [hpeta]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hresidual]
    exact mul_le_mul_of_nonneg_right hchains hresidual
  let leftBoundaryScale : ℝ :=
    leftTrace.terminalScale 0 *
      leftTrace.terminalScale
        (leftTrace.terminalPrefix.terminalOutgoingEdgeSlot hleft) *
      invSqKerMass ^ 2
  let rightBoundaryScale : ℝ :=
    rightTrace.terminalScale 0 *
      rightTrace.terminalScale
        (rightTrace.terminalPrefix.terminalOutgoingEdgeSlot hright) *
      invSqKerMass ^ 2
  have hleftBoundaryScale : 0 ≤ leftBoundaryScale := by
    dsimp only [leftBoundaryScale]
    exact mul_nonneg
      (mul_nonneg
        (leftTrace.terminalCertificate.scale_pos 0).le
        (leftTrace.terminalCertificate.scale_pos _).le)
      (sq_nonneg _)
  have hrightBoundaryScale : 0 ≤ rightBoundaryScale := by
    dsimp only [rightBoundaryScale]
    exact mul_nonneg
      (mul_nonneg
        (rightTrace.terminalCertificate.scale_pos 0).le
        (rightTrace.terminalCertificate.scale_pos _).le)
      (sq_nonneg _)
  have hdensity :=
    terminal.norm_endpointIntegratedResidualDensity_le
      π hleft hright α β p leftBoundaryScale rightBoundaryScale
      hleftBoundary hrightBoundary
  calc
    ‖terminal.endpointIntegratedResidualDensity
        π hleft hright α β p‖ ≤
        leftBoundaryScale * rightBoundaryScale *
          ‖terminal.endpointErasedResidualSumTerminalCore
            π hleft hright p‖ := hdensity
    _ ≤ leftBoundaryScale * rightBoundaryScale *
          ((leftTrace.terminalPrefix.endpointErasedScaleProduct
              hleft leftTrace.terminalScale *
            leftTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hleft p.1) *
          (rightTrace.terminalPrefix.endpointErasedScaleProduct
              hright rightTrace.terminalScale *
            rightTrace.terminalPrefix.endpointErasedInvSqChainProduct
              hright p.2) *
          r324ResidualPrimitiveSumProduct ρ ε κp κm π
            (terminal.terminalDoubledReconstruct p)) :=
      mul_le_mul_of_nonneg_left hcore
        (mul_nonneg hleftBoundaryScale hrightBoundaryScale)
    _ = terminal.endpointIntegratedGroupedMajorant
          leftTrace.terminalScale rightTrace.terminalScale
          hleft hright π p := by
      unfold endpointIntegratedGroupedMajorant
      dsimp only [terminal, R324TwoHalfTerminalData.ofCertifiedTraces]
      rw [leftTrace.terminalPrefix.activeEdgeScaleProduct_eq_boundary_mul_endpointErased
          hleft leftTrace.terminalScale,
        rightTrace.terminalPrefix.activeEdgeScaleProduct_eq_boundary_mul_endpointErased
          hright rightTrace.terminalScale]
      dsimp only [leftBoundaryScale, rightBoundaryScale, terminal]
      ring

/-- Terminal-product version of the grouped majorant.  All diagonal
exceptions have been removed under the product Haar measure. -/
theorem ae_norm_endpointIntegratedResidualDensity_le_groupedMajorant
    {leftRes : R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes : R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    (fun p =>
      ‖terminal.endpointIntegratedResidualDensity
        π hleft hright α β p‖) ≤ᵐ[
      (Measure.pi fun _ :
          leftTrace.terminalPrefix.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          rightTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)]
      fun p =>
        terminal.endpointIntegratedGroupedMajorant
          leftTrace.terminalScale rightTrace.terminalScale
          hleft hright π p := by
  dsimp only
  have hleftOff :=
    leftTrace.terminalPrefix.ae_endpointErased_edgeDisplacement_ne_zero
      hleft
  have hrightOff :=
    rightTrace.terminalPrefix.ae_endpointErased_edgeDisplacement_ne_zero
      hright
  have hleftProd :=
    (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi fun _ :
        leftTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)).tendsto_ae
        hleftOff
  have hrightProd :=
    (Measure.quasiMeasurePreserving_snd
      (μ := Measure.pi fun _ :
        leftTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)
      (ν := Measure.pi fun _ :
        rightTrace.terminalPrefix.SurvivingCoordinate => paperMeasure)).tendsto_ae
        hrightOff
  filter_upwards [hleftProd, hrightProd] with p hp hq
  exact
    norm_endpointIntegratedResidualDensity_le_groupedMajorant_of_offDiagonal
      leftTrace rightTrace π hleft hright α β p hp hq

/-- Pullback of the grouped majorant to the literal initial nested-cross
carrier. -/
def initialNestedEndpointIntegratedGroupedMajorant
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)
    (leftScale rightScale : Fin (m + 1) → ℝ)
    (hleft : terminal.left.state.active.Nonempty)
    (hright : terminal.right.state.active.Nonempty)
    (π : κp.singles ≃ κm.singles)
    (v : terminal.NestedCoordinate π → T4) : ℝ :=
  terminal.endpointIntegratedGroupedMajorant
    leftScale rightScale hleft hright π
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v)

/-- Initial-nested-carrier form of the endpoint-integrated grouped bound.
It is the terminal-product theorem transported by the exact
measure-preserving two-half/nested reindexing. -/
theorem ae_norm_initialNestedEndpointIntegratedResidualDensity_le_groupedMajorant
    {leftRes : R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes : R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
    (fun v =>
      ‖terminal.initialNestedEndpointIntegratedResidualDensity
        π hleft hright α β v‖) ≤ᵐ[
      Measure.pi fun _ : terminal.NestedCoordinate π => paperMeasure]
      fun v =>
        terminal.initialNestedEndpointIntegratedGroupedMajorant
          leftTrace.terminalScale rightTrace.terminalScale
          hleft hright π v := by
  dsimp only
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces leftTrace rightTrace
  let e := terminal.terminalProductPiMeasurableEquivNested π
  have hprod :=
    ae_norm_endpointIntegratedResidualDensity_le_groupedMajorant
      leftTrace rightTrace π hleft hright α β
  have hp :=
    terminal.measurePreserving_terminalProductPiMeasurableEquivNested π
  have hinv := MeasurePreserving.symm e hp
  have hpull := hinv.quasiMeasurePreserving.tendsto_ae hprod
  filter_upwards [hpull] with v hv
  change
    ‖terminal.endpointIntegratedResidualDensity
        π hleft hright α β (e.symm v)‖ ≤
      terminal.endpointIntegratedGroupedMajorant
        leftTrace.terminalScale rightTrace.terminalScale
        hleft hright π (e.symm v) at hv
  simpa only [initialNestedEndpointIntegratedResidualDensity,
    initialNestedEndpointIntegratedGroupedMajorant, terminal, e] using hv

end R324TwoHalfTerminalData

end

end Anderson4D
