import Anderson4D.DetParametrix.Paper42_Moment.R324PaperOutgoingEndpointReuse
import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingHeadGapReindex
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointErasedPhaseAIndependence
import Anderson4D.DetParametrix.Paper42_Moment.R324DriverRootInstantiation

/-!
# Paper Step 4(A): outgoing-gap Fubini and endpoint-free outer factor

This module supplies the two exact coordinate facts needed after the retained
outgoing terminal has been split from an arbitrary endpoint stop.

* The existing primitive-head gap reindex is turned from
  `last = first + gap` into the outgoing paper orientation
  `last = first - gap`, and ordered with `first` outermost.
* Once the terminal is removed and a residual single remains, the phased
  split factor outside the terminal head is independent of the outgoing
  endpoint variable.

Only measure-preserving changes of variables and sparse-chain geometry are
used.  No norm or estimate occurs.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The paper's outgoing `(first, gap, internal)` coordinates -/

/-- On endpoint pairs, change `(first,last)` to
`(first, first - last)`.  This is the existing gap-first shear followed by
negation of the gap and a swap; it introduces no new coordinate analysis. -/
def r324EndpointFirstOutgoingGapMeasurableEquiv :
    T4 × T4 ≃ᵐ T4 × T4 :=
  r324EndpointGapFirstMeasurableEquiv |>.trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.neg T4)
      (MeasurableEquiv.refl T4)).trans
      (MeasurableEquiv.prodComm : T4 × T4 ≃ᵐ T4 × T4))

@[simp]
theorem r324EndpointFirstOutgoingGapMeasurableEquiv_apply
    (first last : T4) :
    r324EndpointFirstOutgoingGapMeasurableEquiv (first, last) =
      (first, first - last) := by
  change (first, -(last - first)) = (first, first - last)
  congr 1
  abel

@[simp]
theorem r324EndpointFirstOutgoingGapMeasurableEquiv_symm_apply
    (first gap : T4) :
    r324EndpointFirstOutgoingGapMeasurableEquiv.symm (first, gap) =
      (first, first - gap) := by
  change
    r324EndpointGapFirstMeasurableEquiv.symm (-gap, first) =
      (first, first - gap)
  rw [r324EndpointGapFirstMeasurableEquiv_symm_apply]
  congr 1
  abel

/-- Negation preserves the paper Haar measure on the four-torus. -/
theorem measurePreserving_r324NegT4 :
    MeasurePreserving (MeasurableEquiv.neg T4)
      paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  change
    MeasurePreserving
      (fun u : T4 => fun i => -u i)
      (volume : Measure T4) (volume : Measure T4)
  exact
    measurePreserving_pi
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun _ u => -u) fun _ =>
        Measure.measurePreserving_neg _

/-- The outgoing endpoint shear preserves the exact paper product measure. -/
theorem measurePreserving_r324EndpointFirstOutgoingGapMeasurableEquiv :
    MeasurePreserving
      r324EndpointFirstOutgoingGapMeasurableEquiv
      (paperMeasure.prod paperMeasure)
      (paperMeasure.prod paperMeasure) := by
  have hneg :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.neg T4)
          (MeasurableEquiv.refl T4))
        (paperMeasure.prod paperMeasure)
        (paperMeasure.prod paperMeasure) :=
    measurePreserving_r324NegT4.prod
      (MeasurePreserving.id paperMeasure)
  have hswap :
      MeasurePreserving
        (MeasurableEquiv.prodComm : T4 × T4 ≃ᵐ T4 × T4)
        (paperMeasure.prod paperMeasure)
        (paperMeasure.prod paperMeasure) :=
    Measure.measurePreserving_swap
  exact hswap.comp (hneg.comp
    measurePreserving_r324EndpointGapFirstMeasurableEquiv)

/-- Split a positive primitive tuple in the exact outgoing paper order
`((first,gap),internal)`, with `last = first - gap`. -/
def r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv
    (n : ℕ) (hn : 1 ≤ n) :
    (Fin (2 * n) → T4) ≃ᵐ
      (T4 × T4) × (Fin (2 * n - 2) → T4) :=
  (r324PrimitiveBlockTupleMeasurableEquiv n hn).trans
    (MeasurableEquiv.prodCongr
      r324EndpointFirstOutgoingGapMeasurableEquiv
      (MeasurableEquiv.refl (Fin (2 * n - 2) → T4)))

@[simp]
theorem r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv_symm_apply
    (n : ℕ) (hn : 1 ≤ n)
    (first gap : T4)
    (u : Fin (2 * n - 2) → T4) :
    (r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv n hn).symm
        ((first, gap), u) =
      primitiveAssemble n hn first (first - gap) u := by
  change
    (r324PrimitiveBlockTupleMeasurableEquiv n hn).symm
        (r324EndpointFirstOutgoingGapMeasurableEquiv.symm
          (first, gap), u) =
      primitiveAssemble n hn first (first - gap) u
  rw [r324EndpointFirstOutgoingGapMeasurableEquiv_symm_apply]
  exact
    r324PrimitiveBlockTupleMeasurableEquiv_symm_apply
      n hn (first, first - gap) u

/-- The full outgoing primitive-head reindex preserves product Haar measure. -/
theorem measurePreserving_r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv
    (n : ℕ) (hn : 1 ≤ n) :
    MeasurePreserving
      (r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv n hn)
      (Measure.pi fun _ : Fin (2 * n) => paperMeasure)
      ((paperMeasure.prod paperMeasure).prod
        (Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure)) := by
  have htail :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          r324EndpointFirstOutgoingGapMeasurableEquiv
          (MeasurableEquiv.refl (Fin (2 * n - 2) → T4)))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure))
        ((paperMeasure.prod paperMeasure).prod
          (Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure)) :=
    measurePreserving_r324EndpointFirstOutgoingGapMeasurableEquiv.prod
      (MeasurePreserving.id
        (Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure))
  exact htail.comp
    (measurePreserving_r324PrimitiveBlockTupleMeasurableEquiv n hn)

/-- Exact primitive-block Fubini in outgoing paper coordinates, with `first`
outermost so the fixed-first Fourier-defect identity applies directly. -/
theorem integral_standardBlock_eq_integral_first_outgoingGap_internal
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (hn : 1 ≤ n)
    (f : (Fin (2 * n) → T4) → E)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (2 * n) => paperMeasure)) :
    (∫ t, f t ∂Measure.pi fun _ : Fin (2 * n) => paperMeasure) =
      ∫ first : T4,
        ∫ gap : T4,
          ∫ u : Fin (2 * n - 2) → T4,
            f (primitiveAssemble n hn first (first - gap) u)
            ∂Measure.pi fun _ => paperMeasure
          ∂paperMeasure
        ∂paperMeasure := by
  let e := r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv n hn
  let mu := Measure.pi fun _ : Fin (2 * n) => paperMeasure
  let muInternal :=
    Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  let nu := (paperMeasure.prod paperMeasure).prod muInternal
  have hp : MeasurePreserving e mu nu :=
    measurePreserving_r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv n hn
  have htarget : Integrable (fun q => f (e.symm q)) nu := by
    have hiff :=
      hp.symm.integrable_comp_emb e.symm.measurableEmbedding (g := f)
    change Integrable (f ∘ e.symm) nu
    exact hiff.mpr hf
  have houter :
      Integrable
        (fun p : T4 × T4 =>
          ∫ u : Fin (2 * n - 2) → T4,
            f (e.symm (p, u)) ∂muInternal)
        (paperMeasure.prod paperMeasure) :=
    htarget.integral_prod_left
  calc
    (∫ t, f t ∂mu) =
        ∫ q, f (e.symm q) ∂nu := by
          symm
          simpa only [Function.comp_apply] using hp.symm.integral_comp' f
    _ =
        ∫ p : T4 × T4,
          ∫ u : Fin (2 * n - 2) → T4,
            f (e.symm (p, u)) ∂muInternal
          ∂( paperMeasure.prod paperMeasure) :=
      integral_prod _ htarget
    _ =
        ∫ first : T4,
          ∫ gap : T4,
            ∫ u : Fin (2 * n - 2) → T4,
              f (e.symm ((first, gap), u)) ∂muInternal
            ∂paperMeasure
          ∂paperMeasure :=
      integral_prod _ houter
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with first
      apply integral_congr_ae
      filter_upwards with gap
      apply integral_congr_ae
      filter_upwards with u
      rw [r324PrimitiveHeadFirstOutgoingGapMeasurableEquiv_symm_apply]

/-! ## Endpoint independence of the terminal split outer factor -/

namespace R324WithinHalfResidualPrefix
namespace R324PaperOutgoingEndpointTerminal

variable {rho : SmoothCutoff} {lam eps : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}

/-- The completed residual prefix after removing the retained outgoing
terminal. -/
abbrev terminalPost
    (data : R324PaperOutgoingEndpointTerminal res) :
    R324WithinHalfResidualPrefix rho lam eps pairing :=
  data.endpoint.stop.afterHead data.terminalData.terminal []
    data.endpoint.stop_remaining

@[simp]
theorem terminalPost_remaining
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.terminalPost.remaining = [] :=
  rfl

/-- Removing the singleton terminal completes the analytic schedule. -/
theorem terminalPost_processed_eq_schedule
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.terminalPost.state.processed = r322AnalyticSchedule pairing := by
  have hschedule := data.terminalPost.schedule_eq
  rw [data.terminalPost_remaining, List.append_nil] at hschedule
  exact hschedule.symm

/-- The completed post-terminal carrier is the paper's final residual
carrier. -/
theorem terminalPost_active_eq_finalActive
    (data : R324PaperOutgoingEndpointTerminal res) :
    data.terminalPost.state.active = finalActive pairing :=
  data.terminalPost.active_eq_finalActive_of_processed_eq_schedule
    data.terminalPost_processed_eq_schedule

/-- A surviving single gives the nonempty terminal interior carrier used to
separate both endpoint legs. -/
theorem terminalPost_active_nonempty_of_singles
    (data : R324PaperOutgoingEndpointTerminal res)
    (hsingles : pairing.singles.Nonempty) :
    data.terminalPost.state.active.Nonempty := by
  obtain ⟨i, hi⟩ := hsingles
  refine ⟨i, ?_⟩
  rw [data.terminalPost_active_eq_finalActive]
  exact singles_subset_finalActive pairing hi

/-- Every vertex surviving the outgoing terminal lies strictly to the left
of that terminal.  Its right endpoint is the final internal vertex, so there
is no second exterior region. -/
theorem terminalPost_active_lt_terminal_left
    (data : R324PaperOutgoingEndpointTerminal res)
    {i : Fin m} (hi : i ∈ data.terminalPost.state.active) :
    i < data.terminalData.terminal.1.1 := by
  change
    i ∈ (data.endpoint.stop.afterHead data.terminalData.terminal []
      data.endpoint.stop_remaining).state.active at hi
  rw [data.endpoint.stop.afterHead_active
    data.terminalData.terminal [] data.endpoint.stop_remaining] at hi
  have hiStop := (Finset.mem_sdiff.mp hi).1
  have hiNotBlock := (Finset.mem_sdiff.mp hi).2
  by_contra hnot
  have hleft : data.terminalData.terminal.1.1 ≤ i :=
    le_of_not_gt hnot
  have hright : i ≤ data.terminalData.terminal.1.2 := by
    change i.val ≤ data.terminalData.terminal.1.2.val
    have hiLt := i.isLt
    have hterminal := data.terminal_right_eq_last
    omega
  apply hiNotBlock
  rw [data.terminal_block_eq_stop_active_inter_Icc]
  exact Finset.mem_inter.mpr
    ⟨hiStop, Finset.mem_Icc.mpr ⟨hleft, hright⟩⟩

/-- In the residual terminal branch, the old head predecessor is exactly the
outgoing boundary slot of the completed post-terminal carrier. -/
theorem predecessorSlot_eq_terminalPost_outgoing
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty) :
    r324WithinHalfPredecessorSlot data.endpoint.stop.state
        data.terminalData.terminal =
      data.terminalPost.terminalOutgoingEdgeSlot hactive := by
  let predecessor :=
    r324WithinHalfPredecessorSlot data.endpoint.stop.state
      data.terminalData.terminal
  have hp :=
    r324WithinHalfPredecessorSlot_mem data.endpoint.stop.state
      data.terminalData.terminal
  rw [r324WithinHalfPredecessorCandidates] at hp
  rcases Finset.mem_union.mp hp with hzero | hinter
  · have heq : predecessor = 0 := by
      simpa only [predecessor, Finset.mem_singleton] using hzero
    exact (hpred heq).elim
  · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hinter
    have hiStop := (Finset.mem_filter.mp hi).1
    have hiLeft := (Finset.mem_filter.mp hi).2
    have hiNotBlock : i ∉ data.terminalData.terminal.2 := by
      intro hiBlock
      have hiGeometry :
          i ∈ data.endpoint.stop.state.active ∩
            Finset.Icc data.terminalData.terminal.1.1
              data.terminalData.terminal.1.2 := by
        rw [← data.terminal_block_eq_stop_active_inter_Icc]
        exact hiBlock
      exact
        (not_le_of_gt hiLeft)
          (Finset.mem_Icc.mp (Finset.mem_inter.mp hiGeometry).2).1
    have hiPost : i ∈ data.terminalPost.state.active := by
      unfold terminalPost
      rw [data.endpoint.stop.afterHead_active
        data.terminalData.terminal [] data.endpoint.stop_remaining]
      exact Finset.mem_sdiff.mpr ⟨hiStop, hiNotBlock⟩
    have hiGreatest :
        ∀ j ∈ data.terminalPost.state.active, j ≤ i := by
      intro j hj
      have hjLeft := data.terminalPost_active_lt_terminal_left hj
      change
        j ∈ (data.endpoint.stop.afterHead data.terminalData.terminal []
          data.endpoint.stop_remaining).state.active at hj
      rw [data.endpoint.stop.afterHead_active
        data.terminalData.terminal [] data.endpoint.stop_remaining] at hj
      have hjCandidate :
          r324InternalVertexEdgeSlot j ∈
            r324WithinHalfPredecessorCandidates
              data.endpoint.stop.state data.terminalData.terminal := by
        rw [r324WithinHalfPredecessorCandidates]
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨j, Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp hj).1, hjLeft⟩, rfl⟩
      have hjLe :=
        Finset.le_max'
          (r324WithinHalfPredecessorCandidates
            data.endpoint.stop.state data.terminalData.terminal)
          (r324InternalVertexEdgeSlot j) hjCandidate
      have heqVal := congrArg Fin.val heq
      unfold r324InternalVertexEdgeSlot at hjLe heqVal
      change j.val ≤ i.val
      change j.val + 1 ≤ predecessor.val at hjLe
      change i.val + 1 = predecessor.val at heqVal
      omega
    have hmaxEq :
        data.terminalPost.state.active.max' hactive = i := by
      apply le_antisymm
      · exact hiGreatest _
          (Finset.max'_mem data.terminalPost.state.active hactive)
      · exact Finset.le_max' data.terminalPost.state.active i hiPost
    unfold R324WithinHalfResidualPrefix.terminalOutgoingEdgeSlot
    rw [hmaxEq]
    exact heq.symm

/-- At a nonempty completed post-terminal carrier, the incoming phase anchor
does not see the outgoing external variable. -/
theorem terminalPost_incomingPhaseAnchor_eq_of_outgoing_endpoint
    (data : R324PaperOutgoingEndpointTerminal res)
    (hactive : data.terminalPost.state.active.Nonempty)
    (x y y' : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4) :
    data.terminalPost.incomingPhaseAnchor x y v =
      data.terminalPost.incomingPhaseAnchor x y' v := by
  rw [data.terminalPost.incomingPhaseAnchor_eq_terminalIncomingAnchor
      hactive,
    data.terminalPost.incomingPhaseAnchor_eq_terminalIncomingAnchor
      hactive]

/-- Every ordinary factor outside the retained terminal head is independent
of the outgoing endpoint.  The only post-terminal active edge that can reach
that endpoint is the old predecessor, and it belongs to `headChainSlots`, so
the erased outer product excludes it. -/
theorem incomingErasedHeadOuterFactor_eq_of_outgoing_endpoint
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (x y y' : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4) :
    data.endpoint.stop.incomingErasedHeadOuterFactor
        data.terminalData.terminal [] data.endpoint.stop_remaining
        rho eps x y v =
      data.endpoint.stop.incomingErasedHeadOuterFactor
        data.terminalData.terminal [] data.endpoint.stop_remaining
        rho eps x y' v := by
  have hout := data.predecessorSlot_eq_terminalPost_outgoing hpred hactive
  unfold R324WithinHalfResidualPrefix.incomingErasedHeadOuterFactor
  rw [data.terminalPost.residualDifferenceProduct_of_remaining_nil
      data.terminalPost_remaining x y,
    data.terminalPost.residualDifferenceProduct_of_remaining_nil
      data.terminalPost_remaining x y',
    data.terminalPost.residualPrimitiveProduct_of_remaining_nil
      data.terminalPost_remaining rho eps]
  simp only [mul_one]
  unfold R324WithinHalfResidualPrefix.incomingErasedHeadOuterChainProductAfter
  apply Finset.prod_congr rfl
  intro edge hedge
  by_cases hedgeActive : edge ∈ data.terminalPost.activeEdgeSlots
  · have hedgeZero : edge ≠ 0 := (Finset.mem_erase.mp hedge).1
    have hedgeNotHead :
        edge ∉ data.endpoint.stop.headChainSlots
          data.terminalData.terminal [] data.endpoint.stop_remaining :=
      (Finset.mem_sdiff.mp (Finset.mem_erase.mp hedge).2).2
    have hedgePred :
        edge ≠ r324WithinHalfPredecessorSlot
          data.endpoint.stop.state data.terminalData.terminal := by
      intro heq
      apply hedgeNotHead
      unfold R324WithinHalfResidualPrefix.headChainSlots
      rw [heq]
      simp
    have hedgeOutgoing :
        edge ≠ data.terminalPost.terminalOutgoingEdgeSlot hactive := by
      rw [← hout]
      exact hedgePred
    have hedgeErased :
        edge ∈ data.terminalPost.endpointErasedActiveEdgeSlots hactive := by
      unfold R324WithinHalfResidualPrefix.endpointErasedActiveEdgeSlots
      exact Finset.mem_erase.mpr
        ⟨hedgeOutgoing, Finset.mem_erase.mpr
          ⟨hedgeZero, hedgeActive⟩⟩
    exact
      (data.terminalPost
        |>.residualChainEdgeFactor_eq_zeroEndpoints_of_mem_endpointErased
          hactive x y (data.terminalPost.reconstruct v) hedgeErased).trans
        (data.terminalPost
          |>.residualChainEdgeFactor_eq_zeroEndpoints_of_mem_endpointErased
            hactive x y' (data.terminalPost.reconstruct v)
              hedgeErased).symm
  · unfold R324WithinHalfResidualPrefix.residualChainEdgeFactor
    rw [if_neg hedgeActive, if_neg hedgeActive]

/-- The complete coefficient/phase/exterior factor held fixed during the
outgoing terminal's primitive and endpoint integrations. -/
def terminalSplitOuter
    (data : R324PaperOutgoingEndpointTerminal res)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4) : ℂ :=
  coefficient v *
    charT4 incomingMode (data.terminalPost.incomingPhaseAnchor x 0 v) *
    (data.endpoint.stop.incomingErasedHeadOuterFactor
      data.terminalData.terminal [] data.endpoint.stop_remaining
      rho eps x 0 v : ℂ)

/-- Exact pointwise terminal split with the outgoing-independent outer factor
made literal. -/
theorem incomingPhasedResidualDensity_terminal_split_eq_rawLocal_mul_outer
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode : Z4) (x y : T4)
    (t : Fin (2 * residualBlockOrder data.terminalData.terminal.2) → T4)
    (v : data.terminalPost.SurvivingCoordinate → T4) :
    data.endpoint.stop.incomingPhasedResidualDensity
        (coefficient v) incomingMode rho eps x y
        ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
          data.terminalData.terminal [] data.endpoint.stop_remaining).symm
          (t, v)) =
      (data.terminalContext.rawLocalIntegrand rho eps
        (data.terminalPredecessorPoint x v - y)
        (fun j => t j - y) : ℂ) *
        data.terminalSplitOuter coefficient incomingMode x v := by
  rw [data.incomingPhasedResidualDensity_terminal_split_of_ne_zero
    hpred (coefficient v) incomingMode x y t v]
  rw [data.terminalPost_incomingPhaseAnchor_eq_of_outgoing_endpoint
      hactive x y 0 v,
    data.incomingErasedHeadOuterFactor_eq_of_outgoing_endpoint
      hpred hactive x y 0 v]
  unfold terminalSplitOuter
  ring

/-- **Complete exact outgoing-terminal section.**

For fixed post-terminal coordinates, the whole standard primitive tuple and
the outgoing Fourier variable are integrated in the paper order.  The
terminal split outer factor is held fixed only after its endpoint
independence has been proved above.  The conclusion exposes exactly the
ordinary primitive phase defect; no absolute value has been taken. -/
theorem lamEps_pow_integral_standardBlock_outgoingFourier_eq_defect
    (data : R324PaperOutgoingEndpointTerminal res)
    (hpred :
      r324WithinHalfPredecessorSlot data.endpoint.stop.state
          data.terminalData.terminal ≠ 0)
    (hactive : data.terminalPost.state.active.Nonempty)
    (coefficient :
      (data.terminalPost.SurvivingCoordinate → T4) → ℂ)
    (incomingMode outgoingMode : Z4) (x : T4)
    (v : data.terminalPost.SurvivingCoordinate → T4)
    (hhead :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder
              data.terminalData.terminal.2) → T4 =>
          ∫ y : T4,
            charT4 outgoingMode y *
              data.endpoint.stop.incomingPhasedResidualDensity
                (coefficient v) incomingMode rho eps x y
                ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                  data.terminalData.terminal []
                  data.endpoint.stop_remaining).symm (t, v))
            ∂paperMeasure)
        (Measure.pi fun _ => paperMeasure))
    (hint :
      ∀ (gap first : T4)
        (κB :
          {κB : PartialPairing
              (Fin (2 * residualBlockOrder
                data.terminalData.terminal.2)) //
            κB ∈ primitiveFullPairings
              (residualBlockOrder data.terminalData.terminal.2)}),
        Integrable
          (fun r : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith rho eps
              (2 * residualBlockOrder data.terminalData.terminal.2)
              κB.1 data.terminalContext.internalEdges
              (primitiveAssemble
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                first (first - gap) r))
          (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam eps : ℂ) ^
          (2 * residualBlockOrder data.terminalData.terminal.2) *
        (∫ t : Fin (2 * residualBlockOrder
              data.terminalData.terminal.2) → T4,
          ∫ y : T4,
            charT4 outgoingMode y *
              data.endpoint.stop.incomingPhasedResidualDensity
                (coefficient v) incomingMode rho eps x y
                ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                  data.terminalData.terminal []
                  data.endpoint.stop_remaining).symm (t, v))
            ∂paperMeasure
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ first : T4,
        ((data.terminalContext.state.edges
              (r324WithinHalfPredecessorSlot
                data.terminalContext.state data.terminalContext.step)
              (data.terminalPredecessorPoint x v - first) : ℝ) : ℂ) *
          (paperSecondOrderModeDecay outgoingMode : ℂ) *
          charT4 outgoingMode first *
          (∫ gap : T4,
            (primitiveKernelDiff rho lam eps
                (residualBlockOrder data.terminalData.terminal.2)
                data.terminalContext.one_le_blockOrder
                data.terminalContext.internalEdges gap : ℂ) *
              (charT4 (-outgoingMode) gap - 1)
            ∂paperMeasure) *
          data.terminalSplitOuter coefficient incomingMode x v
        ∂paperMeasure := by
  have hreindex :=
    integral_standardBlock_eq_integral_first_outgoingGap_internal
      (residualBlockOrder data.terminalData.terminal.2)
      data.terminalContext.one_le_blockOrder
      (fun t : Fin (2 * residualBlockOrder
            data.terminalData.terminal.2) → T4 =>
        ∫ y : T4,
          charT4 outgoingMode y *
            data.endpoint.stop.incomingPhasedResidualDensity
              (coefficient v) incomingMode rho eps x y
              ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                data.terminalData.terminal []
                data.endpoint.stop_remaining).symm (t, v))
          ∂paperMeasure)
      hhead
  rw [hreindex]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with first
  rw [← integral_const_mul]
  calc
    (∫ gap : T4,
        (lamEps lam eps : ℂ) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) *
          (∫ r : Fin (2 * residualBlockOrder
                data.terminalData.terminal.2 - 2) → T4,
            ∫ y : T4,
              charT4 outgoingMode y *
                data.endpoint.stop.incomingPhasedResidualDensity
                  (coefficient v) incomingMode rho eps x y
                  ((data.endpoint.stop.splitSurvivingPiMeasurableEquiv
                    data.terminalData.terminal []
                    data.endpoint.stop_remaining).symm
                    (primitiveAssemble
                      (residualBlockOrder
                        data.terminalData.terminal.2)
                      data.terminalContext.one_le_blockOrder
                      first (first - gap) r, v))
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure) =
      ∫ gap : T4,
        (lamEps lam eps : ℂ) ^
            (2 * residualBlockOrder data.terminalData.terminal.2) *
          (∫ r : Fin (2 * residualBlockOrder
                data.terminalData.terminal.2 - 2) → T4,
            ∫ y : T4,
              charT4 outgoingMode y *
                ((data.terminalContext.rawLocalIntegrand rho eps
                  (data.terminalPredecessorPoint x v - y)
                  (fun j =>
                    primitiveAssemble
                      (residualBlockOrder data.terminalData.terminal.2)
                      data.terminalContext.one_le_blockOrder
                      first (first - gap) r j - y) : ℂ) *
                  data.terminalSplitOuter coefficient incomingMode x v)
              ∂paperMeasure
            ∂Measure.pi fun _ => paperMeasure)
        ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with gap
          apply congrArg
          apply integral_congr_ae
          filter_upwards with r
          apply integral_congr_ae
          filter_upwards with y
          rw [data.incomingPhasedResidualDensity_terminal_split_eq_rawLocal_mul_outer
            hpred hactive coefficient incomingMode x y]
    _ = _ :=
      data.integral_lamEps_pow_terminalOutgoingFourier_gap_eq_defect
        outgoingMode (data.terminalPredecessorPoint x v) first
        (data.terminalSplitOuter coefficient incomingMode x v)
        (hint · first)

end R324PaperOutgoingEndpointTerminal
end R324WithinHalfResidualPrefix

end

end Anderson4D
