import Anderson4D.DetParametrix.Paper42_Moment.R324PaperBudgetedEndpointStop

/-!
# Structural one-half endpoint routes for paper Step 4(A)

The signed endpoint identities live in `R324PaperEndpointTwoHalfSplice` and
`R324PaperEndpointParameterizedEE`.  This file supplies their structural
inputs.  Each branch retains the genuine alternating transport or retained
outgoing stop on which its signed identity is stated, and separately flattens
only the common terminal budget into `R324PaperHalfCompletedRoute`.

No endpoint integral is estimated here.  In particular the four literal case
costs remain `DD`, `DE`, `ED`, and `EE`; uniformization is deferred until the
two completed halves have been spliced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

/-- The paper estimates needed by every structural endpoint route.  The
exceptional-head provider is indexed by the actual incoming Fourier mode;
all other data are mode-independent. -/
structure R324PaperHalfRouteProviders
    (pairing : PartialPairing (Fin m)) (incomingMode : Z4) where
  /-- The common support constant from Proposition 4.1.  Endpoint routes
  retain it because an outgoing exceptional block is estimated only after
  its signed Fourier defect has been formed. -/
  supportConstant : Real
  supportConstant_pos : 0 < supportConstant
  hm : 0 < m
  heps : 0 < eps
  heps1 : eps <= 1
  hC : 0 <= C
  hlam : 0 <= lam
  hK : 1 <= K
  hA : 1 <= A
  prop41Provider :
    R324WithinHalfProp41Provider
      rho C lam eps supportConstant pairing
  analyticProvider :
    R324WithinHalfLocalBlockProvider rho C lam eps K pairing
  budgetProvider :
    R324WithinHalfBudgetLocalBlockProvider
      rho C lam eps K A pairing
  headBudget :
    R324WithinHalfInsertedExceptionalHeadBudget
      rho C lam eps K pairing incomingMode
  /-- The same uniform inserted-kernel budget pays a retained exceptional
  outgoing block after its signed Fourier defect has been formed.  The
  factor two is the literal Green-difference constant in paper Step 4(A). -/
  outgoingInsertedBudget : forall n : Nat, 1 <= n ->
    2 *
        (∫ z : T4,
          primitiveInsertedMajorant C lam eps
            supportConstant n z ∂paperMeasure) <=
      (C * lam) ^ (2 * n) * K
  initialCertificate :
    R324WithinHalfEdgeCertificate
      (r324InitialWithinHalfEdgeState m) (fun _ => A)

namespace R324PaperHalfRouteProviders

variable {incomingMode : Z4}

theorem hK_nonneg
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) :
    0 <= K :=
  zero_le_one.trans providers.hK

theorem initialBudgetReachable
    (_providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) :
    R324WithinHalfBudgetScaleReachable pairing rho C lam eps K A
      (R324WithinHalfResidualPrefix.initial rho lam eps pairing).state
      (fun _ => A) :=
  R324WithinHalfBudgetScaleReachable.initial

end R324PaperHalfRouteProviders

variable {incomingMode : Z4}

/-! ## A reusable nonzero-predecessor fact -/

/-- A surviving final vertex to the left of a scheduled head is an explicit
nonzero predecessor candidate.  This is the small geometric fact needed to
consume a retained outgoing terminal without changing slot zero. -/
theorem predecessorSlot_ne_zero_of_finalActive_lt
    (res : R324WithinHalfResidualPrefix rho lam eps pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (_hremaining : res.remaining = head :: tail)
    (i : Fin m) (hiFinal : i ∈ finalActive pairing)
    (hiLt : i < head.1.1) :
    r324WithinHalfPredecessorSlot res.state head ≠ 0 := by
  have hiCurrent : i ∈ res.state.active := by
    apply (mem_r322AnalyticActiveCarrier_iff
      res.state.processed i).mpr
    intro step hstep hiStep
    have hstepSchedule : step ∈ r322AnalyticSchedule pairing := by
      rw [res.schedule_eq]
      exact List.mem_append_left res.remaining hstep
    have hblock : step.2 ∈ extractionBlocks pairing := by
      apply (r322AnalyticSchedule_blocks_perm_extractionBlocks
        pairing).mem_iff.mp
      exact List.mem_map.mpr ⟨step, hstepSchedule, rfl⟩
    exact (Finset.disjoint_left.mp
      (extractionBlocks_disjoint_finalActive pairing))
        ((mem_finsetUnionList_iff (extractionBlocks pairing)).mpr
          ⟨step.2, hblock, hiStep⟩) hiFinal
  have hcandidate :
      r324InternalVertexEdgeSlot i ∈
        r324WithinHalfPredecessorCandidates res.state head := by
    rw [r324WithinHalfPredecessorCandidates]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨hiCurrent, hiLt⟩, rfl⟩
  have hcandidateLe :=
    r324WithinHalfCandidate_le_predecessorSlot res.state head
      (r324InternalVertexEdgeSlot i) hcandidate
  intro hzero
  apply r324InternalVertexEdgeSlot_ne_zero i
  apply Fin.le_zero_iff.mp
  simpa only [hzero] using hcandidateLe

/-! ## Branch witness packages -/

structure R324PaperHalfDirectDirectRoute
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) where
  transport : R324WithinHalfAlternatingTransport
    (R324WithinHalfResidualPrefix.initial rho lam eps pairing)
  route : R324PaperHalfCompletedRoute
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) pairing incomingMode
  route_cases : route.cases =
    ![R324EndpointReductionCase.directFourier,
      R324EndpointReductionCase.directFourier]
  route_final : route.final = transport.final
  route_transportedMultiplier :
    route.transportedMultiplier = transport.multiplier incomingMode
  route_firstCharge : route.firstCharge = A

structure R324PaperHalfDirectExceptionalRoute
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) where
  terminalData : R324ShortcutTerminalSchedule pairing
  trace : R324WithinHalfStopBeforeStepTrace terminalData.terminal []
    (R324WithinHalfResidualPrefix.initial rho lam eps pairing) (fun _ => A)
  ordinary : trace.OrdinaryAlong
  /-- The paper's Step 4(A) outgoing-endpoint estimate is made on the
  state immediately before the retained terminal is consumed.  Keep the
  synchronized budget on that literal state; the completed route below is
  the post-terminal carrier and cannot reconstruct this information. -/
  stopBudgetScale : Fin (m + 1) -> Real
  stopReachable :
    R324WithinHalfBudgetScaleReachable
      pairing rho C lam eps K A trace.stopPrefix.state stopBudgetScale
  stopCertificate :
    R324WithinHalfEdgeCertificate trace.stopPrefix.state stopBudgetScale
  stopScale_le_budget :
    forall edge, trace.stopScale edge <= stopBudgetScale edge
  /-- The direct incoming leg is ordinary throughout the stopped prefix,
  so the synchronized complete budget keeps its initial boundary value.
  This is the exact equality returned by the producer; retaining it avoids
  reconstructing the stopped traversal in Step 4(A). -/
  stopBudgetScale_zero_eq_base : stopBudgetScale 0 = A
  endpoint : R324WithinHalfEndpointStopAtTerminal terminalData.terminal
    (R324WithinHalfResidualPrefix.initial rho lam eps pairing)
  endpoint_eq : endpoint =
    R324WithinHalfEndpointStopAtTerminal.of_ordinaryTrace trace ordinary
  outgoing : R324PaperOutgoingEndpointTerminal
    (R324WithinHalfResidualPrefix.initial rho lam eps pairing)
  outgoing_eq : outgoing =
    { terminalData := terminalData, endpoint := endpoint }
  /-- The retained terminal is genuinely fed from an internal predecessor.
  This is proved when the literal `DE` route is selected and is required by
  the signed outgoing-endpoint identity; it must not be forgotten when the
  completed post-terminal carrier is formed. -/
  predecessor_ne_zero :
    r324WithinHalfPredecessorSlot endpoint.stop.state
        terminalData.terminal ≠ 0
  /-- The direct incoming single survives the retained outgoing block, so
  the post-terminal carrier on which the endpoint defect is evaluated is
  nonempty. -/
  terminalPost_active : outgoing.terminalPost.state.active.Nonempty
  route : R324PaperHalfCompletedRoute
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) pairing incomingMode
  route_cases : route.cases =
    ![R324EndpointReductionCase.directFourier,
      R324EndpointReductionCase.insertedSacrifice]
  route_final : route.final = outgoing.terminalPost

structure R324PaperHalfExceptionalDirectRoute
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) where
  pack :
    R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing
  transport : R324WithinHalfAlternatingTransport
    (pack.data.trace.stopPrefix.afterHead
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq)
  route : R324PaperHalfCompletedRoute
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) pairing incomingMode
  route_cases : route.cases =
    ![R324EndpointReductionCase.insertedSacrifice,
      R324EndpointReductionCase.directFourier]
  route_final : route.final = transport.final
  /-- The constructor already proves this stronger, literal after-head
  budget estimate.  Retaining it pays the complete exceptional incoming
  head before the final direct Fourier operation. -/
  multiplier_mul_afterHeadBudgetScale_le_terminalScale_zero :
    ‖transport.multiplier incomingMode‖ * pack.afterHeadBudgetScale 0 <=
      route.terminalScale 0

structure R324PaperHalfExceptionalExceptionalRoute
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) where
  pack :
    R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing
  terminalData : R324ShortcutTerminalSchedule pairing
  endpoint : R324BudgetedEndpointStopAtTerminal
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) terminalData.terminal
    (pack.data.trace.stopPrefix.afterHead
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq)
    pack.afterHeadBudgetScale incomingMode
  outgoing : R324PaperOutgoingEndpointTerminal
    (pack.data.trace.stopPrefix.afterHead
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq)
  outgoing_eq : outgoing =
    { terminalData := terminalData, endpoint := endpoint.endpoint }
  route : R324PaperHalfCompletedRoute
    (rho := rho) (C := C) (lam := lam) (eps := eps)
    (K := K) (A := A) pairing incomingMode
  route_cases : route.cases =
    ![R324EndpointReductionCase.insertedSacrifice,
      R324EndpointReductionCase.insertedSacrifice]
  route_final : route.final = outgoing.terminalPost

/-! ## Direct/direct -/

/-- Genuine all-schedule transport for the `DD` branch. -/
theorem R324PaperHalfRouteProviders.exists_directDirect
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode)
    (_hfirst : (⟨0, providers.hm⟩ : Fin m) ∈ finalActive pairing)
    (_hshortcut : Fin.last m ∉ extractedRightEdges pairing) :
    Nonempty (R324PaperHalfDirectDirectRoute providers) := by
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps pairing
  obtain ⟨transport, terminalScale, terminalReachable,
      terminalCertificate, htransport⟩ :=
    exists_budgetSynchronizedAlternatingTransport
      providers.heps providers.heps1 providers.hC providers.hlam
      providers.hK_nonneg providers.hA providers.analyticProvider
      providers.budgetProvider initial (fun _ => A) (fun _ => A)
      providers.initialCertificate providers.initialBudgetReachable
      providers.initialCertificate (fun _ => le_rfl)
      incomingMode providers.headBudget
  let route := R324PaperHalfCompletedRoute.ofAlternatingTransport
    transport terminalScale terminalReachable terminalCertificate
    ![R324EndpointReductionCase.directFourier,
      R324EndpointReductionCase.directFourier]
    A (zero_le_one.trans providers.hA) htransport
  exact ⟨{
    transport := transport
    route := route
    route_cases := rfl
    route_final := rfl
    route_transportedMultiplier := rfl
    route_firstCharge := rfl }⟩

/-! ## Direct/exceptional -/

/-- A list decomposition exposing a head distinct from the final named
terminal necessarily leaves that terminal at the end of the head suffix.
This is the paper schedule fact used to start a retained-outgoing stop after
an earlier exceptional incoming head. -/
private theorem exists_suffix_append_singleton_of_append_cons_eq_append_singleton
    {alpha : Type*} {pre₁ pre₂ suffix : List alpha}
    {head terminal : alpha}
    (h : pre₁ ++ head :: suffix = pre₂ ++ [terminal])
    (hne : head ≠ terminal) :
    ∃ post : List alpha, suffix = post ++ [terminal] := by
  have hlength := congrArg List.length h
  have hlt : pre₁.length < pre₂.length := by
    by_contra hnot
    have hle : pre₂.length <= pre₁.length := Nat.le_of_not_gt hnot
    have hsuffixLength : suffix.length = 0 := by
      simp only [List.length_append, List.length_cons,
        List.length_nil] at hlength
      omega
    have hsuffix : suffix = [] := List.length_eq_zero_iff.mp hsuffixLength
    subst suffix
    have hreverse := congrArg List.reverse h
    simp only [List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append] at hreverse
    exact hne (List.cons.inj hreverse).1
  have aux : forall {left right : List alpha},
      left ++ head :: suffix = right ++ [terminal] ->
      left.length < right.length ->
      exists post : List alpha, suffix = post ++ [terminal] := by
    intro left right heq hlen
    induction left generalizing right with
    | nil =>
        cases right with
        | nil => simp at hlen
        | cons first rest =>
            simp only [List.nil_append, List.cons_append] at heq
            injection heq with _ hsuffix
            exact ⟨rest, hsuffix⟩
    | cons first rest ih =>
        cases right with
        | nil => simp at hlen
        | cons first' rest' =>
            simp only [List.cons_append] at heq
            injection heq with _ htail
            apply ih htail
            simp only [List.length_cons] at hlen
            omega
  exact aux h hlt

/-- The terminal extraction block is disjoint from every final single, so a
surviving first vertex lies strictly to its left. -/
private theorem first_lt_shortcutTerminal
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode)
    (terminalData : R324ShortcutTerminalSchedule pairing)
    (hfirst : (⟨0, providers.hm⟩ : Fin m) ∈ finalActive pairing) :
    (⟨0, providers.hm⟩ : Fin m) < terminalData.terminal.1.1 := by
  let first : Fin m := ⟨0, providers.hm⟩
  have hblock : terminalData.terminal.2 ∈ extractionBlocks pairing := by
    apply (r322AnalyticSchedule_blocks_perm_extractionBlocks
      pairing).mem_iff.mp
    exact List.mem_map.mpr
      ⟨terminalData.terminal, terminalData.terminal_mem_schedule, rfl⟩
  have hleftMem : terminalData.terminal.1.1 ∈ terminalData.terminal.2 :=
    (r322AnalyticSchedule_forall_aligned pairing terminalData.terminal
      terminalData.terminal_mem_schedule).1
  have hleftNe : terminalData.terminal.1.1 ≠ first := by
    intro heq
    have hfirstMem : first ∈ terminalData.terminal.2 := by
      rw [← heq]
      exact hleftMem
    exact (Finset.disjoint_left.mp
      (extractionBlocks_disjoint_finalActive pairing))
        ((mem_finsetUnionList_iff (extractionBlocks pairing)).mpr
          ⟨terminalData.terminal.2, hblock, hfirstMem⟩) hfirst
  apply Fin.mk_lt_mk.mpr
  have hneVal : terminalData.terminal.1.1.val ≠ 0 := by
    intro hz
    apply hleftNe
    apply Fin.ext
    simpa only [first] using hz
  exact Nat.pos_of_ne_zero hneVal

/-- Literal `DE` route: the proper prefix is wholly ordinary, then the
canonical outgoing shortcut is retained and consumed exactly once. -/
theorem R324PaperHalfRouteProviders.exists_directExceptional
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode)
    (hfirst : (⟨0, providers.hm⟩ : Fin m) ∈ finalActive pairing)
    (hshortcut : Fin.last m ∈ extractedRightEdges pairing) :
    Nonempty (R324PaperHalfDirectExceptionalRoute providers) := by
  obtain ⟨terminalData⟩ :=
    exists_r324ShortcutTerminalSchedule pairing hshortcut
  let initial := R324WithinHalfResidualPrefix.initial rho lam eps pairing
  obtain ⟨trace, stopBudgetScale, stopReachable,
      stopCertificate, hstopScale, hstopZeroIfOrdinary⟩ :=
    R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_pairedStopBefore
      providers.hC providers.hlam providers.hK_nonneg providers.hA
      providers.heps providers.heps1 providers.analyticProvider
      providers.budgetProvider terminalData.terminal [] terminalData.proper
      initial (fun _ => A) (fun _ => A) providers.initialCertificate
      providers.initialBudgetReachable providers.initialCertificate
      (fun _ => le_rfl) (by
        change r322AnalyticSchedule pairing =
          terminalData.proper ++ terminalData.terminal :: []
        simpa using terminalData.schedule_eq)
  have ordinary : trace.OrdinaryAlong :=
    trace.ordinaryAlong_of_first_mem_finalActive providers.hm hfirst
  let endpoint :=
    R324WithinHalfEndpointStopAtTerminal.of_ordinaryTrace trace ordinary
  let endpointBudget : R324BudgetedEndpointStopAtTerminal
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) terminalData.terminal initial
      (fun _ => A) incomingMode :=
    { endpoint := endpoint
      stopBudgetScale := stopBudgetScale
      stopReachable := by
        simpa only [endpoint,
          R324WithinHalfEndpointStopAtTerminal.of_ordinaryTrace] using
            stopReachable
      stopCertificate := by
        simpa only [endpoint,
          R324WithinHalfEndpointStopAtTerminal.of_ordinaryTrace] using
            stopCertificate
      multiplier_budget := by
        change ‖(1 : Complex)‖ * A <= stopBudgetScale 0
        rw [norm_one, one_mul, hstopZeroIfOrdinary ordinary] }
  have hpred :
      r324WithinHalfPredecessorSlot endpoint.stop.state
          terminalData.terminal ≠ 0 := by
    apply predecessorSlot_ne_zero_of_finalActive_lt endpoint.stop
      terminalData.terminal [] endpoint.stop_remaining
      (⟨0, providers.hm⟩ : Fin m) hfirst
    exact first_lt_shortcutTerminal providers terminalData hfirst
  obtain ⟨route, hrouteCases, hrouteFinal⟩ :=
    R324BudgetedEndpointStopAtTerminal.completedRoute_after_outgoingTerminal
      providers.budgetProvider terminalData endpointBudget hpred
      ![R324EndpointReductionCase.directFourier,
        R324EndpointReductionCase.insertedSacrifice]
      A (zero_le_one.trans providers.hA) le_rfl
  let outgoing : R324PaperOutgoingEndpointTerminal initial :=
    { terminalData := terminalData, endpoint := endpoint }
  exact ⟨{
    terminalData := terminalData
    trace := trace
    ordinary := ordinary
    stopBudgetScale := stopBudgetScale
    stopReachable := stopReachable
    stopCertificate := stopCertificate
    stopScale_le_budget := hstopScale
    stopBudgetScale_zero_eq_base := hstopZeroIfOrdinary ordinary
    endpoint := endpoint
    endpoint_eq := rfl
    outgoing := outgoing
    outgoing_eq := rfl
    predecessor_ne_zero := hpred
    terminalPost_active := by
      rw [outgoing.terminalPost_active_eq_finalActive]
      exact ⟨_, hfirst⟩
    route := route
    route_cases := hrouteCases
    route_final := by simpa only [outgoing] using hrouteFinal }⟩

/-! ## Exceptional/direct -/

/-- The incoming exceptional head is removed first and its exact signed
multiplier is transported through the remaining schedule. -/
theorem R324PaperHalfRouteProviders.exists_exceptionalDirect
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode)
    (hfirst : (⟨0, providers.hm⟩ : Fin m) ∉ finalActive pairing)
    (_hshortcut : Fin.last m ∉ extractedRightEdges pairing) :
    Nonempty (R324PaperHalfExceptionalDirectRoute providers) := by
  obtain ⟨pack⟩ :=
    R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_of_initial_certificate
      providers.hm hfirst providers.heps providers.heps1
      providers.hC providers.hlam providers.hK_nonneg providers.hA
      providers.analyticProvider providers.budgetProvider
      providers.initialCertificate
  obtain ⟨transport, terminalScale, terminalReachable,
      terminalCertificate, htransport⟩ :=
    pack.exists_budgetSynchronizedAlternatingTransport_afterHead
      providers.heps providers.heps1 providers.hC providers.hlam
      providers.hK_nonneg providers.hA providers.analyticProvider
      providers.budgetProvider incomingMode providers.headBudget
  let route := pack.completedRouteOfIncomingExceptional transport
    terminalScale terminalReachable terminalCertificate incomingMode
    ![R324EndpointReductionCase.insertedSacrifice,
      R324EndpointReductionCase.directFourier]
    htransport providers.hC providers.hlam providers.hK providers.hA
  exact ⟨{
    pack := pack
    transport := transport
    route := route
    route_cases := rfl
    route_final := rfl
    multiplier_mul_afterHeadBudgetScale_le_terminalScale_zero :=
      htransport }⟩

/-! ## Exceptional/exceptional -/

/-- Literal `EE` route.  The first exceptional incoming block is charged
before the after-head suffix is traversed.  The canonical outgoing shortcut
is kept as the last unconsumed block, so the returned `outgoing` is exactly
the dependent witness required by the parameterized signed `EE` identity. -/
theorem R324PaperHalfRouteProviders.exists_exceptionalExceptional
    (providers : R324PaperHalfRouteProviders
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode)
    (hfirst : (⟨0, providers.hm⟩ : Fin m) ∉ finalActive pairing)
    (hshortcut : Fin.last m ∈ extractedRightEdges pairing)
    (hsingles : pairing.singles.Nonempty) :
    Nonempty (R324PaperHalfExceptionalExceptionalRoute providers) := by
  obtain ⟨pack⟩ :=
    R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.exists_of_initial_certificate
      providers.hm hfirst providers.heps providers.heps1
      providers.hC providers.hlam providers.hK_nonneg providers.hA
      providers.analyticProvider providers.budgetProvider
      providers.initialCertificate
  obtain ⟨terminalData⟩ :=
    exists_r324ShortcutTerminalSchedule pairing hshortcut
  have hdistinct : pack.data.terminal ≠ terminalData.terminal :=
    pack.data.terminal_ne_outgoingTerminal_of_singles_nonempty
      terminalData providers.hm hsingles
  obtain ⟨middle, hsuffix⟩ :=
    exists_suffix_append_singleton_of_append_cons_eq_append_singleton
      (pack.data.schedule_eq.symm.trans terminalData.schedule_eq) hdistinct
  let afterHead := pack.data.trace.stopPrefix.afterHead
    pack.data.terminal pack.data.suffix
    pack.data.trace.stopPrefix_remaining_eq
  let analyticScale :=
    r324WithinHalfUpdatedEdgeScale pack.data.stopContext
      pack.data.stopScale C lam K
  obtain ⟨_analyticBound, analyticCertificate⟩ :=
    providers.analyticProvider pack.data.trace.stopPrefix
      pack.data.terminal pack.data.suffix
      pack.data.trace.stopPrefix_remaining_eq
      pack.data.stopScale pack.data.trace.stopCertificate
  have hscale : forall edge,
      analyticScale edge <= pack.afterHeadBudgetScale edge := by
    intro edge
    exact
      R324IncomingExceptionalStopTraceAssembly.R324IncomingExceptionalBudgetedStopTraceAssembly.analyticUpdate_le_budgetUpdate
        pack.data.trace.stopPrefix pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq
        pack.data.stopScale pack.stopBudgetScale
        pack.data.trace.stopCertificate pack.budgetCertificate
        pack.budgetReachable pack.stopScale_le providers.hC providers.hlam
        providers.hK_nonneg providers.hA edge
  obtain ⟨endpoint⟩ :=
    R324BudgetedEndpointStopAtTerminal.exists_of_providers
      providers.heps providers.heps1 providers.hC providers.hlam
      providers.hK_nonneg providers.hA providers.analyticProvider
      providers.budgetProvider providers.headBudget afterHead
      analyticScale pack.afterHeadBudgetScale analyticCertificate
      pack.afterHeadBudgetReachable
      (pack.afterHeadBudgetCertificate providers.budgetProvider)
      hscale terminalData.terminal middle (by
        dsimp only [afterHead]
        rw [R324WithinHalfResidualPrefix.afterHead_remaining]
        exact hsuffix)
  let outgoing : R324PaperOutgoingEndpointTerminal afterHead :=
    { terminalData := terminalData, endpoint := endpoint.endpoint }
  obtain ⟨single, hsingle⟩ := hsingles
  have hsingleFinal : single ∈ finalActive pairing :=
    singles_subset_finalActive pairing hsingle
  have hsingleLt : single < terminalData.terminal.1.1 := by
    by_contra hnot
    have hleftLe : terminalData.terminal.1.1 <= single :=
      le_of_not_gt hnot
    have hrightLe : single <= terminalData.terminal.1.2 := by
      apply Fin.mk_le_mk.mpr
      rw [terminalData.terminal_right]
      have hlt := single.isLt
      omega
    have hsingleStop : single ∈ endpoint.endpoint.stop.state.active :=
      endpoint.endpoint.finalActive_subset_stop_active hsingleFinal
    have hsingleBlock : single ∈ terminalData.terminal.2 := by
      rw [outgoing.terminal_block_eq_stop_active_inter_Icc]
      exact Finset.mem_inter.mpr
        ⟨hsingleStop, Finset.mem_Icc.mpr ⟨hleftLe, hrightLe⟩⟩
    have hblock : terminalData.terminal.2 ∈ extractionBlocks pairing := by
      apply (r322AnalyticSchedule_blocks_perm_extractionBlocks
        pairing).mem_iff.mp
      exact List.mem_map.mpr
        ⟨terminalData.terminal, terminalData.terminal_mem_schedule, rfl⟩
    exact (Finset.disjoint_left.mp
      (extractionBlocks_disjoint_finalActive pairing))
        ((mem_finsetUnionList_iff (extractionBlocks pairing)).mpr
          ⟨terminalData.terminal.2, hblock, hsingleBlock⟩) hsingleFinal
  have hpred :
      r324WithinHalfPredecessorSlot endpoint.endpoint.stop.state
          terminalData.terminal ≠ 0 :=
    predecessorSlot_ne_zero_of_finalActive_lt endpoint.endpoint.stop
      terminalData.terminal [] endpoint.endpoint.stop_remaining
      single hsingleFinal hsingleLt
  obtain ⟨route, hrouteCases, hrouteFinal⟩ :=
    R324BudgetedEndpointStopAtTerminal.completedRoute_after_outgoingTerminal
      providers.budgetProvider terminalData endpoint hpred
      ![R324EndpointReductionCase.insertedSacrifice,
        R324EndpointReductionCase.insertedSacrifice]
      pack.firstExceptionalScale
      (pack.firstExceptionalScale_nonneg providers.hC providers.hlam)
      (pack.firstExceptionalScale_le_afterHeadBudgetScale
        providers.hC providers.hlam providers.hK providers.hA)
  exact ⟨{
    pack := pack
    terminalData := terminalData
    endpoint := endpoint
    outgoing := outgoing
    outgoing_eq := rfl
    route := route
    route_cases := hrouteCases
    route_final := by simpa only [outgoing] using hrouteFinal }⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
