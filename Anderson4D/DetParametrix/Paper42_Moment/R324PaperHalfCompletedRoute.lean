import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointParameterizedEE

/-!
# Completed one-half endpoint routes for paper Step 4(A)

The four signed endpoint calculations (`DD`, `DE`, `ED`, and `EE`) have
different dependent coordinate carriers.  Their common *numerical* output is
much smaller: a completed residual prefix, a reachable complete-budget scale
on that prefix, its edge certificate, and the charge left by the first
exceptional incoming head (when there is one).

This file records exactly that common output.  It deliberately does not put
an endpoint density, an integral identity, or an a.e. majorization into the
structure.  Those facts are proved by the four branch lemmas only after the
corresponding signed endpoint integrations have been performed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open SmoothCutoff
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {rho : SmoothCutoff} {C lam eps K A : Real}
    {m : Nat} {pairing : PartialPairing (Fin m)}

namespace R324WithinHalfStopBeforeStepTrace

/-- If the first internal vertex survives the complete pairing reduction,
every head before an arbitrary retained terminal has a nonzero predecessor.
Consequently the literal stop trace is wholly ordinary.  This is the direct
incoming half of the paper's `DD/DE` dichotomy. -/
theorem ordinaryAlong_of_first_mem_finalActive
    {terminal : R322ExtractionStep m}
    {suffix : List (R322ExtractionStep m)}
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    {scale : Fin (m + 1) -> Real}
    (trace : R324WithinHalfStopBeforeStepTrace terminal suffix res scale)
    (hm : 0 < m)
    (hfirst : (⟨0, hm⟩ : Fin m) ∈ finalActive pairing) :
    trace.OrdinaryAlong := by
  apply trace.ordinaryAlong_of_predecessorSlot_ne_zero
  intro current head tail hremaining _hsuffix _hterminalSuffix
  let first : Fin m := ⟨0, hm⟩
  have hfirstCurrent : first ∈ current.state.active := by
    apply (mem_r322AnalyticActiveCarrier_iff
      current.state.processed first).mpr
    intro step hstep hiStep
    have hstepSchedule : step ∈ r322AnalyticSchedule pairing := by
      rw [current.schedule_eq]
      exact List.mem_append_left current.remaining hstep
    have hblock : step.2 ∈ extractionBlocks pairing := by
      apply (r322AnalyticSchedule_blocks_perm_extractionBlocks
        pairing).mem_iff.mp
      exact List.mem_map.mpr ⟨step, hstepSchedule, rfl⟩
    exact (Finset.disjoint_left.mp
      (extractionBlocks_disjoint_finalActive pairing))
        ((mem_finsetUnionList_iff (extractionBlocks pairing)).mpr
          ⟨step.2, hblock, hiStep⟩) hfirst
  have hheadSchedule : head ∈ r322AnalyticSchedule pairing := by
    rw [current.schedule_eq, hremaining]
    simp
  have hheadBlock : head.2 ∈ extractionBlocks pairing := by
    apply (r322AnalyticSchedule_blocks_perm_extractionBlocks
      pairing).mem_iff.mp
    exact List.mem_map.mpr ⟨head, hheadSchedule, rfl⟩
  have hfirstNotHead : first ∉ head.2 := by
    intro hiHead
    exact (Finset.disjoint_left.mp
      (extractionBlocks_disjoint_finalActive pairing))
        ((mem_finsetUnionList_iff (extractionBlocks pairing)).mpr
          ⟨head.2, hheadBlock, hiHead⟩) hfirst
  have hheadLeftMem : head.1.1 ∈ head.2 :=
    (r322AnalyticSchedule_forall_aligned
      pairing head hheadSchedule).1
  have hheadLeftNe : head.1.1 ≠ first := by
    intro heq
    exact hfirstNotHead (heq ▸ hheadLeftMem)
  have hfirstLt : first < head.1.1 := by
    apply Fin.mk_lt_mk.mpr
    have hneVal : head.1.1.val ≠ 0 := by
      intro hz
      apply hheadLeftNe
      apply Fin.ext
      simpa only [first] using hz
    exact Nat.pos_of_ne_zero hneVal
  have hcandidate :
      r324InternalVertexEdgeSlot first ∈
        r324WithinHalfPredecessorCandidates current.state head := by
    rw [r324WithinHalfPredecessorCandidates]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨first, Finset.mem_filter.mpr ⟨hfirstCurrent, hfirstLt⟩, rfl⟩
  have hcandidateLe :=
    r324WithinHalfCandidate_le_predecessorSlot current.state head
      (r324InternalVertexEdgeSlot first) hcandidate
  intro hzero
  apply r324InternalVertexEdgeSlot_ne_zero first
  apply Fin.le_zero_iff.mp
  simpa only [hzero] using hcandidateLe

end R324WithinHalfStopBeforeStepTrace

/-- Common numerical carrier left by any of the four paper endpoint routes
on one half.  `firstCharge` is the scale-sized factor which precedes the
literal ordinary-`J` endpoint sacrifice; direct incoming routes may take it
to be their initial slot-zero budget. -/
structure R324PaperHalfCompletedRoute
    (pairing : PartialPairing (Fin m)) (incomingMode : Z4) where
  cases : R324PaperHalfEndpointCases
  final : R324WithinHalfResidualPrefix rho lam eps pairing
  final_remaining : final.remaining = []
  terminalScale : Fin (m + 1) -> Real
  terminalReachable :
    R324WithinHalfBudgetScaleReachable
      pairing rho C lam eps K A final.state terminalScale
  terminalCertificate :
    R324WithinHalfEdgeCertificate final.state terminalScale
  transportedMultiplier : Complex
  firstCharge : Real
  firstCharge_nonneg : 0 <= firstCharge
  multiplier_mul_firstCharge_le_terminal :
    ‖transportedMultiplier‖ * firstCharge <= terminalScale 0

namespace R324PaperHalfCompletedRoute

variable {incomingMode : Z4}

/-- The endpoint cost remains the literal case-by-case cost until the two
halves have been spliced. -/
def endpointSacrifice
    (route : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) : Real :=
  r324PaperHalfEndpointSacrifice eps route.cases

theorem endpointSacrifice_nonneg
    (route : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) :
    0 <= route.endpointSacrifice :=
  r324PaperHalfEndpointSacrifice_nonneg eps route.cases

/-- Flatten a genuine completed alternating suffix into the common route
carrier.  The branch lemma retains `transport` itself for its signed
identity; only its terminal numerical data are stored here. -/
def ofAlternatingTransport
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (transport : R324WithinHalfAlternatingTransport res)
    (terminalScale : Fin (m + 1) -> Real)
    (terminalReachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A transport.final.state terminalScale)
    (terminalCertificate :
      R324WithinHalfEdgeCertificate transport.final.state terminalScale)
    (cases : R324PaperHalfEndpointCases)
    (firstCharge : Real) (hfirst : 0 <= firstCharge)
    (hcharge :
      ‖transport.multiplier incomingMode‖ * firstCharge <= terminalScale 0) :
    R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode where
  cases := cases
  final := transport.final
  final_remaining := transport.final_remaining
  terminalScale := terminalScale
  terminalReachable := terminalReachable
  terminalCertificate := terminalCertificate
  transportedMultiplier := transport.multiplier incomingMode
  firstCharge := firstCharge
  firstCharge_nonneg := hfirst
  multiplier_mul_firstCharge_le_terminal := hcharge

/-- Flatten a retained-outgoing terminal after its exact Fourier/primitive
collapse.  The real witness is the caller's `outgoing` stop; unlike a
spurious identity transport, it records the actual paper route ending at
`terminalPost`. -/
def ofOutgoingTerminalPost
    {res : R324WithinHalfResidualPrefix rho lam eps pairing}
    (outgoing : R324PaperOutgoingEndpointTerminal res)
    (terminalScale : Fin (m + 1) -> Real)
    (terminalReachable :
      R324WithinHalfBudgetScaleReachable pairing rho C lam eps K A
        outgoing.terminalPost.state terminalScale)
    (terminalCertificate :
      R324WithinHalfEdgeCertificate outgoing.terminalPost.state terminalScale)
    (cases : R324PaperHalfEndpointCases)
    (transportedMultiplier : Complex)
    (firstCharge : Real) (hfirst : 0 <= firstCharge)
    (hcharge :
      ‖transportedMultiplier‖ * firstCharge <= terminalScale 0) :
    R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode where
  cases := cases
  final := outgoing.terminalPost
  final_remaining := outgoing.terminalPost_remaining
  terminalScale := terminalScale
  terminalReachable := terminalReachable
  terminalCertificate := terminalCertificate
  transportedMultiplier := transportedMultiplier
  firstCharge := firstCharge
  firstCharge_nonneg := hfirst
  multiplier_mul_firstCharge_le_terminal := hcharge

/-- Empty remaining schedule identifies the completed carrier with the
canonical final active set. -/
theorem final_active_eq_finalActive
    (route : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode) :
    route.final.state.active = finalActive pairing := by
  have hschedule := route.final.schedule_eq
  rw [route.final_remaining, List.append_nil] at hschedule
  exact route.final.active_eq_finalActive_of_processed_eq_schedule
    hschedule.symm

/-- Two completed one-half routes form the terminal carrier consumed by the
nested-cross Step 3 estimate. -/
def twoHalfTerminal
    {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    (leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode)
    (rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode) :
    R324TwoHalfTerminalData rho lam eps kappaP kappaM where
  left := leftRoute.final
  right := rightRoute.final
  left_remaining := leftRoute.final_remaining
  right_remaining := rightRoute.final_remaining
  left_processed := by
    have hschedule := leftRoute.final.schedule_eq
    rw [leftRoute.final_remaining, List.append_nil] at hschedule
    exact hschedule.symm
  right_processed := by
    have hschedule := rightRoute.final.schedule_eq
    rw [rightRoute.final_remaining, List.append_nil] at hschedule
    exact hschedule.symm

/-- Concatenate the two literal one-half case ledgers in the paper order
`LI, LO, RI, RO`. -/
def combinedCases
    {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    (leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode)
    (rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode) :
    Fin 4 -> R324EndpointReductionCase :=
  ![leftRoute.cases 0, leftRoute.cases 1,
    rightRoute.cases 0, rightRoute.cases 1]

@[simp]
theorem leftHalfEndpointCases_combinedCases
    {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    (leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode)
    (rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode) :
    r324LeftHalfEndpointCases
        (combinedCases leftRoute rightRoute) = leftRoute.cases := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem rightHalfEndpointCases_combinedCases
    {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    (leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode)
    (rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode) :
    r324RightHalfEndpointCases
        (combinedCases leftRoute rightRoute) = rightRoute.cases := by
  funext i
  fin_cases i <;> rfl

/-- Exact two-half endpoint cost.  No uniform `eps^-8` enlargement occurs
in the common route layer. -/
theorem endpointSacrifice_mul_eq_combinedProduct
    {kappaP kappaM : PartialPairing (Fin m)}
    {leftMode rightMode : Z4}
    (leftRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaP leftMode)
    (rightRoute : R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) kappaM rightMode) :
    leftRoute.endpointSacrifice * rightRoute.endpointSacrifice =
      r324EndpointPrimitiveSacrificeProduct eps
        (combinedCases leftRoute rightRoute) := by
  unfold endpointSacrifice
  rw [← r324PaperHalfEndpointSacrifice_mul_eq_product eps
    (combinedCases leftRoute rightRoute)]
  simp

end R324PaperHalfCompletedRoute

/-! ## The first exceptional incoming-head charge

The following is the reusable numerical calculation previously repeated in
the full/full endpoint proof.  The complete budget and the signed analytic
trace are synchronized on the same literal incoming stop.  Therefore the
ordinary primitive scale of that first head is paid by the after-head
slot-zero budget, and the later alternating multiplier telescopes into the
terminal slot-zero scale.
-/

namespace R324IncomingExceptionalStopTraceAssembly
namespace R324IncomingExceptionalBudgetedStopTraceAssembly

variable {initialScale : Fin (m + 1) -> Real}

/-- The exact analytic scale exposed by the first exceptional incoming
primitive head. -/
def firstExceptionalScale
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing) : Real :=
  r324WithinHalfInternalEdgeScaleProduct
      pack.data.stopContext pack.data.stopScale *
    (C * lam) ^ (2 * residualBlockOrder pack.data.terminal.2)

theorem firstExceptionalScale_nonneg
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing)
    (hC : 0 <= C) (hlam : 0 <= lam) :
    0 <= pack.firstExceptionalScale := by
  exact mul_nonneg
    pack.data.trace.stopCertificate.internalEdgeScaleProduct_pos.le
    (pow_nonneg (mul_nonneg hC hlam) _)

/-- The first exceptional head scale is already contained in the complete
after-head slot-zero budget.  This is the paper's first-exceptional charge,
before applying the ordinary-`J` estimate and its literal `eps^-2` cost. -/
theorem firstExceptionalScale_le_afterHeadBudgetScale
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 1 <= K) (hA : 1 <= A) :
    pack.firstExceptionalScale <= pack.afterHeadBudgetScale 0 := by
  let stopCtx : R324WithinHalfStepContext pairing :=
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
  have hbudgetCoreNonneg :
      0 <= budgetInternalScale * (C * lam) ^ (2 * p) := by
    exact mul_nonneg
      pack.budgetCertificate.internalEdgeScaleProduct_pos.le
      (pow_nonneg (mul_nonneg hC hlam) _)
  have hAA : 1 <= A * A := by
    calc
      1 <= A := hA
      _ = A * 1 := by ring
      _ <= A * A :=
        mul_le_mul_of_nonneg_left hA (zero_le_one.trans hA)
  have hAAK : 1 <= (A * A) * K :=
    hAA.trans (le_mul_of_one_le_right (zero_le_one.trans hAA) hK)
  change internalScale * (C * lam) ^ (2 * p) <=
    pack.afterHeadBudgetScale 0
  calc
    internalScale * (C * lam) ^ (2 * p) <=
        budgetInternalScale * (C * lam) ^ (2 * p) :=
      mul_le_mul_of_nonneg_right hinternalLe
        (pow_nonneg (mul_nonneg hC hlam) _)
    _ = (budgetInternalScale * (C * lam) ^ (2 * p)) * 1 := by ring
    _ <= (budgetInternalScale * (C * lam) ^ (2 * p)) *
        ((A * A) * K) :=
      mul_le_mul_of_nonneg_left hAAK hbudgetCoreNonneg
    _ = A * (budgetInternalScale * A) *
        (C * lam) ^ (2 * p) * K := by ring
    _ = pack.afterHeadBudgetScale 0 := hafterEq.symm

/-- End-to-end first-exceptional charge after the literal alternating suffix.
No ordinary-`J` sacrifice has yet been enlarged or made uniform. -/
theorem multiplier_mul_firstExceptionalScale_le_terminal
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing)
    (transport : R324WithinHalfAlternatingTransport
      (pack.data.trace.stopPrefix.afterHead
        pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq))
    (terminalScale : Fin (m + 1) -> Real)
    (incomingMode : Z4)
    (htransport :
      ‖transport.multiplier incomingMode‖ *
          pack.afterHeadBudgetScale 0 <= terminalScale 0)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 1 <= K) (hA : 1 <= A) :
    ‖transport.multiplier incomingMode‖ * pack.firstExceptionalScale <=
      terminalScale 0 := by
  exact
    (mul_le_mul_of_nonneg_left
      (pack.firstExceptionalScale_le_afterHeadBudgetScale
        hC hlam hK hA)
      (norm_nonneg _)).trans htransport

/-- Package a completed exceptional-incoming route once the paper's
budget-synchronized alternating suffix has been constructed. -/
def completedRouteOfIncomingExceptional
    (pack : R324IncomingExceptionalBudgetedStopTraceAssembly
      (rho := rho) (C := C) (lam := lam)
      (eps := eps) (K := K) (A := A) pairing)
    (transport : R324WithinHalfAlternatingTransport
      (pack.data.trace.stopPrefix.afterHead
        pack.data.terminal pack.data.suffix
        pack.data.trace.stopPrefix_remaining_eq))
    (terminalScale : Fin (m + 1) -> Real)
    (terminalReachable :
      R324WithinHalfBudgetScaleReachable
        pairing rho C lam eps K A transport.final.state terminalScale)
    (terminalCertificate :
      R324WithinHalfEdgeCertificate transport.final.state terminalScale)
    (incomingMode : Z4)
    (cases : R324PaperHalfEndpointCases)
    (htransport :
      ‖transport.multiplier incomingMode‖ *
          pack.afterHeadBudgetScale 0 <= terminalScale 0)
    (hC : 0 <= C) (hlam : 0 <= lam) (hK : 1 <= K) (hA : 1 <= A) :
    R324PaperHalfCompletedRoute
      (rho := rho) (C := C) (lam := lam) (eps := eps)
      (K := K) (A := A) pairing incomingMode where
  cases := cases
  final := transport.final
  final_remaining := transport.final_remaining
  terminalScale := terminalScale
  terminalReachable := terminalReachable
  terminalCertificate := terminalCertificate
  transportedMultiplier := transport.multiplier incomingMode
  firstCharge := pack.firstExceptionalScale
  firstCharge_nonneg := pack.firstExceptionalScale_nonneg hC hlam
  multiplier_mul_firstCharge_le_terminal :=
    pack.multiplier_mul_firstExceptionalScale_le_terminal
      transport terminalScale incomingMode htransport hC hlam hK hA

end R324IncomingExceptionalBudgetedStopTraceAssembly
end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
