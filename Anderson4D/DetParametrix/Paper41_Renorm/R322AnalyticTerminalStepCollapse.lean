import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProperStepFubini
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticTerminalCarrier
import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseATerminalBlockUpdate

/-!
# The carrier-relative terminal collapse for R-322

After every proper schedule step has been integrated, the last extraction
block occupies the whole remaining carrier.  This module reads its current
heterogeneous edges in increasing carrier order and identifies the signed
terminal spatial integral with the genuine Proposition 4.1 primitive kernel.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Certified data at the terminal step of a non-splitting R-322
schedule. -/
structure R322AnalyticTerminalStepContext
    (q : ℕ) (hq : 1 ≤ q) where
  state : R322AnalyticEdgeState q hq
  pairing : PartialPairing (Fin (2 * q))
  pairing_mem : pairing ∈ nonSplitPairings q
  terminal : R322ExtractionStep (2 * q)
  schedule_eq :
    r322AnalyticSchedule pairing =
      state.processed ++ [terminal]
  terminal_endpoint :
    terminal.1 = r322WholeEndpoint q hq

namespace R322AnalyticTerminalStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticTerminalStepContext q hq)

theorem terminal_mem_schedule :
    ctx.terminal ∈ r322AnalyticSchedule ctx.pairing := by
  rw [ctx.schedule_eq]
  simp

theorem block_mem_extractionBlocks :
    ctx.terminal.2 ∈ extractionBlocks ctx.pairing := by
  apply
    (r322AnalyticSchedule_blocks_perm_extractionBlocks
      ctx.pairing).mem_iff.mp
  exact List.mem_map.mpr
    ⟨ctx.terminal, ctx.terminal_mem_schedule, rfl⟩

theorem blockFullyPaired :
    IsFullyPairedOn ctx.pairing ctx.terminal.2 :=
  extractionBlock_isFullyPairedOn_of_mem
    ctx.pairing ctx.terminal.2
    ctx.block_mem_extractionBlocks

theorem one_le_blockOrder :
    1 ≤ residualBlockOrder ctx.terminal.2 :=
  r322AnalyticSchedule_blockOrder_pos
    ctx.pairing
    (mem_nonSplitPairings.mp ctx.pairing_mem).1
    ctx.terminal ctx.terminal_mem_schedule

/-- The terminal concrete block is precisely the current active carrier. -/
theorem block_eq_active :
    ctx.terminal.2 = ctx.state.active := by
  exact
    r322AnalyticTerminal_block_eq_activeCarrier
      hq ctx.pairing ctx.state.processed ctx.terminal
        ctx.schedule_eq ctx.terminal_endpoint

/-- Increasing enumeration of the residual terminal carrier. -/
def blockOrderIso :
    Fin (2 * residualBlockOrder ctx.terminal.2) ≃o
      ctx.terminal.2 :=
  residualPrimitiveBlockOrderIso
    ctx.pairing ctx.terminal.2 ctx.blockFullyPaired

/-- The last point in the increasing terminal-block enumeration is the
global right endpoint. -/
theorem blockOrderIso_last :
    (ctx.blockOrderIso
      (primitiveLast
        (residualBlockOrder ctx.terminal.2)
        ctx.one_le_blockOrder)).1 =
      (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.terminal ctx.terminal_mem_schedule
  let rightInBlock : ctx.terminal.2 :=
    ⟨ctx.terminal.1.2, haligned.2.1⟩
  obtain ⟨j, hj⟩ :=
    ctx.blockOrderIso.surjective rightInBlock
  have hjlast :
      j ≤
        primitiveLast
          (residualBlockOrder ctx.terminal.2)
          ctx.one_le_blockOrder := by
    change j.val ≤
      2 * residualBlockOrder ctx.terminal.2 - 1
    have hjlt := j.isLt
    omega
  have hrightLe :
      ctx.terminal.1.2 ≤
        (ctx.blockOrderIso
          (primitiveLast
            (residualBlockOrder ctx.terminal.2)
            ctx.one_le_blockOrder)).1 := by
    have hmono :=
      ctx.blockOrderIso.monotone hjlast
    rw [hj] at hmono
    exact hmono
  have hlastLe :
      (ctx.blockOrderIso
        (primitiveLast
          (residualBlockOrder ctx.terminal.2)
          ctx.one_le_blockOrder)).1 ≤
        ctx.terminal.1.2 :=
    (haligned.2.2 _
      (ctx.blockOrderIso
        (primitiveLast
          (residualBlockOrder ctx.terminal.2)
          ctx.one_le_blockOrder)).2).2
  have heq :
      (ctx.blockOrderIso
        (primitiveLast
          (residualBlockOrder ctx.terminal.2)
          ctx.one_le_blockOrder)).1 =
        ctx.terminal.1.2 :=
    le_antisymm hlastLe hrightLe
  rw [heq, ctx.terminal_endpoint]
  rfl

/-- Ambient edge slot at the `j`th internal adjacency of the terminal
carrier. -/
def internalEdge
    (j : Fin (2 * residualBlockOrder ctx.terminal.2 - 1)) :
    Fin (2 * q - 1) :=
  ⟨(ctx.blockOrderIso
      ⟨j.val, by
        have hj := j.isLt
        have hn := ctx.one_le_blockOrder
        omega⟩).1.val,
    by
      let jf :
          Fin (2 * residualBlockOrder ctx.terminal.2) :=
        ⟨j.val, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩
      have hjlast :
          jf <
            primitiveLast
              (residualBlockOrder ctx.terminal.2)
              ctx.one_le_blockOrder := by
        change j.val <
          2 * residualBlockOrder ctx.terminal.2 - 1
        exact j.isLt
      have himage :=
        ctx.blockOrderIso.strictMono hjlast
      change
        (ctx.blockOrderIso jf).1 <
          (ctx.blockOrderIso
            (primitiveLast
              (residualBlockOrder ctx.terminal.2)
              ctx.one_le_blockOrder)).1 at himage
      rw [ctx.blockOrderIso_last] at himage
      exact Fin.mk_lt_mk.mp himage⟩

/-- The current heterogeneous edge family, read in the increasing order
of the terminal carrier.  Previously collapsed nonlocal kernels therefore
occupy exactly the slots at which they survived. -/
def internalEdges :
    Fin (2 * residualBlockOrder ctx.terminal.2 - 1) →
      T4 → ℝ :=
  fun j => ctx.state.edges (ctx.internalEdge j)

/-- Signed spatial integral of the remaining whole carrier. -/
def terminalSpatialIntegral
    (ρ : SmoothCutoff) (lam ε : ℝ) (z w : T4) : ℝ :=
  lamEps lam ε ^
      (2 * residualBlockOrder ctx.terminal.2) *
    ∫ u :
        Fin (2 * residualBlockOrder ctx.terminal.2 - 2) → T4,
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.terminal.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.terminal.2)},
        detJclosedIntegrandWith ρ ε
          (2 * residualBlockOrder ctx.terminal.2)
          κB.1 ctx.internalEdges
          (primitiveAssemble
            (residualBlockOrder ctx.terminal.2)
            ctx.one_le_blockOrder z w u)
      ∂Measure.pi fun _ => paperMeasure

/-- The terminal signed integral is exactly the heterogeneous primitive
kernel to which Proposition 4.1 applies. -/
theorem terminalSpatialIntegral_eq_primitiveKernel
    (ρ : SmoothCutoff) (lam ε : ℝ) (z w : T4)
    (hint :
      ∀ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.terminal.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.terminal.2)},
        Integrable
          (fun u :
              Fin (2 * residualBlockOrder
                ctx.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder ctx.terminal.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder z w u))
          (Measure.pi fun _ => paperMeasure)) :
    ctx.terminalSpatialIntegral ρ lam ε z w =
      primitiveKernel ρ lam ε
        (residualBlockOrder ctx.terminal.2)
        ctx.one_le_blockOrder ctx.internalEdges z w := by
  exact
    integral_sum_terminal_detJclosedIntegrandWith_eq_primitiveKernel
      ρ lam ε
      (residualBlockOrder ctx.terminal.2)
      ctx.one_le_blockOrder ctx.internalEdges z w hint

end R322AnalyticTerminalStepContext

end

end Anderson4D
