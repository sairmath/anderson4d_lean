import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticActiveEdgeLedger
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticTerminalStepCollapse

/-!
# The active-edge ledger at the R-322 terminal step

At the terminal step, the concrete block is the entire remaining carrier.
Consequently its canonically ordered internal chain slots are exactly the
ambient edge slots whose left vertex is still active.  This module proves
that finite-set identity and the resulting exact scale-product identity.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R322AnalyticTerminalStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticTerminalStepContext q hq)

/-- Ambient image of the terminal primitive kernel's internal edge slots. -/
def internalEdgesFinset : Finset (Fin (2 * q - 1)) :=
  Finset.univ.image ctx.internalEdge

theorem internalEdge_injective :
    Function.Injective ctx.internalEdge := by
  intro i j hij
  have hvertex :
      (ctx.blockOrderIso
          ⟨i.val, by
            have hi := i.isLt
            have hn := ctx.one_le_blockOrder
            omega⟩).1 =
        (ctx.blockOrderIso
          ⟨j.val, by
            have hj := j.isLt
            have hn := ctx.one_le_blockOrder
            omega⟩).1 := by
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simpa only [internalEdge] using hval
  have hindex :
      (⟨i.val, by
          have hi := i.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩ :
        Fin (2 * residualBlockOrder ctx.terminal.2)) =
      ⟨j.val, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩ := by
    apply ctx.blockOrderIso.injective
    exact Subtype.ext hvertex
  apply Fin.ext
  simpa using congrArg Fin.val hindex

theorem internalEdgesFinset_subset_activeEdges :
    ctx.internalEdgesFinset ⊆
      r322AnalyticActiveEdges ctx.state := by
  intro edge hedge
  obtain ⟨j, _hj, rfl⟩ :=
    Finset.mem_image.mp hedge
  rw [mem_r322AnalyticActiveEdges, ← ctx.block_eq_active]
  exact
    (ctx.blockOrderIso
      ⟨j.val, by
        have hj := j.isLt
        have hn := ctx.one_le_blockOrder
        omega⟩).2

/-- Every active ambient edge occurs at a unique internal slot of the
terminal primitive block. -/
theorem activeEdges_subset_internalEdgesFinset :
    r322AnalyticActiveEdges ctx.state ⊆
      ctx.internalEdgesFinset := by
  intro edge hedge
  have hleftBlock :
      r322AnalyticEdgeLeftVertex edge ∈ ctx.terminal.2 := by
    rw [ctx.block_eq_active]
    exact mem_r322AnalyticActiveEdges.mp hedge
  let leftInBlock : ctx.terminal.2 :=
    ⟨r322AnalyticEdgeLeftVertex edge, hleftBlock⟩
  obtain ⟨i, hi⟩ :=
    ctx.blockOrderIso.surjective leftInBlock
  have hine :
      i.val ≠
        2 * residualBlockOrder ctx.terminal.2 - 1 := by
    intro hilast
    have hieq :
        i =
          primitiveLast
            (residualBlockOrder ctx.terminal.2)
            ctx.one_le_blockOrder := by
      apply Fin.ext
      simpa only [primitiveLast] using hilast
    have hglobal :
        r322AnalyticEdgeLeftVertex edge =
          (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) := by
      have hordered :
          (ctx.blockOrderIso i).1 =
            (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) := by
        rw [hieq, ctx.blockOrderIso_last]
      rw [hi] at hordered
      simpa only [leftInBlock] using hordered
    have hedgeLt := edge.isLt
    have hval := congrArg Fin.val hglobal
    simpa only [r322AnalyticEdgeLeftVertex] using
      (show edge.val ≠ 2 * q - 1 by omega) hval
  have hiLt :
      i.val <
        2 * residualBlockOrder ctx.terminal.2 - 1 := by
    have hiBound := i.isLt
    omega
  let j :
      Fin (2 * residualBlockOrder ctx.terminal.2 - 1) :=
    ⟨i.val, hiLt⟩
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  have hordered :
      (ctx.blockOrderIso
        ⟨j.val, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩).1 =
        r322AnalyticEdgeLeftVertex edge := by
    have hindex :
        (⟨j.val, by
            have hj := j.isLt
            have hn := ctx.one_le_blockOrder
            omega⟩ :
          Fin (2 * residualBlockOrder ctx.terminal.2)) = i := by
      apply Fin.ext
      rfl
    rw [hindex, hi]
  have hval := congrArg Fin.val hordered
  simpa only [internalEdge, r322AnalyticEdgeLeftVertex] using hval

/-- The terminal internal slots are exactly the still-active ambient edge
slots. -/
theorem internalEdgesFinset_eq_activeEdges :
    ctx.internalEdgesFinset =
      r322AnalyticActiveEdges ctx.state := by
  apply Finset.Subset.antisymm
  · exact ctx.internalEdgesFinset_subset_activeEdges
  · exact ctx.activeEdges_subset_internalEdgesFinset

/-- The scale product seen by the final Proposition 4.1 kernel is exactly
the active-edge scale product carried through the proper-prefix induction. -/
theorem internalEdgeScaleProduct_eq_activeEdgeScaleProduct
    (scale : Fin (2 * q - 1) → ℝ) :
    (∏ j, scale (ctx.internalEdge j)) =
      ∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge := by
  rw [← ctx.internalEdgesFinset_eq_activeEdges]
  unfold internalEdgesFinset
  exact
    (Finset.prod_image
      ctx.internalEdge_injective.injOn).symm

/-- Proposition 4.1 at the terminal carrier, with the exact active-edge
product furnished by the proper-prefix budget ledger. -/
theorem abs_terminalSpatialIntegral_le_activeEdgeScaleProduct_mul_majorant
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (primitiveConstant supportConstant : ℝ)
    (scale : Fin (2 * q - 1) → ℝ)
    (hcert : R322AnalyticEdgeCertificate ctx.state scale)
    (hprop :
      ∀ H : Fin
          (2 * residualBlockOrder ctx.terminal.2 - 1) →
            T4 → ℝ,
        IsAdmissiblePrimitiveInput
            (residualBlockOrder ctx.terminal.2) H →
          MemEClassT4
              (primitiveKernelDiff ρ lam ε
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff ρ lam ε
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder H) ∧
              PrimitiveKernelBounds ρ lam ε
                (residualBlockOrder ctx.terminal.2)
                ctx.one_le_blockOrder H
                supportConstant primitiveConstant)
    (z : T4) (hz : z ≠ 0)
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
                ctx.one_le_blockOrder z 0 u))
          (Measure.pi fun _ => paperMeasure)) :
    |ctx.terminalSpatialIntegral ρ lam ε z 0| ≤
      (∏ edge ∈ r322AnalyticActiveEdges ctx.state, scale edge) *
        primitiveKernelMajorant primitiveConstant lam ε
          supportConstant
          (residualBlockOrder ctx.terminal.2) z := by
  rw [ctx.terminalSpatialIntegral_eq_primitiveKernel
    ρ lam ε z 0 hint]
  have hbound :=
    primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
      ρ ctx.one_le_blockOrder ctx.internalEdges
      (fun j => scale (ctx.internalEdge j))
      (fun j => hcert.scale_pos (ctx.internalEdge j))
      (fun j => hcert.memE (ctx.internalEdge j))
      (fun j => hcert.bound (ctx.internalEdge j))
      hprop z hz
  rw [ctx.internalEdgeScaleProduct_eq_activeEdgeScaleProduct scale]
    at hbound
  simpa only [primitiveKernelDiff] using hbound

end R322AnalyticTerminalStepContext

end

end Anderson4D
