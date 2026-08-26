import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticResidualIntegrability
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticTerminalActiveEdges
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticQuantitativePrefix
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticBudgetProductInvariant
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticTerminalIntegrability
import Anderson4D.DetParametrix.Paper41_Renorm.R322DetIntegrability

/-!
# Exact iteration of the R-322 residual invariant

Paper: R-322 — §4.1 → (3.22): the constructive renormalization-constant bound

This module iterates the one-proper-block identity proved in
`R322AnalyticResidualPrefixInvariant` and identifies the final singleton
whole-carrier residual with the terminal heterogeneous primitive integral.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R322AnalyticTerminalStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticTerminalStepContext q hq)

/-- The first point in the increasing terminal carrier is the global left
endpoint. -/
theorem blockOrderIso_zero :
    (ctx.blockOrderIso
      ⟨0, by
        have hn := ctx.one_le_blockOrder
        omega⟩).1 =
      (⟨0, by omega⟩ : Fin (2 * q)) := by
  have haligned :=
    r322AnalyticSchedule_forall_aligned
      ctx.pairing ctx.terminal ctx.terminal_mem_schedule
  let leftInBlock : ctx.terminal.2 :=
    ⟨ctx.terminal.1.1, haligned.1⟩
  obtain ⟨j, hj⟩ :=
    ctx.blockOrderIso.surjective leftInBlock
  let zeroIndex :
      Fin (2 * residualBlockOrder ctx.terminal.2) :=
    ⟨0, by
      have hn := ctx.one_le_blockOrder
      omega⟩
  have hzeroLe : zeroIndex ≤ j := by
    change 0 ≤ j.val
    omega
  have hleftLe :
      (ctx.blockOrderIso zeroIndex).1 ≤ ctx.terminal.1.1 := by
    have hmono := ctx.blockOrderIso.monotone hzeroLe
    rw [hj] at hmono
    exact hmono
  have hleftLower :
      ctx.terminal.1.1 ≤ (ctx.blockOrderIso zeroIndex).1 :=
    (haligned.2.2 _ (ctx.blockOrderIso zeroIndex).2).1
  have heq :
      (ctx.blockOrderIso zeroIndex).1 = ctx.terminal.1.1 :=
    le_antisymm hleftLe hleftLower
  change (ctx.blockOrderIso zeroIndex).1 =
    (⟨0, by omega⟩ : Fin (2 * q))
  rw [heq, ctx.terminal_endpoint]
  rfl

/-- The sparse successor of a terminal-chain left vertex is its next vertex
in the increasing terminal block enumeration. -/
theorem successorVertex_internalEdge
    (j : Fin (2 * residualBlockOrder ctx.terminal.2 - 1)) :
    r322AnalyticSuccessorVertex ctx.state
        (r322AnalyticEdgeLeftVertex (ctx.internalEdge j))
        (by
          change (ctx.internalEdge j).val < 2 * q - 1
          exact (ctx.internalEdge j).isLt) =
      (ctx.blockOrderIso
        ⟨j.val + 1, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩).1 := by
  let leftIndex :
      Fin (2 * residualBlockOrder ctx.terminal.2) :=
    ⟨j.val, by
      have hj := j.isLt
      have hn := ctx.one_le_blockOrder
      omega⟩
  let rightIndex :
      Fin (2 * residualBlockOrder ctx.terminal.2) :=
    ⟨j.val + 1, by
      have hj := j.isLt
      have hn := ctx.one_le_blockOrder
      omega⟩
  let leftVertex : Fin (2 * q) :=
    (ctx.blockOrderIso leftIndex).1
  let rightVertex : Fin (2 * q) :=
    (ctx.blockOrderIso rightIndex).1
  have hedgeLeft :
      r322AnalyticEdgeLeftVertex (ctx.internalEdge j) =
        leftVertex := by
    apply Fin.ext
    rfl
  have hrightActive : rightVertex ∈ ctx.state.active := by
    rw [← ctx.block_eq_active]
    exact (ctx.blockOrderIso rightIndex).2
  have hleftRight : leftVertex < rightVertex := by
    exact ctx.blockOrderIso.strictMono (by
      change j.val < j.val + 1
      omega)
  have hrightCandidate :
      rightVertex ∈
        r322AnalyticSuccessorCandidates
          ctx.state
          (r322AnalyticEdgeLeftVertex
            (ctx.internalEdge j)) := by
    apply Finset.mem_filter.mpr
    rw [hedgeLeft]
    exact ⟨hrightActive, hleftRight⟩
  apply le_antisymm
  · unfold r322AnalyticSuccessorVertex
    exact Finset.min'_le _ _ hrightCandidate
  · let successor :=
      r322AnalyticSuccessorVertex ctx.state
        (r322AnalyticEdgeLeftVertex (ctx.internalEdge j))
        (by
          change (ctx.internalEdge j).val < 2 * q - 1
          exact (ctx.internalEdge j).isLt)
    have hsuccessorActive : successor ∈ ctx.state.active :=
      r322AnalyticSuccessorVertex_mem_active _ _ _
    let successorInBlock : ctx.terminal.2 :=
      ⟨successor, by
        rw [ctx.block_eq_active]
        exact hsuccessorActive⟩
    let k := ctx.blockOrderIso.symm successorInBlock
    have hkImage :
        (ctx.blockOrderIso k).1 = successor := by
      exact congrArg Subtype.val
        (ctx.blockOrderIso.apply_symm_apply successorInBlock)
    have hleftSuccessor :
        leftVertex < successor := by
      rw [← hedgeLeft]
      exact r322AnalyticSuccessorVertex_gt _ _ _
    have hleftIndexLt : leftIndex < k := by
      apply ctx.blockOrderIso.lt_iff_lt.mp
      have himage :
          (ctx.blockOrderIso leftIndex).1 <
            (ctx.blockOrderIso k).1 := by
        rw [hkImage]
        exact hleftSuccessor
      exact himage
    have hrightIndexLe : rightIndex ≤ k := by
      change j.val + 1 ≤ k.val
      change j.val < k.val at hleftIndexLt
      omega
    have himage :=
      ctx.blockOrderIso.monotone hrightIndexLe
    have himageVal :
        (ctx.blockOrderIso rightIndex).1 ≤
          (ctx.blockOrderIso k).1 :=
      himage
    change rightVertex ≤ successor
    rw [← hkImage]
    exact himageVal

end R322AnalyticTerminalStepContext

namespace R322AnalyticResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {q : ℕ} {hq : 1 ≤ q}
    (res : R322AnalyticResidualPrefix ρ lam ε q hq)
    (terminal : R322ExtractionStep (2 * q))
    (hremaining : res.remaining = [terminal])
    (hterminal :
      terminal.1 = r322WholeEndpoint q hq)

private abbrev terminalContext :
    R322AnalyticTerminalStepContext q hq :=
  res.terminalStepContext terminal hremaining hterminal

include hremaining in
theorem terminal_remainingOrder :
    res.remainingOrder =
      residualBlockOrder terminal.2 := by
  unfold remainingOrder
  rw [hremaining]
  simp

include hremaining hterminal in
theorem terminal_one_le_blockOrder :
    1 ≤ residualBlockOrder terminal.2 := by
  simpa only [terminalContext, terminalStepContext] using
    (res.terminalContext terminal hremaining hterminal)
      |>.one_le_blockOrder

include hremaining hterminal in
theorem terminal_remainingRightValues :
    res.remainingRightValues =
      [2 * q - 1] := by
  unfold remainingRightValues
  rw [hremaining]
  simp only [List.map_cons, List.map_nil]
  rw [hterminal]
  rfl

include hterminal in
theorem terminal_residualStepDifference
    (x : Fin (2 * q) → T4) :
    res.residualStepDifference x terminal = 1 := by
  unfold residualStepDifference
  rw [hterminal]
  simp only [r322WholeEndpoint]
  split_ifs with hguard
  · omega
  · rfl

include hremaining hterminal in
theorem terminal_residualDifferenceProduct
    (x : Fin (2 * q) → T4) :
    res.residualDifferenceProduct x = 1 := by
  unfold residualDifferenceProduct
  rw [hremaining]
  simp [res.terminal_residualStepDifference
    terminal hterminal x]

include hremaining in
theorem terminal_remainingBlockIndex_zero :
    (res.remainingBlockIndex
      ⟨0, by simp [hremaining]⟩).1 =
        terminal.2 := by
  rw [remainingBlockIndex_val]
  simp [hremaining]

include hremaining in
theorem terminal_residualPrimitiveProduct
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x : Fin (2 * q) → T4) :
    res.residualPrimitiveProduct ρ' ε' x =
      r322ExtractionBlockPrimitiveSum ρ' ε'
        res.pairing
        (res.remainingBlockIndex
          ⟨0, by simp [hremaining]⟩) x := by
  unfold residualPrimitiveProduct
  let j0 : Fin res.remaining.length :=
    ⟨0, by simp [hremaining]⟩
  rw [Fintype.prod_eq_single j0]
  intro j hj
  exfalso
  apply hj
  apply Fin.ext
  have hjlt := j.isLt
  simp [hremaining] at hjlt
  omega

/-- Stable terminal-block order whose source mentions the displayed
terminal step rather than the reducible context field. -/
def terminalBlockOrderIso
    (res' : R322AnalyticResidualPrefix ρ lam ε q hq)
    (terminal' : R322ExtractionStep (2 * q))
    (hremaining' : res'.remaining = [terminal'])
    (hterminal' :
      terminal'.1 = r322WholeEndpoint q hq) :
    Fin (2 * residualBlockOrder terminal'.2) ≃o terminal'.2 := by
  let ctx :=
    res'.terminalContext terminal' hremaining' hterminal'
  exact
    residualPrimitiveBlockOrderIso
      res'.pairing terminal'.2
      (extractionBlock_isFullyPairedOn_of_mem
        res'.pairing terminal'.2
        ctx.block_mem_extractionBlocks)

include hremaining hterminal in
theorem terminalBlockOrderIso_apply_eq_context
    (i : Fin (2 * residualBlockOrder terminal.2)) :
    (res.terminalBlockOrderIso
      terminal hremaining hterminal i).1 =
      ((res.terminalContext terminal hremaining hterminal)
        |>.blockOrderIso i).1 := by
  apply Fin.ext
  rfl

include hremaining hterminal in
theorem terminalBlockOrderIso_zero :
    (res.terminalBlockOrderIso
      terminal hremaining hterminal
      ⟨0, by
        have hn :=
          res.terminal_one_le_blockOrder
            terminal hremaining hterminal
        omega⟩).1 =
      (⟨0, by omega⟩ : Fin (2 * q)) := by
  rw [res.terminalBlockOrderIso_apply_eq_context
    terminal hremaining hterminal]
  exact
    (res.terminalContext terminal hremaining hterminal)
      |>.blockOrderIso_zero

include hremaining hterminal in
theorem terminalBlockOrderIso_last :
    (res.terminalBlockOrderIso
      terminal hremaining hterminal
      (primitiveLast
        (residualBlockOrder terminal.2)
        (res.terminal_one_le_blockOrder
          terminal hremaining hterminal))).1 =
      (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) := by
  rw [res.terminalBlockOrderIso_apply_eq_context
    terminal hremaining hterminal]
  exact
    (res.terminalContext terminal hremaining hterminal)
      |>.blockOrderIso_last

/-- The ambient tuple read in the increasing order of the terminal active
carrier. -/
def terminalBlockTuple
    (res' : R322AnalyticResidualPrefix ρ lam ε q hq)
    (terminal' : R322ExtractionStep (2 * q))
    (hremaining' : res'.remaining = [terminal'])
    (hterminal' :
      terminal'.1 = r322WholeEndpoint q hq)
    (x : Fin (2 * q) → T4) :
    Fin (2 * residualBlockOrder terminal'.2) → T4 :=
  fun i =>
    x (terminalBlockOrderIso
      res' terminal' hremaining' hterminal' i).1

include hremaining hterminal in
theorem terminal_residualChainEdgeFactor_internal
    (x : Fin (2 * q) → T4)
    (j : Fin (2 * residualBlockOrder terminal.2 - 1)) :
    res.residualChainEdgeFactor x
        ((res.terminalContext terminal hremaining hterminal)
          |>.internalEdge j) =
      ((res.terminalContext terminal hremaining hterminal)
        |>.internalEdges j)
          (res.terminalBlockTuple terminal hremaining hterminal x
              ⟨j.val, by
                have hj := j.isLt
                have _hn :=
                  (res.terminalContext terminal hremaining hterminal)
                    |>.one_le_blockOrder
                omega⟩ -
            res.terminalBlockTuple terminal hremaining hterminal x
              ⟨j.val + 1, by
                have hj := j.isLt
                have _hn :=
                  (res.terminalContext terminal hremaining hterminal)
                    |>.one_le_blockOrder
                omega⟩) := by
  let ctx := res.terminalContext terminal hremaining hterminal
  change
    Fin (2 * residualBlockOrder ctx.terminal.2 - 1) at j
  change
    res.residualChainEdgeFactor x (ctx.internalEdge j) =
      ctx.internalEdges j
        (x (ctx.blockOrderIso
              ⟨j.val, by
                have hj := j.isLt
                have hn := ctx.one_le_blockOrder
                omega⟩).1 -
          x (ctx.blockOrderIso
              ⟨j.val + 1, by
                have hj := j.isLt
                have hn := ctx.one_le_blockOrder
                omega⟩).1)
  have hactive :
      r322AnalyticEdgeLeftVertex (ctx.internalEdge j) ∈
        res.state.active := by
    change r322AnalyticEdgeLeftVertex (ctx.internalEdge j) ∈
      ctx.state.active
    rw [← ctx.block_eq_active]
    exact
      (ctx.blockOrderIso
        ⟨j.val, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩).2
  have hnotReserved :
      (ctx.internalEdge j).val ∉
        res.remainingRightValues := by
    rw [res.terminal_remainingRightValues
      terminal hremaining hterminal]
    simp only [List.mem_singleton]
    exact ne_of_lt (ctx.internalEdge j).isLt
  unfold residualChainEdgeFactor
  rw [if_pos hactive, if_neg hnotReserved]
  change
    ctx.state.edges (ctx.internalEdge j)
        (x (r322AnalyticEdgeLeftVertex (ctx.internalEdge j)) -
          x (res.edgeSuccessor (ctx.internalEdge j))) =
      ctx.state.edges (ctx.internalEdge j)
        (x (ctx.blockOrderIso
              ⟨j.val, by
                have hj := j.isLt
                have hn := ctx.one_le_blockOrder
                omega⟩).1 -
          x (ctx.blockOrderIso
              ⟨j.val + 1, by
                have hj := j.isLt
                have hn := ctx.one_le_blockOrder
                omega⟩).1)
  rw [show
    r322AnalyticEdgeLeftVertex (ctx.internalEdge j) =
      (ctx.blockOrderIso
        ⟨j.val, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩).1 by
        apply Fin.ext
        rfl]
  rw [show
    res.edgeSuccessor (ctx.internalEdge j) =
      (ctx.blockOrderIso
        ⟨j.val + 1, by
          have hj := j.isLt
          have hn := ctx.one_le_blockOrder
          omega⟩).1 by
        exact ctx.successorVertex_internalEdge j]

theorem terminal_residualChainEdgeFactor_eq_one_of_not_active
    (x : Fin (2 * q) → T4)
    (edge : Fin (2 * q - 1))
    (hedge :
      edge ∉ r322AnalyticActiveEdges res.state) :
    res.residualChainEdgeFactor x edge = 1 := by
  unfold residualChainEdgeFactor
  rw [if_neg]
  simpa only [mem_r322AnalyticActiveEdges] using hedge

include hremaining hterminal in
theorem terminal_residualChainProduct
    (x : Fin (2 * q) → T4) :
    res.residualChainProduct x =
      primitiveChainProduct
        (residualBlockOrder terminal.2)
        ((res.terminalContext terminal hremaining hterminal)
          |>.one_le_blockOrder)
        ((res.terminalContext terminal hremaining hterminal)
          |>.internalEdges)
        (res.terminalBlockTuple terminal hremaining hterminal x) := by
  let ctx := res.terminalContext terminal hremaining hterminal
  change
    res.residualChainProduct x =
      primitiveChainProduct
        (residualBlockOrder ctx.terminal.2)
        ctx.one_le_blockOrder ctx.internalEdges
        (fun i => x (ctx.blockOrderIso i).1)
  unfold residualChainProduct primitiveChainProduct
  calc
    (∏ edge, res.residualChainEdgeFactor x edge) =
        ∏ edge ∈ r322AnalyticActiveEdges res.state,
          res.residualChainEdgeFactor x edge := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro edge _hedgeUniv hedge
      exact
        res.terminal_residualChainEdgeFactor_eq_one_of_not_active
          x edge hedge
    _ =
        ∏ j,
          ctx.internalEdges j
            (x (ctx.blockOrderIso
                (primitiveEdgeLeft
                  (residualBlockOrder ctx.terminal.2)
                  ctx.one_le_blockOrder j)).1 -
              x (ctx.blockOrderIso
                (primitiveEdgeRight
                  (residualBlockOrder ctx.terminal.2)
                  ctx.one_le_blockOrder j)).1) := by
      have hstate : ctx.state = res.state := by
        dsimp only [ctx, terminalContext, terminalStepContext]
      rw [← hstate]
      rw [← ctx.internalEdgesFinset_eq_activeEdges]
      unfold R322AnalyticTerminalStepContext.internalEdgesFinset
      rw [Finset.prod_image ctx.internalEdge_injective.injOn]
      apply Finset.prod_congr rfl
      intro j _hj
      convert
        res.terminal_residualChainEdgeFactor_internal
          terminal hremaining hterminal x j using 1
      rfl

include hremaining hterminal in
theorem terminal_residualPrimitiveProduct_eq_covarianceSum
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x : Fin (2 * q) → T4) :
    res.residualPrimitiveProduct ρ' ε' x =
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder terminal.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder terminal.2)},
        primitiveCovarianceProduct ρ' ε'
          (residualBlockOrder terminal.2) κB.1
          (res.terminalBlockTuple
            terminal hremaining hterminal x) := by
  rw [res.terminal_residualPrimitiveProduct
    terminal hremaining ρ' ε' x]
  let ctx := res.terminalContext terminal hremaining hterminal
  let B : ExtractionBlockIndex res.pairing :=
    ⟨terminal.2, ctx.block_mem_extractionBlocks⟩
  have hB :
      res.remainingBlockIndex
          ⟨0, by simp [hremaining]⟩ = B := by
    apply Subtype.ext
    exact res.terminal_remainingBlockIndex_zero
      terminal hremaining
  rw [hB]
  unfold r322ExtractionBlockPrimitiveSum
    extractionBlockPrimitiveCovarianceFactor
    terminalBlockTuple
  apply Finset.sum_congr rfl
  intro κB _hκB
  congr 2

include hremaining hterminal in
theorem terminal_residualIntegrand_eq_closedSum
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x : Fin (2 * q) → T4) :
    res.residualIntegrand ρ' ε' x =
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder terminal.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder terminal.2)},
        detJclosedIntegrandWith ρ' ε'
          (2 * residualBlockOrder terminal.2)
          κB.1
          ((res.terminalContext terminal hremaining hterminal)
            |>.internalEdges)
          (res.terminalBlockTuple
            terminal hremaining hterminal x) := by
  let ctx := res.terminalContext terminal hremaining hterminal
  rw [sum_terminal_detJclosedIntegrandWith_eq_primitiveIntegrand
    ρ' ε' (residualBlockOrder terminal.2)
    ctx.one_le_blockOrder ctx.internalEdges
    (res.terminalBlockTuple terminal hremaining hterminal x)]
  unfold residualIntegrand
  rw [res.terminal_residualDifferenceProduct
    terminal hremaining hterminal x, mul_one]
  rw [res.terminal_residualChainProduct
    terminal hremaining hterminal x]
  rw [res.terminal_residualPrimitiveProduct_eq_covarianceSum
    terminal hremaining hterminal ρ' ε' x]
  unfold primitiveIntegrand
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_subtype
  intro κ
  rfl

/-- Increasing internal terminal-block positions are exactly the surviving
spatial coordinates of a singleton whole-carrier residual. -/
def terminalInternalCoordinateEquiv :
    Fin (2 * residualBlockOrder terminal.2 - 2) ≃
      res.SurvivingCoordinate where
  toFun j := by
    let ctx := res.terminalContext terminal hremaining hterminal
    let k :
        Fin (2 * residualBlockOrder ctx.terminal.2) :=
      ⟨j.val + 1, by
        have hj := j.isLt
        have hn := ctx.one_le_blockOrder
        change
          j.val <
            2 * residualBlockOrder ctx.terminal.2 - 2 at hj
        omega⟩
    let vertex := (ctx.blockOrderIso k).1
    have hactive : vertex ∈ res.state.active := by
      change vertex ∈ ctx.state.active
      rw [← ctx.block_eq_active]
      exact (ctx.blockOrderIso k).2
    have hpositive : 0 < vertex.val := by
      let zeroIndex :
          Fin (2 * residualBlockOrder ctx.terminal.2) :=
        ⟨0, by
          have hn := ctx.one_le_blockOrder
          omega⟩
      have hk : zeroIndex < k := by
        change 0 < j.val + 1
        omega
      have himage := ctx.blockOrderIso.strictMono hk
      change
        (ctx.blockOrderIso zeroIndex).1 <
          vertex at himage
      rw [ctx.blockOrderIso_zero] at himage
      exact Fin.mk_lt_mk.mp himage
    have hlast : vertex.val < 2 * q - 1 := by
      let lastIndex :=
        primitiveLast
          (residualBlockOrder ctx.terminal.2)
          ctx.one_le_blockOrder
      have hk : k < lastIndex := by
        change j.val + 1 <
          2 * residualBlockOrder ctx.terminal.2 - 1
        have hj := j.isLt
        change
          j.val <
            2 * residualBlockOrder ctx.terminal.2 - 2 at hj
        omega
      have himage := ctx.blockOrderIso.strictMono hk
      change
        vertex <
          (ctx.blockOrderIso lastIndex).1 at himage
      rw [ctx.blockOrderIso_last] at himage
      exact Fin.mk_lt_mk.mp himage
    exact ⟨vertex, hactive, hpositive, hlast⟩
  invFun i := by
    let ctx := res.terminalContext terminal hremaining hterminal
    have hiBlock : i.1 ∈ ctx.terminal.2 := by
      rw [ctx.block_eq_active]
      exact i.2.1
    let k :=
      ctx.blockOrderIso.symm
        (⟨i.1, hiBlock⟩ : ctx.terminal.2)
    have hkImage :
        (ctx.blockOrderIso k).1 = i.1 :=
      congrArg Subtype.val
        (ctx.blockOrderIso.apply_symm_apply
          (⟨i.1, hiBlock⟩ : ctx.terminal.2))
    have hkPos : 0 < k.val := by
      by_contra hnot
      have hkzero : k.val = 0 := Nat.eq_zero_of_not_pos hnot
      have hk :
          k =
            ⟨0, by
              have hn := ctx.one_le_blockOrder
              omega⟩ := by
        apply Fin.ext
        exact hkzero
      rw [hk, ctx.blockOrderIso_zero] at hkImage
      have hval := congrArg Fin.val hkImage
      have hiPos := i.2.2.1
      omega
    have hkLast :
        k.val <
          2 * residualBlockOrder ctx.terminal.2 - 1 := by
      have hkBound := k.isLt
      by_contra hnot
      have hkeq :
          k.val =
            2 * residualBlockOrder ctx.terminal.2 - 1 := by
        omega
      have hk :
          k =
            primitiveLast
              (residualBlockOrder ctx.terminal.2)
              ctx.one_le_blockOrder := by
        apply Fin.ext
        simpa only [primitiveLast] using hkeq
      rw [hk, ctx.blockOrderIso_last] at hkImage
      have hval := congrArg Fin.val hkImage
      have hiLast := i.2.2.2
      exact (ne_of_lt hiLast) hval.symm
    exact
      ⟨k.val - 1, by
        have horder :
            residualBlockOrder terminal.2 =
              residualBlockOrder ctx.terminal.2 := by
          dsimp only [ctx, terminalContext, terminalStepContext]
        rw [horder]
        omega⟩
  left_inv j := by
    apply Fin.ext
    let ctx := res.terminalContext terminal hremaining hterminal
    let k :
        Fin (2 * residualBlockOrder ctx.terminal.2) :=
      ⟨j.val + 1, by
        have hj := j.isLt
        have hn := ctx.one_le_blockOrder
        change
          j.val <
            2 * residualBlockOrder ctx.terminal.2 - 2 at hj
        omega⟩
    have hrecover :
        ctx.blockOrderIso.symm (ctx.blockOrderIso k) = k :=
      ctx.blockOrderIso.symm_apply_apply k
    have hval := congrArg Fin.val hrecover
    change
      (ctx.blockOrderIso.symm
        (ctx.blockOrderIso k)).val - 1 = j.val
    rw [hval]
    have hkVal : k.val = j.val + 1 := rfl
    omega
  right_inv i := by
    apply Subtype.ext
    let ctx := res.terminalContext terminal hremaining hterminal
    have hiBlock : i.1 ∈ ctx.terminal.2 := by
      rw [ctx.block_eq_active]
      exact i.2.1
    let k :=
      ctx.blockOrderIso.symm
        (⟨i.1, hiBlock⟩ : ctx.terminal.2)
    have hkImage :
        (ctx.blockOrderIso k).1 = i.1 :=
      congrArg Subtype.val
        (ctx.blockOrderIso.apply_symm_apply
          (⟨i.1, hiBlock⟩ : ctx.terminal.2))
    have hkPos : 0 < k.val := by
      by_contra hnot
      have hkzero : k.val = 0 := Nat.eq_zero_of_not_pos hnot
      have hk :
          k =
            ⟨0, by
              have hn := ctx.one_le_blockOrder
              omega⟩ := by
        apply Fin.ext
        exact hkzero
      rw [hk, ctx.blockOrderIso_zero] at hkImage
      have hval := congrArg Fin.val hkImage
      have hiPos := i.2.2.1
      omega
    change
      (ctx.blockOrderIso
        ⟨(k.val - 1) + 1, by
          have hkBound := k.isLt
          omega⟩).1 = i.1
    have hindex :
        (⟨(k.val - 1) + 1, by
            have hkBound := k.isLt
            omega⟩ :
          Fin (2 * residualBlockOrder ctx.terminal.2)) = k := by
      apply Fin.ext
      change (k.val - 1) + 1 = k.val
      omega
    rw [hindex, hkImage]

/-- Product-coordinate reindex from the terminal residual carrier to the
standard internal primitive coordinates. -/
def terminalInternalPiMeasurableEquiv :
    (res.SurvivingCoordinate → T4) ≃ᵐ
      (Fin (2 * residualBlockOrder terminal.2 - 2) → T4) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : res.SurvivingCoordinate => T4)
    (res.terminalInternalCoordinateEquiv
      terminal hremaining hterminal)).symm

include hremaining hterminal in
theorem measurePreserving_terminalInternalPiMeasurableEquiv :
    MeasurePreserving
      (res.terminalInternalPiMeasurableEquiv
        terminal hremaining hterminal)
      (Measure.pi fun _ : res.SurvivingCoordinate =>
        paperMeasure)
      (Measure.pi fun _ :
          Fin (2 * residualBlockOrder terminal.2 - 2) =>
        paperMeasure) := by
  simpa only [terminalInternalPiMeasurableEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ : res.SurvivingCoordinate => paperMeasure)
      (res.terminalInternalCoordinateEquiv
        terminal hremaining hterminal)).symm

@[simp]
theorem terminalInternalPiMeasurableEquiv_apply
    (v : res.SurvivingCoordinate → T4)
    (j : Fin (2 * residualBlockOrder terminal.2 - 2)) :
    res.terminalInternalPiMeasurableEquiv
        terminal hremaining hterminal v j =
      v (res.terminalInternalCoordinateEquiv
        terminal hremaining hterminal j) :=
  rfl

include hremaining hterminal in
theorem terminalBlockTuple_reconstruct_eq_primitiveAssemble
    (z : T4) (v : res.SurvivingCoordinate → T4) :
    res.terminalBlockTuple terminal hremaining hterminal
        (res.reconstruct z v) =
      primitiveAssemble
        (residualBlockOrder terminal.2)
        (res.terminal_one_le_blockOrder
          terminal hremaining hterminal)
        z 0
        (res.terminalInternalPiMeasurableEquiv
          terminal hremaining hterminal v) := by
  let ctx := res.terminalContext terminal hremaining hterminal
  let hn :=
    res.terminal_one_le_blockOrder
      terminal hremaining hterminal
  funext i
  by_cases hzero : i.val = 0
  · have hi :
        i =
          (⟨0, by
            have hn' := hn
            omega⟩ :
          Fin (2 * residualBlockOrder terminal.2)) :=
      Fin.ext hzero
    rw [hi, primitiveAssemble_zero]
    unfold terminalBlockTuple
    rw [res.terminalBlockOrderIso_zero
      terminal hremaining hterminal]
    exact res.reconstruct_zero z v
  by_cases hlast :
      i.val =
        2 * residualBlockOrder terminal.2 - 1
  · have hi :
        i =
          primitiveLast
            (residualBlockOrder terminal.2)
            hn := by
      apply Fin.ext
      simpa only [primitiveLast] using hlast
    rw [hi, primitiveAssemble_last]
    unfold terminalBlockTuple
    rw [res.terminalBlockOrderIso_last
      terminal hremaining hterminal]
    exact res.reconstruct_last z v
  · let j :
        Fin (2 * residualBlockOrder terminal.2 - 2) :=
      ⟨i.val - 1, by
        have hiBound := i.isLt
        omega⟩
    have hij :
        (⟨j.val + 1, by
            have hj := j.isLt
            have hn' := hn
            omega⟩ :
          Fin (2 * residualBlockOrder terminal.2)) = i := by
      apply Fin.ext
      dsimp only [j]
      omega
    let si : res.SurvivingCoordinate :=
      res.terminalInternalCoordinateEquiv
        terminal hremaining hterminal j
    let ji :
        Fin (2 * residualBlockOrder terminal.2) :=
      ⟨j.val + 1, by
        have hj := j.isLt
        have hn' := hn
        omega⟩
    have hji : ji = i := by
      apply Fin.ext
      exact congrArg Fin.val hij
    have hvertex :
        si.1 =
          (res.terminalBlockOrderIso
            terminal hremaining hterminal i).1 := by
      calc
        si.1 =
            (res.terminalBlockOrderIso
              terminal hremaining hterminal ji).1 := by
          apply Fin.ext
          rfl
        _ =
            (res.terminalBlockOrderIso
              terminal hremaining hterminal i).1 := by
          rw [hji]
    calc
      res.terminalBlockTuple terminal hremaining hterminal
          (res.reconstruct z v) i =
          res.reconstruct z v si.1 := by
        unfold terminalBlockTuple
        rw [hvertex]
      _ = v si :=
        res.reconstruct_surviving z v si
      _ =
          res.terminalInternalPiMeasurableEquiv
            terminal hremaining hterminal v j := by
        rw [terminalInternalPiMeasurableEquiv_apply]
      _ =
          primitiveAssemble
            (residualBlockOrder terminal.2)
            hn z 0
            (res.terminalInternalPiMeasurableEquiv
              terminal hremaining hterminal v) i := by
        have hijPrimitive :
            primitiveInternalIdx
              (residualBlockOrder terminal.2) hn j = i := by
          apply Fin.ext
          rw [primitiveInternalIdx_val_residual]
          dsimp only [j]
          omega
        rw [← hijPrimitive, primitiveAssemble_internal]

include hremaining hterminal in
/-- A singleton whole-carrier residual is exactly the terminal heterogeneous
primitive integral, with no division by the coupling and no nonzero-power
side condition. -/
theorem terminal_residualValue_eq_terminalSpatialIntegral
    (z : T4) :
    res.residualValue ρ lam ε z =
      ((res.terminalContext terminal hremaining hterminal)
        |>.terminalSpatialIntegral ρ lam ε z 0) := by
  let ctx := res.terminalContext terminal hremaining hterminal
  let hn :=
    res.terminal_one_le_blockOrder
      terminal hremaining hterminal
  let e :=
    res.terminalInternalPiMeasurableEquiv
      terminal hremaining hterminal
  let F :
      (Fin (2 * residualBlockOrder terminal.2 - 2) → T4) →
        ℝ :=
    fun u =>
      ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder terminal.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder terminal.2)},
        detJclosedIntegrandWith ρ ε
          (2 * residualBlockOrder terminal.2)
          κB.1 ctx.internalEdges
          (primitiveAssemble
            (residualBlockOrder terminal.2)
            hn z 0 u)
  have hreindex :
      (∫ v : res.SurvivingCoordinate → T4,
          F (e v)
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ u :
            Fin (2 * residualBlockOrder terminal.2 - 2) → T4,
          F u
        ∂Measure.pi fun _ => paperMeasure := by
    exact
      (res.measurePreserving_terminalInternalPiMeasurableEquiv
        terminal hremaining hterminal).integral_comp' F
  calc
    res.residualValue ρ lam ε z =
        lamEps lam ε ^
            (2 * residualBlockOrder terminal.2) *
          ∫ v : res.SurvivingCoordinate → T4,
            F (e v)
          ∂Measure.pi fun _ => paperMeasure := by
      unfold residualValue
      rw [res.terminal_remainingOrder terminal hremaining]
      apply congrArg (fun value : ℝ =>
        lamEps lam ε ^
          (2 * residualBlockOrder terminal.2) * value)
      apply integral_congr_ae
      filter_upwards with v
      dsimp only [F, e]
      rw [res.terminal_residualIntegrand_eq_closedSum
        terminal hremaining hterminal ρ ε
        (res.reconstruct z v)]
      rw [res.terminalBlockTuple_reconstruct_eq_primitiveAssemble
        terminal hremaining hterminal z v]
    _ =
        lamEps lam ε ^
            (2 * residualBlockOrder terminal.2) *
          ∫ u :
              Fin (2 * residualBlockOrder terminal.2 - 2) → T4,
            F u
          ∂Measure.pi fun _ => paperMeasure := by
      exact congrArg
        (fun value : ℝ =>
          lamEps lam ε ^
            (2 * residualBlockOrder terminal.2) * value)
        hreindex
    _ = ctx.terminalSpatialIntegral ρ lam ε z 0 := by
      unfold R322AnalyticTerminalStepContext.terminalSpatialIntegral
      dsimp only [F, hn, ctx, terminalContext,
        terminalStepContext]
      rfl

/-- Full current-residual integrability gives the exact weighted local
section integrability needed at almost every genuine outer coordinate.  The
weight is retained: no invalid cancellation is made on its zero set. -/
theorem eventually_integrable_weightedLocal_of_integrable
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (hint :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          res.residualIntegrand ρ ε
            (res.reconstruct z v))
        (Measure.pi fun _ => paperMeasure)) :
    let ctx :=
      res.properStepContext
        step suffix hremaining hproper
    let post :=
      res.afterProper step suffix hremaining hproper
    let base :
        (post.SurvivingCoordinate → T4) →
          Fin (2 * q) → T4 :=
      fun outer => post.reconstruct z outer
    let outerFactor :
        (post.SurvivingCoordinate → T4) → ℝ :=
      fun outer =>
        res.properOuterIntegrand
          step suffix hremaining hproper
          ρ ε (base outer)
    ∀ᵐ outer ∂(Measure.pi fun _ :
        post.SurvivingCoordinate => paperMeasure),
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder step.2) → T4 =>
          ctx.rawLocalIntegrand ρ ε
              (ctx.predecessorPoint (base outer) -
                ctx.successorPoint (base outer)) t *
            outerFactor outer)
        (Measure.pi fun _ => paperMeasure) := by
  dsimp only
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper step suffix hremaining hproper
  let μPre :
      Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μOuter :
      Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μBlock :
      Measure
        (Fin (2 * residualBlockOrder step.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let split :=
    res.properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper
  let base :
      (post.SurvivingCoordinate → T4) →
        Fin (2 * q) → T4 :=
    fun outer => post.reconstruct z outer
  let outerFactor :
      (post.SurvivingCoordinate → T4) → ℝ :=
    fun outer =>
      res.properOuterIntegrand
        step suffix hremaining hproper
        ρ ε (base outer)
  let g :
      ((post.SurvivingCoordinate → T4) ×
        (Fin (2 * residualBlockOrder step.2) → T4)) → ℝ :=
    fun p =>
      res.residualIntegrand ρ ε
        (res.properReconstructBlockTuple
          step suffix hremaining hproper
          (base p.1) p.2)
  have hcomp : Integrable (g ∘ split) μPre := by
    apply hint.congr
    filter_upwards with v
    change
      res.residualIntegrand ρ ε
          (res.reconstruct z v) =
        g (split v)
    unfold g split
    rw [res.reconstructBlockTuple_properOuterBlockSplit
      step suffix hremaining hproper z v]
  have hg : Integrable g (μOuter.prod μBlock) :=
    (res.measurePreserving_properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper).integrable_comp_emb
        split.measurableEmbedding |>.mp hcomp
  filter_upwards [hg.prod_right_ae] with outer houter
  have hactual :
      Integrable
        (fun actual :
            Fin (2 * residualBlockOrder step.2) → T4 =>
          ctx.ambientLocalIntegrand ρ ε
              (ctx.reconstructBlockTuple
                (base outer) actual) *
            outerFactor outer)
        μBlock := by
    apply houter.congr
    filter_upwards with actual
    dsimp only [g, ctx, properStepContext]
    rw [
      res.residualIntegrand_eq_ambientLocal_mul_outer
        step suffix hremaining hproper ρ ε,
      res.properOuterIntegrand_properReconstructBlockTuple
        step suffix hremaining hproper
        ρ ε (base outer) actual,
      res.properReconstructBlockTuple_eq_context
        step suffix hremaining hproper
        (base outer) actual]
    rfl
  let translation :=
    ctx.residualBlockTranslation
      (ctx.successorPoint (base outer))
  have htranslated :
      Integrable
        ((fun actual :
            Fin (2 * residualBlockOrder step.2) → T4 =>
          ctx.ambientLocalIntegrand ρ ε
              (ctx.reconstructBlockTuple
                (base outer) actual) *
            outerFactor outer) ∘ translation)
        μBlock :=
    (ctx.measurePreserving_residualBlockTranslation
      (ctx.successorPoint (base outer))).integrable_comp_emb
        translation.measurableEmbedding |>.mpr hactual
  apply htranslated.congr
  filter_upwards with t
  change
    ctx.ambientLocalIntegrand ρ ε
        (ctx.reconstructBlockTuple
          (base outer) (translation t)) *
        outerFactor outer =
      ctx.rawLocalIntegrand ρ ε
          (ctx.predecessorPoint (base outer) -
            ctx.successorPoint (base outer)) t *
        outerFactor outer
  rw [ctx.residualBlockTranslation_apply]
  change
    ctx.ambientLocalIntegrand ρ ε
        (ctx.reconstructRelativeBlockTuple
          (base outer) t) *
        outerFactor outer =
      ctx.rawLocalIntegrand ρ ε
          (ctx.predecessorPoint (base outer) -
            ctx.successorPoint (base outer)) t *
        outerFactor outer
  rw [ctx.ambientLocalIntegrand_reconstructRelativeBlockTuple]

/-- A weighted local section suffices for the exact collapse.  On the zero
weight set both sides vanish; away from it, scalar cancellation recovers
the unweighted local integrability required by the existing Fubini theorem. -/
theorem R322AnalyticProperStepContext.rawLocalSpatialIntegral_mul_outer_eq_nextState_of_weighted
    (ctx : R322AnalyticProperStepContext q hq)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (u : T4) (outer : ℝ)
    (hweighted :
      Integrable
        (fun t :
            Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
          ctx.rawLocalIntegrand ρ ε u t * outer)
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    lamEps lam ε ^
          (2 * residualBlockOrder ctx.step.2) *
        (∫ t :
            Fin (2 * residualBlockOrder ctx.step.2) → T4,
          ctx.rawLocalIntegrand ρ ε u t * outer
          ∂Measure.pi fun _ => paperMeasure) =
      (ctx.nextState ρ lam ε).edges
          ctx.predecessorEdge u * outer := by
  by_cases houter : outer = 0
  · simp [houter]
  · have hscaled :=
      hweighted.const_mul outer⁻¹
    have hlocal :
        Integrable (ctx.localIntegrand ρ ε u)
          (Measure.pi fun _ => paperMeasure) := by
      apply hscaled.congr
      filter_upwards with t
      rw [← ctx.rawLocalIntegrand_eq_localIntegrand ρ ε u t]
      field_simp
    exact
      ctx.rawLocalSpatialIntegral_mul_outer_eq_nextState
        ρ lam ε u outer hlocal hinternal

/-- Weighted-section form of the exact outer substitution. -/
theorem R322AnalyticProperStepContext.processedResidualOuterIntegral_eq_updated_of_weighted
    (ctx : R322AnalyticProperStepContext q hq)
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (base : Ω → Fin (2 * q) → T4)
    (outer : Ω → ℝ)
    (hweighted :
      ∀ᵐ ω ∂ν,
        Integrable
          (fun t :
              Fin (2 * residualBlockOrder ctx.step.2) → T4 =>
            ctx.rawLocalIntegrand ρ ε
                (ctx.predecessorPoint (base ω) -
                  ctx.successorPoint (base ω)) t *
              outer ω)
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder ctx.step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder ctx.step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder ctx.step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder ctx.step.2)
                κB.1 ctx.internalEdges
                (primitiveAssemble
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    ctx.processedResidualOuterIntegral
        ν ρ lam ε base outer =
      ctx.updatedResidualOuterIntegral
        ν ρ lam ε base outer := by
  unfold R322AnalyticProperStepContext.processedResidualOuterIntegral
    R322AnalyticProperStepContext.processedResidualIntegrand
    R322AnalyticProperStepContext.updatedResidualOuterIntegral
  apply integral_congr_ae
  filter_upwards [hweighted] with ω hω
  convert
    rawLocalSpatialIntegral_mul_outer_eq_nextState_of_weighted
      ctx
      ρ lam ε
      (ctx.predecessorPoint (base ω) -
        ctx.successorPoint (base ω))
      (outer ω) hω hinternal using 1
  apply congrArg (fun value : ℝ =>
    lamEps lam ε ^
      (2 * residualBlockOrder ctx.step.2) * value)
  apply integral_congr_ae
  filter_upwards with t
  rw [ctx.ambientLocalIntegrand_reconstructRelativeBlockTuple]

/-- Strengthened exact one-step residual identity.  Full current
integrability supplies weighted sections automatically, so the only
separate Fubini premise is the genuine closed-primitive section
integrability. -/
theorem residualValue_eq_afterProper_of_integrable
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (hint :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          res.residualIntegrand ρ ε
            (res.reconstruct z v))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder step.2)
                κB.1
                (res.properStepContext
                  step suffix hremaining hproper).internalEdges
                (primitiveAssemble
                  (residualBlockOrder step.2)
                  (res.properStepContext
                    step suffix hremaining hproper).one_le_blockOrder
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    res.residualValue ρ lam ε z =
      (res.afterProper step suffix
        hremaining hproper).residualValue
          ρ lam ε z := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  let ν :
      Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let base :
      (post.SurvivingCoordinate → T4) →
        Fin (2 * q) → T4 :=
    fun outer => post.reconstruct z outer
  let outerFactor :
      (post.SurvivingCoordinate → T4) → ℝ :=
    fun outer =>
      res.properOuterIntegrand
        step suffix hremaining hproper
        ρ ε (base outer)
  have hweighted :
      ∀ᵐ outer ∂ν,
        Integrable
          (fun t :
              Fin (2 * residualBlockOrder step.2) → T4 =>
            ctx.rawLocalIntegrand ρ ε
                (ctx.predecessorPoint (base outer) -
                  ctx.successorPoint (base outer)) t *
              outerFactor outer)
          (Measure.pi fun _ => paperMeasure) := by
    simpa only [ctx, post, ν, base, outerFactor] using
      res.eventually_integrable_weightedLocal_of_integrable
        step suffix hremaining hproper z hint
  have hinner :
      ∀ outer,
        (∫ t :
            Fin (2 * residualBlockOrder step.2) → T4,
          res.residualIntegrand ρ ε
            (res.properReconstructBlockTuple
              step suffix hremaining hproper
              (base outer) t)
          ∂Measure.pi fun _ => paperMeasure) =
          ∫ t :
              Fin (2 * residualBlockOrder step.2) → T4,
            ctx.ambientLocalIntegrand ρ ε
                (ctx.reconstructRelativeBlockTuple
                  (base outer) t) *
              outerFactor outer
            ∂Measure.pi fun _ => paperMeasure := by
    intro outer
    calc
      (∫ t :
          Fin (2 * residualBlockOrder step.2) → T4,
        res.residualIntegrand ρ ε
          (res.properReconstructBlockTuple
            step suffix hremaining hproper
            (base outer) t)
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ t :
            Fin (2 * residualBlockOrder step.2) → T4,
          ctx.ambientLocalIntegrand ρ ε
              (ctx.reconstructBlockTuple
                (base outer) t) *
            outerFactor outer
          ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        rw [
          res.residualIntegrand_eq_ambientLocal_mul_outer
            step suffix hremaining hproper ρ ε,
          res.properOuterIntegrand_properReconstructBlockTuple
            step suffix hremaining hproper
            ρ ε (base outer) t,
          res.properReconstructBlockTuple_eq_context
            step suffix hremaining hproper
            (base outer) t]
      _ = _ :=
        ctx.integral_actualBlock_eq_relativeBlock
          ρ ε (base outer) (outerFactor outer)
  let laterPower :=
    lamEps lam ε ^ (2 * post.remainingOrder)
  calc
    res.residualValue ρ lam ε z =
        lamEps lam ε ^ (2 * res.remainingOrder) *
          ∫ outer : post.SurvivingCoordinate → T4,
            ∫ t :
                Fin (2 * residualBlockOrder step.2) → T4,
              res.residualIntegrand ρ ε
                (res.properReconstructBlockTuple
                  step suffix hremaining hproper
                  (base outer) t)
              ∂Measure.pi fun _ => paperMeasure
            ∂ν :=
      res.residualValue_eq_iteratedProperRaw
        step suffix hremaining hproper
        ρ lam ε z hint
    _ =
        laterPower *
          ctx.processedResidualOuterIntegral
            ν ρ lam ε base outerFactor := by
      unfold R322AnalyticProperStepContext.processedResidualOuterIntegral
        R322AnalyticProperStepContext.processedResidualIntegrand
      rw [res.remainingOrder_eq_current_add_afterProper
        step suffix hremaining hproper]
      rw [← integral_const_mul]
      conv_rhs => rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with outer
      rw [hinner outer]
      dsimp only [laterPower, ctx, post, properStepContext]
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    _ =
        laterPower *
          ctx.updatedResidualOuterIntegral
            ν ρ lam ε base outerFactor := by
      apply congrArg (fun value : ℝ =>
        laterPower * value)
      exact
        R322AnalyticProperStepContext.processedResidualOuterIntegral_eq_updated_of_weighted
          ctx ν ρ lam ε base outerFactor
          hweighted hinternal
    _ = post.residualValue ρ lam ε z := by
      unfold R322AnalyticProperStepContext.updatedResidualOuterIntegral
        residualValue
      dsimp only [laterPower, ν]
      apply congrArg (fun value : ℝ =>
        lamEps lam ε ^ (2 * post.remainingOrder) * value)
      apply integral_congr_ae
      filter_upwards with outer
      have hstate :
          post.state = ctx.nextState ρ lam ε := by
        dsimp only [post, ctx, afterProper, properStepContext]
      rw [← hstate]
      simpa only [ctx, post, base, outerFactor] using
        (res.afterProper_residualIntegrand_eq_updated_mul_outer
          step suffix hremaining hproper
          ρ ε (base outer)).symm

/-- Full residual integrability is preserved by one genuine proper
collapse without a separate standard-section hypothesis.  The current
full integrability supplies exactly the weighted local sections needed
by the scalar-safe collapse identity. -/
theorem integrable_residualIntegrand_afterProper_of_weighted
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (hint :
      Integrable
        (fun v : res.SurvivingCoordinate → T4 =>
          res.residualIntegrand ρ ε
            (res.reconstruct z v))
        (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
        ∀ κB :
            {κ : PartialPairing
                (Fin (2 * residualBlockOrder step.2)) //
              κ ∈ primitiveFullPairings
                (residualBlockOrder step.2)},
          Integrable
            (fun v :
                Fin (2 * residualBlockOrder step.2 - 2) → T4 =>
              detJclosedIntegrandWith ρ ε
                (2 * residualBlockOrder step.2)
                κB.1
                (res.properStepContext
                  step suffix hremaining hproper).internalEdges
                (primitiveAssemble
                  (residualBlockOrder step.2)
                  (res.properStepContext
                    step suffix hremaining hproper).one_le_blockOrder
                  p.1 p.2 v))
            (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun outer :
          (res.afterProper step suffix
            hremaining hproper).SurvivingCoordinate → T4 =>
        (res.afterProper step suffix
          hremaining hproper).residualIntegrand ρ ε
            ((res.afterProper step suffix
              hremaining hproper).reconstruct z outer))
      (Measure.pi fun _ => paperMeasure) := by
  let ctx :=
    res.properStepContext
      step suffix hremaining hproper
  let post :=
    res.afterProper
      step suffix hremaining hproper
  let μPre : Measure (res.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μOuter :
      Measure (post.SurvivingCoordinate → T4) :=
    Measure.pi fun _ => paperMeasure
  let μBlock :
      Measure
        (Fin (2 * residualBlockOrder step.2) → T4) :=
    Measure.pi fun _ => paperMeasure
  let e :=
    res.properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper
  let base :
      (post.SurvivingCoordinate → T4) →
        Fin (2 * q) → T4 :=
    fun outer => post.reconstruct z outer
  let outerFactor :
      (post.SurvivingCoordinate → T4) → ℝ :=
    fun outer =>
      res.properOuterIntegrand
        step suffix hremaining hproper
        ρ ε (base outer)
  let g :
      ((post.SurvivingCoordinate → T4) ×
        (Fin (2 * residualBlockOrder step.2) → T4)) → ℝ :=
    fun p =>
      res.residualIntegrand ρ ε
        (res.properReconstructBlockTuple
          step suffix hremaining hproper
          (base p.1) p.2)
  have hcomp : Integrable (g ∘ e) μPre := by
    apply hint.congr
    filter_upwards with v
    change
      res.residualIntegrand ρ ε
          (res.reconstruct z v) =
        g (e v)
    unfold g e
    rw [
      res.reconstructBlockTuple_properOuterBlockSplit
        step suffix hremaining hproper z v]
  have hg : Integrable g (μOuter.prod μBlock) :=
    (res.measurePreserving_properOuterBlockPiMeasurableEquiv
      step suffix hremaining hproper).integrable_comp_emb
        e.measurableEmbedding |>.mp hcomp
  have hintegral :
      Integrable
        (fun outer =>
          ∫ t, g (outer, t) ∂μBlock)
        μOuter :=
    hg.integral_prod_left
  have hscaled :
      Integrable
        (fun outer =>
          lamEps lam ε ^
              (2 * residualBlockOrder step.2) *
            (∫ t, g (outer, t) ∂μBlock))
        μOuter :=
    hintegral.const_mul _
  have hweighted :
      ∀ᵐ outer ∂μOuter,
        Integrable
          (fun t :
              Fin (2 * residualBlockOrder step.2) → T4 =>
            ctx.rawLocalIntegrand ρ ε
                (ctx.predecessorPoint (base outer) -
                  ctx.successorPoint (base outer)) t *
              outerFactor outer)
          (Measure.pi fun _ => paperMeasure) := by
    simpa only [ctx, post, μOuter, base, outerFactor] using
      res.eventually_integrable_weightedLocal_of_integrable
        step suffix hremaining hproper z hint
  apply hscaled.congr
  filter_upwards [hweighted] with outer houter
  have hinner :
      (∫ t, g (outer, t) ∂μBlock) =
        ∫ t :
            Fin (2 * residualBlockOrder step.2) → T4,
          ctx.rawLocalIntegrand ρ ε
              (ctx.predecessorPoint (base outer) -
                ctx.successorPoint (base outer)) t *
            outerFactor outer
          ∂Measure.pi fun _ => paperMeasure := by
    calc
      (∫ t, g (outer, t) ∂μBlock) =
          ∫ t :
              Fin (2 * residualBlockOrder step.2) → T4,
            ctx.ambientLocalIntegrand ρ ε
                (ctx.reconstructBlockTuple
                  (base outer) t) *
              outerFactor outer
            ∂Measure.pi fun _ => paperMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [g, ctx, properStepContext]
        rw [
          res.residualIntegrand_eq_ambientLocal_mul_outer
            step suffix hremaining hproper ρ ε,
          res.properOuterIntegrand_properReconstructBlockTuple
            step suffix hremaining hproper
            ρ ε (base outer) t,
          res.properReconstructBlockTuple_eq_context
            step suffix hremaining hproper
            (base outer) t]
        rfl
      _ =
          ∫ t :
              Fin (2 * residualBlockOrder step.2) → T4,
            ctx.ambientLocalIntegrand ρ ε
                (ctx.reconstructRelativeBlockTuple
                  (base outer) t) *
              outerFactor outer
            ∂Measure.pi fun _ => paperMeasure :=
        ctx.integral_actualBlock_eq_relativeBlock
          ρ ε (base outer) (outerFactor outer)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        rw [
          ctx.ambientLocalIntegrand_reconstructRelativeBlockTuple]
  have hcollapse :=
    R322AnalyticProperStepContext.rawLocalSpatialIntegral_mul_outer_eq_nextState_of_weighted
      ctx
      ρ lam ε
      (ctx.predecessorPoint (base outer) -
        ctx.successorPoint (base outer))
      (outerFactor outer) houter hinternal
  have hpost :
      post.residualIntegrand ρ ε (base outer) =
        (ctx.nextState ρ lam ε).edges
            ctx.predecessorEdge
            (ctx.predecessorPoint (base outer) -
              ctx.successorPoint (base outer)) *
          outerFactor outer := by
    have hstate :
        post.state = ctx.nextState ρ lam ε := by
      dsimp only [post, ctx, afterProper, properStepContext]
    rw [← hstate]
    simpa only [ctx, post, base, outerFactor] using
      res.afterProper_residualIntegrand_eq_updated_mul_outer
        step suffix hremaining hproper
        ρ ε (base outer)
  rw [hpost, hinner]
  exact hcollapse

/-- The exact analytic side conditions consumed by one proper residual
transition at the displayed external endpoint. -/
structure ProperStepPremises
    (z : T4)
    (step : R322ExtractionStep (2 * q))
    (suffix : List (R322ExtractionStep (2 * q)))
    (hremaining : res.remaining = step :: suffix)
    (hproper :
      step.1 ≠ r322WholeEndpoint q hq) : Prop where
  internal :
    ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
      ∀ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder step.2)},
        Integrable
          (fun v :
              Fin (2 * residualBlockOrder step.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 * residualBlockOrder step.2)
              κB.1
              (res.properStepContext
                step suffix hremaining hproper).internalEdges
              (primitiveAssemble
                (residualBlockOrder step.2)
                (res.properStepContext
                  step suffix hremaining hproper).one_le_blockOrder
                p.1 p.2 v))
          (Measure.pi fun _ => paperMeasure)

/-- A finite exact proper-prefix run.  Every constructor records the actual
section-integrability facts used by Fubini; no global assumption or hidden
pointwise-to-a.e. pullback is built into the trace. -/
inductive ProperRun
    (z : T4) :
    R322AnalyticResidualPrefix ρ lam ε q hq →
      R322AnalyticResidualPrefix ρ lam ε q hq → Prop
  | refl
      (res : R322AnalyticResidualPrefix ρ lam ε q hq) :
      ProperRun z res res
  | step
      (res : R322AnalyticResidualPrefix ρ lam ε q hq)
      (current : R322ExtractionStep (2 * q))
      (suffix : List (R322ExtractionStep (2 * q)))
      (hremaining : res.remaining = current :: suffix)
      (hproper :
        current.1 ≠ r322WholeEndpoint q hq)
      (premises :
        res.ProperStepPremises z current suffix
          hremaining hproper)
      {finish :
        R322AnalyticResidualPrefix ρ lam ε q hq}
      (tail :
        ProperRun z
          (res.afterProper current suffix
            hremaining hproper)
          finish) :
      ProperRun z res finish

namespace ProperRun

variable {start finish :
    R322AnalyticResidualPrefix ρ lam ε q hq}
    {z : T4}

/-- Exact value invariance and full integrability propagate together along
an honest proper run. -/
theorem residualValue_eq
    (run : ProperRun z start finish)
    (hint :
      Integrable
        (fun v : start.SurvivingCoordinate → T4 =>
          start.residualIntegrand ρ ε
            (start.reconstruct z v))
        (Measure.pi fun _ => paperMeasure)) :
    start.residualValue ρ lam ε z =
      finish.residualValue ρ lam ε z := by
  induction run with
  | refl res =>
      rfl
  | step res current suffix hremaining hproper
      premises tail ih =>
      have hone :
          res.residualValue ρ lam ε z =
            (res.afterProper current suffix
              hremaining hproper).residualValue
                ρ lam ε z :=
        res.residualValue_eq_afterProper_of_integrable
          current suffix hremaining hproper z
          hint premises.internal
      have hnext :
          Integrable
            (fun v :
                (res.afterProper current suffix
                  hremaining hproper).SurvivingCoordinate → T4 =>
              (res.afterProper current suffix
                hremaining hproper).residualIntegrand ρ ε
                ((res.afterProper current suffix
                  hremaining hproper).reconstruct z v))
            (Measure.pi fun _ => paperMeasure) :=
        res.integrable_residualIntegrand_afterProper_of_weighted
          current suffix hremaining hproper z
          hint premises.internal
      exact hone.trans (ih hnext)

end ProperRun

/-- One terminal object carrying both the exact residual run and the
quantitative edge data used by its final majorant.  All fields refer to the
same `finish.state`; no comparison between separately selected terminal
contexts is needed downstream. -/
structure R322AnalyticAlignedTerminalData
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (C lam ε K A : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4) where
  finish :
    R322AnalyticResidualPrefix ρ lam ε q hq
  terminal : R322ExtractionStep (2 * q)
  scale : Fin (2 * q - 1) → ℝ
  pairing_eq : finish.pairing = κ
  remaining_eq : finish.remaining = [terminal]
  terminal_endpoint :
    terminal.1 = r322WholeEndpoint q hq
  run :
    ProperRun z
      (initial ρ lam ε hq κ hκ) finish
  budgetReachable :
    R322AnalyticBudgetScaleReachable
      hq ρ C lam ε K A κ hκ
      finish.state scale
  edgeCertificate :
    R322AnalyticEdgeCertificate
      finish.state scale

/-- The canonical proper prefix admits an honest exact run.  Quantitative
edge certificates are propagated on the very same residual object, rather
than selecting unrelated states with the same processed list. -/
theorem exists_r322AnalyticAlignedTerminalData
    (ρ : SmoothCutoff) :
    ∃ supportConstant C K A : ℝ,
      0 < supportConstant ∧ 0 < C ∧ 0 < K ∧ 1 ≤ A ∧
      (∀ (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
          (G : Fin (2 * n - 1) → T4 → ℝ),
          0 < lam → 0 < ε → ε ≤ 1 →
          n ≤ truncOrder ε →
          IsAdmissiblePrimitiveInput n G →
            MemEClassT4
                (primitiveKernelDiff ρ lam ε n hn G) ∧
              MemEClassT4
                (primitiveKernelInsertedDiff ρ lam ε n hn G) ∧
              PrimitiveKernelBounds ρ lam ε n hn G
                supportConstant C) ∧
      ∀ (lam ε : ℝ) (q : ℕ) (hq : 1 ≤ q)
        (κ : PartialPairing (Fin (2 * q)))
        (hκ : κ ∈ nonSplitPairings q)
        (z : T4),
        0 < lam →
        0 < ε →
        ε ≤ 1 →
        1 ≤ |Real.log ε| →
        q ≤ truncOrder ε →
        Nonempty
          (R322AnalyticAlignedTerminalData
            hq ρ C lam ε K A κ hκ z) := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨K, hK, hstep⟩ :=
    exists_r322AnalyticEdgeCertificate_updateProper_internalProduct_offDiagonal
      hsupport
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r322InitialAnalyticEdgeCertificate_one_le_uniform
  refine
    ⟨supportConstant, C, K, A,
      hsupport, hC, hK, hA, hprop, ?_⟩
  intro lam ε q hq κ hκ z
    hlam hε hε1 hlog hqtrunc
  obtain ⟨proper, terminal,
      hschedule, hterminal, hproper⟩ :=
    r322AnalyticSchedule_eq_proper_append_terminal_of_isNonSplit
      hq (mem_nonSplitPairings.mp hκ)
  have go :
      ∀ (steps : List (R322ExtractionStep (2 * q)))
        (current :
          R322AnalyticResidualPrefix ρ lam ε q hq)
        (scale : Fin (2 * q - 1) → ℝ),
        current.remaining = steps ++ [terminal] →
        current.pairing = κ →
        (∀ step ∈ steps,
          step.1 ≠ r322WholeEndpoint q hq) →
        R322AnalyticBudgetScaleReachable
          hq ρ C lam ε K A κ hκ current.state scale →
        R322AnalyticEdgeCertificate current.state scale →
        ∃ (finish :
            R322AnalyticResidualPrefix ρ lam ε q hq)
          (finalScale : Fin (2 * q - 1) → ℝ),
          ProperRun z current finish ∧
            finish.remaining = [terminal] ∧
            finish.pairing = κ ∧
            R322AnalyticBudgetScaleReachable
              hq ρ C lam ε K A κ hκ
              finish.state finalScale ∧
            R322AnalyticEdgeCertificate
              finish.state finalScale := by
    intro steps
    induction steps with
    | nil =>
        intro current scale hremaining hpairing _hproper
          hreachable hcert
        exact
          ⟨current, scale, ProperRun.refl current,
            by simpa using hremaining,
            hpairing, hreachable, hcert⟩
    | cons step rest ih =>
        intro current scale hremaining hpairing hproperSteps
          hreachable hcert
        let suffix :
            List (R322ExtractionStep (2 * q)) :=
          rest ++ [terminal]
        have hremainingHead :
            current.remaining = step :: suffix := by
          simpa only [suffix, List.cons_append] using
            hremaining
        have hproperHead :
            step.1 ≠ r322WholeEndpoint q hq :=
          hproperSteps step (by simp)
        let ctx : R322AnalyticProperStepContext q hq :=
          current.properStepContext
            step suffix hremainingHead hproperHead
        have hctxPairing :
            ctx.pairing = κ := by
          simpa only [ctx, properStepContext] using hpairing
        have hblockTrunc :
            residualBlockOrder ctx.step.2 ≤
              truncOrder ε := by
          exact extractionBlockOrder_le_truncOrder
            ctx.pairing
            (mem_nonSplitPairings.mp ctx.pairing_mem).1
            ctx.block_mem_extractionBlocks ε hqtrunc
        have hpropCtx :
            ∀ H, IsAdmissiblePrimitiveInput
                (residualBlockOrder ctx.step.2) H →
              MemEClassT4
                  (primitiveKernelDiff ρ lam ε
                    (residualBlockOrder ctx.step.2)
                    ctx.one_le_blockOrder H) ∧
                MemEClassT4
                  (primitiveKernelInsertedDiff ρ lam ε
                    (residualBlockOrder ctx.step.2)
                    ctx.one_le_blockOrder H) ∧
                PrimitiveKernelBounds ρ lam ε
                  (residualBlockOrder ctx.step.2)
                  ctx.one_le_blockOrder H
                  supportConstant C := by
          intro H hH
          exact hprop lam ε
            (residualBlockOrder ctx.step.2)
            ctx.one_le_blockOrder H
            hlam hε hε1 hblockTrunc hH
        have hprimitive :
            R322AnalyticPrimitiveCertificate
              ctx scale ρ C lam ε supportConstant :=
          hcert.primitiveCertificate_of_reachable
            current.absorbed hε
            (lt_of_lt_of_le zero_lt_one hlog) hpropCtx
        have hanalytic :
            R322AnalyticEdgeCertificate
              (ctx.nextState ρ lam ε)
              (r322AnalyticUpdatedEdgeScale
                ctx scale
                (r322AnalyticInternalEdgeScaleProduct
                  ctx scale)
                C lam K) :=
          hstep ρ C lam ε q hq
            current.pairing current.pairing_mem
            ctx current.absorbed rfl scale
            hcert hprimitive hC hlam hε hε1 hlog
        have hbudget :
            R322AnalyticEdgeCertificate
              (ctx.nextState ρ lam ε)
              (ctx.budgetUpdatedEdgeScale
                scale C lam K) :=
          hreachable.edgeCertificate_to_budgetUpdatedEdgeScale
            ctx hctxPairing rfl hA hanalytic
        let post :
            R322AnalyticResidualPrefix ρ lam ε q hq :=
          current.afterProper
            step suffix hremainingHead hproperHead
        have hremainingPost :
            post.remaining = rest ++ [terminal] := by
          rfl
        have hproperRest :
            ∀ later ∈ rest,
              later.1 ≠ r322WholeEndpoint q hq := by
          intro later hlater
          exact hproperSteps later (by simp [hlater])
        have hpairingPost :
            post.pairing = κ := by
          simpa only [post, afterProper] using hpairing
        have hreachablePost :
            R322AnalyticBudgetScaleReachable
              hq ρ C lam ε K A κ hκ post.state
              (ctx.budgetUpdatedEdgeScale
                scale C lam K) := by
          exact R322AnalyticBudgetScaleReachable.update
            ctx hctxPairing hreachable
        obtain ⟨finish, finalScale, tail,
            hfinish, hfinishPairing,
            hfinishReachable, hfinishCert⟩ :=
          ih post
            (ctx.budgetUpdatedEdgeScale scale C lam K)
            hremainingPost hpairingPost hproperRest
            hreachablePost hbudget
        have hinternal :
            ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
              ∀ κB :
                  {τ : PartialPairing
                      (Fin
                        (2 *
                          residualBlockOrder step.2)) //
                    τ ∈ primitiveFullPairings
                      (residualBlockOrder step.2)},
                Integrable
                  (fun v :
                      Fin
                        (2 *
                          residualBlockOrder step.2 - 2) →
                            T4 =>
                    detJclosedIntegrandWith ρ ε
                      (2 * residualBlockOrder step.2)
                      κB.1 ctx.internalEdges
                      (primitiveAssemble
                        (residualBlockOrder step.2)
                        ctx.one_le_blockOrder
                        p.1 p.2 v))
                  (Measure.pi fun _ => paperMeasure) := by
          exact current.absorbed
            |>.eventually_integrable_stepClosedIntegrand_section
              ctx hcert hε hε1
        exact
          ⟨finish, finalScale,
            ProperRun.step
              current step suffix
              hremainingHead hproperHead
              ⟨hinternal⟩ tail,
            hfinish, hfinishPairing,
            hfinishReachable, hfinishCert⟩
  let start :=
    initial ρ lam ε hq κ hκ
  have hremainingStart :
      start.remaining = proper ++ [terminal] := by
    simpa only [start, initial] using hschedule
  have hreachableStart :
      R322AnalyticBudgetScaleReachable
        hq ρ C lam ε K A κ hκ start.state
        (fun _ => A) := by
    exact R322AnalyticBudgetScaleReachable.initial
  have hcertStart :
      R322AnalyticEdgeCertificate
        start.state (fun _ => A) := by
    simpa only [start, initial] using hinitial q hq
  obtain ⟨finish, finalScale, run,
      hfinish, hfinishPairing,
      hfinishReachable, hfinishCert⟩ :=
    go proper start (fun _ => A)
      hremainingStart rfl hproper
      hreachableStart hcertStart
  exact ⟨{
    finish := finish
    terminal := terminal
    scale := finalScale
    pairing_eq := hfinishPairing
    remaining_eq := hfinish
    terminal_endpoint := hterminal
    run := by simpa only [start] using run
    budgetReachable := hfinishReachable
    edgeCertificate := hfinishCert }⟩

/-- Run-only projection of the aligned quantitative construction. -/
theorem exists_canonical_properRun
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4)
    (hlam : 0 < lam)
    (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hqtrunc : q ≤ truncOrder ε) :
    ∃ (finish :
        R322AnalyticResidualPrefix ρ lam ε q hq)
      (terminal : R322ExtractionStep (2 * q)),
      finish.remaining = [terminal] ∧
        terminal.1 = r322WholeEndpoint q hq ∧
        ProperRun z
          (initial ρ lam ε hq κ hκ) finish := by
  obtain ⟨supportConstant, C, K, A,
      _hsupport, _hC, _hK, _hA, _hprop, hdata⟩ :=
    exists_r322AnalyticAlignedTerminalData ρ
  obtain ⟨data⟩ :=
    hdata lam ε q hq κ hκ z
      hlam hε hε1 hlog hqtrunc
  exact
    ⟨data.finish, data.terminal,
      data.remaining_eq, data.terminal_endpoint,
      data.run⟩

/-- Endpoint-fibre exact identity furnished by any complete honest proper
run ending at its singleton whole-carrier residual. -/
theorem endpointFiberDetJSum_eq_terminalSpatialIntegral_of_run
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4)
    (finish :
      R322AnalyticResidualPrefix ρ lam ε q hq)
    (terminal : R322ExtractionStep (2 * q))
    (hremaining : finish.remaining = [terminal])
    (hterminal :
      terminal.1 = r322WholeEndpoint q hq)
    (run :
      ProperRun z
        (initial ρ lam ε hq κ hκ) finish)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      ((finish.terminalContext
        terminal hremaining hterminal)
        |>.terminalSpatialIntegral ρ lam ε z 0) := by
  have hinitial :
      Integrable
        (fun v :
            (initial ρ lam ε hq κ hκ).SurvivingCoordinate → T4 =>
          (initial ρ lam ε hq κ hκ).residualIntegrand
            ρ ε
            ((initial ρ lam ε hq κ hκ).reconstruct z v))
        (Measure.pi fun _ => paperMeasure) :=
    integrable_initial_residualIntegrand
      ρ lam ε hq κ hκ z hint
  calc
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
        (initial ρ lam ε hq κ hκ).residualValue
          ρ lam ε z :=
      endpointFiberDetJSum_eq_initial_residualValue
        ρ lam ε hq κ hκ z hint
    _ = finish.residualValue ρ lam ε z :=
      run.residualValue_eq hinitial
    _ =
        ((finish.terminalContext
          terminal hremaining hterminal)
          |>.terminalSpatialIntegral ρ lam ε z 0) :=
      finish.terminal_residualValue_eq_terminalSpatialIntegral
        terminal hremaining hterminal z

/-- Joint integrability of one frozen `J` summand with the terminal
endpoint fixed at zero.  This retains the internal variables, unlike
`integrable_detJ_zero`, and is therefore the genuine source of the
almost-everywhere fixed-endpoint sections used below. -/
theorem integrable_detJintegrand_zeroEndpoint
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q : ℕ) (hq : 1 ≤ q)
    (σ : PartialPairing (Fin (2 * q))) :
    Integrable
      (fun p : T4 × (Fin (2 * q - 2) → T4) =>
        detJintegrand ρ ε q σ
          (primitiveAssemble q hq p.1 0 p.2))
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (2 * q - 2) =>
          paperMeasure)) := by
  cases q with
  | zero =>
      omega
  | succ n =>
      obtain ⟨w, hsection⟩ :=
        exists_integrable_detJintegrand_endpoint_section
          ρ hε hε1 n σ
      let shiftEndpoint : T4 ≃ᵐ T4 :=
        MeasurableEquiv.piCongrRight fun i =>
          MeasurableEquiv.addRight (w i)
      let shiftInternal :
          (Fin (2 * n) → T4) ≃ᵐ
            (Fin (2 * n) → T4) :=
        MeasurableEquiv.piCongrRight fun _ =>
          MeasurableEquiv.addRight w
      let shift :
          (T4 × (Fin (2 * n) → T4)) ≃ᵐ
            (T4 × (Fin (2 * n) → T4)) :=
        MeasurableEquiv.prodCongr
          shiftEndpoint shiftInternal
      have hendpoint :
          MeasurePreserving shiftEndpoint
            paperMeasure paperMeasure := by
        rw [paperMeasure_eq_volume]
        change
          MeasurePreserving
            (fun z : T4 => fun i => z i + w i)
            (volume : Measure T4)
            (volume : Measure T4)
        exact
          measurePreserving_pi
            (fun _ : Fin dim =>
              (volume :
                Measure (AddCircle (2 * Real.pi))))
            (fun _ : Fin dim =>
              (volume :
                Measure (AddCircle (2 * Real.pi))))
            (fun i =>
              measurePreserving_add_right
                (volume :
                  Measure (AddCircle (2 * Real.pi)))
                (w i))
      have hinternal :
          MeasurePreserving shiftInternal
            (Measure.pi fun _ : Fin (2 * n) =>
              paperMeasure)
            (Measure.pi fun _ : Fin (2 * n) =>
              paperMeasure) := by
        change
          MeasurePreserving
            (fun v i => v i + w)
            (Measure.pi fun _ : Fin (2 * n) =>
              paperMeasure)
            (Measure.pi fun _ : Fin (2 * n) =>
              paperMeasure)
        exact measurePreserving_pi
          (fun _ : Fin (2 * n) => paperMeasure)
          (fun _ : Fin (2 * n) => paperMeasure)
          (fun _ => by
            rw [paperMeasure_eq_volume]
            exact measurePreserving_add_right
              (volume : Measure T4) w)
      have hshift :
          MeasurePreserving shift
            (paperMeasure.prod
              (Measure.pi fun _ : Fin (2 * n) =>
                paperMeasure))
            (paperMeasure.prod
              (Measure.pi fun _ : Fin (2 * n) =>
                paperMeasure)) :=
        hendpoint.prod hinternal
      have htranslated :=
        hshift.integrable_comp_of_integrable hsection
      apply htranslated.congr
      filter_upwards with p
      change
        detJintegrand ρ ε (n + 1) σ
            (r322DetJTupleSucc n
              ((shift p).1) w ((shift p).2)) =
          detJintegrand ρ ε (n + 1) σ
            (primitiveAssemble
              (n + 1) (by omega) p.1 0 p.2)
      have htuple :
          r322DetJTupleSucc n
              ((shift p).1) w ((shift p).2) =
            fun j =>
              primitiveAssemble
                (n + 1) (by omega) p.1 0 p.2 j + w := by
        have hshiftApply :
            shift p =
              (p.1 + w, fun i => p.2 i + w) := by
          rfl
        have htranslatedTuple :
            r322DetJTupleSucc n
                ((shift p).1) w ((shift p).2) =
              fun j =>
                r322DetJTupleSucc n
                  p.1 0 p.2 j + w := by
          rw [hshiftApply]
          funext j
          unfold r322DetJTupleSucc
          simpa only [Prod.fst, Prod.snd, zero_add] using
            assemble_add_const_r322
              p.1 0 w p.2 _
        have hbase :
            r322DetJTupleSucc n p.1 0 p.2 =
              primitiveAssemble
                (n + 1) (by omega) p.1 0 p.2 := by
          funext j
          unfold r322DetJTupleSucc primitiveAssemble
          apply congrArg (assemble p.1 0 p.2)
          apply Fin.ext
          rfl
        simpa only [hbase] using htranslatedTuple
      rw [htuple, detJintegrand_add_const_r322]

/-- Every summand in one endpoint-signature fibre has an integrable
internal section for almost every external endpoint. -/
theorem eventually_integrable_endpointFiber_sections
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q))) :
    ∀ᵐ z ∂paperMeasure,
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure) := by
  exact Filter.eventually_all.2 fun τ =>
    (integrable_detJintegrand_zeroEndpoint
      ρ hε hε1 q hq τ.1).prod_right_ae

/-- Uniform fixed-signature majorant whose exact identity and quantitative
terminal estimate are proved on one aligned terminal context. -/
theorem exists_r322AnalyticAlignedEndpointMajorant
    (ρ : SmoothCutoff) :
    ∃ supportConstant primitiveConstant : ℝ,
      0 < supportConstant ∧ 0 < primitiveConstant ∧
      ∀ (lam ε : ℝ) (q : ℕ) (hq : 1 ≤ q)
        (κ : PartialPairing (Fin (2 * q)))
        (_hκ : κ ∈ nonSplitPairings q)
        (z : T4),
        0 < lam →
        0 < ε →
        ε ≤ 1 →
        1 ≤ |Real.log ε| →
        q ≤ truncOrder ε →
        z ≠ 0 →
        (∀ τ : ReductionEndpointFiberAt κ,
          Integrable
            (fun v : Fin (2 * q - 2) → T4 =>
              detJintegrand ρ ε q τ.1
                (primitiveAssemble q hq z 0 v))
            (Measure.pi fun _ => paperMeasure)) →
        |endpointFiberDetJSum ρ lam ε q
            (reductionEndpointSignature κ) z| ≤
          primitiveKernelMajorant
            primitiveConstant lam ε
              supportConstant q z := by
  obtain ⟨supportConstant, C, K, A,
      hsupport, hC, hK, hA, hprop, hdata⟩ :=
    exists_r322AnalyticAlignedTerminalData ρ
  let primitiveConstant : ℝ :=
    A * max 1 K * C
  have hprimitiveConstant :
      0 < primitiveConstant := by
    dsimp only [primitiveConstant]
    exact mul_pos
      (mul_pos (lt_of_lt_of_le zero_lt_one hA)
        (lt_of_lt_of_le zero_lt_one
          (le_max_left 1 K)))
      hC
  refine
    ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, ?_⟩
  intro lam ε q hq κ hκ z
    hlam hε hε1 hlog hqtrunc hz hint
  obtain ⟨data⟩ :=
    hdata lam ε q hq κ hκ z
      hlam hε hε1 hlog hqtrunc
  let ctx : R322AnalyticTerminalStepContext q hq :=
    data.finish.terminalStepContext
      data.terminal data.remaining_eq
        data.terminal_endpoint
  have hpairing :
      ctx.pairing = κ := by
    simpa only [ctx, terminalStepContext] using
      data.pairing_eq
  have hblockTrunc :
      residualBlockOrder ctx.terminal.2 ≤
        truncOrder ε := by
    exact extractionBlockOrder_le_truncOrder
      ctx.pairing
      (mem_nonSplitPairings.mp ctx.pairing_mem).1
      ctx.block_mem_extractionBlocks ε hqtrunc
  have hpropCtx :
      ∀ H, IsAdmissiblePrimitiveInput
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
            supportConstant C := by
    intro H hH
    exact hprop lam ε
      (residualBlockOrder ctx.terminal.2)
      ctx.one_le_blockOrder H
      hlam hε hε1 hblockTrunc hH
  have hexact :
      endpointFiberDetJSum ρ lam ε q
          (reductionEndpointSignature κ) z =
        ctx.terminalSpatialIntegral ρ lam ε z 0 := by
    simpa only [ctx] using
      endpointFiberDetJSum_eq_terminalSpatialIntegral_of_run
        κ hκ z data.finish data.terminal
        data.remaining_eq data.terminal_endpoint
        data.run hint
  have hterminalHint :
      ∀ κB :
          {τ : PartialPairing
              (Fin
                (2 *
                  residualBlockOrder
                    ctx.terminal.2)) //
            τ ∈ primitiveFullPairings
              (residualBlockOrder ctx.terminal.2)},
        Integrable
          (fun v :
              Fin
                (2 *
                  residualBlockOrder
                    ctx.terminal.2 - 2) → T4 =>
            detJclosedIntegrandWith ρ ε
              (2 *
                residualBlockOrder
                  ctx.terminal.2)
              κB.1 ctx.internalEdges
              (primitiveAssemble
                (residualBlockOrder
                  ctx.terminal.2)
                ctx.one_le_blockOrder z 0 v))
          (Measure.pi fun _ => paperMeasure) := by
    exact data.finish.absorbed
      |>.terminalClosedIntegrand_hint
        ctx data.edgeCertificate hε hε1 z hz
  rw [hexact]
  simpa only [primitiveConstant] using
    ctx.abs_terminalSpatialIntegral_le_finalMajorant
      hpairing data.budgetReachable
      hA hK hC.le hlam.le supportConstant
      data.edgeCertificate hpropCtx z hz
      hterminalHint

/-- The production fixed-signature bound in the strength actually needed
by the downstream spatial integral.  The internal section premise is
discharged from joint frozen-`J` integrability, hence the honest conclusion
is almost everywhere in the external endpoint. -/
theorem exists_r322AnalyticAlignedEndpointMajorantAE
    (ρ : SmoothCutoff) :
    ∃ supportConstant primitiveConstant : ℝ,
      0 < supportConstant ∧ 0 < primitiveConstant ∧
      ∀ (lam ε : ℝ) (q : ℕ) (_hq : 1 ≤ q)
        (κ : PartialPairing (Fin (2 * q)))
        (_hκ : κ ∈ nonSplitPairings q),
        0 < lam →
        0 < ε →
        ε ≤ 1 →
        1 ≤ |Real.log ε| →
        q ≤ truncOrder ε →
        ∀ᵐ z ∂paperMeasure,
          |endpointFiberDetJSum ρ lam ε q
              (reductionEndpointSignature κ) z| ≤
            primitiveKernelMajorant
              primitiveConstant lam ε
                supportConstant q z := by
  obtain ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, hpointwise⟩ :=
    exists_r322AnalyticAlignedEndpointMajorant ρ
  refine
    ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, ?_⟩
  intro lam ε q hq κ hκ
    hlam hε hε1 hlog hqtrunc
  filter_upwards
      [eventually_integrable_endpointFiber_sections
        ρ hε hε1 hq κ,
       compl_mem_ae_iff.mpr
        (paperMeasure_singleton (0 : T4))]
      with z hint hz
  have hz0 : z ≠ 0 := by
    simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hz
  exact hpointwise lam ε q hq κ hκ z
    hlam hε hε1 hlog hqtrunc hz0 hint

/-! ## Almost-everywhere numerical closure -/

/-- Fixed-signature reduction output at the exact strength consumed by the
spatial integral. -/
def RenormFiberReductionOutputAE
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  (∀ σ ∈ nonSplitPairings q,
      Integrable (fun z : T4 => detJ ρ lam ε q σ z 0)
        paperMeasure) ∧
    ∀ s ∈ nonSplitReductionEndpointSignatures q,
      ∀ᵐ z ∂paperMeasure,
        |endpointFiberDetJSum ρ lam ε q s z| ≤
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z

/-- Grouped reduction output with an almost-everywhere spatial bound. -/
def RenormReductionOutputAE
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (primitiveConstant supportConstant : ℝ) : Prop :=
  (∀ σ ∈ nonSplitPairings q,
      Integrable (fun z : T4 => detJ ρ lam ε q σ z 0)
        paperMeasure) ∧
    ∀ᵐ z ∂paperMeasure,
      groupedDetJAbsSum ρ lam ε q z ≤
        primitiveKernelMajorant primitiveConstant lam ε
          supportConstant q z

/-- Summing the finite endpoint signatures preserves an a.e. estimate and
costs the same `4^(2q)` factor as the pointwise interface. -/
theorem RenormFiberReductionOutputAE.toRenormReductionOutputAE
    {ρ : SmoothCutoff} {lam ε : ℝ} {q : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hC : 0 ≤ primitiveConstant) (hlam : 0 ≤ lam)
    (hred : RenormFiberReductionOutputAE ρ lam ε q
      primitiveConstant supportConstant) :
    RenormReductionOutputAE ρ lam ε q
      (4 * primitiveConstant) supportConstant := by
  refine ⟨hred.1, ?_⟩
  have hall :
      ∀ᵐ z ∂paperMeasure,
        ∀ s ∈ nonSplitReductionEndpointSignatures q,
          |endpointFiberDetJSum ρ lam ε q s z| ≤
            primitiveKernelMajorant primitiveConstant lam ε
              supportConstant q z :=
    (Filter.eventually_all_finset
      (nonSplitReductionEndpointSignatures q)).2
        (fun s hs => hred.2 s hs)
  filter_upwards [hall] with z hz
  unfold groupedDetJAbsSum
  calc
    (∑ s ∈ nonSplitReductionEndpointSignatures q,
        |endpointFiberDetJSum ρ lam ε q s z|) ≤
        ∑ _s ∈ nonSplitReductionEndpointSignatures q,
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z :=
      Finset.sum_le_sum fun s hs => hz s hs
    _ =
        ((nonSplitReductionEndpointSignatures q).card : ℝ) *
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * q) *
          primitiveKernelMajorant primitiveConstant lam ε
            supportConstant q z := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          card_nonSplitReductionEndpointSignatures_le q
      · exact primitiveKernelMajorant_nonneg hC hlam
    _ = primitiveKernelMajorant
          (4 * primitiveConstant) lam ε
            supportConstant q z := by
      unfold primitiveKernelMajorant
      rw [show (4 * primitiveConstant) * lam =
          4 * (primitiveConstant * lam) by ring,
        mul_pow]
      ring

/-- The aligned analytic construction supplies the complete fixed-signature
a.e. reduction package, including the independent integrability field. -/
theorem exists_r322RenormFiberReductionOutputAE
    (ρ : SmoothCutoff) :
    ∃ supportConstant primitiveConstant : ℝ,
      0 < supportConstant ∧ 0 < primitiveConstant ∧
      ∀ (lam ε : ℝ) (q : ℕ) (_hq : 1 ≤ q),
        0 < lam →
        0 < ε →
        ε ≤ 1 →
        1 ≤ |Real.log ε| →
        q ≤ truncOrder ε →
        RenormFiberReductionOutputAE
          ρ lam ε q primitiveConstant supportConstant := by
  obtain ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, hae⟩ :=
    exists_r322AnalyticAlignedEndpointMajorantAE ρ
  refine
    ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, ?_⟩
  intro lam ε q hq hlam hε hε1 hlog hqtrunc
  refine ⟨?_, ?_⟩
  · intro σ hσ
    exact integrable_detJ_zero
      ρ lam hε hε1 q hq σ
  · intro s hs
    obtain ⟨κ, hκ, hsignature⟩ :=
      Finset.mem_image.mp hs
    simpa only [hsignature] using
      hae lam ε q hq κ hκ
        hlam hε hε1 hlog hqtrunc

/-- An a.e. grouped majorant controls the renormalization constant by the
same majorant integral as the stronger pointwise interface. -/
theorem abs_renormC2q_le_integral_primitiveKernelMajorant_of_ae
    {ρ : SmoothCutoff} {lam ε : ℝ} {q : ℕ}
    {primitiveConstant supportConstant : ℝ}
    (hε : 0 < ε)
    (hred : RenormReductionOutputAE ρ lam ε q
      primitiveConstant supportConstant) :
    |renormC2q ρ lam ε q| ≤
      ∫ z, primitiveKernelMajorant primitiveConstant lam ε
        supportConstant q z ∂paperMeasure := by
  let fiber :
      (Finset (Fin (2 * q)) × Finset (Fin (2 * q))) →
        T4 → ℝ :=
    fun s z =>
      endpointFiberDetJSum ρ lam ε q s z
  have hfiberInt :
      ∀ s ∈ nonSplitReductionEndpointSignatures q,
        Integrable (fiber s) paperMeasure := by
    intro s hs
    apply integrable_finsetSum
    intro σ hσ
    exact hred.1 σ (Finset.mem_filter.mp hσ).1
  have hfiberAbsInt :
      ∀ s ∈ nonSplitReductionEndpointSignatures q,
        Integrable (fun z => |fiber s z|) paperMeasure := by
    intro s hs
    simpa only [Real.norm_eq_abs] using
      (hfiberInt s hs).norm
  have hsumInt :
      Integrable
        (fun z : T4 =>
          ∑ s ∈ nonSplitReductionEndpointSignatures q,
            |fiber s z|)
        paperMeasure := by
    apply integrable_finsetSum
    intro s hs
    exact hfiberAbsInt s hs
  calc
    |renormC2q ρ lam ε q| =
        |∑ s ∈ nonSplitReductionEndpointSignatures q,
          ∑ σ ∈ nonSplitPairings q with
            reductionEndpointSignature σ = s,
            ∫ z, detJ ρ lam ε q σ z 0 ∂paperMeasure| := by
      rw [renormC2q_eq_sum]
      simp only [renormC2qTerm]
      rw [← sum_nonSplitPairings_by_endpointSignature]
    _ ≤ ∑ s ∈ nonSplitReductionEndpointSignatures q,
          |∑ σ ∈ nonSplitPairings q with
            reductionEndpointSignature σ = s,
            ∫ z, detJ ρ lam ε q σ z 0 ∂paperMeasure| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ nonSplitReductionEndpointSignatures q,
          ∫ z, |fiber s z| ∂paperMeasure := by
      apply Finset.sum_le_sum
      intro s hs
      have hfiberIntegral :
          (∑ σ ∈ nonSplitPairings q with
              reductionEndpointSignature σ = s,
              ∫ z, detJ ρ lam ε q σ z 0
                ∂paperMeasure) =
            ∫ z, fiber s z ∂paperMeasure := by
        unfold fiber endpointFiberDetJSum
        symm
        exact integral_finsetSum _ fun σ hσ =>
          hred.1 σ (Finset.mem_filter.mp hσ).1
      rw [hfiberIntegral]
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (μ := paperMeasure) (fiber s))
    _ = ∫ z,
          ∑ s ∈ nonSplitReductionEndpointSignatures q,
            |fiber s z| ∂paperMeasure := by
      symm
      exact integral_finsetSum _ hfiberAbsInt
    _ ≤ ∫ z, primitiveKernelMajorant primitiveConstant lam ε
          supportConstant q z ∂paperMeasure := by
      apply integral_mono_ae hsumInt
        (integrable_primitiveKernelMajorant primitiveConstant lam ε
          supportConstant q hε)
      filter_upwards [hred.2] with z hz
      exact hz

/-! ## Uniform numerical closure -/

/-- Raw integrated form of (4.15) from the honest almost-everywhere
reduction output.  The integration constants are chosen independently of
the cutoff, coupling, scale, perturbative order, and primitive constant. -/
theorem exists_abs_renormC2q_le_raw_of_ae :
    ∃ Cball Creg : ℝ, 0 < Cball ∧ 0 < Creg ∧
      ∀ (ρ : SmoothCutoff)
        (primitiveConstant supportConstant lam ε : ℝ)
        (q : ℕ),
        0 < ε → 0 < supportConstant →
        1 ≤ |Real.log ε| →
        RenormReductionOutputAE ρ lam ε q
          primitiveConstant supportConstant →
          |renormC2q ρ lam ε q| ≤
            (primitiveConstant * lam) ^ (2 * q) *
              ((Cball * supportConstant ^ 2 + Creg) *
                ε⁻¹ ^ (2 : ℕ) / |Real.log ε|) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveKernelMajorant_le
  refine ⟨Cball, Creg, hCball, hCreg, ?_⟩
  intro ρ primitiveConstant supportConstant lam ε q
    hε hsupport hlog hred
  exact
    (abs_renormC2q_le_integral_primitiveKernelMajorant_of_ae
      hε hred).trans
        (hmajorant primitiveConstant lam ε supportConstant q
          hε hsupport hlog)

/-- Numerical closure of R-322 for the almost-everywhere reduction
interface.  One positive constant is chosen before `ρ`, `λ`, `ε`, and `q`;
all order-independent integration losses are absorbed into the base of the
even power. -/
theorem exists_renormC_bound_of_reduction_ae
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ Crenorm : ℝ, 0 < Crenorm ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ),
        0 ≤ lam → 0 < ε →
        1 ≤ |Real.log ε| → 1 ≤ q →
        RenormReductionOutputAE ρ lam ε q
          primitiveConstant supportConstant →
          |renormC2q ρ lam ε q| ≤
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ (2 * q) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hraw⟩ :=
    exists_abs_renormC2q_le_raw_of_ae
  let K : ℝ := Cball * supportConstant ^ 2 + Creg
  let Crenorm : ℝ := primitiveConstant * (K + 1)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hCrenorm : 0 < Crenorm := by
    dsimp only [Crenorm]
    positivity
  refine ⟨Crenorm, hCrenorm, ?_⟩
  intro ρ lam ε q hlam hε hlog hq hred
  have hraw' :=
    hraw ρ primitiveConstant supportConstant lam ε q
      hε hsupport hlog hred
  have hscale :
      0 ≤ ε⁻¹ ^ (2 : ℕ) / |Real.log ε| := by
    positivity
  have habsorb :
      (primitiveConstant * lam) ^ (2 * q) * K ≤
        (Crenorm * lam) ^ (2 * q) := by
    have h :=
      mul_constant_le_absorbed_even_pow
        (base := primitiveConstant * lam) (K := K)
        (mul_nonneg hprimitive.le hlam) hK.le hq
    dsimp only [Crenorm]
    convert h using 1
    ring
  calc
    |renormC2q ρ lam ε q| ≤
        (primitiveConstant * lam) ^ (2 * q) *
          (K * ε⁻¹ ^ (2 : ℕ) /
            |Real.log ε|) := by
      simpa only [K] using hraw'
    _ =
        ((primitiveConstant * lam) ^ (2 * q) * K) *
          (ε⁻¹ ^ (2 : ℕ) /
            |Real.log ε|) := by
      ring
    _ ≤
        (Crenorm * lam) ^ (2 * q) *
          (ε⁻¹ ^ (2 : ℕ) /
            |Real.log ε|) :=
      mul_le_mul_of_nonneg_right habsorb hscale
    _ =
        ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
          (Crenorm * lam) ^ (2 * q) := by
      ring

/-- **Constructive R-322, paper (3.22).**

For a fixed cutoff, the exact residual iteration, its quantitative terminal
estimate, the almost-everywhere section argument, endpoint-signature
aggregation, spatial integration, and numerical absorption close to one
all-order theorem.  The named constant is uniform in `λ`, `ε`, and `q`.
The logarithmic lower bound is derived from
`1 ≤ q ≤ truncOrder ε`, rather than exposed as an extra hypothesis. -/
theorem exists_r322_renormC2q_bound
    (ρ : SmoothCutoff) :
    ∃ Crenorm : ℝ, 0 < Crenorm ∧
      ∀ (lam ε : ℝ) (q : ℕ),
        0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ q → q ≤ truncOrder ε →
          |renormC2q ρ lam ε q| ≤
            ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
              (Crenorm * lam) ^ (2 * q) := by
  obtain ⟨supportConstant, primitiveConstant,
      hsupport, hprimitive, hfiber⟩ :=
    exists_r322RenormFiberReductionOutputAE ρ
  have hgroupedPrimitive :
      0 < 4 * primitiveConstant := by
    positivity
  obtain ⟨Crenorm, hCrenorm, hbound⟩ :=
    exists_renormC_bound_of_reduction_ae
      hgroupedPrimitive hsupport
  refine ⟨Crenorm, hCrenorm, ?_⟩
  intro lam ε q hlam hε hε1 hq hqtrunc
  have hlog :
      (1 : ℝ) ≤ |Real.log ε| := by
    calc
      (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hq
      _ ≤ (truncOrder ε : ℝ) := by
        exact_mod_cast hqtrunc
      _ ≤ |Real.log ε| := by
        exact
          Nat.floor_le
            (abs_nonneg (Real.log ε))
  have hfiberOutput :=
    hfiber lam ε q hq
      hlam hε hε1 hlog hqtrunc
  have hgrouped :
      RenormReductionOutputAE ρ lam ε q
        (4 * primitiveConstant) supportConstant :=
    hfiberOutput.toRenormReductionOutputAE
      hprimitive.le hlam.le
  exact
    hbound ρ lam ε q hlam.le hε hlog hq
      hgrouped

/-- Complete exact R-322 iteration along the canonical proper prefix.
The terminal context is produced by the same residual run that proves the
identity, so no equality between independently selected terminal states is
assumed. -/
theorem exists_terminalContext_endpointFiberDetJSum_eq
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {q : ℕ} (hq : 1 ≤ q)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (z : T4)
    (hlam : 0 < lam)
    (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hlog : 1 ≤ |Real.log ε|)
    (hqtrunc : q ≤ truncOrder ε)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    ∃ ctx : R322AnalyticTerminalStepContext q hq,
      endpointFiberDetJSum ρ lam ε q
          (reductionEndpointSignature κ) z =
        ctx.terminalSpatialIntegral ρ lam ε z 0 := by
  obtain ⟨finish, terminal,
      hremaining, hterminal, run⟩ :=
    exists_canonical_properRun
      ρ lam ε hq κ hκ z
      hlam hε hε1 hlog hqtrunc
  let ctx :=
    finish.terminalStepContext
      terminal hremaining hterminal
  refine ⟨ctx, ?_⟩
  simpa only [ctx] using
    endpointFiberDetJSum_eq_terminalSpatialIntegral_of_run
      κ hκ z finish terminal
      hremaining hterminal run hint

end R322AnalyticResidualPrefix

end

end Anderson4D
