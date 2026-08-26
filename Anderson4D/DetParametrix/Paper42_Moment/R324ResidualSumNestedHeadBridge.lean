import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualSumTerminalProjection
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualCompletePrimitiveHead

/-!
# Exact first-head bridge for the complete R-324 residual sum

This file keeps the signed terminal within-half chains intact while
reindexing the complete residual primitive sum along the literal initial
nested-cross schedule.  For a nonempty schedule it then exposes the
head/post coordinate split before any norm or estimate is taken.

The complete primitive-pairing sum on the head is kept as one finite sum.
The final lemmas identify the physical terminal Green chains with one
canonical head chain and the two outer connector edges.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The literal residual sum carried by an arbitrary nested suffix -/

/-- Complete primitive-sum product along the remaining blocks of one
literal nested-cross prefix.  The argument is still the ambient doubled
tuple, so this definition introduces no coordinate replacement. -/
def r324NestedResidualPrimitiveSumProduct
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (res : R324NestedCrossResidualPrefix κp κm π)
    (v : Fin (2 * m) → T4) : ℝ :=
  (res.remaining.map fun block =>
    r324PrimitivePartitionBlockSum
      ρ ε κp κm π block.carrier v).prod

@[simp]
theorem r324NestedResidualPrimitiveSumProduct_initial
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (v : Fin (2 * m) → T4) :
    r324NestedResidualPrimitiveSumProduct
        ρ ε κp κm π
        (R324NestedCrossResidualPrefix.initial κp κm π) v =
      r324ResidualPrimitiveSumProduct
        ρ ε κp κm π v := by
  symm
  exact
    r324ResidualPrimitiveSumProduct_eq_nestedSchedule
      ρ ε κp κm π v

theorem r324NestedResidualPrimitiveSumProduct_head
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (ctx : R324NestedCrossStepContext κp κm π)
    (v : Fin (2 * m) → T4) :
    r324NestedResidualPrimitiveSumProduct
        ρ ε κp κm π ctx.residual v =
      r324PrimitivePartitionBlockSum
          ρ ε κp κm π ctx.head.carrier v *
        r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π ctx.next v := by
  unfold r324NestedResidualPrimitiveSumProduct
  rw [ctx.remaining_eq]
  rfl

/-! ## The signed physical core on the concrete initial prefix -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The two completed, still signed, within-half Green chains read on the
literal initial nested reconstruction. -/
def initialNestedSignedChainFactor
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) : ℂ :=
  (terminal.left.residualChainProduct x y
      (fun i =>
        terminal.nestedReconstruct π v
          (leftMomentIndex i)) : ℂ) *
    (terminal.right.residualChainProduct z w
      (fun i =>
        terminal.nestedReconstruct π v
          (rightMomentIndex i)) : ℂ)

/-- Pointwise identification of the transported physical core with the
literal initial nested prefix: the terminal Green chains stay signed and
the complete residual primitive sums remain grouped blockwise. -/
theorem initialNestedResidualSumPhysicalCore_eq_signedChain_mul_nested
    (π : κp.singles ≃ κm.singles)
    (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) :
    terminal.initialNestedResidualSumPhysicalCore
        π x y z w v =
      terminal.initialNestedSignedChainFactor
          π x y z w v *
        (r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π
          (R324NestedCrossResidualPrefix.initial
            κp κm π)
          (terminal.nestedReconstruct π v) : ℂ) := by
  let p :=
    (terminal.terminalProductPiMeasurableEquivNested π).symm v
  have hp :
      terminal.terminalProductPiMeasurableEquivNested π p = v :=
    (terminal.terminalProductPiMeasurableEquivNested π).apply_symm_apply v
  have hreconstruct :
      terminal.terminalDoubledReconstruct p =
        terminal.nestedReconstruct π v := by
    rw [← hp]
    exact
      terminal.terminalDoubledReconstruct_eq_nestedReconstruct π p
  have hleft :
      terminal.left.reconstruct p.1 =
        fun i =>
          terminal.nestedReconstruct π v
            (leftMomentIndex i) := by
    funext i
    have hi :=
      congrFun hreconstruct (leftMomentIndex i)
    simpa only [terminalDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex] using hi
  have hright :
      terminal.right.reconstruct p.2 =
        fun i =>
          terminal.nestedReconstruct π v
            (rightMomentIndex i) := by
    funext i
    have hi :=
      congrFun hreconstruct (rightMomentIndex i)
    simpa only [terminalDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex] using hi
  unfold initialNestedResidualSumPhysicalCore
    terminalResidualSumPhysicalCore
    residualSumCrossFactor
    initialNestedSignedChainFactor
  change
    (terminal.left.residualIntegrand
        ρ ε x y (terminal.left.reconstruct p.1) : ℂ) *
      (terminal.right.residualIntegrand
        ρ ε z w (terminal.right.reconstruct p.2) : ℂ) *
      (r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (terminal.terminalDoubledReconstruct p) : ℂ) =
      _
  rw [terminal.left_residualIntegrand_eq_chain,
    terminal.right_residualIntegrand_eq_chain,
    hleft, hright, hreconstruct,
    r324NestedResidualPrimitiveSumProduct_initial]

end R324TwoHalfTerminalData

/-! ## A nonempty initial schedule and its exact head/post split -/

/-- The proof-relevant first step of a nonempty literal initial schedule. -/
def r324InitialNestedCrossStepContext
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial
        κp κm π).remaining = head :: tail) :
    R324NestedCrossStepContext κp κm π where
  residual :=
    R324NestedCrossResidualPrefix.initial κp κm π
  head := head
  tail := tail
  remaining_eq := hremaining

namespace R324NestedCrossStepContext

variable {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}

/-- Exact first-head factorization of the complete residual primitive sum
after the proved head/post coordinate split. -/
theorem initial_residualSum_reconstruct_split
    (ctx : R324NestedCrossStepContext κp κm π)
    (hinitial :
      ctx.residual =
        R324NestedCrossResidualPrefix.initial κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (t : Fin (2 * ctx.order) → T4)
    (post : ctx.PostCoordinate → T4) :
    r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (ctx.reconstruct
          (ctx.splitSurvivingPiMeasurableEquiv.symm
            (t, post))) =
      r324PrimitivePartitionBlockSum
          ρ ε κp κm π ctx.head.carrier
          (ctx.reconstruct
            (ctx.splitSurvivingPiMeasurableEquiv.symm
              (t, post))) *
        r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π ctx.next
          (ctx.reconstruct
            (ctx.splitSurvivingPiMeasurableEquiv.symm
              (t, post))) := by
  rw [← r324NestedResidualPrimitiveSumProduct_initial
    ρ ε κp κm π]
  rw [← hinitial]
  exact
    r324NestedResidualPrimitiveSumProduct_head
      ρ ε ctx _

/-- The head covariance factor, multiplied by the moving central gap, is
the complete primitive head integrand with the trivial local chain.  The
physical signed terminal Green chains have deliberately not been moved
inside this factor. -/
theorem centralGap_mul_headBlockSum_eq_completeCrossGap_one
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (t : Fin (2 * ctx.order) → T4)
    (post : ctx.PostCoordinate → T4) :
    torusDistSq
          (t ctx.leftGapIndex - t ctx.rightGapIndex) *
        r324PrimitivePartitionBlockSum
          ρ ε κp κm π ctx.head.carrier
          (ctx.reconstruct
            (ctx.splitSurvivingPiMeasurableEquiv.symm
              (t, post))) =
      ctx.completeCrossGapPrimitiveIntegrand
        ρ ε (fun _ _ => 1) t := by
  have hchain :
      primitiveChainProduct
          ctx.order ctx.one_le_order
          (fun _ _ => (1 : ℝ)) t = 1 := by
    unfold primitiveChainProduct
    simp
  calc
    _ =
        torusDistSq
            (t ctx.leftGapIndex - t ctx.rightGapIndex) *
          primitiveChainProduct
              ctx.order ctx.one_le_order
              (fun _ _ => (1 : ℝ)) t *
          r324PrimitivePartitionBlockSum
            ρ ε κp κm π ctx.head.carrier
            (ctx.reconstruct
              (ctx.splitSurvivingPiMeasurableEquiv.symm
                (t, post))) := by
      rw [hchain]
      ring
    _ =
        ctx.completeCrossGapPrimitiveIntegrand
          ρ ε (fun _ _ => 1) t :=
      ctx.headGapChainBlockSum_eq_completeCrossGapPrimitiveIntegrand
        ρ ε (fun _ _ => 1) t post

/-- Pointwise head normal form at an arbitrary nested suffix.  Unlike
`centralGap_mul_initialResidualSum_reconstruct_split`, this statement does
not identify the current residual with the initial prefix.  It is therefore
the recursive covariance identity needed after each proper head has been
removed: the complete primitive sum stays grouped, the current head is
exposed exactly, and the untouched product is indexed by `ctx.next`. -/
theorem centralGap_mul_nestedResidualSum_reconstruct_split
    (ctx : R324NestedCrossStepContext κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (t : Fin (2 * ctx.order) → T4)
    (post : ctx.PostCoordinate → T4) :
    torusDistSq
          (t ctx.leftGapIndex - t ctx.rightGapIndex) *
        r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π ctx.residual
          (ctx.reconstruct
            (ctx.splitSurvivingPiMeasurableEquiv.symm
              (t, post))) =
      ctx.completeCrossGapPrimitiveIntegrand
          ρ ε (fun _ _ => 1) t *
        r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π ctx.next
          (ctx.reconstruct
            (ctx.splitSurvivingPiMeasurableEquiv.symm
              (t, post))) := by
  rw [r324NestedResidualPrimitiveSumProduct_head]
  rw [← mul_assoc,
    ctx.centralGap_mul_headBlockSum_eq_completeCrossGap_one
      ρ ε t post]

/-- Pointwise first-head normal form: after multiplying by the moving
central gap, the whole complete residual sum is one complete primitive
head integrand times the untouched literal suffix product. -/
theorem centralGap_mul_initialResidualSum_reconstruct_split
    (ctx : R324NestedCrossStepContext κp κm π)
    (hinitial :
      ctx.residual =
        R324NestedCrossResidualPrefix.initial κp κm π)
    (ρ : SmoothCutoff) (ε : ℝ)
    (t : Fin (2 * ctx.order) → T4)
    (post : ctx.PostCoordinate → T4) :
    torusDistSq
          (t ctx.leftGapIndex - t ctx.rightGapIndex) *
        r324ResidualPrimitiveSumProduct
          ρ ε κp κm π
          (ctx.reconstruct
            (ctx.splitSurvivingPiMeasurableEquiv.symm
              (t, post))) =
      ctx.completeCrossGapPrimitiveIntegrand
          ρ ε (fun _ _ => 1) t *
        r324NestedResidualPrimitiveSumProduct
          ρ ε κp κm π ctx.next
          (ctx.reconstruct
            (ctx.splitSurvivingPiMeasurableEquiv.symm
              (t, post))) := by
  rw [ctx.initial_residualSum_reconstruct_split
    hinitial ρ ε t post]
  rw [← mul_assoc,
    ctx.centralGap_mul_headBlockSum_eq_completeCrossGap_one
      ρ ε t post]

end R324NestedCrossStepContext

end

end Anderson4D
