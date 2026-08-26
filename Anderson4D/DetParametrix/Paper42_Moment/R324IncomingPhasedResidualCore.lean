import Anderson4D.DetParametrix.Paper42_Moment.R324IncomingPhaseAnchorGeometry

/-!
# Slot-zero-erased residual cores carrying an incoming Fourier phase

After the incoming endpoint has been Fourier integrated, production slot
zero no longer contributes an ordinary edge factor.  Its Fourier character
is instead carried by `incomingPhaseAnchor`.  This file records that
representation pointwise.

The erased core is also evaluated against an arbitrary family of named
edges.  The corresponding congruence theorem makes precise that the value
does not inspect edge slot zero.  For an ordinary later head, whose
predecessor is not slot zero, the usual local/outer factorization survives
verbatim after erasing slot zero.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix
        ρ lam ε pairing)

/-! ## A slot-zero-free evaluator -/

/-- One sparse-chain factor evaluated with an arbitrary named-edge family. -/
def residualChainEdgeFactorWithEdges
    (edges : Fin (m + 1) → T4 → ℝ)
    (x y : T4) (v : Fin m → T4)
    (edge : Fin (m + 1)) : ℝ :=
  if edge ∈ res.activeEdgeSlots then
    if edge ∈ res.remainingOutgoingSlots then
      1
    else
      edges edge (res.edgeDisplacement x y v edge)
  else 1

/-- The ordinary sparse-chain product with production slot zero deleted. -/
def incomingErasedResidualChainProductWithEdges
    (edges : Fin (m + 1) → T4 → ℝ)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ edge ∈ (Finset.univ : Finset (Fin (m + 1))).erase 0,
    res.residualChainEdgeFactorWithEdges edges x y v edge

/-- One remaining signed difference evaluated with an arbitrary named-edge
family. -/
def residualStepDifferenceWithEdges
    (edges : Fin (m + 1) → T4 → ℝ)
    (x y : T4) (v : Fin m → T4)
    (step : R322ExtractionStep m) : ℝ :=
  let edge :=
    r324InternalVertexEdgeSlot step.1.2
  edges edge
      (assemble x y v (varIdx step.1.2) -
        assemble x y v (res.edgeSuccessor edge)) -
    edges edge
      (assemble x y v (varIdx step.1.1) -
        assemble x y v (res.edgeSuccessor edge))

/-- Product of all remaining signed differences, evaluated with an
arbitrary named-edge family. -/
def residualDifferenceProductWithEdges
    (edges : Fin (m + 1) → T4 → ℝ)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  (res.remaining.map
    (res.residualStepDifferenceWithEdges edges x y v)).prod

/-- Complete slot-zero-erased residual core evaluated with an arbitrary
named-edge family. -/
def incomingErasedResidualIntegrandWithEdges
    (edges : Fin (m + 1) → T4 → ℝ)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  res.incomingErasedResidualChainProductWithEdges edges x y v *
    res.residualDifferenceProductWithEdges edges x y v *
    res.residualPrimitiveProduct ρ' ε' v

/-- Slot zero is not an internal-vertex edge slot. -/
theorem r324InternalVertexEdgeSlot_ne_zero
    (i : Fin m) :
    r324InternalVertexEdgeSlot i ≠
      (0 : Fin (m + 1)) := by
  intro hzero
  have hval := congrArg Fin.val hzero
  simp only [r324InternalVertexEdgeSlot, Fin.val_zero] at hval
  omega

/-- The erased evaluator only inspects named edges away from slot zero. -/
theorem incomingErasedResidualIntegrandWithEdges_congr
    (edges edges' : Fin (m + 1) → T4 → ℝ)
    (hoff :
      ∀ edge : Fin (m + 1), edge ≠ 0 →
        edges edge = edges' edge)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualIntegrandWithEdges
        edges ρ' ε' x y v =
      res.incomingErasedResidualIntegrandWithEdges
        edges' ρ' ε' x y v := by
  have hchain :
      res.incomingErasedResidualChainProductWithEdges
          edges x y v =
        res.incomingErasedResidualChainProductWithEdges
          edges' x y v := by
    unfold incomingErasedResidualChainProductWithEdges
    apply Finset.prod_congr rfl
    intro edge hedge
    have hedgeNe : edge ≠ 0 :=
      (Finset.mem_erase.mp hedge).1
    unfold residualChainEdgeFactorWithEdges
    rw [hoff edge hedgeNe]
  have hstep
      (step : R322ExtractionStep m) :
      res.residualStepDifferenceWithEdges
          edges x y v step =
        res.residualStepDifferenceWithEdges
          edges' x y v step := by
    dsimp only [residualStepDifferenceWithEdges]
    rw [hoff
      (r324InternalVertexEdgeSlot step.1.2)
      (r324InternalVertexEdgeSlot_ne_zero step.1.2)]
  have hdifference :
      res.residualDifferenceProductWithEdges
          edges x y v =
        res.residualDifferenceProductWithEdges
          edges' x y v := by
    unfold residualDifferenceProductWithEdges
    apply congrArg List.prod
    apply List.map_congr_left
    intro step _hstep
    exact hstep step
  unfold incomingErasedResidualIntegrandWithEdges
  rw [hchain, hdifference]

/-- In particular, replacing the named edge at slot zero has no effect on
the erased residual core. -/
@[simp]
theorem incomingErasedResidualIntegrandWithEdges_update_zero
    (edges : Fin (m + 1) → T4 → ℝ)
    (replacement : T4 → ℝ)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualIntegrandWithEdges
        (Function.update edges 0 replacement)
        ρ' ε' x y v =
      res.incomingErasedResidualIntegrandWithEdges
        edges ρ' ε' x y v := by
  apply res.incomingErasedResidualIntegrandWithEdges_congr
  intro edge hedge
  simp [hedge]

/-! ## The actual reachable-state core -/

/-- The ordinary residual chain with its incoming production slot deleted. -/
def incomingErasedResidualChainProduct
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ edge ∈ (Finset.univ : Finset (Fin (m + 1))).erase 0,
    res.residualChainEdgeFactor x y v edge

/-- The complete reachable-state residual integrand after deleting the
ordinary factor at production slot zero. -/
def incomingErasedResidualIntegrand
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  res.incomingErasedResidualChainProduct x y v *
    res.residualDifferenceProduct x y v *
    res.residualPrimitiveProduct ρ' ε' v

/-- The concrete erased core is the arbitrary-edge evaluator at the
reachable state's named-edge family. -/
theorem incomingErasedResidualIntegrand_eq_withEdges
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualIntegrand ρ' ε' x y v =
      res.incomingErasedResidualIntegrandWithEdges
        res.state.edges ρ' ε' x y v := by
  rfl

/-- Usable extensional form of independence from `state.edges 0`. -/
theorem incomingErasedResidualIntegrand_eq_withEdges_of_eq_off_zero
    (edges : Fin (m + 1) → T4 → ℝ)
    (hoff :
      ∀ edge : Fin (m + 1), edge ≠ 0 →
        edges edge = res.state.edges edge)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedResidualIntegrandWithEdges
        edges ρ' ε' x y v =
      res.incomingErasedResidualIntegrand
        ρ' ε' x y v := by
  rw [res.incomingErasedResidualIntegrand_eq_withEdges]
  exact
    res.incomingErasedResidualIntegrandWithEdges_congr
      edges res.state.edges hoff ρ' ε' x y v

/-- Exact product erasure at slot zero. -/
theorem residualChainProduct_eq_zero_mul_incomingErased
    (x y : T4) (v : Fin m → T4) :
    res.residualChainProduct x y v =
      res.residualChainEdgeFactor x y v 0 *
        res.incomingErasedResidualChainProduct x y v := by
  unfold residualChainProduct
    incomingErasedResidualChainProduct
  exact
    (Finset.mul_prod_erase
      (Finset.univ : Finset (Fin (m + 1)))
      (res.residualChainEdgeFactor x y v)
      (Finset.mem_univ 0)).symm

/-- The full residual integrand is the slot-zero edge factor times the
slot-zero-erased core. -/
theorem residualIntegrand_eq_zero_mul_incomingErased
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4) (v : Fin m → T4) :
    res.residualIntegrand ρ' ε' x y v =
      res.residualChainEdgeFactor x y v 0 *
        res.incomingErasedResidualIntegrand
          ρ' ε' x y v := by
  unfold residualIntegrand
    incomingErasedResidualIntegrand
  rw [res.residualChainProduct_eq_zero_mul_incomingErased]
  ring

/-! ## Fourier phase carried by the erased core -/

/-- A coefficient times the transported incoming Fourier character and the
slot-zero-erased residual core. -/
def incomingPhasedResidualDensity
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (v : res.SurvivingCoordinate → T4) : ℂ :=
  coefficient *
    charT4 k (res.incomingPhaseAnchor x y v) *
    (res.incomingErasedResidualIntegrand
      ρ' ε' x y (res.reconstruct v) : ℂ)

/-! ## Ordinary heads preserve the erased representation -/

section Head

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

include tail hremaining

/-- If the current predecessor is not slot zero, every local ordinary-chain
slot is retained by `erase 0`. -/
theorem zero_not_mem_headChainSlots_of_predecessor_ne_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0) :
    (0 : Fin (m + 1)) ∉
      res.headChainSlots head tail hremaining := by
  rw [headChainSlots]
  simp only [Finset.mem_union, Finset.mem_singleton]
  rintro (hzero | hzero)
  · exact hpred hzero.symm
  · obtain ⟨j, _hj, heq⟩ :=
      Finset.mem_image.mp hzero
    have hlt :=
      res.predecessorSlot_lt_internalSlot
        head tail hremaining j
    rw [heq] at hlt
    exact (not_lt_of_ge (Fin.zero_le _)) hlt

/-- The outer chain after an ordinary head, with slot zero still erased. -/
def incomingErasedHeadOuterChainProductAfter
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ edge ∈
      ((Finset.univ \ res.headChainSlots
        head tail hremaining).erase 0),
    (res.afterHead
      head tail hremaining).residualChainEdgeFactor
        x y v edge

/-- All post-head factors outside an ordinary local head, with slot zero
deleted from the ordinary-chain part. -/
def incomingErasedHeadOuterFactor
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) : ℝ :=
  res.incomingErasedHeadOuterChainProductAfter
      head tail hremaining x y
      ((res.afterHead
        head tail hremaining).reconstruct v) *
    (res.afterHead
      head tail hremaining).residualDifferenceProduct
        x y
        ((res.afterHead
          head tail hremaining).reconstruct v) *
    (res.afterHead
      head tail hremaining).residualPrimitiveProduct
        ρ' ε'
        ((res.afterHead
          head tail hremaining).reconstruct v)

/-- The erased outer chain is independent of the head coordinates and is
unchanged by an ordinary head collapse. -/
theorem incomingErasedHeadOuterChainProductBefore_reconstruct_split
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    (∏ edge ∈
        ((Finset.univ \ res.headChainSlots
          head tail hremaining).erase 0),
      res.residualChainEdgeFactor x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v)))
        edge) =
      res.incomingErasedHeadOuterChainProductAfter
        head tail hremaining x y
        ((res.afterHead
          head tail hremaining).reconstruct v) := by
  unfold incomingErasedHeadOuterChainProductAfter
  apply Finset.prod_congr rfl
  intro edge hedge
  apply
    res.residualChainEdgeFactor_reconstruct_split_outer
      head tail hremaining x y t v
  exact
    (Finset.mem_sdiff.mp
      (Finset.mem_erase.mp hedge).2).2

/-- When the current predecessor is slot zero, the already-outer chain does
not contain slot zero, so erasing it once more is vacuous. -/
theorem incomingErasedHeadOuterChainProductAfter_eq_headOuter_of_eq_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : T4) (v : Fin m → T4) :
    res.incomingErasedHeadOuterChainProductAfter
        head tail hremaining x y v =
      res.headOuterChainProductAfter
        head tail hremaining x y v := by
  have hzero :
      (0 : Fin (m + 1)) ∉
        (Finset.univ \
          res.headChainSlots head tail hremaining) := by
    simp [headChainSlots, hpred]
  unfold incomingErasedHeadOuterChainProductAfter
    headOuterChainProductAfter
  rw [(Finset.erase_eq_self.mpr hzero)]

/-- Consequently the erased and ordinary outer factors coincide at a head
fed by slot zero. -/
theorem incomingErasedHeadOuterFactor_eq_headOuterFactor_of_eq_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingErasedHeadOuterFactor
        head tail hremaining ρ' ε' x y v =
      res.headOuterFactor
        head tail hremaining ρ' ε' x y v := by
  unfold incomingErasedHeadOuterFactor headOuterFactor
  rw [
    res.incomingErasedHeadOuterChainProductAfter_eq_headOuter_of_eq_zero
      head tail hremaining hpred]

/-- Pointwise ordinary-head factorization of the erased pre-head chain. -/
theorem
    incomingErasedResidualChainProduct_reconstruct_split_of_ne_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingErasedResidualChainProduct x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      res.residualChainEdgeFactor x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          (r324WithinHalfPredecessorSlot
            res.state head) *
        res.headInternalChainProduct
          head tail hremaining x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) *
        res.incomingErasedHeadOuterChainProductAfter
          head tail hremaining x y
          ((res.afterHead
            head tail hremaining).reconstruct v) := by
  let preTuple :=
    res.reconstruct
      ((res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).symm (t, v))
  let erased :=
    (Finset.univ : Finset (Fin (m + 1))).erase 0
  let localSlots :=
    res.headChainSlots head tail hremaining
  have hzero :
      (0 : Fin (m + 1)) ∉ localSlots :=
    res.zero_not_mem_headChainSlots_of_predecessor_ne_zero
      head tail hremaining hpred
  have hinter : erased ∩ localSlots = localSlots := by
    apply Finset.inter_eq_right.mpr
    intro edge hedge
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      subst edge
      exact hzero hedge
    · exact Finset.mem_univ edge
  have hdiff :
      erased \ localSlots =
        ((Finset.univ \ localSlots).erase 0) := by
    dsimp only [erased]
    ext edge
    simp only [Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_univ]
    tauto
  have hpartition :=
    Finset.prod_inter_mul_prod_sdiff
      erased localSlots
      (res.residualChainEdgeFactor x y preTuple)
  rw [hinter, hdiff] at hpartition
  unfold incomingErasedResidualChainProduct
  dsimp only [preTuple, erased, localSlots] at hpartition ⊢
  rw [← hpartition]
  rw [res.prod_headChainSlots_before
    head tail hremaining]
  rw [
    res.incomingErasedHeadOuterChainProductBefore_reconstruct_split
      head tail hremaining x y t v]

/-- At a head fed by slot zero, erasure removes precisely the predecessor
factor and leaves the internal local chain followed by the erased outer
chain. -/
theorem
    incomingErasedResidualChainProduct_reconstruct_split_of_eq_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingErasedResidualChainProduct x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      res.headInternalChainProduct
          head tail hremaining x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) *
        res.incomingErasedHeadOuterChainProductAfter
          head tail hremaining x y
          ((res.afterHead
            head tail hremaining).reconstruct v) := by
  let preTuple :=
    res.reconstruct
      ((res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).symm (t, v))
  let erased :=
    (Finset.univ : Finset (Fin (m + 1))).erase 0
  let internalSlots :=
    res.headInternalSlots head tail hremaining
  have hzeroInternal :
      (0 : Fin (m + 1)) ∉ internalSlots := by
    dsimp only [internalSlots]
    rw [← hpred]
    exact
      res.predecessorSlot_not_mem_headInternalSlots
        head tail hremaining
  have hinter :
      erased ∩ internalSlots = internalSlots := by
    apply Finset.inter_eq_right.mpr
    intro edge hedge
    exact
      Finset.mem_erase.mpr
        ⟨by
          intro heq
          subst edge
          exact hzeroInternal hedge,
          Finset.mem_univ edge⟩
  have hdiff :
      erased \ internalSlots =
        ((Finset.univ \
          res.headChainSlots head tail hremaining).erase 0) := by
    dsimp only [erased, internalSlots]
    ext edge
    simp [headChainSlots, hpred]
  have hpartition :=
    Finset.prod_inter_mul_prod_sdiff
      erased internalSlots
      (res.residualChainEdgeFactor x y preTuple)
  rw [hinter, hdiff] at hpartition
  unfold incomingErasedResidualChainProduct
  dsimp only [preTuple, erased, internalSlots] at hpartition ⊢
  rw [← hpartition]
  rw [res.prod_headInternalSlots
    head tail hremaining]
  change
    res.headInternalChainProduct
        head tail hremaining x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) *
      (∏ edge ∈
          ((Finset.univ \
            res.headChainSlots head tail hremaining).erase 0),
        res.residualChainEdgeFactor x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          edge) =
      _
  rw [
    res.incomingErasedHeadOuterChainProductBefore_reconstruct_split
      head tail hremaining x y t v]

/-- The three retained local factors at a slot-zero head are exactly the
existing translated incoming-erased raw local core. -/
theorem incomingErasedHeadLocalCore_reconstruct_split
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    (((res.headInternalChainProduct
          head tail hremaining x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) *
        res.residualStepDifference x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))
          head *
        r322ExtractionBlockPrimitiveSum ρ' ε' pairing
          (res.headContext
            head tail hremaining).blockIndex
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v)))) : ℝ) : ℂ) =
      (res.headContext
        head tail hremaining).incomingErasedTranslatedRawLocalCore
          ρ' ε'
          (res.headSuccessorPoint
            head tail hremaining x y v)
          t := by
  rw [
    res.headInternalChainProduct_split
      head tail hremaining x y t v,
    res.residualStepDifference_head_split
      head tail hremaining x y t v,
    res.extractionBlockPrimitiveSum_reconstruct_split
      head tail hremaining ρ' ε' t v]
  unfold R324WithinHalfStepContext.incomingErasedTranslatedRawLocalCore
  dsimp only [headContext]
  push_cast
  ring_nf
  congr

/-- Exact pointwise entry interface for the exceptional branch: after
slot-zero erasure, the retained head is the translated erased raw local
core and every post-head factor is the ordinary outer factor. -/
theorem incomingErasedResidualIntegrand_reconstruct_split_of_eq_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head = 0)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    (res.incomingErasedResidualIntegrand ρ' ε' x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) : ℂ) =
      (res.headContext
        head tail hremaining).incomingErasedTranslatedRawLocalCore
          ρ' ε'
          (res.headSuccessorPoint
            head tail hremaining x y v)
          t *
        (res.headOuterFactor
          head tail hremaining ρ' ε' x y v : ℂ) := by
  unfold incomingErasedResidualIntegrand
  rw [
    res.incomingErasedResidualChainProduct_reconstruct_split_of_eq_zero
      head tail hremaining hpred x y t v,
    res.residualDifferenceProduct_reconstruct_split
      head tail hremaining x y t v,
    res.residualPrimitiveProduct_reconstruct_split
      head tail hremaining ρ' ε' t v,
    res.incomingErasedHeadOuterChainProductAfter_eq_headOuter_of_eq_zero
      head tail hremaining hpred]
  have hlocal :=
    res.incomingErasedHeadLocalCore_reconstruct_split
      head tail hremaining ρ' ε' x y t v
  unfold headOuterFactor
  rw [← hlocal]
  push_cast
  ring

/-- Pointwise ordinary-head split of the complete erased pre-head core. -/
theorem incomingErasedResidualIntegrand_reconstruct_split_of_ne_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingErasedResidualIntegrand ρ' ε' x y
        (res.reconstruct
          ((res.splitSurvivingPiMeasurableEquiv
            head tail hremaining).symm (t, v))) =
      res.headLocalFactor
          head tail hremaining ρ' ε' x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) *
        res.incomingErasedHeadOuterFactor
          head tail hremaining ρ' ε' x y v := by
  unfold incomingErasedResidualIntegrand
    headLocalFactor incomingErasedHeadOuterFactor
  rw [
    res.incomingErasedResidualChainProduct_reconstruct_split_of_ne_zero
      head tail hremaining hpred x y t v,
    res.residualDifferenceProduct_reconstruct_split
      head tail hremaining x y t v,
    res.residualPrimitiveProduct_reconstruct_split
      head tail hremaining ρ' ε' t v]
  ring

/-- Pointwise factorization of the complete erased post-head core. -/
theorem afterHead_incomingErasedResidualIntegrand_of_ne_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    (res.afterHead
      head tail hremaining).incomingErasedResidualIntegrand
        ρ' ε' x y
        ((res.afterHead
          head tail hremaining).reconstruct v) =
      (res.afterHead
        head tail hremaining).residualChainEdgeFactor
          x y
          ((res.afterHead
            head tail hremaining).reconstruct v)
          (r324WithinHalfPredecessorSlot
            res.state head) *
        res.incomingErasedHeadOuterFactor
          head tail hremaining ρ' ε' x y v := by
  let post :=
    res.afterHead head tail hremaining
  let postTuple := post.reconstruct v
  let erased :=
    (Finset.univ : Finset (Fin (m + 1))).erase 0
  let localSlots :=
    res.headChainSlots head tail hremaining
  have hzero :
      (0 : Fin (m + 1)) ∉ localSlots :=
    res.zero_not_mem_headChainSlots_of_predecessor_ne_zero
      head tail hremaining hpred
  have hinter : erased ∩ localSlots = localSlots := by
    apply Finset.inter_eq_right.mpr
    intro edge hedge
    exact
      Finset.mem_erase.mpr
        ⟨by
          intro heq
          subst edge
          exact hzero hedge,
          Finset.mem_univ edge⟩
  have hdiff :
      erased \ localSlots =
        ((Finset.univ \ localSlots).erase 0) := by
    dsimp only [erased]
    ext edge
    simp only [Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_univ]
    tauto
  have hpartition :=
    Finset.prod_inter_mul_prod_sdiff
      erased localSlots
      (post.residualChainEdgeFactor x y postTuple)
  rw [hinter, hdiff] at hpartition
  unfold incomingErasedResidualIntegrand
    incomingErasedResidualChainProduct
    incomingErasedHeadOuterFactor
    incomingErasedHeadOuterChainProductAfter
  dsimp only [post, postTuple, erased, localSlots] at hpartition ⊢
  rw [← hpartition]
  rw [res.prod_headChainSlots_after
    head tail hremaining]
  ring

/-- The phase and the erased core both have the ordinary local/outer
pointwise split. -/
theorem incomingPhasedResidualDensity_reconstruct_split_of_ne_zero
    (hpred :
      r324WithinHalfPredecessorSlot res.state head ≠ 0)
    (coefficient : ℂ) (k : Z4)
    (ρ' : SmoothCutoff) (ε' : ℝ)
    (x y : T4)
    (t : Fin (2 * residualBlockOrder head.2) → T4)
    (v :
      (res.afterHead
        head tail hremaining).SurvivingCoordinate → T4) :
    res.incomingPhasedResidualDensity
        coefficient k ρ' ε' x y
        ((res.splitSurvivingPiMeasurableEquiv
          head tail hremaining).symm (t, v)) =
      coefficient *
        charT4 k
          ((res.afterHead
            head tail hremaining).incomingPhaseAnchor x y v) *
        (res.headLocalFactor
          head tail hremaining ρ' ε' x y
          (res.reconstruct
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))) : ℂ) *
        (res.incomingErasedHeadOuterFactor
          head tail hremaining ρ' ε' x y v : ℂ) := by
  unfold incomingPhasedResidualDensity
  rw [
    res.incomingPhaseAnchor_reconstruct_split_eq_afterHead
      head tail hremaining hpred x y t v,
    res.incomingErasedResidualIntegrand_reconstruct_split_of_ne_zero
      head tail hremaining hpred ρ' ε' x y t v]
  push_cast
  ring

end Head

namespace R324IncomingExceptionalStopTraceAssembly

variable {C K : ℝ}
    {initialScale : Fin (m + 1) → ℝ}

/-- The exact exceptional-stop Fourier density is the phased, slot-zero-
erased residual density.  The arbitrary post factor is absorbed into the
pointwise scalar coefficient; the retained head and the complete suffix
remain uncollapsed. -/
theorem incomingExceptionalStopFourierDensity_eq_incomingPhasedResidualDensity
    {Ω : Type*}
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) pairing initialScale)
    (k : Z4) (y : Ω → T4)
    (postOuter :
      Ω →
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate →
            T4) → ℂ)
    (ω : Ω)
    (t : Fin (2 * residualBlockOrder data.terminal.2) → T4)
    (v :
      (data.trace.stopPrefix.afterHead
        data.terminal data.suffix
        data.trace.stopPrefix_remaining_eq).SurvivingCoordinate → T4) :
    data.incomingExceptionalStopFourierDensity
        k y postOuter (ω, t, v) =
      data.trace.stopPrefix.incomingPhasedResidualDensity
        ((paperSecondOrderModeDecay k : ℂ) *
          postOuter ω v)
        k ρ ε 0 (y ω)
        ((data.trace.stopPrefix
          |>.splitSurvivingPiMeasurableEquiv
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).symm (t, v)) := by
  let res := data.trace.stopPrefix
  have hpred :
      r324WithinHalfPredecessorSlot
          res.state data.terminal =
        0 :=
    data.stop_predecessorSlot_eq_zero
  unfold incomingExceptionalStopFourierDensity
    incomingPhasedResidualDensity
  rw [translatedGreenMode_eq]
  rw [
    res.incomingPhaseAnchor_reconstruct_split_eq_headFirst
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq hpred
      0 (y ω) t v,
    res.incomingErasedResidualIntegrand_reconstruct_split_of_eq_zero
      data.terminal data.suffix
      data.trace.stopPrefix_remaining_eq hpred
      ρ ε 0 (y ω) t v]
  dsimp only [res, stopContext]
  unfold paperSecondOrderModeDecay paperModeNormSq
  ring_nf

end R324IncomingExceptionalStopTraceAssembly

end R324WithinHalfResidualPrefix

end

end Anderson4D
