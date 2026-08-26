import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticProcessedIntegrandBridge

/-! # Ambient residual coordinates for the R-322 proper-step induction

After a proper prefix has been integrated, the variables which remain are
the vertices of `R322AnalyticEdgeState.active`.  The edge stored at an active
left vertex connects it to the next active vertex, not necessarily to the
next ambient index.  This file supplies that successor, reconstructs one
ambient block relative to its active successor, and proves the corresponding
outer-Fubini update.

The relative block variable is translated back into the actual ambient
tuple.  Thus the theorem below does not identify an unintegrated original
integrand with an already collapsed state.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The next vertex in a sparse active carrier -/

/-- Active vertices strictly after `i`. -/
def r322AnalyticSuccessorCandidates
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (i : Fin (2 * q)) :
    Finset (Fin (2 * q)) :=
  state.active.filter fun j => i < j

/-- There is a successor candidate whenever `i` lies before the global
right endpoint. -/
theorem r322AnalyticSuccessorCandidates_nonempty
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (i : Fin (2 * q))
    (hi : i.val < 2 * q - 1) :
    (r322AnalyticSuccessorCandidates state i).Nonempty := by
  let last : Fin (2 * q) := ⟨2 * q - 1, by omega⟩
  refine ⟨last, Finset.mem_filter.mpr
    ⟨state.last_mem, ?_⟩⟩
  change i.val < 2 * q - 1
  exact hi

/-- Least active vertex strictly after `i`. -/
def r322AnalyticSuccessorVertex
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (i : Fin (2 * q))
    (hi : i.val < 2 * q - 1) :
    Fin (2 * q) :=
  (r322AnalyticSuccessorCandidates state i).min'
    (r322AnalyticSuccessorCandidates_nonempty state i hi)

theorem r322AnalyticSuccessorVertex_mem_active
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (i : Fin (2 * q))
    (hi : i.val < 2 * q - 1) :
    r322AnalyticSuccessorVertex state i hi ∈ state.active := by
  have hmem :=
    Finset.min'_mem
      (r322AnalyticSuccessorCandidates state i)
      (r322AnalyticSuccessorCandidates_nonempty state i hi)
  exact (Finset.mem_filter.mp hmem).1

theorem r322AnalyticSuccessorVertex_gt
    {q : ℕ} {hq : 1 ≤ q}
    (state : R322AnalyticEdgeState q hq)
    (i : Fin (2 * q))
    (hi : i.val < 2 * q - 1) :
    i < r322AnalyticSuccessorVertex state i hi := by
  have hmem :=
    Finset.min'_mem
      (r322AnalyticSuccessorCandidates state i)
      (r322AnalyticSuccessorCandidates_nonempty state i hi)
  exact (Finset.mem_filter.mp hmem).2

namespace R322AnalyticProperStepContext

variable {q : ℕ} {hq : 1 ≤ q}
    (ctx : R322AnalyticProperStepContext q hq)

/-- The active successor immediately outside the right edge of this proper
block. -/
def successorVertex : Fin (2 * q) :=
  r322AnalyticSuccessorVertex ctx.state ctx.step.1.2 ctx.bounds.2

theorem successorVertex_mem_active :
    ctx.successorVertex ∈ ctx.state.active :=
  r322AnalyticSuccessorVertex_mem_active
    ctx.state ctx.step.1.2 ctx.bounds.2

theorem stepRight_lt_successorVertex :
    ctx.step.1.2 < ctx.successorVertex :=
  r322AnalyticSuccessorVertex_gt
    ctx.state ctx.step.1.2 ctx.bounds.2

/-- The chosen predecessor is outside the block being integrated. -/
theorem predecessorVertex_not_mem_step :
    r322AnalyticPredecessorVertex
        ctx.state ctx.step ctx.bounds.1 ∉
      ctx.step.2 := by
  rw [
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      ctx.pairing ctx.state.processed ctx.suffix
      ctx.step ctx.schedule_eq]
  intro hmem
  have hleft :=
    (Finset.mem_Icc.mp (Finset.mem_inter.mp hmem).2).1
  have hpred :=
    r322AnalyticPredecessorVertex_lt_left
      ctx.state ctx.step ctx.bounds.1
  exact (not_lt_of_ge hleft) hpred

/-- The active successor is likewise outside the block. -/
theorem successorVertex_not_mem_step :
    ctx.successorVertex ∉ ctx.step.2 := by
  rw [
    r322AnalyticSchedule_step_block_eq_activeCarrier_inter_Icc
      ctx.pairing ctx.state.processed ctx.suffix
      ctx.step ctx.schedule_eq]
  intro hmem
  have hright :=
    (Finset.mem_Icc.mp (Finset.mem_inter.mp hmem).2).2
  exact
    (not_lt_of_ge hright)
      ctx.stepRight_lt_successorVertex

/-- Ambient value at the sparse predecessor. -/
def predecessorPoint (x : Fin (2 * q) → T4) : T4 :=
  x (r322AnalyticPredecessorVertex
    ctx.state ctx.step ctx.bounds.1)

/-- Ambient value at the sparse successor. -/
def successorPoint (x : Fin (2 * q) → T4) : T4 :=
  x ctx.successorVertex

/-- Translate the actual standard block tuple so that its active successor
is at zero. -/
def translatedStandardBlockTuple
    (x : Fin (2 * q) → T4) :
    Fin (2 * residualBlockOrder ctx.step.2) → T4 :=
  fun j => ctx.standardBlockTuple x j - ctx.successorPoint x

/-- Put a relative standard block tuple back into the ambient coordinates,
using the actual active successor as translation anchor. -/
def reconstructRelativeBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    Fin (2 * q) → T4 :=
  ctx.reconstructBlockTuple base
    (fun j => t j + ctx.successorPoint base)

@[simp]
theorem standardBlockTuple_reconstructRelativeBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.standardBlockTuple
        (ctx.reconstructRelativeBlockTuple base t) =
      fun j => t j + ctx.successorPoint base := by
  unfold reconstructRelativeBlockTuple
  rw [ctx.standardBlockTuple_reconstructBlockTuple]

@[simp]
theorem predecessorPoint_reconstructRelativeBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.predecessorPoint
        (ctx.reconstructRelativeBlockTuple base t) =
      ctx.predecessorPoint base := by
  unfold predecessorPoint reconstructRelativeBlockTuple
    reconstructBlockTuple
  simp [ctx.predecessorVertex_not_mem_step]

@[simp]
theorem successorPoint_reconstructRelativeBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.successorPoint
        (ctx.reconstructRelativeBlockTuple base t) =
      ctx.successorPoint base := by
  unfold successorPoint reconstructRelativeBlockTuple
    reconstructBlockTuple
  simp [ctx.successorVertex_not_mem_step]

@[simp]
theorem translatedStandardBlockTuple_reconstructRelativeBlockTuple
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.translatedStandardBlockTuple
        (ctx.reconstructRelativeBlockTuple base t) =
      t := by
  funext j
  rw [translatedStandardBlockTuple,
    ctx.standardBlockTuple_reconstructRelativeBlockTuple,
    ctx.successorPoint_reconstructRelativeBlockTuple]
  simp

/-! ## The actual local factor on an ambient residual tuple -/

/-- The local factor read from an actual ambient residual tuple.

The incoming edge reads the sparse predecessor, the internal chain reads the
heterogeneous state edges, and the outgoing difference is anchored at the
least active successor.  Only the covariance sum of the current schedule
block occurs here; all factors from the remaining suffix belong to the outer
residual integrand. -/
def ambientLocalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) : ℝ :=
  ctx.state.edges ctx.predecessorEdge
      (ctx.predecessorPoint x -
        ctx.standardBlockTuple x
          ⟨0, by
            have hn := ctx.one_le_blockOrder
            omega⟩) *
    primitiveChainProduct
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (ctx.standardBlockTuple x) *
    (ctx.state.edges ctx.outgoingEdge
        (ctx.standardBlockTuple x
            (primitiveLast
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder) -
          ctx.successorPoint x) -
      ctx.state.edges ctx.outgoingEdge
        (ctx.standardBlockTuple x
            ⟨0, by
              have hn := ctx.one_le_blockOrder
              omega⟩ -
          ctx.successorPoint x)) *
    ∑ κB :
        {κ : PartialPairing
            (Fin (2 * residualBlockOrder ctx.step.2)) //
          κ ∈ primitiveFullPairings
            (residualBlockOrder ctx.step.2)},
      primitiveCovarianceProduct ρ ε
        (residualBlockOrder ctx.step.2) κB.1
        (ctx.standardBlockTuple x)

private theorem primitiveChainProduct_sub_const
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (x : Fin (2 * n) → T4) (a : T4) :
    primitiveChainProduct n hn G
        (fun i => x i - a) =
      primitiveChainProduct n hn G x := by
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j _hj
  apply congrArg (G j)
  change
    (x (primitiveEdgeLeft n hn j) - a) -
        (x (primitiveEdgeRight n hn j) - a) =
      x (primitiveEdgeLeft n hn j) -
        x (primitiveEdgeRight n hn j)
  abel

private theorem primitiveCovarianceProduct_sub_const
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) (a : T4) :
    primitiveCovarianceProduct ρ ε n κ
        (fun i => x i - a) =
      primitiveCovarianceProduct ρ ε n κ x := by
  unfold primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  apply congrArg (ρ.etaEpsT4 ε)
  change (x i - a) - (x (κ i) - a) = x i - x (κ i)
  abel

/-- Translation by the actual active successor recognizes the ambient local
factor as the exact raw local integrand consumed by the collapse theorem. -/
theorem ambientLocalIntegrand_eq_rawLocalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (x : Fin (2 * q) → T4) :
    ctx.ambientLocalIntegrand ρ ε x =
      ctx.rawLocalIntegrand ρ ε
        (ctx.predecessorPoint x - ctx.successorPoint x)
        (ctx.translatedStandardBlockTuple x) := by
  have hchain :
      primitiveChainProduct
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges
          (ctx.translatedStandardBlockTuple x) =
        primitiveChainProduct
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder ctx.internalEdges
          (ctx.standardBlockTuple x) := by
    exact primitiveChainProduct_sub_const
      (residualBlockOrder ctx.step.2)
      ctx.one_le_blockOrder ctx.internalEdges
      (ctx.standardBlockTuple x) (ctx.successorPoint x)
  have hcov :
      (∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1
          (ctx.translatedStandardBlockTuple x)) =
        ∑ κB :
          {κ : PartialPairing
              (Fin (2 * residualBlockOrder ctx.step.2)) //
            κ ∈ primitiveFullPairings
              (residualBlockOrder ctx.step.2)},
        primitiveCovarianceProduct ρ ε
          (residualBlockOrder ctx.step.2) κB.1
          (ctx.standardBlockTuple x) := by
    apply Finset.sum_congr rfl
    intro κB _hκB
    exact primitiveCovarianceProduct_sub_const
      ρ ε (residualBlockOrder ctx.step.2) κB.1
      (ctx.standardBlockTuple x) (ctx.successorPoint x)
  unfold ambientLocalIntegrand rawLocalIntegrand
  rw [hchain, hcov]
  unfold translatedStandardBlockTuple
  have hincoming :
      ctx.predecessorPoint x - ctx.successorPoint x -
          (ctx.standardBlockTuple x
            ⟨0, by
              have hn := ctx.one_le_blockOrder
              omega⟩ -
            ctx.successorPoint x) =
        ctx.predecessorPoint x -
          ctx.standardBlockTuple x
            ⟨0, by
              have hn := ctx.one_le_blockOrder
              omega⟩ := by
    abel
  rw [hincoming]

/-- On the translated ambient reconstruction, the actual local factor is
literally the raw local factor at the predecessor-successor displacement. -/
theorem ambientLocalIntegrand_reconstructRelativeBlockTuple
    (ρ : SmoothCutoff) (ε : ℝ)
    (base : Fin (2 * q) → T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.ambientLocalIntegrand ρ ε
        (ctx.reconstructRelativeBlockTuple base t) =
      ctx.rawLocalIntegrand ρ ε
        (ctx.predecessorPoint base - ctx.successorPoint base) t := by
  rw [ctx.ambientLocalIntegrand_eq_rawLocalIntegrand,
    ctx.predecessorPoint_reconstructRelativeBlockTuple,
    ctx.successorPoint_reconstructRelativeBlockTuple,
    ctx.translatedStandardBlockTuple_reconstructRelativeBlockTuple]

/-! ## Haar translation from actual to relative block coordinates -/

/-- Simultaneous translation of every standard block coordinate. -/
def residualBlockTranslation
    (a : T4) :
    (Fin (2 * residualBlockOrder ctx.step.2) → T4) ≃ᵐ
      (Fin (2 * residualBlockOrder ctx.step.2) → T4) :=
  MeasurableEquiv.piCongrRight fun _ =>
    MeasurableEquiv.addRight a

@[simp]
theorem residualBlockTranslation_apply
    (a : T4)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ctx.residualBlockTranslation a t =
      fun j => t j + a := by
  funext j
  rfl

/-- Product Haar measure is invariant under the simultaneous block
translation. -/
theorem measurePreserving_residualBlockTranslation
    (a : T4) :
    MeasurePreserving
      (ctx.residualBlockTranslation a)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure) := by
  change
    MeasurePreserving
      (fun t j => t j + a)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure)
      (Measure.pi fun _ :
        Fin (2 * residualBlockOrder ctx.step.2) =>
          paperMeasure)
  exact measurePreserving_pi
    (fun _ :
      Fin (2 * residualBlockOrder ctx.step.2) =>
        paperMeasure)
    (fun _ :
      Fin (2 * residualBlockOrder ctx.step.2) =>
        paperMeasure)
    (f := fun _ x => x + a) fun _j => by
      rw [paperMeasure_eq_volume]
      exact measurePreserving_add_right (volume : Measure T4) a

/-- The integral over actual block coordinates is exactly the integral over
coordinates relative to the active successor. -/
theorem integral_actualBlock_eq_relativeBlock
    (ρ : SmoothCutoff) (ε : ℝ)
    (base : Fin (2 * q) → T4) (outer : ℝ) :
    (∫ actual :
        Fin (2 * residualBlockOrder ctx.step.2) → T4,
      ctx.ambientLocalIntegrand ρ ε
          (ctx.reconstructBlockTuple base actual) *
        outer
      ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder ctx.step.2) → T4,
        ctx.ambientLocalIntegrand ρ ε
            (ctx.reconstructRelativeBlockTuple base t) *
          outer
        ∂Measure.pi fun _ => paperMeasure := by
  let f :
      (Fin (2 * residualBlockOrder ctx.step.2) → T4) → ℝ :=
    fun actual =>
      ctx.ambientLocalIntegrand ρ ε
          (ctx.reconstructBlockTuple base actual) *
        outer
  calc
    (∫ actual :
        Fin (2 * residualBlockOrder ctx.step.2) → T4,
        f actual
        ∂Measure.pi fun _ => paperMeasure) =
      ∫ t :
          Fin (2 * residualBlockOrder ctx.step.2) → T4,
        f (ctx.residualBlockTranslation
          (ctx.successorPoint base) t)
        ∂Measure.pi fun _ => paperMeasure := by
      exact
        (ctx.measurePreserving_residualBlockTranslation
          (ctx.successorPoint base)).integral_comp' f |>.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [ctx.residualBlockTranslation_apply]
      rfl

/-! ## One processed-prefix residual integral -/

/-- The genuine pre-collapse integrand for one processed-prefix step,
including an arbitrary factor depending only on the surviving outer
coordinates. -/
def processedResidualIntegrand
    (ρ : SmoothCutoff) (ε : ℝ)
    (base : Fin (2 * q) → T4)
    (outer : ℝ)
    (t : Fin (2 * residualBlockOrder ctx.step.2) → T4) :
    ℝ :=
  ctx.ambientLocalIntegrand ρ ε
      (ctx.reconstructRelativeBlockTuple base t) *
    outer

/-- The nested outer integral before one proper processed-prefix update. -/
def processedResidualOuterIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (base : Ω → Fin (2 * q) → T4)
    (outer : Ω → ℝ) : ℝ :=
  ∫ ω,
    lamEps lam ε ^
        (2 * residualBlockOrder ctx.step.2) *
      (∫ t :
          Fin (2 * residualBlockOrder ctx.step.2) → T4,
        ctx.processedResidualIntegrand ρ ε
          (base ω) (outer ω) t
        ∂Measure.pi fun _ => paperMeasure)
    ∂ν

/-- The residual outer integral after the local block has been absorbed into
the predecessor edge. -/
def updatedResidualOuterIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (base : Ω → Fin (2 * q) → T4)
    (outer : Ω → ℝ) : ℝ :=
  ∫ ω,
    (ctx.nextState ρ lam ε).edges ctx.predecessorEdge
        (ctx.predecessorPoint (base ω) -
          ctx.successorPoint (base ω)) *
      outer ω
    ∂ν

/-- **Iterable processed-prefix Fubini headline.**

One actual ambient block, reconstructed relative to its active successor, is
integrated out and replaced by exactly the predecessor edge of `nextState`.
The outer coordinate and its complete remaining factor are unchanged. -/
theorem processedResidualOuterIntegral_eq_updated
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (base : Ω → Fin (2 * q) → T4)
    (outer : Ω → ℝ)
    (hstandard :
      ∀ᵐ ω ∂ν,
        Integrable
          (ctx.localIntegrand ρ ε
            (ctx.predecessorPoint (base ω) -
              ctx.successorPoint (base ω)))
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
    ctx.processedResidualOuterIntegral ν ρ lam ε base outer =
      ctx.updatedResidualOuterIntegral ν ρ lam ε base outer := by
  unfold processedResidualOuterIntegral
    updatedResidualOuterIntegral processedResidualIntegrand
  have hstep :=
    ctx.integral_outer_rawLocalIntegrand_eq_nextState
      ν ρ lam ε
      (fun ω =>
        ctx.predecessorPoint (base ω) -
          ctx.successorPoint (base ω))
      outer hstandard hinternal
  calc
    (∫ ω,
        lamEps lam ε ^
            (2 * residualBlockOrder ctx.step.2) *
          (∫ t :
              Fin (2 * residualBlockOrder ctx.step.2) → T4,
            ctx.ambientLocalIntegrand ρ ε
                (ctx.reconstructRelativeBlockTuple
                  (base ω) t) *
              outer ω
            ∂Measure.pi fun _ => paperMeasure)
        ∂ν) =
      ∫ ω,
        lamEps lam ε ^
            (2 * residualBlockOrder ctx.step.2) *
          (∫ t :
              Fin (2 * residualBlockOrder ctx.step.2) → T4,
            ctx.rawLocalIntegrand ρ ε
                (ctx.predecessorPoint (base ω) -
                  ctx.successorPoint (base ω)) t *
              outer ω
            ∂Measure.pi fun _ => paperMeasure)
        ∂ν := by
      apply integral_congr_ae
      filter_upwards with ω
      apply congrArg
        (fun a : ℝ =>
          lamEps lam ε ^
              (2 * residualBlockOrder ctx.step.2) * a)
      apply integral_congr_ae
      filter_upwards with t
      rw [ctx.ambientLocalIntegrand_reconstructRelativeBlockTuple]
    _ = _ := hstep

end R322AnalyticProperStepContext

/-! ## Connection to the actual endpoint fibre at the initial state -/

/-- The initial residual integrand is the exact analytic-head local factor
times the complete suffix factor.  At the initial state the active carrier is
all vertices and every state edge is `greenFn`. -/
def r322InitialResidualIntegrand
    {q : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (x : Fin (2 * q) → T4) : ℝ :=
  r322AnalyticHeadLocalIntegrandFactor
      ρ ε κ head tail hschedule x *
    r322AnalyticHeadOuterIntegrandFactor
      ρ ε κ head tail hschedule x

/-- The initial residual integrand is pointwise the actual endpoint-fibre
sum, not a model integrand. -/
theorem sum_endpointFiber_detJintegrand_eq_initialResidualIntegrand
    {q : ℕ}
    (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (x : Fin (2 * q) → T4) :
    (∑ τ : ReductionEndpointFiberAt κ,
        detJintegrand ρ ε q τ.1 x) =
      r322InitialResidualIntegrand
        ρ ε κ head tail hschedule x := by
  unfold r322InitialResidualIntegrand
  exact
    sum_endpointFiber_detJintegrand_eq_analyticHead_mul_outer
      ρ ε κ (mem_nonSplitPairings.mp hκ).1
      head tail hschedule x

/-- Initial outer integral in standard coordinates for the first scheduled
proper block.  This is the residual object before any analytic absorption. -/
def r322InitialResidualOuterIntegral
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4) : ℝ :=
  lamEps lam ε ^ (2 * q) *
    ∫ vC :
        {i : Fin (2 * q - 2) //
          ¬r322SelectedFinPredicate
            (r322InternalCoordinatesOfBlock
              q hq head.2) i} → T4,
      ∫ t : Fin (2 * residualBlockOrder head.2) → T4,
        r322InitialResidualIntegrand
          ρ ε κ head tail hschedule
          (r322AnalyticProperHeadReconstruct
            hq κ hκ head tail hschedule hproper z vC t)
        ∂Measure.pi fun _ => paperMeasure
      ∂Measure.pi fun _ => paperMeasure

/-- **Actual-fibre initial headline.**  Spatial Fubini and the
measure-preserving block reindex identify `endpointFiberDetJSum` with the
initial processed residual outer integral. -/
theorem endpointFiberDetJSum_eq_initialResidualOuterIntegral
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (head : R322ExtractionStep (2 * q))
    (tail : List (R322ExtractionStep (2 * q)))
    (hschedule :
      r322AnalyticSchedule κ = head :: tail)
    (hproper :
      head.1 ≠ r322WholeEndpoint q hq)
    (z : T4)
    (hint :
      ∀ τ : ReductionEndpointFiberAt κ,
        Integrable
          (fun v : Fin (2 * q - 2) → T4 =>
            detJintegrand ρ ε q τ.1
              (primitiveAssemble q hq z 0 v))
          (Measure.pi fun _ => paperMeasure)) :
    endpointFiberDetJSum ρ lam ε q
        (reductionEndpointSignature κ) z =
      r322InitialResidualOuterIntegral
        hq ρ lam ε κ hκ head tail hschedule hproper z := by
  rw [
    endpointFiberDetJSum_eq_analyticStepSpatialFubini
      ρ lam ε hq κ hκ head
      (by rw [hschedule]; simp) z hint]
  unfold r322InitialResidualOuterIntegral
  apply congrArg
    (fun a : ℝ => lamEps lam ε ^ (2 * q) * a)
  apply integral_congr_ae
  filter_upwards with vC
  rw [
    integral_r322AnalyticProperHeadSelected_eq_standardBlock
      hq κ hκ head tail hschedule hproper]
  apply integral_congr_ae
  filter_upwards with t
  rw [
    r322AnalyticProperHeadSelectedTupleMeasurableEquiv_eq_plain
      hq κ hκ head tail hschedule hproper]
  exact
    sum_endpointFiber_detJintegrand_eq_initialResidualIntegrand
      ρ ε κ hκ head tail hschedule
      (r322AnalyticProperHeadReconstruct
        hq κ hκ head tail hschedule hproper z vC t)

end

end Anderson4D
