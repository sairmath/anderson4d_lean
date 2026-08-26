import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualStep
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticPrimitiveCertificate
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticCollapseIntegrability
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticReachableIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedCollapseClosure

/-!
# Quantitative one-block closure for an R-324 within-half suffix

This file supplies the analytic counterpart of the exact residual transport:
every genuine schedule head is estimated by Proposition 4.1, its predecessor
edge scale is updated once, and the resulting certificate is carried through
the literal remaining suffix.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Future outgoing slots remain free Green edges -/

theorem r324WithinHalfPredecessorSlot_val_le_step_left
    {m : ℕ} (state : R324WithinHalfEdgeState m)
    (step : R322ExtractionStep m) :
    (r324WithinHalfPredecessorSlot state step).val ≤
      step.1.1.val := by
  have hp :=
    r324WithinHalfPredecessorSlot_mem state step
  rw [r324WithinHalfPredecessorCandidates] at hp
  rcases Finset.mem_union.mp hp with hzero | hinter
  · have heq :
        r324WithinHalfPredecessorSlot state step = 0 := by
      simpa using hzero
    rw [heq]
    exact Nat.zero_le _
  · obtain ⟨i, hi, heq⟩ :=
      Finset.mem_image.mp hinter
    have hlt := (Finset.mem_filter.mp hi).2
    have hval := congrArg Fin.val heq
    simp only [r324InternalVertexEdgeSlot] at hval
    change i.val < step.1.1.val at hlt
    omega

namespace R324WithinHalfStateReachable

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- An edge strictly to the right of every processed block is untouched by
the genuine within-half collapse recursion. -/
theorem edge_eq_greenFn_of_processed_right_lt
    {state : R324WithinHalfEdgeState m}
    (hstate :
      R324WithinHalfStateReachable pairing ρ lam ε state)
    (edge : Fin (m + 1))
    (hfuture :
      ∀ earlier ∈ state.processed,
        earlier.1.2.val < edge.val) :
    state.edges edge = greenFn := by
  induction hstate with
  | initial =>
      rfl
  | absorb ctx hctx ih =>
      have hcurrent :
          ctx.step.1.2.val < edge.val := by
        apply hfuture ctx.step
        simp [R324WithinHalfStepContext.absorb]
      have hprevious :
          ∀ earlier ∈ ctx.state.processed,
            earlier.1.2.val < edge.val := by
        intro earlier hearlier
        apply hfuture earlier
        simp [R324WithinHalfStepContext.absorb, hearlier]
      have hleftRight :
          ctx.step.1.1.val ≤ ctx.step.1.2.val := by
        have haligned :=
          r322AnalyticSchedule_forall_aligned
            pairing ctx.step ctx.step_mem_schedule
        exact Fin.mk_le_mk.mp
          ((haligned.2.2 ctx.step.1.1 haligned.1).2)
      have hne :
          edge ≠
            r324WithinHalfPredecessorSlot
              ctx.state ctx.step := by
        intro heq
        have hp :=
          r324WithinHalfPredecessorSlot_val_le_step_left
            ctx.state ctx.step
        have hval := congrArg Fin.val heq
        omega
      rw [ctx.absorb_edges_of_ne ρ lam ε edge hne]
      exact ih hprevious

end R324WithinHalfStateReachable

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)

/-- The outgoing edge of the literal remaining head has not yet been
updated, so the actual R-324 collapse uses the free Green function there. -/
theorem state_edges_head_outgoing_eq_greenFn
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail) :
    res.state.edges
        (r324InternalVertexEdgeSlot head.1.2) =
      greenFn := by
  apply
    res.reachable.edge_eq_greenFn_of_processed_right_lt
  intro earlier hearlier
  have hp :=
    r322AnalyticSchedule_pairwise_right_lt pairing
  rw [res.schedule_eq, hremaining,
    List.pairwise_append] at hp
  have hright :
      earlier.1.2 < head.1.2 :=
    hp.2.2 earlier hearlier head (by simp)
  unfold r324InternalVertexEdgeSlot
  change earlier.1.2.val < head.1.2.val + 1
  omega

end R324WithinHalfResidualPrefix

/-! ## Slotwise quantitative certificates -/

/-- Every named edge is measurable, belongs to the paper's symmetry class,
and is controlled off the identity by its own positive inverse-square scale.
-/
structure R324WithinHalfEdgeCertificate
    {m : ℕ} (state : R324WithinHalfEdgeState m)
    (scale : Fin (m + 1) → ℝ) : Prop where
  scale_pos : ∀ edge, 0 < scale edge
  measurable : ∀ edge, Measurable (state.edges edge)
  memE : ∀ edge, MemEClassT4 (state.edges edge)
  bound : ∀ edge z, z ≠ 0 →
    |state.edges edge z| ≤ scale edge * invSqKer z

/-- The all-Green initial state has a uniform quantitative certificate. -/
theorem exists_r324InitialWithinHalfEdgeCertificate
    (m : ℕ) :
    ∃ A : ℝ, 0 < A ∧
      R324WithinHalfEdgeCertificate
        (r324InitialWithinHalfEdgeState m)
        (fun _ => A) := by
  obtain ⟨A, hA, hgreen⟩ := greenFn_le
  refine ⟨A, hA, ⟨fun _ => hA, ?_, ?_, ?_⟩⟩
  · intro edge
    simpa [r324InitialWithinHalfEdgeState] using measurable_greenFn
  · intro edge
    simpa [r324InitialWithinHalfEdgeState] using greenFn_memE
  · intro edge z hz
    change |greenFn z| ≤ A * invSqKer z
    exact greenFn_abs_le_mul_invSqKer hgreen z hz

/-- Product of all current named scales used by the literal head primitive.
-/
def r324WithinHalfInternalEdgeScaleProduct
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)
    (scale : Fin (m + 1) → ℝ) : ℝ :=
  ∏ j : Fin (2 * residualBlockOrder ctx.step.2 - 1),
    scale (ctx.internalSlot j)

theorem R324WithinHalfEdgeCertificate.internalEdgeScaleProduct_pos
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {ctx : R324WithinHalfStepContext pairing}
    {scale : Fin (m + 1) → ℝ}
    (hcert :
      R324WithinHalfEdgeCertificate ctx.state scale) :
    0 < r324WithinHalfInternalEdgeScaleProduct ctx scale := by
  unfold r324WithinHalfInternalEdgeScaleProduct
  exact Finset.prod_pos
    fun j _ => hcert.scale_pos (ctx.internalSlot j)

/-- Exact local scale ledger for one actual within-half head collapse. -/
def r324WithinHalfUpdatedEdgeScale
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ) : Fin (m + 1) → ℝ :=
  Function.update scale
    (r324WithinHalfPredecessorSlot ctx.state ctx.step)
    (scale (r324WithinHalfPredecessorSlot ctx.state ctx.step) *
      r324WithinHalfInternalEdgeScaleProduct ctx scale *
      (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K)

@[simp]
theorem r324WithinHalfUpdatedEdgeScale_predecessor
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ) :
    r324WithinHalfUpdatedEdgeScale ctx scale C lam K
        (r324WithinHalfPredecessorSlot ctx.state ctx.step) =
      scale (r324WithinHalfPredecessorSlot ctx.state ctx.step) *
        r324WithinHalfInternalEdgeScaleProduct ctx scale *
        (C * lam) ^ (2 * residualBlockOrder ctx.step.2) * K := by
  simp [r324WithinHalfUpdatedEdgeScale]

theorem r324WithinHalfUpdatedEdgeScale_of_ne
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)
    (scale : Fin (m + 1) → ℝ)
    (C lam K : ℝ) (edge : Fin (m + 1))
    (hne :
      edge ≠
        r324WithinHalfPredecessorSlot ctx.state ctx.step) :
    r324WithinHalfUpdatedEdgeScale ctx scale C lam K edge =
      scale edge := by
  simp [r324WithinHalfUpdatedEdgeScale, hne]

/-! ## One genuine Proposition 4.1 block estimate -/

/-- The local analytic data derived for the primitive kernel of one literal
schedule head.  Its scale is the product of the current internal edge scales;
integrability is for the exact three-kernel collapse with free Green outgoing
edge. -/
structure R324WithinHalfPrimitiveCertificate
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (ctx : R324WithinHalfStepContext pairing)
    (scale : Fin (m + 1) → ℝ)
    (ρ : SmoothCutoff)
    (C lam ε supportConstant : ℝ) : Prop where
  measurable : Measurable (ctx.primitiveKernel ρ lam ε)
  memE : MemEClassT4 (ctx.primitiveKernel ρ lam ε)
  bound : ∀ u, u ≠ 0 →
    |ctx.primitiveKernel ρ lam ε u| ≤
      r324WithinHalfInternalEdgeScaleProduct ctx scale *
        primitiveKernelMajorant C lam ε supportConstant
          (residualBlockOrder ctx.step.2) u
  integrable : ∀ x, x ≠ 0 →
    Integrable
      (r322CollapseIntegrand
        (ctx.state.edges
          (r324WithinHalfPredecessorSlot ctx.state ctx.step))
        (ctx.primitiveKernel ρ lam ε)
        greenFn x)
      (paperMeasure.prod paperMeasure)

/-- The current slotwise certificate and Proposition 4.1 produce the full
local primitive certificate.  In particular, raw integrability is derived
from the inverse-square convolution majorant, rather than stored globally. -/
theorem R324WithinHalfEdgeCertificate.primitiveCertificate
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {ctx : R324WithinHalfStepContext pairing}
    {scale : Fin (m + 1) → ℝ}
    (hcert :
      R324WithinHalfEdgeCertificate ctx.state scale)
    (ρ : SmoothCutoff)
    (C lam ε supportConstant : ℝ)
    (hε : 0 < ε)
    (hlog : 0 < |Real.log ε|)
    (hprop :
      ∀ (H :
          Fin (2 * residualBlockOrder ctx.step.2 - 1) →
            T4 → ℝ),
        IsAdmissiblePrimitiveInput
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
              ctx.one_le_blockOrder H supportConstant C) :
    R324WithinHalfPrimitiveCertificate
      ctx scale ρ C lam ε supportConstant := by
  let J : T4 → ℝ := ctx.primitiveKernel ρ lam ε
  let Jscale : ℝ :=
    r324WithinHalfInternalEdgeScaleProduct ctx scale
  have hJscale : 0 < Jscale :=
    hcert.internalEdgeScaleProduct_pos
  have hJmeas : Measurable J := by
    dsimp only [J]
    unfold R324WithinHalfStepContext.primitiveKernel
    exact
      measurable_primitiveKernelDiff
        ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder
        ctx.internalEdges
        (fun j => hcert.measurable (ctx.internalSlot j))
  have hJmem : MemEClassT4 J := by
    dsimp only [J]
    unfold R324WithinHalfStepContext.primitiveKernel
    exact
      primitiveKernelDiff_memE
        ρ lam ε
        (residualBlockOrder ctx.step.2)
        ctx.one_le_blockOrder
        ctx.internalEdges
        (fun j => hcert.memE (ctx.internalSlot j))
  have hJbound :
      ∀ z, z ≠ 0 →
        |J z| ≤ Jscale *
          primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder ctx.step.2) z := by
    intro z hz
    dsimp only [J, Jscale]
    simpa [
      R324WithinHalfStepContext.primitiveKernel,
      R324WithinHalfStepContext.internalEdges,
      r324WithinHalfInternalEdgeScaleProduct] using
      primitiveKernelDiff_le_prod_edgeScales_mul_majorant_offDiagonal
        ρ ctx.one_le_blockOrder ctx.internalEdges
        (fun j => scale (ctx.internalSlot j))
        (fun j => hcert.scale_pos (ctx.internalSlot j))
        (fun j => hcert.memE (ctx.internalSlot j))
        (fun j => hcert.bound (ctx.internalSlot j))
        hprop z hz
  obtain ⟨B, hB, hmajor⟩ :=
    exists_primitiveKernelMajorant_le_invSq_add_one
      C lam ε supportConstant
      (residualBlockOrder ctx.step.2) hε hlog
  obtain ⟨Cgreen, hCgreen, hgreen⟩ := greenFn_le
  have hJinv :
      ∀ z, z ≠ 0 →
        |J z| ≤
          (Jscale * B) * (invSqKer z + 1) := by
    intro z hz
    calc
      |J z| ≤ Jscale *
          primitiveKernelMajorant C lam ε supportConstant
            (residualBlockOrder ctx.step.2) z :=
        hJbound z hz
      _ ≤ Jscale * (B * (invSqKer z + 1)) :=
        mul_le_mul_of_nonneg_left (hmajor z) hJscale.le
      _ = (Jscale * B) * (invSqKer z + 1) := by
        ring
  refine ⟨hJmeas, hJmem, hJbound, ?_⟩
  intro x hx
  exact
    integrable_r322CollapseIntegrand_of_invSq_add_one
      (hcert.measurable
        (r324WithinHalfPredecessorSlot ctx.state ctx.step))
      hJmeas
      (hcert.scale_pos
        (r324WithinHalfPredecessorSlot ctx.state ctx.step)).le
      (mul_nonneg hJscale.le hB)
      hCgreen.le
      (hcert.bound
        (r324WithinHalfPredecessorSlot ctx.state ctx.step))
      hJinv
      (fun z hz =>
        greenFn_abs_le_mul_invSqKer hgreen z hz)
      hx

/-- **Local block inequality and certificate transport.**

The universal constant comes from the one-block Proposition 4.1 collapse
estimate.  For each literal schedule head, the first conjunct is the exact
predecessor-edge inequality; the second conjunct transports the complete
slotwise certificate to `afterHead`. -/
theorem exists_r324WithinHalf_localBlockClosure
    {supportConstant : ℝ}
    (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : SmoothCutoff) (C lam ε : ℝ)
        (m : ℕ) (pairing : PartialPairing (Fin m))
        (res :
          R324WithinHalfResidualPrefix ρ lam ε pairing)
        (head : R322ExtractionStep m)
        (tail : List (R322ExtractionStep m))
        (hremaining : res.remaining = head :: tail)
        (scale : Fin (m + 1) → ℝ),
        R324WithinHalfEdgeCertificate res.state scale →
        0 < C → 0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        (∀ (H :
            Fin (2 * residualBlockOrder head.2 - 1) →
              T4 → ℝ),
          IsAdmissiblePrimitiveInput
              (residualBlockOrder head.2) H →
            MemEClassT4
                (primitiveKernelDiff ρ lam ε
                  (residualBlockOrder head.2)
                  (res.headContext
                    head tail hremaining).one_le_blockOrder H) ∧
              MemEClassT4
                (primitiveKernelInsertedDiff ρ lam ε
                  (residualBlockOrder head.2)
                  (res.headContext
                    head tail hremaining).one_le_blockOrder H) ∧
              PrimitiveKernelBounds ρ lam ε
                (residualBlockOrder head.2)
                (res.headContext
                  head tail hremaining).one_le_blockOrder
                H supportConstant C) →
        (∀ x, x ≠ 0 →
          |(res.afterHead
              head tail hremaining).state.edges
              (r324WithinHalfPredecessorSlot
                res.state head) x| ≤
            r324WithinHalfUpdatedEdgeScale
                (res.headContext head tail hremaining)
                scale C lam K
                (r324WithinHalfPredecessorSlot
                  res.state head) *
              invSqKer x) ∧
          R324WithinHalfEdgeCertificate
            (res.afterHead head tail hremaining).state
            (r324WithinHalfUpdatedEdgeScale
              (res.headContext head tail hremaining)
              scale C lam K) := by
  obtain ⟨K, hK, hstep⟩ :=
    exists_r322Collapse_le_scaled_middle_offDiagonal hsupport
  refine ⟨K, hK, ?_⟩
  intro ρ C lam ε m pairing res head tail hremaining scale
    hcert hC hlam hε hε1 hlog hprop
  let ctx :=
    res.headContext head tail hremaining
  have hprimitive :
      R324WithinHalfPrimitiveCertificate
        ctx scale ρ C lam ε supportConstant := by
    apply hcert.primitiveCertificate
      ρ C lam ε supportConstant hε
      (lt_of_lt_of_le zero_lt_one hlog)
    intro H hH
    exact hprop H hH
  have hout :
      ctx.state.edges ctx.outgoingSlot = greenFn := by
    change
      res.state.edges
          (r324InternalVertexEdgeSlot head.1.2) =
        greenFn
    exact
      res.state_edges_head_outgoing_eq_greenFn
          head tail hremaining
  have hpred :
      ∀ x, x ≠ 0 →
        |(res.afterHead
            head tail hremaining).state.edges
            (r324WithinHalfPredecessorSlot res.state head) x| ≤
          r324WithinHalfUpdatedEdgeScale
              ctx scale C lam K
              (r324WithinHalfPredecessorSlot res.state head) *
            invSqKer x := by
    intro x hx
    rw [res.afterHead_state head tail hremaining]
    change
      |(ctx.absorb ρ lam ε).edges
          (r324WithinHalfPredecessorSlot
            ctx.state ctx.step) x| ≤
        r324WithinHalfUpdatedEdgeScale
            ctx scale C lam K
            (r324WithinHalfPredecessorSlot
              ctx.state ctx.step) *
          invSqKer x
    rw [ctx.absorb_edges_predecessor]
    unfold R324WithinHalfStepContext.collapsedKernel
    rw [hout]
    rw [r324WithinHalfUpdatedEdgeScale_predecessor]
    exact
      hstep C lam ε
        (scale
          (r324WithinHalfPredecessorSlot res.state head))
        (r324WithinHalfInternalEdgeScaleProduct ctx scale)
        (residualBlockOrder head.2)
        (res.state.edges
          (r324WithinHalfPredecessorSlot res.state head))
        (ctx.primitiveKernel ρ lam ε)
        x hC.le hlam.le
        (hcert.scale_pos
          (r324WithinHalfPredecessorSlot res.state head)).le
        hcert.internalEdgeScaleProduct_pos
        hε hε1 hlog hx
        hprimitive.measurable hprimitive.memE
        hprimitive.bound
        (hcert.bound
          (r324WithinHalfPredecessorSlot res.state head))
        (hprimitive.integrable x hx)
  refine ⟨hpred, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro edge
    by_cases hedge :
        edge =
          r324WithinHalfPredecessorSlot res.state head
    · subst edge
      change
        0 <
          r324WithinHalfUpdatedEdgeScale
            ctx scale C lam K
            (r324WithinHalfPredecessorSlot
              ctx.state ctx.step)
      rw [r324WithinHalfUpdatedEdgeScale_predecessor]
      exact
        mul_pos
          (mul_pos
            (mul_pos
              (hcert.scale_pos _)
              hcert.internalEdgeScaleProduct_pos)
            (pow_pos (mul_pos hC hlam) _))
          hK
    · rw [r324WithinHalfUpdatedEdgeScale_of_ne
        ctx scale C lam K edge hedge]
      exact hcert.scale_pos edge
  · intro edge
    by_cases hedge :
        edge =
          r324WithinHalfPredecessorSlot res.state head
    · subst edge
      rw [res.afterHead_state head tail hremaining]
      change
        Measurable
          ((ctx.absorb ρ lam ε).edges
            (r324WithinHalfPredecessorSlot
              ctx.state ctx.step))
      rw [ctx.absorb_edges_predecessor]
      unfold R324WithinHalfStepContext.collapsedKernel
      exact measurable_r322Collapse
        (hcert.measurable _) hprimitive.measurable
        (hcert.measurable _)
    · rw [res.afterHead_state head tail hremaining]
      rw [ctx.absorb_edges_of_ne ρ lam ε edge hedge]
      exact hcert.measurable edge
  · intro edge
    by_cases hedge :
        edge =
          r324WithinHalfPredecessorSlot res.state head
    · subst edge
      rw [res.afterHead_state head tail hremaining]
      change
        MemEClassT4
          ((ctx.absorb ρ lam ε).edges
            (r324WithinHalfPredecessorSlot
              ctx.state ctx.step))
      rw [ctx.absorb_edges_predecessor]
      unfold R324WithinHalfStepContext.collapsedKernel
      exact r322Collapse_memE
        (hcert.memE _) hprimitive.memE (hcert.memE _)
    · rw [res.afterHead_state head tail hremaining]
      rw [ctx.absorb_edges_of_ne ρ lam ε edge hedge]
      exact hcert.memE edge
  · intro edge z hz
    by_cases hedge :
        edge =
          r324WithinHalfPredecessorSlot res.state head
    · subst edge
      exact hpred z hz
    · rw [res.afterHead_state head tail hremaining]
      rw [ctx.absorb_edges_of_ne ρ lam ε edge hedge]
      rw [r324WithinHalfUpdatedEdgeScale_of_ne
        ctx scale C lam K edge hedge]
      exact hcert.bound edge z hz

/-! ## Literal suffix induction -/

/-- Proposition 4.1 evidence at every literal head that can occur during the
within-half suffix recursion.  This is a family of local block estimates,
not a global moment bound. -/
def R324WithinHalfProp41Provider
    (ρ : SmoothCutoff)
    (C lam ε supportConstant : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) : Prop :=
  ∀ (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (H :
      Fin (2 * residualBlockOrder head.2 - 1) →
        T4 → ℝ),
    IsAdmissiblePrimitiveInput
        (residualBlockOrder head.2) H →
      MemEClassT4
          (primitiveKernelDiff ρ lam ε
            (residualBlockOrder head.2)
            (res.headContext
              head tail hremaining).one_le_blockOrder H) ∧
        MemEClassT4
          (primitiveKernelInsertedDiff ρ lam ε
            (residualBlockOrder head.2)
            (res.headContext
              head tail hremaining).one_le_blockOrder H) ∧
        PrimitiveKernelBounds ρ lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          H supportConstant C

/-- A provider of one certified scale update at every nonempty literal
suffix.  Its first output is the actual local pointwise block inequality. -/
def R324WithinHalfLocalBlockProvider
    (ρ : SmoothCutoff) (C lam ε K : ℝ)
    {m : ℕ} (pairing : PartialPairing (Fin m)) : Prop :=
  ∀ (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)
    (scale : Fin (m + 1) → ℝ),
    R324WithinHalfEdgeCertificate res.state scale →
      (∀ x, x ≠ 0 →
        |(res.afterHead
            head tail hremaining).state.edges
            (r324WithinHalfPredecessorSlot
              res.state head) x| ≤
          r324WithinHalfUpdatedEdgeScale
              (res.headContext head tail hremaining)
              scale C lam K
              (r324WithinHalfPredecessorSlot
                res.state head) *
            invSqKer x) ∧
        R324WithinHalfEdgeCertificate
          (res.afterHead head tail hremaining).state
          (r324WithinHalfUpdatedEdgeScale
            (res.headContext head tail hremaining)
            scale C lam K)

/-- A proof-relevant trace records every genuine local inequality and exact
scale update through the remaining list. -/
inductive R324WithinHalfQuantitativeIterationReady
    {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)} :
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing) →
    (Fin (m + 1) → ℝ) → Prop
  | terminal
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (scale : Fin (m + 1) → ℝ)
      (hremaining : res.remaining = [])
      (certificate :
        R324WithinHalfEdgeCertificate res.state scale) :
      R324WithinHalfQuantitativeIterationReady res scale
  | step
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (head : R322ExtractionStep m)
      (tail : List (R322ExtractionStep m))
      (hremaining : res.remaining = head :: tail)
      (scale : Fin (m + 1) → ℝ)
      (certificate :
        R324WithinHalfEdgeCertificate res.state scale)
      (localBound :
        ∀ x, x ≠ 0 →
          |(res.afterHead
              head tail hremaining).state.edges
              (r324WithinHalfPredecessorSlot
                res.state head) x| ≤
            r324WithinHalfUpdatedEdgeScale
                (res.headContext head tail hremaining)
                scale C lam K
                (r324WithinHalfPredecessorSlot
                  res.state head) *
              invSqKer x)
      (next :
        R324WithinHalfQuantitativeIterationReady
          (C := C) (lam := lam) (K := K)
          (res.afterHead head tail hremaining)
          (r324WithinHalfUpdatedEdgeScale
            (res.headContext head tail hremaining)
            scale C lam K)) :
      R324WithinHalfQuantitativeIterationReady res scale

/-- Structural recursion on the literal remaining suffix constructs the
complete quantitative trace from local block closure. -/
theorem R324WithinHalfQuantitativeIterationReady.of_provider
    {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)
    (scale : Fin (m + 1) → ℝ)
    (certificate :
      R324WithinHalfEdgeCertificate res.state scale) :
    R324WithinHalfQuantitativeIterationReady
      (C := C) (lam := lam) (K := K) res scale := by
  cases hremaining : res.remaining with
  | nil =>
      exact
        R324WithinHalfQuantitativeIterationReady.terminal
          res scale hremaining certificate
  | cons head tail =>
      obtain ⟨hlocal, hnextCertificate⟩ :=
        provider res head tail hremaining scale certificate
      exact
        R324WithinHalfQuantitativeIterationReady.step
          res head tail hremaining scale certificate
          hlocal
          (R324WithinHalfQuantitativeIterationReady.of_provider
            provider
            (res.afterHead head tail hremaining)
            (r324WithinHalfUpdatedEdgeScale
              (res.headContext head tail hremaining)
              scale C lam K)
            hnextCertificate)
termination_by res.remaining.length
decreasing_by simp [hremaining]

/-- A complete local trace reaches the literal empty suffix and leaves a
certified terminal state whose processed list is the whole analytic
schedule. -/
theorem
    R324WithinHalfQuantitativeIterationReady.exists_terminal_certificate
    {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (ready :
      R324WithinHalfQuantitativeIterationReady
        (C := C) (lam := lam) (K := K) res scale) :
    ∃ (terminal :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (terminalScale : Fin (m + 1) → ℝ),
      terminal.remaining = [] ∧
        terminal.state.processed =
          r322AnalyticSchedule pairing ∧
        R324WithinHalfEdgeCertificate
          terminal.state terminalScale := by
  induction ready with
  | terminal terminal terminalScale hremaining certificate =>
      refine
        ⟨terminal, terminalScale, hremaining, ?_,
          certificate⟩
      have hschedule := terminal.schedule_eq
      rw [hremaining, List.append_nil] at hschedule
      exact hschedule.symm
  | step _res _head _tail _hremaining _scale
      _certificate _localBound _next ih =>
      exact ih

/-- Phase-A quantitative closure: Proposition 4.1 is applied locally at
every block and then iterated through the literal suffix.  The conclusion is
only a terminal slotwise certificate; no target-shaped global moment bound
is assumed. -/
theorem exists_r324WithinHalf_terminalCertificate_of_prop41
    {supportConstant : ℝ}
    (hsupport : 0 < supportConstant) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (ρ : SmoothCutoff) (C lam ε : ℝ)
        (m : ℕ) (pairing : PartialPairing (Fin m)),
        0 < C → 0 < lam → 0 < ε → ε ≤ 1 →
        1 ≤ |Real.log ε| →
        R324WithinHalfProp41Provider
          ρ C lam ε supportConstant pairing →
        ∀ (res :
            R324WithinHalfResidualPrefix ρ lam ε pairing)
          (scale : Fin (m + 1) → ℝ),
          R324WithinHalfEdgeCertificate res.state scale →
            ∃ (terminal :
                R324WithinHalfResidualPrefix
                  ρ lam ε pairing)
              (terminalScale : Fin (m + 1) → ℝ),
              terminal.remaining = [] ∧
                terminal.state.processed =
                  r322AnalyticSchedule pairing ∧
                R324WithinHalfEdgeCertificate
                  terminal.state terminalScale := by
  obtain ⟨K, hK, hlocal⟩ :=
    exists_r324WithinHalf_localBlockClosure hsupport
  refine ⟨K, hK, ?_⟩
  intro ρ C lam ε m pairing hC hlam hε hε1 hlog
    hprop res scale hcert
  have provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing := by
    intro current head tail hremaining currentScale
      currentCertificate
    exact
      hlocal ρ C lam ε m pairing
        current head tail hremaining currentScale
        currentCertificate hC hlam hε hε1 hlog
        (fun H hH =>
          hprop current head tail hremaining H hH)
  exact
    (R324WithinHalfQuantitativeIterationReady.of_provider
      provider res scale hcert).exists_terminal_certificate

end

end Anderson4D
