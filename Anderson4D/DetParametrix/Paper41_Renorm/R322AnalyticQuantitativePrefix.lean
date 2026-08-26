import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticCollapseIntegrability
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticBudgetScaleInvariant
import Anderson4D.DetParametrix.Paper41_Renorm.R322ReductionClosure

/-!
# Quantitative reachability along the genuine R-322 proper prefix

The qualitative sparse-carrier history and its numerical edge budget are
advanced together.  At each proper step the primitive certificate is built
from Proposition 4.1 and the current edge certificate; in particular, its
fixed-endpoint integrability field is proved before the one-block estimate is
applied.  The analytic output is then enlarged to the complete deleted-block
budget using the invariant value of the future outgoing Green scale.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

/-- Complete qualitative and quantitative data carried by one genuine
proper prefix of the production R-322 schedule. -/
structure R322AnalyticQuantitativePrefixData
    {q : ℕ} (hq : 1 ≤ q)
    (ρ : SmoothCutoff) (C lam ε K A : ℝ)
    (κ : PartialPairing (Fin (2 * q)))
    (hκ : κ ∈ nonSplitPairings q)
    (pre : List (R322ExtractionStep (2 * q))) where
  state : R322AnalyticEdgeState q hq
  scale : Fin (2 * q - 1) → ℝ
  absorbed :
    R322AnalyticAbsorbedState
      ρ lam ε hq κ hκ state
  processed : state.processed = pre
  budgetReachable :
    R322AnalyticBudgetScaleReachable
      hq ρ C lam ε K A κ hκ state scale
  edgeCertificate :
    R322AnalyticEdgeCertificate state scale

/-- Proposition 4.1 and the one-block theorem provide constants, chosen
before the coupling, mollification scale, perturbative order, pairing, and
proper prefix, for which every genuine proper prefix has a simultaneous
absorbed-state, budget-reachability, and slotwise edge certificate.

The initial Green scale is chosen once for every perturbative order and is
normalized by `1 ≤ A`.  Thus `A`, the Proposition 4.1 constant `C`, and the
one-block constant `K` are all uniform over `q` and the whole prefix. -/
theorem exists_r322AnalyticQuantitativePrefixData
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
        (pre suffix : List (R322ExtractionStep (2 * q))),
        0 < lam →
        0 < ε →
        ε ≤ 1 →
        1 ≤ |Real.log ε| →
        q ≤ truncOrder ε →
        r322AnalyticSchedule κ = pre ++ suffix →
        (∀ step ∈ pre,
          step.1 ≠ r322WholeEndpoint q hq) →
        Nonempty (R322AnalyticQuantitativePrefixData
          hq ρ C lam ε K A κ hκ pre) := by
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
  intro lam ε q hq κ hκ pre
    suffix hlam hε hε1 hlog hqtrunc
    hschedule hproper
  induction pre using List.reverseRecOn generalizing suffix with
  | nil =>
      refine ⟨?_⟩
      exact
        { state := r322InitialAnalyticEdgeState q hq
          scale := fun _ => A
          absorbed := R322AnalyticAbsorbedState.initial
          processed := rfl
          budgetReachable :=
            R322AnalyticBudgetScaleReachable.initial
          edgeCertificate := hinitial q hq }
  | append_singleton pre step ih =>
      have hprefix :
          r322AnalyticSchedule κ =
            pre ++ step :: suffix := by
        simpa [List.append_assoc] using hschedule
      have hproperPre :
          ∀ s ∈ pre,
            s.1 ≠ r322WholeEndpoint q hq := by
        intro s hs
        exact hproper s (by
          simp only [List.mem_append, List.mem_singleton]
          exact Or.inl hs)
      obtain ⟨data⟩ :=
        ih (step :: suffix) hprefix hproperPre
      let ctx : R322AnalyticProperStepContext q hq :=
        { state := data.state
          pairing := κ
          pairing_mem := hκ
          suffix := suffix
          step := step
          schedule_eq := by
            rw [data.processed]
            exact hprefix
          proper := hproper step (by simp) }
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
            MemEClassT4 (primitiveKernelDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder H) ∧
            MemEClassT4 (primitiveKernelInsertedDiff ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder H) ∧
            PrimitiveKernelBounds ρ lam ε
              (residualBlockOrder ctx.step.2)
              ctx.one_le_blockOrder H supportConstant C := by
        intro H hH
        exact hprop lam ε
          (residualBlockOrder ctx.step.2)
          ctx.one_le_blockOrder H
          hlam hε hε1 hblockTrunc hH
      have hprimitive :
          R322AnalyticPrimitiveCertificate
            ctx data.scale ρ C lam ε supportConstant :=
        data.edgeCertificate.primitiveCertificate_of_reachable
          data.absorbed hε
          (lt_of_lt_of_le zero_lt_one hlog) hpropCtx
      have hanalytic :
          R322AnalyticEdgeCertificate
            (ctx.nextState ρ lam ε)
            (r322AnalyticUpdatedEdgeScale
              ctx data.scale
              (r322AnalyticInternalEdgeScaleProduct
                ctx data.scale)
              C lam K) :=
        hstep ρ C lam ε q hq κ hκ
          ctx data.absorbed rfl data.scale
          data.edgeCertificate hprimitive
          hC hlam hε hε1 hlog
      have hbudget :
          R322AnalyticEdgeCertificate
            (ctx.nextState ρ lam ε)
            (ctx.budgetUpdatedEdgeScale
              data.scale C lam K) :=
        data.budgetReachable
          |>.edgeCertificate_to_budgetUpdatedEdgeScale
            ctx rfl rfl hA hanalytic
      refine ⟨?_⟩
      exact
        { state := ctx.nextState ρ lam ε
          scale := ctx.budgetUpdatedEdgeScale
            data.scale C lam K
          absorbed :=
            R322AnalyticAbsorbedState.update
              ctx rfl data.absorbed
          processed := by
            simp [R322AnalyticProperStepContext.nextState,
              ctx, data.processed]
          budgetReachable :=
            R322AnalyticBudgetScaleReachable.update
              ctx rfl data.budgetReachable
          edgeCertificate := hbudget }

end

end Anderson4D
