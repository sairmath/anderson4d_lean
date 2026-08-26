import Anderson4D.DetParametrix.Paper42_Moment.R324StopBeforeStepProjection
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualSumTerminalProjection

/-!
# Cross-factor projection at an exceptional incoming stop

The cross-cut primitive factor reads only the final residual carrier.  Hence,
when the left within-half trace stops immediately before an exceptional
incoming head, that factor may already be read on the coordinates surviving
after the retained head.  The right half remains at its literal initial
carrier.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

namespace R324WithinHalfResidualPrefix
namespace R324IncomingExceptionalStopTraceAssembly

variable {ρ : SmoothCutoff} {C lam ε K : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {initialScale : Fin (m + 1) → ℝ}

/-- Projecting the left initial tuple through a certified incoming stop and
then discarding the retained head does not change the cross-cut primitive
sum.  This is the one-sided analogue of terminal projection: the right half
is untouched, while the retained left head is harmless because every final
residual vertex lies outside every extraction block. -/
theorem
    r324ResidualPrimitiveSumProduct_eq_afterHeadProjection
    (data :
      R324IncomingExceptionalStopTraceAssembly
        (ρ := ρ) (C := C) (lam := lam)
        (ε := ε) (K := K) κp initialScale)
    (π : κp.singles ≃ κm.singles)
    (vl :
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε κp).SurvivingCoordinate → T4)
    (vr :
      (R324WithinHalfResidualPrefix.initial
        ρ lam ε κm).SurvivingCoordinate → T4) :
    r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κp)
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm)
          (vl, vr)) =
      r324ResidualPrimitiveSumProduct
        ρ ε κp κm π
        (r324TwoHalfRootDoubledReconstruct
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq)
          (R324WithinHalfResidualPrefix.initial
            ρ lam ε κm)
          ((data.trace.stopPrefix
              |>.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection vl)).2,
            vr)) := by
  apply
    r324ResidualPrimitiveSumProduct_congr_on_active
      ρ ε κp κm π
  intro q hq
  by_cases hqLeft : q.val < m
  · obtain ⟨i, hiFinal, rfl⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive
        hq hqLeft
    simp only [
      r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_leftMomentIndex]
    have hiStop :
        i ∈ data.trace.stopPrefix.state.active :=
      data.trace.finalActive_subset_stopPrefix_active
        hiFinal
    have hiNotTerminal : i ∉ data.terminal.2 := by
      intro hiTerminal
      have hiRemoved :
          i ∈ finsetUnionList (extractionBlocks κp) :=
        (mem_finsetUnionList_iff
          (extractionBlocks κp)).mpr
          ⟨data.terminal.2,
            data.stopContext.block_mem_extractionBlocks,
            hiTerminal⟩
      exact
        (Finset.disjoint_left.mp
          (extractionBlocks_disjoint_finalActive κp))
          hiRemoved hiFinal
    have hiPost :
        i ∈
          (data.trace.stopPrefix.afterHead
            data.terminal data.suffix
            data.trace.stopPrefix_remaining_eq).state.active := by
      change
        i ∈
          (data.stopContext.absorb ρ lam ε).active
      rw [R324WithinHalfStepContext.absorb_active]
      exact Finset.mem_sdiff.mpr
        ⟨hiStop, hiNotTerminal⟩
    let iStop :
        data.trace.stopPrefix.SurvivingCoordinate :=
      ⟨i, hiStop⟩
    let iPost :
        (data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).SurvivingCoordinate :=
      ⟨i, hiPost⟩
    calc
      (R324WithinHalfResidualPrefix.initial
          ρ lam ε κp).reconstruct vl i =
          data.trace.stopPrefix.reconstruct
            (data.trace.stopProjection vl) i :=
        data.trace.reconstruct_stopProjection vl iStop
      _ = data.trace.stopProjection vl iStop :=
        data.trace.stopPrefix.reconstruct_surviving
          (data.trace.stopProjection vl) iStop
      _ =
          data.trace.stopProjection vl
            (data.trace.stopPrefix.postSurvivingCoordinate
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq iPost) := by
        apply congrArg (data.trace.stopProjection vl)
        apply Subtype.ext
        rfl
      _ =
          (data.trace.stopPrefix
              |>.splitSurvivingPiMeasurableEquiv
                data.terminal data.suffix
                data.trace.stopPrefix_remaining_eq
                (data.trace.stopProjection vl)).2 iPost := by
        exact
          (data.trace.stopPrefix
            |>.splitSurvivingPiMeasurableEquiv_apply_snd
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq
              (data.trace.stopProjection vl) iPost).symm
      _ =
          (data.trace.stopPrefix.afterHead
              data.terminal data.suffix
              data.trace.stopPrefix_remaining_eq).reconstruct
            (data.trace.stopPrefix
                |>.splitSurvivingPiMeasurableEquiv
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  (data.trace.stopProjection vl)).2 i :=
        ((data.trace.stopPrefix.afterHead
          data.terminal data.suffix
          data.trace.stopPrefix_remaining_eq).reconstruct_surviving
            (data.trace.stopPrefix
                |>.splitSurvivingPiMeasurableEquiv
                  data.terminal data.suffix
                  data.trace.stopPrefix_remaining_eq
                  (data.trace.stopProjection vl)).2
            iPost).symm
  · have hqRight : m ≤ q.val := by omega
    obtain ⟨j, _hjFinal, rfl⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive
        hq hqRight
    simp only [
      r324TwoHalfRootDoubledReconstruct,
      momentDoubleFinEquiv_symm_rightMomentIndex]

end R324IncomingExceptionalStopTraceAssembly
end R324WithinHalfResidualPrefix

end

end Anderson4D
