import Anderson4D.DetParametrix.Paper42_Moment.R324InitialResidualSignedCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullStep1NormalizedClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedBranchDichotomy
import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedBlockProductClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperBracketMainConditional

/-!
# Closing paper Steps 2--3 on every residual-refined fibre

This capstone combines the exact signed two-half collapse with the complete
nested-run endpoint estimate.  The only case split is the literal one on a
refined representative: zero coupling, full/full, or a nonempty residual
carrier.  No modulus is taken before all within-half and cross-block
collapses have finished.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## The nonempty initial nested-cross suffix -/

/-- A surviving single forces the canonical nested cross schedule to have
a first block. -/
theorem exists_r324InitialNestedCross_head_of_singles_nonempty
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hsingles : κp.singles.Nonempty) :
    ∃ (head : R324NestedCrossBlock κp κm π)
      (tail : List (R324NestedCrossBlock κp κm π)),
      (R324NestedCrossResidualPrefix.initial
        κp κm π).remaining = head :: tail := by
  obtain ⟨i, hi⟩ := hsingles
  have hiActive :
      leftMomentIndex i ∈ momentResidualActive κp κm := by
    unfold momentResidualActive
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨i, singles_subset_finalActive κp hi, rfl⟩
  have hiUnion :
      leftMomentIndex i ∈
        finsetUnionList
          (nonemptyMomentResidualCollapseBlocks κp κm π) := by
    unfold nonemptyMomentResidualCollapseBlocks
    rw [finsetUnionList_filter_nonempty,
      finsetUnionList_momentResidualCollapseBlocks]
    exact hiActive
  have hblocks :
      nonemptyMomentResidualCollapseBlocks κp κm π ≠ [] := by
    intro hnil
    rw [hnil] at hiUnion
    simp [finsetUnionList] at hiUnion
  cases hschedule : r324NestedCrossSchedule κp κm π with
  | nil =>
      have hcarriers :=
        r324NestedCrossSchedule_carriers κp κm π
      rw [hschedule] at hcarriers
      simp only [List.map_nil] at hcarriers
      exact False.elim (hblocks hcarriers.symm)
  | cons head tail =>
      exact ⟨head, tail, by
        simp only [R324NestedCrossResidualPrefix.initial]
        exact hschedule⟩

/-- The literal within-half pairings of any moment contraction are either
both full or carry a left residual single. -/
theorem momentContraction_singles_nonempty_or_both_isFull
    {m : ℕ} (e : MomentContraction m) :
    e.1.singles.Nonempty ∨
      (e.1.IsFull ∧ e.2.1.IsFull) := by
  by_cases hsingles : e.1.singles.Nonempty
  · exact Or.inl hsingles
  · right
    have hpempty : e.1.singles = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hsingles
    have hmempty : e.2.1.singles = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hmnonempty
      obtain ⟨j, hj⟩ := hmnonempty
      let i : e.1.singles := e.2.2.symm ⟨j, hj⟩
      exact hsingles ⟨i.1, i.2⟩
    exact
      ⟨PartialPairing.isFull_iff_singles_eq_empty.mpr hpempty,
        PartialPairing.isFull_iff_singles_eq_empty.mpr hmempty⟩

/-! ## Exact signed endpoint collapse -/

/-- One residual-refined deterministic fibre, multiplied only by the two
within-half coupling powers, is exactly the signed endpoint-integrated
nested residual density. -/
theorem lamEps_pow_momentRefinedDeterministicTermSum_eq_initialNestedEndpoint
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {leftScale rightScale : Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κp) leftScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        (R324WithinHalfResidualPrefix.initial
          ρ lam ε κm) rightScale)
    (π : κp.singles ≃ κm.singles)
    (hleft : leftTrace.terminalPrefix.state.active.Nonempty)
    (hright : rightTrace.terminalPrefix.state.active.Nonempty)
    (α β : Z4)
    (s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hs : s ∈ momentContractionSignatures m)
    (hr : r ∈ momentResidualChainSignaturesAt m s)
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (hκp : e₀.1 = κp) (hκm : e₀.2.1 = κm)
    (hπ : HEq e₀.2.2 π)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let terminal :=
      R324TwoHalfTerminalData.ofCertifiedTraces
        leftTrace rightTrace
    (lamEps lam ε : ℂ) ^
          (2 *
            ((R324WithinHalfResidualPrefix.initial
                ρ lam ε κp).remainingOrder +
              (R324WithinHalfResidualPrefix.initial
                ρ lam ε κm).remainingOrder)) *
        momentRefinedDeterministicTermSum
          ρ ε m α β s r =
      ∫ v : terminal.NestedCoordinate π → T4,
        terminal.initialNestedEndpointIntegratedResidualDensity
          π hleft hright α β v
        ∂Measure.pi fun _ => paperMeasure := by
  subst κp
  subst κm
  cases hπ
  dsimp only
  let leftRes :=
    R324WithinHalfResidualPrefix.initial ρ lam ε e₀.1
  let rightRes :=
    R324WithinHalfResidualPrefix.initial ρ lam ε e₀.2.1
  let terminal :=
    R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace
  have hroot :=
    momentRefinedDeterministicTermSum_eq_initialTwoHalfRoot
      ρ lam hε hε1 α β s hs r hr e₀ he₀
  have hleftAE :=
    R324WithinHalfResidualPrefix.eventually_integrable_initial_residualIntegrand
      ρ lam hε hε1 e₀.1
  have hrightAE :=
    R324WithinHalfResidualPrefix.eventually_integrable_initial_residualIntegrand
      ρ lam hε hε1 e₀.2.1
  have hleftNested := Measure.ae_ae_of_ae_prod hleftAE
  have hrightNested := Measure.ae_ae_of_ae_prod hrightAE
  rw [hroot]
  calc
    _ = ∫ x, ∫ y, ∫ z, ∫ w,
          momentFourierPhase α β x y z w *
            (∫ v : terminal.NestedCoordinate e₀.2.2 → T4,
              terminal.initialNestedResidualSumPhysicalCore
                e₀.2.2 x y z w v
              ∂Measure.pi fun _ => paperMeasure)
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hleftNested] with x hx
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hx] with y hxy
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hrightNested] with z hz
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hz] with w hzw
      have hcollapse :=
        leftTrace.twoHalf_lamEps_pow_integral_initialRootProduct_eq_initialNested_of_sections
          rightTrace e₀.2.2 x y z w hε hε1 hxy hzw
      have hphaseRoot :
          (∫ p :
              (leftRes.SurvivingCoordinate → T4) ×
                (rightRes.SurvivingCoordinate → T4),
            momentFourierPhase α β x y z w *
              (leftRes.residualIntegrand
                ρ ε x y (leftRes.reconstruct p.1) : ℂ) *
              (rightRes.residualIntegrand
                ρ ε z w (rightRes.reconstruct p.2) : ℂ) *
              (r324ResidualPrimitiveSumProduct
                ρ ε e₀.1 e₀.2.1 e₀.2.2
                (r324TwoHalfRootDoubledReconstruct
                  leftRes rightRes p) : ℂ)
            ∂((Measure.pi fun _ => paperMeasure).prod
              (Measure.pi fun _ => paperMeasure))) =
            momentFourierPhase α β x y z w *
              (∫ p :
                  (leftRes.SurvivingCoordinate → T4) ×
                    (rightRes.SurvivingCoordinate → T4),
                (leftRes.residualIntegrand
                  ρ ε x y (leftRes.reconstruct p.1) : ℂ) *
                  ((rightRes.residualIntegrand
                    ρ ε z w (rightRes.reconstruct p.2) : ℂ) *
                    (r324ResidualPrimitiveSumProduct
                      ρ ε e₀.1 e₀.2.1 e₀.2.2
                      (r324TwoHalfRootDoubledReconstruct
                        leftRes rightRes p) : ℂ))
                ∂((Measure.pi fun _ => paperMeasure).prod
                  (Measure.pi fun _ => paperMeasure))) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with p
        ring
      rw [hphaseRoot]
      calc
        (lamEps lam ε : ℂ) ^
              (2 * (leftRes.remainingOrder + rightRes.remainingOrder)) *
            (momentFourierPhase α β x y z w * _) =
          momentFourierPhase α β x y z w *
            ((lamEps lam ε : ℂ) ^
              (2 * (leftRes.remainingOrder + rightRes.remainingOrder)) *
              _) := by ring
        _ = _ := congrArg
          (fun t : ℂ => momentFourierPhase α β x y z w * t)
          hcollapse
    _ = _ :=
      integral_phase_mul_initialNestedResidualSum_eq_endpointIntegrated_of_storedCertificates
        leftTrace rightTrace e₀.2.2 hleft hright α β hε hε1

/-! ## Uniform closure of paper Steps 2--3 -/

/-- One pair of cutoff-dependent constants closes paper Steps 2--3 on every
residual-refined fibre.  Both constants are selected before the coupling,
mollification scale, perturbative order, and external Fourier modes. -/
theorem exists_r324PaperRefinedStep23Input
    (ρ : SmoothCutoff) :
    ∃ primitiveConstant supportConstant : ℝ,
      0 < primitiveConstant ∧ 0 < supportConstant ∧
        R324PaperRefinedStep23Input
          ρ primitiveConstant supportConstant := by
  obtain
      ⟨_phaseSupport, runSupport, C, K, A, B,
        _hphaseSupport, hrunSupport, hC, hK, hA, hB,
        htraces, hresidual⟩ :=
    exists_r324InitialResidualEndpointIntegral_le_ambientMajorant ρ
  obtain ⟨fullConstant, hfullConstant, hfullBound⟩ :=
    exists_fullFull_refined_bound_of_normalizedStep1_at_support
      ρ hrunSupport
  let residualConstant :=
    r324TwoHalfCompleteAbsorbedBase A C K B
  let primitiveConstant := max fullConstant residualConstant
  have hresidualConstant : 0 < residualConstant := by
    exact r324TwoHalfCompleteAbsorbedBase_pos A C K B
  have hprimitiveConstant : 0 < primitiveConstant := by
    exact hfullConstant.trans_le
      (by
        dsimp only [primitiveConstant]
        exact le_max_left _ _)
  refine
    ⟨primitiveConstant, runSupport,
      hprimitiveConstant, hrunSupport, ?_⟩
  intro lam ε m α β hlam hε hε1 hlog hm hmtrunc
  refine ⟨⟨?_⟩⟩
  intro s hs r hr
  rcases hlam.eq_or_lt with hlamZero | hlamPos
  · subst lam
    have htwoM : 2 * m ≠ 0 := by omega
    have hweight : |lamEps 0 ε| ^ (2 * m) = 0 := by
      simp only [lamEps, zero_div, abs_zero, zero_pow htwoM]
    rw [hweight, zero_mul]
    exact integral_nonneg fun z =>
      primitiveInsertedMajorant_nonneg
        hprimitiveConstant.le (le_refl 0)
  ·
    let e₀ : MomentContraction m :=
      r324RefinedContractionRepresentative m s r
    have he₀ :
        e₀ ∈ momentRefinedContractionFiber m s r := by
      simpa only [e₀] using
        r324RefinedContractionRepresentative_mem hr
    rcases momentContraction_singles_nonempty_or_both_isFull e₀ with
      hsingles | hbothFull
    · obtain ⟨leftData⟩ :=
        htraces lam ε m e₀.1
          hlamPos hε hε1 hlog hmtrunc
      obtain ⟨rightData⟩ :=
        htraces lam ε m e₀.2.1
          hlamPos hε hε1 hlog hmtrunc
      let terminal :=
        R324TwoHalfTerminalData.ofCertifiedTraces
          leftData.analytic rightData.analytic
      have hleft :
          leftData.analytic.terminalPrefix.state.active.Nonempty :=
        terminal.left_active_nonempty_of_singles_nonempty hsingles
      have hright :
          rightData.analytic.terminalPrefix.state.active.Nonempty :=
        terminal.right_active_nonempty_of_singles_nonempty
          e₀.2.2 hsingles
      obtain ⟨head, tail, hremaining⟩ :=
        exists_r324InitialNestedCross_head_of_singles_nonempty
          e₀.1 e₀.2.1 e₀.2.2 hsingles
      have hendpoint :=
        hresidual leftData rightData
          hlamPos hε hε1 hlog hm hmtrunc
          hleft hright head tail hremaining α β
      have hcollapse :=
        lamEps_pow_momentRefinedDeterministicTermSum_eq_initialNestedEndpoint
          leftData.analytic rightData.analytic e₀.2.2
          hleft hright α β s r hs hr e₀ he₀
          rfl rfl (HEq.rfl) hε hε1
      have horder :=
        r324InitialSchedules_remainingOrders_eq_ambient
          ρ lam ε e₀.1 e₀.2.1 e₀.2.2
      have hweighted :=
        weighted_norm_le_of_collapsed_endpointIntegral
          (lam := lam) (ε := ε) (m := m)
          (leftOrder :=
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.1).remainingOrder)
          (rightOrder :=
            (R324WithinHalfResidualPrefix.initial
              ρ lam ε e₀.2.1).remainingOrder)
          (crossOrder :=
            (R324NestedCrossResidualPrefix.initial
              e₀.1 e₀.2.1 e₀.2.2).remainingOrder)
          horder
          (momentRefinedDeterministicTermSum
            ρ ε m α β s r)
          (fun v : terminal.NestedCoordinate e₀.2.2 → T4 =>
            terminal.initialNestedEndpointIntegratedResidualDensity
              e₀.2.2 hleft hright α β v)
          hcollapse hendpoint
      exact hweighted.trans
        (integral_primitiveInsertedMajorant_mono_const
          hresidualConstant.le
          (by
            dsimp only [primitiveConstant, residualConstant]
            exact le_max_right _ _)
          lam hε runSupport m)
    · have hbound :=
        hfullBound lam ε m α β hlamPos.le hε hε1 hlog hm hmtrunc
          e₀ he₀ hbothFull.1 hbothFull.2
      exact hbound.trans
        (integral_primitiveInsertedMajorant_mono_const
          hfullConstant.le
          (by
            dsimp only [primitiveConstant]
            exact le_max_left _ _)
          lam hε runSupport m)

end

end Anderson4D
