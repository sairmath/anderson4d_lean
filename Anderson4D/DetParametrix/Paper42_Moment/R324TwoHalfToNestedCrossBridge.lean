import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfResidualStep
import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossResidualState
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse

/-!
# Exact bridge from the two within-half terminal carriers to the nested cross carrier

After the left and right canonical within-half suffixes have both been
processed, their surviving coordinates are precisely the two copies of
`finalActive`.  Paper §4.2 Step 3 starts from the union of those two copies.
This file proves that identification as an actual coordinate equivalence and
lifts it to a measure-preserving reindexing of product Haar measure.

The physical core below uses the genuine terminal within-half residual
integrands and the genuine marker-preserving covariance product.  Thus the
integral bridge does not pass through a separately postulated,
target-shaped density.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- A completed within-half prefix has exactly the paper's terminal active
carrier. -/
theorem active_eq_finalActive_of_processed_eq_schedule
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hprocessed :
      res.state.processed = r322AnalyticSchedule pairing) :
    res.state.active = finalActive pairing := by
  unfold R324WithinHalfEdgeState.active
    r322AnalyticActiveCarrier
  rw [hprocessed, finalActive_eq_sdiff_extractionBlocks]
  congr 1
  ext i
  constructor
  · intro hi
    obtain ⟨B, hB, hiB⟩ :=
      (mem_finsetUnionList_iff
        ((r322AnalyticSchedule pairing).map Prod.snd)).mp hi
    exact
      (mem_finsetUnionList_iff
        (extractionBlocks pairing)).mpr
        ⟨B,
          (r322AnalyticSchedule_blocks_perm_extractionBlocks
            pairing).mem_iff.mp hB,
          hiB⟩
  · intro hi
    obtain ⟨B, hB, hiB⟩ :=
      (mem_finsetUnionList_iff
        (extractionBlocks pairing)).mp hi
    exact
      (mem_finsetUnionList_iff
        ((r322AnalyticSchedule pairing).map Prod.snd)).mpr
        ⟨B,
          (r322AnalyticSchedule_blocks_perm_extractionBlocks
            pairing).mem_iff.mpr hB,
          hiB⟩

end R324WithinHalfResidualPrefix

namespace R324NestedCrossResidualPrefix

/-- The initial nested schedule carries exactly all variables left by the
two within-half reductions. -/
theorem initial_activeCarrier_eq_momentResidualActive
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (initial κp κm π).activeCarrier =
      momentResidualActive κp κm := by
  unfold activeCarrier initial
  rw [r324NestedCrossSchedule_carriers]
  unfold nonemptyMomentResidualCollapseBlocks
  rw [finsetUnionList_filter_nonempty,
    finsetUnionList_momentResidualCollapseBlocks]

end R324NestedCrossResidualPrefix

/-! ## Completed two-half data -/

/-- The proof-relevant endpoint of both literal within-half schedules. -/
structure R324TwoHalfTerminalData
    (ρ : SmoothCutoff) (lam ε : ℝ)
    {m : ℕ} (κp κm : PartialPairing (Fin m)) where
  left : R324WithinHalfResidualPrefix ρ lam ε κp
  right : R324WithinHalfResidualPrefix ρ lam ε κm
  left_remaining : left.remaining = []
  right_remaining : right.remaining = []
  left_processed :
    left.state.processed = r322AnalyticSchedule κp
  right_processed :
    right.state.processed = r322AnalyticSchedule κm

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)

/-- Coordinates of the literal initial nested cross prefix. -/
abbrev NestedCoordinate
    (_terminal :
      R324TwoHalfTerminalData ρ lam ε κp κm)
    (π : κp.singles ≃ κm.singles) : Type :=
  {i : Fin (2 * m) //
    i ∈
      (R324NestedCrossResidualPrefix.initial
        κp κm π).activeCarrier}

noncomputable instance nestedCoordinateFintype
    (π : κp.singles ≃ κm.singles) :
    Fintype (terminal.NestedCoordinate π) :=
  inferInstance

/-- The two terminal within-half carriers, with their ambient labels
preserved, map canonically into the initial nested cross carrier. -/
def survivingSumToNested
    (π : κp.singles ≃ κm.singles) :
    terminal.left.SurvivingCoordinate ⊕
        terminal.right.SurvivingCoordinate →
      terminal.NestedCoordinate π
  | Sum.inl i =>
      ⟨leftMomentIndex i.1, by
        rw [
          R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
            κp κm π]
        rw [leftMomentIndex_mem_momentResidualActive_iff]
        rw [←
          terminal.left.active_eq_finalActive_of_processed_eq_schedule
            terminal.left_processed]
        exact i.2⟩
  | Sum.inr j =>
      ⟨rightMomentIndex j.1, by
        rw [
          R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
            κp κm π]
        rw [rightMomentIndex_mem_momentResidualActive_iff]
        rw [←
          terminal.right.active_eq_finalActive_of_processed_eq_schedule
            terminal.right_processed]
        exact j.2⟩

/-- The two terminal within-half carriers, with their ambient labels
preserved, are exactly the initial nested cross carrier. -/
def survivingSumEquivNested
    (π : κp.singles ≃ κm.singles) :
    terminal.left.SurvivingCoordinate ⊕
        terminal.right.SurvivingCoordinate ≃
      terminal.NestedCoordinate π :=
  Equiv.ofBijective
    (terminal.survivingSumToNested π)
    ⟨by
      intro a b hab
      cases a with
      | inl i =>
          cases b with
          | inl j =>
              apply congrArg Sum.inl
              apply Subtype.ext
              apply leftMomentIndex_injective
              exact congrArg Subtype.val hab
          | inr j =>
              have hval :=
                congrArg
                  (fun x : terminal.NestedCoordinate π => x.1.val)
                  hab
              simp only [survivingSumToNested,
                leftMomentIndex, rightMomentIndex] at hval
              have hi := i.1.isLt
              omega
      | inr i =>
          cases b with
          | inl j =>
              have hval :=
                congrArg
                  (fun x : terminal.NestedCoordinate π => x.1.val)
                  hab
              simp only [survivingSumToNested,
                leftMomentIndex, rightMomentIndex] at hval
              have hj := j.1.isLt
              omega
          | inr j =>
              apply congrArg Sum.inr
              apply Subtype.ext
              apply rightMomentIndex_injective
              exact congrArg Subtype.val hab,
    by
      intro x
      have hx :
          x.1 ∈ momentResidualActive κp κm := by
        rw [←
          R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
            κp κm π]
        exact x.2
      by_cases hleft : x.1.val < m
      · obtain ⟨i, hi, hxi⟩ :=
          exists_leftMomentIndex_of_mem_momentResidualActive
            hx hleft
        let i' : terminal.left.SurvivingCoordinate :=
          ⟨i, by
            rw [
              terminal.left.active_eq_finalActive_of_processed_eq_schedule
                terminal.left_processed]
            exact hi⟩
        refine ⟨Sum.inl i', ?_⟩
        apply Subtype.ext
        exact hxi.symm
      · obtain ⟨j, hj, hxj⟩ :=
          exists_rightMomentIndex_of_mem_momentResidualActive
            hx (by omega)
        let j' : terminal.right.SurvivingCoordinate :=
          ⟨j, by
            rw [
              terminal.right.active_eq_finalActive_of_processed_eq_schedule
                terminal.right_processed]
            exact hj⟩
        refine ⟨Sum.inr j', ?_⟩
        apply Subtype.ext
        exact hxj.symm⟩

/-- Product terminal coordinates reindexed as the literal initial nested
coordinate tuple. -/
def terminalProductPiMeasurableEquivNested
    (π : κp.singles ≃ κm.singles) :
    (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4) ≃ᵐ
      (terminal.NestedCoordinate π → T4) :=
  (MeasurableEquiv.sumPiEquivProdPi
      (fun _ :
        terminal.left.SurvivingCoordinate ⊕
          terminal.right.SurvivingCoordinate => T4)).symm.trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : terminal.NestedCoordinate π => T4)
      (terminal.survivingSumEquivNested π))

@[simp]
theorem terminalProductPiMeasurableEquivNested_apply_left
    (π : κp.singles ≃ κm.singles)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4)
    (i : terminal.left.SurvivingCoordinate) :
    terminal.terminalProductPiMeasurableEquivNested π (vl, vr)
      (terminal.survivingSumEquivNested π (Sum.inl i)) =
      vl i := by
  have happ :
      terminal.terminalProductPiMeasurableEquivNested π (vl, vr) =
        (MeasurableEquiv.piCongrLeft
          (fun _ : terminal.NestedCoordinate π => T4)
          (terminal.survivingSumEquivNested π))
          ((MeasurableEquiv.sumPiEquivProdPi
            (fun _ :
              terminal.left.SurvivingCoordinate ⊕
                terminal.right.SurvivingCoordinate => T4)).symm
            (vl, vr)) := by
    rfl
  rw [happ]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

@[simp]
theorem terminalProductPiMeasurableEquivNested_apply_right
    (π : κp.singles ≃ κm.singles)
    (vl : terminal.left.SurvivingCoordinate → T4)
    (vr : terminal.right.SurvivingCoordinate → T4)
    (j : terminal.right.SurvivingCoordinate) :
    terminal.terminalProductPiMeasurableEquivNested π (vl, vr)
      (terminal.survivingSumEquivNested π (Sum.inr j)) =
      vr j := by
  have happ :
      terminal.terminalProductPiMeasurableEquivNested π (vl, vr) =
        (MeasurableEquiv.piCongrLeft
          (fun _ : terminal.NestedCoordinate π => T4)
          (terminal.survivingSumEquivNested π))
          ((MeasurableEquiv.sumPiEquivProdPi
            (fun _ :
              terminal.left.SurvivingCoordinate ⊕
                terminal.right.SurvivingCoordinate => T4)).symm
            (vl, vr)) := by
    rfl
  rw [happ]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

/-- The exact product-Haar measure is preserved by the two-half to nested
coordinate reindexing. -/
theorem measurePreserving_terminalProductPiMeasurableEquivNested
    (π : κp.singles ≃ κm.singles) :
    MeasurePreserving
      (terminal.terminalProductPiMeasurableEquivNested π)
      ((Measure.pi fun _ :
          terminal.left.SurvivingCoordinate => paperMeasure).prod
        (Measure.pi fun _ :
          terminal.right.SurvivingCoordinate => paperMeasure))
      (Measure.pi fun _ :
        terminal.NestedCoordinate π => paperMeasure) := by
  have hsum :=
    (measurePreserving_sumPiEquivProdPi
      (fun _ :
        terminal.left.SurvivingCoordinate ⊕
          terminal.right.SurvivingCoordinate =>
        paperMeasure)).symm
  have hcongr :=
    measurePreserving_piCongrLeft
      (fun _ : terminal.NestedCoordinate π => paperMeasure)
      (terminal.survivingSumEquivNested π)
  have hfun :
      (terminal.terminalProductPiMeasurableEquivNested π :
        ((terminal.left.SurvivingCoordinate → T4) ×
          (terminal.right.SurvivingCoordinate → T4)) →
          (terminal.NestedCoordinate π → T4)) =
        (MeasurableEquiv.piCongrLeft
          (fun _ : terminal.NestedCoordinate π => T4)
          (terminal.survivingSumEquivNested π)) ∘
        (MeasurableEquiv.sumPiEquivProdPi
          (fun _ :
            terminal.left.SurvivingCoordinate ⊕
              terminal.right.SurvivingCoordinate => T4)).symm := by
    funext p
    rfl
  rw [hfun]
  exact hcongr.comp hsum

/-! ## Genuine terminal and nested physical cores -/

/-- Assemble the two genuine terminal within-half reconstructions into the
doubled ambient carrier.  This definition is independent of the nested
schedule. -/
def terminalDoubledReconstruct
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    Fin (2 * m) → T4 :=
  fun k =>
    match (momentDoubleFinEquiv m).symm k with
    | Sum.inl i => terminal.left.reconstruct p.1 i
    | Sum.inr j => terminal.right.reconstruct p.2 j

/-- Reconstruct the doubled ambient tuple from the literal initial nested
carrier, setting only genuinely absent coordinates to zero. -/
def nestedReconstruct
    (π : κp.singles ≃ κm.singles)
    (v : terminal.NestedCoordinate π → T4) :
    Fin (2 * m) → T4 :=
  fun k =>
    if hk :
        k ∈
          (R324NestedCrossResidualPrefix.initial
            κp κm π).activeCarrier then
      v ⟨k, hk⟩
    else 0

@[simp]
theorem nestedReconstruct_surviving
    (π : κp.singles ≃ κm.singles)
    (v : terminal.NestedCoordinate π → T4)
    (i : terminal.NestedCoordinate π) :
    terminal.nestedReconstruct π v i.1 = v i := by
  unfold nestedReconstruct
  rw [dif_pos i.2]

/-- The abstract measure reindexing reconstructs exactly the same ambient
doubled tuple as the two concrete terminal within-half reconstructions. -/
theorem terminalDoubledReconstruct_eq_nestedReconstruct
    (π : κp.singles ≃ κm.singles)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    terminal.terminalDoubledReconstruct p =
      terminal.nestedReconstruct π
        (terminal.terminalProductPiMeasurableEquivNested π p) := by
  funext k
  generalize hs :
      (momentDoubleFinEquiv m).symm k = s
  cases s with
  | inl i =>
      have hk :
          k = leftMomentIndex i := by
        have h := congrArg (momentDoubleFinEquiv m) hs
        simpa using h
      subst k
      unfold terminalDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_leftMomentIndex]
      by_cases hi : i ∈ terminal.left.state.active
      · let i' : terminal.left.SurvivingCoordinate := ⟨i, hi⟩
        have hnested :
            leftMomentIndex i ∈
              (R324NestedCrossResidualPrefix.initial
                κp κm π).activeCarrier := by
          rw [
            R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
              κp κm π,
            leftMomentIndex_mem_momentResidualActive_iff,
            ←
              terminal.left.active_eq_finalActive_of_processed_eq_schedule
                terminal.left_processed]
          exact hi
        unfold nestedReconstruct
        rw [dif_pos hnested]
        change
          terminal.left.reconstruct p.1 i =
            terminal.terminalProductPiMeasurableEquivNested π p
              ⟨leftMomentIndex i, hnested⟩
        rw [terminal.left.reconstruct_surviving p.1 i']
        have hcoord :
            (⟨leftMomentIndex i, hnested⟩ :
                terminal.NestedCoordinate π) =
              terminal.survivingSumEquivNested π
                (Sum.inl i') := by
          apply Subtype.ext
          rfl
        rw [hcoord]
        simpa only [Prod.eta] using
          (terminal.terminalProductPiMeasurableEquivNested_apply_left
            π p.1 p.2 i').symm
      · have hnested :
            leftMomentIndex i ∉
              (R324NestedCrossResidualPrefix.initial
                κp κm π).activeCarrier := by
          rw [
            R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
              κp κm π,
            leftMomentIndex_mem_momentResidualActive_iff,
            ←
              terminal.left.active_eq_finalActive_of_processed_eq_schedule
                terminal.left_processed]
          exact hi
        unfold R324WithinHalfResidualPrefix.reconstruct
          nestedReconstruct
        change
          (if hi' : i ∈ terminal.left.state.active then
              p.1 ⟨i, hi'⟩
            else 0) =
            if hk :
                leftMomentIndex i ∈
                  (R324NestedCrossResidualPrefix.initial
                    κp κm π).activeCarrier then
              terminal.terminalProductPiMeasurableEquivNested π p
                ⟨leftMomentIndex i, hk⟩
            else 0
        rw [dif_neg hi, dif_neg hnested]
  | inr j =>
      have hk :
          k = rightMomentIndex j := by
        have h := congrArg (momentDoubleFinEquiv m) hs
        simpa using h
      subst k
      unfold terminalDoubledReconstruct
      rw [momentDoubleFinEquiv_symm_rightMomentIndex]
      by_cases hj : j ∈ terminal.right.state.active
      · let j' : terminal.right.SurvivingCoordinate := ⟨j, hj⟩
        have hnested :
            rightMomentIndex j ∈
              (R324NestedCrossResidualPrefix.initial
                κp κm π).activeCarrier := by
          rw [
            R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
              κp κm π,
            rightMomentIndex_mem_momentResidualActive_iff,
            ←
              terminal.right.active_eq_finalActive_of_processed_eq_schedule
                terminal.right_processed]
          exact hj
        unfold nestedReconstruct
        rw [dif_pos hnested]
        change
          terminal.right.reconstruct p.2 j =
            terminal.terminalProductPiMeasurableEquivNested π p
              ⟨rightMomentIndex j, hnested⟩
        rw [terminal.right.reconstruct_surviving p.2 j']
        have hcoord :
            (⟨rightMomentIndex j, hnested⟩ :
                terminal.NestedCoordinate π) =
              terminal.survivingSumEquivNested π
                (Sum.inr j') := by
          apply Subtype.ext
          rfl
        rw [hcoord]
        simpa only [Prod.eta] using
          (terminal.terminalProductPiMeasurableEquivNested_apply_right
            π p.1 p.2 j').symm
      · have hnested :
            rightMomentIndex j ∉
              (R324NestedCrossResidualPrefix.initial
                κp κm π).activeCarrier := by
          rw [
            R324NestedCrossResidualPrefix.initial_activeCarrier_eq_momentResidualActive
              κp κm π,
            rightMomentIndex_mem_momentResidualActive_iff,
            ←
              terminal.right.active_eq_finalActive_of_processed_eq_schedule
                terminal.right_processed]
          exact hj
        unfold R324WithinHalfResidualPrefix.reconstruct
          nestedReconstruct
        change
          (if hj' : j ∈ terminal.right.state.active then
              p.2 ⟨j, hj'⟩
            else 0) =
            if hk :
                rightMomentIndex j ∈
                  (R324NestedCrossResidualPrefix.initial
                    κp κm π).activeCarrier then
              terminal.terminalProductPiMeasurableEquivNested π p
                ⟨rightMomentIndex j, hk⟩
            else 0
        rw [dif_neg hj, dif_neg hnested]

/-- At an actually completed suffix, no unprocessed difference or primitive
factor remains hidden in the within-half residual integrand. -/
theorem left_residualIntegrand_eq_chain
    (x y : T4)
    (v : Fin m → T4) :
    terminal.left.residualIntegrand ρ ε x y v =
      terminal.left.residualChainProduct x y v := by
  letI : IsEmpty (Fin terminal.left.remaining.length) :=
    ⟨fun i => by
      have hi := i.isLt
      have hlen :=
        congrArg List.length terminal.left_remaining
      simp only [List.length_nil] at hlen
      omega⟩
  unfold R324WithinHalfResidualPrefix.residualIntegrand
    R324WithinHalfResidualPrefix.residualDifferenceProduct
    R324WithinHalfResidualPrefix.residualPrimitiveProduct
  simp [terminal.left_remaining]

/-- Right-copy counterpart of `left_residualIntegrand_eq_chain`. -/
theorem right_residualIntegrand_eq_chain
    (z w : T4)
    (v : Fin m → T4) :
    terminal.right.residualIntegrand ρ ε z w v =
      terminal.right.residualChainProduct z w v := by
  letI : IsEmpty (Fin terminal.right.remaining.length) :=
    ⟨fun i => by
      have hi := i.isLt
      have hlen :=
        congrArg List.length terminal.right_remaining
      simp only [List.length_nil] at hlen
      omega⟩
  unfold R324WithinHalfResidualPrefix.residualIntegrand
    R324WithinHalfResidualPrefix.residualDifferenceProduct
    R324WithinHalfResidualPrefix.residualPrimitiveProduct
  simp [terminal.right_remaining]

/-- Genuine post-phase-A physical fibre on the product of the two completed
within-half carriers.  The projected marker remains inside the complete
physical covariance product. -/
def terminalMarkedPhysicalCore
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) : ℂ :=
  (terminal.left.residualIntegrand ρ ε x y
      (terminal.left.reconstruct p.1) : ℂ) *
    (terminal.right.residualIntegrand ρ ε z w
      (terminal.right.reconstruct p.2) : ℂ) *
    ρ.r324MarkedPairingCovarianceProductOn ε L
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (momentResidualActive κp κm)
      (terminal.terminalDoubledReconstruct p)

/-- The same genuine physical fibre, now expressed on the literal initial
nested carrier.  This is a lossless coordinate transport of
`terminalMarkedPhysicalCore`, not an independently postulated model
integrand. -/
def initialNestedMarkedPhysicalCore
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (v : terminal.NestedCoordinate π → T4) : ℂ :=
  terminal.terminalMarkedPhysicalCore π selected L x y z w
    ((terminal.terminalProductPiMeasurableEquivNested π).symm v)

/-- In particular, the genuine marker-preserving covariance product is
unchanged by the terminal-to-nested coordinate bridge. -/
theorem markedCovariance_terminal_eq_nested
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (momentResidualActive κp κm)
        (terminal.terminalDoubledReconstruct p) =
      ρ.r324MarkedPairingCovarianceProductOn ε L
        (momentCombinedPairing κp κm π)
        (r324ResidualMarkedLowerEndpoint selected)
        (momentResidualActive κp κm)
        (terminal.nestedReconstruct π
          (terminal.terminalProductPiMeasurableEquivNested π p)) := by
  rw [terminal.terminalDoubledReconstruct_eq_nestedReconstruct π p]

/-- Pointwise losslessness of the physical terminal-to-nested transport. -/
theorem initialNestedMarkedPhysicalCore_reindex
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4)
    (p :
      (terminal.left.SurvivingCoordinate → T4) ×
        (terminal.right.SurvivingCoordinate → T4)) :
    terminal.initialNestedMarkedPhysicalCore
        π selected L x y z w
        (terminal.terminalProductPiMeasurableEquivNested π p) =
      terminal.terminalMarkedPhysicalCore
        π selected L x y z w p := by
  unfold initialNestedMarkedPhysicalCore
  rw [MeasurableEquiv.symm_apply_apply]

/-- **Exact two-half-to-nested Fubini bridge.**

The integral of the actual completed two-half physical fibre is exactly
the integral of that same fibre on
`R324NestedCrossResidualPrefix.initial`.  No norm, estimate, or enlarged
density is introduced. -/
theorem integral_terminalMarkedPhysicalCore_eq_initialNested
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ) (x y z w : T4) :
    (∫ p,
        terminal.terminalMarkedPhysicalCore
          π selected L x y z w p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure))) =
      ∫ v,
        terminal.initialNestedMarkedPhysicalCore
          π selected L x y z w v
        ∂(Measure.pi fun _ :
          terminal.NestedCoordinate π => paperMeasure) := by
  have hp :=
    terminal.measurePreserving_terminalProductPiMeasurableEquivNested π
  calc
    (∫ p,
        terminal.terminalMarkedPhysicalCore
          π selected L x y z w p
        ∂((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure))) =
        ∫ p,
          terminal.initialNestedMarkedPhysicalCore
            π selected L x y z w
            (terminal.terminalProductPiMeasurableEquivNested π p)
          ∂((Measure.pi fun _ :
              terminal.left.SurvivingCoordinate => paperMeasure).prod
            (Measure.pi fun _ :
              terminal.right.SurvivingCoordinate => paperMeasure)) := by
      apply integral_congr_ae
      filter_upwards with p
      exact
        (terminal.initialNestedMarkedPhysicalCore_reindex
          π selected L x y z w p).symm
    _ =
        ∫ v,
          terminal.initialNestedMarkedPhysicalCore
            π selected L x y z w v
          ∂(Measure.pi fun _ :
            terminal.NestedCoordinate π => paperMeasure) := by
      simpa only [Function.comp_apply] using
        hp.integral_comp'
          (fun v =>
            terminal.initialNestedMarkedPhysicalCore
              π selected L x y z w v)

end R324TwoHalfTerminalData

/-! ## Weighted within-half transition

The scalar residual-value iteration from the earlier module is insufficient
under a cross covariance, because that covariance depends on the coordinates
which survive the current half.  The following theorem is the required
outer-functional strengthening: the outer function may depend arbitrarily
on every post-head coordinate, but is fixed during the current local block
integral. -/

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing)

section WeightedHead

variable
    (head : R322ExtractionStep m)
    (tail : List (R322ExtractionStep m))
    (hremaining : res.remaining = head :: tail)

/-- One exact head transition with a genuinely coordinate-dependent complex
outer factor.  Its pullback to the pre-head carrier is the second component
of the proved measure-preserving head/post split. -/
theorem lamEps_pow_integral_residual_mul_postOuter_eq_afterHead
    (x y : T4)
    (outer :
      ((res.afterHead head tail hremaining).SurvivingCoordinate →
        T4) → ℂ)
    (hfull :
      Integrable
        (fun w : res.SurvivingCoordinate → T4 =>
          (res.residualIntegrand ρ ε x y
              (res.reconstruct w) : ℂ) *
            outer
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2)
        (Measure.pi fun _ => paperMeasure))
    (hstandard :
      ∀ v :
          (res.afterHead head tail hremaining).SurvivingCoordinate →
            T4,
        Integrable
          ((res.headContext head tail hremaining).localIntegrand
            ρ ε
            (res.headPredecessorPoint
                head tail hremaining x y v -
              res.headSuccessorPoint
                head tail hremaining x y v))
          (Measure.pi fun _ => paperMeasure))
    (hinternal :
      ∀ _v :
          (res.afterHead head tail hremaining).SurvivingCoordinate →
            T4,
        ∀ᵐ p ∂(paperMeasure.prod paperMeasure),
          ∀ κB :
              {κ : PartialPairing
                  (Fin (2 * residualBlockOrder head.2)) //
                κ ∈ primitiveFullPairings
                  (residualBlockOrder head.2)},
            Integrable
              (fun w :
                  Fin (2 * residualBlockOrder head.2 - 2) → T4 =>
                detJclosedIntegrandWith ρ ε
                  (2 * residualBlockOrder head.2)
                  κB.1
                  (res.headContext
                    head tail hremaining).internalEdges
                  (primitiveAssemble
                    (residualBlockOrder head.2)
                    (res.headContext
                      head tail hremaining).one_le_blockOrder
                    p.1 p.2 w))
              (Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ w : res.SurvivingCoordinate → T4,
          (res.residualIntegrand ρ ε x y
              (res.reconstruct w) : ℂ) *
            outer
              (res.splitSurvivingPiMeasurableEquiv
                head tail hremaining w).2
          ∂Measure.pi fun _ => paperMeasure) =
      (lamEps lam ε : ℂ) ^
          (2 *
            (res.afterHead
              head tail hremaining).remainingOrder) *
        (∫ v :
            (res.afterHead
              head tail hremaining).SurvivingCoordinate → T4,
          ((res.afterHead
              head tail hremaining).residualIntegrand
                ρ ε x y
                ((res.afterHead
                  head tail hremaining).reconstruct v) : ℂ) *
            outer v
          ∂Measure.pi fun _ => paperMeasure) := by
  have hsplit :=
    res.integral_splitSurviving_post_first
      head tail hremaining
      (fun w : res.SurvivingCoordinate → T4 =>
        (res.residualIntegrand ρ ε x y
            (res.reconstruct w) : ℂ) *
          outer
            (res.splitSurvivingPiMeasurableEquiv
              head tail hremaining w).2)
      hfull
  have hexponent :
      2 * res.remainingOrder =
        2 *
            (res.afterHead
              head tail hremaining).remainingOrder +
          2 * residualBlockOrder head.2 := by
    have horder :=
      res.remainingOrder_head head tail hremaining
    omega
  rw [hexponent, pow_add, hsplit]
  rw [mul_assoc]
  rw [← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  have hsplitSnd :
      ∀ t : Fin (2 * residualBlockOrder head.2) → T4,
        (res.splitSurvivingPiMeasurableEquiv
            head tail hremaining
            ((res.splitSurvivingPiMeasurableEquiv
              head tail hremaining).symm (t, v))).2 =
          v := by
    intro t
    exact congrArg Prod.snd
      ((res.splitSurvivingPiMeasurableEquiv
        head tail hremaining).apply_symm_apply (t, v))
  simp_rw [hsplitSnd]
  have hsection :=
    res.lamEps_pow_integral_residualIntegrand_section_eq_afterHead
      head tail hremaining x y v
      (hstandard v) (hinternal v)
  have houter :
      (∫ t :
          Fin (2 * residualBlockOrder head.2) → T4,
        (res.residualIntegrand ρ ε x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v))) : ℂ) *
          outer v
        ∂Measure.pi fun _ => paperMeasure) =
        (∫ t :
            Fin (2 * residualBlockOrder head.2) → T4,
          (res.residualIntegrand ρ ε x y
            (res.reconstruct
              ((res.splitSurvivingPiMeasurableEquiv
                head tail hremaining).symm (t, v))) : ℂ)
          ∂Measure.pi fun _ => paperMeasure) *
          outer v := by
    exact integral_mul_const _ _
  rw [houter, ← mul_assoc, hsection]

end WeightedHead

end R324WithinHalfResidualPrefix

/-- A data-valued version of the exact within-half ready trace.

The earlier trace intentionally lives in `Prop`, so Lean correctly forbids
eliminating it to obtain the terminal coordinate type.  This `Type`-valued
trace stores the same genuine step certificates and can therefore carry a
coordinate-dependent outer function all the way to its actual terminal
carrier. -/
inductive R324WithinHalfWeightedTrace
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (x y : T4) :
    R324WithinHalfResidualPrefix ρ lam ε pairing → Type
  | terminal
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (hremaining : res.remaining = []) :
      R324WithinHalfWeightedTrace x y res
  | step
      (res :
        R324WithinHalfResidualPrefix ρ lam ε pairing)
      (head : R322ExtractionStep m)
      (tail : List (R322ExtractionStep m))
      (hremaining : res.remaining = head :: tail)
      (ready :
        R324WithinHalfResidualPrefix.R324WithinHalfResidualStepReady
          res head tail hremaining x y)
      (next :
        R324WithinHalfWeightedTrace x y
          (res.afterHead head tail hremaining)) :
      R324WithinHalfWeightedTrace x y res

namespace R324WithinHalfWeightedTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    {x y : T4}

/-- The literal terminal prefix reached by a data-valued trace. -/
def terminalPrefix
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    (trace : R324WithinHalfWeightedTrace x y res) :
    R324WithinHalfResidualPrefix ρ lam ε pairing :=
  match trace with
  | .terminal .. => res
  | @R324WithinHalfWeightedTrace.step
      _ _ _ _ _ _ _ _ _ _ _ _ next => next.terminalPrefix

/-- Restrict a current surviving tuple through every proved head/post split
until it becomes a tuple on the actual terminal carrier. -/
def terminalProjection
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    (trace : R324WithinHalfWeightedTrace x y res) :
    (res.SurvivingCoordinate → T4) →
      (trace.terminalPrefix.SurvivingCoordinate → T4) :=
  match trace with
  | .terminal .. => fun v => v
  | @R324WithinHalfWeightedTrace.step
      _ _ _ _ _ _ _
      current head tail hremaining _ next =>
      fun v =>
        next.terminalProjection
          (current.splitSurvivingPiMeasurableEquiv
            head tail hremaining v).2

/-- Weighted integrability required exactly at the nonterminal nodes. -/
def WeightedIntegrableAlong
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    (trace : R324WithinHalfWeightedTrace x y res)
    (outer :
      (trace.terminalPrefix.SurvivingCoordinate → T4) → ℂ) :
    Prop :=
  match trace with
  | .terminal .. => True
  | @R324WithinHalfWeightedTrace.step
      _ _ _ _ _ _ _
      current head tail hremaining _ next =>
      Integrable
          (fun v : current.SurvivingCoordinate → T4 =>
            (current.residualIntegrand ρ ε x y
                (current.reconstruct v) : ℂ) *
              outer
                (next.terminalProjection
                  (current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining v).2))
          (Measure.pi fun _ => paperMeasure) ∧
        next.WeightedIntegrableAlong outer

/-- The terminal prefix has an empty suffix. -/
theorem terminalPrefix_remaining_eq_nil
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    (trace : R324WithinHalfWeightedTrace x y res) :
    trace.terminalPrefix.remaining = [] := by
  induction trace with
  | terminal terminal hremaining =>
      exact hremaining
  | step current head tail hremaining hstep next ih =>
      exact ih

/-- The terminal prefix has processed the complete analytic schedule. -/
theorem terminalPrefix_processed_eq_schedule
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    (trace : R324WithinHalfWeightedTrace x y res) :
    trace.terminalPrefix.state.processed =
      r322AnalyticSchedule pairing := by
  induction trace with
  | terminal terminal hremaining =>
      have hschedule := terminal.schedule_eq
      rw [hremaining, List.append_nil] at hschedule
      exact hschedule.symm
  | step current head tail hremaining hstep next ih =>
      exact ih

/-- **Exact weighted iteration through the full literal suffix.** -/
theorem lamEps_pow_integral_mul_terminalOuter_eq_terminal
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    (trace : R324WithinHalfWeightedTrace x y res)
    (outer :
      (trace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (hweighted : trace.WeightedIntegrableAlong outer) :
    (lamEps lam ε : ℂ) ^ (2 * res.remainingOrder) *
        (∫ v : res.SurvivingCoordinate → T4,
          (res.residualIntegrand ρ ε x y
              (res.reconstruct v) : ℂ) *
            outer (trace.terminalProjection v)
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          trace.terminalPrefix.SurvivingCoordinate → T4,
        ((trace.terminalPrefix.residualIntegrand
            ρ ε x y
            (trace.terminalPrefix.reconstruct v) : ℂ) *
          outer v)
        ∂Measure.pi fun _ => paperMeasure := by
  induction trace with
  | terminal terminal hremaining =>
      have horder :
          terminal.remainingOrder = 0 := by
        unfold R324WithinHalfResidualPrefix.remainingOrder
        rw [hremaining]
        rfl
      simp only [terminalPrefix, terminalProjection]
      rw [horder]
      simp
      rfl
  | step current head tail hremaining hstep next ih =>
      have hcurrent : Integrable
          (fun v : current.SurvivingCoordinate → T4 =>
            (current.residualIntegrand ρ ε x y
                (current.reconstruct v) : ℂ) *
              outer
                (next.terminalProjection
                  (current.splitSurvivingPiMeasurableEquiv
                    head tail hremaining v).2))
          (Measure.pi fun _ => paperMeasure) :=
        hweighted.1
      have hnext :
          next.WeightedIntegrableAlong outer :=
        hweighted.2
      change
        (lamEps lam ε : ℂ) ^ (2 * current.remainingOrder) *
            (∫ v : current.SurvivingCoordinate → T4,
              (current.residualIntegrand ρ ε x y
                  (current.reconstruct v) : ℂ) *
                outer
                  (next.terminalProjection
                    (current.splitSurvivingPiMeasurableEquiv
                      head tail hremaining v).2)
              ∂Measure.pi fun _ => paperMeasure) =
          ∫ v :
              next.terminalPrefix.SurvivingCoordinate → T4,
            ((next.terminalPrefix.residualIntegrand
                ρ ε x y
                (next.terminalPrefix.reconstruct v) : ℂ) *
              outer v)
            ∂Measure.pi fun _ => paperMeasure
      rw [
        current.lamEps_pow_integral_residual_mul_postOuter_eq_afterHead
          head tail hremaining x y
          (fun v => outer (next.terminalProjection v))
          hcurrent hstep.standard hstep.internal]
      exact ih outer hnext

/-- A uniform genuine step provider constructs the data-valued trace needed
for coordinate-dependent outer factors. -/
def of_provider
    (x y : T4)
    (provider :
      R324WithinHalfResidualPrefix.R324WithinHalfResidualStepProvider
        (ρ := ρ) (lam := lam) (ε := ε)
        (pairing := pairing) x y)
    (res :
      R324WithinHalfResidualPrefix ρ lam ε pairing) :
    R324WithinHalfWeightedTrace x y res := by
  cases hremaining : res.remaining with
  | nil =>
      exact
        R324WithinHalfWeightedTrace.terminal
          res hremaining
  | cons head tail =>
      exact
        R324WithinHalfWeightedTrace.step
          res head tail hremaining
          (provider res head tail hremaining)
          (of_provider x y provider
            (res.afterHead head tail hremaining))
termination_by res.remaining.length
decreasing_by simp [hremaining]

end R324WithinHalfWeightedTrace

namespace R324TwoHalfTerminalData

/-- Package the actual terminal prefixes of two data-valued within-half
traces for the carrier/Fubini bridge above. -/
def ofTraces
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {x y z w : T4}
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    (leftTrace :
      R324WithinHalfWeightedTrace x y leftRes)
    (rightTrace :
      R324WithinHalfWeightedTrace z w rightRes) :
    R324TwoHalfTerminalData ρ lam ε κp κm where
  left := leftTrace.terminalPrefix
  right := rightTrace.terminalPrefix
  left_remaining :=
    leftTrace.terminalPrefix_remaining_eq_nil
  right_remaining :=
    rightTrace.terminalPrefix_remaining_eq_nil
  left_processed :=
    leftTrace.terminalPrefix_processed_eq_schedule
  right_processed :=
    rightTrace.terminalPrefix_processed_eq_schedule

end R324TwoHalfTerminalData

namespace R324WithinHalfWeightedTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {x y z w : T4}
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}

/-- The genuine marked cross covariance, evaluated on the two actual
terminal projections of a pair of weighted traces. -/
def terminalMarkedCrossFactor
    (leftTrace :
      R324WithinHalfWeightedTrace x y leftRes)
    (rightTrace :
      R324WithinHalfWeightedTrace z w rightRes)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (vl : leftTrace.terminalPrefix.SurvivingCoordinate → T4)
    (vr : rightTrace.terminalPrefix.SurvivingCoordinate → T4) : ℂ :=
  let terminal :=
    R324TwoHalfTerminalData.ofTraces leftTrace rightTrace
  ρ.r324MarkedPairingCovarianceProductOn ε L
    (momentCombinedPairing κp κm π)
    (r324ResidualMarkedLowerEndpoint selected)
    (momentResidualActive κp κm)
    (terminal.terminalDoubledReconstruct (vl, vr))

/-- **Exact two-sided weighted within-half iteration.**

The left trace is collapsed with the right terminal projection fixed, then
the right trace is collapsed with the completed left integral as its outer
factor.  The theorem stays in physical space and takes no norm. -/
theorem twoHalf_lamEps_pow_integral_eq_terminal
    (leftTrace :
      R324WithinHalfWeightedTrace x y leftRes)
    (rightTrace :
      R324WithinHalfWeightedTrace z w rightRes)
    (cross :
      (leftTrace.terminalPrefix.SurvivingCoordinate → T4) →
        (rightTrace.terminalPrefix.SurvivingCoordinate → T4) → ℂ)
    (hleft :
      ∀ vr : rightRes.SurvivingCoordinate → T4,
        leftTrace.WeightedIntegrableAlong
          (fun vl =>
            cross vl (rightTrace.terminalProjection vr)))
    (hright :
      rightTrace.WeightedIntegrableAlong
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl vr)
            ∂Measure.pi fun _ => paperMeasure)) :
    (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
        (∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^
                (2 * leftRes.remainingOrder) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand ρ ε x y
                    (leftRes.reconstruct vl) : ℂ) *
                  cross
                    (leftTrace.terminalProjection vl)
                    (rightTrace.terminalProjection vr)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ vr :
          rightTrace.terminalPrefix.SurvivingCoordinate → T4,
        ((rightTrace.terminalPrefix.residualIntegrand
            ρ ε z w
            (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
          (∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl vr)
            ∂Measure.pi fun _ => paperMeasure))
        ∂Measure.pi fun _ => paperMeasure := by
  have hleftEq :
      ∀ vr : rightRes.SurvivingCoordinate → T4,
        (lamEps lam ε : ℂ) ^ (2 * leftRes.remainingOrder) *
            (∫ vl : leftRes.SurvivingCoordinate → T4,
              (leftRes.residualIntegrand ρ ε x y
                  (leftRes.reconstruct vl) : ℂ) *
                cross
                  (leftTrace.terminalProjection vl)
                  (rightTrace.terminalProjection vr)
              ∂Measure.pi fun _ => paperMeasure) =
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              cross vl (rightTrace.terminalProjection vr))
            ∂Measure.pi fun _ => paperMeasure := by
    intro vr
    exact
      leftTrace.lamEps_pow_integral_mul_terminalOuter_eq_terminal
        (fun vl =>
          cross vl (rightTrace.terminalProjection vr))
        (hleft vr)
  simp_rw [hleftEq]
  exact
    rightTrace.lamEps_pow_integral_mul_terminalOuter_eq_terminal
      (fun vr =>
        ∫ vl :
            leftTrace.terminalPrefix.SurvivingCoordinate → T4,
          ((leftTrace.terminalPrefix.residualIntegrand
              ρ ε x y
              (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
            cross vl vr)
          ∂Measure.pi fun _ => paperMeasure)
      hright

/-- Fubini identifies the iterated terminal expression with the genuine
product-carrier `terminalMarkedPhysicalCore`. -/
theorem integral_terminalMarkedPhysicalCore_eq_iterated
    (leftTrace :
      R324WithinHalfWeightedTrace x y leftRes)
    (rightTrace :
      R324WithinHalfWeightedTrace z w rightRes)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (hintegrable :
      Integrable
        ((R324TwoHalfTerminalData.ofTraces
          leftTrace rightTrace).terminalMarkedPhysicalCore
            π selected L x y z w)
        ((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure))) :
    (∫ p,
        (R324TwoHalfTerminalData.ofTraces
          leftTrace rightTrace).terminalMarkedPhysicalCore
            π selected L x y z w p
        ∂((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure))) =
      ∫ vr :
          rightTrace.terminalPrefix.SurvivingCoordinate → T4,
        ((rightTrace.terminalPrefix.residualIntegrand
            ρ ε z w
            (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
          (∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              terminalMarkedCrossFactor
                leftTrace rightTrace π selected L vl vr)
            ∂Measure.pi fun _ => paperMeasure))
        ∂Measure.pi fun _ => paperMeasure := by
  letI :
      IsFiniteMeasure
        (Measure.pi fun _ :
          leftTrace.terminalPrefix.SurvivingCoordinate =>
            paperMeasure) :=
    Measure.pi.instIsFiniteMeasure _
  letI :
      IsFiniteMeasure
        (Measure.pi fun _ :
          rightTrace.terminalPrefix.SurvivingCoordinate =>
            paperMeasure) :=
    Measure.pi.instIsFiniteMeasure _
  letI :
      SigmaFinite
        (Measure.pi fun _ :
          leftTrace.terminalPrefix.SurvivingCoordinate =>
            paperMeasure) :=
    IsFiniteMeasure.toSigmaFinite _
  letI :
      SigmaFinite
        (Measure.pi fun _ :
          rightTrace.terminalPrefix.SurvivingCoordinate =>
            paperMeasure) :=
    IsFiniteMeasure.toSigmaFinite _
  letI :
      SFinite
        (Measure.pi fun _ :
          leftTrace.terminalPrefix.SurvivingCoordinate =>
            paperMeasure) :=
    inferInstance
  letI :
      SFinite
        (Measure.pi fun _ :
          rightTrace.terminalPrefix.SurvivingCoordinate =>
            paperMeasure) :=
    inferInstance
  rw [integral_prod_symm
    (μ := Measure.pi fun _ :
      leftTrace.terminalPrefix.SurvivingCoordinate =>
        paperMeasure)
    (ν := Measure.pi fun _ :
      rightTrace.terminalPrefix.SurvivingCoordinate =>
        paperMeasure)
    _ hintegrable]
  apply integral_congr_ae
  filter_upwards with vr
  calc
    (∫ vl,
        (R324TwoHalfTerminalData.ofTraces
          leftTrace rightTrace).terminalMarkedPhysicalCore
            π selected L x y z w (vl, vr)
        ∂Measure.pi fun _ => paperMeasure) =
        ∫ vl,
          (rightTrace.terminalPrefix.residualIntegrand
              ρ ε z w
              (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              terminalMarkedCrossFactor
                leftTrace rightTrace π selected L vl vr)
          ∂Measure.pi fun _ => paperMeasure := by
      apply integral_congr_ae
      filter_upwards with vl
      unfold R324TwoHalfTerminalData.terminalMarkedPhysicalCore
        terminalMarkedCrossFactor
      simp only [R324TwoHalfTerminalData.ofTraces]
      ring
    _ =
        (rightTrace.terminalPrefix.residualIntegrand
            ρ ε z w
            (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
          (∫ vl,
            (leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              terminalMarkedCrossFactor
                leftTrace rightTrace π selected L vl vr
            ∂Measure.pi fun _ => paperMeasure) := by
      simpa only using
        (integral_const_mul
          (μ := Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure)
          (rightTrace.terminalPrefix.residualIntegrand
              ρ ε z w
              (rightTrace.terminalPrefix.reconstruct vr) : ℂ)
          (fun vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4 =>
            (leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              terminalMarkedCrossFactor
                leftTrace rightTrace π selected L vl vr))

/-- **Full exact bridge: two physical within-half traces to the literal
initial nested cross prefix.**

Only integrability facts are assumed.  The equality itself is derived from
the genuine local collapse identities, Fubini, and the proved
measure-preserving carrier equivalence. -/
theorem twoHalf_lamEps_pow_integral_eq_initialNested
    (leftTrace :
      R324WithinHalfWeightedTrace x y leftRes)
    (rightTrace :
      R324WithinHalfWeightedTrace z w rightRes)
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (L : ℝ)
    (hleft :
      ∀ vr : rightRes.SurvivingCoordinate → T4,
        leftTrace.WeightedIntegrableAlong
          (fun vl =>
            terminalMarkedCrossFactor
              leftTrace rightTrace π selected L
              vl (rightTrace.terminalProjection vr)))
    (hright :
      rightTrace.WeightedIntegrableAlong
        (fun vr =>
          ∫ vl :
              leftTrace.terminalPrefix.SurvivingCoordinate → T4,
            ((leftTrace.terminalPrefix.residualIntegrand
                ρ ε x y
                (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
              terminalMarkedCrossFactor
                leftTrace rightTrace π selected L vl vr)
            ∂Measure.pi fun _ => paperMeasure))
    (hterminal :
      Integrable
        ((R324TwoHalfTerminalData.ofTraces
          leftTrace rightTrace).terminalMarkedPhysicalCore
            π selected L x y z w)
        ((Measure.pi fun _ :
            leftTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure).prod
          (Measure.pi fun _ :
            rightTrace.terminalPrefix.SurvivingCoordinate =>
              paperMeasure))) :
    (lamEps lam ε : ℂ) ^ (2 * rightRes.remainingOrder) *
        (∫ vr : rightRes.SurvivingCoordinate → T4,
          (rightRes.residualIntegrand ρ ε z w
              (rightRes.reconstruct vr) : ℂ) *
            ((lamEps lam ε : ℂ) ^
                (2 * leftRes.remainingOrder) *
              (∫ vl : leftRes.SurvivingCoordinate → T4,
                (leftRes.residualIntegrand ρ ε x y
                    (leftRes.reconstruct vl) : ℂ) *
                  terminalMarkedCrossFactor
                    leftTrace rightTrace π selected L
                    (leftTrace.terminalProjection vl)
                    (rightTrace.terminalProjection vr)
                ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure) =
      ∫ v :
          (R324TwoHalfTerminalData.ofTraces
            leftTrace rightTrace).NestedCoordinate π → T4,
        (R324TwoHalfTerminalData.ofTraces
          leftTrace rightTrace).initialNestedMarkedPhysicalCore
            π selected L x y z w v
        ∂Measure.pi fun _ => paperMeasure := by
  calc
    _ =
        ∫ vr :
            rightTrace.terminalPrefix.SurvivingCoordinate → T4,
          ((rightTrace.terminalPrefix.residualIntegrand
              ρ ε z w
              (rightTrace.terminalPrefix.reconstruct vr) : ℂ) *
            (∫ vl :
                leftTrace.terminalPrefix.SurvivingCoordinate → T4,
              ((leftTrace.terminalPrefix.residualIntegrand
                  ρ ε x y
                  (leftTrace.terminalPrefix.reconstruct vl) : ℂ) *
                terminalMarkedCrossFactor
                  leftTrace rightTrace π selected L vl vr)
              ∂Measure.pi fun _ => paperMeasure))
          ∂Measure.pi fun _ => paperMeasure :=
      twoHalf_lamEps_pow_integral_eq_terminal
        leftTrace rightTrace
        (terminalMarkedCrossFactor
          leftTrace rightTrace π selected L)
        hleft hright
    _ =
        ∫ p,
          (R324TwoHalfTerminalData.ofTraces
            leftTrace rightTrace).terminalMarkedPhysicalCore
              π selected L x y z w p
          ∂((Measure.pi fun _ :
              leftTrace.terminalPrefix.SurvivingCoordinate =>
                paperMeasure).prod
            (Measure.pi fun _ :
              rightTrace.terminalPrefix.SurvivingCoordinate =>
                paperMeasure)) :=
      (integral_terminalMarkedPhysicalCore_eq_iterated
        leftTrace rightTrace π selected L hterminal).symm
    _ = _ :=
      (R324TwoHalfTerminalData.ofTraces
        leftTrace rightTrace
      ).integral_terminalMarkedPhysicalCore_eq_initialNested
        π selected L x y z w

end R324WithinHalfWeightedTrace

end

end Anderson4D
