import Anderson4D.Continuum.Discretization
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkerPreservingResidualCollapse

/-!
# Finite cell decomposition with one open pairing edge

For the selected R-324 covariance edge the two endpoint cells must remain
independent.  Every other covariance edge retains the copied-cell
assignment used in the proof of Proposition 4.1.  This file constructs
that mixed assignment as an honest finite measurable partition and
specializes it to the genuine marked residual cross edge.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- A lattice word respects every pairing edge except the two endpoints
of one selected edge. -/
def RespectsPairingExcept
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (y : Fin m → Z4) : Prop :=
  ∀ i : Fin m, i ≠ a → i ≠ b →
    y (κ i) = y i

instance instDecidableRespectsPairingExcept
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (y : Fin m → Z4) :
    Decidable (RespectsPairingExcept κ a b y) :=
  inferInstanceAs
    (Decidable
      (∀ i : Fin m, i ≠ a → i ≠ b →
        y (κ i) = y i))

/-- Use the actual floor cells at the selected endpoints and the usual
copied anchor cell everywhere else. -/
def openEdgeCellAssignment
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (ε : ℝ)
    (x : Fin m → T4) : Fin m → Z4 :=
  fun i =>
    if i = a then torusFloorCell ε (x i)
    else if i = b then torusFloorCell ε (x i)
    else pairedCellAssignment κ ε x i

@[simp]
theorem openEdgeCellAssignment_left
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (ε : ℝ)
    (x : Fin m → T4) :
    openEdgeCellAssignment κ a b ε x a =
      torusFloorCell ε (x a) := by
  simp [openEdgeCellAssignment]

@[simp]
theorem openEdgeCellAssignment_right
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (ε : ℝ)
    (x : Fin m → T4) :
    openEdgeCellAssignment κ a b ε x b =
      torusFloorCell ε (x b) := by
  simp [openEdgeCellAssignment]

/-- No unselected endpoint can be paired into the selected edge. -/
theorem pairing_ne_selected_of_ne_endpoints
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b i : Fin m) (hκab : κ a = b)
    (hia : i ≠ a) (hib : i ≠ b) :
    κ i ≠ a ∧ κ i ≠ b := by
  have hκba : κ b = a := by
    rw [← hκab]
    exact κ.apply_apply a
  constructor
  · intro h
    have hi := congrArg κ h
    rw [κ.apply_apply, hκab] at hi
    exact hib hi
  · intro h
    have hi := congrArg κ h
    rw [κ.apply_apply, hκba] at hi
    exact hia hi

/-- Every unselected edge still receives one copied label. -/
theorem openEdgeCellAssignment_respectsExcept
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b)
    (ε : ℝ) (x : Fin m → T4) :
    RespectsPairingExcept κ a b
      (openEdgeCellAssignment κ a b ε x) := by
  intro i hia hib
  obtain ⟨hκia, hκib⟩ :=
    pairing_ne_selected_of_ne_endpoints
      κ a b i hκab hia hib
  simp only [openEdgeCellAssignment,
    hia, hib, hκia, hκib, ↓reduceIte]
  exact pairedCellAssignment_apply κ ε x i

/-- The mixed assignment is measurable. -/
theorem measurable_openEdgeCellAssignment
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (ε : ℝ) :
    Measurable (openEdgeCellAssignment κ a b ε) := by
  apply measurable_pi_lambda
  intro i
  by_cases hia : i = a
  · subst i
    simp only [openEdgeCellAssignment, ↓reduceIte]
    change Measurable
      (torusFloorCell ε ∘
        (fun x : Fin m → T4 => x a))
    exact
      (measurable_torusFloorCell ε).comp
        (measurable_pi_apply a)
  · by_cases hib : i = b
    · subst i
      simp only [openEdgeCellAssignment, hia,
        ↓reduceIte]
      change Measurable
        (torusFloorCell ε ∘
          (fun x : Fin m → T4 => x b))
      exact
        (measurable_torusFloorCell ε).comp
          (measurable_pi_apply b)
    · simp only [openEdgeCellAssignment,
        hia, hib, ↓reduceIte]
      exact
        (measurable_torusFloorCell ε).comp
          (measurable_pi_apply (pairingAnchor κ i))

/-- Every mixed assignment lies in the finite torus grid. -/
theorem openEdgeCellAssignment_mem_piFinset
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) {ε : ℝ} (hε : 0 < ε)
    (x : Fin m → T4) :
    openEdgeCellAssignment κ a b ε x ∈
      Fintype.piFinset (fun _ : Fin m => torusGrid ε) := by
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hia : i = a
  · subst i
    simp only [openEdgeCellAssignment, ↓reduceIte]
    exact torusFloorCell_mem_torusGrid hε _
  · by_cases hib : i = b
    · subst i
      simp only [openEdgeCellAssignment, hia,
        ↓reduceIte]
      exact torusFloorCell_mem_torusGrid hε _
    · simp only [openEdgeCellAssignment, hia, hib,
        ↓reduceIte, pairedCellAssignment]
      exact torusFloorCell_mem_torusGrid hε _

/-- The actual finite measurable partition for one open edge.  Its index
set already enforces the unmarked copied-label predicate, so no later
enlargement is needed. -/
def openEdgeTorusGridCells
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b)
    (ε : ℝ) (hε : 0 < ε) :
    FiniteMeasurableCells (Fin m → T4) (Fin m → Z4) where
  indices :=
    (Fintype.piFinset
      (fun _ : Fin m => torusGrid ε)).filter
        (RespectsPairingExcept κ a b)
  index := openEdgeCellAssignment κ a b ε
  range_subset := fun x =>
    Finset.mem_filter.mpr
      ⟨openEdgeCellAssignment_mem_piFinset
          κ a b hε x,
        openEdgeCellAssignment_respectsExcept
          κ a b hκab ε x⟩
  measurable_fiber := fun y =>
    (measurable_openEdgeCellAssignment κ a b ε)
      (measurableSet_singleton y)

/-- Exact finite cell decomposition for every integrable real
majorant on the physical coordinates of one open pairing edge. -/
theorem integral_eq_sum_openEdgeTorusGridCells
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b)
    (ε : ℝ) (hε : 0 < ε)
    (f : (Fin m → T4) → ℝ)
    (hf : Integrable f
      (Measure.pi fun _ : Fin m => paperMeasure)) :
    (∫ x, f x
        ∂(Measure.pi fun _ : Fin m => paperMeasure)) =
      ∑ y ∈ (openEdgeTorusGridCells
          κ a b hκab ε hε).indices,
        ∫ x in
            (openEdgeTorusGridCells
              κ a b hκab ε hε).index ⁻¹' {y},
          f x
          ∂(Measure.pi fun _ : Fin m => paperMeasure) := by
  let P :=
    openEdgeTorusGridCells κ a b hκab ε hε
  rw [← setIntegral_univ,
    ← P.iUnion_fibers]
  exact integral_biUnion_finset P.indices
    (fun i _hi => P.measurable_fiber i)
    P.pairwiseDisjoint
    (fun _i _hi => hf.integrableOn)

/-! ## Specialization to the genuine selected residual edge -/

/-- The marked residual cross edge supplies the exact open-edge cell
partition needed by the selected configuration fibre. -/
def r324MarkedResidualOpenEdgeCells
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε) :
    FiniteMeasurableCells
      (Fin (2 * m) → T4) (Fin (2 * m) → Z4) :=
  openEdgeTorusGridCells
    (momentCombinedPairing κp κm π)
    (r324ResidualMarkedLowerEndpoint selected)
    (r324ResidualMarkedUpperEndpoint π selected)
    (momentCombinedPairing_r324ResidualMarkedLowerEndpoint
      κp κm π selected)
    ε hε

/-- Every cell word occurring in the genuine selected residual
partition respects every unmarked covariance edge. -/
theorem r324MarkedResidualOpenEdgeCells_index_respects
    {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (ε : ℝ) (hε : 0 < ε)
    (x : Fin (2 * m) → T4) :
    RespectsPairingExcept
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (r324ResidualMarkedUpperEndpoint π selected)
      ((r324MarkedResidualOpenEdgeCells
        κp κm π selected ε hε).index x) := by
  exact
    openEdgeCellAssignment_respectsExcept
      (momentCombinedPairing κp κm π)
      (r324ResidualMarkedLowerEndpoint selected)
      (r324ResidualMarkedUpperEndpoint π selected)
      (momentCombinedPairing_r324ResidualMarkedLowerEndpoint
        κp κm π selected)
      ε x

end

end Anderson4D
