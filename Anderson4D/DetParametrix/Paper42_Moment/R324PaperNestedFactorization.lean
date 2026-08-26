import Anderson4D.DetParametrix.Paper42_Moment.R324PaperCrossPair
import Anderson4D.DetParametrix.Paper42_Moment.R324ConcretePhaseATraceAssembly

/-!
# The nested context factorization, from the schedule head

Paper: R-324 — §4.2 Step 3, factorization inputs for the nested reduction

`R324InitialNestedContextFactorization.of_initial_marked_head` builds the
factorization Step 3's end-to-end handoff needs, but only when the *marked*
block is already the first block of the nested schedule.  For Steps 2–3
that is not a restriction, for two reasons proved elsewhere:

* the marking is inert there.  Steps 2–3 are about (4.18), which carries no
  frequency projection at all, and
  `r324MarkedPairingCovarianceProductOn_eq_plain` shows the marked
  covariance product is the plain one at any nonpositive threshold, for
  *any* distinguished endpoint.  So the choice of `selected` is free.
* every block of the schedule is some slot's marked block
  (`exists_selected_markedBlock_eq`), because paper Step 3(b) makes the
  blocks straddle the cut and a cross-cut relatively primitive block must
  contain a cross pair.

Choosing the slot inside the schedule *head* therefore satisfies the
constructor's hypothesis outright.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Every block of the nested cross schedule is the marked block of some
residual covariance slot: its three certificates come from membership in
the canonical residual decomposition, and the cross-cut witness is the
`crossCut` field, which paper Step 3(b) supplies. -/
theorem R324NestedCrossBlock.exists_markedSlot
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    (block : R324NestedCrossBlock κp κm π) :
    ∃ selected : R324ResidualCovarianceSlot κp,
      r324MarkedResidualBlock κp κm π selected = block.carrier := by
  obtain ⟨hplain, _hne⟩ :=
    mem_nonemptyMomentResidualCollapseBlocks.mp block.mem_schedule
  obtain ⟨l, hl, r, hr, hlm, hrm⟩ := block.crossCut
  exact
    exists_selected_markedBlock_eq κp κm π block.mem_schedule
      (momentResidualCollapseBlock_isFullyPairedOn_of_mem κp κm π
        block.carrier hplain)
      (momentResidualCollapseBlock_isRelPrimitiveOn_of_mem κp κm π
        block.carrier hplain)
      hl hr hlm hrm

/-- **The factorization Step 3's handoff consumes, with no restriction on
the marked carrier.**

Given the schedule head, choose the covariance slot inside it; the marked
block is then the head, and `of_initial_marked_head` applies.  The joint
integrability of the physical core follows from the fixed-scale recipe in
`docs/R324_PAPER_PROOF.md`. -/
theorem exists_r324InitialNestedContextFactorization_of_head
    {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {terminal : R324TwoHalfTerminalData ρ lam ε κp κm}
    {L : ℝ} {x y z w : T4}
    (head : R324NestedCrossBlock κp κm π)
    (tail : List (R324NestedCrossBlock κp κm π))
    (hremaining :
      (R324NestedCrossResidualPrefix.initial κp κm π).remaining =
        head :: tail)
    (hphysical :
      ∀ selected : R324ResidualCovarianceSlot κp,
        Integrable
          (terminal.initialNestedMarkedPhysicalCore
            π selected L x y z w)
          (Measure.pi fun _ :
            terminal.NestedCoordinate π => paperMeasure)) :
    ∃ selected : R324ResidualCovarianceSlot κp,
      Nonempty
        (R324InitialNestedContextFactorization
          ρ lam ε κp κm π selected terminal L x y z w) := by
  obtain ⟨selected, hsel⟩ := head.exists_markedSlot
  exact
    ⟨selected,
      ⟨R324InitialNestedContextFactorization.of_initial_marked_head
        head tail hremaining hsel.symm (hphysical selected)⟩⟩

end

end Anderson4D
