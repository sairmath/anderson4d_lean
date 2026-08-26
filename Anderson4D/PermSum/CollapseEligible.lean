import Anderson4D.PermSum.Statements

/-!
# Eligible branches for the Proposition 5.9 collapse

This file formalizes the choice made in (5.40).  Eligibility is written
without division:

`8 * N'_v ≤ N_{v⁺}`.

If eligible branches exist, a branch of maximal address length is a valid
"lowest" choice.  The choice need not be unique, and none of the later
arguments should depend on a tie-breaking convention.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

/-- Division-free form of the collapse condition (5.40). -/
def CollapseEligible {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (v : VPos t) : Prop :=
  v ∈ nonrootBranches t ∧
    8 * accumulatedScale Nm mu v ≤ scaleN Nm (parentV v)

instance {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (v : VPos t) : Decidable (CollapseEligible Nm mu v) :=
  by
    unfold CollapseEligible
    infer_instance

/-- The finite set of branches satisfying (5.40). -/
def eligibleBranches {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    Finset (VPos t) :=
  (nonrootBranches t).filter fun v =>
    8 * accumulatedScale Nm mu v ≤ scaleN Nm (parentV v)

@[simp] theorem mem_eligibleBranches_iff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (v : VPos t) :
    v ∈ eligibleBranches Nm mu ↔ CollapseEligible Nm mu v := by
  simp [eligibleBranches, CollapseEligible]

/-- A lowest eligible branch has no strictly lower eligible branch. -/
def IsLowestCollapseEligible {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (v : VPos t) : Prop :=
  CollapseEligible Nm mu v ∧
    ∀ u ∈ branchNodesUnder v, u ≠ v →
      ¬CollapseEligible Nm mu u

/-- Any nonempty eligible set has a lowest member.  Maximizing address length
is enough because strict descendants have strictly longer addresses. -/
theorem exists_lowestCollapseEligible {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hne : (eligibleBranches Nm mu).Nonempty) :
    ∃ v : VPos t, IsLowestCollapseEligible Nm mu v := by
  classical
  obtain ⟨v, hv, hvmax⟩ :=
    Finset.exists_max_image
      (eligibleBranches Nm mu) (fun u => u.1.length) hne
  refine ⟨v, (mem_eligibleBranches_iff Nm mu v).mp hv, ?_⟩
  intro u hu huv huelig
  have hue :
      u ∈ eligibleBranches Nm mu :=
    (mem_eligibleBranches_iff Nm mu u).mpr huelig
  have hlenMax : u.1.length ≤ v.1.length := hvmax u hue
  have hprefix : v.1 <+: u.1 := by
    simpa [branchNodesUnder] using (Finset.mem_filter.mp hu).2
  have hlenPrefix : v.1.length ≤ u.1.length := hprefix.length_le
  have hleneq : v.1.length = u.1.length :=
    Nat.le_antisymm hlenPrefix hlenMax
  have hpaths : v.1 = u.1 := hprefix.eq_of_length hleneq
  apply huv
  exact Subtype.ext hpaths.symm

/-- An eligible branch's accumulated scale is bounded by its parent scale;
the stronger factor-eight inequality is retained in `CollapseEligible`. -/
theorem eligible_accumulated_le_parent {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} {v : VPos t}
    (hv : CollapseEligible Nm mu v) :
    accumulatedScale Nm mu v ≤ scaleN Nm (parentV v) := by
  rcases hv with ⟨_, hv⟩
  omega

/-- If there is no eligible branch, the whole tree satisfies the single-scale
condition (5.38).  Equality is deliberately counted as eligible. -/
theorem noEligible_implies_singleScale {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hempty : eligibleBranches Nm mu = ∅) :
    SatisfiesSingleScaleCondition Nm mu := by
  intro v hv
  have hnot :
      ¬(8 * accumulatedScale Nm mu v ≤ scaleN Nm (parentV v)) := by
    intro h
    have :
        v ∈ eligibleBranches Nm mu := by
      exact (mem_eligibleBranches_iff Nm mu v).mpr ⟨hv, h⟩
    rw [hempty] at this
    simp at this
  omega

/-- Every scale carried by a marking is dyadic, including totalized junk
values away from branch nodes. -/
theorem scaleN_isDyadicNat {t : PlaneTree}
    (Nm : HeppMarking t) (v : VPos t) :
    IsDyadicNat (scaleN Nm v) := by
  exact ⟨Nm.Nexp v, rfl⟩

end Anderson4D
