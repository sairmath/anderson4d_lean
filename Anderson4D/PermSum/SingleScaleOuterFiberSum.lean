import Anderson4D.PermSum.SingleScaleInterpolatedGain
import Anderson4D.PermSum.SingleScaleOuterAssembly

set_option warningAsError true
set_option autoImplicit false

/-!
# Outer aggregation for a fixed coarse class word

This file combines three finite ledgers used after the fixed-`(N,X)` inner
estimate:

* the number of valid `(N,X)` refinements of a fixed active-`P` word;
* the anchor-dependent oriented active-`P` sequence weight;
* the global simple/compound majority payoff.

The positional exceptional set is independent of the analytic class word.
Consequently, an anchor selected separately for every refinement can first
be enlarged to the sum over every anchor and every active-`P` word.  The
remaining refinement cardinal is exactly paper (5.79).
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Every original-edge active-`P` weight is nonnegative. -/
theorem anchoredOrientedActivePWeight_nonneg
    (theta : ℝ)
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {n : ℕ}
    (E : Finset (Fin n)) (anchor : Fin (n + 1))
    (w : Fin (n + 1) → ActivePClass Nm mu) :
    0 ≤ anchoredOrientedActivePWeight theta E anchor w := by
  unfold anchoredOrientedActivePWeight
  apply Finset.prod_nonneg
  intro j _hj
  unfold anchoredOrientedActivePEdgeGain anchoredActivePEdgeGain
  split
  · exact le_min zero_le_one (Real.rpow_nonneg (by positivity) _)
  · exact le_min zero_le_one (Real.rpow_nonneg (by positivity) _)

/--
An arbitrary anchor choice for every member of a finite family costs no
more than the family cardinal times the sum over all anchors and all words.
This is the abstract enlargement used before applying the sequence theorem.
-/
theorem sum_anchorSelected_orientedActivePWeight_le
    (theta : ℝ)
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {n : ℕ}
    (s : Finset (Fin (n + 1) → ActiveNXClass Nm mu))
    (chooseAnchor :
      (Fin (n + 1) → ActiveNXClass Nm mu) → Fin (n + 1))
    (E : Fin (n + 1) → Finset (Fin n)) :
    (∑ x ∈ s,
        anchoredOrientedActivePWeight theta
          (E (chooseAnchor x)) (chooseAnchor x)
          (fun i => activeNXToP Nm mu (x i))) ≤
      (s.card : ℝ) *
        ∑ anchor : Fin (n + 1),
          ∑ w : Fin (n + 1) → ActivePClass Nm mu,
            anchoredOrientedActivePWeight theta
              (E anchor) anchor w := by
  let total : ℝ :=
    ∑ anchor : Fin (n + 1),
      ∑ w : Fin (n + 1) → ActivePClass Nm mu,
        anchoredOrientedActivePWeight theta (E anchor) anchor w
  have hterm :
      ∀ x : Fin (n + 1) → ActiveNXClass Nm mu,
        anchoredOrientedActivePWeight theta
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i)) ≤
          total := by
    intro x
    have hword :
        anchoredOrientedActivePWeight theta
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i)) ≤
          ∑ w : Fin (n + 1) → ActivePClass Nm mu,
            anchoredOrientedActivePWeight theta
              (E (chooseAnchor x)) (chooseAnchor x) w := by
      apply Finset.single_le_sum
      · intro w _hw
        exact anchoredOrientedActivePWeight_nonneg theta
          (E (chooseAnchor x)) (chooseAnchor x) w
      · exact Finset.mem_univ _
    calc
      anchoredOrientedActivePWeight theta
          (E (chooseAnchor x)) (chooseAnchor x)
          (fun i => activeNXToP Nm mu (x i)) ≤
          ∑ w : Fin (n + 1) → ActivePClass Nm mu,
            anchoredOrientedActivePWeight theta
              (E (chooseAnchor x)) (chooseAnchor x) w :=
        hword
      _ ≤ total := by
        dsimp only [total]
        exact Finset.single_le_sum
          (f := fun anchor =>
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredOrientedActivePWeight theta (E anchor) anchor w)
          (fun anchor _hanchor => by
            apply Finset.sum_nonneg
            intro w _hw
            exact anchoredOrientedActivePWeight_nonneg theta
              (E anchor) anchor w)
          (Finset.mem_univ (chooseAnchor x))
  calc
    (∑ x ∈ s,
        anchoredOrientedActivePWeight theta
          (E (chooseAnchor x)) (chooseAnchor x)
          (fun i => activeNXToP Nm mu (x i))) ≤
        ∑ _x ∈ s, total := by
      apply Finset.sum_le_sum
      intro x _hx
      exact hterm x
    _ = (s.card : ℝ) * total := by simp
    _ = (s.card : ℝ) *
        ∑ anchor : Fin (n + 1),
          ∑ w : Fin (n + 1) → ActivePClass Nm mu,
            anchoredOrientedActivePWeight theta
              (E anchor) anchor w := rfl

/--
Length-polymorphic form of paper (5.79).  The paper-facing theorem fixes
the domain to `Fin (totalMultiplicity mu)`; this form is convenient after
writing that length syntactically as `(totalMultiplicity mu - 1) + 1`.
-/
theorem paper579_conditional_classWord_count_of_length
    {t : PlaneTree} {M : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (y : Fin M → ActivePClass Nm mu)
    (hy : y ∈ validWords (M := M) (activePMultiplicity Nm mu)) :
    (validRefinements
      (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y).card =
      ∏ P ∈ pCarrier Nm mu,
        Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) := by
  have hmass : ∀ P : ActivePClass Nm mu,
      (∑ a :
          {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P},
        activeNXMultiplicity Nm mu a.1) =
        Fintype.card {j : Fin M // y j = P} := by
    intro P
    calc
      (∑ a :
          {a : ActiveNXClass Nm mu // activeNXToP Nm mu a = P},
        activeNXMultiplicity Nm mu a.1) =
          activePMultiplicity Nm mu P :=
        activeNX_fiber_mass Nm mu P
      _ = ((Finset.univ : Finset (Fin M)).filter
          fun j => y j = P).card :=
        ((Finset.mem_filter.mp hy).2 P).symm
      _ = Fintype.card {j : Fin M // y j = P} := by
        rw [Fintype.card_subtype]
  calc
    (validRefinements
      (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y).card =
        ∏ P : ActivePClass Nm mu,
          Nat.multinomial Finset.univ
            (fun a :
              {a : ActiveNXClass Nm mu //
                activeNXToP Nm mu a = P} =>
              activeNXMultiplicity Nm mu a.1) :=
      card_validRefinements
        (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y hmass
    _ = ∏ P : ActivePClass Nm mu,
        Nat.multinomial (nxAtP Nm mu P.1) (multiplicityNX Nm mu) := by
      apply Finset.prod_congr rfl
      intro P _hP
      exact activeNX_fiber_multinomial Nm mu P
    _ = ∏ P ∈ pCarrier Nm mu,
        Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu) := by
      exact Finset.prod_coe_sort
        (pCarrier Nm mu)
        (fun P : ℕ =>
          Nat.multinomial (nxAtP Nm mu P) (multiplicityNX Nm mu))

set_option maxHeartbeats 800000 in
/--
Outer aggregation for one valid active-`P` word.

Each valid `(N,X)` refinement may choose its own anchor.  Both phase flags
are fixed to `false`; the interpolated exceptional set is the purely
positional one, hence independent of the refinement word.  The resulting
weighted refinement sum is bounded by one exponential constant times the
global original outer-leaf payoff.
-/
theorem fixedPWord_refinement_orientedWeight_le_originalPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)),
        let n := totalMultiplicity mu - 1
        ∀ (y : Fin (n + 1) → ActivePClass Nm mu)
          (_hy : y ∈ validWords (M := n + 1)
            (activePMultiplicity Nm mu))
          (chooseAnchor :
            (Fin (n + 1) → ActiveNXClass Nm mu) → Fin (n + 1))
          (O : Finset (AdjacentIndex (n + 1))),
          (∑ x ∈ validRefinements
              (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (finAnchorPositionalInterpolatedExceptionalFinEdges
                false false (chooseAnchor x) O)
              (chooseAnchor x)
              (fun i => activeNXToP Nm mu (x i))) ≤
            C ^ totalMultiplicity mu *
              ∏ l : HeppLeaf t,
                originalOuterLeafPayoff Nm mu compound l := by
  obtain ⟨Cseq, hCseq, hseq⟩ :=
    finAnchorPositional_orientedActiveP_totalMultiplicity_oneSixteenth_le
  obtain ⟨Couter, hCouter, houter⟩ :=
    globalOuterMajorityRefinement
  let C : ℝ := Cseq * Couter
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro t ht hroot Nm mu compound
  dsimp only
  intro y hy chooseAnchor O
  let n := totalMultiplicity mu - 1
  let refinements :=
    validRefinements
      (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y
  let E : Fin (n + 1) → Finset (Fin n) :=
    fun anchor =>
      finAnchorPositionalInterpolatedExceptionalFinEdges
        false false anchor O
  have hlen : n + 1 = totalMultiplicity mu := by
    dsimp [n]
    exact Nat.sub_add_cancel
      (le_trans (by omega) (two_le_totalMultiplicity mu))
  have htermBound :
      ∀ x : Fin (n + 1) → ActiveNXClass Nm mu,
        anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i)) ≤
          Cseq ^ totalMultiplicity mu := by
    intro x
    have hselected :
        anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i)) ≤
          ∑ anchor : Fin (n + 1),
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (E anchor) anchor w := by
      calc
        anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i)) ≤
            ∑ w : Fin (n + 1) → ActivePClass Nm mu,
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (E (chooseAnchor x)) (chooseAnchor x) w := by
          apply Finset.single_le_sum
          · intro w _hw
            exact anchoredOrientedActivePWeight_nonneg (1 / 16 : ℝ)
              (E (chooseAnchor x)) (chooseAnchor x) w
          · exact Finset.mem_univ _
        _ ≤
            ∑ anchor : Fin (n + 1),
              ∑ w : Fin (n + 1) → ActivePClass Nm mu,
                anchoredOrientedActivePWeight (1 / 16 : ℝ)
                  (E anchor) anchor w := by
          exact Finset.single_le_sum
            (f := fun anchor =>
              ∑ w : Fin (n + 1) → ActivePClass Nm mu,
                anchoredOrientedActivePWeight (1 / 16 : ℝ)
                  (E anchor) anchor w)
            (fun anchor _hanchor => by
              apply Finset.sum_nonneg
              intro w _hw
              exact anchoredOrientedActivePWeight_nonneg (1 / 16 : ℝ)
                (E anchor) anchor w)
            (Finset.mem_univ (chooseAnchor x))
    have hall :=
      hseq Nm mu
        (fun _anchor => false) (fun _anchor => false)
        x O
    exact hselected.trans (by simpa only [E] using hall)
  have hrefinement :
      (∑ x ∈ refinements,
          anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i))) ≤
        (refinements.card : ℝ) *
          Cseq ^ totalMultiplicity mu := by
    calc
      (∑ x ∈ refinements,
          anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i))) ≤
          ∑ _x ∈ refinements, Cseq ^ totalMultiplicity mu := by
        apply Finset.sum_le_sum
        intro x _hx
        exact htermBound x
      _ = (refinements.card : ℝ) *
          Cseq ^ totalMultiplicity mu := by simp
  have hcardNat :
      refinements.card =
        ∏ P ∈ pCarrier Nm mu,
          Nat.multinomial (nxAtP Nm mu P)
            (multiplicityNX Nm mu) := by
    dsimp only [refinements]
    exact paper579_conditional_classWord_count_of_length Nm mu y hy
  have hcardReal :
      (refinements.card : ℝ) =
        ∏ P ∈ pCarrier Nm mu,
          (Nat.multinomial (nxAtP Nm mu P)
            (multiplicityNX Nm mu) : ℝ) := by
    exact_mod_cast hcardNat
  have houterBound :
      (∏ P ∈ pCarrier Nm mu,
          (Nat.multinomial (nxAtP Nm mu P)
            (multiplicityNX Nm mu) : ℝ)) ≤
        Couter ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l :=
    houter ht hroot Nm mu compound
  calc
    (∑ x ∈ validRefinements
        (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
      anchoredOrientedActivePWeight (1 / 16 : ℝ)
        (finAnchorPositionalInterpolatedExceptionalFinEdges
          false false (chooseAnchor x) O)
        (chooseAnchor x)
        (fun i => activeNXToP Nm mu (x i))) =
        ∑ x ∈ refinements,
          anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i)) := by
      rfl
    _ ≤ (refinements.card : ℝ) *
          Cseq ^ totalMultiplicity mu :=
      hrefinement
    _ =
        (∏ P ∈ pCarrier Nm mu,
          (Nat.multinomial (nxAtP Nm mu P)
            (multiplicityNX Nm mu) : ℝ)) *
          Cseq ^ totalMultiplicity mu := by rw [hcardReal]
    _ ≤
        (Couter ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l) *
          Cseq ^ totalMultiplicity mu :=
      mul_le_mul_of_nonneg_right houterBound (by positivity)
    _ =
        C ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l := by
      dsimp [C]
      rw [mul_pow]
      ring

set_option maxHeartbeats 1000000 in
/--
Global outer ledger consumed by the final single-scale assembly.

The sum is first over every valid active-`P` word and then over all valid
`(N,X)` refinements.  The refinement condition identifies the active-`P`
word of each fine word with the fixed outer word.  Since the refinement
cardinality is independent of that outer word, paper (5.79) can be pulled
out before the valid-word carrier is enlarged to all active-`P` functions.
The sequence estimate is therefore used exactly once.
-/
theorem global_refinement_orientedWeight_le_originalPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)),
        let n := totalMultiplicity mu - 1
        ∀ (chooseAnchor :
            (Fin (n + 1) → ActiveNXClass Nm mu) → Fin (n + 1))
          (O : Finset (AdjacentIndex (n + 1))),
          (∑ y ∈ validWords (M := n + 1)
              (activePMultiplicity Nm mu),
            ∑ x ∈ validRefinements
                (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (finAnchorPositionalInterpolatedExceptionalFinEdges
                  false false (chooseAnchor x) O)
                (chooseAnchor x)
                (fun i => activeNXToP Nm mu (x i))) ≤
            C ^ totalMultiplicity mu *
              ∏ l : HeppLeaf t,
                originalOuterLeafPayoff Nm mu compound l := by
  obtain ⟨Cseq, hCseq, hseq⟩ :=
    finAnchorPositional_orientedActiveP_totalMultiplicity_oneSixteenth_le
  obtain ⟨Couter, hCouter, houter⟩ :=
    globalOuterMajorityRefinement
  let C : ℝ := Cseq * Couter
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro t ht hroot Nm mu compound
  dsimp only
  intro chooseAnchor O
  let n := totalMultiplicity mu - 1
  let validP :=
    validWords (M := n + 1) (activePMultiplicity Nm mu)
  let refinements :=
    fun y : Fin (n + 1) → ActivePClass Nm mu =>
      validRefinements
        (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y
  let E : Fin (n + 1) → Finset (Fin n) :=
    fun anchor =>
      finAnchorPositionalInterpolatedExceptionalFinEdges
        false false anchor O
  let outerCount : ℝ :=
    ∏ P ∈ pCarrier Nm mu,
      (Nat.multinomial (nxAtP Nm mu P)
        (multiplicityNX Nm mu) : ℝ)
  have hfiber :
      ∀ y ∈ validP,
        (∑ x ∈ refinements y,
          anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i))) ≤
          outerCount *
            ∑ anchor : Fin (n + 1),
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (E anchor) anchor y := by
    intro y hy
    have hcardNat :
        (refinements y).card =
          ∏ P ∈ pCarrier Nm mu,
            Nat.multinomial (nxAtP Nm mu P)
              (multiplicityNX Nm mu) := by
      exact paper579_conditional_classWord_count_of_length Nm mu y hy
    have hcard :
        ((refinements y).card : ℝ) = outerCount := by
      dsimp only [outerCount]
      exact_mod_cast hcardNat
    calc
      (∑ x ∈ refinements y,
          anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (E (chooseAnchor x)) (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i))) ≤
          ∑ _x ∈ refinements y,
            ∑ anchor : Fin (n + 1),
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (E anchor) anchor y := by
        apply Finset.sum_le_sum
        intro x hx
        have hxy :
            (fun i => activeNXToP Nm mu (x i)) = y := by
          funext i
          exact (Finset.mem_filter.mp hx).2 i
        rw [hxy]
        exact Finset.single_le_sum
          (f := fun anchor =>
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E anchor) anchor y)
          (fun anchor _hanchor =>
            anchoredOrientedActivePWeight_nonneg (1 / 16 : ℝ)
              (E anchor) anchor y)
          (Finset.mem_univ (chooseAnchor x))
      _ = ((refinements y).card : ℝ) *
            ∑ anchor : Fin (n + 1),
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (E anchor) anchor y := by simp
      _ = outerCount *
            ∑ anchor : Fin (n + 1),
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (E anchor) anchor y := by rw [hcard]
  have hvalidToAll :
      (∑ y ∈ validP,
          ∑ anchor : Fin (n + 1),
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E anchor) anchor y) ≤
        ∑ y : Fin (n + 1) → ActivePClass Nm mu,
          ∑ anchor : Fin (n + 1),
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E anchor) anchor y := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ validP)
      (fun y _hy _hnot => by
        apply Finset.sum_nonneg
        intro anchor _hanchor
        exact anchoredOrientedActivePWeight_nonneg (1 / 16 : ℝ)
          (E anchor) anchor y)
  have hleafCard : 1 ≤ Fintype.card (HeppLeaf t) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    obtain ⟨cs⟩ := t
    exact le_max_left 1 (leafCountList cs)
  let l : HeppLeaf t :=
    Classical.choice
      (Fintype.card_pos_iff.mp (lt_of_lt_of_le (by omega) hleafCard))
  let a : ActiveNXClass Nm mu :=
    ⟨singleScaleSigma1 Nm mu l,
      Finset.mem_image_of_mem _ (Finset.mem_univ l)⟩
  let cls : Fin (n + 1) → ActiveNXClass Nm mu := fun _ => a
  have hsequence :
      (∑ anchor : Fin (n + 1),
          ∑ y : Fin (n + 1) → ActivePClass Nm mu,
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E anchor) anchor y) ≤
        Cseq ^ totalMultiplicity mu := by
    have h :=
      hseq Nm mu
        (fun _anchor => false) (fun _anchor => false)
        cls O
    simpa only [E] using h
  have houterBound :
      outerCount ≤
        Couter ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l := by
    dsimp only [outerCount]
    exact houter ht hroot Nm mu compound
  calc
    (∑ y ∈ validWords (M := n + 1)
        (activePMultiplicity Nm mu),
      ∑ x ∈ validRefinements
          (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
        anchoredOrientedActivePWeight (1 / 16 : ℝ)
          (finAnchorPositionalInterpolatedExceptionalFinEdges
            false false (chooseAnchor x) O)
          (chooseAnchor x)
          (fun i => activeNXToP Nm mu (x i))) =
        ∑ y ∈ validP,
          ∑ x ∈ refinements y,
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E (chooseAnchor x)) (chooseAnchor x)
              (fun i => activeNXToP Nm mu (x i)) := by
      rfl
    _ ≤ ∑ y ∈ validP,
          outerCount *
            ∑ anchor : Fin (n + 1),
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (E anchor) anchor y := by
      apply Finset.sum_le_sum
      intro y hy
      exact hfiber y hy
    _ = outerCount *
        ∑ y ∈ validP,
          ∑ anchor : Fin (n + 1),
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E anchor) anchor y := by
      rw [Finset.mul_sum]
    _ ≤ outerCount *
        ∑ y : Fin (n + 1) → ActivePClass Nm mu,
          ∑ anchor : Fin (n + 1),
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E anchor) anchor y :=
      mul_le_mul_of_nonneg_left hvalidToAll (by
        dsimp only [outerCount]
        positivity)
    _ = outerCount *
        ∑ anchor : Fin (n + 1),
          ∑ y : Fin (n + 1) → ActivePClass Nm mu,
            anchoredOrientedActivePWeight (1 / 16 : ℝ)
              (E anchor) anchor y := by
      rw [Finset.sum_comm]
    _ ≤ outerCount * Cseq ^ totalMultiplicity mu :=
      mul_le_mul_of_nonneg_left hsequence (by
        dsimp only [outerCount]
        positivity)
    _ ≤
        (Couter ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l) *
          Cseq ^ totalMultiplicity mu :=
      mul_le_mul_of_nonneg_right houterBound (by positivity)
    _ =
        C ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l := by
      dsimp [C]
      rw [mul_pow]
      ring

set_option maxHeartbeats 1000000 in
/--
The global outer ledger with an arbitrary nonnegative coefficient common
to every fine word.  This form preserves the word-independent completed
base-scale coefficient supplied by `SingleScaleAnchorScaleLedger`.
-/
theorem
    global_refinement_common_mul_orientedWeight_le_originalPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)),
        let n := totalMultiplicity mu - 1
        ∀ (chooseAnchor :
            (Fin (n + 1) → ActiveNXClass Nm mu) → Fin (n + 1))
          (O : Finset (AdjacentIndex (n + 1)))
          (common : ℝ) (_hcommon : 0 ≤ common),
          (∑ y ∈ validWords (M := n + 1)
              (activePMultiplicity Nm mu),
            ∑ x ∈ validRefinements
                (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
              common *
                anchoredOrientedActivePWeight (1 / 16 : ℝ)
                  (finAnchorPositionalInterpolatedExceptionalFinEdges
                    false false (chooseAnchor x) O)
                  (chooseAnchor x)
                  (fun i => activeNXToP Nm mu (x i))) ≤
            C ^ totalMultiplicity mu *
              (∏ l : HeppLeaf t,
                originalOuterLeafPayoff Nm mu compound l) *
              common := by
  obtain ⟨C, hC, hbound⟩ :=
    global_refinement_orientedWeight_le_originalPayoff
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu compound
  dsimp only
  intro chooseAnchor O common hcommon
  have h := hbound ht hroot Nm mu compound chooseAnchor O
  calc
    (∑ y ∈ validWords (M := totalMultiplicity mu - 1 + 1)
        (activePMultiplicity Nm mu),
      ∑ x ∈ validRefinements
          (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
        common *
          anchoredOrientedActivePWeight (1 / 16 : ℝ)
            (finAnchorPositionalInterpolatedExceptionalFinEdges
              false false (chooseAnchor x) O)
            (chooseAnchor x)
            (fun i => activeNXToP Nm mu (x i))) =
        common *
          (∑ y ∈ validWords (M := totalMultiplicity mu - 1 + 1)
              (activePMultiplicity Nm mu),
            ∑ x ∈ validRefinements
                (activeNXMultiplicity Nm mu) (activeNXToP Nm mu) y,
              anchoredOrientedActivePWeight (1 / 16 : ℝ)
                (finAnchorPositionalInterpolatedExceptionalFinEdges
                  false false (chooseAnchor x) O)
                (chooseAnchor x)
                (fun i => activeNXToP Nm mu (x i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum]
    _ ≤ common *
        (C ^ totalMultiplicity mu *
          ∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l) :=
      mul_le_mul_of_nonneg_left h hcommon
    _ =
        C ^ totalMultiplicity mu *
          (∏ l : HeppLeaf t,
            originalOuterLeafPayoff Nm mu compound l) *
          common := by ring

end XYCluster

end

end Anderson4D
