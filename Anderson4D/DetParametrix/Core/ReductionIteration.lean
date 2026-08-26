import Anderson4D.Combinatorics.PairingExtract

/-!
# Accounting for the deterministic interval-reduction loop

This file supplies the combinatorial bookkeeping used in paper §4.1
(R-322).  The endpoint extraction in `PairingExtract.lean` already
implements Definition 3.1 on a shrinking active set.  Here we prove:

* removing a fully paired subset preserves fullness of the remainder;
* the final active set remains fully paired whenever the initial set is;
* each extraction consumes at least two active indices, giving the sharp
  division-free budget `2 * numberOfReductions + finalCard ≤ initialCard`;
* for a full pairing the terminal active set is empty.

These are the termination and power-counting facts needed when each
primitive reduction contributes one factor controlled by Proposition 4.1.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-! ## Fullness under removal -/

/-- Removing a `κ`-closed fully paired set from another fully paired set
leaves a fully paired set. -/
theorem IsFullyPairedOn.sdiff
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {A B : Finset (Fin m)}
    (hA : IsFullyPairedOn κ A) (hB : IsFullyPairedOn κ B) :
    IsFullyPairedOn κ (A \ B) := by
  constructor
  · intro i hi
    exact hA.ne_of_mem (Finset.mem_sdiff.mp hi).1
  · intro i hi
    rw [Finset.mem_sdiff] at hi ⊢
    exact ⟨hA.apply_mem hi.1, hB.apply_notMem hi.2⟩

/-- At every fuel depth, a fully paired active carrier yields a fully
paired terminal carrier. -/
theorem extractAuxS_final_fullyPaired
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ (active : Finset (Fin m)),
      IsFullyPairedOn κ active →
      IsFullyPairedOn κ (extractAuxS κ fuel active).2 := by
  induction fuel with
  | zero =>
      intro active hactive
      simpa using hactive
  | succ fuel ih =>
      intro active hactive
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAuxS_succ_pos fuel h]
        apply ih
        exact hactive.sdiff
          (selectRel_isRelFullyPaired κ active h).isFullyPairedOn
      · rw [extractAuxS_succ_neg fuel h]
        exact hactive

/-! ## Closure and singles under removal -/

/-- The extraction loop preserves closure under the pairing map, without
requiring the active carrier to contain no singles. -/
theorem extractAuxS_final_apply_mem
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ (active : Finset (Fin m)),
      (∀ i ∈ active, κ i ∈ active) →
      ∀ i ∈ (extractAuxS κ fuel active).2,
        κ i ∈ (extractAuxS κ fuel active).2 := by
  induction fuel with
  | zero =>
      intro active hclosed i hi
      exact hclosed i hi
  | succ fuel ih =>
      intro active hclosed i hi
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAuxS_succ_pos fuel h] at hi ⊢
        apply ih
        · intro j hj
          rw [Finset.mem_sdiff] at hj ⊢
          exact ⟨hclosed j hj.1,
            (selectRel_isRelFullyPaired κ active h).isFullyPairedOn
              |>.apply_notMem hj.2⟩
        · exact hi
      · rw [extractAuxS_succ_neg fuel h] at hi ⊢
        exact hclosed i hi

/-- A fixed point cannot lie in a fully paired block, so any single
which is initially active survives every extraction step. -/
theorem mem_extractAuxS_final_of_mem_singles
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ (active : Finset (Fin m)) (i : Fin m),
      i ∈ active → i ∈ κ.singles →
      i ∈ (extractAuxS κ fuel active).2 := by
  induction fuel with
  | zero =>
      intro active i hi _
      exact hi
  | succ fuel ih =>
      intro active i hi hiSingle
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAuxS_succ_pos fuel h]
        apply ih
        · rw [Finset.mem_sdiff]
          refine ⟨hi, ?_⟩
          intro hiBlock
          exact
            (selectRel_isRelFullyPaired κ active h).isFullyPairedOn
              |>.ne_of_mem hiBlock
              (PartialPairing.mem_singles.mp hiSingle)
        · exact hiSingle
      · rw [extractAuxS_succ_neg fuel h]
        exact hi

/-- The terminal active carrier is closed under every nontrivial pair
(and also under fixed points). -/
theorem finalActive_apply_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    {i : Fin m} (hi : i ∈ finalActive κ) :
    κ i ∈ finalActive κ := by
  exact extractAuxS_final_apply_mem κ m Finset.univ
    (fun _ _ => Finset.mem_univ _) i hi

/-- Every single survives the Definition 3.1 extraction loop. -/
theorem singles_subset_finalActive
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    κ.singles ⊆ finalActive κ := by
  intro i hi
  exact mem_extractAuxS_final_of_mem_singles
    κ m Finset.univ i (Finset.mem_univ _) hi

/-! ## Exact reduction budget -/

/-- Every extraction removes at least two active indices.  The final-card
term is retained, making this an induction invariant rather than merely a
terminal estimate. -/
theorem extractAuxS_reduction_budget
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      2 * (extractAuxS κ fuel active).1.length +
          (extractAuxS κ fuel active).2.card ≤
        active.card := by
  induction fuel with
  | zero =>
      intro active
      simp
  | succ fuel ih =>
      intro active
      by_cases h : ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAuxS_succ_pos fuel h]
        dsimp only [List.length_cons]
        have hchild := ih
          (active \ relIcc active (selectRel κ active h).1
            (selectRel κ active h).2)
        have hshrink := card_sdiff_relIcc_add_two_le
          (selectRel_isRelFullyPaired κ active h)
        omega
      · rw [extractAuxS_succ_neg fuel h]
        simp

/-- Public budget for Definition 3.1 extraction:
`2 * |extract κ| + |finalActive κ| ≤ m`. -/
theorem extract_reduction_budget
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    2 * (extract κ).length + (finalActive κ).card ≤ m := by
  have h := extractAuxS_reduction_budget κ m Finset.univ
  rw [← extract_eq_extractAuxS_fst] at h
  simpa [finalActive] using h

/-- In particular the number of primitive interval reductions is at most
half the perturbative order. -/
theorem extract_length_le_half
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extract κ).length ≤ m / 2 := by
  have h := extract_reduction_budget κ
  omega

/-! ## Full pairings leave no residual active indices -/

private theorem exists_relFullyPaired_of_nonempty
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (hne : active.Nonempty) (hfull : IsFullyPairedOn κ active) :
    ∃ a b, IsRelFullyPaired κ active a b := by
  let a : Fin m := active.min' hne
  let b : Fin m := active.max' hne
  have ha : a ∈ active := Finset.min'_mem active hne
  have hb : b ∈ active := Finset.max'_mem active hne
  have hab : a ≤ b := (Finset.min'_le active b hb).trans le_rfl
  have hrel : relIcc active a b = active := by
    ext i
    rw [mem_relIcc]
    constructor
    · exact fun hi => hi.1
    · intro hi
      exact ⟨hi, Finset.min'_le active i hi,
        Finset.le_max' active i hi⟩
  exact ⟨a, b, ha, hb, hab, by simpa [hrel] using hfull⟩

/-- A full pairing is exhausted completely by the relative interval
extraction loop. -/
theorem finalActive_eq_empty_of_full
    {m : ℕ} {κ : PartialPairing (Fin m)} (hκ : κ.IsFull) :
    finalActive κ = ∅ := by
  have hterminal := extract_fuel_sufficient κ
  have hfullInitial :
      IsFullyPairedOn κ (Finset.univ : Finset (Fin m)) :=
    isFullyPairedOn_univ_iff.mpr hκ
  have hfullFinal :
      IsFullyPairedOn κ (finalActive κ) :=
    extractAuxS_final_fullyPaired κ m Finset.univ hfullInitial
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  exact hterminal
    (exists_relFullyPaired_of_nonempty hne hfullFinal)

/-- For a full pairing, the accounting identity has no terminal residue. -/
theorem two_mul_extract_length_le_of_full
    {m : ℕ} {κ : PartialPairing (Fin m)} (hκ : κ.IsFull) :
    2 * (extract κ).length ≤ m := by
  have h := extract_reduction_budget κ
  rw [finalActive_eq_empty_of_full hκ] at h
  simpa using h

end Anderson4D
