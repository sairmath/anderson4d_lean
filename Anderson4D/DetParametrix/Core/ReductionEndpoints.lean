import Anderson4D.DetParametrix.Core.ReductionIteration
import Anderson4D.DetParametrix.Core.Estimates
import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Endpoint geometry of the R-322 extraction loop

This file formalizes the structural assertion used in paper §4.1,
Step 1: the endpoint intervals selected by Definition 3.1 are pairwise
disjoint or nested.  In extraction order a later interval can only lie
strictly to the left, strictly to the right, or strictly contain the
earlier interval; it cannot cross it or lie inside the trace that has
already been removed.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- Directional laminarity for an earlier extracted interval `p` and a
later extracted interval `q`. -/
def EarlierReductionIntervalCompatible
    {m : ℕ} (p q : Fin m × Fin m) : Prop :=
  p.2 < q.1 ∨ q.2 < p.1 ∨
    (q.1 < p.1 ∧ p.2 < q.2)

/-- Symmetric disjoint-or-nested relation used by the Dyck-word
bookkeeping. -/
def ReductionIntervalsLaminar
    {m : ℕ} (p q : Fin m × Fin m) : Prop :=
  p.2 < q.1 ∨ q.2 < p.1 ∨
    (p.1 < q.1 ∧ q.2 < p.2) ∨
    (q.1 < p.1 ∧ p.2 < q.2)

theorem EarlierReductionIntervalCompatible.laminar
    {m : ℕ} {p q : Fin m × Fin m}
    (h : EarlierReductionIntervalCompatible p q) :
    ReductionIntervalsLaminar p q := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

theorem ReductionIntervalsLaminar.symm
    {m : ℕ} {p q : Fin m × Fin m}
    (h : ReductionIntervalsLaminar p q) :
    ReductionIntervalsLaminar q p := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-! ## Every selected interval has two distinct endpoints -/

private theorem selected_fst_lt_snd
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    (selectRel κ active h).1 <
      (selectRel κ active h).2 := by
  let p := selectRel κ active h
  have hp :=
    selectRel_isRelFullyPaired κ active h
  have hne : p.1 ≠ p.2 := by
    intro heq
    have hleft :
        p.1 ∈ relIcc active p.1 p.2 :=
      hp.left_mem_relIcc
    have hpair :
        κ p.1 ∈ relIcc active p.1 p.2 :=
      hp.isFullyPairedOn.apply_mem hleft
    have hbounds := (mem_relIcc.mp hpair).2
    have hk : κ p.1 = p.1 := by
      apply le_antisymm
      · simpa only [heq] using hbounds.2
      · exact hbounds.1
    exact hp.isFullyPairedOn.ne_of_mem hleft hk
  exact lt_of_le_of_ne hp.le hne

theorem extractAux_mem_fst_lt_snd
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ (active : Finset (Fin m))
      (p : Fin m × Fin m),
      p ∈ extractAux κ fuel active →
        p.1 < p.2 := by
  induction fuel with
  | zero =>
      intro active p hp
      simp at hp
  | succ fuel ih =>
      intro active p hp
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAux_succ_pos fuel h] at hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact selected_fst_lt_snd h
        · exact ih _ _ hp
      · rw [extractAux_succ_neg fuel h] at hp
        simp at hp

theorem extract_mem_fst_lt_snd
    {m : ℕ} (κ : PartialPairing (Fin m))
    (p : Fin m × Fin m) (hp : p ∈ extract κ) :
    p.1 < p.2 :=
  extractAux_mem_fst_lt_snd κ m Finset.univ p hp

/-! ## Pairwise laminarity -/

private theorem selected_compatible_with_later
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)}
    (h : ∃ a b, IsRelFullyPaired κ active a b)
    {fuel : ℕ} {q : Fin m × Fin m}
    (hq :
      q ∈ extractAux κ fuel
        (active \ relIcc active
          (selectRel κ active h).1
          (selectRel κ active h).2)) :
    EarlierReductionIntervalCompatible
      (selectRel κ active h) q := by
  let p := selectRel κ active h
  let active' :=
    active \ relIcc active p.1 p.2
  have hqmem :=
    extractAux_mem κ fuel active' q hq
  have hqleft : q.1 ∈ active' := hqmem.1
  have hqright : q.2 ∈ active' := hqmem.2.1
  have hqorder : q.1 ≤ q.2 := hqmem.2.2
  have hporder :
      p.1 ≤ p.2 :=
    (selectRel_isRelFullyPaired κ active h).le
  have hleftNot :
      ¬(p.1 ≤ q.1 ∧ q.1 ≤ p.2) := by
    intro hbetween
    exact (Finset.mem_sdiff.mp hqleft).2
      (mem_relIcc.mpr
        ⟨(Finset.mem_sdiff.mp hqleft).1,
          hbetween.1, hbetween.2⟩)
  have hrightNot :
      ¬(p.1 ≤ q.2 ∧ q.2 ≤ p.2) := by
    intro hbetween
    exact (Finset.mem_sdiff.mp hqright).2
      (mem_relIcc.mpr
        ⟨(Finset.mem_sdiff.mp hqright).1,
          hbetween.1, hbetween.2⟩)
  dsimp only [p] at hporder hleftNot hrightNot ⊢
  unfold EarlierReductionIntervalCompatible
  omega

theorem extractAux_pairwise_earlierCompatible
    {m : ℕ} (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractAux κ fuel active).Pairwise
        EarlierReductionIntervalCompatible := by
  induction fuel with
  | zero =>
      intro active
      exact List.Pairwise.nil
  | succ fuel ih =>
      intro active
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAux_succ_pos fuel h]
        apply List.pairwise_cons.mpr
        constructor
        · intro q hq
          exact selected_compatible_with_later h hq
        · exact ih _
      · rw [extractAux_succ_neg fuel h]
        exact List.Pairwise.nil

/-- The extracted endpoint intervals are pairwise disjoint or nested,
exactly the structural fact behind the paper's Dyck-word encoding. -/
theorem extract_pairwise_laminar
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extract κ).Pairwise ReductionIntervalsLaminar :=
  (extractAux_pairwise_earlierCompatible
    κ m Finset.univ).imp
      fun h => h.laminar

/-! ## Endpoint disjointness and counting -/

theorem ReductionIntervalsLaminar.fst_ne_snd
    {m : ℕ} {p q : Fin m × Fin m}
    (hlam : ReductionIntervalsLaminar p q)
    (hp : p.1 < p.2) (hq : q.1 < q.2) :
    p.1 ≠ q.2 := by
  rcases hlam with h | h | h | h <;> omega

private theorem extract_laminar_of_mem_of_ne
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {p q : Fin m × Fin m}
    (hp : p ∈ extract κ) (hq : q ∈ extract κ)
    (hpq : p ≠ q) :
    ReductionIntervalsLaminar p q := by
  obtain ⟨i, hi⟩ := List.get_of_mem hp
  obtain ⟨j, hj⟩ := List.get_of_mem hq
  have hij : i ≠ j := by
    intro hij
    apply hpq
    rw [← hi, ← hj, hij]
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hrel :=
      (extract_pairwise_laminar κ).rel_get_of_lt hij
    simpa only [hi, hj] using hrel
  · have hrel :=
      (extract_pairwise_laminar κ).rel_get_of_lt hji
    have hqp : ReductionIntervalsLaminar q p := by
      simpa only [hi, hj] using hrel
    exact hqp.symm

/-- No index is simultaneously a left and a right endpoint of two
extracted intervals. -/
theorem disjoint_leftEndpoints_rightEndpoints
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Disjoint (leftEndpoints κ) (rightEndpoints κ) := by
  rw [Finset.disjoint_left]
  intro x hxleft hxright
  rw [leftEndpoints, List.mem_toFinset] at hxleft
  rw [rightEndpoints, List.mem_toFinset] at hxright
  obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hxleft
  obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hxright
  have hpstrict := extract_mem_fst_lt_snd κ p hp
  have hqstrict := extract_mem_fst_lt_snd κ q hq
  by_cases hpq : p = q
  · subst q
    exact (ne_of_lt hpstrict) (hpx.trans hqx.symm)
  · have hlam :=
      extract_laminar_of_mem_of_ne hp hq hpq
    exact hlam.fst_ne_snd hpstrict hqstrict
      (hpx.trans hqx.symm)

/-- The union of all selected endpoints contains exactly two positions
per extracted interval. -/
theorem card_union_reductionEndpoints
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (leftEndpoints κ ∪ rightEndpoints κ).card =
      2 * (extract κ).length := by
  rw [Finset.card_union_of_disjoint
      (disjoint_leftEndpoints_rightEndpoints κ),
    leftEndpoints_card_eq_length,
    rightEndpoints_card_eq_length]
  omega

/-- The endpoint-role signature used to group the R-322 sum before the
analytic interval reductions. -/
def reductionEndpointSignature
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Finset (Fin m) × Finset (Fin m) :=
  (leftEndpoints κ, rightEndpoints κ)

/-- All signatures realized by the non-splitting pairings at order
`2q`. -/
def nonSplitReductionEndpointSignatures (q : ℕ) :
    Finset
      (Finset (Fin (2 * q)) ×
        Finset (Fin (2 * q))) :=
  (nonSplitPairings q).image reductionEndpointSignature

/-- The endpoint and bracket-role choices in paper §4.1, Step 1 cost at
most `4^(2q)`.  This is the same coarse exponential factor obtained
there from choosing the endpoint union and then a Dyck word. -/
theorem card_nonSplitReductionEndpointSignatures_le
    (q : ℕ) :
    (nonSplitReductionEndpointSignatures q).card ≤
      4 ^ (2 * q) := by
  calc
    (nonSplitReductionEndpointSignatures q).card ≤
        Fintype.card
          (Finset (Fin (2 * q)) ×
            Finset (Fin (2 * q))) :=
      Finset.card_le_univ _
    _ = 4 ^ (2 * q) := by
      simp only [Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin]
      rw [show (4 : ℕ) = 2 * 2 by norm_num,
        mul_pow]

/-! ## Exact regrouping by endpoint signature -/

/-- Regrouping the non-splitting pairing sum by its extraction-endpoint
signature loses no terms and introduces no multiplicity.  This is the
finite-sum identity used before estimating each signature fiber in
paper §4.1, Step 1. -/
theorem sum_nonSplitPairings_by_endpointSignature
    {M : Type*} [AddCommMonoid M]
    (q : ℕ)
    (F : PartialPairing (Fin (2 * q)) → M) :
    (∑ s ∈ nonSplitReductionEndpointSignatures q,
        ∑ κ ∈ nonSplitPairings q with
          reductionEndpointSignature κ = s,
          F κ) =
      ∑ κ ∈ nonSplitPairings q, F κ := by
  apply Finset.sum_fiberwise_of_maps_to
  intro κ hκ
  exact Finset.mem_image.mpr ⟨κ, hκ, rfl⟩

/-- If every endpoint-signature fiber costs at most `B`, the whole
non-splitting pairing sum costs at most `4^(2q) B`. -/
theorem sum_nonSplitPairings_le_of_endpointSignature_fibers
    (q : ℕ)
    (F : PartialPairing (Fin (2 * q)) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hfiber :
      ∀ s ∈ nonSplitReductionEndpointSignatures q,
        (∑ κ ∈ nonSplitPairings q with
          reductionEndpointSignature κ = s,
          F κ) ≤ B) :
    (∑ κ ∈ nonSplitPairings q, F κ) ≤
      (4 : ℝ) ^ (2 * q) * B := by
  rw [← sum_nonSplitPairings_by_endpointSignature q F]
  calc
    (∑ s ∈ nonSplitReductionEndpointSignatures q,
        ∑ κ ∈ nonSplitPairings q with
          reductionEndpointSignature κ = s,
          F κ) ≤
        ∑ _s ∈ nonSplitReductionEndpointSignatures q,
          B :=
      Finset.sum_le_sum hfiber
    _ =
        ((nonSplitReductionEndpointSignatures q).card :
          ℝ) * B := by
      simp
    _ ≤ (4 : ℝ) ^ (2 * q) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast
        card_nonSplitReductionEndpointSignatures_le q

end Anderson4D
