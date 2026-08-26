import Anderson4D.DetParametrix.Core.ReductionSelectorRigidity
import Anderson4D.DetParametrix.Paper41_Renorm.R322EndpointProductClosure

/-!
# Selector and Fubini routing for R-322

This file turns the deterministic smallest-leftmost selector into the analytic
inside-to-outside route used in paper Section 4.1.  The first task is to
separate the final primitive block from all proper blocks: for a non-splitting
full pairing, an extracted interval can meet a global endpoint only when it is
the whole interval.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The unique extracted interval meeting the global left endpoint -/

/-- Every pair in the public extraction list was already a fully paired
relative interval in the initial full carrier. -/
theorem extract_mem_isRelFullyPaired_univ
    {m : ℕ} (κ : PartialPairing (Fin m))
    (p : Fin m × Fin m) (hp : p ∈ extract κ) :
    IsRelFullyPaired κ Finset.univ p.1 p.2 := by
  exact
    extractAux_mem_isRelFullyPaired
      κ m Finset.univ p hp

/-- In the initial carrier, a relative interval is the ordinary interval. -/
theorem relIcc_univ
    {m : ℕ} (a b : Fin m) :
    relIcc (Finset.univ : Finset (Fin m)) a b =
      Finset.Icc a b := by
  ext i
  simp [relIcc]

/-- For a non-splitting full pairing, an extracted interval whose left
endpoint is the global first index must be the whole interval. -/
theorem extracted_right_eq_last_of_isNonSplit_of_left_eq_zero
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hq : 1 ≤ q)
    (hκ : IsNonSplit κ)
    (p : Fin (2 * q) × Fin (2 * q))
    (hp : p ∈ extract κ)
    (hleft :
      p.1 = (⟨0, by omega⟩ : Fin (2 * q))) :
    p.2 =
      (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) := by
  have hrel :=
    extract_mem_isRelFullyPaired_univ κ p hp
  have hpaired :
      IsFullyPairedOn κ (Finset.Icc p.1 p.2) := by
    rw [← relIcc_univ p.1 p.2]
    exact hrel.isFullyPairedOn
  apply Fin.ext
  change p.2.val = 2 * q - 1
  by_contra hnot
  have hproper : p.2.val + 1 < 2 * q := by
    have hp2 := p.2.isLt
    omega
  apply hκ.2
  refine
    ⟨p.2.val,
      Finset.mem_range.mpr p.2.isLt,
      hproper, ?_⟩
  have hprefix :
      Finset.univ.filter
          (fun i : Fin (2 * q) =>
            i.val ≤ p.2.val) =
        Finset.Icc p.1 p.2 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Icc]
    rw [hleft]
    change (i.val ≤ p.2.val ↔
      0 ≤ i.val ∧ i.val ≤ p.2.val)
    omega
  rw [hprefix]
  exact hpaired

/-- Dually, an extracted interval whose right endpoint is the global last
index must also begin at the global first index.  The proof uses fullness:
the complement of a fully paired suffix is a fully paired proper prefix,
which is forbidden by `IsNonSplit`. -/
theorem extracted_left_eq_zero_of_isNonSplit_of_right_eq_last
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hq : 1 ≤ q)
    (hκ : IsNonSplit κ)
    (p : Fin (2 * q) × Fin (2 * q))
    (hp : p ∈ extract κ)
    (hright :
      p.2 =
        (⟨2 * q - 1, by omega⟩ :
          Fin (2 * q))) :
    p.1 = (⟨0, by omega⟩ : Fin (2 * q)) := by
  have hrel :=
    extract_mem_isRelFullyPaired_univ κ p hp
  have hsuffix :
      IsFullyPairedOn κ (Finset.Icc p.1 p.2) := by
    rw [← relIcc_univ p.1 p.2]
    exact hrel.isFullyPairedOn
  have huniv :
      IsFullyPairedOn κ
        (Finset.univ : Finset (Fin (2 * q))) :=
    isFullyPairedOn_univ_iff.mpr hκ.1
  have hcomplement :
      IsFullyPairedOn κ
        ((Finset.univ : Finset (Fin (2 * q))) \
          Finset.Icc p.1 p.2) :=
    huniv.sdiff hsuffix
  apply Fin.ext
  change p.1.val = 0
  by_contra hnot
  have hpos : 0 < p.1.val := by omega
  apply hκ.2
  refine
    ⟨p.1.val - 1,
      Finset.mem_range.mpr (by omega),
      by omega, ?_⟩
  have hprefix :
      Finset.univ.filter
          (fun i : Fin (2 * q) =>
            i.val ≤ p.1.val - 1) =
        (Finset.univ : Finset (Fin (2 * q))) \
          Finset.Icc p.1 p.2 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff, Finset.mem_Icc]
    have hi := i.isLt
    have hp1 := p.1.isLt
    have hp2 : p.2.val = 2 * q - 1 := by
      exact congrArg Fin.val hright
    change
      (i.val ≤ p.1.val - 1 ↔
        ¬(p.1.val ≤ i.val ∧ i.val ≤ p.2.val))
    omega
  rw [hprefix]
  exact hcomplement

/-- In a non-splitting extraction, meeting either global endpoint is
equivalent to being the unique whole-interval endpoint pair. -/
theorem extracted_meets_global_endpoint_iff_whole
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hq : 1 ≤ q)
    (hκ : IsNonSplit κ)
    (p : Fin (2 * q) × Fin (2 * q))
    (hp : p ∈ extract κ) :
    (p.1 = (⟨0, by omega⟩ : Fin (2 * q)) ∨
        p.2 =
          (⟨2 * q - 1, by omega⟩ :
            Fin (2 * q))) ↔
      p =
        ((⟨0, by omega⟩ : Fin (2 * q)),
          (⟨2 * q - 1, by omega⟩ :
            Fin (2 * q))) := by
  constructor
  · intro h
    rcases h with hleft | hright
    · apply Prod.ext
      · exact hleft
      · exact
          extracted_right_eq_last_of_isNonSplit_of_left_eq_zero
            hq hκ p hp hleft
    · apply Prod.ext
      · exact
          extracted_left_eq_zero_of_isNonSplit_of_right_eq_last
            hq hκ p hp hright
      · exact hright
  · intro h
    subst p
    exact Or.inl rfl

/-! ## The endpoint list and concrete block list are aligned -/

/-- The endpoint pair selected at one step is the pair of order bounds of
the concrete relative trace removed at that step. -/
def ExtractionPairBlockAligned
    {m : ℕ} (p : Fin m × Fin m)
    (B : Finset (Fin m)) : Prop :=
  p.1 ∈ B ∧ p.2 ∈ B ∧
    ∀ i ∈ B, p.1 ≤ i ∧ i ≤ p.2

/-- The endpoint and concrete-trace recursions are pointwise aligned, not
merely equal in length. -/
theorem extractAux_extractionBlocksAux_aligned
    {m : ℕ} (κ : PartialPairing (Fin m))
    (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      List.Forall₂ ExtractionPairBlockAligned
        (extractAux κ fuel active)
        (extractionBlocksAux κ fuel active) := by
  induction fuel with
  | zero =>
      intro active
      exact List.Forall₂.nil
  | succ fuel ih =>
      intro active
      by_cases h :
          ∃ a b, IsRelFullyPaired κ active a b
      · rw [extractAux_succ_pos fuel h,
          extractionBlocksAux_succ_pos fuel h]
        apply List.Forall₂.cons
        · let p := selectRel κ active h
          have hp :=
            selectRel_isRelFullyPaired κ active h
          refine
            ⟨hp.left_mem_relIcc,
              hp.right_mem_relIcc, ?_⟩
          intro i hi
          exact (mem_relIcc.mp hi).2
        · exact ih _
      · rw [extractAux_succ_neg fuel h,
          extractionBlocksAux_succ_neg fuel h]
        exact List.Forall₂.nil

private theorem exists_left_of_forall₂_of_mem_right
    {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys)
    {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, R x y := by
  induction h with
  | nil =>
      simp at hy
  | cons hxy htail ih =>
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨_, List.mem_cons_self, hxy⟩
      · obtain ⟨x, hx, hR⟩ := ih hy
        exact
          ⟨x, List.mem_cons_of_mem _ hx, hR⟩

/-- Public endpoint/block alignment. -/
theorem exists_extractedPair_aligned_of_mem_extractionBlocks
    {m : ℕ} (κ : PartialPairing (Fin m))
    {B : Finset (Fin m)}
    (hB : B ∈ extractionBlocks κ) :
    ∃ p ∈ extract κ,
      ExtractionPairBlockAligned p B := by
  exact
    exists_left_of_forall₂_of_mem_right
      (extractAux_extractionBlocksAux_aligned
        κ m Finset.univ)
      hB

/-! ## The whole endpoint pair exists and is terminal -/

/-- A full non-splitting pairing has a whole-interval extraction pair. -/
theorem whole_pair_mem_extract_of_isNonSplit
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hq : 1 ≤ q) (hκ : IsNonSplit κ) :
    ((⟨0, by omega⟩ : Fin (2 * q)),
        (⟨2 * q - 1, by omega⟩ :
          Fin (2 * q))) ∈
      extract κ := by
  let first : Fin (2 * q) := ⟨0, by omega⟩
  obtain ⟨B, hB, hfirstB⟩ :=
    mem_extractionBlock_of_full κ hκ.1 first
  obtain ⟨p, hp, haligned⟩ :=
    exists_extractedPair_aligned_of_mem_extractionBlocks
      κ hB
  have hleft : p.1 = first := by
    apply Fin.ext
    change p.1.val = 0
    have hle := (haligned.2.2 first hfirstB).1
    change p.1.val ≤ first.val at hle
    have hle' : p.1.val ≤ 0 := by
      simpa only [first] using hle
    omega
  have hright :=
    extracted_right_eq_last_of_isNonSplit_of_left_eq_zero
      hq hκ p hp hleft
  simpa only [first] using
    (show
      p =
        ((⟨0, by omega⟩ : Fin (2 * q)),
          (⟨2 * q - 1, by omega⟩ :
            Fin (2 * q))) by
      exact Prod.ext hleft hright) ▸ hp

private theorem list_eq_prefix_append_singleton_of_terminal
    {α : Type*} {R : α → α → Prop}
    {xs : List α} {x : α}
    (hpairwise : xs.Pairwise R)
    (hx : x ∈ xs)
    (hterminal : ∀ y, R x y → False) :
    ∃ pre, xs = pre ++ [x] := by
  induction xs with
  | nil =>
      simp at hx
  | cons a xs ih =>
      rw [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hx
      rcases hx with hax | hx
      · subst a
        have hnil : xs = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro y hy
          exact hterminal y (hpairwise.1 y hy)
        subst xs
        exact ⟨[], rfl⟩
      · obtain ⟨pre, hpre⟩ :=
          ih hpairwise.2 hx
        exact
          ⟨a :: pre, by
            rw [hpre]
            rfl⟩

/-- The whole interval cannot precede another extracted interval. -/
theorem whole_pair_not_earlierCompatible
    {q : ℕ} (hq : 1 ≤ q)
    (p : Fin (2 * q) × Fin (2 * q)) :
    ¬EarlierReductionIntervalCompatible
      ((⟨0, by omega⟩ : Fin (2 * q)),
        (⟨2 * q - 1, by omega⟩ :
          Fin (2 * q)))
      p := by
  unfold EarlierReductionIntervalCompatible
  change
    ¬((2 * q - 1 < p.1.val) ∨
      (p.2.val < 0) ∨
      (p.1.val < 0 ∧
        2 * q - 1 < p.2.val))
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  omega

/-- The deterministic selector removes every proper block first and the
whole block last. -/
theorem extract_eq_prefix_append_whole_of_isNonSplit
    {q : ℕ} {κ : PartialPairing (Fin (2 * q))}
    (hq : 1 ≤ q) (hκ : IsNonSplit κ) :
    ∃ proper,
      extract κ =
        proper ++
          [((⟨0, by omega⟩ : Fin (2 * q)),
            (⟨2 * q - 1, by omega⟩ :
              Fin (2 * q)))] := by
  apply
    list_eq_prefix_append_singleton_of_terminal
      (extractAux_pairwise_earlierCompatible
        κ (2 * q) Finset.univ)
      (whole_pair_mem_extract_of_isNonSplit hq hκ)
  intro p hp
  exact whole_pair_not_earlierCompatible hq p hp

end

end Anderson4D
