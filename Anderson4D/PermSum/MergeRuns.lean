import Anderson4D.Combinatorics.PrimitiveWord
import Mathlib.Data.List.Destutter
import Mathlib.Data.List.Perm.Subperm

/-!
# Merging adjacent equal letters

This file isolates the run-merging operation used in the deduction of
Proposition 5.7 from Proposition 5.9, paper equations (5.34)--(5.37).
`mergeEqualRuns` keeps one representative of every maximal constant run.
The generic `listChainProduct_mergeEqualRuns` lemma records the analytic
reason this operation is harmless: an edge joining two equal letters has
weight one.
-/

namespace Anderson4D

open scoped BigOperators

section Runs

variable {α R : Type*} [DecidableEq α]

/-- Keep exactly one representative of every maximal constant run. -/
def mergeEqualRuns (l : List α) : List α :=
  l.destutter (· ≠ ·)

theorem mergeEqualRuns_sublist (l : List α) :
    List.Sublist (mergeEqualRuns l) l :=
  List.destutter_sublist _ _

theorem mergeEqualRuns_isChain (l : List α) :
    (mergeEqualRuns l).IsChain (· ≠ ·) :=
  List.isChain_destutter _ _

@[simp]
theorem mergeEqualRuns_eq_nil {l : List α} :
    mergeEqualRuns l = [] ↔ l = [] :=
  by simp [mergeEqualRuns]

theorem mergeEqualRuns_length_le (l : List α) :
    (mergeEqualRuns l).length ≤ l.length :=
  (mergeEqualRuns_sublist l).length_le

theorem mergeEqualRuns_count_le (l : List α) (a : α) :
    (mergeEqualRuns l).count a ≤ l.count a := by
  apply (List.subperm_iff_count.mp (mergeEqualRuns_sublist l).subperm) a

private theorem mem_destutter'_ne_iff (x a : α) :
    ∀ l : List α, x ∈ l.destutter' (· ≠ ·) a ↔ x = a ∨ x ∈ l
  | [] => by simp
  | b :: l => by
      rw [List.destutter'_cons]
      by_cases hab : a ≠ b
      · simp only [if_pos hab, List.mem_cons, mem_destutter'_ne_iff]
      · have hab' : a = b := not_ne_iff.mp hab
        simp only [if_neg hab, mem_destutter'_ne_iff]
        simp [hab']

@[simp]
theorem mem_mergeEqualRuns_iff (x : α) (l : List α) :
    x ∈ mergeEqualRuns l ↔ x ∈ l := by
  cases l with
  | nil => simp [mergeEqualRuns]
  | cons a l =>
      simpa [mergeEqualRuns, List.destutter_cons'] using
        mem_destutter'_ne_iff x a l

/-- Consecutive-edge product on a list. -/
def listChainProduct [Monoid R] (edge : α → α → R) : List α → R
  | [] => 1
  | [_] => 1
  | a :: b :: l => edge a b * listChainProduct edge (b :: l)

omit [DecidableEq α] in
/-- `listChainProduct` is the product of `edge` over the list zipped with
its tail. -/
theorem listChainProduct_eq_zipWith [Monoid R] (edge : α → α → R)
    (l : List α) :
    listChainProduct edge l = (List.zipWith edge l l.tail).prod := by
  induction l using List.twoStepInduction with
  | nil => simp [listChainProduct]
  | singleton a => simp [listChainProduct]
  | cons_cons a b l _ ih =>
      simp [listChainProduct, ih]

omit [DecidableEq α] in
/-- Mapping the vertices of a chain is the same as precomposing its edge
weight in both arguments. -/
theorem listChainProduct_map {β : Type*} [Monoid R]
    (edge : β → β → R) (f : α → β) (l : List α) :
    listChainProduct edge (l.map f) =
      listChainProduct (fun a b => edge (f a) (f b)) l := by
  induction l using List.twoStepInduction with
  | nil => simp [listChainProduct]
  | singleton a => simp [listChainProduct]
  | cons_cons a b l _ ih =>
      simp only [List.map_cons, listChainProduct]
      simpa only [List.map_cons] using
        congrArg (fun x => edge (f a) (f b) * x) (ih b)

private theorem destutter'_ne_eq_cons (a : α) :
    ∀ l : List α, ∃ t, l.destutter' (· ≠ ·) a = a :: t
  | [] => ⟨[], rfl⟩
  | b :: l => by
      rw [List.destutter'_cons]
      by_cases hab : a ≠ b
      · exact ⟨l.destutter' (· ≠ ·) b, by simp [hab]⟩
      · simpa [hab] using destutter'_ne_eq_cons a l

/-- Merging equal runs preserves any chain product whose equal-letter edge
weight is one. -/
theorem listChainProduct_mergeEqualRuns [Monoid R] (edge : α → α → R)
    (hdiag : ∀ a, edge a a = 1) :
    ∀ l : List α, listChainProduct edge (mergeEqualRuns l) =
      listChainProduct edge l
  | [] => by simp [mergeEqualRuns, listChainProduct]
  | a :: l => by
      change listChainProduct edge (l.destutter' (· ≠ ·) a) =
        listChainProduct edge (a :: l)
      induction l generalizing a with
      | nil => simp [listChainProduct]
      | cons b l ih =>
          rw [List.destutter'_cons]
          by_cases hab : a ≠ b
          · obtain ⟨t, ht⟩ := destutter'_ne_eq_cons b l
            simp only [if_pos hab, ht, listChainProduct]
            rw [← ht, ih]
          · have hab' : a = b := not_ne_iff.mp hab
            subst b
            have hself : ¬a ≠ a := fun h => h rfl
            simp only [if_neg hself, listChainProduct, hdiag, one_mul]
            exact ih a

end Runs

section Words

variable {α R : Type*} [DecidableEq α] {m : ℕ}

private theorem merge_count_ofFn {β : Type*}
    [BEq β] [LawfulBEq β] [DecidableEq β] :
    ∀ {n : ℕ} (g : Fin n → β) (b : β),
      (List.ofFn g).count b =
        (Finset.univ.filter fun i => g i = b).card
  | 0, g, b => by simp
  | n + 1, g, b => by
      rw [List.ofFn_succ, List.count_cons,
        merge_count_ofFn (fun i => g i.succ) b,
        Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      simp only [beq_iff_eq]
      omega

/-- List form of a word after all adjacent equal letters have been merged. -/
def mergedWordList (w : Fin m → α) : List α :=
  mergeEqualRuns (List.ofFn w)

/-- Multiplicity of a letter after run merging. -/
def mergedMultiplicity (w : Fin m → α) (a : α) : ℕ :=
  (mergedWordList w).count a

/-- The compressed word, indexed by its (generally smaller) length. -/
def mergedWord (w : Fin m → α) :
    Fin (mergedWordList w).length → α :=
  (mergedWordList w).get

theorem mergedWordList_length_le (w : Fin m → α) :
    (mergedWordList w).length ≤ m := by
  simpa [mergedWordList] using
    mergeEqualRuns_length_le (List.ofFn w)

theorem mergedMultiplicity_le_originalCount (w : Fin m → α) (a : α) :
    mergedMultiplicity w a ≤ (List.ofFn w).count a :=
  mergeEqualRuns_count_le (List.ofFn w) a

theorem mergedMultiplicity_pos_iff (w : Fin m → α) (a : α) :
    0 < mergedMultiplicity w a ↔ ∃ i, w i = a := by
  change 0 < (mergeEqualRuns (List.ofFn w)).count a ↔ _
  rw [List.count_pos_iff, mem_mergeEqualRuns_iff, List.mem_ofFn']
  simp only [Set.mem_range]

/-- The compressed word has the compressed multiplicities by construction. -/
theorem mergedWord_mem_validWords [Fintype α] (w : Fin m → α) :
    mergedWord w ∈ validWords (mergedMultiplicity w) := by
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun a => ?_⟩
  calc
    (Finset.univ.filter fun j => mergedWord w j = a).card =
        (List.ofFn (mergedWord w)).count a :=
      (merge_count_ofFn (mergedWord w) a).symm
    _ = mergedMultiplicity w a := by
      rw [show List.ofFn (mergedWord w) = mergedWordList w by
        exact List.ofFn_get (mergedWordList w)]
      rfl

/-- The new multiplicities sum to the compressed word length. -/
theorem sum_mergedMultiplicity [Fintype α] (w : Fin m → α) :
    ∑ a : α, mergedMultiplicity w a = (mergedWordList w).length := by
  let l := mergedWordList w
  calc
    ∑ a : α, mergedMultiplicity w a = ∑ a : α, l.count a := by
      simp [mergedMultiplicity, l]
    _ = ∑ a ∈ l.toFinset, l.count a := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ ha
      rw [List.count_eq_zero]
      simpa using ha
    _ = l.length := List.sum_toFinset_count_eq_length l

/-- Adjacent letters of the compressed word are distinct. -/
theorem mergedWord_noAdjacentEqual (w : Fin m → α) :
    NoAdjacentEqual (mergedWord w) := by
  intro j hj
  have hchain := mergeEqualRuns_isChain (List.ofFn w)
  have h := List.isChain_iff_getElem.mp hchain j.1 hj
  unfold mergedWord
  intro heq
  apply h
  convert heq using 1
  · simp [mergedWordList, List.get_eq_getElem]
  · simp [mergedWordList, List.get_eq_getElem]
    congr

/-- Word-level form of run-merging invariance for a generic edge product. -/
theorem mergedWordList_chainProduct [Monoid R] (edge : α → α → R)
    (hdiag : ∀ a, edge a a = 1) (w : Fin m → α) :
    listChainProduct edge (mergedWordList w) =
      listChainProduct edge (List.ofFn w) :=
  listChainProduct_mergeEqualRuns edge hdiag (List.ofFn w)

end Words

end Anderson4D
