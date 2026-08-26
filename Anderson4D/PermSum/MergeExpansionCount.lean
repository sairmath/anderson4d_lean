import Anderson4D.PermSum.CollapseCompositionCount
import Anderson4D.PermSum.CollapsePrimitivity
import Anderson4D.PermSum.MergeRuns

/-!
# Counting expansions of a run-compressed word

This module supplies the finite-fiber count needed in the deduction of
Proposition 5.7 from Proposition 5.9.  Once the compressed word is fixed, an
original word is determined by the positive lengths of its constant runs.
Those lengths form an ordinary composition of the original word length, so
every compression fiber has cardinality at most `2 ^ M`.
-/

namespace Anderson4D

open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

variable {α : Type*} [DecidableEq α]

/-! ## Run-length reconstruction -/

/-- Expand a list of run representatives using the corresponding list of
run lengths.  Mismatched tails are ignored by `zipWith`; all applications
below carry an equality of the two list lengths. -/
def expandRunLengths (representatives : List α)
    (lengths : List ℕ) : List α :=
  (List.zipWith
    (fun a n => List.replicate n a) representatives lengths).flatten

omit [DecidableEq α] in
@[simp]
theorem expandRunLengths_nil_left (lengths : List ℕ) :
    expandRunLengths ([] : List α) lengths = [] :=
  rfl

omit [DecidableEq α] in
@[simp]
theorem expandRunLengths_nil_right (representatives : List α) :
    expandRunLengths representatives [] = [] := by
  cases representatives <;> rfl

omit [DecidableEq α] in
@[simp]
theorem expandRunLengths_cons (a : α) (n : ℕ)
    (representatives : List α) (lengths : List ℕ) :
    expandRunLengths (a :: representatives) (n :: lengths) =
      List.replicate n a ++
        expandRunLengths representatives lengths :=
  rfl

/-- A compressed nonempty list still starts with the original first
letter. -/
theorem mergeEqualRuns_cons_eq_cons (a : α) (l : List α) :
    ∃ tail, mergeEqualRuns (a :: l) = a :: tail := by
  change ∃ tail, l.destutter' (· ≠ ·) a = a :: tail
  induction l generalizing a with
  | nil =>
      exact ⟨[], by simp⟩
  | cons b l ih =>
      rw [List.destutter'_cons]
      by_cases hab : a ≠ b
      · exact ⟨l.destutter' (· ≠ ·) b, by simp [hab]⟩
      · have hab' : a = b := not_ne_iff.mp hab
        subst b
        simpa [hab] using ih a

/-- Every list is obtained from its run-compressed list by a positive
composition of its length. -/
theorem exists_composition_expandRunLengths_mergeEqualRuns
    (l : List α) :
    ∃ c : Composition l.length,
      c.blocks.length = (mergeEqualRuns l).length ∧
        expandRunLengths (mergeEqualRuns l) c.blocks = l := by
  induction l with
  | nil =>
      let c : Composition 0 :=
        { blocks := []
          blocks_pos := by simp
          blocks_sum := by simp }
      exact ⟨c, by simp [c, mergeEqualRuns], by simp [c]⟩
  | cons a tail ih =>
      cases tail with
      | nil =>
          let c : Composition 1 :=
            { blocks := [1]
              blocks_pos := by simp
              blocks_sum := by simp }
          exact ⟨c, by simp [c, mergeEqualRuns],
            by simp [c, mergeEqualRuns, expandRunLengths]⟩
      | cons b rest =>
          obtain ⟨c, hcLength, hcExpand⟩ := ih
          obtain ⟨compressedTail, hcompressedTail⟩ :=
            mergeEqualRuns_cons_eq_cons b rest
          have hcBlocks :
              ∃ n ns, c.blocks = n :: ns := by
            cases hblocks : c.blocks with
            | nil =>
                have : 0 =
                    (mergeEqualRuns (b :: rest)).length := by
                  simpa [hblocks] using hcLength
                rw [hcompressedTail] at this
                simp at this
            | cons n ns =>
                exact ⟨n, ns, rfl⟩
          obtain ⟨n, ns, hcBlocks⟩ := hcBlocks
          have hn : 0 < n :=
            c.blocks_pos (by simp [hcBlocks])
          have hcSum :
              n + ns.sum = (b :: rest).length := by
            simpa [hcBlocks] using c.blocks_sum
          have hcLength' :
              ns.length = compressedTail.length := by
            rw [hcBlocks, hcompressedTail] at hcLength
            simpa using Nat.succ.inj hcLength
          have hcExpand' :
              List.replicate n b ++
                  expandRunLengths compressedTail ns =
                b :: rest := by
            simpa [hcBlocks, hcompressedTail] using hcExpand
          by_cases hab : a = b
          · subst b
            let c' : Composition (a :: a :: rest).length :=
              { blocks := (n + 1) :: ns
                blocks_pos := by
                  intro k hk
                  simp only [List.mem_cons] at hk
                  rcases hk with rfl | hk
                  · omega
                  · exact c.blocks_pos (by simp [hcBlocks, hk])
                blocks_sum := by
                  rw [List.sum_cons]
                  simp only [List.length_cons] at hcSum ⊢
                  omega }
            refine ⟨c', ?_, ?_⟩
            · have hmerge :
                  mergeEqualRuns (a :: a :: rest) =
                    mergeEqualRuns (a :: rest) := by
                simp [mergeEqualRuns, List.destutter_cons']
              rw [hmerge, hcompressedTail]
              simp [c', hcLength']
            · have hmerge :
                  mergeEqualRuns (a :: a :: rest) =
                    mergeEqualRuns (a :: rest) := by
                simp [mergeEqualRuns, List.destutter_cons']
              rw [hmerge, hcompressedTail]
              simp only [c', expandRunLengths_cons,
                List.replicate_succ]
              rw [List.cons_append, hcExpand']
          · let c' : Composition (a :: b :: rest).length :=
              { blocks := 1 :: n :: ns
                blocks_pos := by
                  intro k hk
                  simp only [List.mem_cons] at hk
                  rcases hk with rfl | hk
                  · simp
                  · exact c.blocks_pos (by simp [hcBlocks, hk])
                blocks_sum := by
                  rw [List.sum_cons, List.sum_cons]
                  simp only [List.length_cons] at hcSum ⊢
                  omega }
            refine ⟨c', ?_, ?_⟩
            · have hmerge :
                  mergeEqualRuns (a :: b :: rest) =
                    a :: mergeEqualRuns (b :: rest) := by
                simp [mergeEqualRuns, List.destutter_cons', hab]
              rw [hmerge, hcompressedTail]
              simp [c', hcLength']
            · have hmerge :
                  mergeEqualRuns (a :: b :: rest) =
                    a :: mergeEqualRuns (b :: rest) := by
                simp [mergeEqualRuns, List.destutter_cons', hab]
              rw [hmerge, hcompressedTail]
              simp only [c', expandRunLengths_cons,
                List.replicate_one, List.singleton_append]
              rw [hcExpand']

/-! ## Composition coordinates on finite words -/

/-- Finite-word form of the run-length reconstruction theorem. -/
theorem exists_mergedRunComposition {M : ℕ}
    (w : Fin M → α) :
    ∃ c : Composition M,
      c.blocks.length = (mergedWordList w).length ∧
        expandRunLengths (mergedWordList w) c.blocks =
          List.ofFn w := by
  have h :=
    exists_composition_expandRunLengths_mergeEqualRuns
      (List.ofFn w)
  rw [List.length_ofFn] at h
  exact h

/-- A chosen positive run-length vector for a finite word.  Its two
specification lemmas below, rather than the choice itself, are the public
interface. -/
noncomputable def mergedRunComposition {M : ℕ}
    (w : Fin M → α) : Composition M :=
  Classical.choose (exists_mergedRunComposition w)

@[simp]
theorem mergedRunComposition_blocks_length {M : ℕ}
    (w : Fin M → α) :
    (mergedRunComposition w).blocks.length =
      (mergedWordList w).length :=
  (Classical.choose_spec (exists_mergedRunComposition w)).1

@[simp]
theorem expandRunLengths_mergedRunComposition {M : ℕ}
    (w : Fin M → α) :
    expandRunLengths (mergedWordList w)
        (mergedRunComposition w).blocks =
      List.ofFn w :=
  (Classical.choose_spec (exists_mergedRunComposition w)).2

/-- Among words with one fixed compressed representative list, the chosen
run-length composition is injective. -/
theorem mergedRunComposition_injective_on_mergedWordList
    {M : ℕ} {s : Finset (Fin M → α)} {v : List α} :
    Function.Injective
      (fun w : ↥(s.filter fun w => mergedWordList w = v) =>
        mergedRunComposition w.1) := by
  intro w₁ w₂ hcomposition
  apply Subtype.ext
  apply List.ofFn_injective
  have hw₁ :
      mergedWordList w₁.1 = v :=
    (Finset.mem_filter.mp w₁.2).2
  have hw₂ :
      mergedWordList w₂.1 = v :=
    (Finset.mem_filter.mp w₂.2).2
  change mergedRunComposition w₁.1 =
    mergedRunComposition w₂.1 at hcomposition
  calc
    List.ofFn w₁.1 =
        expandRunLengths (mergedWordList w₁.1)
          (mergedRunComposition w₁.1).blocks :=
      (expandRunLengths_mergedRunComposition w₁.1).symm
    _ = expandRunLengths v
          (mergedRunComposition w₁.1).blocks := by rw [hw₁]
    _ = expandRunLengths v
          (mergedRunComposition w₂.1).blocks := by rw [hcomposition]
    _ = expandRunLengths (mergedWordList w₂.1)
          (mergedRunComposition w₂.1).blocks := by rw [hw₂]
    _ = List.ofFn w₂.1 :=
      expandRunLengths_mergedRunComposition w₂.1

/-- Every fixed-compressed-list fiber in any finite family of length-`M`
words has cardinality at most `2 ^ M`. -/
theorem card_filter_mergedWordList_le_two_pow
    {M : ℕ} (s : Finset (Fin M → α)) (v : List α) :
    (s.filter fun w => mergedWordList w = v).card ≤ 2 ^ M := by
  calc
    (s.filter fun w => mergedWordList w = v).card =
        Fintype.card ↥(s.filter fun w => mergedWordList w = v) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Composition M) :=
      Fintype.card_le_of_injective
        (fun w : ↥(s.filter fun w => mergedWordList w = v) =>
          mergedRunComposition w.1)
        mergedRunComposition_injective_on_mergedWordList
    _ ≤ 2 ^ M := card_composition_le_two_pow M

/-! ## The prescribed multiplicity/compressed-word fiber -/

/-- Original valid words with prescribed compressed multiplicity and
prescribed compressed word list.  Using `List.ofFn v` avoids any dependent
cast between the varying compressed lengths. -/
def mergeExpansionFiber [Fintype α] {M K : ℕ}
    (ml sl : α → ℕ) (v : Fin K → α) :
    Finset (Fin M → α) :=
  (validWords ml).filter fun w =>
    mergedMultiplicity w = sl ∧
      mergedWordList w = List.ofFn v

@[simp]
theorem mem_mergeExpansionFiber_iff [Fintype α]
    {M K : ℕ} (ml sl : α → ℕ) (v : Fin K → α)
    (w : Fin M → α) :
    w ∈ mergeExpansionFiber ml sl v ↔
      w ∈ validWords ml ∧
        mergedMultiplicity w = sl ∧
        mergedWordList w = List.ofFn v := by
  simp [mergeExpansionFiber]

/-- The exact fiber requested in the run-compression regrouping costs at
most `2 ^ M`.  The bound is stronger than needed: validity, the value of
`sl`, and the no-adjacent condition on `v` play no role in the count. -/
theorem card_mergeExpansionFiber_le_two_pow [Fintype α]
    {M K : ℕ} (ml sl : α → ℕ) (v : Fin K → α) :
    (mergeExpansionFiber (M := M) ml sl v).card ≤ 2 ^ M := by
  calc
    (mergeExpansionFiber (M := M) ml sl v).card ≤
        ((validWords ml).filter fun w =>
          mergedWordList w = List.ofFn v).card := by
      apply Finset.card_le_card
      intro w hw
      have hdata :=
        (mem_mergeExpansionFiber_iff ml sl v w).mp hw
      exact Finset.mem_filter.mpr ⟨hdata.1, hdata.2.2⟩
    _ ≤ 2 ^ M :=
      card_filter_mergedWordList_le_two_pow
        (validWords ml) (List.ofFn v)

/-! ## Generic nonnegative weighted regrouping -/

/-- The nondependent key carried by a run-compressed word. -/
def mergeOutcome {M : ℕ} (w : Fin M → α) :
    (α → ℕ) × List α :=
  (mergedMultiplicity w, mergedWordList w)

/-- The finite set of compression outcomes realized by a finite word
family. -/
def mergeOutcomeImage [Fintype α] {M : ℕ}
    (s : Finset (Fin M → α)) :
    Finset ((α → ℕ) × List α) :=
  s.image mergeOutcome

/-- A fiber of the full compression outcome is no larger than the fiber
obtained by retaining only its compressed representative list. -/
theorem card_filter_mergeOutcome_le_two_pow
    [Fintype α]
    {M : ℕ} (s : Finset (Fin M → α))
    (outcome : (α → ℕ) × List α) :
    (s.filter fun w => mergeOutcome w = outcome).card ≤
      2 ^ M := by
  calc
    (s.filter fun w => mergeOutcome w = outcome).card ≤
        (s.filter fun w =>
          mergedWordList w = outcome.2).card := by
      apply Finset.card_le_card
      intro w hw
      have houtcome := (Finset.mem_filter.mp hw).2
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hw).1,
          congrArg Prod.snd houtcome⟩
    _ ≤ 2 ^ M :=
      card_filter_mergedWordList_le_two_pow s outcome.2

/-- Exact finite regrouping of a statistic that depends only on the
compression outcome. -/
theorem sum_comp_mergeOutcome_eq_sum_fibers
    [Fintype α]
    {M : ℕ} (s : Finset (Fin M → α))
    (F : ((α → ℕ) × List α) → ℝ) :
    (∑ w ∈ s, F (mergeOutcome w)) =
      ∑ outcome ∈ mergeOutcomeImage s,
        ((s.filter fun w =>
          mergeOutcome w = outcome).card : ℝ) *
          F outcome := by
  symm
  calc
    (∑ outcome ∈ mergeOutcomeImage s,
        ((s.filter fun w =>
          mergeOutcome w = outcome).card : ℝ) *
          F outcome) =
        ∑ outcome ∈ mergeOutcomeImage s,
          ∑ w ∈ s.filter
              (fun w => mergeOutcome w = outcome),
            F (mergeOutcome w) := by
      apply Finset.sum_congr rfl
      intro outcome houtcome
      calc
        ((s.filter fun w =>
            mergeOutcome w = outcome).card : ℝ) *
              F outcome =
            ∑ w ∈ s.filter
                (fun w => mergeOutcome w = outcome),
              F outcome := by simp
        _ = ∑ w ∈ s.filter
              (fun w => mergeOutcome w = outcome),
            F (mergeOutcome w) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2]
    _ = ∑ w ∈ s, F (mergeOutcome w) := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun w hw =>
          Finset.mem_image.mpr ⟨w, hw, rfl⟩)
        (fun w => F (mergeOutcome w))

/-- Generic weighted run-compression bound.  A nonnegative statistic on
compressed outcomes loses at most `2 ^ M` when pulled back and summed over
any finite family of original words. -/
theorem sum_comp_mergeOutcome_le_two_pow_mul_sum
    [Fintype α]
    {M : ℕ} (s : Finset (Fin M → α))
    (F : ((α → ℕ) × List α) → ℝ)
    (hF : ∀ outcome ∈ mergeOutcomeImage s, 0 ≤ F outcome) :
    (∑ w ∈ s, F (mergeOutcome w)) ≤
      (2 : ℝ) ^ M *
        ∑ outcome ∈ mergeOutcomeImage s, F outcome := by
  rw [sum_comp_mergeOutcome_eq_sum_fibers]
  calc
    (∑ outcome ∈ mergeOutcomeImage s,
        ((s.filter fun w =>
          mergeOutcome w = outcome).card : ℝ) *
          F outcome) ≤
        ∑ outcome ∈ mergeOutcomeImage s,
          (2 : ℝ) ^ M * F outcome := by
      apply Finset.sum_le_sum
      intro outcome houtcome
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          card_filter_mergeOutcome_le_two_pow s outcome
      · exact hF outcome houtcome
    _ = (2 : ℝ) ^ M *
        ∑ outcome ∈ mergeOutcomeImage s, F outcome := by
      rw [Finset.mul_sum]

/-! ## Primitivity transport -/

omit [DecidableEq α] in
/-- Run expansion distributes over an aligned concatenation. -/
theorem expandRunLengths_append
    (representatives₁ representatives₂ : List α)
    (lengths₁ lengths₂ : List ℕ)
    (haligned :
      representatives₁.length = lengths₁.length) :
    expandRunLengths (representatives₁ ++ representatives₂)
        (lengths₁ ++ lengths₂) =
      expandRunLengths representatives₁ lengths₁ ++
        expandRunLengths representatives₂ lengths₂ := by
  induction representatives₁ generalizing lengths₁ with
  | nil =>
      have hnil : lengths₁ = [] := by
        simpa using List.length_eq_zero_iff.mp haligned.symm
      subst lengths₁
      simp
  | cons a representatives₁ ih =>
      cases lengths₁ with
      | nil =>
          simp at haligned
      | cons n lengths₁ =>
          have haligned' :
              representatives₁.length = lengths₁.length := by
            simpa using Nat.succ.inj haligned
          simp only [List.cons_append, expandRunLengths_cons,
            ih lengths₁ haligned', List.append_assoc]

omit [DecidableEq α] in
/-- A letter predicate holding on all run representatives holds throughout
their expansion. -/
theorem forall_mem_expandRunLengths
    (representatives : List α) (lengths : List ℕ)
    (P : α → Prop)
    (hP : ∀ a ∈ representatives, P a) :
    ∀ x ∈ expandRunLengths representatives lengths, P x := by
  induction representatives generalizing lengths with
  | nil =>
      simp
  | cons a representatives ih =>
      cases lengths with
      | nil =>
          simp
      | cons n lengths =>
          intro x hx
          simp only [expandRunLengths_cons, List.mem_append] at hx
          rcases hx with hx | hx
          · have hxa : x = a :=
              (List.mem_replicate.mp hx).2
            rw [hxa]
            exact hP a (List.mem_cons_self)
          · exact ih lengths
              (fun b hb => hP b (List.mem_cons_of_mem a hb))
              x hx

omit [DecidableEq α] in
/-- Positive aligned run lengths make the expansion of a nonempty
representative list nonempty. -/
theorem expandRunLengths_ne_nil
    (representatives : List α) (lengths : List ℕ)
    (hrepr : representatives ≠ [])
    (haligned : representatives.length = lengths.length)
    (hpos : ∀ n ∈ lengths, 0 < n) :
    expandRunLengths representatives lengths ≠ [] := by
  cases representatives with
  | nil =>
      exact (hrepr rfl).elim
  | cons a representatives =>
      cases lengths with
      | nil =>
          simp at haligned
      | cons n lengths =>
          have hn : 0 < n :=
            hpos n (List.mem_cons_self)
          simp only [expandRunLengths_cons]
          intro hnil
          have hreplicate :
              List.replicate n a = [] :=
            (List.append_eq_nil_iff.mp hnil).1
          have hnzero :
              n = 0 :=
            (List.replicate_eq_nil_iff a).mp hreplicate
          omega

omit [DecidableEq α] in
/-- Split a length list along an aligned three-part decomposition of its
representative list. -/
theorem exists_expandRunLengths_three_parts
    (representatives pre mid post : List α)
    (lengths : List ℕ)
    (hrepr :
      representatives = pre ++ mid ++ post)
    (haligned :
      representatives.length = lengths.length) :
    ∃ lengthsPre lengthsMid lengthsPost : List ℕ,
      lengths = lengthsPre ++ lengthsMid ++ lengthsPost ∧
        pre.length = lengthsPre.length ∧
        mid.length = lengthsMid.length ∧
        post.length = lengthsPost.length ∧
        expandRunLengths representatives lengths =
          expandRunLengths pre lengthsPre ++
            expandRunLengths mid lengthsMid ++
              expandRunLengths post lengthsPost := by
  let lengthsPre := lengths.take pre.length
  let lengthsRest := lengths.drop pre.length
  let lengthsMid := lengthsRest.take mid.length
  let lengthsPost := lengthsRest.drop mid.length
  have hlengths :
      lengths = lengthsPre ++ lengthsMid ++ lengthsPost := by
    calc
      lengths =
          lengths.take pre.length ++
            lengths.drop pre.length :=
        (List.take_append_drop pre.length lengths).symm
      _ = lengthsPre ++
          (lengthsRest.take mid.length ++
            lengthsRest.drop mid.length) := by
        rw [List.take_append_drop mid.length lengthsRest]
      _ = lengthsPre ++ lengthsMid ++ lengthsPost := by
        simp only [lengthsMid, lengthsPost, List.append_assoc]
  have htotal :
      lengths.length =
        pre.length + mid.length + post.length := by
    rw [← haligned, hrepr]
    simp only [List.length_append]
  have hpreLe : pre.length ≤ lengths.length := by
    omega
  have hrestLength :
      lengthsRest.length = mid.length + post.length := by
    simp only [lengthsRest, List.length_drop]
    omega
  have hmidLe : mid.length ≤ lengthsRest.length := by
    omega
  have hlengthPre :
      lengthsPre.length = pre.length := by
    simp [lengthsPre, Nat.min_eq_left hpreLe]
  have hlengthMid :
      lengthsMid.length = mid.length := by
    simp [lengthsMid, Nat.min_eq_left hmidLe]
  have hlengthPost :
      lengthsPost.length = post.length := by
    simp [lengthsPost, hrestLength]
  refine ⟨lengthsPre, lengthsMid, lengthsPost,
    hlengths, hlengthPre.symm, hlengthMid.symm,
    hlengthPost.symm, ?_⟩
  rw [hrepr, hlengths]
  calc
    expandRunLengths (pre ++ mid ++ post)
        (lengthsPre ++ lengthsMid ++ lengthsPost) =
      expandRunLengths (pre ++ mid)
          (lengthsPre ++ lengthsMid) ++
        expandRunLengths post lengthsPost := by
      apply expandRunLengths_append
      simp [hlengthPre, hlengthMid]
    _ = (expandRunLengths pre lengthsPre ++
          expandRunLengths mid lengthsMid) ++
        expandRunLengths post lengthsPost := by
      rw [expandRunLengths_append pre mid
        lengthsPre lengthsMid hlengthPre.symm]
    _ = expandRunLengths pre lengthsPre ++
        expandRunLengths mid lengthsMid ++
          expandRunLengths post lengthsPost := by
      simp only [List.append_assoc]

/-- Finite-word specialization of
`letterPositions_eq_Icc_of_decompose`, avoiding dependent casts through
`(List.ofFn w).length`. -/
theorem letterPositions_eq_Icc_of_ofFn_decompose
    [Fintype α] {M : ℕ} (S : Finset α)
    (w : Fin M → α) (pre mid post : List α)
    (hdecompose :
      List.ofFn w = pre ++ mid ++ post)
    (hpre : ∀ x ∈ pre, x ∉ S)
    (hmid : ∀ x ∈ mid, x ∈ S)
    (hpost : ∀ x ∈ post, x ∉ S)
    (hmidNonempty : mid ≠ []) :
    ∃ a b : Fin M,
      a ≤ b ∧ letterPositions w S = Finset.Icc a b := by
  have hmidPos : 0 < mid.length :=
    List.length_pos_iff.mpr hmidNonempty
  have hlength :
      M = pre.length + mid.length + post.length := by
    have h := congrArg List.length hdecompose
    simpa only [List.length_ofFn, List.length_append] using h
  let a : Fin M := ⟨pre.length, by omega⟩
  let b : Fin M :=
    ⟨pre.length + mid.length - 1, by omega⟩
  refine ⟨a, b, ?_, ?_⟩
  · apply Fin.mk_le_mk.mpr
    omega
  · ext i
    rw [mem_letterPositions]
    let i' : Fin (List.ofFn w).length :=
      Fin.cast (by simp) i
    have hget :
        (List.ofFn w).get i' = w i := by
      rw [List.get_ofFn]
      congr 1
    rw [← hget,
      get_mem_iff_middle_range_of_forall
        S (List.ofFn w) pre mid post
        hdecompose hpre hmid hpost i']
    simp only [Finset.mem_Icc]
    change
      (pre.length ≤ i.1 ∧
          i.1 < pre.length + mid.length) ↔
        pre.length ≤ i.1 ∧
          i.1 ≤ pre.length + mid.length - 1
    omega

/-- Inserting positive repetitions inside constant runs preserves the
paper's no-proper-leaf-block condition.  Thus run compression transports
primitivity to the compressed word. -/
theorem mergedWord_noProperLeafBlock
    [Fintype α] {M : ℕ} (w : Fin M → α)
    (hprimitive : NoProperLeafBlock w) :
    NoProperLeafBlock (mergedWord w) := by
  intro S hSNonempty hSProper a b hab hpositions
  change
    letterPositions
      (listWord (mergedWordList w)) S =
        Finset.Icc a b at hpositions
  obtain ⟨pre, mid, post, hdecompose, hmidNonempty,
      hpre, hmid, hpost⟩ :=
    decompose_of_letterPositions_eq_Icc
      S (mergedWordList w) a b hab hpositions
  let lengths := (mergedRunComposition w).blocks
  have haligned :
      (mergedWordList w).length = lengths.length := by
    exact (mergedRunComposition_blocks_length w).symm
  obtain ⟨lengthsPre, lengthsMid, lengthsPost,
      hlengths, hlengthPre, hlengthMid, hlengthPost,
      hexpand⟩ :=
    exists_expandRunLengths_three_parts
      (mergedWordList w) pre mid post lengths
      hdecompose haligned
  let expandedPre := expandRunLengths pre lengthsPre
  let expandedMid := expandRunLengths mid lengthsMid
  let expandedPost := expandRunLengths post lengthsPost
  have horiginal :
      List.ofFn w =
        expandedPre ++ expandedMid ++ expandedPost := by
    calc
      List.ofFn w =
          expandRunLengths (mergedWordList w) lengths := by
        exact (expandRunLengths_mergedRunComposition w).symm
      _ = expandedPre ++ expandedMid ++ expandedPost := by
        exact hexpand
  have hpreExpanded :
      ∀ x ∈ expandedPre, x ∉ S := by
    exact forall_mem_expandRunLengths
      pre lengthsPre (fun x => x ∉ S) hpre
  have hmidExpanded :
      ∀ x ∈ expandedMid, x ∈ S := by
    exact forall_mem_expandRunLengths
      mid lengthsMid (fun x => x ∈ S) hmid
  have hpostExpanded :
      ∀ x ∈ expandedPost, x ∉ S := by
    exact forall_mem_expandRunLengths
      post lengthsPost (fun x => x ∉ S) hpost
  have hlengthsMidPos :
      ∀ n ∈ lengthsMid, 0 < n := by
    intro n hn
    apply (mergedRunComposition w).blocks_pos
    change n ∈ lengths
    rw [hlengths]
    simp [hn]
  have hmidExpandedNonempty :
      expandedMid ≠ [] := by
    exact expandRunLengths_ne_nil
      mid lengthsMid hmidNonempty hlengthMid hlengthsMidPos
  obtain ⟨a', b', hab', hpositionsOriginal⟩ :=
    letterPositions_eq_Icc_of_ofFn_decompose
      S w expandedPre expandedMid expandedPost
      horiginal hpreExpanded hmidExpanded hpostExpanded
      hmidExpandedNonempty
  have hfullOriginal :
      Finset.Icc a' b' =
        (Finset.univ : Finset (Fin M)) :=
    hprimitive S hSNonempty hSProper
      a' b' hab' hpositionsOriginal
  have hwordPositionsFull :
      letterPositions w S =
        (Finset.univ : Finset (Fin M)) :=
    hpositionsOriginal.trans hfullOriginal
  have hcompressedAll :
      ∀ x ∈ mergedWordList w, x ∈ S := by
    intro x hx
    have hxOriginal :
        x ∈ List.ofFn w := by
      apply (mem_mergeEqualRuns_iff x (List.ofFn w)).mp
      simpa only [mergedWordList] using hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hxOriginal
    have hiPosition :
        i ∈ letterPositions w S := by
      rw [hwordPositionsFull]
      exact Finset.mem_univ i
    rw [mem_letterPositions, hi] at hiPosition
    exact hiPosition
  have hcompressedPositionsFull :
      letterPositions (mergedWord w) S =
        (Finset.univ :
          Finset (Fin (mergedWordList w).length)) := by
    ext i
    rw [mem_letterPositions]
    simp only [Finset.mem_univ, iff_true]
    apply hcompressedAll
    exact List.get_mem (mergedWordList w) i
  calc
    Finset.Icc a b =
        letterPositions (mergedWord w) S :=
      hpositions.symm
    _ = Finset.univ :=
      hcompressedPositionsFull

end

end Anderson4D
