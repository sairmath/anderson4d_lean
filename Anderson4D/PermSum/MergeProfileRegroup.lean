import Anderson4D.PermSum.MergeMultiplicityFamily
import Anderson4D.PermSum.MergeWeightBridge

/-!
# Exact run-compression regrouping by profile

This is the finite-sum ledger behind paper (5.34)--(5.37).  The source
domain is never enlarged in an equality: it consists of valid words
satisfying the paper's primitive word condition.  Their compressed words
are automatically no-adjacent and remain primitive.  Enlargement to a
larger list fiber occurs only in the cardinality upper bound.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A compressed outcome with its multiplicity coordinate packaged in the
finite profile carrier. -/
abbrev MergeProfileOutcome (ml : α → ℕ) :=
  MergeMultiplicityProfile ml × List α

/-- The packaged run-compression outcome of a valid word. -/
def mergedProfileOutcome {M : ℕ} (ml : α → ℕ)
    (w : MergeValidWord (M := M) ml) :
    MergeProfileOutcome ml :=
  (mergedMultiplicityProfile ml w, mergedWordList w.1)

@[simp]
theorem mergedProfileOutcome_fst {M : ℕ} (ml : α → ℕ)
    (w : MergeValidWord (M := M) ml) :
    (mergedProfileOutcome ml w).1 =
      mergedMultiplicityProfile ml w := by
  rfl

@[simp]
theorem mergedProfileOutcome_snd {M : ℕ} (ml : α → ℕ)
    (w : MergeValidWord (M := M) ml) :
    (mergedProfileOutcome ml w).2 = mergedWordList w.1 := by
  rfl

/-- The two canonical word views of a list agree. -/
private theorem listWord_eq_get {β : Type*} (l : List β) :
    listWord l = l.get := by
  apply List.ofFn_injective
  rw [ofFn_listWord]
  exact (List.ofFn_get l).symm

/-- Packaged outcomes realized by an arbitrary finite family of valid
words. -/
def mergeProfileOutcomeImage {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml)) :
    Finset (MergeProfileOutcome ml) := by
  classical
  exact s.image (mergedProfileOutcome ml)

/-- Exact regrouping by the full packaged outcome. -/
theorem sum_eq_sum_mergeProfileOutcome_fibers
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeProfileOutcome ml → ℝ) :
    (∑ w ∈ s, F (mergedProfileOutcome ml w)) =
      ∑ q ∈ mergeProfileOutcomeImage ml s,
        ((s.filter fun w =>
          mergedProfileOutcome ml w = q).card : ℝ) *
          F q := by
  classical
  symm
  calc
    (∑ q ∈ mergeProfileOutcomeImage ml s,
        ((s.filter fun w =>
          mergedProfileOutcome ml w = q).card : ℝ) * F q) =
        ∑ q ∈ mergeProfileOutcomeImage ml s,
          ∑ w ∈ s.filter
              (fun w => mergedProfileOutcome ml w = q),
            F (mergedProfileOutcome ml w) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc
        ((s.filter fun w =>
            mergedProfileOutcome ml w = q).card : ℝ) * F q =
            ∑ w ∈ s.filter
                (fun w => mergedProfileOutcome ml w = q),
              F q := by simp
        _ = ∑ w ∈ s.filter
              (fun w => mergedProfileOutcome ml w = q),
            F (mergedProfileOutcome ml w) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [(Finset.mem_filter.mp hw).2]
    _ = ∑ w ∈ s, F (mergedProfileOutcome ml w) := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun w hw =>
          Finset.mem_image.mpr ⟨w, hw, rfl⟩)
        (fun w => F (mergedProfileOutcome ml w))

/-- Exact regrouping of realized compressed outcomes by their multiplicity
profile. -/
theorem sum_mergeProfileOutcomeImage_eq_sum_profile_fibers
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeProfileOutcome ml → ℝ) :
    (∑ q ∈ mergeProfileOutcomeImage ml s, F q) =
      ∑ p ∈ mergeMultiplicityProfileImage ml s,
        ∑ q ∈ (mergeProfileOutcomeImage ml s).filter
            (fun q => q.1 = p),
          F q := by
  classical
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun q hq => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    F

/-- The literal two-stage regrouping used in the final assembly: first by
compressed multiplicity profile, then by the compressed representative
list. -/
theorem sum_eq_sum_profile_then_outcome_fibers
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeProfileOutcome ml → ℝ) :
    (∑ w ∈ s, F (mergedProfileOutcome ml w)) =
      ∑ p ∈ mergeMultiplicityProfileImage ml s,
        ∑ q ∈ (mergeProfileOutcomeImage ml s).filter
            (fun q => q.1 = p),
          ((s.filter fun w =>
            mergedProfileOutcome ml w = q).card : ℝ) *
            F q := by
  rw [sum_eq_sum_mergeProfileOutcome_fibers]
  exact sum_mergeProfileOutcomeImage_eq_sum_profile_fibers
    ml s (fun q =>
      ((s.filter fun w =>
        mergedProfileOutcome ml w = q).card : ℝ) * F q)

/-- A fixed packaged-outcome fiber has at most `2^M` elements.  The proof
injects the exact finite source fiber into the larger fiber obtained by
remembering only the compressed list, and then invokes the run-composition
count. -/
theorem card_filter_mergedProfileOutcome_le_two_pow
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (q : MergeProfileOutcome ml) :
    (s.filter fun w => mergedProfileOutcome ml w = q).card ≤
      2 ^ M := by
  classical
  let source :=
    s.filter fun w => mergedProfileOutcome ml w = q
  let target :=
    (validWords (M := M) ml).filter fun w =>
      mergedWordList w = q.2
  let inclusion : ↥source → ↥target :=
    fun w =>
      ⟨w.1.1, Finset.mem_filter.mpr
        ⟨w.1.2, by
          have houtcome :
              mergedProfileOutcome ml w.1 = q :=
            (Finset.mem_filter.mp w.2).2
          exact congrArg Prod.snd houtcome⟩⟩
  have hinjective : Function.Injective inclusion := by
    intro w₁ w₂ h
    apply Subtype.ext
    apply Subtype.ext
    simpa [inclusion] using congrArg Subtype.val h
  calc
    (s.filter fun w =>
        mergedProfileOutcome ml w = q).card =
        Fintype.card ↥source := by
      exact (Fintype.card_coe source).symm
    _ ≤ Fintype.card ↥target :=
      Fintype.card_le_of_injective inclusion hinjective
    _ = target.card := Fintype.card_coe target
    _ ≤ 2 ^ M :=
      card_filter_mergedWordList_le_two_pow
        (validWords (M := M) ml) q.2

/-- The primitive source domain from Proposition 5.7, represented without
dropping or adding any word. -/
def primitiveMergeWordFamily {M : ℕ} (ml : α → ℕ) :
    Finset (MergeValidWord (M := M) ml) :=
  Finset.univ.filter fun w => NoProperLeafBlock w.1

/-- Every outcome in the exact primitive image has the two restrictions
required for the Proposition 5.9 input: no adjacent equal letters and the
primitive word condition. -/
theorem mem_primitive_mergeProfileOutcomeImage_restrictions
    {M : ℕ} (ml : α → ℕ) (q : MergeProfileOutcome ml)
    (hq :
      q ∈ mergeProfileOutcomeImage ml
        (primitiveMergeWordFamily (M := M) ml)) :
    NoAdjacentEqual (listWord q.2) ∧
      NoProperLeafBlock (listWord q.2) := by
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  have hprimitive :
      NoProperLeafBlock w.1 :=
    (Finset.mem_filter.mp hw).2
  constructor
  · rw [listWord_eq_get]
    exact mergedWord_noAdjacentEqual w.1
  · rw [listWord_eq_get]
    exact mergedWord_noProperLeafBlock w.1 hprimitive

/-- Pulling a nonnegative compressed-outcome weight back to original words
costs at most the run-composition factor `2^M`. -/
theorem sum_comp_mergedProfileOutcome_le_two_pow_mul_sum
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeProfileOutcome ml → ℝ)
    (hF :
      ∀ q ∈ mergeProfileOutcomeImage ml s, 0 ≤ F q) :
    (∑ w ∈ s, F (mergedProfileOutcome ml w)) ≤
      (2 : ℝ) ^ M *
        ∑ q ∈ mergeProfileOutcomeImage ml s, F q := by
  rw [sum_eq_sum_mergeProfileOutcome_fibers]
  calc
    (∑ q ∈ mergeProfileOutcomeImage ml s,
        ((s.filter fun w =>
          mergedProfileOutcome ml w = q).card : ℝ) * F q) ≤
        ∑ q ∈ mergeProfileOutcomeImage ml s,
          (2 : ℝ) ^ M * F q := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          card_filter_mergedProfileOutcome_le_two_pow ml s q
      · exact hF q hq
    _ = (2 : ℝ) ^ M *
        ∑ q ∈ mergeProfileOutcomeImage ml s, F q := by
      rw [Finset.mul_sum]

/-- If the total compressed-outcome contribution is bounded uniformly for
each realized profile, then the profile count contributes at most
`2^(∑ ml)`. -/
theorem sum_mergeProfileOutcomeImage_le_two_pow_sum_mul
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeProfileOutcome ml → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hprofile :
      ∀ p ∈ mergeMultiplicityProfileImage ml s,
        (∑ q ∈ (mergeProfileOutcomeImage ml s).filter
            (fun q => q.1 = p),
          F q) ≤ B) :
    (∑ q ∈ mergeProfileOutcomeImage ml s, F q) ≤
      (2 : ℝ) ^ (∑ a : α, ml a) * B := by
  rw [sum_mergeProfileOutcomeImage_eq_sum_profile_fibers]
  calc
    (∑ p ∈ mergeMultiplicityProfileImage ml s,
        ∑ q ∈ (mergeProfileOutcomeImage ml s).filter
            (fun q => q.1 = p),
          F q) ≤
        ∑ _p ∈ mergeMultiplicityProfileImage ml s, B := by
      exact Finset.sum_le_sum fun p hp => hprofile p hp
    _ = ((mergeMultiplicityProfileImage ml s).card : ℝ) * B := by
      simp
    _ ≤ (2 : ℝ) ^ (∑ a : α, ml a) * B := by
      gcongr
      exact_mod_cast
        card_mergeMultiplicityProfileImage_le_two_pow_sum ml s

/-- General two-ledger bound: one `2^M` for expansions of a fixed
compressed outcome and one `2^(∑ ml)` for possible multiplicity profiles. -/
theorem sum_comp_mergedProfileOutcome_le_two_pow_mul_two_pow_sum
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (F : MergeProfileOutcome ml → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hF :
      ∀ q ∈ mergeProfileOutcomeImage ml s, 0 ≤ F q)
    (hprofile :
      ∀ p ∈ mergeMultiplicityProfileImage ml s,
        (∑ q ∈ (mergeProfileOutcomeImage ml s).filter
            (fun q => q.1 = p),
          F q) ≤ B) :
    (∑ w ∈ s, F (mergedProfileOutcome ml w)) ≤
      (2 : ℝ) ^ M *
        ((2 : ℝ) ^ (∑ a : α, ml a) * B) := by
  calc
    (∑ w ∈ s, F (mergedProfileOutcome ml w)) ≤
        (2 : ℝ) ^ M *
          ∑ q ∈ mergeProfileOutcomeImage ml s, F q :=
      sum_comp_mergedProfileOutcome_le_two_pow_mul_sum
        ml s F hF
    _ ≤ (2 : ℝ) ^ M *
        ((2 : ℝ) ^ (∑ a : α, ml a) * B) := by
      gcongr
      exact sum_mergeProfileOutcomeImage_le_two_pow_sum_mul
        ml s F B hB hprofile

/-- Final-assembly-facing form on the exact primitive domain.  When the
original multiplicities sum to the word length, the two binary ledgers
combine to the explicit loss `4^M`. -/
theorem primitive_merge_regroup_le_four_pow
    {M : ℕ} (ml : α → ℕ)
    (hsum : (∑ a : α, ml a) = M)
    (F : MergeProfileOutcome ml → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hF :
      ∀ q ∈ mergeProfileOutcomeImage ml
          (primitiveMergeWordFamily (M := M) ml),
        0 ≤ F q)
    (hprofile :
      ∀ p ∈ mergeMultiplicityProfileImage ml
          (primitiveMergeWordFamily (M := M) ml),
        (∑ q ∈
            (mergeProfileOutcomeImage ml
              (primitiveMergeWordFamily (M := M) ml)).filter
                (fun q => q.1 = p),
          F q) ≤ B) :
    (∑ w ∈ primitiveMergeWordFamily (M := M) ml,
        F (mergedProfileOutcome ml w)) ≤
      (4 : ℝ) ^ M * B := by
  calc
    (∑ w ∈ primitiveMergeWordFamily (M := M) ml,
        F (mergedProfileOutcome ml w)) ≤
        (2 : ℝ) ^ M *
          ((2 : ℝ) ^ (∑ a : α, ml a) * B) :=
      sum_comp_mergedProfileOutcome_le_two_pow_mul_two_pow_sum
        ml (primitiveMergeWordFamily (M := M) ml)
        F B hB hF hprofile
    _ = (4 : ℝ) ^ M * B := by
      rw [hsum, ← mul_assoc, ← mul_pow]
      norm_num

/-! ## Fixed-profile words for the Proposition 5.9 call -/

/-- Total length encoded by a packaged multiplicity profile. -/
def MergeMultiplicityProfile.total {ml : α → ℕ}
    (p : MergeMultiplicityProfile ml) : ℕ :=
  ∑ a : α, p.toNat a

/-- Every realized outcome whose first coordinate is `p` has the length
encoded by `p`. -/
theorem mergeProfileOutcome_length_eq_total
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (p : MergeMultiplicityProfile ml)
    (q : MergeProfileOutcome ml)
    (hq : q ∈ mergeProfileOutcomeImage ml s)
    (hqp : q.1 = p) :
    q.2.length = p.total := by
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  calc
    (mergedWordList w.1).length =
        ∑ a : α, (mergedMultiplicityProfile ml w a : ℕ) :=
      (sum_mergedMultiplicityProfile ml w).symm
    _ = p.total := by
      change mergedMultiplicityProfile ml w = p at hqp
      rw [hqp]
      rfl

/-- Transport a list word to a prescribed, propositionally equal length. -/
private def castListWord {β : Type*} (l : List β) {N : ℕ}
    (h : l.length = N) : Fin N → β :=
  h ▸ listWord l

private theorem ofFn_castListWord {β : Type*} (l : List β) {N : ℕ}
    (h : l.length = N) :
    List.ofFn (castListWord l h) = l := by
  cases h
  simp [castListWord]

private theorem castListWord_mem_validWords
    {β : Type*} [Fintype β] [DecidableEq β]
    (l : List β) {N : ℕ} (h : l.length = N)
    (mult : β → ℕ)
    (hl : listWord l ∈ validWords mult) :
    castListWord l h ∈ validWords mult := by
  cases h
  simpa [castListWord] using hl

private theorem castListWord_noAdjacentEqual
    {β : Type*} [DecidableEq β]
    (l : List β) {N : ℕ} (h : l.length = N)
    (hl : NoAdjacentEqual (listWord l)) :
    NoAdjacentEqual (castListWord l h) := by
  cases h
  simpa [castListWord] using hl

private theorem castListWord_noProperLeafBlock
    {β : Type*} [Fintype β] [DecidableEq β]
    (l : List β) {N : ℕ} (h : l.length = N)
    (hl : NoProperLeafBlock (listWord l)) :
    NoProperLeafBlock (castListWord l h) := by
  cases h
  simpa [castListWord] using hl

/-- The list representative of every realized outcome has exactly its
profile multiplicity before the harmless length transport. -/
theorem listWord_mem_validWords_profile_toNat
    {M : ℕ} (ml : α → ℕ)
    (s : Finset (MergeValidWord (M := M) ml))
    (q : MergeProfileOutcome ml)
    (hq : q ∈ mergeProfileOutcomeImage ml s) :
    listWord q.2 ∈ validWords q.1.toNat := by
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rw [listWord_eq_get]
  change
    mergedWord w.1 ∈
      validWords (mergedMultiplicityProfile ml w).toNat
  rw [mergedMultiplicityProfile_toNat]
  exact mergedWord_mem_validWords w.1

/-- The exact compressed-outcome fiber at a fixed multiplicity profile,
retaining the primitive source domain. -/
def primitiveProfileOutcomeFiber {M : ℕ} (ml : α → ℕ)
    (p : MergeMultiplicityProfile ml) :
    Finset (MergeProfileOutcome ml) :=
  (mergeProfileOutcomeImage ml
      (primitiveMergeWordFamily (M := M) ml)).filter
    fun q => q.1 = p

/-- A fixed-profile outcome, cast to the common profile length. -/
def primitiveProfileFiberWord {M : ℕ} (ml : α → ℕ)
    (p : MergeMultiplicityProfile ml)
    (q : ↥(primitiveProfileOutcomeFiber (M := M) ml p)) :
    Fin p.total → α :=
  castListWord q.1.2 <|
    mergeProfileOutcome_length_eq_total
      ml (primitiveMergeWordFamily (M := M) ml)
      p q.1 (Finset.mem_filter.mp q.2).1
      (Finset.mem_filter.mp q.2).2

@[simp]
theorem ofFn_primitiveProfileFiberWord
    {M : ℕ} (ml : α → ℕ)
    (p : MergeMultiplicityProfile ml)
    (q : ↥(primitiveProfileOutcomeFiber (M := M) ml p)) :
    List.ofFn (primitiveProfileFiberWord ml p q) = q.1.2 := by
  unfold primitiveProfileFiberWord
  exact ofFn_castListWord _ _

/-- Fixed-profile outcome words are honest words with multiplicity
`p.toNat`. -/
theorem primitiveProfileFiberWord_mem_validWords
    {M : ℕ} (ml : α → ℕ)
    (p : MergeMultiplicityProfile ml)
    (q : ↥(primitiveProfileOutcomeFiber (M := M) ml p)) :
    primitiveProfileFiberWord ml p q ∈
      validWords p.toNat := by
  have hqImage :
      q.1 ∈ mergeProfileOutcomeImage ml
        (primitiveMergeWordFamily (M := M) ml) :=
    (Finset.mem_filter.mp q.2).1
  have hqp : q.1.1 = p :=
    (Finset.mem_filter.mp q.2).2
  have hvalid :
      listWord q.1.2 ∈ validWords q.1.1.toNat :=
    listWord_mem_validWords_profile_toNat ml
      (primitiveMergeWordFamily (M := M) ml) q.1 hqImage
  rw [hqp] at hvalid
  exact castListWord_mem_validWords q.1.2
    (mergeProfileOutcome_length_eq_total
      ml (primitiveMergeWordFamily (M := M) ml)
      p q.1 hqImage hqp)
    p.toNat hvalid

/-- The common-length representative retains both paper restrictions. -/
theorem primitiveProfileFiberWord_restrictions
    {M : ℕ} (ml : α → ℕ)
    (p : MergeMultiplicityProfile ml)
    (q : ↥(primitiveProfileOutcomeFiber (M := M) ml p)) :
    NoAdjacentEqual (primitiveProfileFiberWord ml p q) ∧
      NoProperLeafBlock (primitiveProfileFiberWord ml p q) := by
  have hqImage :
      q.1 ∈ mergeProfileOutcomeImage ml
        (primitiveMergeWordFamily (M := M) ml) :=
    (Finset.mem_filter.mp q.2).1
  have hqp : q.1.1 = p :=
    (Finset.mem_filter.mp q.2).2
  have hrestrictions :=
    mem_primitive_mergeProfileOutcomeImage_restrictions
      ml q.1 hqImage
  let hlength :=
    mergeProfileOutcome_length_eq_total
      ml (primitiveMergeWordFamily (M := M) ml)
      p q.1 hqImage hqp
  exact
    ⟨castListWord_noAdjacentEqual q.1.2 hlength hrestrictions.1,
      castListWord_noProperLeafBlock q.1.2 hlength hrestrictions.2⟩

/-- Distinct fixed-profile compressed outcomes give distinct common-length
words. -/
theorem primitiveProfileFiberWord_injective
    {M : ℕ} (ml : α → ℕ)
    (p : MergeMultiplicityProfile ml) :
    Function.Injective
      (primitiveProfileFiberWord (M := M) ml p) := by
  intro q₁ q₂ hword
  have hlists := congrArg List.ofFn hword
  simp only [ofFn_primitiveProfileFiberWord] at hlists
  apply Subtype.ext
  apply Prod.ext
  · exact
      ((Finset.mem_filter.mp q₁.2).2).trans
        ((Finset.mem_filter.mp q₂.2).2).symm
  · exact hlists

section HeppWeight

open PlaneTree

variable {t : PlaneTree}

private theorem heppChainWeight_castListWord
    (z : HeppLeaf t → Fin 4 → ℤ)
    (l : List (HeppLeaf t)) {N : ℕ}
    (h : l.length = N) :
    heppChainWeight z (castListWord l h) =
      heppChainWeight z (listWord l) := by
  cases h
  simp [castListWord]

/-- On a fixed profile fiber, the transported primitive-separated weight is
the chain weight of the original compressed list. -/
theorem primitiveSeparatedChainWeight_profileFiberWord
    {M : ℕ} (ml : HeppLeaf t → ℕ)
    (p : MergeMultiplicityProfile ml)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (q : ↥(primitiveProfileOutcomeFiber (M := M) ml p)) :
    primitiveSeparatedChainWeight z
        (primitiveProfileFiberWord ml p q) =
      heppChainWeight z (listWord q.1.2) := by
  have hrestrictions :=
    primitiveProfileFiberWord_restrictions ml p q
  unfold primitiveSeparatedChainWeight
  rw [if_pos ⟨hrestrictions.2, hrestrictions.1⟩]
  unfold primitiveProfileFiberWord
  exact heppChainWeight_castListWord z q.1.2 _

/-- The compressed chain-weight sum for one realized profile embeds into
the exact `wordSum` to which Proposition 5.9 applies.  No word-domain
equality is claimed: the last step enlarges by nonnegativity. -/
theorem sum_primitiveProfileFiber_chainWeight_le_wordSum
    {M : ℕ} (ml : HeppLeaf t → ℕ)
    (p : MergeMultiplicityProfile ml)
    (z : HeppLeaf t → Fin 4 → ℤ) :
    (∑ q : ↥(primitiveProfileOutcomeFiber (M := M) ml p),
        heppChainWeight z (listWord q.1.2)) ≤
      wordSum (M := p.total) p.toNat
        (primitiveSeparatedChainWeight z) := by
  classical
  let f :=
    primitiveProfileFiberWord (M := M) ml p
  have hinjective : Function.Injective f :=
    primitiveProfileFiberWord_injective ml p
  have hsubset :
      (Finset.univ.image f) ⊆ validWords p.toNat := by
    intro w hw
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hw
    exact primitiveProfileFiberWord_mem_validWords ml p q
  calc
    (∑ q : ↥(primitiveProfileOutcomeFiber (M := M) ml p),
        heppChainWeight z (listWord q.1.2)) =
        ∑ q : ↥(primitiveProfileOutcomeFiber (M := M) ml p),
          primitiveSeparatedChainWeight z (f q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact
        (primitiveSeparatedChainWeight_profileFiberWord
          ml p z q).symm
    _ = ∑ w ∈ Finset.univ.image f,
        primitiveSeparatedChainWeight z w := by
      rw [Finset.sum_image]
      intro q₁ _ q₂ _ h
      exact hinjective h
    _ ≤ ∑ w ∈ validWords p.toNat,
        primitiveSeparatedChainWeight z w := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun w _ _ =>
          primitiveSeparatedChainWeight_nonneg z w)
    _ = wordSum (M := p.total) p.toNat
        (primitiveSeparatedChainWeight z) := rfl

end HeppWeight

end

end Anderson4D
