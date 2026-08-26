import Mathlib

/-!
# Words, the definitional factorial ledger, and word-level collapse

PAPER_MAP node **D-ledger** for Deng–Shen (arXiv:2607.10105),
implementing the *pure word model* of DESIGN §5.5: all §5.4 permutation sums with
multiplicities ((5.15), (5.33)) are stated as sums over word maps `w : Fin M → α`
with prescribed fiber sizes (`validWords`), never over labeled copies.

* `Anderson4D.validWords`, `Anderson4D.inducedWord` — admissible words and the word
  induced by a labeled arrangement `σ : Fin M ≃ Σ a, Fin (mult a)`.
* `Anderson4D.card_arrangements_fiber`, `Anderson4D.ledger_sum` — a valid word is
  induced by exactly `∏ a, (mult a)!` labeled arrangements, so any statistic summed
  over labeled arrangements equals `∏ a, (mult a)!` times its sum over valid words.
* `Anderson4D.wordSum`, `Anderson4D.paperSum` — the **definitional ledger**
  `paperSum mult F := (∏ a, ((mult a)! : ℝ)) * wordSum mult F`;
  statements of P-5.7/P-5.9/P-5.10 put `paperSum` on the left-hand side, and
  `paperSum_eq_sum_arrangements` converts at statement boundaries.
* `Anderson4D.NoAdjacentEqual` — the "no adjacent equal letters" side condition of
  (5.15)/(5.33), with a decidability instance.
* `Anderson4D.wordCollapseEquiv` — the §5.4.1 collapse as an honest word-level
  `Equiv`: a word over `A ⊕ B` is the same data as its nonempty blocks
  (maximal runs of inside letters) plus its collapsed word over `Unit ⊕ B` with
  markers pairwise non-adjacent and marker count = block count.  Letter counts
  transport (`count_inl_collapse`, `count_inr_collapse`).
* `Anderson4D.wordSumFiltered`, `Anderson4D.paperSumFiltered` — restricted sums
  over words satisfying a side condition, with monotonicity for nonnegative `F`.

This is the stable word carrier used by the permutation-sum formalization.
-/

namespace Anderson4D

/-! ### The word-level collapse equivalence -/

variable {A B : Type*}

/-- No two adjacent letters of `s` are both markers (`Sum.inl _`).  This expresses that
the marked positions come from *maximal* runs of inside letters. -/
def NoTwoAdjacentMarkers (s : List (Unit ⊕ B)) : Prop :=
  s.IsChain fun x y => x.isLeft = false ∨ y.isLeft = false

/-- The number of markers in a collapsed word.  Stated via `countP Sum.isLeft` so that no
decidable equality on `B` is needed; see `markerCount_eq_count` for the version with
`List.count (Sum.inl ())`. -/
def markerCount (s : List (Unit ⊕ B)) : ℕ :=
  s.countP (·.isLeft)

/-- Collapse a word into its list of blocks (maximal runs of inside letters) and its
collapsed word (each maximal run replaced by one marker `Sum.inl ()`). -/
def collapse : List (A ⊕ B) → List (List A) × List (Unit ⊕ B)
  | [] => ([], [])
  | .inr b :: w => ((collapse w).1, .inr b :: (collapse w).2)
  | [.inl a] => ([[a]], [.inl ()])
  | .inl a :: .inl a' :: w =>
      ((collapse (.inl a' :: w)).1.modifyHead (a :: ·), (collapse (.inl a' :: w)).2)
  | .inl a :: .inr b :: w =>
      ([a] :: (collapse (.inr b :: w)).1, .inl () :: (collapse (.inr b :: w)).2)

/-- Substitute the i-th block for the i-th marker (in order): the inverse of `collapse`.
On inputs violating the block/marker bookkeeping it silently drops the offending data;
such inputs are excluded by the subtype in `wordCollapseEquiv`. -/
def expand : List (List A) → List (Unit ⊕ B) → List (A ⊕ B)
  | _, [] => []
  | bs, .inr b :: s => .inr b :: expand bs s
  | [], .inl _ :: s => expand [] s
  | blk :: bs, .inl _ :: s => blk.map .inl ++ expand bs s

/-! #### Small facts about `NoTwoAdjacentMarkers` -/

theorem nta_nil : NoTwoAdjacentMarkers ([] : List (Unit ⊕ B)) := .nil

theorem nta_cons_inr {s : List (Unit ⊕ B)} (b : B) (h : NoTwoAdjacentMarkers s) :
    NoTwoAdjacentMarkers (Sum.inr b :: s) := by
  cases s with
  | nil => exact .singleton _
  | cons y t => exact .cons_cons (Or.inl rfl) h

theorem nta_inl_cons_inr {s : List (Unit ⊕ B)} (u : Unit) (b : B)
    (h : NoTwoAdjacentMarkers (Sum.inr b :: s)) :
    NoTwoAdjacentMarkers (Sum.inl u :: Sum.inr b :: s) :=
  .cons_cons (Or.inr rfl) h

theorem nta_of_cons {x : Unit ⊕ B} {s : List (Unit ⊕ B)}
    (h : NoTwoAdjacentMarkers (x :: s)) : NoTwoAdjacentMarkers s := by
  cases s with
  | nil => exact .nil
  | cons y t => exact (List.isChain_cons_cons.1 h).2

/-- After a marker, the next letter (if any) is an outside letter. -/
theorem nta_marker_head {u : Unit} {y : Unit ⊕ B} {s : List (Unit ⊕ B)}
    (h : NoTwoAdjacentMarkers (Sum.inl u :: y :: s)) : ∃ b : B, y = Sum.inr b := by
  obtain ⟨hr, -⟩ := List.isChain_cons_cons.1 h
  cases y with
  | inl v => simp at hr
  | inr b => exact ⟨b, rfl⟩

/-! #### Structure of `collapse` -/

/-- A word starting with an inside letter collapses to a first block starting with that
letter and a collapsed word starting with a marker. -/
theorem collapse_inl_cons (w : List (A ⊕ B)) :
    ∀ a : A, ∃ tl bs s,
      collapse (Sum.inl a :: w) = ((a :: tl) :: bs, Sum.inl () :: s) := by
  induction w with
  | nil => exact fun a => ⟨[], [], [], by simp [collapse]⟩
  | cons x w ih =>
    intro a
    cases x with
    | inl a' =>
      obtain ⟨tl, bs, s, h⟩ := ih a'
      exact ⟨a' :: tl, bs, s, by simp [collapse, h, List.modifyHead]⟩
    | inr b =>
      exact ⟨[], (collapse (Sum.inr b :: w)).1, (collapse (Sum.inr b :: w)).2,
        by simp [collapse]⟩

/-- Collapsing a nonempty inside run prepended to a word that does not start with an
inside letter: the run becomes the first block and contributes one marker. -/
theorem collapse_inlRun_append (as : List A) (a : A) (w : List (A ⊕ B))
    (hw : w = [] ∨ ∃ b w', w = Sum.inr b :: w') :
    collapse ((a :: as).map Sum.inl ++ w)
      = ((a :: as) :: (collapse w).1, Sum.inl () :: (collapse w).2) := by
  induction as generalizing a with
  | nil =>
    rcases hw with rfl | ⟨b, w', rfl⟩
    · simp [collapse]
    · simp [collapse]
  | cons a' as ih =>
    have h := ih a'
    simp only [List.map_cons, List.cons_append] at h ⊢
    simp only [collapse, h, List.modifyHead]

/-- `expand` never produces a word starting with an inside letter, provided the collapsed
word does not start with a marker. -/
theorem expand_shape (bs : List (List A)) (s : List (Unit ⊕ B))
    (hs : s = [] ∨ ∃ b s', s = Sum.inr b :: s') :
    expand bs s = [] ∨ ∃ b w', expand bs s = Sum.inr b :: w' := by
  rcases hs with rfl | ⟨b, s', rfl⟩
  · left; cases bs <;> simp [expand]
  · right; exact ⟨b, expand bs s', by simp [expand]⟩

/-- The three structural invariants of a collapsed word: all blocks are nonempty, the
marker count equals the block count, and no two markers are adjacent. -/
theorem collapse_spec (w : List (A ⊕ B)) :
    (∀ blk ∈ (collapse w).1, blk ≠ []) ∧
      markerCount (collapse w).2 = (collapse w).1.length ∧
      NoTwoAdjacentMarkers (collapse w).2 := by
  induction w with
  | nil => exact ⟨by simp [collapse], by simp [collapse, markerCount], nta_nil⟩
  | cons x w ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    cases x with
    | inr b =>
      refine ⟨by simpa only [collapse] using ih1, ?_, ?_⟩
      · simp only [collapse, markerCount, List.countP_cons] at ih2 ⊢
        simpa using ih2
      · simp only [collapse]
        exact nta_cons_inr b ih3
    | inl a =>
      cases w with
      | nil =>
        refine ⟨by simp [collapse], by simp [collapse, markerCount], ?_⟩
        simp only [collapse]
        exact .singleton _
      | cons y w' =>
        cases y with
        | inl a' =>
          obtain ⟨tl, bs, s, h⟩ := collapse_inl_cons w' a'
          rw [h] at ih1 ih2 ih3
          refine ⟨?_, ?_, ?_⟩
          · simp only [collapse, h, List.modifyHead]
            intro blk hblk
            rcases List.mem_cons.1 hblk with rfl | hblk
            · simp
            · exact ih1 blk (List.mem_cons_of_mem _ hblk)
          · simp only [collapse, h, List.modifyHead] at ih2 ⊢
            simpa using ih2
          · simpa only [collapse, h] using ih3
        | inr b =>
          simp only [collapse] at ih1 ih2 ih3 ⊢
          refine ⟨?_, ?_, ?_⟩
          · intro blk hblk
            rcases List.mem_cons.1 hblk with rfl | hblk
            · simp
            · exact ih1 blk hblk
          · simp only [markerCount, List.countP_cons] at ih2 ⊢
            simpa using ih2
          · exact nta_inl_cons_inr () b ih3

/-- Right inverse: collapsing an expansion recovers the block/marker data. -/
theorem collapse_expand (s : List (Unit ⊕ B)) (bs : List (List A))
    (hbs : ∀ blk ∈ bs, blk ≠ []) (hlen : markerCount s = bs.length)
    (hnta : NoTwoAdjacentMarkers s) :
    collapse (expand bs s) = (bs, s) := by
  induction s generalizing bs with
  | nil =>
    obtain rfl : bs = [] := by
      simpa [markerCount] using hlen.symm
    simp [expand, collapse]
  | cons x s ih =>
    cases x with
    | inr b =>
      have h1 : markerCount s = bs.length := by
        simpa [markerCount] using hlen
      simp only [expand, collapse, ih bs hbs h1 (nta_of_cons hnta)]
    | inl u =>
      cases bs with
      | nil => simp [markerCount] at hlen
      | cons blk bs =>
        obtain ⟨a, as, rfl⟩ : ∃ a as, blk = a :: as := by
          cases blk with
          | nil => exact absurd rfl (hbs [] (List.mem_cons_self ..))
          | cons a as => exact ⟨a, as, rfl⟩
        have hbs' : ∀ blk ∈ bs, blk ≠ [] :=
          fun blk hblk => hbs blk (List.mem_cons_of_mem _ hblk)
        have hlen' : markerCount s = bs.length := by
          simpa [markerCount] using hlen
        have hs' : s = [] ∨ ∃ b s', s = Sum.inr b :: s' := by
          cases s with
          | nil => exact Or.inl rfl
          | cons y t =>
            obtain ⟨b, rfl⟩ := nta_marker_head (u := u) hnta
            exact Or.inr ⟨b, t, rfl⟩
        simp only [expand,
          collapse_inlRun_append as a _ (expand_shape bs s hs'),
          ih bs hbs' hlen' (nta_of_cons hnta)]

/-- Left inverse: expanding the collapse of a word recovers the word. -/
theorem expand_collapse (w : List (A ⊕ B)) :
    expand (collapse w).1 (collapse w).2 = w := by
  induction w with
  | nil => simp [collapse, expand]
  | cons x w ih =>
    cases x with
    | inr b =>
      simp only [collapse, expand, ih]
    | inl a =>
      cases w with
      | nil => simp [collapse, expand]
      | cons y w' =>
        cases y with
        | inl a' =>
          obtain ⟨tl, bs, s, h⟩ := collapse_inl_cons w' a'
          rw [h] at ih
          simp only [collapse, h, List.modifyHead]
          simp only [expand, List.map_cons, List.cons_append] at ih ⊢
          simpa using ih
        | inr b =>
          simp only [collapse] at ih ⊢
          simp only [expand, List.map_cons, List.map_nil, List.singleton_append] at ih ⊢
          simpa using ih

/-- **Word-level collapse equivalence** (§5.4.1 collapse, DESIGN §5.5).  A word over
`A ⊕ B` is the same data as a list of nonempty blocks over `A` together with a collapsed
word over `Unit ⊕ B` whose marker count equals the number of blocks and in which no two
markers are adjacent.  The forward map is `collapse`; the inverse substitutes the i-th
block for the i-th marker. -/
def wordCollapseEquiv (A B : Type*) :
    List (A ⊕ B) ≃
      { p : List (List A) × List (Unit ⊕ B) //
        (∀ blk ∈ p.1, blk ≠ []) ∧ markerCount p.2 = p.1.length ∧
          NoTwoAdjacentMarkers p.2 } where
  toFun w := ⟨collapse w, collapse_spec w⟩
  invFun p := expand p.1.1 p.1.2
  left_inv w := expand_collapse w
  right_inv p := Subtype.ext (collapse_expand p.1.2 p.1.1 p.2.1 p.2.2.1 p.2.2.2)

/-! #### Letter-count transport

Mathlib's `Sum.instBEq` currently has no `LawfulBEq` instance, so we first record how
`==` computes on constructors; this lets `simp` normalize `List.count` on sum types. -/

@[simp] theorem inl_beq_inl [BEq A] [BEq B] (a a' : A) :
    ((Sum.inl a : A ⊕ B) == Sum.inl a') = (a == a') := rfl

@[simp] theorem inr_beq_inr [BEq A] [BEq B] (b b' : B) :
    ((Sum.inr b : A ⊕ B) == Sum.inr b') = (b == b') := rfl

@[simp] theorem inl_beq_inr [BEq A] [BEq B] (a : A) (b : B) :
    ((Sum.inl a : A ⊕ B) == Sum.inr b) = false := rfl

@[simp] theorem inr_beq_inl [BEq A] [BEq B] (a : A) (b : B) :
    ((Sum.inr b : A ⊕ B) == Sum.inl a) = false := rfl

/-- With decidable equality available, `markerCount` is the count of the marker letter. -/
theorem markerCount_eq_count [DecidableEq B] (s : List (Unit ⊕ B)) :
    markerCount s = s.count (Sum.inl ()) := by
  induction s with
  | nil => simp [markerCount]
  | cons x s ih =>
    simp only [markerCount, List.countP_cons] at ih ⊢
    rw [List.count_cons, ih]
    cases x with
    | inl u => cases u; simp
    | inr b => simp

/-- Inside-letter counts sum over the blocks of the collapse. -/
theorem count_inl_collapse [DecidableEq A] [DecidableEq B] (a : A) (w : List (A ⊕ B)) :
    w.count (Sum.inl a) = ((collapse w).1.map fun blk => blk.count a).sum := by
  induction w with
  | nil => simp [collapse]
  | cons x w ih =>
    cases x with
    | inr b =>
      simpa [collapse, List.count_cons] using ih
    | inl a' =>
      cases w with
      | nil => simp [collapse, List.count_cons]
      | cons y w' =>
        cases y with
        | inl a'' =>
          obtain ⟨tl, bs, s, h⟩ := collapse_inl_cons w' a''
          rw [h] at ih
          simp [collapse, h, List.modifyHead, List.count_cons] at ih ⊢
          omega
        | inr b =>
          simp [collapse, List.count_cons] at ih ⊢
          omega

/-- Outside-letter counts are preserved by the collapse. -/
theorem count_inr_collapse [DecidableEq A] [DecidableEq B] (b : B) (w : List (A ⊕ B)) :
    w.count (Sum.inr b) = (collapse w).2.count (Sum.inr b) := by
  induction w with
  | nil => simp [collapse]
  | cons x w ih =>
    cases x with
    | inr b' =>
      simp [collapse, List.count_cons, ih]
    | inl a =>
      cases w with
      | nil => simp [collapse, List.count_cons]
      | cons y w' =>
        cases y with
        | inl a' =>
          simpa [collapse, List.count_cons] using ih
        | inr b' =>
          simp [collapse, List.count_cons] at ih ⊢
          omega

/-! #### Concrete sanity checks (`A := Bool`, `B := Fin 2`) -/

private def demoWord : List (Bool ⊕ Fin 2) :=
  [.inl true, .inl false, .inr 0, .inr 1, .inl true]

#guard collapse demoWord
  = ([[true, false], [true]], [.inl (), .inr 0, .inr 1, .inl ()])
#guard expand (collapse demoWord).1 (collapse demoWord).2 = demoWord
#guard (wordCollapseEquiv Bool (Fin 2)).symm (wordCollapseEquiv Bool (Fin 2) demoWord)
  = demoWord
#guard ((wordCollapseEquiv Bool (Fin 2)) demoWord).val.2.length = 4
#guard markerCount ((wordCollapseEquiv Bool (Fin 2)) demoWord).val.2 = 2
#guard demoWord.count (.inl true) = 2
#guard ((collapse demoWord).1.map fun blk => blk.count true).sum = 2
#guard demoWord.count (.inr 0) = (collapse demoWord).2.count (.inr 0)

/-! ### The factorial ledger -/

/-- The fiber of a sigma type over a point `a` of the base. -/
def sigmaFstFiber {ι : Type*} {β : ι → Type*} (a : ι) :
    { x : Σ i, β i // x.1 = a } ≃ β a where
  toFun x := x.2 ▸ x.1.2
  invFun y := ⟨⟨a, y⟩, rfl⟩
  left_inv := by rintro ⟨⟨i, y⟩, rfl⟩; rfl
  right_inv y := rfl

private theorem sigma_mk_eq_of_fst_eq {ι : Type*} {β : ι → Type*} (x : Σ i, β i) {c : ι}
    (h : x.1 = c) : (⟨c, h ▸ x.2⟩ : Σ i, β i) = x := by
  rcases x with ⟨i, y⟩
  subst h
  rfl

section Ledger

open scoped Nat

variable {α : Type*} [Fintype α] [DecidableEq α] {M : ℕ} (mult : α → ℕ)

/-- The word induced by a labeled arrangement: forget the labels. -/
def inducedWord (σ : Fin M ≃ Σ a : α, Fin (mult a)) : Fin M → α :=
  fun j => (σ j).1

/-- The family of fiber bijections extracted from a labeled arrangement inducing `w`. -/
def toFiberEquiv (w : Fin M → α) (σ : Fin M ≃ Σ a : α, Fin (mult a))
    (hσ : ∀ j, (σ j).1 = w j) (a : α) : { j : Fin M // w j = a } ≃ Fin (mult a) :=
  (σ.subtypeEquiv (q := fun y : Σ a' : α, Fin (mult a') => y.1 = a)
    fun j => by rw [hσ j]).trans (sigmaFstFiber a)

/-- A labeled arrangement inducing the word `w` is the same data as a family of
bijections from the fibers of `w` to the multiplicity index sets. -/
def arrangementEquivFiberEquivs (w : Fin M → α) :
    { σ : Fin M ≃ Σ a : α, Fin (mult a) // ∀ j, (σ j).1 = w j }
      ≃ ∀ a : α, ({ j : Fin M // w j = a } ≃ Fin (mult a)) where
  toFun σ a := toFiberEquiv mult w σ.1 σ.2 a
  invFun F :=
    ⟨(Equiv.sigmaFiberEquiv w).symm.trans (Equiv.sigmaCongrRight F), fun j => rfl⟩
  left_inv := by
    rintro ⟨σ, hσ⟩
    refine Subtype.ext (Equiv.ext fun j => ?_)
    exact sigma_mk_eq_of_fst_eq (σ j) (hσ j)
  right_inv := by
    intro F
    funext a
    refine Equiv.ext fun x => ?_
    obtain ⟨j, hj⟩ := x
    subst hj
    rfl

/-- **Fiber-count lemma.**  A word `w` with the fiber condition
`#{j | w j = a} = mult a` is induced by exactly `∏ a, (mult a)!` labeled arrangements:
the `(mult a)!` relabelings within each letter fiber act freely and transitively. -/
theorem card_arrangements_fiber (w : Fin M → α)
    (hw : ∀ a, (Finset.univ.filter fun j => w j = a).card = mult a) :
    Fintype.card { σ : Fin M ≃ Σ a : α, Fin (mult a) // ∀ j, (σ j).1 = w j }
      = ∏ a : α, (mult a)! := by
  rw [Fintype.card_congr (arrangementEquivFiberEquivs mult w), Fintype.card_pi]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hcard : Fintype.card { j : Fin M // w j = a } = mult a := by
    rw [Fintype.card_subtype]
    exact hw a
  rw [Fintype.card_equiv (Fintype.equivFinOfCardEq hcard), hcard]

omit [Fintype α] in
/-- Every induced word satisfies the fiber condition. -/
theorem inducedWord_fiber_card (σ : Fin M ≃ Σ a : α, Fin (mult a)) (a : α) :
    (Finset.univ.filter fun j => inducedWord mult σ j = a).card = mult a := by
  rw [← Fintype.card_subtype,
    Fintype.card_congr (toFiberEquiv mult (inducedWord mult σ) σ (fun j => rfl) a)]
  exact Fintype.card_fin _

/-- The words `Fin M → α` satisfying the fiber condition for `mult`: DESIGN §5.5's
admissible words with prescribed letter multiplicities (paper (5.15), (5.33)). -/
def validWords : Finset (Fin M → α) :=
  Finset.univ.filter fun w : Fin M → α =>
    ∀ a, (Finset.univ.filter fun j => w j = a).card = mult a

theorem inducedWord_mem_validWords (σ : Fin M ≃ Σ a : α, Fin (mult a)) :
    inducedWord mult σ ∈ validWords mult :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, inducedWord_fiber_card mult σ⟩

/-- `Finset.filter` form of the fiber-count lemma: the labeled arrangements inducing a
fixed valid word `w` number exactly `∏ a, (mult a)!`. -/
theorem card_arrangements_inducing {w : Fin M → α} (hw : w ∈ validWords mult) :
    (Finset.univ.filter fun σ : Fin M ≃ Σ a : α, Fin (mult a) =>
      inducedWord mult σ = w).card = ∏ a : α, (mult a)! := by
  rw [← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypeEquivRight fun σ => funext_iff)]
  exact card_arrangements_fiber mult w (Finset.mem_filter.1 hw).2

/-- **Factorial ledger** (ℕ-valued statistics).  Summing any word statistic over all
labeled arrangements counts each admissible word exactly `∏ a, (mult a)!` times.  (This
is where the `(s+1)!⁻¹` of (5.45)(i) comes from: it cancels the ledger factor, and is
*not* produced by the collapse itself.) -/
theorem ledger_sum (F : (Fin M → α) → ℕ) :
    ∑ σ : Fin M ≃ Σ a : α, Fin (mult a), F (inducedWord mult σ)
      = (∏ a : α, (mult a)!) * ∑ w ∈ validWords mult, F w := by
  rw [← Finset.sum_fiberwise_of_maps_to' (t := validWords mult) (g := inducedWord mult)
      (fun σ _ => inducedWord_mem_validWords mult σ) F,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun w hw => by
    rw [Finset.sum_const, smul_eq_mul, card_arrangements_inducing mult hw]

/-- **Factorial ledger**, real-valued form: the version consumed by the analytic
estimates (the statistics of §5.4 are real). -/
theorem ledger_sum_real (F : (Fin M → α) → ℝ) :
    ∑ σ : Fin M ≃ Σ a : α, Fin (mult a), F (inducedWord mult σ)
      = (∏ a : α, ((mult a)! : ℝ)) * ∑ w ∈ validWords mult, F w := by
  rw [← Finset.sum_fiberwise_of_maps_to' (t := validWords mult) (g := inducedWord mult)
      (fun σ _ => inducedWord_mem_validWords mult σ) F,
    Finset.mul_sum, ← Nat.cast_prod]
  exact Finset.sum_congr rfl fun w hw => by
    rw [Finset.sum_const, nsmul_eq_mul, card_arrangements_inducing mult hw]

/-! ### The definitional ledger

`paperSum` is *defined* as `∏ a, (mult a)!` times the raw word sum.  Statements of
P-5.7, P-5.9, P-5.10 and R-decomp's (5.10) put `paperSum` on the left-hand side with
the paper's right-hand sides verbatim; internal proofs manipulate `wordSum` and convert
only at statement boundaries via `paperSum_eq_sum_arrangements`. -/

/-- Sum of a real word statistic over the admissible words for `mult`. -/
def wordSum (F : (Fin M → α) → ℝ) : ℝ :=
  ∑ w ∈ validWords mult, F w

/-- The paper's labeled-arrangement sum, *defined* through the factorial ledger:
`paperSum mult F = (∏ a, (mult a)!) * wordSum mult F`. -/
def paperSum (F : (Fin M → α) → ℝ) : ℝ :=
  (∏ a : α, ((mult a)! : ℝ)) * wordSum mult F

/-- **Statement-boundary conversion.**  The definitional `paperSum` equals the honest
sum over labeled arrangements; this is the only bridge the analytic layer needs. -/
theorem paperSum_eq_sum_arrangements (F : (Fin M → α) → ℝ) :
    paperSum mult F = ∑ σ : Fin M ≃ Σ a : α, Fin (mult a), F (inducedWord mult σ) := by
  unfold paperSum wordSum
  exact (ledger_sum_real mult F).symm

/-! ### Restricted word sums

Sums over the admissible words satisfying a side condition `P` (e.g. the adjacency and
primitivity restrictions of (5.15)/(5.33)), with the monotonicity in `P` used by the
estimates. -/

/-- Sum of a real word statistic over the admissible words satisfying `P`. -/
def wordSumFiltered (P : (Fin M → α) → Prop) [DecidablePred P]
    (F : (Fin M → α) → ℝ) : ℝ :=
  ∑ w ∈ (validWords mult).filter P, F w

/-- The `paperSum` analogue of `wordSumFiltered`: ledger factor times restricted sum. -/
def paperSumFiltered (P : (Fin M → α) → Prop) [DecidablePred P]
    (F : (Fin M → α) → ℝ) : ℝ :=
  (∏ a : α, ((mult a)! : ℝ)) * wordSumFiltered mult P F

/-- Dropping a side condition can only increase a sum of nonnegative statistics. -/
theorem wordSumFiltered_le_wordSum (P : (Fin M → α) → Prop) [DecidablePred P]
    (F : (Fin M → α) → ℝ) (hF : ∀ w ∈ validWords mult, 0 ≤ F w) :
    wordSumFiltered mult P F ≤ wordSum mult F := by
  unfold wordSumFiltered wordSum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset P (validWords mult))
    fun w hw _ => hF w hw

/-- Dropping a side condition can only increase a `paperSum` of nonnegative statistics. -/
theorem paperSumFiltered_le_paperSum (P : (Fin M → α) → Prop) [DecidablePred P]
    (F : (Fin M → α) → ℝ) (hF : ∀ w ∈ validWords mult, 0 ≤ F w) :
    paperSumFiltered mult P F ≤ paperSum mult F := by
  unfold paperSumFiltered paperSum
  exact mul_le_mul_of_nonneg_left (wordSumFiltered_le_wordSum mult P F hF)
    (Finset.prod_nonneg fun a _ => Nat.cast_nonneg _)

end Ledger

/-! ### Word predicates (paper (5.15)/(5.33) side conditions)

Primitivity of words is *not* defined here: in the paper it is relative to the tree
structure and enters only with the collapse induction. -/

section Predicates

variable {α : Type*} {M : ℕ}

/-- Paper (5.15)/(5.33) side condition: no two adjacent positions of the word carry
equal letters. -/
def NoAdjacentEqual (w : Fin M → α) : Prop :=
  ∀ j : Fin M, ∀ h : j.val + 1 < M, w j ≠ w ⟨j.val + 1, h⟩

instance [DecidableEq α] (w : Fin M → α) : Decidable (NoAdjacentEqual w) :=
  inferInstanceAs
    (Decidable (∀ j : Fin M, ∀ h : j.val + 1 < M, w j ≠ w ⟨j.val + 1, h⟩))

#guard NoAdjacentEqual ![0, 1, 0]
#guard ¬ NoAdjacentEqual ![0, 1, 1]

end Predicates

end Anderson4D
