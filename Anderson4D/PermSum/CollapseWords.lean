import Anderson4D.PermSum.Words
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Finite-word collapse data for the Proposition 5.9 induction

This file upgrades the list-level collapse equivalence in `PermSum/Words.lean`
to the actual finite words used by `validWords`.

There are two deliberately separate stages.

* `finWordRawCollapseEquiv` remembers the maximal inside blocks and the
  collapsed outside word.  Its codomain records the original length, so this
  is an equivalence for `Fin n`-indexed words rather than merely for lists.
* The flattened inside word `π₁`, its composition, the proper cut set `O`,
  and the collapsed word `π₂` are canonical projections of that data.

No cardinality or quotient argument occurs here: reconstruction is by
`List.splitWrtComposition` followed by `expand`.
-/

namespace Anderson4D

variable {A B : Type*}

/-- The codomain already used by `wordCollapseEquiv`, now given a reusable name. -/
abbrev RawCollapseData (A B : Type*) :=
  { p : List (List A) × List (Unit ⊕ B) //
    (∀ blk ∈ p.1, blk ≠ []) ∧ markerCount p.2 = p.1.length ∧
      NoTwoAdjacentMarkers p.2 }

namespace RawCollapseData

/-- The maximal inside blocks. -/
def blocks (d : RawCollapseData A B) : List (List A) :=
  d.1.1

/-- The word in which each maximal inside block is replaced by a marker. -/
def collapsed (d : RawCollapseData A B) : List (Unit ⊕ B) :=
  d.1.2

/-- Reconstruct the uncollapsed list. -/
def expandWord (d : RawCollapseData A B) : List (A ⊕ B) :=
  expand d.blocks d.collapsed

/-- The length before collapse. -/
def expandedLength (d : RawCollapseData A B) : ℕ :=
  d.expandWord.length

/-- The inside letters, with the maximal blocks concatenated in order. -/
def insideList (d : RawCollapseData A B) : List A :=
  d.blocks.flatten

/-- The number of inside letters. -/
def insideLength (d : RawCollapseData A B) : ℕ :=
  d.insideList.length

/-- The composition recording the lengths of the maximal inside blocks. -/
def blockComposition (d : RawCollapseData A B) : Composition d.insideLength where
  blocks := d.blocks.map List.length
  blocks_pos := by
    intro k hk
    obtain ⟨blk, hblk, rfl⟩ := List.mem_map.1 hk
    exact List.length_pos_iff.2 (d.2.1 blk hblk)
  blocks_sum := by
    simp only [insideLength, insideList, List.length_flatten]

@[simp] theorem blockComposition_blocks (d : RawCollapseData A B) :
    d.blockComposition.blocks = d.blocks.map List.length :=
  rfl

@[simp] theorem blockComposition_length (d : RawCollapseData A B) :
    d.blockComposition.length = d.blocks.length := by
  simp [Composition.length]

/-- Splitting `π₁` at the recorded composition cuts recovers the maximal
inside blocks in order. -/
@[simp] theorem split_insideList_blockComposition (d : RawCollapseData A B) :
    d.insideList.splitWrtComposition d.blockComposition = d.blocks := by
  exact List.splitWrtComposition_flatten d.blocks d.blockComposition rfl

/-- The inside word `π₁`, indexed by its finite length. -/
def insideWord (d : RawCollapseData A B) : Fin d.insideLength → A :=
  List.Vector.get (⟨d.insideList, rfl⟩ : List.Vector A d.insideLength)

/-- The collapsed word `π₂`, indexed by its finite length. -/
def collapsedWord (d : RawCollapseData A B) : Fin d.collapsed.length → Unit ⊕ B :=
  List.Vector.get
    (⟨d.collapsed, rfl⟩ : List.Vector (Unit ⊕ B) d.collapsed.length)

/-- Marker positions in `π₂`.  There is one marker per inside block.

These are **not** the paper's cut set `O`: their cardinality is the number
of blocks, whereas `O` contains the proper cuts and has one fewer element. -/
def markerPositions (d : RawCollapseData A B) :
    Finset (Fin d.collapsed.length) :=
  Finset.univ.filter fun i => (d.collapsedWord i).isLeft = true

@[simp] theorem mem_markerPositions_iff (d : RawCollapseData A B)
    (i : Fin d.collapsed.length) :
    i ∈ d.markerPositions ↔ (d.collapsedWord i).isLeft = true := by
  simp [markerPositions]

/-- There is one marker position for every maximal inside block. -/
theorem card_markerPositions (d : RawCollapseData A B) :
    d.markerPositions.card = d.blocks.length := by
  let v : List.Vector (Unit ⊕ B) d.collapsed.length := ⟨d.collapsed, rfl⟩
  have h :=
    Fin.card_filter_univ_eq_vector_get_eq_count true
      (v.map fun x => x.isLeft)
  have hcount :
      (v.map fun x => x.isLeft).toList.count true = markerCount d.collapsed := by
    simp [v, markerCount, List.count, Function.comp_def]
  calc
    d.markerPositions.card =
        (Finset.univ.filter fun i => (v.get i).isLeft = true).card := by
          simp [markerPositions, collapsedWord, v]
    _ = (Finset.univ.filter fun i =>
          ((v.map fun x => x.isLeft).get i) = true).card := by
          simp
    _ = (v.map fun x => x.isLeft).toList.count true := h
    _ = markerCount d.collapsed := hcount
    _ = d.blocks.length := d.2.2.1

/-- Equivalently, the marker set has the length of the block composition. -/
theorem card_markerPositions_eq_composition_length (d : RawCollapseData A B) :
    d.markerPositions.card = d.blockComposition.length := by
  rw [card_markerPositions, blockComposition_length]

/-- The embedding of proper composition cuts into the gaps of `π₁`.

The value is the zero-based index of the letter immediately before the cut:
the proper partial sum after block `i`, minus one. -/
def cutEmbedding (d : RawCollapseData A B) :
    Fin (d.blockComposition.length - 1) ↪ Fin (d.insideLength - 1) where
  toFun i := by
    let c := d.blockComposition
    have hiproper : i.val + 1 < c.length := by
      change i.val + 1 < d.blockComposition.length
      omega
    have hfirst : 0 < c.sizeUpTo 1 := by
      have h := c.sizeUpTo_strict_mono (i := 0) (by omega)
      simpa using h
    have hpos : 0 < c.sizeUpTo (i.val + 1) :=
      lt_of_lt_of_le hfirst
        (c.monotone_sizeUpTo (by omega : 1 ≤ i.val + 1))
    have hlt :
        c.sizeUpTo (i.val + 1) < c.sizeUpTo (i.val + 2) :=
      c.sizeUpTo_strict_mono hiproper
    have hle :
        c.sizeUpTo (i.val + 2) ≤ c.sizeUpTo c.length :=
      c.monotone_sizeUpTo (by omega)
    refine ⟨c.sizeUpTo (i.val + 1) - 1, ?_⟩
    rw [c.sizeUpTo_length] at hle
    omega
  inj' := by
    intro i j hij
    let c := d.blockComposition
    have hiproper : i.val + 1 < c.length := by
      change i.val + 1 < d.blockComposition.length
      omega
    have hjproper : j.val + 1 < c.length := by
      change j.val + 1 < d.blockComposition.length
      omega
    have hfirst : 0 < c.sizeUpTo 1 := by
      have h := c.sizeUpTo_strict_mono (i := 0) (by omega)
      simpa using h
    have hipos : 0 < c.sizeUpTo (i.val + 1) :=
      lt_of_lt_of_le hfirst
        (c.monotone_sizeUpTo (by omega : 1 ≤ i.val + 1))
    have hjpos : 0 < c.sizeUpTo (j.val + 1) :=
      lt_of_lt_of_le hfirst
        (c.monotone_sizeUpTo (by omega : 1 ≤ j.val + 1))
    have hsum :
        c.sizeUpTo (i.val + 1) = c.sizeUpTo (j.val + 1) := by
      have hval :=
        congrArg (fun x : Fin (d.insideLength - 1) => x.val) hij
      change
        d.blockComposition.sizeUpTo (i.val + 1) - 1 =
          d.blockComposition.sizeUpTo (j.val + 1) - 1 at hval
      change 0 < d.blockComposition.sizeUpTo (i.val + 1) at hipos
      change 0 < d.blockComposition.sizeUpTo (j.val + 1) at hjpos
      change d.blockComposition.sizeUpTo (i.val + 1) =
        d.blockComposition.sizeUpTo (j.val + 1)
      omega
    have hb :
        c.boundary ⟨i.val + 1, by omega⟩ =
          c.boundary ⟨j.val + 1, by omega⟩ := by
      apply Fin.ext
      exact hsum
    have hindex := c.boundary.injective hb
    apply Fin.ext
    have hval :
        i.val + 1 = j.val + 1 := by
      simpa using congrArg Fin.val hindex
    exact Nat.add_right_cancel hval

@[simp] theorem cutEmbedding_val (d : RawCollapseData A B)
    (i : Fin (d.blockComposition.length - 1)) :
    (d.cutEmbedding i).val =
      d.blockComposition.sizeUpTo (i.val + 1) - 1 :=
  rfl

/-- The paper's selected cut set `O`: the proper partial sums of the block
composition, represented as gaps of `π₁`. -/
def cutIndices (d : RawCollapseData A B) :
    Finset (Fin (d.insideLength - 1)) :=
  Finset.univ.map d.cutEmbedding

theorem mem_cutIndices_iff (d : RawCollapseData A B)
    (j : Fin (d.insideLength - 1)) :
    j ∈ d.cutIndices ↔
      ∃ i : Fin (d.blockComposition.length - 1),
        d.cutEmbedding i = j := by
  simp [cutIndices]

/-- The degenerate-case-safe cut count: zero blocks and one block both
have no proper cuts. -/
@[simp] theorem card_cutIndices (d : RawCollapseData A B) :
    d.cutIndices.card = d.blocks.length - 1 := by
  simp [cutIndices, blockComposition_length]

/-- Universal cut ledger, including the zero-block degeneration. -/
theorem card_cutIndices_add_min_one (d : RawCollapseData A B) :
    d.cutIndices.card + min 1 d.blocks.length = d.blocks.length := by
  rw [card_cutIndices]
  omega

/-- In the nonempty case used in §5.4.1, `|O| + 1` is the number of
inside blocks (the paper's `s + 1`). -/
theorem card_cutIndices_add_one (d : RawCollapseData A B)
    (hblocks : d.blocks ≠ []) :
    d.cutIndices.card + 1 = d.blocks.length := by
  rw [card_cutIndices]
  have : 0 < d.blocks.length := List.length_pos_iff.2 hblocks
  omega

/-- The original word is recovered by inserting the composition blocks into
the marker occurrences of the compound letter, in order. -/
@[simp] theorem expandWord_eq (d : RawCollapseData A B) :
    d.expandWord = expand d.blocks d.collapsed :=
  rfl

end RawCollapseData

/-- Raw collapse data whose expansion has the prescribed finite length. -/
abbrev FixedRawCollapseData (A B : Type*) (n : ℕ) :=
  { d : RawCollapseData A B // d.expandedLength = n }

/-- Fixed-length lists are finite words. -/
def finWordVectorEquiv (α : Type*) (n : ℕ) :
    (Fin n → α) ≃ List.Vector α n :=
  (Equiv.vectorEquivFin α n).symm

/-- Restrict `wordCollapseEquiv` to vectors of a fixed length. -/
def vectorRawCollapseEquiv (A B : Type*) (n : ℕ) :
    List.Vector (A ⊕ B) n ≃ FixedRawCollapseData A B n where
  toFun v := by
    let d : RawCollapseData A B := wordCollapseEquiv A B v.1
    refine ⟨d, ?_⟩
    change (expand (collapse v.1).1 (collapse v.1).2).length = n
    rw [expand_collapse, v.2]
  invFun d := ⟨d.1.expandWord, d.2⟩
  left_inv v := by
    apply Subtype.ext
    exact expand_collapse v.1
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    exact collapse_expand d.1.collapsed d.1.blocks
      d.1.2.1 d.1.2.2.1 d.1.2.2.2

/-- **Finite raw collapse equivalence.**  This lifts the list equivalence to
the `Fin n → A ⊕ B` carrier of `validWords`. -/
def finWordRawCollapseEquiv (A B : Type*) (n : ℕ) :
    (Fin n → A ⊕ B) ≃ FixedRawCollapseData A B n :=
  (finWordVectorEquiv (A ⊕ B) n).trans (vectorRawCollapseEquiv A B n)

/-- Length transport is part of the finite equivalence's codomain. -/
@[simp] theorem finWordRawCollapseEquiv_expandedLength
    {n : ℕ} (w : Fin n → A ⊕ B) :
    ((finWordRawCollapseEquiv A B n w).1).expandedLength = n :=
  (finWordRawCollapseEquiv A B n w).2

/-- The list reconstructed from the finite collapse coordinates is exactly
the list underlying the original finite word. -/
@[simp] theorem finWordRawCollapseEquiv_expandWord
    {n : ℕ} (w : Fin n → A ⊕ B) :
    ((finWordRawCollapseEquiv A B n w).1).expandWord = List.ofFn w := by
  change
    expand
        (collapse (List.Vector.ofFn w).toList).1
        (collapse (List.Vector.ofFn w).toList).2 =
      List.ofFn w
  rw [List.Vector.toList_ofFn, expand_collapse]

/-- **Finite `(π₁, O, π₂)` collapse equivalence.**

The codomain stores the maximal blocks; `insideWord`, `blockComposition`,
`cutIndices`, and `collapsedWord` are its canonical `(π₁, O, π₂)`
coordinates.  The inverse inserts the blocks at the marker occurrences of
`π₂` in order. -/
def finWordCollapseEquiv (A B : Type*) (n : ℕ) :
    (Fin n → A ⊕ B) ≃ FixedRawCollapseData A B n :=
  finWordRawCollapseEquiv A B n

/-! ## Length and multiplicity transport -/

/-- Multiplicity specification on raw collapse data.  Inside counts are
summed over the composition blocks; outside counts are read from `π₂`. -/
def CollapseMultiplicitySpec [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (d : RawCollapseData A B) : Prop :=
  (∀ a : A,
      (d.blocks.map fun blk => blk.count a).sum = mult (.inl a)) ∧
    ∀ b : B, d.collapsed.count (.inr b) = mult (.inr b)

/-- Count an inside letter in a finite sum-word by counting its index fiber. -/
theorem count_inl_ofFn_eq_fiberCard [DecidableEq A] [DecidableEq B] :
    ∀ {n : ℕ} (w : Fin n → A ⊕ B) (a : A),
      (List.ofFn w).count (.inl a) =
        (Finset.univ.filter fun i => w i = .inl a).card
  | 0, w, a => by simp
  | n + 1, w, a => by
      rw [List.ofFn_succ, List.count_cons,
        count_inl_ofFn_eq_fiberCard (fun i => w i.succ) a,
        Fin.card_filter_univ_succ']
      cases h : w 0 with
      | inl a' => simp [Nat.add_comm]
      | inr b => simp

/-- Count an outside letter in a finite sum-word by counting its index fiber. -/
theorem count_inr_ofFn_eq_fiberCard [DecidableEq A] [DecidableEq B] :
    ∀ {n : ℕ} (w : Fin n → A ⊕ B) (b : B),
      (List.ofFn w).count (.inr b) =
        (Finset.univ.filter fun i => w i = .inr b).card
  | 0, w, b => by simp
  | n + 1, w, b => by
      rw [List.ofFn_succ, List.count_cons,
        count_inr_ofFn_eq_fiberCard (fun i => w i.succ) b,
        Fin.card_filter_univ_succ']
      cases h : w 0 with
      | inl a => simp
      | inr b' => simp [Nat.add_comm]

/-- `validWords` transports exactly to the inside-block and outside-word
multiplicity conditions. -/
theorem mem_validWords_iff_collapseMultiplicitySpec
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (mult : A ⊕ B → ℕ) (w : Fin n → A ⊕ B) :
    w ∈ validWords mult ↔
      CollapseMultiplicitySpec mult
        (wordCollapseEquiv A B (List.ofFn w)) := by
  rw [validWords, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hw
    constructor
    · intro a
      calc
        (((collapse (List.ofFn w)).1.map fun blk => blk.count a).sum) =
            (List.ofFn w).count (.inl a) :=
          (count_inl_collapse a (List.ofFn w)).symm
        _ = (Finset.univ.filter fun i => w i = .inl a).card :=
          count_inl_ofFn_eq_fiberCard w a
        _ = mult (.inl a) := hw (.inl a)
    · intro b
      calc
        (collapse (List.ofFn w)).2.count (.inr b) =
            (List.ofFn w).count (.inr b) :=
          (count_inr_collapse b (List.ofFn w)).symm
        _ = (Finset.univ.filter fun i => w i = .inr b).card :=
          count_inr_ofFn_eq_fiberCard w b
        _ = mult (.inr b) := hw (.inr b)
  · rintro ⟨hinside, houtside⟩ x
    cases x with
    | inl a =>
        calc
          (Finset.univ.filter fun i => w i = .inl a).card =
              (List.ofFn w).count (.inl a) :=
            (count_inl_ofFn_eq_fiberCard w a).symm
          _ = ((collapse (List.ofFn w)).1.map fun blk => blk.count a).sum :=
            count_inl_collapse a (List.ofFn w)
          _ = mult (.inl a) := hinside a
    | inr b =>
        calc
          (Finset.univ.filter fun i => w i = .inr b).card =
              (List.ofFn w).count (.inr b) :=
            (count_inr_ofFn_eq_fiberCard w b).symm
          _ = (collapse (List.ofFn w)).2.count (.inr b) :=
            count_inr_collapse b (List.ofFn w)
          _ = mult (.inr b) := houtside b

/-- The same transport stated directly through the finite raw equivalence. -/
theorem mem_validWords_iff_finWordRawCollapseSpec
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (mult : A ⊕ B → ℕ) (w : Fin n → A ⊕ B) :
    w ∈ validWords mult ↔
      CollapseMultiplicitySpec mult
        ((finWordRawCollapseEquiv A B n w).1) := by
  change w ∈ validWords mult ↔
    CollapseMultiplicitySpec mult
      (wordCollapseEquiv A B (List.Vector.ofFn w).toList)
  rw [List.Vector.toList_ofFn]
  exact mem_validWords_iff_collapseMultiplicitySpec mult w

end Anderson4D
