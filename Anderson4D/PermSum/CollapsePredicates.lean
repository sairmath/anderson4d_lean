import Anderson4D.PermSum.CollapseWords
import Anderson4D.PermSum.Statements

/-!
# Predicate transport for the Proposition 5.9 word collapse

This file proves the logical side-condition transport used in the collapse
step of §5.4.1.  The proper composition cuts are first identified with
`AdjacentIndex`; adjacency is then transported both to the flattened inside
word (away from those cuts) and to the collapsed outside word.
-/

namespace Anderson4D

open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

variable {A B : Type*}

/-! ## The inside alphabet -/

/-- The original letters belonging to the selected subtree. -/
def insideAlphabet [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Finset (A ⊕ B) :=
  Finset.univ.image Sum.inl

@[simp]
theorem inl_mem_insideAlphabet [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (a : A) :
    (Sum.inl a : A ⊕ B) ∈ insideAlphabet := by
  simp [insideAlphabet]

@[simp]
theorem inr_not_mem_insideAlphabet [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (b : B) :
    (Sum.inr b : A ⊕ B) ∉ insideAlphabet := by
  simp [insideAlphabet]

theorem insideAlphabet_nonempty [Fintype A] [Fintype B] [Nonempty A]
    [DecidableEq A] [DecidableEq B] :
    (insideAlphabet : Finset (A ⊕ B)).Nonempty := by
  let a : A := Classical.choice inferInstance
  exact ⟨.inl a, inl_mem_insideAlphabet a⟩

theorem insideAlphabet_ssubset_univ [Fintype A] [Fintype B] [Nonempty B]
    [DecidableEq A] [DecidableEq B] :
    (insideAlphabet : Finset (A ⊕ B)) ⊂ Finset.univ := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
  let b : B := Classical.choice inferInstance
  intro heq
  have hb : (Sum.inr b : A ⊕ B) ∈ insideAlphabet := by
    rw [heq]
    exact Finset.mem_univ _
  exact inr_not_mem_insideAlphabet b hb

/-! ## Finite-word/list bridges -/

/-- Gaps of a word of length `n` and the project's adjacency indices are the
same finite type. -/
def finPredEquivAdjacentIndex (n : ℕ) :
    Fin (n - 1) ≃ AdjacentIndex n where
  toFun i := by
    have hi : i.1 + 1 < n := by omega
    exact ⟨⟨i.1, by omega⟩, hi⟩
  invFun i :=
    ⟨i.1.1, by omega⟩
  left_inv i := by
    ext
    rfl
  right_inv i := by
    ext
    rfl

@[simp]
theorem finPredEquivAdjacentIndex_val (n : ℕ) (i : Fin (n - 1)) :
    ((finPredEquivAdjacentIndex n i).1 : ℕ) = i :=
  rfl

@[simp]
theorem finPredEquivAdjacentIndex_symm_val (n : ℕ)
    (i : AdjacentIndex n) :
    ((finPredEquivAdjacentIndex n).symm i : ℕ) = i.1.1 :=
  rfl

/-- `NoAdjacentEqual` is exactly the ordinary unequal-neighbour chain
condition on the list underlying a finite word. -/
theorem noAdjacentEqual_iff_isChain_ofFn {α : Type*} {n : ℕ}
    (w : Fin n → α) :
    NoAdjacentEqual w ↔ (List.ofFn w).IsChain (· ≠ ·) := by
  rw [List.isChain_ofFn]
  constructor
  · intro h i hi
    exact h ⟨i, Nat.lt_of_succ_lt hi⟩ hi
  · intro h j hj
    exact h j.1 hj

namespace RawCollapseData

/-- The paper cut set on the exact carrier expected by Proposition 5.10. -/
def adjacentCutIndices (d : RawCollapseData A B) :
    Finset (AdjacentIndex d.insideLength) :=
  d.cutIndices.map (finPredEquivAdjacentIndex d.insideLength).toEmbedding

theorem mem_adjacentCutIndices_iff (d : RawCollapseData A B)
    (j : AdjacentIndex d.insideLength) :
    j ∈ d.adjacentCutIndices ↔
      (finPredEquivAdjacentIndex d.insideLength).symm j ∈ d.cutIndices := by
  simp [adjacentCutIndices]

@[simp]
theorem card_adjacentCutIndices (d : RawCollapseData A B) :
    d.adjacentCutIndices.card = d.blocks.length - 1 := by
  rw [adjacentCutIndices, Finset.card_map, card_cutIndices]

@[simp]
theorem ofFn_insideWord (d : RawCollapseData A B) :
    List.ofFn d.insideWord = d.insideList := by
  exact List.ofFn_get _

@[simp]
theorem ofFn_collapsedWord (d : RawCollapseData A B) :
    List.ofFn d.collapsedWord = d.collapsed := by
  exact List.ofFn_get _

end RawCollapseData

/-! ## List-level collapse lemmas -/

/-- Collapsing maximal inside runs preserves unequal adjacency in the
collapsed word. -/
theorem collapse_collapsed_isChain_ne [DecidableEq A] [DecidableEq B] :
    ∀ w : List (A ⊕ B),
      w.IsChain (· ≠ ·) → (collapse w).2.IsChain (· ≠ ·)
  | [], _ => by simp [collapse]
  | [x], _ => by
      cases x <;> simp [collapse]
  | .inl a :: .inl a' :: w, h => by
      have htail : (Sum.inl a' :: w).IsChain (· ≠ ·) :=
        (List.isChain_cons_cons.mp h).2
      simpa only [collapse] using collapse_collapsed_isChain_ne _ htail
  | .inl a :: .inr b :: w, h => by
      have htail : (Sum.inr b :: w).IsChain (· ≠ ·) :=
        (List.isChain_cons_cons.mp h).2
      have ih := collapse_collapsed_isChain_ne _ htail
      simpa only [collapse] using
        (List.IsChain.cons_cons (by simp) ih)
  | .inr b :: .inl a :: w, h => by
      have htail : (Sum.inl a :: w).IsChain (· ≠ ·) :=
        (List.isChain_cons_cons.mp h).2
      have ih := collapse_collapsed_isChain_ne _ htail
      obtain ⟨tl, bs, s, hcollapse⟩ := collapse_inl_cons w a
      rw [hcollapse] at ih
      simpa only [collapse, hcollapse] using
        (List.IsChain.cons_cons Sum.inr_ne_inl ih)
  | .inr b :: .inr b' :: w, h => by
      have hrel : (Sum.inr b : A ⊕ B) ≠ .inr b' :=
        (List.isChain_cons_cons.mp h).1
      have htail : (Sum.inr b' :: w).IsChain (· ≠ ·) :=
        (List.isChain_cons_cons.mp h).2
      have ih := collapse_collapsed_isChain_ne _ htail
      have hbb : b ≠ b' := by
        intro hEq
        exact hrel (by simp [hEq])
      simpa only [collapse] using
        (List.IsChain.cons_cons (by simpa using hbb) ih)

/-- Every maximal inside block inherits unequal adjacency from the original
word. -/
theorem collapse_blocks_isChain_ne [DecidableEq A] [DecidableEq B] :
    ∀ w : List (A ⊕ B),
      w.IsChain (· ≠ ·) →
        ∀ blk ∈ (collapse w).1, blk.IsChain (· ≠ ·)
  | [], _ => by simp [collapse]
  | [x], _ => by
      cases x <;> simp [collapse]
  | .inr b :: y :: w, h => by
      have htail : (y :: w).IsChain (· ≠ ·) :=
        (List.isChain_cons_cons.mp h).2
      simpa only [collapse] using collapse_blocks_isChain_ne _ htail
  | .inl a :: .inr b :: w, h => by
      have htail : (Sum.inr b :: w).IsChain (· ≠ ·) :=
        (List.isChain_cons_cons.mp h).2
      have ih := collapse_blocks_isChain_ne _ htail
      simp only [collapse, List.mem_cons]
      intro blk hblk
      rcases hblk with rfl | hblk
      · exact .singleton _
      · exact ih blk hblk
  | .inl a :: .inl a' :: w, h => by
      have hrel : (Sum.inl a : A ⊕ B) ≠ .inl a' :=
        (List.isChain_cons_cons.mp h).1
      have haa : a ≠ a' := by
        intro hEq
        exact hrel (by simp [hEq])
      have htail : (Sum.inl a' :: w).IsChain (· ≠ ·) :=
        (List.isChain_cons_cons.mp h).2
      have ih := collapse_blocks_isChain_ne _ htail
      obtain ⟨tl, bs, s, hcollapse⟩ := collapse_inl_cons w a'
      rw [hcollapse] at ih
      simp only [collapse, hcollapse, List.modifyHead, List.mem_cons]
      intro blk hblk
      rcases hblk with rfl | hblk
      · exact List.IsChain.cons_cons haa
          (ih (a' :: tl) (List.mem_cons_self))
      · exact ih blk (List.mem_cons_of_mem _ hblk)

/-! ## The one-block degeneration -/

/-- A collapsed list has no marker exactly when every entry is an outside
letter. -/
theorem markerCount_eq_zero_iff_exists_map_inr
    (s : List (Unit ⊕ B)) :
    markerCount s = 0 ↔ ∃ bs : List B, s = bs.map Sum.inr := by
  constructor
  · induction s with
    | nil => exact fun _ => ⟨[], rfl⟩
    | cons x s ih =>
        intro h
        cases x with
        | inl u => simp [markerCount] at h
        | inr b =>
            have htail : markerCount s = 0 := by
              simpa [markerCount] using h
            obtain ⟨bs, rfl⟩ := ih htail
            exact ⟨b :: bs, rfl⟩
  · rintro ⟨bs, rfl⟩
    induction bs with
    | nil => simp [markerCount]
    | cons b bs ih => simp [markerCount]

/-- A collapsed list with one marker is an outside prefix, the unique
marker, and an outside suffix. -/
theorem markerCount_eq_one_decompose (s : List (Unit ⊕ B))
    (h : markerCount s = 1) :
    ∃ pre post : List B,
      s = pre.map Sum.inr ++ [.inl ()] ++ post.map Sum.inr := by
  induction s with
  | nil =>
      simp [markerCount] at h
  | cons x s ih =>
      cases x with
      | inl u =>
          have htail : markerCount s = 0 := by
            simpa [markerCount] using h
          obtain ⟨post, hpost⟩ :=
            (markerCount_eq_zero_iff_exists_map_inr s).mp htail
          cases u
          exact ⟨[], post, by simp [hpost]⟩
      | inr b =>
          have htail : markerCount s = 1 := by
            simpa [markerCount] using h
          obtain ⟨pre, post, hdecomp⟩ := ih htail
          exact ⟨b :: pre, post, by simp [hdecomp]⟩

private theorem expand_nil_map_inr (s : List B) :
    expand ([] : List (List A)) (s.map Sum.inr) =
      s.map (Sum.inr : B → A ⊕ B) := by
  induction s with
  | nil => simp [expand]
  | cons b s ih => simp [expand, ih]

private theorem expand_singleton_marker_decomposition
    (blk : List A) (pre post : List B) :
    expand [blk]
        (pre.map Sum.inr ++ [.inl ()] ++ post.map Sum.inr) =
      pre.map Sum.inr ++ blk.map Sum.inl ++ post.map Sum.inr := by
  induction pre with
  | nil =>
      simp [expand, expand_nil_map_inr]
  | cons b pre ih =>
      simpa [expand] using congrArg (List.cons (Sum.inr b)) ih

/-- If there is one inside block, expansion is an outside prefix followed by
that block and an outside suffix. -/
theorem expand_single_block_decompose (d : RawCollapseData A B)
    (hblocks : d.blocks.length = 1) :
    ∃ blk : List A, ∃ pre post : List B,
      blk ≠ [] ∧ d.blocks = [blk] ∧
        d.expandWord =
          pre.map Sum.inr ++ blk.map Sum.inl ++ post.map Sum.inr := by
  obtain ⟨blk, hblk⟩ : ∃ blk, d.blocks = [blk] := by
    exact List.length_eq_one_iff.mp hblocks
  have hnonempty : blk ≠ [] := by
    apply d.2.1 blk
    change blk ∈ d.blocks
    simp [hblk]
  have hmarker : markerCount d.collapsed = 1 := by
    exact d.2.2.1.trans hblocks
  obtain ⟨pre, post, hcollapsed⟩ :=
    markerCount_eq_one_decompose d.collapsed hmarker
  refine ⟨blk, pre, post, hnonempty, hblk, ?_⟩
  change expand d.blocks d.collapsed =
    pre.map Sum.inr ++ blk.map Sum.inl ++ post.map Sum.inr
  rw [hblk, hcollapsed]
  exact expand_singleton_marker_decomposition blk pre post

namespace RawCollapseData

/-- The collapsed outside word inherits the no-equal-neighbours condition
from the expanded word. -/
theorem collapsedWord_noAdjacentEqual [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B)
    (h : d.expandWord.IsChain (· ≠ ·)) :
    NoAdjacentEqual d.collapsedWord := by
  rw [noAdjacentEqual_iff_isChain_ofFn, d.ofFn_collapsedWord]
  have hc := collapse_collapsed_isChain_ne d.expandWord h
  change
    (collapse (expand d.blocks d.collapsed)).2.IsChain (· ≠ ·) at hc
  rw [collapse_expand d.collapsed d.blocks d.2.1 d.2.2.1 d.2.2.2] at hc
  exact hc

/-- Every recorded inside block inherits the no-equal-neighbours condition
from the expanded word. -/
theorem blocks_isChain_ne [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B)
    (h : d.expandWord.IsChain (· ≠ ·)) :
    ∀ blk ∈ d.blocks, blk.IsChain (· ≠ ·) := by
  have hc := collapse_blocks_isChain_ne d.expandWord h
  change
    ∀ blk ∈ (collapse (expand d.blocks d.collapsed)).1,
      blk.IsChain (· ≠ ·) at hc
  rw [collapse_expand d.collapsed d.blocks d.2.1 d.2.2.1 d.2.2.2] at hc
  exact hc

/-- Reading a letter from a composition block agrees with reading the
flattened inside list at the block offset. -/
theorem getElem_block_eq_insideList (d : RawCollapseData A B)
    (i j : ℕ) (hi : i < d.blocks.length)
    (hj : j < d.blocks[i].length) :
    d.blocks[i][j] =
      d.insideList.get ⟨d.blockComposition.sizeUpTo i + j, by
        have hi' : i < d.blockComposition.length := by
          simpa using hi
        have hblockLength :
            d.blocks[i].length = d.blockComposition.blocks[i]'hi' := by
          change d.blocks[i].length =
            (d.blocks.map List.length)[i]'(by simpa using hi)
          simp
        have hend :=
          d.blockComposition.sizeUpTo_succ hi'
        have hle := d.blockComposition.sizeUpTo_le (i + 1)
        change
          d.blockComposition.sizeUpTo (i + 1) ≤
              d.insideList.length at hle
        rw [hblockLength] at hj
        omega⟩ := by
  have hblockLength :
      d.blocks[i].length =
        d.blockComposition.blocks[i]'(by simpa using hi) := by
    change d.blocks[i].length =
      (d.blocks.map List.length)[i]'(by simpa using hi)
    simp
  have hi' : i < d.blockComposition.length := by
    simpa using hi
  have hend :
      d.blockComposition.sizeUpTo i + d.blocks[i].length =
        d.blockComposition.sizeUpTo (i + 1) := by
    rw [d.blockComposition.sizeUpTo_succ hi', hblockLength]
  have hglobal :
      d.blockComposition.sizeUpTo i + j < d.insideList.length := by
    have hendpoint :
        d.blockComposition.sizeUpTo (i + 1) ≤ d.insideList.length := by
      simpa only [insideLength] using
        d.blockComposition.sizeUpTo_le (i + 1)
    omega
  have hb :
      d.blocks[i] =
        (d.insideList.take
          (d.blockComposition.sizeUpTo (i + 1))).drop
          (d.blockComposition.sizeUpTo i) := by
    have hslice :=
      List.getElem_splitWrtComposition d.insideList d.blockComposition i
        (by simpa using hi)
    simpa only [d.split_insideList_blockComposition] using hslice
  simp only [hb, List.getElem_drop, List.getElem_take]
  rfl

/-- A gap outside the canonical cut set is not a proper composition
boundary. -/
theorem sizeUpTo_ne_succ_of_not_mem_cutIndices
    (d : RawCollapseData A B) (j : Fin (d.insideLength - 1))
    (hj : j ∉ d.cutIndices) (i : ℕ)
    (hi : i + 1 < d.blockComposition.length) :
    d.blockComposition.sizeUpTo (i + 1) ≠ j.1 + 1 := by
  intro hboundary
  apply hj
  rw [d.mem_cutIndices_iff]
  let k : Fin (d.blockComposition.length - 1) := ⟨i, by omega⟩
  refine ⟨k, Fin.ext ?_⟩
  rw [d.cutEmbedding_val]
  change d.blockComposition.sizeUpTo (i + 1) - 1 = j.1
  omega

/-- The flattened inside word has unequal neighbours away from precisely the
proper composition cuts. -/
theorem insideWord_noAdjacentOutside [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B)
    (h : d.expandWord.IsChain (· ≠ ·)) :
    NoAdjacentOutside d.adjacentCutIndices d.insideWord := by
  intro edge hedge
  let j : Fin (d.insideLength - 1) :=
    (finPredEquivAdjacentIndex d.insideLength).symm edge
  have hj : j ∉ d.cutIndices := by
    intro hjmem
    apply hedge
    rw [d.mem_adjacentCutIndices_iff]
    exact hjmem
  let p : Fin d.insideLength := edge.1
  let c := d.blockComposition
  let i : Fin c.length := c.index p
  have hstrict :
      p.1 + 1 < c.sizeUpTo (i.1 + 1) := by
    have hbelow := c.lt_sizeUpTo_index_succ p
    change p.1 < c.sizeUpTo (i.1 + 1) at hbelow
    have hle : p.1 + 1 ≤ c.sizeUpTo (i.1 + 1) := by omega
    by_contra hnotStrict
    have hboundary :
        c.sizeUpTo (i.1 + 1) = p.1 + 1 := by omega
    have hiProper : i.1 + 1 < c.length := by
      by_contra hnot
      have hilast : i.1 + 1 = c.length := by
        have hi := i.2
        omega
      have hsize :
          c.sizeUpTo (i.1 + 1) = d.insideLength := by
        rw [hilast, c.sizeUpTo_length]
      have hlt := edge.2
      change p.1 + 1 < d.insideLength at hlt
      omega
    have hnotBoundary :
        c.sizeUpTo (i.1 + 1) ≠ p.1 + 1 := by
      have hne :=
        d.sizeUpTo_ne_succ_of_not_mem_cutIndices j hj i.1
          (by simpa [c] using hiProper)
      simpa [c, p, j] using hne
    exact hnotBoundary hboundary
  have hstart : c.sizeUpTo i.1 ≤ p.1 :=
    c.sizeUpTo_index_le p
  have hiBlocks : i.1 < d.blocks.length := by
    simpa [c] using i.2
  have hblockLength :
      (d.blocks[i.1]'hiBlocks).length = c.blocks[i.1]'i.2 := by
    change (d.blocks[i.1]'hiBlocks).length =
      (d.blocks.map List.length)[i.1]'(by simpa [c] using i.2)
    simp
  have hend :
      c.sizeUpTo i.1 + (d.blocks[i.1]'hiBlocks).length =
        c.sizeUpTo (i.1 + 1) := by
    rw [hblockLength, c.sizeUpTo_succ i.2]
  let q := p.1 - c.sizeUpTo i.1
  have hq : q + 1 < (d.blocks[i.1]'hiBlocks).length := by
    dsimp [q]
    omega
  have hblockChain :
      (d.blocks[i.1]'hiBlocks).IsChain (· ≠ ·) := by
    apply d.blocks_isChain_ne h
    exact List.get_mem d.blocks ⟨i.1, hiBlocks⟩
  have hne :=
    List.isChain_iff_getElem.mp hblockChain q hq
  have hleft :=
    d.getElem_block_eq_insideList i.1 q
      (by simpa [c] using i.2) (by omega)
  have hright :=
    d.getElem_block_eq_insideList i.1 (q + 1)
      (by simpa [c] using i.2) hq
  rw [hleft, hright] at hne
  have hcsize :
      c.sizeUpTo i.1 = d.blockComposition.sizeUpTo i.1 := by
    rfl
  change
    d.insideList.get p ≠
      d.insideList.get ⟨p.1 + 1, edge.2⟩
  convert hne using 1 <;> apply congrArg d.insideList.get <;> apply Fin.ext <;>
    dsimp [q] <;> omega

/-- The cut set is nonempty as soon as the selected inside letters form at
least two maximal blocks. -/
theorem one_le_card_adjacentCutIndices (d : RawCollapseData A B)
    (hblocks : 2 ≤ d.blocks.length) :
    1 ≤ d.adjacentCutIndices.card := by
  rw [d.card_adjacentCutIndices]
  omega

/-- Exact nondegenerate cut-count criterion. -/
theorem adjacentCutIndices_nonempty_iff (d : RawCollapseData A B) :
    d.adjacentCutIndices.Nonempty ↔ 2 ≤ d.blocks.length := by
  constructor
  · intro h
    have hcard := Finset.card_pos.mpr h
    rw [d.card_adjacentCutIndices] at hcard
    omega
  · intro h
    apply Finset.card_pos.mp
    rw [d.card_adjacentCutIndices]
    omega

end RawCollapseData

/-! ## Transport directly from the finite collapse equivalence -/

/-- The original finite word supplies the expanded-list chain hypothesis used
by both predicate transports. -/
theorem finWordCollapse_expand_isChain [DecidableEq A] [DecidableEq B]
    {n : ℕ} (w : Fin n → A ⊕ B) (hw : NoAdjacentEqual w) :
    ((finWordCollapseEquiv A B n w).1).expandWord.IsChain (· ≠ ·) := by
  have hchain := (noAdjacentEqual_iff_isChain_ofFn w).mp hw
  change
    ((finWordRawCollapseEquiv A B n w).1).expandWord.IsChain (· ≠ ·)
  rw [finWordRawCollapseEquiv_expandWord]
  exact hchain

/-- Finite-word form of the inside predicate transport required before
applying Proposition 5.10. -/
theorem finWordCollapse_insideWord_noAdjacentOutside
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (w : Fin n → A ⊕ B) (hw : NoAdjacentEqual w) :
    let d := (finWordCollapseEquiv A B n w).1
    NoAdjacentOutside d.adjacentCutIndices d.insideWord := by
  dsimp only
  exact RawCollapseData.insideWord_noAdjacentOutside _
    (finWordCollapse_expand_isChain w hw)

/-- Finite-word form of the collapsed-word adjacency transport used by the
inductive call on the contracted tree. -/
theorem finWordCollapse_collapsedWord_noAdjacentEqual
    [DecidableEq A] [DecidableEq B]
    {n : ℕ} (w : Fin n → A ⊕ B) (hw : NoAdjacentEqual w) :
    let d := (finWordCollapseEquiv A B n w).1
    NoAdjacentEqual d.collapsedWord := by
  dsimp only
  exact RawCollapseData.collapsedWord_noAdjacentEqual _
    (finWordCollapse_expand_isChain w hw)

end Anderson4D
