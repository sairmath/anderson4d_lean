import Anderson4D.PermSum.CollapseBoundaryChain
import Anderson4D.PermSum.CollapsePredicates
import Anderson4D.PermSum.CollapseTreeCoordinates
import Anderson4D.PermSum.MergeWeights

/-!
# Inside-block chains and the cut-exception chain

This file proves the exact connector used in the collapse step: multiplying
the consecutive weights internal to the maximal inside blocks is the same as
multiplying the flattened inside-word chain after omitting precisely the
proper composition cuts.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace RawCollapseData

variable {A B : Type*}

/-- A gap internal to one block of the inside-word composition. -/
abbrev InsideBlockGap (d : RawCollapseData A B) :=
  Σ i : Fin d.blockComposition.length,
    Fin (d.blockComposition.blocksFun i - 1)

/-- The `i`th composition block, read directly from the flattened inside
word. -/
def insideBlockWord (d : RawCollapseData A B)
    (i : Fin d.blockComposition.length) :
    Fin (d.blockComposition.blocksFun i) → A :=
  fun j => d.insideWord (d.blockComposition.embedding i j)

/-- The composition view of a block recovers the recorded list block. -/
theorem ofFn_insideBlockWord (d : RawCollapseData A B)
    (i : Fin d.blockComposition.length) :
    List.ofFn (d.insideBlockWord i) =
      d.blocks.get ⟨i.1, by simpa using i.2⟩ := by
  have hlength :
      (d.blocks.get ⟨i.1, by simpa using i.2⟩).length =
        d.blockComposition.blocksFun i := by
    change
      d.blocks[i.1].length =
        (d.blocks.map List.length)[i.1]'(by simpa using i.2)
    simp
  apply List.ext_getElem
  · simpa using hlength.symm
  · intro j hjLeft hjRight
    have hget :=
      d.getElem_block_eq_insideList i.1 j
        (by simpa using i.2) hjRight
    simp only [List.getElem_ofFn]
    symm
    change d.blocks[i.1][j] = d.insideList.get _
    convert hget using 1
    apply congrArg d.insideList.get
    apply Fin.ext
    rfl

/-- The left endpoint in the flattened inside word of an internal block gap. -/
def insideBlockGapLeft (d : RawCollapseData A B)
    (g : d.InsideBlockGap) : Fin d.insideLength :=
  d.blockComposition.embedding g.1
    ⟨g.2.1, by
      have hg := g.2.2
      omega⟩

/-- The right endpoint in the flattened inside word of an internal block gap. -/
def insideBlockGapRight (d : RawCollapseData A B)
    (g : d.InsideBlockGap) : Fin d.insideLength :=
  d.blockComposition.embedding g.1
    ⟨g.2.1 + 1, by
      have hg := g.2.2
      omega⟩

@[simp]
theorem insideBlockGapLeft_val (d : RawCollapseData A B)
    (g : d.InsideBlockGap) :
    (d.insideBlockGapLeft g : ℕ) =
      d.blockComposition.sizeUpTo g.1 + g.2 := by
  rfl

@[simp]
theorem insideBlockGapRight_val (d : RawCollapseData A B)
    (g : d.InsideBlockGap) :
    (d.insideBlockGapRight g : ℕ) =
      d.blockComposition.sizeUpTo g.1 + g.2 + 1 := by
  rfl

/-- An internal block gap, regarded as an adjacency index of the flattened
inside word. -/
def insideBlockGapAdjacentIndex (d : RawCollapseData A B)
    (g : d.InsideBlockGap) : AdjacentIndex d.insideLength :=
  ⟨d.insideBlockGapLeft g, by
    change
      d.blockComposition.sizeUpTo g.1 + g.2.1 + 1 <
        d.insideLength
    have hg : g.2.1 + 1 < d.blockComposition.blocksFun g.1 := by
      have := g.2.2
      omega
    change
      g.2.1 + 1 <
        d.blockComposition.blocks[g.1.1]'g.1.2 at hg
    have hend :=
      d.blockComposition.sizeUpTo_succ g.1.2
    have htotal :=
      d.blockComposition.sizeUpTo_le (g.1.1 + 1)
    change
      d.blockComposition.sizeUpTo (g.1.1 + 1) ≤
        d.insideLength at htotal
    omega⟩

@[simp]
theorem insideBlockGapAdjacentIndex_val (d : RawCollapseData A B)
    (g : d.InsideBlockGap) :
    ((d.insideBlockGapAdjacentIndex g).1 : ℕ) =
      d.blockComposition.sizeUpTo g.1 + g.2 := by
  rfl

@[simp]
theorem adjacentSucc_insideBlockGapAdjacentIndex
    (d : RawCollapseData A B) (g : d.InsideBlockGap) :
    adjacentSucc (d.insideBlockGapAdjacentIndex g) =
      d.insideBlockGapRight g := by
  apply Fin.ext
  rfl

theorem insideBlockGapAdjacentIndex_injective (d : RawCollapseData A B) :
    Function.Injective d.insideBlockGapAdjacentIndex := by
  rintro ⟨i, q⟩ ⟨i', q'⟩ h
  have hleft :
      d.insideBlockGapLeft ⟨i, q⟩ =
        d.insideBlockGapLeft ⟨i', q'⟩ := by
    exact congrArg Subtype.val h
  have hi : i = i' := by
    have hindex := congrArg d.blockComposition.index hleft
    simpa [insideBlockGapLeft] using hindex
  subst i'
  have hq : q = q' := by
    apply Fin.ext
    have hval := congrArg Fin.val hleft
    simpa [insideBlockGapLeft] using
      Nat.add_left_cancel hval
  subst q'
  rfl

/-- The canonical embedding of internal block gaps into flattened adjacency
indices. -/
def insideBlockGapEmbedding (d : RawCollapseData A B) :
    d.InsideBlockGap ↪ AdjacentIndex d.insideLength :=
  ⟨d.insideBlockGapAdjacentIndex, d.insideBlockGapAdjacentIndex_injective⟩

/-- An internal block gap is never a proper composition cut. -/
theorem insideBlockGapAdjacentIndex_not_mem (d : RawCollapseData A B)
    (g : d.InsideBlockGap) :
    d.insideBlockGapAdjacentIndex g ∉ d.adjacentCutIndices := by
  intro hmem
  rw [d.mem_adjacentCutIndices_iff, d.mem_cutIndices_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hval := congrArg Fin.val hk
  simp only [cutEmbedding_val, finPredEquivAdjacentIndex_symm_val,
    insideBlockGapAdjacentIndex_val] at hval
  have hkpos :
      0 < d.blockComposition.sizeUpTo (k.1 + 1) := by
    have hfirst : 0 < d.blockComposition.sizeUpTo 1 := by
      have hkbound := k.2
      have hlength : 0 < d.blockComposition.length := by
        omega
      have hmono :=
        d.blockComposition.sizeUpTo_strict_mono
          (i := 0) hlength
      simpa using hmono
    exact lt_of_lt_of_le hfirst
      (d.blockComposition.monotone_sizeUpTo (by omega))
  have hboundary :
      d.blockComposition.sizeUpTo (k.1 + 1) =
        d.blockComposition.sizeUpTo g.1 + g.2.1 + 1 := by
    omega
  have hg :
      g.2.1 + 1 < d.blockComposition.blocksFun g.1 := by
    have := g.2.2
    omega
  change
    g.2.1 + 1 <
      d.blockComposition.blocks[g.1.1]'g.1.2 at hg
  have hend :=
    d.blockComposition.sizeUpTo_succ g.1.2
  by_cases hki : k.1 + 1 ≤ g.1.1
  · have hmono :=
      d.blockComposition.monotone_sizeUpTo hki
    omega
  · have hmono :=
      d.blockComposition.monotone_sizeUpTo
        (by omega : g.1.1 + 1 ≤ k.1 + 1)
    omega

/-- Every adjacency index outside the proper cuts comes from a unique
internal block gap. -/
theorem exists_insideBlockGap_of_not_mem (d : RawCollapseData A B)
    (edge : AdjacentIndex d.insideLength)
    (hedge : edge ∉ d.adjacentCutIndices) :
    ∃ g : d.InsideBlockGap,
      d.insideBlockGapAdjacentIndex g = edge := by
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
    have hle : p.1 + 1 ≤ c.sizeUpTo (i.1 + 1) := by
      omega
    by_contra hnotStrict
    have hboundary :
        c.sizeUpTo (i.1 + 1) = p.1 + 1 := by
      omega
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
  have hend := c.sizeUpTo_succ i.2
  let q := p.1 - c.sizeUpTo i.1
  have hq : q + 1 < c.blocksFun i := by
    change
      q + 1 < c.blocks[i.1]'i.2
    dsimp [q]
    omega
  let g : d.InsideBlockGap :=
    ⟨i, ⟨q, by
      change q < c.blocksFun i - 1
      omega⟩⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Fin.ext
  change c.sizeUpTo i.1 + q = p.1
  dsimp [q]
  omega

/-- Internal gaps of all blocks are canonically equivalent to adjacency
indices outside the proper composition cuts. -/
def insideBlockGapEquivNonCut (d : RawCollapseData A B) :
    d.InsideBlockGap ≃
      {edge : AdjacentIndex d.insideLength //
        edge ∉ d.adjacentCutIndices} :=
  Equiv.ofBijective
    (fun g =>
      ⟨d.insideBlockGapAdjacentIndex g,
        d.insideBlockGapAdjacentIndex_not_mem g⟩)
    ⟨fun _ _ h =>
        d.insideBlockGapAdjacentIndex_injective
          (congrArg Subtype.val h),
      fun edge => by
        obtain ⟨g, hg⟩ :=
          d.exists_insideBlockGap_of_not_mem edge.1 edge.2
        exact ⟨g, Subtype.ext hg⟩⟩

/-- Reindex a cut-exception product by the internal gaps of the composition
blocks. -/
theorem prod_ite_adjacentCutIndices_eq_prod_insideBlockGap
    (d : RawCollapseData A B)
    (f : AdjacentIndex d.insideLength → ℝ) :
    (∏ edge : AdjacentIndex d.insideLength,
        if edge ∈ d.adjacentCutIndices then 1 else f edge) =
      ∏ g : d.InsideBlockGap, f (d.insideBlockGapAdjacentIndex g) := by
  let p : AdjacentIndex d.insideLength → Prop :=
    fun edge => edge ∉ d.adjacentCutIndices
  calc
    (∏ edge : AdjacentIndex d.insideLength,
        if edge ∈ d.adjacentCutIndices then 1 else f edge) =
        ∏ edge : AdjacentIndex d.insideLength,
          if p edge then f edge else 1 := by
            apply Finset.prod_congr rfl
            intro edge _
            by_cases h : edge ∈ d.adjacentCutIndices <;>
              simp [p, h]
    _ = ∏ edge ∈ Finset.univ.filter p, f edge := by
      simpa using
        (Finset.prod_filter (s := Finset.univ) p f).symm
    _ = ∏ edge : {edge : AdjacentIndex d.insideLength // p edge},
        f edge.1 := by
      apply Finset.prod_subtype
      intro edge
      simp
    _ = ∏ g : d.InsideBlockGap,
        f (d.insideBlockGapAdjacentIndex g) := by
      let e := d.insideBlockGapEquivNonCut
      calc
        (∏ edge : {edge : AdjacentIndex d.insideLength // p edge},
            f edge.1) =
            ∏ g : d.InsideBlockGap, f (e g).1 := by
              simpa [p] using
                (e.prod_comp (fun edge => f edge.1)).symm
        _ = ∏ g : d.InsideBlockGap,
            f (d.insideBlockGapAdjacentIndex g) := by
              apply Finset.prod_congr rfl
              intro g _
              rfl

/-- The chain product of a recorded block is the indexed chain product of
that block as read from the flattened inside word. -/
theorem listChainProduct_block_eq_indexed
    (d : RawCollapseData A B)
    (edge : (A ⊕ B) → (A ⊕ B) → ℝ)
    (i : Fin d.blockComposition.length) :
    listChainProduct edge
        ((d.blocks.get ⟨i.1, by simpa using i.2⟩).map Sum.inl) =
      indexedChainProduct
        (fun a b : A => edge (.inl a) (.inl b))
        (d.insideBlockWord i) := by
  calc
    listChainProduct edge
        ((d.blocks.get ⟨i.1, by simpa using i.2⟩).map Sum.inl) =
        listChainProduct
          (fun a b : A => edge (.inl a) (.inl b))
          (d.blocks.get ⟨i.1, by simpa using i.2⟩) := by
            exact listChainProduct_map edge Sum.inl _
    _ = listChainProduct
        (fun a b : A => edge (.inl a) (.inl b))
        (List.ofFn (d.insideBlockWord i)) := by
          rw [d.ofFn_insideBlockWord i]
    _ = indexedChainProduct
        (fun a b : A => edge (.inl a) (.inl b))
        (d.insideBlockWord i) :=
      listChainProduct_ofFn _ _

/-- The product of all recorded inside-block chains, reindexed by the
internal gaps of the block composition. -/
theorem insideBlockChainProduct_eq_prod_insideBlockGap
    (d : RawCollapseData A B)
    (edge : (A ⊕ B) → (A ⊕ B) → ℝ) :
    d.insideBlockChainProduct edge =
      ∏ g : d.InsideBlockGap,
        edge (.inl (d.insideWord (d.insideBlockGapLeft g)))
          (.inl (d.insideWord (d.insideBlockGapRight g))) := by
  let blockProduct : List A → ℝ :=
    fun block => listChainProduct edge (block.map Sum.inl)
  have hlist :
      (d.blocks.map blockProduct).prod =
        ∏ i : Fin d.blocks.length, blockProduct (d.blocks.get i) := by
    rw [← List.ofFn_getElem_eq_map d.blocks blockProduct,
      List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro i _
    rfl
  let e : Fin d.blockComposition.length ≃ Fin d.blocks.length :=
    finCongr d.blockComposition_length
  calc
    d.insideBlockChainProduct edge =
        (d.blocks.map blockProduct).prod := by
          rfl
    _ = ∏ i : Fin d.blocks.length,
        blockProduct (d.blocks.get i) := hlist
    _ = ∏ i : Fin d.blockComposition.length,
        blockProduct (d.blocks.get (e i)) := by
          exact
            (e.prod_comp
              (fun i : Fin d.blocks.length =>
                blockProduct (d.blocks.get i))).symm
    _ = ∏ i : Fin d.blockComposition.length,
        indexedChainProduct
          (fun a b : A => edge (.inl a) (.inl b))
          (d.insideBlockWord i) := by
            apply Finset.prod_congr rfl
            intro i _
            simpa [blockProduct, e] using
              d.listChainProduct_block_eq_indexed edge i
    _ = ∏ i : Fin d.blockComposition.length,
        ∏ q : Fin (d.blockComposition.blocksFun i - 1),
          edge
            (.inl (d.insideWord
              (d.insideBlockGapLeft ⟨i, q⟩)))
            (.inl (d.insideWord
              (d.insideBlockGapRight ⟨i, q⟩))) := by
                apply Finset.prod_congr rfl
                intro i _
                unfold indexedChainProduct
                simp only [Nat.pred_eq_sub_one]
                apply Finset.prod_congr rfl
                intro q _
                rfl
    _ = ∏ g : d.InsideBlockGap,
        edge (.inl (d.insideWord (d.insideBlockGapLeft g)))
          (.inl (d.insideWord (d.insideBlockGapRight g))) := by
            exact (Fintype.prod_sigma' _).symm

end RawCollapseData

/-! ## Tree-facing connector -/

/-- The internal block factor in the expanded lattice chain is exactly the
restricted-tree Hepp chain with the proper composition cuts omitted. -/
theorem RawCollapseData.insideBlockChainProduct_originalCollapseEdge_eq_heppChainWeightExcept
    {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    d.insideBlockChainProduct (originalCollapseEdge z) =
      heppChainWeightExcept (restrictEmbedding z r)
        d.adjacentCutIndices (restrictedInsideWord r d) := by
  rw [d.insideBlockChainProduct_eq_prod_insideBlockGap]
  unfold heppChainWeightExcept
  rw [d.prod_ite_adjacentCutIndices_eq_prod_insideBlockGap]
  apply Finset.prod_congr rfl
  intro g _
  change
    latticeEdgeWeight
        (z (d.insideWord (d.insideBlockGapLeft g)).1)
        (z (d.insideWord (d.insideBlockGapRight g)).1) =
      latticeEdgeWeight
        (restrictEmbedding z r
          ((restrictLeafEquiv r).symm
            (d.insideWord (d.insideBlockGapLeft g))))
        (restrictEmbedding z r
          ((restrictLeafEquiv r).symm
            (d.insideWord (d.insideBlockGapRight g))))
  have hleft :=
    restrictEmbedding_apply_inside z r
      (d.insideWord (d.insideBlockGapLeft g))
  have hright :=
    restrictEmbedding_apply_inside z r
      (d.insideWord (d.insideBlockGapRight g))
  simpa only [restrictInsideLeaf] using
    congrArg₂ latticeEdgeWeight hleft.symm hright.symm

end
end Anderson4D
