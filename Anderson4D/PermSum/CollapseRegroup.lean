import Anderson4D.PermSum.CollapseFubini
import Anderson4D.PermSum.CollapseRawSum
import Anderson4D.PermSum.CollapseRHS

/-!
# Fixed-shape regrouping of the raw collapse sum

On one fixed block-composition shape, the raw datum is injectively determined
by its flattened inside list and collapsed list.  This module separates the
fixed-word majorant into a nonnegative weight of each list and applies the
finite Fubini bound.  No estimate for the number of shapes is taken here.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

/-! ## The cut set determined by a shape -/

/-- Proper partial sums of `shape`, represented as adjacency indices of an
arbitrary list.  The definition remains total when the list has the wrong
length; the fixed-shape application only uses the matching length. -/
def collapseShapeAdjacentCutIndices
    (shape : List ℕ) (n : ℕ) :
    Finset (AdjacentIndex n) := by
  classical
  exact Finset.univ.filter fun j =>
    ∃ i : ℕ, i + 1 < shape.length ∧
      (shape.take (i + 1)).sum = j.1.1 + 1

@[simp]
theorem mem_collapseShapeAdjacentCutIndices_iff
    (shape : List ℕ) (n : ℕ)
    (j : AdjacentIndex n) :
    j ∈ collapseShapeAdjacentCutIndices shape n ↔
      ∃ i : ℕ, i + 1 < shape.length ∧
        (shape.take (i + 1)).sum = j.1.1 + 1 := by
  classical
  simp [collapseShapeAdjacentCutIndices]

/-- A raw datum in the shape fiber has exactly the shape-defined cut set. -/
theorem RawCollapseData.adjacentCutIndices_eq_shape
    {A B : Type*} (d : RawCollapseData A B)
    (shape : List ℕ) (hshape : d.collapseShape = shape) :
    d.adjacentCutIndices =
      collapseShapeAdjacentCutIndices shape d.insideLength := by
  ext j
  rw [mem_collapseShapeAdjacentCutIndices_iff,
    d.mem_adjacentCutIndices_iff, d.mem_cutIndices_iff]
  have hlength :
      d.blockComposition.length = shape.length := by
    rw [d.blockComposition_length,
      ← d.collapseShape_length, hshape]
  have hblocks :
      d.blockComposition.blocks = shape := by
    rw [d.blockComposition_blocks]
    exact hshape
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k.1, ?_, ?_⟩
    · omega
    · have hval := congrArg Fin.val hk
      rw [d.cutEmbedding_val] at hval
      have hpositive :
          0 < d.blockComposition.sizeUpTo (k.1 + 1) := by
        have hfirst :
            0 < d.blockComposition.sizeUpTo 1 := by
          have hmono :=
            d.blockComposition.sizeUpTo_strict_mono
              (i := 0) (by
                have hkBound := k.2
                omega)
          simpa using hmono
        exact lt_of_lt_of_le hfirst
          (d.blockComposition.monotone_sizeUpTo (by omega))
      have hsum :
          d.blockComposition.sizeUpTo (k.1 + 1) =
            j.1.1 + 1 := by
        change
          d.blockComposition.sizeUpTo (k.1 + 1) - 1 =
            j.1.1 at hval
        omega
      rw [Composition.sizeUpTo, hblocks] at hsum
      exact hsum
  · rintro ⟨i, hi, hsum⟩
    let k : Fin (d.blockComposition.length - 1) :=
      ⟨i, by
        omega⟩
    refine ⟨k, ?_⟩
    apply Fin.ext
    rw [d.cutEmbedding_val]
    have hsum' :
        d.blockComposition.sizeUpTo (i + 1) = j.1.1 + 1 := by
      rw [Composition.sizeUpTo, hblocks]
      exact hsum
    change
      d.blockComposition.sizeUpTo (i + 1) - 1 = j.1.1
    omega

/-! ## Word and list chain weights -/

/-- P-5.10's cut-exception summand with the cut set determined by `shape`. -/
def collapseInsideWordChainWeight
    {A : Type*} [DecidableEq A]
    {n : ℕ} (z : A → Fin 4 → ℤ) (shape : List ℕ)
    (w : Fin n → A) : ℝ :=
  let O := collapseShapeAdjacentCutIndices shape n
  if NoAdjacentOutside O w then
    ∏ j : AdjacentIndex n,
      if j ∈ O then 1
      else latticeEdgeWeight (z (w j.1)) (z (w (adjacentSucc j)))
  else
    0

/-- The same weight as a function of the underlying list, for fixed-shape
Fubini separation. -/
def collapseInsideListChainWeight
    {A : Type*} [DecidableEq A]
    (z : A → Fin 4 → ℤ) (shape : List ℕ) (l : List A) : ℝ :=
  collapseInsideWordChainWeight z shape (listWord l)

/-- Transport a finite word across an equality of its carrier lengths. -/
def castFinWord {A : Type*} {n m : ℕ}
    (h : n = m) (w : Fin n → A) : Fin m → A :=
  fun i => w (i.cast h.symm)

@[simp]
theorem castFinWord_listWord_ofFn
    {A : Type*} {n : ℕ} (w : Fin n → A) :
    castFinWord (List.length_ofFn (f := w))
        (listWord (List.ofFn w)) =
      w := by
  funext i
  simp [castFinWord, listWord, List.Vector.get]

/-- The inside chain statistic is invariant under transport of the finite
carrier along a length equality. -/
theorem collapseInsideWordChainWeight_cast
    {A : Type*} [DecidableEq A] {n m : ℕ}
    (z : A → Fin 4 → ℤ) (shape : List ℕ)
    (h : n = m) (w : Fin n → A) :
    collapseInsideWordChainWeight z shape w =
      collapseInsideWordChainWeight z shape (castFinWord h w) := by
  subst m
  rfl

theorem collapseInsideWordChainWeight_nonneg
    {A : Type*} [DecidableEq A] {n : ℕ}
    (z : A → Fin 4 → ℤ) (shape : List ℕ) (w : Fin n → A) :
    0 ≤ collapseInsideWordChainWeight z shape w := by
  classical
  simp only [collapseInsideWordChainWeight]
  split_ifs
  · apply Finset.prod_nonneg
    intro j _
    split_ifs
    · positivity
    · unfold latticeEdgeWeight
      positivity
  · exact le_rfl

theorem collapseInsideListChainWeight_nonneg
    {A : Type*} [DecidableEq A]
    (z : A → Fin 4 → ℤ) (shape : List ℕ) (l : List A) :
    0 ≤ collapseInsideListChainWeight z shape l :=
  collapseInsideWordChainWeight_nonneg z shape (listWord l)

@[simp]
theorem collapseInsideListChainWeight_ofFn
    {A : Type*} [DecidableEq A] {n : ℕ}
    (z : A → Fin 4 → ℤ) (shape : List ℕ) (w : Fin n → A) :
    collapseInsideListChainWeight z shape (List.ofFn w) =
      collapseInsideWordChainWeight z shape w := by
  unfold collapseInsideListChainWeight
  rw [collapseInsideWordChainWeight_cast z shape
    (List.length_ofFn (f := w)),
    castFinWord_listWord_ofFn]

/-- Renaming a fixed-shape inside word to the restricted-tree alphabet turns
the raw shape weight into the exact P-5.10 summand. -/
theorem collapseInsideWordChainWeight_eq_restricted
    {t : PlaneTree} {n : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (shape : List ℕ) (w : Fin n → InsideLeaf r) :
    collapseInsideWordChainWeight
        (fun a : InsideLeaf r => z a.1) shape w =
      singleScaleChainWeight (restrictEmbedding z r)
        (collapseShapeAdjacentCutIndices shape n)
        (wordRenameEquiv (restrictInsideAlphabetEquiv r) n w) := by
  let O := collapseShapeAdjacentCutIndices shape n
  have hpredicate :=
    noAdjacentOutside_wordRename_iff
      (restrictInsideAlphabetEquiv r) O w
  unfold collapseInsideWordChainWeight singleScaleChainWeight
    heppChainWeightExcept
  by_cases hraw : NoAdjacentOutside O w
  · have hrenamed :
        NoAdjacentOutside O
          (wordRenameEquiv (restrictInsideAlphabetEquiv r) n w) :=
      hpredicate.mpr hraw
    rw [if_pos hraw, if_pos hrenamed]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j ∈ O
    · change j ∈ collapseShapeAdjacentCutIndices shape n at hj
      rw [if_pos hj, if_pos hj]
    · change j ∉ collapseShapeAdjacentCutIndices shape n at hj
      rw [if_neg hj, if_neg hj, wordRenameEquiv_apply,
        wordRenameEquiv_apply]
      have hleft := restrictEmbedding_apply_inside z r (w j.1)
      have hright :=
        restrictEmbedding_apply_inside z r (w (adjacentSucc j))
      simpa only [restrictInsideLeaf, restrictInsideAlphabetEquiv] using
        congrArg₂ latticeEdgeWeight hleft.symm hright.symm
  · have hrenamed :
        ¬NoAdjacentOutside O
          (wordRenameEquiv (restrictInsideAlphabetEquiv r) n w) := by
      intro h
      exact hraw (hpredicate.mp h)
    rw [if_neg hraw, if_neg hrenamed]

/-- Shape length is the number of blocks in every datum of the fiber. -/
theorem RawCollapseData.blocks_length_eq_shape_length
    {A B : Type*} (d : RawCollapseData A B)
    {shape : List ℕ} (hshape : d.collapseShape = shape) :
    d.blocks.length = shape.length := by
  rw [← d.collapseShape_length, hshape]

/-- Shape mass is the flattened inside length in every datum of the fiber. -/
theorem RawCollapseData.insideLength_eq_shape_sum
    {A B : Type*} (d : RawCollapseData A B)
    {shape : List ℕ} (hshape : d.collapseShape = shape) :
    d.insideLength = shape.sum := by
  rw [← d.collapseShape_sum, hshape]

/-- The list-only inside chain is exactly the actual restricted-tree
single-scale summand on a datum in the shape fiber. -/
theorem RawCollapseData.collapseInsideListChainWeight_eq_singleScale
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (shape : List ℕ) (hshape : d.collapseShape = shape) :
    collapseInsideListChainWeight
        (fun a : InsideLeaf r => z a.1) shape d.insideList =
      singleScaleChainWeight (restrictEmbedding z r)
        d.adjacentCutIndices (restrictedInsideWord r d) := by
  have hcuts := d.adjacentCutIndices_eq_shape shape hshape
  unfold collapseInsideListChainWeight
  change collapseInsideWordChainWeight
    (fun a : InsideLeaf r => z a.1) shape d.insideWord =
      singleScaleChainWeight (restrictEmbedding z r)
        d.adjacentCutIndices (restrictedInsideWord r d)
  unfold collapseInsideWordChainWeight singleScaleChainWeight
    heppChainWeightExcept
  rw [← hcuts]
  have hpredicate :=
    noAdjacentOutside_wordRename_iff
      (restrictInsideAlphabetEquiv r)
      d.adjacentCutIndices d.insideWord
  by_cases hraw :
      NoAdjacentOutside d.adjacentCutIndices d.insideWord
  · have hrenamed :
        NoAdjacentOutside d.adjacentCutIndices
          (restrictedInsideWord r d) := by
      change
        NoAdjacentOutside d.adjacentCutIndices
          (wordRenameEquiv (restrictInsideAlphabetEquiv r)
            d.insideLength d.insideWord)
      exact hpredicate.mpr hraw
    rw [if_pos hraw, if_pos hrenamed]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j ∈ d.adjacentCutIndices
    · simp [hj]
    · simp only [hj, if_false]
      rw [restrictedInsideWord_apply, restrictedInsideWord_apply]
      have hleft :=
        restrictEmbedding_apply_inside z r (d.insideWord j.1)
      have hright :=
        restrictEmbedding_apply_inside z r
          (d.insideWord (adjacentSucc j))
      simpa only [restrictInsideLeaf] using
        congrArg₂ latticeEdgeWeight hleft.symm hright.symm
  · have hrenamed :
        ¬NoAdjacentOutside d.adjacentCutIndices
          (restrictedInsideWord r d) := by
      intro h
      apply hraw
      change
        NoAdjacentOutside d.adjacentCutIndices
          (wordRenameEquiv (restrictInsideAlphabetEquiv r)
            d.insideLength d.insideWord) at h
      exact hpredicate.mp h
    rw [if_neg hraw, if_neg hrenamed]

/-! ## Fixed-shape marginal weights -/

/-- Inside-list marginal: inverse marker factorial, inside factorial ledger,
the geometric `4^n`, and the restricted single-scale word weight. -/
def collapseInsideShapeWeight
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (shape : List ℕ) (l : List (InsideLeaf r)) : ℝ :=
  (shape.length.factorial : ℝ)⁻¹ *
    (∏ a : InsideLeaf r,
      ((insideMultiplicity
        (splitLeafMultiplicity mu r) a).factorial : ℝ)) *
    (4 : ℝ) ^ shape.sum *
    collapseInsideListChainWeight
      (fun a : InsideLeaf r => z a.1) shape l

/-- Collapsed-list marginal: contracted factorial ledger and the raw
marker/outside primitive-separated word weight. -/
def collapseContractedShapeWeight
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (shape : List ℕ)
    (l : List (Unit ⊕ OutsideLeaf r)) : ℝ :=
  (∏ x : Unit ⊕ OutsideLeaf r,
      ((markerMultiplicity shape.length
        (outsideMultiplicity (splitLeafMultiplicity mu r)) x).factorial :
          ℝ)) *
    primitiveSeparatedAlphabetChainWeight
      (collapsedCollapsePoint z r lstar) (listWord l)

theorem collapseInsideShapeWeight_nonneg
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (shape : List ℕ) (l : List (InsideLeaf r)) :
    0 ≤ collapseInsideShapeWeight mu z r shape l := by
  unfold collapseInsideShapeWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg <;> positivity
    · positivity
  · exact collapseInsideListChainWeight_nonneg
      (fun a : InsideLeaf r => z a.1) shape l

theorem collapseContractedShapeWeight_nonneg
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (shape : List ℕ)
    (l : List (Unit ⊕ OutsideLeaf r)) :
    0 ≤ collapseContractedShapeWeight mu z r lstar shape l := by
  unfold collapseContractedShapeWeight
  apply mul_nonneg
  · positivity
  · unfold primitiveSeparatedAlphabetChainWeight
    split_ifs
    · unfold alphabetChainWeight latticeEdgeWeight
      positivity
    · exact le_rfl

/-- The primitive-separated alphabet statistic is invariant under transport
of the finite carrier along a length equality. -/
theorem primitiveSeparatedAlphabetChainWeight_cast
    {A : Type*} [Fintype A] [DecidableEq A] {n m : ℕ}
    (z : A → Fin 4 → ℤ) (h : n = m) (w : Fin n → A) :
    primitiveSeparatedAlphabetChainWeight z w =
      primitiveSeparatedAlphabetChainWeight z (castFinWord h w) := by
  subst m
  rfl

@[simp]
theorem primitiveSeparatedAlphabetChainWeight_listWord_ofFn
    {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
    (z : A → Fin 4 → ℤ) (w : Fin n → A) :
    primitiveSeparatedAlphabetChainWeight z
        (listWord (List.ofFn w)) =
      primitiveSeparatedAlphabetChainWeight z w := by
  rw [primitiveSeparatedAlphabetChainWeight_cast z
    (List.length_ofFn (f := w)),
    castFinWord_listWord_ofFn]

/-- Renaming a marker/outside word to the contracted-tree alphabet turns
the raw alphabet statistic into the exact contracted P-5.9 summand. -/
theorem primitiveSeparatedAlphabetChainWeight_eq_contracted
    {t : PlaneTree} {n : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r)
    (w : Fin n → Unit ⊕ OutsideLeaf r) :
    primitiveSeparatedAlphabetChainWeight
        (collapsedCollapsePoint z r lstar) w =
      primitiveSeparatedChainWeight (contractEmbedding z r lstar)
        (wordRenameEquiv (contractCollapsedAlphabetEquiv r) n w) := by
  let e := contractCollapsedAlphabetEquiv r
  let p := collapsedCollapsePoint z r lstar
  calc
    primitiveSeparatedAlphabetChainWeight p w =
        primitiveSeparatedAlphabetChainWeight
          (fun l => p (e.symm l))
          (wordRenameEquiv e n w) := by
      exact
        (primitiveSeparatedAlphabetChainWeight_wordRename e p w).symm
    _ = primitiveSeparatedChainWeight (contractEmbedding z r lstar)
        (wordRenameEquiv e n w) := by
      have hp :
          (fun l : HeppLeaf (contractAt t r.1) => p (e.symm l)) =
            contractEmbedding z r lstar := by
        exact
          collapsedCollapsePoint_contractCollapsedAlphabetEquiv_symm
            z r lstar
      rw [hp]
      rfl

/-! ## Exact factorization on a shape fiber -/

/-- The raw collapsed-list statistic is the primitive-separated statistic
of the corresponding word on the contracted tree. -/
theorem RawCollapseData.collapseContractedListChainWeight_eq
    {t : PlaneTree} (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    primitiveSeparatedAlphabetChainWeight
        (collapsedCollapsePoint z r lstar) (listWord d.collapsed) =
      primitiveSeparatedChainWeight (contractEmbedding z r lstar)
        (contractedCollapsedWord r d) := by
  let e := contractCollapsedAlphabetEquiv r
  let p := collapsedCollapsePoint z r lstar
  change primitiveSeparatedAlphabetChainWeight p d.collapsedWord =
    primitiveSeparatedChainWeight (contractEmbedding z r lstar)
      (contractedCollapsedWord r d)
  calc
    primitiveSeparatedAlphabetChainWeight p d.collapsedWord =
        primitiveSeparatedAlphabetChainWeight
          (fun l => p (e.symm l))
          (wordRenameEquiv e d.collapsed.length d.collapsedWord) := by
      exact
        (primitiveSeparatedAlphabetChainWeight_wordRename
          e p d.collapsedWord).symm
    _ = primitiveSeparatedChainWeight (contractEmbedding z r lstar)
        (contractedCollapsedWord r d) := by
      have hp :
          (fun l : HeppLeaf (contractAt t r.1) => p (e.symm l)) =
            contractEmbedding z r lstar := by
        exact
          collapsedCollapsePoint_contractCollapsedAlphabetEquiv_symm
            z r lstar
      rw [hp]
      rfl

/-- On an active datum in a fixed shape fiber, every factor in the raw
majorant splits exactly into an inside-list and a collapsed-list marginal. -/
theorem collapseRawFixedWordSummand_eq_shapeWeights_of_active
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (shape : List ℕ) (hshape : d.collapseShape = shape)
    (hactive :
      CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d ∧
        NoProperLeafBlock d.expandedWord ∧
        NoAdjacentEqual d.expandedWord) :
    collapseRawFixedWordSummand mu r z lstar d =
      collapseInsideShapeWeight mu z r shape d.insideList *
        collapseContractedShapeWeight mu z r lstar shape d.collapsed := by
  rw [collapseRawFixedWordSummand, if_pos hactive]
  have hblocks := d.blocks_length_eq_shape_length hshape
  have hins := d.insideLength_eq_shape_sum hshape
  have hinside :=
    d.collapseInsideListChainWeight_eq_singleScale z r shape hshape
  have hcontracted :=
    d.collapseContractedListChainWeight_eq z r lstar
  have hpow :
      (4 : ℝ) ^ d.insideLength = (4 : ℝ) ^ shape.sum :=
    congrArg (fun n : ℕ => (4 : ℝ) ^ n) hins
  unfold collapseRawLedgerCoefficient collapseInsideShapeWeight
    collapseContractedShapeWeight
  rw [collapsedMultiplicity_eq_markerMultiplicity, hblocks, hpow,
    hinside, hcontracted]
  ring

/-- The factorized nonnegative marginals dominate the raw summand on every
datum in the shape fiber, including inactive data. -/
theorem collapseRawFixedWordSummand_le_shapeWeights
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (shape : List ℕ) (hshape : d.collapseShape = shape) :
    collapseRawFixedWordSummand mu r z lstar d ≤
      collapseInsideShapeWeight mu z r shape d.insideList *
        collapseContractedShapeWeight mu z r lstar shape d.collapsed := by
  by_cases hactive :
      CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d ∧
        NoProperLeafBlock d.expandedWord ∧
        NoAdjacentEqual d.expandedWord
  · exact le_of_eq
      (collapseRawFixedWordSummand_eq_shapeWeights_of_active
        mu z r lstar d shape hshape hactive)
  · rw [collapseRawFixedWordSummand, if_neg hactive]
    exact mul_nonneg
      (collapseInsideShapeWeight_nonneg mu z r shape d.insideList)
      (collapseContractedShapeWeight_nonneg
        mu z r lstar shape d.collapsed)

/-! ## Valid-word coordinates on a spec shape fiber -/

/-- Fixed-shape data that also satisfy the prescribed split multiplicity. -/
abbrev SpecFixedRawCollapseShapeData
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (M : ℕ) (shape : List ℕ) :=
  {d : FixedRawCollapseData
      (InsideLeaf r) (OutsideLeaf r) M //
    CollapseMultiplicitySpec
        (splitLeafMultiplicity mu r) d.1 ∧
      d.1.collapseShape = shape}

/-- Forget only the multiplicity certificate, retaining the fixed-shape
certificate. -/
def SpecFixedRawCollapseShapeData.toFixedShape
    {t : PlaneTree} {mu : Multiplicities t} {r : VPos t}
    {M : ℕ} {shape : List ℕ}
    (d : SpecFixedRawCollapseShapeData mu r M shape) :
    FixedRawCollapseShapeData
      (InsideLeaf r) (OutsideLeaf r) M shape :=
  ⟨d.1, d.2.2⟩

theorem castFinWord_mem_validWords_iff
    {A : Type*} [Fintype A] [DecidableEq A]
    {n m : ℕ} (h : n = m) (mult : A → ℕ)
    (w : Fin n → A) :
    castFinWord h w ∈ validWords mult ↔
      w ∈ validWords mult := by
  subst m
  rfl

/-- The fixed-shape inside coordinate has exactly the prescribed raw
inside multiplicity. -/
theorem fixedShapeInsideWord_mem_validWords_of_spec
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {M : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B M shape)
    (hSpec : CollapseMultiplicitySpec mult d.1.1) :
    fixedShapeInsideWord d ∈
      validWords (insideMultiplicity mult) := by
  have hmem := d.1.1.insideWord_mem_validWords hSpec
  have hlength := fixedShape_insideLength d
  have hword :
      fixedShapeInsideWord d =
        castFinWord hlength d.1.1.insideWord := by
    funext i
    rfl
  rw [hword]
  exact
    (castFinWord_mem_validWords_iff hlength
      (insideMultiplicity mult) d.1.1.insideWord).mpr hmem

/-- The fixed-shape collapsed coordinate has the marker multiplicity
`shape.length` and the prescribed outside multiplicities. -/
theorem fixedShapeCollapsedWord_mem_validWords_of_spec
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {M : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B M shape)
    (hSpec : CollapseMultiplicitySpec mult d.1.1) :
    fixedShapeCollapsedWord d ∈
      validWords
        (markerMultiplicity shape.length
          (outsideMultiplicity mult)) := by
  have hmem := d.1.1.collapsedWord_mem_validWords hSpec
  have hblocks := d.1.1.blocks_length_eq_shape_length d.2
  rw [collapsedMultiplicity_eq_markerMultiplicity, hblocks] at hmem
  have hlength := fixedShape_collapsedLength d
  have hword :
      fixedShapeCollapsedWord d =
        castFinWord hlength d.1.1.collapsedWord := by
    funext i
    rfl
  rw [hword]
  exact
    (castFinWord_mem_validWords_iff hlength
      (markerMultiplicity shape.length (outsideMultiplicity mult))
      d.1.1.collapsedWord).mpr hmem

/-! ### Tree-facing valid-word subtypes -/

/-- Valid restricted-tree words on the fixed inside length. -/
abbrev RestrictedShapeValidWord
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (shape : List ℕ) :=
  ↥(validWords (M := shape.sum)
    (leafMultiplicity (restrictMultiplicities mu r)))

/-- Valid contracted-tree words on the fixed collapsed length. -/
abbrev ContractedShapeValidWord
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (M : ℕ) (shape : List ℕ)
    (hs : 1 ≤ shape.length - 1) :=
  ↥(validWords (M := M - shape.sum + shape.length)
    (leafMultiplicity
      (contractMultiplicities mu r (shape.length - 1) hs)))

/-- At fixed shape, the renamed marker/outside multiplicity is exactly the
leaf multiplicity of the one contracted tree used by the induction call. -/
theorem fixedShapeContractedMultiplicity_eq
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (shape : List ℕ) (hs : 1 ≤ shape.length - 1) :
    renameMultiplicity (contractCollapsedAlphabetEquiv r)
        (markerMultiplicity shape.length
          (outsideMultiplicity (splitLeafMultiplicity mu r))) =
      leafMultiplicity
        (contractMultiplicities mu r (shape.length - 1) hs) := by
  funext l
  obtain ⟨x, rfl⟩ :=
    (contractCollapsedAlphabetEquiv r).surjective l
  rw [renameMultiplicity_apply]
  cases x with
  | inl u =>
      cases u
      have hmarker :
          contractCollapsedAlphabetEquiv r (.inl ()) =
            contractMarkerLeaf r := by
        apply (contractLeafSumEquiv r).injective
        simp [contractCollapsedAlphabetEquiv]
      rw [hmarker, contractMultiplicities_marker]
      simp only [markerMultiplicity]
      omega
  | inr lout =>
      change outsideMultiplicity
          (splitLeafMultiplicity mu r) lout =
        leafMultiplicity
          (contractMultiplicities mu r (shape.length - 1) hs)
          (contractOutsideLeaf r lout)
      rw [contractMultiplicities_outside]
      rfl

/-- The inside coordinate of a spec+shape datum, packaged directly as a
valid word for the restricted-tree `paperSum`. -/
def specShapeRestrictedValidWord
    {t : PlaneTree} {mu : Multiplicities t} {r : VPos t}
    {M : ℕ} {shape : List ℕ}
    (d : SpecFixedRawCollapseShapeData mu r M shape) :
    RestrictedShapeValidWord mu r shape := by
  let ds := d.toFixedShape
  let w :=
    wordRenameEquiv (restrictInsideAlphabetEquiv r) shape.sum
      (fixedShapeInsideWord ds)
  refine ⟨w, ?_⟩
  have hraw :=
    fixedShapeInsideWord_mem_validWords_of_spec ds d.2.1
  have hrenamed :=
    (wordRename_mem_validWords_iff
      (restrictInsideAlphabetEquiv r)
      (insideMultiplicity (splitLeafMultiplicity mu r))
      (fixedShapeInsideWord ds)).mpr hraw
  change w ∈ validWords (restrictedCoordinateMultiplicity mu r)
  rw [restrictedCoordinateMultiplicity_eq]
  exact hrenamed

/-- The collapsed coordinate of a spec+shape datum, packaged directly as a
valid word for the fixed contracted-tree `paperSum`. -/
def specShapeContractedValidWord
    {t : PlaneTree} {mu : Multiplicities t} {r : VPos t}
    {M : ℕ} {shape : List ℕ}
    (hs : 1 ≤ shape.length - 1)
    (d : SpecFixedRawCollapseShapeData mu r M shape) :
    ContractedShapeValidWord mu r M shape hs := by
  let ds := d.toFixedShape
  let w :=
    wordRenameEquiv (contractCollapsedAlphabetEquiv r)
      (M - shape.sum + shape.length)
      (fixedShapeCollapsedWord ds)
  refine ⟨w, ?_⟩
  have hraw :=
    fixedShapeCollapsedWord_mem_validWords_of_spec ds d.2.1
  have hrenamed :=
    (wordRename_mem_validWords_iff
      (contractCollapsedAlphabetEquiv r)
      (markerMultiplicity shape.length
        (outsideMultiplicity (splitLeafMultiplicity mu r)))
      (fixedShapeCollapsedWord ds)).mpr hraw
  change w ∈ validWords
    (renameMultiplicity (contractCollapsedAlphabetEquiv r)
      (markerMultiplicity shape.length
        (outsideMultiplicity (splitLeafMultiplicity mu r)))) at hrenamed
  rw [fixedShapeContractedMultiplicity_eq mu r shape hs] at hrenamed
  exact hrenamed

/-- No multiplicity-bearing raw datum is counted twice by the two
tree-facing valid-word coordinates. -/
theorem specShapeValidWordPair_injective
    {t : PlaneTree} {mu : Multiplicities t} {r : VPos t}
    {M : ℕ} {shape : List ℕ}
    (hs : 1 ≤ shape.length - 1) :
    Function.Injective fun
      d : SpecFixedRawCollapseShapeData mu r M shape =>
        (specShapeRestrictedValidWord d,
          specShapeContractedValidWord hs d) := by
  intro d e h
  have hinsideRenamed :=
    congrArg Subtype.val (congrArg Prod.fst h)
  have hcollapsedRenamed :=
    congrArg Subtype.val (congrArg Prod.snd h)
  have hinside :
      fixedShapeInsideWord d.toFixedShape =
        fixedShapeInsideWord e.toFixedShape :=
    (wordRenameEquiv
      (restrictInsideAlphabetEquiv r) shape.sum).injective
        hinsideRenamed
  have hcollapsed :
      fixedShapeCollapsedWord d.toFixedShape =
        fixedShapeCollapsedWord e.toFixedShape :=
    (wordRenameEquiv
      (contractCollapsedAlphabetEquiv r)
      (M - shape.sum + shape.length)).injective
        hcollapsedRenamed
  have hfixed : d.toFixedShape = e.toFixedShape := by
    apply fixedShapeWordPair_injective
    exact Prod.ext hinside hcollapsed
  apply Subtype.ext
  change d.1 = e.1
  exact congrArg
    (fun x : FixedRawCollapseShapeData
      (InsideLeaf r) (OutsideLeaf r) M shape => x.1) hfixed

/-! ## Valid-word marginal weights -/

/-- Inside marginal on exactly the valid restricted-tree words. -/
def restrictedShapeMarginalWeight
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (shape : List ℕ)
    (w : RestrictedShapeValidWord mu r shape) : ℝ :=
  (shape.length.factorial : ℝ)⁻¹ *
    (∏ a : InsideLeaf r,
      ((insideMultiplicity
        (splitLeafMultiplicity mu r) a).factorial : ℝ)) *
    (4 : ℝ) ^ shape.sum *
    singleScaleChainWeight (restrictEmbedding z r)
      (collapseShapeAdjacentCutIndices shape shape.sum) w.1

/-- Collapsed marginal on exactly the valid contracted-tree words. -/
def contractedShapeMarginalWeight
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (M : ℕ) (shape : List ℕ)
    (hs : 1 ≤ shape.length - 1)
    (w : ContractedShapeValidWord mu r M shape hs) : ℝ :=
  (∏ x : Unit ⊕ OutsideLeaf r,
      ((markerMultiplicity shape.length
        (outsideMultiplicity (splitLeafMultiplicity mu r)) x).factorial :
          ℝ)) *
    primitiveSeparatedChainWeight (contractEmbedding z r lstar) w.1

theorem restrictedShapeMarginalWeight_nonneg
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (shape : List ℕ)
    (w : RestrictedShapeValidWord mu r shape) :
    0 ≤ restrictedShapeMarginalWeight mu z r shape w := by
  unfold restrictedShapeMarginalWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg <;> positivity
    · positivity
  · unfold singleScaleChainWeight heppChainWeightExcept
    split_ifs
    · apply Finset.prod_nonneg
      intro j _
      split_ifs
      · positivity
      · unfold latticeEdgeWeight
        positivity
    · exact le_rfl

theorem contractedShapeMarginalWeight_nonneg
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (M : ℕ) (shape : List ℕ)
    (hs : 1 ≤ shape.length - 1)
    (w : ContractedShapeValidWord mu r M shape hs) :
    0 ≤ contractedShapeMarginalWeight
      mu z r lstar M shape hs w := by
  unfold contractedShapeMarginalWeight
  apply mul_nonneg
  · positivity
  · unfold primitiveSeparatedChainWeight heppChainWeight
    split_ifs
    · unfold latticeEdgeWeight
      positivity
    · exact le_rfl

/-- On a spec+shape coordinate, the list-level inside marginal is exactly
the corresponding restricted valid-word marginal. -/
theorem collapseInsideShapeWeight_eq_restrictedMarginal
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    {M : ℕ} {shape : List ℕ}
    (d : SpecFixedRawCollapseShapeData mu r M shape) :
    collapseInsideShapeWeight mu z r shape d.1.1.insideList =
      restrictedShapeMarginalWeight mu z r shape
        (specShapeRestrictedValidWord d) := by
  let ds := d.toFixedShape
  change collapseInsideShapeWeight mu z r shape ds.1.1.insideList =
    restrictedShapeMarginalWeight mu z r shape
      (specShapeRestrictedValidWord d)
  rw [← ofFn_fixedShapeInsideWord ds]
  unfold collapseInsideShapeWeight restrictedShapeMarginalWeight
  rw [collapseInsideListChainWeight_ofFn,
    collapseInsideWordChainWeight_eq_restricted]
  rfl

/-- On a spec+shape coordinate, the list-level collapsed marginal is exactly
the corresponding contracted valid-word marginal. -/
theorem collapseContractedShapeWeight_eq_contractedMarginal
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) {M : ℕ} {shape : List ℕ}
    (hs : 1 ≤ shape.length - 1)
    (d : SpecFixedRawCollapseShapeData mu r M shape) :
    collapseContractedShapeWeight
        mu z r lstar shape d.1.1.collapsed =
      contractedShapeMarginalWeight
        mu z r lstar M shape hs
          (specShapeContractedValidWord hs d) := by
  let ds := d.toFixedShape
  change collapseContractedShapeWeight
      mu z r lstar shape ds.1.1.collapsed =
    contractedShapeMarginalWeight
      mu z r lstar M shape hs
        (specShapeContractedValidWord hs d)
  rw [← ofFn_fixedShapeCollapsedWord ds]
  unfold collapseContractedShapeWeight
    contractedShapeMarginalWeight
  rw [primitiveSeparatedAlphabetChainWeight_listWord_ofFn,
    primitiveSeparatedAlphabetChainWeight_eq_contracted]
  rfl

/-! ### Exact marginal sums -/

/-- Summing over the subtype attached to `validWords` is exactly
`wordSum`; no unrestricted word family is introduced. -/
theorem sum_validWordSubtype_eq_wordSum
    {A : Type*} [Fintype A] [DecidableEq A]
    {n : ℕ} (mult : A → ℕ) (F : (Fin n → A) → ℝ) :
    (∑ w : ↥(validWords (M := n) mult), F w.1) =
      wordSum mult F := by
  unfold wordSum
  calc
    (∑ w : ↥(validWords (M := n) mult), F w.1) =
        ∑ w ∈ (validWords (M := n) mult).attach, F w.1 := by
      rw [Finset.attach_eq_univ]
    _ = ∑ w ∈ validWords (M := n) mult, F w :=
      Finset.sum_attach _ F

/-- The restricted valid-word marginal sums to the inverse marker
factorial and geometric factor times the exact restricted `paperSum`. -/
theorem sum_restrictedShapeMarginalWeight_eq_paperSum
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (shape : List ℕ) :
    (∑ w : RestrictedShapeValidWord mu r shape,
        restrictedShapeMarginalWeight mu z r shape w) =
      (shape.length.factorial : ℝ)⁻¹ *
        (4 : ℝ) ^ shape.sum *
        paperSum
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight (restrictEmbedding z r)
            (collapseShapeAdjacentCutIndices shape shape.sum)) := by
  have hledger :=
    factorialLedger_rename (restrictInsideAlphabetEquiv r)
      (insideMultiplicity (splitLeafMultiplicity mu r))
  change
    (∏ b : HeppLeaf (subtreeAt t r.1),
      ((restrictedCoordinateMultiplicity mu r b).factorial : ℝ)) =
      ∏ a : InsideLeaf r,
        ((insideMultiplicity
          (splitLeafMultiplicity mu r) a).factorial : ℝ) at hledger
  rw [restrictedCoordinateMultiplicity_eq] at hledger
  unfold restrictedShapeMarginalWeight
  calc
    (∑ w : RestrictedShapeValidWord mu r shape,
        (shape.length.factorial : ℝ)⁻¹ *
            (∏ a : InsideLeaf r,
              ((insideMultiplicity
                (splitLeafMultiplicity mu r) a).factorial : ℝ)) *
          (4 : ℝ) ^ shape.sum *
          singleScaleChainWeight (restrictEmbedding z r)
            (collapseShapeAdjacentCutIndices shape shape.sum) w.1) =
        ((shape.length.factorial : ℝ)⁻¹ *
            (∏ a : InsideLeaf r,
              ((insideMultiplicity
                (splitLeafMultiplicity mu r) a).factorial : ℝ)) *
          (4 : ℝ) ^ shape.sum) *
          ∑ w : RestrictedShapeValidWord mu r shape,
            singleScaleChainWeight (restrictEmbedding z r)
              (collapseShapeAdjacentCutIndices shape shape.sum) w.1 := by
      rw [Finset.mul_sum]
    _ = ((shape.length.factorial : ℝ)⁻¹ *
            (∏ a : InsideLeaf r,
              ((insideMultiplicity
                (splitLeafMultiplicity mu r) a).factorial : ℝ)) *
          (4 : ℝ) ^ shape.sum) *
        wordSum
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight (restrictEmbedding z r)
            (collapseShapeAdjacentCutIndices shape shape.sum)) := by
      rw [sum_validWordSubtype_eq_wordSum]
    _ = (shape.length.factorial : ℝ)⁻¹ *
        (4 : ℝ) ^ shape.sum *
        paperSum
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight (restrictEmbedding z r)
            (collapseShapeAdjacentCutIndices shape shape.sum)) := by
      unfold paperSum
      rw [← hledger]
      ring

/-- The contracted valid-word marginal sums to the exact contracted-tree
`paperSum`, including its full factorial ledger. -/
theorem sum_contractedShapeMarginalWeight_eq_paperSum
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (M : ℕ) (shape : List ℕ)
    (hs : 1 ≤ shape.length - 1) :
    (∑ w : ContractedShapeValidWord mu r M shape hs,
        contractedShapeMarginalWeight
          mu z r lstar M shape hs w) =
      paperSum
        (M := M - shape.sum + shape.length)
        (leafMultiplicity
          (contractMultiplicities mu r (shape.length - 1) hs))
        (primitiveSeparatedChainWeight
          (contractEmbedding z r lstar)) := by
  have hledger :=
    factorialLedger_rename (contractCollapsedAlphabetEquiv r)
      (markerMultiplicity shape.length
        (outsideMultiplicity (splitLeafMultiplicity mu r)))
  rw [fixedShapeContractedMultiplicity_eq mu r shape hs] at hledger
  unfold contractedShapeMarginalWeight
  calc
    (∑ w : ContractedShapeValidWord mu r M shape hs,
        (∏ x : Unit ⊕ OutsideLeaf r,
            ((markerMultiplicity shape.length
              (outsideMultiplicity
                (splitLeafMultiplicity mu r)) x).factorial : ℝ)) *
          primitiveSeparatedChainWeight
            (contractEmbedding z r lstar) w.1) =
        (∏ x : Unit ⊕ OutsideLeaf r,
            ((markerMultiplicity shape.length
              (outsideMultiplicity
                (splitLeafMultiplicity mu r)) x).factorial : ℝ)) *
          ∑ w : ContractedShapeValidWord mu r M shape hs,
            primitiveSeparatedChainWeight
              (contractEmbedding z r lstar) w.1 := by
      rw [Finset.mul_sum]
    _ = (∏ x : Unit ⊕ OutsideLeaf r,
            ((markerMultiplicity shape.length
              (outsideMultiplicity
                (splitLeafMultiplicity mu r)) x).factorial : ℝ)) *
        wordSum
          (leafMultiplicity
            (contractMultiplicities mu r (shape.length - 1) hs))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) := by
      rw [sum_validWordSubtype_eq_wordSum]
    _ = paperSum
        (M := M - shape.sum + shape.length)
        (leafMultiplicity
          (contractMultiplicities mu r (shape.length - 1) hs))
        (primitiveSeparatedChainWeight
          (contractEmbedding z r lstar)) := by
      unfold paperSum
      rw [← hledger]

/-! ## Concrete fixed-shape Fubini bound -/

/-- The exact valid-word Fubini step for the two factorized marginals.  Both
target types are attached to `validWords`; no sum over all words appears. -/
theorem sum_specShape_shapeWeights_le_validMarginalProduct
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (M : ℕ) (shape : List ℕ)
    (hs : 1 ≤ shape.length - 1) :
    (∑ d : SpecFixedRawCollapseShapeData mu r M shape,
        collapseInsideShapeWeight
            mu z r shape d.1.1.insideList *
          collapseContractedShapeWeight
            mu z r lstar shape d.1.1.collapsed) ≤
      (∑ w : RestrictedShapeValidWord mu r shape,
          restrictedShapeMarginalWeight mu z r shape w) *
        ∑ w : ContractedShapeValidWord mu r M shape hs,
          contractedShapeMarginalWeight
            mu z r lstar M shape hs w := by
  have hfubini :=
    sum_comp_mul_le_sum_mul_sum_of_pair_injective
      (specShapeRestrictedValidWord :
        SpecFixedRawCollapseShapeData mu r M shape →
          RestrictedShapeValidWord mu r shape)
      (specShapeContractedValidWord hs :
        SpecFixedRawCollapseShapeData mu r M shape →
          ContractedShapeValidWord mu r M shape hs)
      (specShapeValidWordPair_injective hs)
      (restrictedShapeMarginalWeight mu z r shape)
      (contractedShapeMarginalWeight
        mu z r lstar M shape hs)
      (restrictedShapeMarginalWeight_nonneg mu z r shape)
      (contractedShapeMarginalWeight_nonneg
        mu z r lstar M shape hs)
  calc
    (∑ d : SpecFixedRawCollapseShapeData mu r M shape,
        collapseInsideShapeWeight
            mu z r shape d.1.1.insideList *
          collapseContractedShapeWeight
            mu z r lstar shape d.1.1.collapsed) =
        ∑ d : SpecFixedRawCollapseShapeData mu r M shape,
          restrictedShapeMarginalWeight mu z r shape
              (specShapeRestrictedValidWord d) *
            contractedShapeMarginalWeight
              mu z r lstar M shape hs
                (specShapeContractedValidWord hs d) := by
      apply Fintype.sum_congr
      intro d
      rw [collapseInsideShapeWeight_eq_restrictedMarginal,
        collapseContractedShapeWeight_eq_contractedMarginal]
    _ ≤
        (∑ w : RestrictedShapeValidWord mu r shape,
          restrictedShapeMarginalWeight mu z r shape w) *
        ∑ w : ContractedShapeValidWord mu r M shape hs,
          contractedShapeMarginalWeight
            mu z r lstar M shape hs w :=
      hfubini

/-- Concrete P-5.9 fixed-shape Fubini bound: the raw fixed-word majorant is
bounded by exactly the two paper sums, with the inverse marker factorial and
`4^n` allocated once. -/
theorem sum_specShape_collapseRawFixedWordSummand_le_paperSums
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (M : ℕ) (shape : List ℕ)
    (hs : 1 ≤ shape.length - 1) :
    (∑ d : SpecFixedRawCollapseShapeData mu r M shape,
        collapseRawFixedWordSummand mu r z lstar d.1.1) ≤
      ((shape.length.factorial : ℝ)⁻¹ *
          (4 : ℝ) ^ shape.sum *
          paperSum
            (leafMultiplicity (restrictMultiplicities mu r))
            (singleScaleChainWeight (restrictEmbedding z r)
              (collapseShapeAdjacentCutIndices shape shape.sum))) *
        paperSum (M := M - shape.sum + shape.length)
          (leafMultiplicity
            (contractMultiplicities mu r (shape.length - 1) hs))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) := by
  calc
    (∑ d : SpecFixedRawCollapseShapeData mu r M shape,
        collapseRawFixedWordSummand mu r z lstar d.1.1) ≤
        ∑ d : SpecFixedRawCollapseShapeData mu r M shape,
          collapseInsideShapeWeight
              mu z r shape d.1.1.insideList *
            collapseContractedShapeWeight
              mu z r lstar shape d.1.1.collapsed := by
      apply Finset.sum_le_sum
      intro d _
      exact collapseRawFixedWordSummand_le_shapeWeights
        mu z r lstar d.1.1 shape d.2.2
    _ ≤
        (∑ w : RestrictedShapeValidWord mu r shape,
          restrictedShapeMarginalWeight mu z r shape w) *
        ∑ w : ContractedShapeValidWord mu r M shape hs,
          contractedShapeMarginalWeight
            mu z r lstar M shape hs w :=
      sum_specShape_shapeWeights_le_validMarginalProduct
        mu z r lstar M shape hs
    _ = ((shape.length.factorial : ℝ)⁻¹ *
          (4 : ℝ) ^ shape.sum *
          paperSum
            (leafMultiplicity (restrictMultiplicities mu r))
            (singleScaleChainWeight (restrictEmbedding z r)
              (collapseShapeAdjacentCutIndices shape shape.sum))) *
        paperSum (M := M - shape.sum + shape.length)
          (leafMultiplicity
            (contractMultiplicities mu r (shape.length - 1) hs))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) := by
      rw [sum_restrictedShapeMarginalWeight_eq_paperSum,
        sum_contractedShapeMarginalWeight_eq_paperSum]

/-- A subtype sum over the spec+shape source is the corresponding filtered
sum over fixed-length raw data. -/
theorem sum_specFixedRawCollapseShapeData_eq_filter
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (M : ℕ) (shape : List ℕ)
    (F : FixedRawCollapseData
      (InsideLeaf r) (OutsideLeaf r) M → ℝ) :
    (∑ d : SpecFixedRawCollapseShapeData mu r M shape, F d.1) =
      ∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData
            (InsideLeaf r) (OutsideLeaf r) M =>
          CollapseMultiplicitySpec
              (splitLeafMultiplicity mu r) d.1 ∧
            d.1.collapseShape = shape),
        F d := by
  classical
  apply Finset.sum_bij (fun d _hd => d.1) <;> simp

/-- Filtered fixed-length form of the concrete valid-word Fubini bound. -/
theorem sum_filter_specShape_collapseRawFixedWordSummand_le_paperSums
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (M : ℕ) (shape : List ℕ)
    (hs : 1 ≤ shape.length - 1) :
    (∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData
            (InsideLeaf r) (OutsideLeaf r) M =>
          CollapseMultiplicitySpec
              (splitLeafMultiplicity mu r) d.1 ∧
            d.1.collapseShape = shape),
        collapseRawFixedWordSummand mu r z lstar d.1) ≤
      ((shape.length.factorial : ℝ)⁻¹ *
          (4 : ℝ) ^ shape.sum *
          paperSum
            (leafMultiplicity (restrictMultiplicities mu r))
            (singleScaleChainWeight (restrictEmbedding z r)
              (collapseShapeAdjacentCutIndices shape shape.sum))) *
        paperSum (M := M - shape.sum + shape.length)
          (leafMultiplicity
            (contractMultiplicities mu r (shape.length - 1) hs))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) := by
  rw [← sum_specFixedRawCollapseShapeData_eq_filter
    mu r M shape
    (fun d =>
      collapseRawFixedWordSummand mu r z lstar d.1)]
  exact sum_specShape_collapseRawFixedWordSummand_le_paperSums
    mu z r lstar M shape hs

/-! ## Witness-facing transport -/

/-- Shape cut sets at propositionally equal lengths are heterogeneously
equal. -/
theorem collapseShapeAdjacentCutIndices_heq
    (shape : List ℕ) {n m : ℕ} (h : n = m) :
    HEq (collapseShapeAdjacentCutIndices shape n)
      (collapseShapeAdjacentCutIndices shape m) := by
  subst m
  rfl

/-- A single-scale `paperSum` is unchanged when its word length and cut set
are transported together. -/
theorem paperSum_singleScale_eq_of_length_and_cuts
    {t : PlaneTree} {n m : ℕ}
    (mult : HeppLeaf t → ℕ)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (O₁ : Finset (AdjacentIndex n))
    (O₂ : Finset (AdjacentIndex m))
    (hlength : n = m) (hcuts : HEq O₁ O₂) :
    paperSum (M := n) mult (singleScaleChainWeight z O₁) =
      paperSum (M := m) mult (singleScaleChainWeight z O₂) := by
  subst m
  have hcuts' : O₁ = O₂ := eq_of_heq hcuts
  subst O₂
  rfl

/-- A primitive-separated `paperSum` is unchanged when both its word length
and prescribed multiplicity are transported. -/
theorem paperSum_primitiveSeparated_eq_of_length_and_multiplicity
    {t : PlaneTree} {n m : ℕ}
    {mult₁ mult₂ : HeppLeaf t → ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hlength : n = m) (hmult : mult₁ = mult₂) :
    paperSum (M := n) mult₁ (primitiveSeparatedChainWeight z) =
      paperSum (M := m) mult₂ (primitiveSeparatedChainWeight z) := by
  subst m
  subst mult₂
  rfl

/-- The proof argument in `contractMultiplicities` is irrelevant when the
cut counts are propositionally equal. -/
theorem contractMultiplicities_eq_of_cutCount_eq
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    {s₁ s₂ : ℕ} (h : s₁ = s₂)
    (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) :
    contractMultiplicities mu r s₁ hs₁ =
      contractMultiplicities mu r s₂ hs₂ := by
  subst s₂
  rfl

/-- Witness-facing form of the fixed-shape bound.  Its right side has
exactly the product consumed by `collapse_analytic_product...`: the
witness's actual cut set, cut count, and collapsed length. -/
theorem sum_filter_witnessShape_collapseRawFixedWordSummand_le_paperSums
    {t : PlaneTree} (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (M : ℕ)
    (d₀ : FixedRawCollapseData
      (InsideLeaf r) (OutsideLeaf r) M)
    (_hSpec₀ : CollapseMultiplicitySpec
      (splitLeafMultiplicity mu r) d₀.1)
    (hblocks : 2 ≤ d₀.1.blocks.length) :
    (∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData
            (InsideLeaf r) (OutsideLeaf r) M =>
          CollapseMultiplicitySpec
              (splitLeafMultiplicity mu r) d.1 ∧
            d.1.collapseShape = d₀.1.collapseShape),
        collapseRawFixedWordSummand mu r z lstar d.1) ≤
      (4 : ℝ) ^ d₀.1.insideLength *
        (((collapseCutCount d₀.1 + 1).factorial : ℝ)⁻¹) *
        paperSum (M := d₀.1.insideLength)
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight
            (restrictEmbedding z r) d₀.1.adjacentCutIndices) *
        paperSum (M := d₀.1.collapsed.length)
          (leafMultiplicity
            (contractMultiplicities mu r
              (collapseCutCount d₀.1)
              (one_le_collapseCutCount d₀.1 hblocks)))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) := by
  let shape := d₀.1.collapseShape
  have hsWitness :=
    one_le_collapseCutCount d₀.1 hblocks
  have hcutsCount :
      shape.length - 1 = collapseCutCount d₀.1 := by
    unfold shape collapseCutCount
    rw [d₀.1.collapseShape_length]
  have hsShape : 1 ≤ shape.length - 1 := by
    rw [hcutsCount]
    exact hsWitness
  have hbase :=
    sum_filter_specShape_collapseRawFixedWordSummand_le_paperSums
      mu z r lstar M shape hsShape
  have hinsideLength :
      shape.sum = d₀.1.insideLength := by
    exact d₀.1.collapseShape_sum
  have hshapeCuts :
      HEq (collapseShapeAdjacentCutIndices shape shape.sum)
        d₀.1.adjacentCutIndices := by
    have htransport :=
      collapseShapeAdjacentCutIndices_heq shape hinsideLength
    have hdatum :=
      d₀.1.adjacentCutIndices_eq_shape shape rfl
    exact htransport.trans (heq_of_eq hdatum.symm)
  have hinsidePaper :=
    paperSum_singleScale_eq_of_length_and_cuts
      (leafMultiplicity (restrictMultiplicities mu r))
      (restrictEmbedding z r)
      (collapseShapeAdjacentCutIndices shape shape.sum)
      d₀.1.adjacentCutIndices hinsideLength hshapeCuts
  let ds : FixedRawCollapseShapeData
      (InsideLeaf r) (OutsideLeaf r) M shape :=
    ⟨d₀, rfl⟩
  have hcollapsedLength :
      M - shape.sum + shape.length =
        d₀.1.collapsed.length := by
    exact (fixedShape_collapsedLength ds).symm
  have hcontractMultiplicity :
      leafMultiplicity
          (contractMultiplicities mu r
            (shape.length - 1) hsShape) =
        leafMultiplicity
          (contractMultiplicities mu r
            (collapseCutCount d₀.1) hsWitness) := by
    exact congrArg leafMultiplicity
      (contractMultiplicities_eq_of_cutCount_eq
        mu r hcutsCount hsShape hsWitness)
  have hcontractPaper :=
    paperSum_primitiveSeparated_eq_of_length_and_multiplicity
      (contractEmbedding z r lstar)
      hcollapsedLength hcontractMultiplicity
  have hmarkerCount :
      shape.length = collapseCutCount d₀.1 + 1 := by
    calc
      shape.length = d₀.1.blocks.length :=
        d₀.1.collapseShape_length
      _ = collapseCutCount d₀.1 + 1 :=
        (collapseCutCount_add_one d₀.1 hblocks).symm
  calc
    (∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData
            (InsideLeaf r) (OutsideLeaf r) M =>
          CollapseMultiplicitySpec
              (splitLeafMultiplicity mu r) d.1 ∧
            d.1.collapseShape = d₀.1.collapseShape),
        collapseRawFixedWordSummand mu r z lstar d.1) ≤
        ((shape.length.factorial : ℝ)⁻¹ *
            (4 : ℝ) ^ shape.sum *
            paperSum
              (leafMultiplicity (restrictMultiplicities mu r))
              (singleScaleChainWeight (restrictEmbedding z r)
                (collapseShapeAdjacentCutIndices shape shape.sum))) *
          paperSum (M := M - shape.sum + shape.length)
            (leafMultiplicity
              (contractMultiplicities mu r
                (shape.length - 1) hsShape))
            (primitiveSeparatedChainWeight
              (contractEmbedding z r lstar)) := hbase
    _ = (4 : ℝ) ^ d₀.1.insideLength *
        (((collapseCutCount d₀.1 + 1).factorial : ℝ)⁻¹) *
        paperSum (M := d₀.1.insideLength)
          (leafMultiplicity (restrictMultiplicities mu r))
          (singleScaleChainWeight
            (restrictEmbedding z r) d₀.1.adjacentCutIndices) *
        paperSum (M := d₀.1.collapsed.length)
          (leafMultiplicity
            (contractMultiplicities mu r
              (collapseCutCount d₀.1) hsWitness))
          (primitiveSeparatedChainWeight
            (contractEmbedding z r lstar)) := by
      rw [hinsidePaper, hcontractPaper,
        hinsideLength, hmarkerCount]
      ring

end

end Anderson4D
