import Anderson4D.PermSum.CollapseSum

/-!
# Finite Fubini bounds for collapse coordinates

The P-5.9 collapse sum must be separated into an inside-word sum and a
collapsed-word sum without paying for the number of original words.  The
mechanism is an injective map into a product, applied separately on every
fixed block-composition shape.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

/-! ## A generic injective finite Fubini bound -/

/-- An injectively indexed subfamily of a nonnegative product sum is bounded
by the full product of the two marginal sums. -/
theorem sum_comp_mul_le_sum_mul_sum_of_pair_injective
    {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
    (f : I → X) (g : I → Y)
    (hpair : Function.Injective fun i => (f i, g i))
    (a : X → ℝ) (b : Y → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y) :
    (∑ i : I, a (f i) * b (g i)) ≤
      (∑ x : X, a x) * ∑ y : Y, b y := by
  classical
  let e : I ↪ X × Y :=
    ⟨fun i => (f i, g i), hpair⟩
  calc
    (∑ i : I, a (f i) * b (g i)) =
        ∑ p ∈ Finset.univ.map e, a p.1 * b p.2 := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ p : X × Y, a p.1 * b p.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro p _hp _hnot
        exact mul_nonneg (ha p.1) (hb p.2)
    _ = ∑ x : X, ∑ y : Y, a x * b y := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : X, a x * (∑ y : Y, b y) := by
      apply Fintype.sum_congr
      intro x
      rw [Finset.mul_sum]
    _ = (∑ x : X, a x) * ∑ y : Y, b y := by
      rw [Finset.sum_mul]

/-! ## Fixed-shape collapse coordinates -/

variable {A B : Type*}

namespace RawCollapseData

/-- The ordered positive block lengths of a raw collapse datum. -/
def collapseShape (d : RawCollapseData A B) : List ℕ :=
  d.blocks.map List.length

@[simp] theorem collapseShape_length (d : RawCollapseData A B) :
    d.collapseShape.length = d.blocks.length := by
  simp [collapseShape]

@[simp] theorem collapseShape_sum (d : RawCollapseData A B) :
    d.collapseShape.sum = d.insideLength := by
  simp [collapseShape, RawCollapseData.insideLength,
    RawCollapseData.insideList]

/-- At fixed shape, the flattened inside word and collapsed word determine
the complete raw datum. -/
theorem eq_of_shape_insideList_collapsed
    (d e : RawCollapseData A B)
    (hshape : d.collapseShape = e.collapseShape)
    (hinside : d.insideList = e.insideList)
    (hcollapsed : d.collapsed = e.collapsed) :
    d = e := by
  apply (rawCollapseCoordinatesEquiv A B).injective
  apply CollapseCoordinates.ext
  · exact hinside
  · exact hshape
  · exact hcollapsed

end RawCollapseData

/-- Fixed-original-length raw data in one block-composition shape fiber. -/
abbrev FixedRawCollapseShapeData
    (A B : Type*) (n : ℕ) (shape : List ℕ) :=
  { d : FixedRawCollapseData A B n //
    d.1.collapseShape = shape }

/-- Coordinate pair on a fixed shape fiber, still in list form. -/
def fixedShapeListPair
    {n : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B n shape) :
    List A × List (Unit ⊕ B) :=
  (d.1.1.insideList, d.1.1.collapsed)

/-- No collapse datum multiplicity remains inside a fixed shape fiber. -/
theorem fixedShapeListPair_injective
    {n : ℕ} {shape : List ℕ} :
    Function.Injective
      (fixedShapeListPair :
        FixedRawCollapseShapeData A B n shape →
          List A × List (Unit ⊕ B)) := by
  intro d e h
  apply Subtype.ext
  apply Subtype.ext
  apply RawCollapseData.eq_of_shape_insideList_collapsed d.1.1 e.1.1
  · exact d.2.trans e.2.symm
  · exact congrArg
      (fun p : List A × List (Unit ⊕ B) => p.1) h
  · exact congrArg
      (fun p : List A × List (Unit ⊕ B) => p.2) h

/-- The common inside-word length in a fixed shape fiber. -/
theorem fixedShape_insideLength
    {n : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B n shape) :
    d.1.1.insideLength = shape.sum := by
  rw [← RawCollapseData.collapseShape_sum d.1.1, d.2]

/-- The common collapsed-word length in a fixed shape fiber. -/
theorem fixedShape_collapsedLength
    {n : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B n shape) :
    d.1.1.collapsed.length =
      n - shape.sum + shape.length := by
  rw [RawCollapseData.collapsed_length_fixed d.1,
    fixedShape_insideLength d,
    ← RawCollapseData.collapseShape_length d.1.1, d.2]

/-- The inside list regarded as a finite word on the shape-determined
carrier. -/
def fixedShapeInsideWord
    {n : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B n shape) :
    Fin shape.sum → A :=
  List.Vector.get
    ⟨d.1.1.insideList, by
      exact fixedShape_insideLength d⟩

/-- The collapsed list regarded as a finite word on its shape-determined
carrier. -/
def fixedShapeCollapsedWord
    {n : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B n shape) :
    Fin (n - shape.sum + shape.length) → Unit ⊕ B :=
  List.Vector.get
    ⟨d.1.1.collapsed, fixedShape_collapsedLength d⟩

@[simp] theorem ofFn_fixedShapeInsideWord
    {n : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B n shape) :
    List.ofFn (fixedShapeInsideWord d) = d.1.1.insideList := by
  let v : List.Vector A shape.sum :=
    ⟨d.1.1.insideList, fixedShape_insideLength d⟩
  change List.ofFn (List.Vector.get v) = d.1.1.insideList
  calc
    List.ofFn (List.Vector.get v) =
        List.Vector.toList
          (List.Vector.ofFn (List.Vector.get v)) :=
      (List.Vector.toList_ofFn _).symm
    _ = List.Vector.toList v :=
      congrArg List.Vector.toList (List.Vector.ofFn_get v)
    _ = d.1.1.insideList := rfl

@[simp] theorem ofFn_fixedShapeCollapsedWord
    {n : ℕ} {shape : List ℕ}
    (d : FixedRawCollapseShapeData A B n shape) :
    List.ofFn (fixedShapeCollapsedWord d) = d.1.1.collapsed := by
  let v : List.Vector (Unit ⊕ B)
      (n - shape.sum + shape.length) :=
    ⟨d.1.1.collapsed, fixedShape_collapsedLength d⟩
  change List.ofFn (List.Vector.get v) = d.1.1.collapsed
  calc
    List.ofFn (List.Vector.get v) =
        List.Vector.toList
          (List.Vector.ofFn (List.Vector.get v)) :=
      (List.Vector.toList_ofFn _).symm
    _ = List.Vector.toList v :=
      congrArg List.Vector.toList (List.Vector.ofFn_get v)
    _ = d.1.1.collapsed := rfl

/-- The pair of finite words is injective on a fixed shape fiber. -/
theorem fixedShapeWordPair_injective
    {n : ℕ} {shape : List ℕ} :
    Function.Injective fun
      d : FixedRawCollapseShapeData A B n shape =>
        (fixedShapeInsideWord d, fixedShapeCollapsedWord d) := by
  intro d e h
  apply fixedShapeListPair_injective
  apply Prod.ext
  · change d.1.1.insideList = e.1.1.insideList
    rw [← ofFn_fixedShapeInsideWord d,
      ← ofFn_fixedShapeInsideWord e]
    exact congrArg List.ofFn (congrArg Prod.fst h)
  · change d.1.1.collapsed = e.1.1.collapsed
    rw [← ofFn_fixedShapeCollapsedWord d,
      ← ofFn_fixedShapeCollapsedWord e]
    exact congrArg List.ofFn (congrArg Prod.snd h)

/-! ## Fubini bounds on one shape fiber -/

/-- A subtype sum over one shape is the corresponding filtered sum over all
fixed-length raw data. -/
theorem sum_fixedRawCollapseShapeData_eq_filter
    [Fintype A] [Fintype B]
    {n : ℕ} {shape : List ℕ}
    (F : FixedRawCollapseData A B n → ℝ) :
    (∑ d : FixedRawCollapseShapeData A B n shape, F d.1) =
      ∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData A B n =>
          d.1.collapseShape = shape),
        F d := by
  classical
  apply Finset.sum_bij (fun d _hd => d.1) <;> simp

/-- Finite-word form of the fixed-shape Fubini bound. -/
theorem sum_fixedShape_wordWeights_le_product
    [Fintype A] [Fintype B]
    {n : ℕ} {shape : List ℕ}
    (F₁ : (Fin shape.sum → A) → ℝ)
    (F₂ :
      (Fin (n - shape.sum + shape.length) → Unit ⊕ B) → ℝ)
    (hF₁ : ∀ w, 0 ≤ F₁ w) (hF₂ : ∀ w, 0 ≤ F₂ w) :
    (∑ d : FixedRawCollapseShapeData A B n shape,
        F₁ (fixedShapeInsideWord d) *
          F₂ (fixedShapeCollapsedWord d)) ≤
      (∑ w₁ : Fin shape.sum → A, F₁ w₁) *
        ∑ w₂ : Fin (n - shape.sum + shape.length) → Unit ⊕ B,
          F₂ w₂ := by
  classical
  exact
    sum_comp_mul_le_sum_mul_sum_of_pair_injective
      fixedShapeInsideWord fixedShapeCollapsedWord
      fixedShapeWordPair_injective F₁ F₂ hF₁ hF₂

/-- List-weight form consumed by collapse estimates.  The right side uses
the two independent finite-word carriers of the shape-determined lengths. -/
theorem sum_fixedShape_listWeights_le_product
    [Fintype A] [Fintype B]
    {n : ℕ} {shape : List ℕ}
    (F₁ : List A → ℝ) (F₂ : List (Unit ⊕ B) → ℝ)
    (hF₁ : ∀ l, 0 ≤ F₁ l) (hF₂ : ∀ l, 0 ≤ F₂ l) :
    (∑ d : FixedRawCollapseShapeData A B n shape,
        F₁ d.1.1.insideList * F₂ d.1.1.collapsed) ≤
      (∑ w₁ : Fin shape.sum → A, F₁ (List.ofFn w₁)) *
        ∑ w₂ : Fin (n - shape.sum + shape.length) → Unit ⊕ B,
          F₂ (List.ofFn w₂) := by
  simpa only [ofFn_fixedShapeInsideWord,
    ofFn_fixedShapeCollapsedWord] using
    sum_fixedShape_wordWeights_le_product
      (n := n) (shape := shape)
      (fun w => F₁ (List.ofFn w))
      (fun w => F₂ (List.ofFn w))
      (fun w => hF₁ (List.ofFn w))
      (fun w => hF₂ (List.ofFn w))

/-- Filtered-data form used immediately after the exact collapse change of
variables.  No cardinality of the shape fiber appears. -/
theorem sum_fixedRaw_filter_shape_listWeights_le_product
    [Fintype A] [Fintype B]
    {n : ℕ} {shape : List ℕ}
    (F₁ : List A → ℝ) (F₂ : List (Unit ⊕ B) → ℝ)
    (hF₁ : ∀ l, 0 ≤ F₁ l) (hF₂ : ∀ l, 0 ≤ F₂ l) :
    (∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData A B n =>
          d.1.collapseShape = shape),
        F₁ d.1.insideList * F₂ d.1.collapsed) ≤
      (∑ w₁ : Fin shape.sum → A, F₁ (List.ofFn w₁)) *
        ∑ w₂ : Fin (n - shape.sum + shape.length) → Unit ⊕ B,
          F₂ (List.ofFn w₂) := by
  rw [← sum_fixedRawCollapseShapeData_eq_filter
    (n := n) (shape := shape)
    (fun d => F₁ d.1.insideList * F₂ d.1.collapsed)]
  exact sum_fixedShape_listWeights_le_product F₁ F₂ hF₁ hF₂

end

end Anderson4D
