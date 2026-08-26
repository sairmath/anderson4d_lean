import Anderson4D.PermSum.CollapseAlphabet
import Anderson4D.PermSum.CollapseCompositionCount
import Anderson4D.PermSum.CollapseFubini

/-!
# Shape ledger for the P-5.9 collapse sum

For a prescribed multiplicity, every valid raw collapse datum has the same
inside-word length.  Its ordered block lengths therefore form a positive
composition of one fixed integer.  This file enumerates only the shapes that
actually occur and splits the finite raw-data sum exactly into their fibers.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

variable {A B : Type*}

namespace RawCollapseData

/-- Every entry of the collapse shape is positive. -/
theorem collapseShape_pos (d : RawCollapseData A B)
    {k : ℕ} (hk : k ∈ d.collapseShape) :
    0 < k := by
  obtain ⟨block, hblock, rfl⟩ := List.mem_map.1 hk
  exact List.length_pos_iff.2 (d.2.1 block hblock)

/-- The multiplicity specification fixes the inside length. -/
theorem insideLength_eq_sum_insideMultiplicity
    [Fintype A] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {d : RawCollapseData A B}
    (h : CollapseMultiplicitySpec mult d) :
    d.insideLength = ∑ a : A, insideMultiplicity mult a :=
  (d.sum_insideMultiplicity_eq_insideLength h).symm

/-- A valid raw datum supplies a positive composition of the fixed total
inside multiplicity. -/
def collapseCompositionOfSpec
    [Fintype A] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (d : RawCollapseData A B)
    (h : CollapseMultiplicitySpec mult d) :
    Composition (∑ a : A, insideMultiplicity mult a) where
  blocks := d.collapseShape
  blocks_pos := d.collapseShape_pos
  blocks_sum := by
    rw [d.collapseShape_sum,
      d.insideLength_eq_sum_insideMultiplicity h]

/-- Positive inside total forces the shape to be nonempty. -/
theorem collapseShape_ne_nil_of_spec
    [Fintype A] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {d : RawCollapseData A B}
    (h : CollapseMultiplicitySpec mult d)
    (hpos : 0 < ∑ a : A, insideMultiplicity mult a) :
    d.collapseShape ≠ [] := by
  intro hnil
  have hsum := (d.collapseCompositionOfSpec mult h).blocks_sum
  change d.collapseShape.sum =
    ∑ a : A, insideMultiplicity mult a at hsum
  rw [hnil] at hsum
  simp at hsum
  omega

end RawCollapseData

/-! ## Tree-facing fixed-length statement -/

open PlaneTree

/-- The inside part of the split multiplicity has exactly the total
multiplicity of the restricted subtree. -/
theorem sum_insideMultiplicity_splitLeafMultiplicity
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t) :
    (∑ l : InsideLeaf r,
        insideMultiplicity (splitLeafMultiplicity mu r) l) =
      totalMultiplicity (restrictMultiplicities mu r) := by
  rw [totalMultiplicity_restrictMultiplicities]
  unfold insideMultiplicityTotal
  apply Fintype.sum_congr
  intro l
  rfl

/-- For the canonical inside/outside split, the valid inside length is
exactly the total multiplicity of the restricted subtree. -/
theorem RawCollapseData.insideLength_eq_totalMultiplicity_restrict
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (h : CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d) :
    d.insideLength =
      totalMultiplicity (restrictMultiplicities mu r) := by
  rw [d.insideLength_eq_sum_insideMultiplicity h]
  exact sum_insideMultiplicity_splitLeafMultiplicity mu r

/-- In the tree-facing situation the selected inside subtree has positive
total multiplicity, so every valid collapse shape is nonempty. -/
theorem RawCollapseData.collapseShape_ne_nil_of_splitSpec
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (h : CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d) :
    d.collapseShape ≠ [] := by
  apply d.collapseShape_ne_nil_of_spec h
  rw [sum_insideMultiplicity_splitLeafMultiplicity]
  have hcard :
      1 ≤ Fintype.card (HeppLeaf (subtreeAt t r.1)) := by
    rw [Fintype.card_coe, card_Leaves_eq_leafCount]
    obtain ⟨children⟩ := subtreeAt t r.1
    exact le_max_left 1 (leafCountList children)
  have htwo :
      2 ≤ totalMultiplicity (restrictMultiplicities mu r) := by
    calc
      2 ≤ 2 * Fintype.card
          (HeppLeaf (subtreeAt t r.1)) := by omega
      _ = ∑ _l : HeppLeaf (subtreeAt t r.1), 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ l : HeppLeaf (subtreeAt t r.1),
          leafMultiplicity (restrictMultiplicities mu r) l := by
        exact Finset.sum_le_sum fun l _ =>
          (restrictMultiplicities mu r).two_le l.1 l.2
      _ = totalMultiplicity (restrictMultiplicities mu r) := rfl
  omega

/-! ## The finite family of occurring shapes -/

/-- Fixed-length raw data satisfying the prescribed multiplicity. -/
def specFixedRawCollapseData
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) :
    Finset (FixedRawCollapseData A B n) :=
  Finset.univ.filter fun d => CollapseMultiplicitySpec mult d.1

@[simp] theorem mem_specFixedRawCollapseData_iff
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ)
    (d : FixedRawCollapseData A B n) :
    d ∈ specFixedRawCollapseData mult n ↔
      CollapseMultiplicitySpec mult d.1 := by
  simp [specFixedRawCollapseData]

/-- Only shapes that are realized by a valid fixed-length raw datum. -/
def validCollapseShapes
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) :
    Finset (List ℕ) :=
  (specFixedRawCollapseData mult n).image
    fun d => d.1.collapseShape

theorem mem_validCollapseShapes_iff
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) (shape : List ℕ) :
    shape ∈ validCollapseShapes mult n ↔
      ∃ d : FixedRawCollapseData A B n,
        CollapseMultiplicitySpec mult d.1 ∧
          d.1.collapseShape = shape := by
  simp [validCollapseShapes, specFixedRawCollapseData]

/-- Every entry of an occurring shape is positive. -/
theorem validCollapseShape_pos
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) {shape : List ℕ}
    (hshape : shape ∈ validCollapseShapes mult n)
    {k : ℕ} (hk : k ∈ shape) :
    0 < k := by
  obtain ⟨d, _hspec, hdshape⟩ :=
    (mem_validCollapseShapes_iff mult n shape).mp hshape
  apply d.1.collapseShape_pos
  rwa [hdshape]

/-- Every occurring shape sums to the one fixed inside total. -/
theorem validCollapseShape_sum
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) {shape : List ℕ}
    (hshape : shape ∈ validCollapseShapes mult n) :
    shape.sum = ∑ a : A, insideMultiplicity mult a := by
  obtain ⟨d, hspec, hdshape⟩ :=
    (mem_validCollapseShapes_iff mult n shape).mp hshape
  rw [← hdshape, d.1.collapseShape_sum,
    d.1.insideLength_eq_sum_insideMultiplicity hspec]

/-- If the fixed inside total is positive, every occurring shape is
nonempty. -/
theorem validCollapseShape_ne_nil
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ)
    (hpos : 0 < ∑ a : A, insideMultiplicity mult a)
    {shape : List ℕ}
    (hshape : shape ∈ validCollapseShapes mult n) :
    shape ≠ [] := by
  intro hnil
  have hsum := validCollapseShape_sum mult n hshape
  rw [hnil] at hsum
  simp at hsum
  omega

/-- An occurring shape, packaged as a genuine mathlib composition of the
fixed inside total. -/
def validCollapseShapeComposition
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ)
    (shape : ↥(validCollapseShapes mult n)) :
    Composition (∑ a : A, insideMultiplicity mult a) where
  blocks := shape.1
  blocks_pos := validCollapseShape_pos mult n shape.2
  blocks_sum := validCollapseShape_sum mult n shape.2

/-- Different occurring shape lists give different compositions. -/
theorem validCollapseShapeComposition_injective
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) :
    Function.Injective (validCollapseShapeComposition mult n) := by
  intro shape₁ shape₂ h
  apply Subtype.ext
  exact congrArg Composition.blocks h

/-- The occurring shape family costs at most the coarse paper factor
`2^(inside total)`. -/
theorem card_validCollapseShapes_le_two_pow
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) :
    (validCollapseShapes mult n).card ≤
      2 ^ (∑ a : A, insideMultiplicity mult a) := by
  calc
    (validCollapseShapes mult n).card =
        Fintype.card ↥(validCollapseShapes mult n) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
        (Composition (∑ a : A, insideMultiplicity mult a)) :=
      Fintype.card_le_of_injective
        (validCollapseShapeComposition mult n)
        (validCollapseShapeComposition_injective mult n)
    _ ≤ 2 ^ (∑ a : A, insideMultiplicity mult a) :=
      card_composition_le_two_pow _

/-- Tree-facing count: the shape loss is controlled by the restricted
inside multiplicity, exactly the `n` used in the collapse step. -/
theorem card_validCollapseShapes_split_le_two_pow_restrict
    {t : PlaneTree} (mu : Multiplicities t) (r : VPos t)
    (originalLength : ℕ) :
    (validCollapseShapes
        (splitLeafMultiplicity mu r) originalLength).card ≤
      2 ^ totalMultiplicity (restrictMultiplicities mu r) := by
  rw [← sum_insideMultiplicity_splitLeafMultiplicity mu r]
  exact card_validCollapseShapes_le_two_pow
    (splitLeafMultiplicity mu r) originalLength

/-! ## Exact outer shape decomposition -/

/-- Any finite sum splits exactly into the fibers of a key map. -/
theorem sum_eq_sum_image_fibers
    {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M]
    (s : Finset ι) (key : ι → κ) (F : ι → M) :
    (∑ x ∈ s, F x) =
      ∑ y ∈ s.image key,
        ∑ x ∈ s.filter (fun x => key x = y), F x := by
  classical
  symm
  calc
    (∑ y ∈ s.image key,
        ∑ x ∈ s.filter (fun x => key x = y), F x) =
        ∑ y ∈ s.image key,
          ∑ x ∈ s, if key x = y then F x else 0 := by
      simp_rw [Finset.sum_filter]
    _ = ∑ x ∈ s,
        ∑ y ∈ s.image key,
          if key x = y then F x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ s, F x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_image.mpr ⟨x, hx, rfl⟩]

/-- The valid fixed-length raw-data sum splits exactly by occurring shape. -/
theorem sum_specFixedRawCollapseData_eq_sum_shapes
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {M : Type*} [AddCommMonoid M]
    (mult : A ⊕ B → ℕ) (n : ℕ)
    (F : FixedRawCollapseData A B n → M) :
    (∑ d ∈ specFixedRawCollapseData mult n, F d) =
      ∑ shape ∈ validCollapseShapes mult n,
        ∑ d ∈ (specFixedRawCollapseData mult n).filter
          (fun d => d.1.collapseShape = shape),
          F d := by
  exact sum_eq_sum_image_fibers
    (specFixedRawCollapseData mult n)
    (fun d => d.1.collapseShape) F

/-- `if spec then ... else 0`, exactly as produced by `CollapseSum`, in
outer-shape/fiber form. -/
theorem sum_ite_collapseMultiplicitySpec_eq_sum_shapes
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {M : Type*} [AddCommMonoid M]
    (mult : A ⊕ B → ℕ) (n : ℕ)
    (F : FixedRawCollapseData A B n → M) :
    (∑ d : FixedRawCollapseData A B n,
        if CollapseMultiplicitySpec mult d.1 then F d else 0) =
      ∑ shape ∈ validCollapseShapes mult n,
        ∑ d ∈ (specFixedRawCollapseData mult n).filter
          (fun d => d.1.collapseShape = shape),
          F d := by
  rw [← sum_specFixedRawCollapseData_eq_sum_shapes mult n F]
  simp [specFixedRawCollapseData, Finset.sum_filter]

/-- A valid-spec shape fiber is a subset of the unrestricted shape fiber
used by `CollapseFubini`. -/
theorem spec_shape_fiber_subset_shape_fiber
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) (shape : List ℕ) :
    (specFixedRawCollapseData mult n).filter
        (fun d => d.1.collapseShape = shape) ⊆
      Finset.univ.filter
        (fun d : FixedRawCollapseData A B n =>
          d.1.collapseShape = shape) := by
  intro d hd
  simp only [Finset.mem_filter] at hd ⊢
  exact ⟨Finset.mem_univ d, hd.2⟩

/-- Nonnegative valid-spec fiber sums are bounded by the unrestricted fiber
to which the Fubini lemma applies. -/
theorem sum_spec_shape_fiber_le_sum_shape_fiber
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (n : ℕ) (shape : List ℕ)
    (F : FixedRawCollapseData A B n → ℝ)
    (hF : ∀ d, 0 ≤ F d) :
    (∑ d ∈ (specFixedRawCollapseData mult n).filter
        (fun d => d.1.collapseShape = shape), F d) ≤
      ∑ d ∈ Finset.univ.filter
        (fun d : FixedRawCollapseData A B n =>
          d.1.collapseShape = shape),
        F d := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (spec_shape_fiber_subset_shape_fiber mult n shape)
    (fun d _hd _hnot => hF d)

end

end Anderson4D
