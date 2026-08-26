import Anderson4D.PermSum.CollapseRawSum
import Anderson4D.PermSum.CollapseShapeLedger

/-!
# Active collapse shapes

The primitive-word condition excludes raw collapse data with fewer than two
inside blocks.  This module records that exclusion at the level of the outer
shape ledger and removes the corresponding zero fibers from the exact
fixed-word sum.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

set_option warningAsError true
set_option autoImplicit false

noncomputable section

variable {A B : Type*}

namespace RawCollapseData

/-- A raw collapse datum satisfying the multiplicity specification expands
to a valid word with those multiplicities. -/
theorem expandedWord_mem_validWords_of_collapseMultiplicitySpec
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (d : RawCollapseData A B)
    (hSpec : CollapseMultiplicitySpec mult d) :
    d.expandedWord ∈ validWords mult := by
  let e :=
    finWordRawCollapseEquiv A B d.expandedLength
  let dFixed : FixedRawCollapseData A B d.expandedLength :=
    ⟨d, rfl⟩
  have hword : e.symm dFixed = d.expandedWord := by
    apply List.ofFn_injective
    simp only [e, dFixed, ofFn_finWordRawCollapseEquiv_symm,
      ofFn_expandedWord]
  rw [← hword]
  apply
    (mem_validWords_iff_finWordRawCollapseSpec
      mult (e.symm dFixed)).mpr
  simpa only [e, dFixed, Equiv.apply_symm_apply] using hSpec

/-- In the tree split, positive leaf multiplicities and primitivity force at
least two maximal inside blocks. -/
theorem two_le_blocks_of_splitSpec_of_noProperLeafBlock
    {t : PlaneTree}
    (_ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (r : VPos t)
    (hr : r ∈ nonrootBranches t)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (hSpec :
      CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d)
    (hprimitive : NoProperLeafBlock d.expandedWord) :
    2 ≤ d.blocks.length := by
  letI : Nonempty (InsideLeaf r) :=
    nonempty_insideLeaf r
  letI : Nonempty (OutsideLeaf r) :=
    nonempty_outsideLeaf_of_ne_root r
      (Finset.mem_erase.mp hr).1 hroot
  have hvalid :
      d.expandedWord ∈
        validWords (splitLeafMultiplicity mu r) :=
    d.expandedWord_mem_validWords_of_collapseMultiplicitySpec
      (splitLeafMultiplicity mu r) hSpec
  have hpos :
      ∀ x : InsideLeaf r ⊕ OutsideLeaf r,
        0 < splitLeafMultiplicity mu r x := by
    intro x
    cases x with
    | inl l =>
        rw [splitLeafMultiplicity_inl]
        exact lt_of_lt_of_le (by omega) (mu.two_le l.1.1 l.1.2)
    | inr l =>
        rw [splitLeafMultiplicity_inr]
        exact lt_of_lt_of_le (by omega) (mu.two_le l.1.1 l.1.2)
  exact
    d.two_le_blocks_of_noProperLeafBlock_of_mem_validWords_of_pos
      (splitLeafMultiplicity mu r) hprimitive hvalid hpos

end RawCollapseData

/-! ## Active shape family -/

/-- Occurring split-alphabet shapes with at least two blocks. -/
def activeCollapseShapes {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (M : ℕ) :
    Finset (List ℕ) :=
  (validCollapseShapes (splitLeafMultiplicity mu r) M).filter
    fun shape => 2 ≤ shape.length

@[simp]
theorem mem_activeCollapseShapes_iff {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t) (M : ℕ)
    (shape : List ℕ) :
    shape ∈ activeCollapseShapes mu r M ↔
      shape ∈ validCollapseShapes
        (splitLeafMultiplicity mu r) M ∧
      2 ≤ shape.length := by
  simp [activeCollapseShapes]

/-! ## Vanishing of inactive shape fibers -/

/-- A fixed-word summand whose collapse shape has fewer than two blocks
vanishes. -/
theorem collapseRawFixedWordSummand_eq_zero_of_shape_length_lt_two
    {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (r : VPos t)
    (hr : r ∈ nonrootBranches t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r))
    (shape : List ℕ)
    (hshape : d.collapseShape = shape)
    (hsmall : shape.length < 2) :
    collapseRawFixedWordSummand mu r z lstar d = 0 := by
  by_cases hactive :
      CollapseMultiplicitySpec (splitLeafMultiplicity mu r) d ∧
        NoProperLeafBlock d.expandedWord ∧
        NoAdjacentEqual d.expandedWord
  · have htwo :
        2 ≤ d.blocks.length :=
      d.two_le_blocks_of_splitSpec_of_noProperLeafBlock
        ht hroot mu r hr hactive.1 hactive.2.1
    have hlt : d.blocks.length < 2 := by
      rw [← d.collapseShape_length, hshape]
      exact hsmall
    omega
  · simp [collapseRawFixedWordSummand, hactive]

/-! ## Exact active-shape decomposition -/

/-- The raw fixed-word total is exactly the sum over occurring shapes with at
least two blocks; all other shape fibers vanish by primitivity. -/
theorem sum_collapseRawFixedWordSummand_eq_sum_activeShapes
    {t : PlaneTree} {M : ℕ}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (r : VPos t)
    (hr : r ∈ nonrootBranches t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (lstar : InsideLeaf r) :
    (∑ d : FixedRawCollapseData
        (InsideLeaf r) (OutsideLeaf r) M,
      collapseRawFixedWordSummand mu r z lstar d.1) =
      ∑ shape ∈ activeCollapseShapes mu r M,
        ∑ d ∈
          (specFixedRawCollapseData
            (splitLeafMultiplicity mu r) M).filter
              (fun d => d.1.collapseShape = shape),
          collapseRawFixedWordSummand mu r z lstar d.1 := by
  calc
    (∑ d : FixedRawCollapseData
        (InsideLeaf r) (OutsideLeaf r) M,
      collapseRawFixedWordSummand mu r z lstar d.1) =
        ∑ d : FixedRawCollapseData
            (InsideLeaf r) (OutsideLeaf r) M,
          if CollapseMultiplicitySpec
              (splitLeafMultiplicity mu r) d.1 then
            collapseRawFixedWordSummand mu r z lstar d.1
          else
            0 := by
      apply Fintype.sum_congr
      intro d
      by_cases hSpec :
          CollapseMultiplicitySpec
            (splitLeafMultiplicity mu r) d.1 <;>
        simp [collapseRawFixedWordSummand, hSpec]
    _ =
        ∑ shape ∈ validCollapseShapes
            (splitLeafMultiplicity mu r) M,
          ∑ d ∈
            (specFixedRawCollapseData
              (splitLeafMultiplicity mu r) M).filter
                (fun d => d.1.collapseShape = shape),
            collapseRawFixedWordSummand mu r z lstar d.1 := by
      exact
        sum_ite_collapseMultiplicitySpec_eq_sum_shapes
          (splitLeafMultiplicity mu r) M
          (fun d =>
            collapseRawFixedWordSummand mu r z lstar d.1)
    _ =
        ∑ shape ∈ activeCollapseShapes mu r M,
          ∑ d ∈
            (specFixedRawCollapseData
              (splitLeafMultiplicity mu r) M).filter
                (fun d => d.1.collapseShape = shape),
            collapseRawFixedWordSummand mu r z lstar d.1 := by
      unfold activeCollapseShapes
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro shape hvalid hnotactive
      have hsmall : shape.length < 2 := by
        have hnotlength : ¬2 ≤ shape.length := by
          intro hlength
          apply hnotactive
          exact Finset.mem_filter.mpr ⟨hvalid, hlength⟩
        omega
      apply Finset.sum_eq_zero
      intro d hd
      have hshape : d.1.collapseShape = shape :=
        (Finset.mem_filter.mp hd).2
      exact
        collapseRawFixedWordSummand_eq_zero_of_shape_length_lt_two
          ht hroot mu r hr z lstar d.1 shape hshape hsmall

end

end Anderson4D
