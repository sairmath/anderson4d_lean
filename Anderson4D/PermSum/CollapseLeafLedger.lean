import Anderson4D.PermSum.CollapseData

/-!
# Simple/compound leaf-factor ledger under collapse

The leaf factors in (5.45) split over the inside and outside leaf carriers.
The contracted tree contributes the same outside factors plus exactly one
new compound-marker factor `((s+1)!)^(3/4)`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Unified version of the paper's simple/compound leaf factor. -/
def paperLeafFactor {t : PlaneTree}
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (l : HeppLeaf t) : ℝ :=
  if l.1 ∈ compound then
    factorialThreeQuarters (leafMultiplicity mu l)
  else
    sqrtFactorial (leafMultiplicity mu l)

/-- Product of all unified leaf factors. -/
def paperLeafProduct {t : PlaneTree}
    (mu : Multiplicities t) (compound : Finset (VPos t)) : ℝ :=
  ∏ l : HeppLeaf t, paperLeafFactor mu compound l

/-- The unified product is exactly the two leaf products printed in
(5.33)/(5.39). -/
theorem paperLeafProduct_eq_simple_mul_compound
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    paperLeafProduct mu compound =
      (∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l)) *
      ∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l) := by
  rw [show paperLeafProduct mu compound =
      ∏ l ∈ Leaves t,
        if l ∈ compound then factorialThreeQuarters (mu.m l)
        else sqrtFactorial (mu.m l) by
    unfold paperLeafProduct
    simpa [paperLeafFactor, leafMultiplicity] using
      (Finset.prod_coe_sort
        (s := Leaves t)
        (f := fun l : VPos t =>
          if l ∈ compound then factorialThreeQuarters (mu.m l)
          else sqrtFactorial (mu.m l)))]
  rw [← simple_union_compound t compound,
    Finset.prod_union (disjoint_simple_compound t compound)]
  congr 1
  · apply Finset.prod_congr rfl
    intro l hl
    have hlc : l ∉ compound :=
      (Finset.mem_sdiff.mp hl).2
    simp [hlc]
  · apply Finset.prod_congr rfl
    intro l hl
    have hlc : l ∈ compound :=
      (Finset.mem_inter.mp hl).2
    simp [hlc]

/-- Product of original factors over inside leaves. -/
def insidePaperLeafProduct {t : PlaneTree}
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) : ℝ :=
  ∏ l : InsideLeaf r, paperLeafFactor mu compound l.1

/-- Product of original factors over outside leaves. -/
def outsidePaperLeafProduct {t : PlaneTree}
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (r : VPos t) : ℝ :=
  ∏ l : OutsideLeaf r, paperLeafFactor mu compound l.1

/-- Original leaf factors split exactly into inside and outside products. -/
theorem paperLeafProduct_eq_inside_mul_outside
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t) :
    paperLeafProduct mu compound =
      insidePaperLeafProduct mu compound r *
        outsidePaperLeafProduct mu compound r := by
  let e := leafInsideOutsideEquiv r
  let f : InsideLeaf r ⊕ OutsideLeaf r → ℝ :=
    Sum.elim
      (fun l : InsideLeaf r => paperLeafFactor mu compound l.1)
      (fun l : OutsideLeaf r => paperLeafFactor mu compound l.1)
  calc
    paperLeafProduct mu compound =
        ∏ l : HeppLeaf t, f (e l) := by
      unfold paperLeafProduct
      apply Fintype.prod_congr
      intro l
      by_cases h : r.1 <+: l.1.1
      · simp [e, f, leafInsideOutsideEquiv, h]
      · simp [e, f, leafInsideOutsideEquiv, h]
    _ = ∏ x : InsideLeaf r ⊕ OutsideLeaf r, f x :=
      Equiv.prod_comp e f
    _ = insidePaperLeafProduct mu compound r *
        outsidePaperLeafProduct mu compound r := by
      rw [Fintype.prod_sum_type]
      rfl

/-- Restriction preserves the unified factor of each inside leaf. -/
theorem paperLeafFactor_restrict
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (l : HeppLeaf (subtreeAt t r.1)) :
    paperLeafFactor (restrictMultiplicities mu r)
        (restrictCompound r compound) l =
      paperLeafFactor mu compound (restrictLeafEquiv r l).1 := by
  unfold paperLeafFactor
  have hmem :
      l.1 ∈ restrictCompound r compound ↔
        (restrictLeafEquiv r l).1.1 ∈ compound := by
    rw [mem_restrictCompound]
    rfl
  have hmult :
      leafMultiplicity (restrictMultiplicities mu r) l =
        leafMultiplicity mu (restrictLeafEquiv r l).1 := by
    rfl
  by_cases h : l.1 ∈ restrictCompound r compound
  · rw [if_pos h, if_pos (hmem.mp h), hmult]
  · rw [if_neg h, if_neg (fun hc => h (hmem.mpr hc)), hmult]

/-- The restricted tree's leaf product is exactly the original inside
product. -/
theorem paperLeafProduct_restrict
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t) :
    paperLeafProduct (restrictMultiplicities mu r)
        (restrictCompound r compound) =
      insidePaperLeafProduct mu compound r := by
  calc
    paperLeafProduct (restrictMultiplicities mu r)
          (restrictCompound r compound) =
        ∏ l : HeppLeaf (subtreeAt t r.1),
          paperLeafFactor mu compound (restrictLeafEquiv r l).1 := by
      unfold paperLeafProduct
      apply Fintype.prod_congr
      exact paperLeafFactor_restrict mu compound r
    _ = insidePaperLeafProduct mu compound r :=
      Equiv.prod_comp (restrictLeafEquiv r)
        (fun l : InsideLeaf r => paperLeafFactor mu compound l.1)

/-- The contracted marker contributes exactly its compound factor. -/
@[simp] theorem paperLeafFactor_contract_marker
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (s : ℕ) (hs : 1 ≤ s) :
    paperLeafFactor (contractMultiplicities mu r s hs)
        (contractCompound r compound) (contractMarkerLeaf r) =
      factorialThreeQuarters (s + 1) := by
  unfold paperLeafFactor
  rw [if_pos]
  · rw [contractMultiplicities_marker]
  · exact contractMarker_mem_contractCompound r compound

/-- Every contracted outside leaf retains its original leaf factor. -/
@[simp] theorem paperLeafFactor_contract_outside
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (s : ℕ) (hs : 1 ≤ s) (l : OutsideLeaf r) :
    paperLeafFactor (contractMultiplicities mu r s hs)
        (contractCompound r compound) (contractOutsideLeaf r l) =
      paperLeafFactor mu compound l.1 := by
  unfold paperLeafFactor
  by_cases h : l.1.1 ∈ compound
  · have hc :
        (contractOutsideLeaf r l).1 ∈
          contractCompound r compound :=
      (contractOutsideLeaf_mem_contractCompound_iff r compound l).mpr h
    rw [if_pos h, if_pos hc, contractMultiplicities_outside]
  · have hc :
        (contractOutsideLeaf r l).1 ∉
          contractCompound r compound := by
      intro hc
      exact h
        ((contractOutsideLeaf_mem_contractCompound_iff
          r compound l).mp hc)
    rw [if_neg h, if_neg hc, contractMultiplicities_outside]

/-- Contracted leaf product = marker factor × original outside product. -/
theorem paperLeafProduct_contract
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (s : ℕ) (hs : 1 ≤ s) :
    paperLeafProduct (contractMultiplicities mu r s hs)
        (contractCompound r compound) =
      factorialThreeQuarters (s + 1) *
        outsidePaperLeafProduct mu compound r := by
  let e := contractLeafSumEquiv r
  let f : Unit ⊕ OutsideLeaf r → ℝ :=
    Sum.elim
      (fun _ : Unit => factorialThreeQuarters (s + 1))
      (fun l : OutsideLeaf r => paperLeafFactor mu compound l.1)
  calc
    paperLeafProduct (contractMultiplicities mu r s hs)
          (contractCompound r compound) =
        ∏ l : HeppLeaf (contractAt t r.1), f (e l) := by
      unfold paperLeafProduct
      apply Fintype.prod_congr
      intro l
      cases h : e l with
      | inl u =>
          cases u
          have hl : l = contractMarkerLeaf r := by
            apply e.injective
            rw [h, contractLeafSumEquiv_marker]
          subst l
          exact paperLeafFactor_contract_marker mu compound r s hs
      | inr lout =>
          have hl : l = contractOutsideLeaf r lout := by
            apply e.injective
            rw [h, contractLeafSumEquiv_contractOutsideLeaf]
          subst l
          exact paperLeafFactor_contract_outside
            mu compound r s hs lout
    _ = ∏ x : Unit ⊕ OutsideLeaf r, f x :=
      Equiv.prod_comp e f
    _ = factorialThreeQuarters (s + 1) *
        outsidePaperLeafProduct mu compound r := by
      rw [Fintype.prod_sum_type]
      simp [f, outsidePaperLeafProduct]

/-- Complete leaf-factor ledger used in (5.45). -/
theorem paperLeafProduct_restrict_mul_contract
    {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (r : VPos t)
    (s : ℕ) (hs : 1 ≤ s) :
    paperLeafProduct (restrictMultiplicities mu r)
          (restrictCompound r compound) *
        paperLeafProduct (contractMultiplicities mu r s hs)
          (contractCompound r compound) =
      paperLeafProduct mu compound *
        factorialThreeQuarters (s + 1) := by
  rw [paperLeafProduct_restrict, paperLeafProduct_contract,
    paperLeafProduct_eq_inside_mul_outside]
  ring

end

end Anderson4D
