import Anderson4D.HeppTree.AutomorphismGeometry
import Anderson4D.HeppTree.ValidParent
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric summation along marked ancestor chains

Marks strictly increase toward the root and are powers of two.  Consequently
the ratios of a fixed branch scale to the scales of its strict ancestors form
a subseries of `1/2 + 1/4 + …`.  This is the geometric input in paper
(5.27), used to keep the six-step volume iteration exponentially bounded.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

/-- Strict branching ancestors of `v`, represented by path prefixes. -/
noncomputable def strictBranchAncestors {t : PlaneTree} (v : VPos t) :
    Finset (VPos t) :=
  (BranchNodes t).filter fun a => a.1 <+: v.1 ∧ a ≠ v

@[simp]
theorem mem_strictBranchAncestors {t : PlaneTree} {v a : VPos t} :
    a ∈ strictBranchAncestors v ↔
      a ∈ BranchNodes t ∧ a.1 <+: v.1 ∧ a ≠ v := by
  simp [strictBranchAncestors]

/-- Number of tree edges from an ancestor `a` down to `v`. -/
def ancestorGap {t : PlaneTree} (v a : VPos t) : ℕ :=
  v.1.length - a.1.length

theorem ancestorGap_pos {t : PlaneTree} {v a : VPos t}
    (ha : a.1 <+: v.1) (hne : a ≠ v) :
    0 < ancestorGap v a := by
  have hle := List.IsPrefix.length_le ha
  have hlt : a.1.length < v.1.length := by
    apply lt_of_le_of_ne hle
    intro heq
    apply hne
    apply Subtype.ext
    have hatake := List.prefix_iff_eq_take.mp ha
    calc
      a.1 = v.1.take a.1.length := hatake
      _ = v.1 := by simp [heq]
  exact Nat.sub_pos_of_lt hlt

/-- Along a valid marked tree, the exponent gain from a branch to any
branching ancestor is at least their depth gap. -/
theorem marking_add_ancestorGap_le
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t)
    {a v : VPos t} (hav : IsAncestor a v)
    (hv : v ∈ BranchNodes t) :
    Nm.Nexp v + ancestorGap v a ≤ Nm.Nexp a := by
  have aux :
      ∀ {u : VPos t} (huv : IsAncestor u v),
        u ∈ BranchNodes t ∧
          Nm.Nexp v + ancestorGap v u ≤ Nm.Nexp u := by
    intro u huv
    induction huv using Relation.ReflTransGen.head_induction_on with
    | refl =>
        exact ⟨hv, by simp [ancestorGap]⟩
    | @head x y hxy hyv ih =>
        have hyBranch : y ∈ BranchNodes t := ih.1
        have hchild : y ∈ childrenOf x := by
          rw [childrenOf_eq_graphChildren]
          exact hxy
        have hlen : y.1.length = x.1.length + 1 :=
          (mem_childrenOf.mp hchild).1
        have hxParent : parentV y = x :=
          (mem_graphChildren.mp hxy).1
        have hyneRoot : y ≠ rootV t := by
          intro hyroot
          subst y
          apply (mem_graphChildren.mp hxy).2
          simpa using hxParent
        have hxBranch : x ∈ BranchNodes t := by
          rw [← hxParent]
          exact parentV_mem_BranchNodes_of_isValid ht hyneRoot
        have hmark : Nm.Nexp y + 1 ≤ Nm.Nexp x := by
          have hgt := Nm.parent_gt y hyBranch hyneRoot
          rw [hxParent] at hgt
          omega
        have hxprefix : x.1 <+: v.1 :=
          (mem_childrenOf.mp hchild).2.trans (IsAncestor.prefix hyv)
        have hxle : x.1.length ≤ v.1.length :=
          List.IsPrefix.length_le hxprefix
        have hyle : y.1.length ≤ v.1.length :=
          List.IsPrefix.length_le (IsAncestor.prefix hyv)
        refine ⟨hxBranch, ?_⟩
        unfold ancestorGap at ih ⊢
        omega
  exact (aux hav).2

/-- Dyadic scale form of `marking_add_ancestorGap_le`. -/
theorem scaleN_mul_two_pow_ancestorGap_le
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t)
    {a v : VPos t} (hav : IsAncestor a v)
    (hv : v ∈ BranchNodes t) :
    scaleN Nm v * 2 ^ ancestorGap v a ≤ scaleN Nm a := by
  rw [scaleN, scaleN, ← pow_add]
  exact Nat.pow_le_pow_right (by omega)
    (marking_add_ancestorGap_le ht Nm hav hv)

/-- Each ancestor-scale ratio is bounded by the corresponding power of
`1/2`. -/
theorem scaleN_div_scaleN_le_half_pow_ancestorGap
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t)
    {a v : VPos t} (hav : IsAncestor a v)
    (hv : v ∈ BranchNodes t) :
    (scaleN Nm v : ℝ) / scaleN Nm a
      ≤ ((1 : ℝ) / 2) ^ ancestorGap v a := by
  have hnat :=
    scaleN_mul_two_pow_ancestorGap_le ht Nm hav hv
  have hleft : (0 : ℝ) < scaleN Nm a := by
    exact_mod_cast scaleN_pos Nm a
  have hright : (0 : ℝ) < (2 : ℕ) ^ ancestorGap v a := by positivity
  rw [one_div, inv_pow, ← one_div]
  rw [div_le_div_iff₀ hleft (by exact_mod_cast hright)]
  norm_num
  exact_mod_cast hnat

private theorem ancestorIndex_injective
    {t : PlaneTree} (v : VPos t) :
    Set.InjOn (fun a : VPos t => ancestorGap v a - 1)
      (strictBranchAncestors v) := by
  intro a ha b hb hab
  change a ∈ strictBranchAncestors v at ha
  change b ∈ strictBranchAncestors v at hb
  rw [mem_strictBranchAncestors] at ha hb
  have hapos := ancestorGap_pos ha.2.1 ha.2.2
  have hbpos := ancestorGap_pos hb.2.1 hb.2.2
  change ancestorGap v a - 1 = ancestorGap v b - 1 at hab
  have hgap : ancestorGap v a = ancestorGap v b := by omega
  have halen : a.1.length = b.1.length := by
    unfold ancestorGap at hgap
    have hale := List.IsPrefix.length_le ha.2.1
    have hble := List.IsPrefix.length_le hb.2.1
    omega
  apply Subtype.ext
  have hatake := List.prefix_iff_eq_take.mp ha.2.1
  have hbtake := List.prefix_iff_eq_take.mp hb.2.1
  rw [hatake, hbtake, halen]

private theorem ancestorIndex_image_subset_range
    {t : PlaneTree} (v : VPos t) :
    (strictBranchAncestors v).image
        (fun a : VPos t => ancestorGap v a - 1)
      ⊆ Finset.range v.1.length := by
  intro k hk
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
  rw [mem_strictBranchAncestors] at ha
  have hpos := ancestorGap_pos ha.2.1 ha.2.2
  have hle := List.IsPrefix.length_le ha.2.1
  rw [Finset.mem_range]
  unfold ancestorGap at hpos ⊢
  omega

/-- **Paper (5.27), one-branch geometric chain.**  The sum of the ratio of
one branch scale to all of its strict branching-ancestor scales is at most
one. -/
theorem sum_scaleN_div_ancestor_le_one
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t)
    {v : VPos t} (hv : v ∈ BranchNodes t) :
    ∑ a ∈ strictBranchAncestors v,
        (scaleN Nm v : ℝ) / scaleN Nm a ≤ 1 := by
  let idx : VPos t → ℕ := fun a => ancestorGap v a - 1
  have hpoint :
      ∀ a ∈ strictBranchAncestors v,
        (scaleN Nm v : ℝ) / scaleN Nm a
          ≤ ((1 : ℝ) / 2) ^ (idx a + 1) := by
    intro a ha
    rw [mem_strictBranchAncestors] at ha
    have hpos := ancestorGap_pos ha.2.1 ha.2.2
    have hratio :=
      scaleN_div_scaleN_le_half_pow_ancestorGap ht Nm
        (isAncestor_of_prefix a v ha.2.1) hv
    simpa [idx, Nat.sub_add_cancel hpos] using hratio
  calc
    ∑ a ∈ strictBranchAncestors v,
        (scaleN Nm v : ℝ) / scaleN Nm a
        ≤ ∑ a ∈ strictBranchAncestors v,
            ((1 : ℝ) / 2) ^ (idx a + 1) :=
      Finset.sum_le_sum fun a ha => hpoint a ha
    _ = ∑ k ∈ (strictBranchAncestors v).image idx,
          ((1 : ℝ) / 2) ^ (k + 1) := by
      rw [Finset.sum_image (ancestorIndex_injective v)]
    _ ≤ ∑ k ∈ Finset.range v.1.length,
          ((1 : ℝ) / 2) ^ (k + 1) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (ancestorIndex_image_subset_range v)
        (fun _ _ _ => by positivity)
    _ = ((1 : ℝ) / 2) *
          ∑ k ∈ Finset.range v.1.length, ((1 : ℝ) / 2) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_succ, mul_comm]
    _ ≤ ((1 : ℝ) / 2) * 2 := by
      gcongr
      exact sum_geometric_two_le v.1.length
    _ = 1 := by norm_num

/-- **Paper (5.27), reordered double-sum form.**  Weighting each branch by
its number of children and then summing its scale ratio over all strict
ancestors costs at most the sum of the child counts. -/
theorem sum_childCount_mul_ancestor_ratio_le
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t) :
    ∑ v ∈ BranchNodes t,
        (childCount t v.1 : ℝ) *
          ∑ a ∈ strictBranchAncestors v,
            (scaleN Nm v : ℝ) / scaleN Nm a
      ≤ ∑ v ∈ BranchNodes t, (childCount t v.1 : ℝ) := by
  apply Finset.sum_le_sum
  intro v hv
  have hinner := sum_scaleN_div_ancestor_le_one ht Nm hv
  exact mul_le_of_le_one_right
    (by exact_mod_cast (Nat.zero_le (childCount t v.1))) hinner

end Anderson4D
