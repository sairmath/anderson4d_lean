import Anderson4D.PermSum.Statements
import Anderson4D.HeppTree.BranchExcess
import Anderson4D.HeppTree.ClusterDiameter
import Anderson4D.HeppTree.LeafCard
import Anderson4D.PermSum.SingleScaleInner

/-!
# Single-scale proof setup

This file implements Steps 1--2 of the proof of Proposition 5.10:
the power count (5.68) and the finite dyadic classification (5.74)--(5.75).
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Step 1: the exact excess identity (5.68) -/

private theorem leafChildren_eq_parentFiber {t : PlaneTree}
    (hroot : rootV t ∈ BranchNodes t) (v : VPos t) :
    leafChildren v =
      (Leaves t).filter (fun l => parentV l = v) := by
  ext l
  simp only [leafChildren, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨hlv, hl⟩
    exact ⟨hl, (mem_childrenOf_iff_ne_root_and_parentV_eq.mp hlv).2⟩
  · rintro ⟨hl, hp⟩
    refine ⟨mem_childrenOf_iff_ne_root_and_parentV_eq.mpr ⟨?_, hp⟩, hl⟩
    intro h
    subst l
    have hzero := mem_Leaves_iff.mp hl
    have htwo := mem_BranchNodes_iff.mp hroot
    omega

private theorem sum_leafChild_excess {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) :
    (∑ v ∈ BranchNodes t,
        ∑ l ∈ leafChildren v, (mu.m l - 1)) =
      ∑ l ∈ Leaves t, (mu.m l - 1) := by
  have hmaps : ∀ l ∈ Leaves t, parentV l ∈ BranchNodes t := by
    intro l hl
    apply parentV_mem_BranchNodes_of_isValid ht
    intro h
    subst l
    have hzero := mem_Leaves_iff.mp hl
    have htwo := mem_BranchNodes_iff.mp hroot
    omega
  simpa only [leafChildren_eq_parentFiber hroot] using
    Finset.sum_fiberwise_of_maps_to hmaps (fun l => mu.m l - 1)

private theorem sum_leaf_excess_add_card {t : PlaneTree}
    (mu : Multiplicities t) :
    (∑ l ∈ Leaves t, (mu.m l - 1)) + (Leaves t).card =
      ∑ l ∈ Leaves t, mu.m l := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have hm := mu.two_le l hl
  omega

/-- Paper equation (5.68), with `m` unfolded as `totalMultiplicity`. -/
theorem sum_gammaInf_sub_one_eq_totalMultiplicity_sub_one
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t) (mu : Multiplicities t) :
    (∑ v ∈ BranchNodes t, (gammaInf mu v - 1)) =
      totalMultiplicity mu - 1 := by
  have hpoint : ∀ v ∈ BranchNodes t,
      gammaInf mu v - 1 =
        (childCount t v.1 - 1) +
          ∑ l ∈ leafChildren v, (mu.m l - 1) := by
    intro v hv
    have htwo := mem_BranchNodes_iff.mp hv
    rw [gammaInf, card_childrenOf]
    omega
  have htotal :
      (∑ l ∈ Leaves t, mu.m l) = totalMultiplicity mu := by
    change (∑ l ∈ Leaves t, mu.m l) =
      ∑ l : {v // v ∈ Leaves t}, mu.m l
    rw [← Finset.sum_attach]
    simp
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib,
    sum_branchNodes_childCount_sub_one_eq_branchExcess,
    sum_leafChild_excess ht hroot]
  have hbranch := branchExcess_add_one_eq_leafCount t ht
  have hleaf := sum_leaf_excess_add_card mu
  rw [card_Leaves_eq_leafCount, htotal] at hleaf
  omega

/-- Pointwise inequality used after (5.68) to absorb the exponential in
(5.69): `γ∞ ≤ 2(γ∞-1)` at every branch node. -/
theorem gammaInf_le_two_mul_sub_one {t : PlaneTree}
    (mu : Multiplicities t) {v : VPos t} (hv : v ∈ BranchNodes t) :
    gammaInf mu v ≤ 2 * (gammaInf mu v - 1) := by
  have htwo := mem_BranchNodes_iff.mp hv
  rw [gammaInf, card_childrenOf]
  omega

/-- Summed power-count consequence of (5.68), with the constant in (5.69)
made explicit. -/
theorem sum_gammaInf_le_two_mul_totalMultiplicity_sub_one
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t) (mu : Multiplicities t) :
    (∑ v ∈ BranchNodes t, gammaInf mu v) ≤
      2 * (totalMultiplicity mu - 1) := by
  calc
    (∑ v ∈ BranchNodes t, gammaInf mu v) ≤
        ∑ v ∈ BranchNodes t, 2 * (gammaInf mu v - 1) :=
      Finset.sum_le_sum fun v hv => gammaInf_le_two_mul_sub_one mu hv
    _ = 2 * (∑ v ∈ BranchNodes t, (gammaInf mu v - 1)) := by
      rw [Finset.mul_sum]
    _ = 2 * (totalMultiplicity mu - 1) := by
      rw [sum_gammaInf_sub_one_eq_totalMultiplicity_sub_one ht hroot]

/-! ### Corrected exponential cost in (5.69)

As recorded in `docs/PAPER_NOTES.md` (5.69), the inclusive ancestor sum contains
the self term.  Its uniform bound is `2`, not the displayed `1`; this leaves
the paper's final `C^m` estimate unchanged.
-/

def weakNonrootBranchAncestors {t : PlaneTree} (u : VPos t) :
    Finset (VPos t) :=
  (nonrootBranches t).filter fun n => n.1 <+: u.1

theorem sum_weakNonrootAncestor_ratios_le_two {t : PlaneTree}
    (ht : t.isValid = true) (Nm : HeppMarking t)
    {u : VPos t} (hu : u ∈ BranchNodes t) :
    (∑ n ∈ weakNonrootBranchAncestors u,
        (scaleN Nm u : ℝ) / scaleN Nm n) ≤ 2 := by
  have hsubset :
      weakNonrootBranchAncestors u ⊆ insert u (strictBranchAncestors u) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    by_cases hnu : n = u
    · exact Finset.mem_insert.mpr (Or.inl hnu)
    · exact Finset.mem_insert.mpr (Or.inr
        (mem_strictBranchAncestors.mpr
          ⟨(Finset.mem_erase.mp hn'.1).2, hn'.2, hnu⟩))
  calc
    (∑ n ∈ weakNonrootBranchAncestors u,
        (scaleN Nm u : ℝ) / scaleN Nm n) ≤
        ∑ n ∈ insert u (strictBranchAncestors u),
          (scaleN Nm u : ℝ) / scaleN Nm n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ => by positivity)
    _ = 1 + ∑ n ∈ strictBranchAncestors u,
          (scaleN Nm u : ℝ) / scaleN Nm n := by
            rw [Finset.sum_insert (by simp [strictBranchAncestors])]
            rw [div_self (by
              exact_mod_cast (scaleN_pos Nm u).ne')]
    _ ≤ 2 := by
      linarith [sum_scaleN_div_ancestor_le_one ht Nm hu]

/-- The exponent in the product-to-exponential step of (5.69), before
reordering the two finite sums. -/
def singleScaleExponentCost {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : ℝ :=
  ∑ n ∈ nonrootBranches t,
    ∑ u ∈ branchNodesUnder n,
      (gammaInf mu u : ℝ) * ((scaleN Nm u : ℝ) / scaleN Nm n)

/-- `singleScaleExponentCost` is exactly the sum of the normalized
accumulated scales occurring after `x ≤ exp x` in (5.69). -/
theorem sum_accumulatedScale_div_eq_exponentCost {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    (∑ n ∈ nonrootBranches t,
        (accumulatedScale Nm mu n : ℝ) / scaleN Nm n) =
      singleScaleExponentCost Nm mu := by
  rw [singleScaleExponentCost]
  apply Finset.sum_congr rfl
  intro n _
  rw [accumulatedScale]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem singleScaleExponentCost_eq_reordered {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    singleScaleExponentCost Nm mu =
      ∑ u ∈ BranchNodes t, (gammaInf mu u : ℝ) *
        ∑ n ∈ weakNonrootBranchAncestors u,
          (scaleN Nm u : ℝ) / scaleN Nm n := by
  simp only [singleScaleExponentCost, branchNodesUnder,
    weakNonrootBranchAncestors]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : n.1 <+: u.1 <;> simp [h]

/-- Quantitative core of the local constant adjustment in (5.69): the reordered
exponent costs at most twice `∑γ∞`. -/
theorem singleScaleExponentCost_le_two_sum_gammaInf {t : PlaneTree}
    (ht : t.isValid = true) (Nm : HeppMarking t)
    (mu : Multiplicities t) :
    singleScaleExponentCost Nm mu ≤
      2 * ∑ u ∈ BranchNodes t, (gammaInf mu u : ℝ) := by
  rw [singleScaleExponentCost_eq_reordered]
  calc
    (∑ u ∈ BranchNodes t, (gammaInf mu u : ℝ) *
        ∑ n ∈ weakNonrootBranchAncestors u,
          (scaleN Nm u : ℝ) / scaleN Nm n) ≤
        ∑ u ∈ BranchNodes t, (gammaInf mu u : ℝ) * 2 := by
          apply Finset.sum_le_sum
          intro u hu
          gcongr
          exact sum_weakNonrootAncestor_ratios_le_two ht Nm hu
    _ = 2 * ∑ u ∈ BranchNodes t, (gammaInf mu u : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring

/-- Combining the local (5.69) constant adjustment with (5.68) gives the explicit
exponent `4(m-1)`. -/
theorem singleScaleExponentCost_le_four_mul_total_sub_one {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    singleScaleExponentCost Nm mu ≤
      4 * ((totalMultiplicity mu - 1 : ℕ) : ℝ) := by
  calc
    singleScaleExponentCost Nm mu ≤
        2 * ∑ u ∈ BranchNodes t, (gammaInf mu u : ℝ) :=
      singleScaleExponentCost_le_two_sum_gammaInf ht Nm mu
    _ ≤ 2 * (2 * (totalMultiplicity mu - 1 : ℕ)) := by
      gcongr
      exact_mod_cast
        sum_gammaInf_le_two_mul_totalMultiplicity_sub_one ht hroot mu
    _ = 4 * ((totalMultiplicity mu - 1 : ℕ) : ℝ) := by ring

/-! ## Step 2: the `(N,X,Y,P)` classification (5.74) -/

private theorem ancestor_eq_of_leaf {t : PlaneTree} {v w : VPos t}
    (hv : v ∈ Leaves t) (hvw : IsAncestor v w) : v = w := by
  induction hvw using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head x y hxy _ _ =>
      have hy : y ∈ childrenOf x := by
        rw [childrenOf_eq_graphChildren]
        exact hxy
      have hpos : 0 < (childrenOf x).card :=
        Finset.card_pos.mpr ⟨y, hy⟩
      rw [card_childrenOf, mem_Leaves_iff.mp hv] at hpos
      omega

private theorem ancestor_parent_of_ne {t : PlaneTree} {a v : VPos t}
    (hav : IsAncestor a v) (hne : a ≠ v) :
    IsAncestor a (parentV v) := by
  apply isAncestor_of_prefix
  let s := List.drop a.1.length v.1
  have heq : a.1 ++ s = v.1 :=
    List.prefix_iff_eq_append.mp hav.prefix
  have hs : s ≠ [] := by
    intro hs
    apply hne
    apply Subtype.ext
    simpa [s, hs] using heq
  change a.1 <+: v.1.dropLast
  rw [← heq, List.dropLast_append_of_ne_nil hs]
  exact List.prefix_append _ _

private theorem parentScale_le_lcaScale {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) {l l' : HeppLeaf t} (hne : l ≠ l') :
    scaleN Nm (parentV l.1) ≤ scaleN Nm (lcaV l.1 l'.1) := by
  have hval : l.1 ≠ l'.1 := fun h => hne (Subtype.ext h)
  have hlcaNe : lcaV l.1 l'.1 ≠ l.1 := by
    intro h
    have ha : IsAncestor l.1 l'.1 := h ▸ lcaV_ancestor_right l.1 l'.1
    exact hval (ancestor_eq_of_leaf l.2 ha)
  have hlcaParent :=
    ancestor_parent_of_ne (lcaV_ancestor_left l.1 l'.1) hlcaNe
  have hlneRoot : l.1 ≠ rootV t := by
    intro h
    have hzero := mem_Leaves_iff.mp (h ▸ l.2)
    have htwo := mem_BranchNodes_iff.mp hroot
    omega
  have hpBranch :=
    parentV_mem_BranchNodes_of_isValid ht hlneRoot
  have hmark :=
    marking_add_ancestorGap_le ht Nm hlcaParent hpBranch
  unfold scaleN
  exact Nat.pow_le_pow_right (by omega) (Nat.le_of_add_right_le hmark)

/-- Paper (5.73): separation at the LCA scale implies separation at half the
larger of the two parent scales. -/
theorem parentScale_separation {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (z : HeppLeaf t → Fin 4 → ℤ)
    (hz : IsSeparatedEmbedding Nm z) {l l' : HeppLeaf t} (hne : l ≠ l') :
    ((max (scaleN Nm (parentV l.1)) (scaleN Nm (parentV l'.1)) : ℕ) : ℝ) / 2 ≤
      znorm (z l - z l') := by
  have hl := parentScale_le_lcaScale ht hroot Nm hne
  have hr := parentScale_le_lcaScale ht hroot Nm hne.symm
  have hmax :
      max (scaleN Nm (parentV l.1)) (scaleN Nm (parentV l'.1)) ≤
        scaleN Nm (lcaV l.1 l'.1) := by
    exact max_le hl (by simpa [lcaV_comm] using hr)
  have hcast :
      ((max (scaleN Nm (parentV l.1))
        (scaleN Nm (parentV l'.1)) : ℕ) : ℝ) ≤
          (scaleN Nm (lcaV l.1 l'.1) : ℝ) := by
    exact_mod_cast hmax
  exact (div_le_div_of_nonneg_right hcast (by norm_num)).trans
    (hz.2 l l' hne)

/-! ### The path correction in the power ledger (5.71) -/

/-- Branch children of `v` lying on the path to `l`. -/
def branchChildrenTowardLeaf {t : PlaneTree} (v : VPos t)
    (l : HeppLeaf t) : Finset (VPos t) :=
  (branchChildren v).filter fun c => c.1 <+: l.1.1

private theorem exists_child_toward_leaf {t : PlaneTree}
    {v : VPos t} {l : HeppLeaf t} (hvl : v.1 <+: l.1.1)
    (hne : v ≠ l.1) :
    ∃ c : VPos t, c ∈ childrenOf v ∧ c.1 <+: l.1.1 := by
  let q := l.1.1.drop v.1.length
  have hq : v.1 ++ q = l.1.1 :=
    List.prefix_iff_eq_append.mp hvl
  have hqne : q ≠ [] := by
    intro hnil
    apply hne
    apply Subtype.ext
    rw [hnil] at hq
    simpa using hq
  obtain ⟨i, q', hqform⟩ := List.exists_cons_of_ne_nil hqne
  rw [hqform] at hq
  have hcpos : IsPos t (v.1 ++ [i]) := by
    apply IsPos_of_prefix l.1.2
    rw [← hq]
    simp
  let c : VPos t := ⟨v.1 ++ [i], hcpos⟩
  refine ⟨c, ?_, ?_⟩
  · rw [mem_childrenOf]
    exact ⟨by simp [c], List.prefix_append _ _⟩
  · change v.1 ++ [i] <+: l.1.1
    rw [← hq]
    simp

private theorem child_eq_of_toward_same_leaf {t : PlaneTree}
    {v c d : VPos t} {l : HeppLeaf t}
    (hc : c ∈ childrenOf v) (hd : d ∈ childrenOf v)
    (hcl : c.1 <+: l.1.1) (hdl : d.1 <+: l.1.1) :
    c = d := by
  apply Subtype.ext
  have hlen : c.1.length = d.1.length := by
    rw [(mem_childrenOf.mp hc).1, (mem_childrenOf.mp hd).1]
  rw [List.prefix_iff_eq_take] at hcl hdl
  calc
    c.1 = l.1.1.take c.1.length := hcl
    _ = l.1.1.take d.1.length := by rw [hlen]
    _ = d.1 := hdl.symm

/-- The correction fiber in (5.71) has cardinality zero off the leaf path
and at its parent, and cardinality one at every earlier ancestor. -/
theorem card_branchChildrenTowardLeaf {t : PlaneTree}
    (ht : t.isValid = true) {v : VPos t} (hv : v ∈ BranchNodes t)
    (l : HeppLeaf t) :
    (branchChildrenTowardLeaf v l).card =
      if v.1 <+: l.1.1 then if v = parentV l.1 then 0 else 1 else 0 := by
  by_cases hvl : v.1 <+: l.1.1
  · by_cases hvp : v = parentV l.1
    · rw [if_pos hvl, if_pos hvp, Finset.card_eq_zero]
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hs
      obtain ⟨c, hc⟩ := hs
      have hc' := Finset.mem_filter.mp hc
      have hcChild := (Finset.mem_inter.mp hc'.1).1
      have hcBranch := (Finset.mem_inter.mp hc'.1).2
      have hlne : l.1 ≠ rootV t := by
        intro hl
        have hp : parentV l.1 = l.1 := by
          rw [hl, parentV_rootV]
        have hvlEq : v = l.1 := hvp.trans hp
        have hzero := mem_Leaves_iff.mp l.2
        have htwo := mem_BranchNodes_iff.mp hv
        rw [hvlEq] at htwo
        omega
      have hlChild : l.1 ∈ childrenOf v :=
        mem_childrenOf_iff_ne_root_and_parentV_eq.mpr ⟨hlne, hvp.symm⟩
      have hcl := child_eq_of_toward_same_leaf hcChild hlChild hc'.2
        List.prefix_rfl
      subst c
      have hzero := mem_Leaves_iff.mp l.2
      have htwo := mem_BranchNodes_iff.mp hcBranch
      omega
    · rw [if_pos hvl, if_neg hvp]
      have hvlne : v ≠ l.1 := by
        intro h
        subst v
        have hzero := mem_Leaves_iff.mp l.2
        have htwo := mem_BranchNodes_iff.mp hv
        omega
      obtain ⟨c, hcChild, hcl⟩ :=
        exists_child_toward_leaf hvl hvlne
      have hclne : c ≠ l.1 := by
        intro h
        subst c
        exact hvp (mem_childrenOf_iff_ne_root_and_parentV_eq.mp hcChild).2.symm
      obtain ⟨d, hdChild, _⟩ :=
        exists_child_toward_leaf hcl hclne
      have hdneRoot : d ≠ rootV t :=
        (mem_childrenOf_iff_ne_root_and_parentV_eq.mp hdChild).1
      have hcBranch : c ∈ BranchNodes t := by
        rw [← (mem_childrenOf_iff_ne_root_and_parentV_eq.mp hdChild).2]
        exact parentV_mem_BranchNodes_of_isValid ht hdneRoot
      have hmem : c ∈ branchChildrenTowardLeaf v l :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_inter.mpr ⟨hcChild, hcBranch⟩, hcl⟩
      apply Nat.le_antisymm
      · rw [Finset.card_le_one_iff]
        intro a b ha hb
        exact child_eq_of_toward_same_leaf
          (Finset.mem_inter.mp (Finset.mem_filter.mp ha).1).1
          (Finset.mem_inter.mp (Finset.mem_filter.mp hb).1).1
          (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      · exact Finset.one_le_card.mpr ⟨c, hmem⟩
  · simp only [hvl, if_false]
    rw [Finset.card_eq_zero]
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hs
    obtain ⟨c, hc⟩ := hs
    have hc' := Finset.mem_filter.mp hc
    exact hvl ((mem_childrenOf.mp (Finset.mem_inter.mp hc'.1).1).2.trans hc'.2)

/-- The unsubtracted form of the first nodewise power count below (5.71). -/
theorem gamma2_power_count {t : PlaneTree}
    (ht : t.isValid = true) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (v : VPos t) :
    gamma2 mu compound v =
      (branchChildren v).card +
        2 * (childrenOf v ∩ simpleLeaves t compound).card +
        ∑ l ∈ childrenOf v ∩ compoundLeaves t compound, mu.m l := by
  let S := childrenOf v ∩ simpleLeaves t compound
  let K := childrenOf v ∩ compoundLeaves t compound
  have hd : Disjoint S K := by
    exact Finset.disjoint_left.mpr fun x hxS hxK =>
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxS).2).2
        (Finset.mem_inter.mp (Finset.mem_inter.mp hxK).2).2
  have hu : S ∪ K = leafChildren v := by
    ext x
    by_cases hx : x ∈ compound
    <;> simp [S, K, leafChildren, simpleLeaves, compoundLeaves, hx]
  have hSK : S.card + K.card = (leafChildren v).card := by
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hchildren := card_leafChildren_add_branchChildren ht v
  have hK :
      (∑ l ∈ K, mu.m l) =
        K.card + ∑ l ∈ K, (mu.m l - 1) := by
    calc
      (∑ l ∈ K, mu.m l) =
          ∑ l ∈ K, (1 + (mu.m l - 1)) := by
            apply Finset.sum_congr rfl
            intro l hl
            have hleaf : l ∈ Leaves t :=
              (Finset.mem_inter.mp (Finset.mem_inter.mp hl).2).1
            have hm := mu.two_le l hleaf
            omega
      _ = K.card + ∑ l ∈ K, (mu.m l - 1) := by
        rw [Finset.sum_add_distrib]
        simp
  unfold gamma2
  change (childrenOf v).card + S.card +
      (∑ l ∈ K, (mu.m l - 1)) =
    (branchChildren v).card + 2 * S.card + ∑ l ∈ K, mu.m l
  omega

/-- The first line of the nodewise exponent count below (5.71). -/
theorem gamma2_sub_one_power_count {t : PlaneTree}
    (ht : t.isValid = true) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (v : VPos t) :
    gamma2 mu compound v - 1 =
      (branchChildren v).card +
        2 * (childrenOf v ∩ simpleLeaves t compound).card +
        (∑ l ∈ childrenOf v ∩ compoundLeaves t compound, mu.m l) - 1 := by
  exact congrArg (fun n : ℕ => n - 1)
    (gamma2_power_count ht mu compound v)

/-- The RHS exponent printed in the second line below (5.71), including the
leaf-path correction contributed by the ratio product. -/
def paper571RhsExponent {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l0 : HeppLeaf t) (v : VPos t) : ℤ :=
  (branchChildren v).card +
    2 * (childrenOf v ∩ simpleLeaves t compound).card +
    (∑ l ∈ childrenOf v ∩ compoundLeaves t compound, mu.m l) - 1 +
    (if v.1 <+: l0.1.1 then 1 else 0) -
    (if v = parentV l0.1 then 1 else 0) -
    (branchChildrenTowardLeaf v l0).card

/-- Full nodewise exponent identity underlying paper (5.71). -/
theorem paper571_exponent_identity {t : PlaneTree}
    (ht : t.isValid = true) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l0 : HeppLeaf t)
    {v : VPos t} (hv : v ∈ BranchNodes t) :
    (gamma2 mu compound v : ℤ) - 1 =
      paper571RhsExponent mu compound l0 v := by
  have hbaseNat := gamma2_power_count ht mu compound v
  have hbase :
      (gamma2 mu compound v : ℤ) =
        (branchChildren v).card +
          2 * (childrenOf v ∩ simpleLeaves t compound).card +
          (∑ l ∈ childrenOf v ∩ compoundLeaves t compound, mu.m l) := by
    exact_mod_cast hbaseNat
  have hparentPrefix :
      v = parentV l0.1 → v.1 <+: l0.1.1 := by
    intro hvp
    have hlne : l0.1 ≠ rootV t := by
      intro hl
      have hp : parentV l0.1 = l0.1 := by
        rw [hl, parentV_rootV]
      have hvl : v = l0.1 := hvp.trans hp
      have hzero := mem_Leaves_iff.mp l0.2
      have htwo := mem_BranchNodes_iff.mp hv
      rw [hvl] at htwo
      omega
    exact (mem_childrenOf.mp
      (mem_childrenOf_iff_ne_root_and_parentV_eq.mpr
        ⟨hlne, hvp.symm⟩)).2
  rw [paper571RhsExponent, hbase, card_branchChildrenTowardLeaf ht hv l0]
  by_cases hvl : v.1 <+: l0.1.1
  · by_cases hvp : v = parentV l0.1
    · subst v
      rw [if_pos (hparentPrefix rfl)]
      simp [hvl]
    · simp [hvl, hvp]
  · have hvp : v ≠ parentV l0.1 := fun h => hvl (hparentPrefix h)
    simp [hvl, hvp]

/-- Largest power of two not exceeding `q` (the value at `q = 0` is unused). -/
def dyadicFloor (q : ℕ) : ℕ :=
  2 ^ Nat.log 2 q

theorem dyadicFloor_bounds {q : ℕ} (hq : q ≠ 0) :
    dyadicFloor q ≤ q ∧ q < 2 * dyadicFloor q := by
  constructor
  · exact Nat.pow_log_le_self 2 hq
  · simpa [dyadicFloor, pow_succ, Nat.mul_comm] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two q

abbrev NXClass := ℕ × ℕ
abbrev NYClass := ℕ × ℕ

/-- `σ₁(l) = (N,X)`: parent scale and multiplicity dyadic block. -/
def singleScaleSigma1 {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (l : HeppLeaf t) : NXClass :=
  (scaleN Nm (parentV l.1), dyadicFloor (leafMultiplicity mu l))

/-- The exact leaf fiber `L_{N,X}`. -/
def leavesAtNX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NXClass) : Finset (HeppLeaf t) :=
  Finset.univ.filter fun l => singleScaleSigma1 Nm mu l = q

/-- Only `(N,X)` blocks which actually occur. -/
def nxCarrier {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : Finset NXClass :=
  Finset.univ.image (singleScaleSigma1 Nm mu)

/-- The finite type of active `(N,X)` classes. -/
abbrev ActiveNXClass {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :=
  {a : NXClass // a ∈ nxCarrier Nm mu}

/-- `σ₂(N,X) = (N,Y)`, where `Y` dyadically brackets `|L_{N,X}|`. -/
def singleScaleSigma2 {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NXClass) : NYClass :=
  (q.1, dyadicFloor (leavesAtNX Nm mu q).card)

/-- Only `(N,Y)` blocks which actually occur. -/
def nyCarrier {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : Finset NYClass :=
  (nxCarrier Nm mu).image (singleScaleSigma2 Nm mu)

/-- `σ₃(N,Y) = P = YN⁴`. -/
def singleScaleSigma3 (q : NYClass) : ℕ :=
  q.2 * q.1 ^ 4

/-- Only volume parameters `P` which actually occur. -/
def pCarrier {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : Finset ℕ :=
  (nyCarrier Nm mu).image singleScaleSigma3

/-- The finite type of distinct active values `P = Y N⁴`. -/
abbrev ActivePClass {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :=
  {P : ℕ // P ∈ pCarrier Nm mu}

def nxAtNY {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) : Finset NXClass :=
  (nxCarrier Nm mu).filter fun a => singleScaleSigma2 Nm mu a = q

def nyAtP {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ℕ) : Finset NYClass :=
  (nyCarrier Nm mu).filter fun q => singleScaleSigma3 q = P

/-- The exact leaf carrier `L_{N,Y}` induced by `σ₂ ∘ σ₁`. -/
def leavesAtNY {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) : Finset (HeppLeaf t) :=
  Finset.univ.filter fun l =>
    singleScaleSigma2 Nm mu (singleScaleSigma1 Nm mu l) = q

/-- The exact leaf carrier `L_P` induced by `σ₃ ∘ σ₂ ∘ σ₁`. -/
def leavesAtP {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ℕ) : Finset (HeppLeaf t) :=
  Finset.univ.filter fun l =>
    singleScaleSigma3
      (singleScaleSigma2 Nm mu (singleScaleSigma1 Nm mu l)) = P

/-- The paper's maximal `X*` in the `σ₂`-fiber. -/
def maxXAtNY {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) : ℕ :=
  (nxAtNY Nm mu q).sup Prod.snd

theorem sigma1_bucket {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (l : HeppLeaf t) :
    (singleScaleSigma1 Nm mu l).2 ≤ leafMultiplicity mu l ∧
      leafMultiplicity mu l < 2 * (singleScaleSigma1 Nm mu l).2 := by
  exact dyadicFloor_bounds (by
    have := mu.two_le l.1 l.2
    simp [leafMultiplicity]
    omega)

theorem sigma2_bucket {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NXClass} (hq : q ∈ nxCarrier Nm mu) :
    (singleScaleSigma2 Nm mu q).2 ≤ (leavesAtNX Nm mu q).card ∧
      (leavesAtNX Nm mu q).card <
        2 * (singleScaleSigma2 Nm mu q).2 := by
  apply dyadicFloor_bounds
  rw [Finset.card_ne_zero]
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨l, by simp [leavesAtNX]⟩

theorem nxClass_dyadic {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NXClass} (hq : q ∈ nxCarrier Nm mu) :
    IsDyadicNat q.1 ∧ IsDyadicNat q.2 := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨⟨Nm.Nexp (parentV l.1), rfl⟩,
    ⟨Nat.log 2 (leafMultiplicity mu l), rfl⟩⟩

theorem nyClass_dyadic {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    IsDyadicNat q.1 ∧ IsDyadicNat q.2 := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨(nxClass_dyadic Nm mu ha).1,
    ⟨Nat.log 2 (leavesAtNX Nm mu a).card, rfl⟩⟩

theorem pClass_dyadic {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {P : ℕ} (hP : P ∈ pCarrier Nm mu) :
    IsDyadicNat P := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨eN, hN⟩ := (nyClass_dyadic Nm mu hq).1
  obtain ⟨eY, hY⟩ := (nyClass_dyadic Nm mu hq).2
  refine ⟨eY + eN * 4, ?_⟩
  rw [singleScaleSigma3, hN, hY, ← pow_mul, ← pow_add]

def multiplicityNX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NXClass) : ℕ :=
  ∑ l ∈ leavesAtNX Nm mu q, leafMultiplicity mu l

/-- Quantitative form of `m_{N,X} ∼ XY` in (5.75), with constants `1,4`. -/
theorem multiplicityNX_bounds {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NXClass} (hq : q ∈ nxCarrier Nm mu) :
    q.2 * (singleScaleSigma2 Nm mu q).2 ≤ multiplicityNX Nm mu q ∧
      multiplicityNX Nm mu q <
        4 * q.2 * (singleScaleSigma2 Nm mu q).2 := by
  let s := leavesAtNX Nm mu q
  have hs : s.Nonempty := by
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨l, by simp [s, leavesAtNX]⟩
  have hpoint : ∀ l ∈ s,
      q.2 ≤ leafMultiplicity mu l ∧ leafMultiplicity mu l < 2 * q.2 := by
    intro l hl
    have hclass := (Finset.mem_filter.mp hl).2
    simpa [s] using (hclass ▸ sigma1_bucket Nm mu l)
  have hlo : s.card * q.2 ≤ multiplicityNX Nm mu q := by
    rw [multiplicityNX]
    calc
      s.card * q.2 = ∑ _l ∈ s, q.2 := by simp
      _ ≤ ∑ l ∈ s, leafMultiplicity mu l :=
        Finset.sum_le_sum fun l hl => (hpoint l hl).1
  have hup : multiplicityNX Nm mu q < s.card * (2 * q.2) := by
    rw [multiplicityNX]
    change (∑ l ∈ s, leafMultiplicity mu l) < _
    calc
      (∑ l ∈ s, leafMultiplicity mu l) < ∑ _l ∈ s, 2 * q.2 :=
        Finset.sum_lt_sum_of_nonempty hs fun l hl => (hpoint l hl).2
      _ = s.card * (2 * q.2) := by simp
  have hy := sigma2_bucket Nm mu hq
  have hx : 0 < q.2 := by
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
    simp [singleScaleSigma1, dyadicFloor]
  constructor
  · calc
      q.2 * (singleScaleSigma2 Nm mu q).2 ≤ q.2 * s.card :=
        Nat.mul_le_mul_left _ hy.1
      _ = s.card * q.2 := Nat.mul_comm _ _
      _ ≤ multiplicityNX Nm mu q := hlo
  · calc
      multiplicityNX Nm mu q < s.card * (2 * q.2) := hup
      _ < (2 * (singleScaleSigma2 Nm mu q).2) * (2 * q.2) :=
        (Nat.mul_lt_mul_right (by omega : 0 < 2 * q.2)).2 hy.2
      _ = 4 * q.2 * (singleScaleSigma2 Nm mu q).2 := by ring

theorem nxClass_second_eq_pow_log {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NXClass} (hq : q ∈ nxCarrier Nm mu) :
    q.2 = 2 ^ Nat.log 2 q.2 := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hq
  simp [singleScaleSigma1, dyadicFloor, Nat.log_pow Nat.one_lt_two]

/-- The distinct dyadic `X` values in a fixed `(N,Y)` fiber sum to at most
twice their maximum. -/
theorem sum_X_nxAtNY_le_two_maxX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    (∑ a ∈ nxAtNY Nm mu q, a.2) ≤ 2 * maxXAtNY Nm mu q := by
  let s := nxAtNY Nm mu q
  let e := fun a : NXClass => Nat.log 2 a.2
  have hs : s.Nonempty := by
    obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
    exact ⟨a, by simp [s, nxAtNY, ha, haq]⟩
  have hactive : ∀ a ∈ s, a ∈ nxCarrier Nm mu :=
    fun a ha => (Finset.mem_filter.mp ha).1
  have hfirst : ∀ a ∈ s, a.1 = q.1 := by
    intro a ha
    have h := congrArg Prod.fst (Finset.mem_filter.mp ha).2
    simpa [singleScaleSigma2] using h
  have hinj : Set.InjOn e s := by
    intro a ha b hb hab
    change Nat.log 2 a.2 = Nat.log 2 b.2 at hab
    apply Prod.ext
    · exact (hfirst a ha).trans (hfirst b hb).symm
    · calc
        a.2 = 2 ^ Nat.log 2 a.2 :=
          nxClass_second_eq_pow_log Nm mu (hactive a ha)
        _ = 2 ^ Nat.log 2 b.2 := by rw [hab]
        _ = b.2 :=
          (nxClass_second_eq_pow_log Nm mu (hactive b hb)).symm
  have himage :
      s.image e ⊆ Finset.range (Nat.log 2 (maxXAtNY Nm mu q) + 1) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le
      (Nat.log_mono_right (show a.2 ≤ maxXAtNY Nm mu q by
        exact Finset.le_sup ha))
  obtain ⟨aMax, haMax, hmax⟩ :=
    Finset.exists_mem_eq_sup s hs Prod.snd
  change maxXAtNY Nm mu q = aMax.2 at hmax
  have hmaxPow : maxXAtNY Nm mu q =
      2 ^ Nat.log 2 (maxXAtNY Nm mu q) := by
    rw [hmax]
    exact nxClass_second_eq_pow_log Nm mu (hactive aMax haMax)
  calc
    (∑ a ∈ nxAtNY Nm mu q, a.2) =
        ∑ a ∈ s, 2 ^ e a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact nxClass_second_eq_pow_log Nm mu (hactive a ha)
    _ = ∑ k ∈ s.image e, 2 ^ k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 (maxXAtNY Nm mu q) + 1),
          2 ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun _ _ _ => Nat.zero_le _)
    _ ≤ 2 * maxXAtNY Nm mu q := by
      have hgeom := geom_sum_mul_of_one_le
        (x := (2 : ℕ)) (by omega) (Nat.log 2 (maxXAtNY Nm mu q) + 1)
      simp only [Nat.reduceSubDiff, mul_one] at hgeom
      rw [hgeom, pow_succ, ← hmaxPow]
      omega

/-! ## The exact finite ledgers in (5.75) -/

def multiplicityNY {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) : ℕ :=
  ∑ a ∈ nxAtNY Nm mu q, multiplicityNX Nm mu a

def multiplicityP {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ℕ) : ℕ :=
  ∑ q ∈ nyAtP Nm mu P, multiplicityNY Nm mu q

/-- Quantitative form of `m_{N,Y} ∼ X*Y` in (5.75), with constants `1,8`. -/
theorem multiplicityNY_bounds {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    maxXAtNY Nm mu q * q.2 ≤ multiplicityNY Nm mu q ∧
      multiplicityNY Nm mu q ≤ 8 * maxXAtNY Nm mu q * q.2 := by
  let s := nxAtNY Nm mu q
  have hs : s.Nonempty := by
    obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
    exact ⟨a, by simp [s, nxAtNY, ha, haq]⟩
  obtain ⟨aMax, haMax, hmax⟩ :=
    Finset.exists_mem_eq_sup s hs Prod.snd
  change maxXAtNY Nm mu q = aMax.2 at hmax
  have haNX : aMax ∈ nxCarrier Nm mu := (Finset.mem_filter.mp haMax).1
  have haClass : singleScaleSigma2 Nm mu aMax = q :=
    (Finset.mem_filter.mp haMax).2
  have hmaxLower := (multiplicityNX_bounds Nm mu haNX).1
  rw [haClass] at hmaxLower
  have hsingle : multiplicityNX Nm mu aMax ≤ multiplicityNY Nm mu q := by
    rw [multiplicityNY]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) haMax
  constructor
  · rw [hmax]
    exact hmaxLower.trans hsingle
  · rw [multiplicityNY]
    calc
      (∑ a ∈ nxAtNY Nm mu q, multiplicityNX Nm mu a) ≤
          ∑ a ∈ nxAtNY Nm mu q, 4 * a.2 * q.2 := by
            apply Finset.sum_le_sum
            intro a ha
            have haNX : a ∈ nxCarrier Nm mu :=
              (Finset.mem_filter.mp ha).1
            have haClass : singleScaleSigma2 Nm mu a = q :=
              (Finset.mem_filter.mp ha).2
            exact Nat.le_of_lt (by
              simpa [haClass] using (multiplicityNX_bounds Nm mu haNX).2)
      _ = 4 * q.2 * (∑ a ∈ nxAtNY Nm mu q, a.2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ ≤ 4 * q.2 * (2 * maxXAtNY Nm mu q) :=
        Nat.mul_le_mul_left _
          (sum_X_nxAtNY_le_two_maxX Nm mu hq)
      _ = 8 * maxXAtNY Nm mu q * q.2 := by ring

/-- `m_{N,Y} = ∑_{σ₂(N,X)=(N,Y)} m_{N,X}` in (5.75). -/
theorem multiplicityNY_eq_fiber_sum {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) :
    multiplicityNY Nm mu q =
      ∑ a ∈ nxAtNY Nm mu q, multiplicityNX Nm mu a :=
  rfl

/-- `m_P = ∑_{YN⁴=P} m_{N,Y}` in (5.75). -/
theorem multiplicityP_eq_fiber_sum {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ℕ) :
    multiplicityP Nm mu P =
      ∑ q ∈ nyAtP Nm mu P, multiplicityNY Nm mu q :=
  rfl

/-- The nested `σ₂` ledger is exactly the multiplicity sum on `L_{N,Y}`. -/
theorem multiplicityNY_eq_leaf_sum {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) :
    multiplicityNY Nm mu q =
      ∑ l ∈ leavesAtNY Nm mu q, leafMultiplicity mu l := by
  have hmaps : ∀ l ∈ leavesAtNY Nm mu q,
      singleScaleSigma1 Nm mu l ∈ nxAtNY Nm mu q := by
    intro l hl
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ l),
        (Finset.mem_filter.mp hl).2⟩
  rw [multiplicityNY]
  calc
    (∑ a ∈ nxAtNY Nm mu q, multiplicityNX Nm mu a) =
        ∑ a ∈ nxAtNY Nm mu q,
          ∑ l ∈ (leavesAtNY Nm mu q).filter
            (fun l => singleScaleSigma1 Nm mu l = a),
              leafMultiplicity mu l := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [multiplicityNX]
                apply Finset.sum_congr
                · ext l
                  have haClass := (Finset.mem_filter.mp ha).2
                  simp only [leavesAtNX, leavesAtNY, Finset.mem_filter,
                    Finset.mem_univ, true_and]
                  constructor
                  · intro h
                    exact ⟨by simpa [h] using haClass, h⟩
                  · exact fun h => h.2
                · intros
                  rfl
    _ = ∑ l ∈ leavesAtNY Nm mu q, leafMultiplicity mu l :=
      Finset.sum_fiberwise_of_maps_to hmaps (leafMultiplicity mu)

/-- The nested `σ₃` ledger is exactly the multiplicity sum on `L_P`. -/
theorem multiplicityP_eq_leaf_sum {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (P : ℕ) :
    multiplicityP Nm mu P =
      ∑ l ∈ leavesAtP Nm mu P, leafMultiplicity mu l := by
  let cls := fun l : HeppLeaf t =>
    singleScaleSigma2 Nm mu (singleScaleSigma1 Nm mu l)
  have hmaps : ∀ l ∈ leavesAtP Nm mu P, cls l ∈ nyAtP Nm mu P := by
    intro l hl
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _
          (Finset.mem_univ l)), (Finset.mem_filter.mp hl).2⟩
  rw [multiplicityP]
  calc
    (∑ q ∈ nyAtP Nm mu P, multiplicityNY Nm mu q) =
        ∑ q ∈ nyAtP Nm mu P,
          ∑ l ∈ (leavesAtP Nm mu P).filter (fun l => cls l = q),
            leafMultiplicity mu l := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [multiplicityNY_eq_leaf_sum]
              apply Finset.sum_congr
              · ext l
                have hqClass := (Finset.mem_filter.mp hq).2
                simp only [leavesAtNY, leavesAtP, Finset.mem_filter,
                  Finset.mem_univ, true_and, cls]
                constructor
                · intro h
                  exact ⟨by simpa [h] using hqClass, h⟩
                · exact fun h => h.2
              · intros
                rfl
    _ = ∑ l ∈ leavesAtP Nm mu P, leafMultiplicity mu l :=
      Finset.sum_fiberwise_of_maps_to hmaps (leafMultiplicity mu)

theorem sum_multiplicityNX {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :
    (∑ q ∈ nxCarrier Nm mu, multiplicityNX Nm mu q) =
      totalMultiplicity mu := by
  simpa [multiplicityNX, leavesAtNX, nxCarrier, totalMultiplicity] using
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (HeppLeaf t)))
      (t := nxCarrier Nm mu) (g := singleScaleSigma1 Nm mu)
      (fun l hl => Finset.mem_image_of_mem _ hl) (leafMultiplicity mu))

theorem sum_multiplicityNY_eq_sum_NX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    (∑ q ∈ nyCarrier Nm mu, multiplicityNY Nm mu q) =
      ∑ a ∈ nxCarrier Nm mu, multiplicityNX Nm mu a := by
  simpa [multiplicityNY, nxAtNY] using
    (Finset.sum_fiberwise_of_maps_to
      (s := nxCarrier Nm mu) (t := nyCarrier Nm mu)
      (g := singleScaleSigma2 Nm mu)
      (fun a ha => Finset.mem_image_of_mem _ ha) (multiplicityNX Nm mu))

theorem sum_multiplicityP_eq_sum_NY {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    (∑ P ∈ pCarrier Nm mu, multiplicityP Nm mu P) =
      ∑ q ∈ nyCarrier Nm mu, multiplicityNY Nm mu q := by
  simpa [multiplicityP, nyAtP] using
    (Finset.sum_fiberwise_of_maps_to
      (s := nyCarrier Nm mu) (t := pCarrier Nm mu)
      (g := singleScaleSigma3)
      (fun q hq => Finset.mem_image_of_mem _ hq) (multiplicityNY Nm mu))

/-- The final identity `m = ∑_P m_P` in (5.75). -/
theorem totalMultiplicity_eq_sum_P {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) :
    totalMultiplicity mu =
      ∑ P ∈ pCarrier Nm mu, multiplicityP Nm mu P := by
  rw [sum_multiplicityP_eq_sum_NY, sum_multiplicityNY_eq_sum_NX,
    sum_multiplicityNX]

/-! ## Root-scale budget used by the mixed skipped-edge estimate -/

def weightedLeafMass {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) : ℕ :=
  ∑ l : HeppLeaf t,
    leafMultiplicity mu l * scaleN Nm (parentV l.1)

private theorem parentFiberMultiplicity_le_gammaInf {t : PlaneTree}
    (hroot : rootV t ∈ BranchNodes t) (mu : Multiplicities t)
    (v : VPos t) :
    (∑ l ∈ (Finset.univ : Finset (HeppLeaf t)).filter
        (fun l => parentV l.1 = v), leafMultiplicity mu l) ≤
      gammaInf mu v := by
  let s := (Finset.univ : Finset (HeppLeaf t)).filter
    (fun l => parentV l.1 = v)
  let vals := s.image fun l => l.1
  have hinj : Set.InjOn (fun l : HeppLeaf t => l.1) s := by
    intro a _ b _ h
    exact Subtype.ext h
  have hsubset : vals ⊆ leafChildren v := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
    have hp := (Finset.mem_filter.mp hl).2
    have hne : l.1 ≠ rootV t := by
      intro h
      have hzero := mem_Leaves_iff.mp (h ▸ l.2)
      have htwo := mem_BranchNodes_iff.mp hroot
      omega
    exact Finset.mem_inter.mpr
      ⟨mem_childrenOf_iff_ne_root_and_parentV_eq.mpr ⟨hne, hp⟩, l.2⟩
  have hsubsum :
      (∑ l ∈ s, leafMultiplicity mu l) ≤
        ∑ l ∈ leafChildren v, mu.m l := by
    rw [show (∑ l ∈ s, leafMultiplicity mu l) =
        ∑ l ∈ vals, mu.m l by
      rw [Finset.sum_image hinj]
      rfl]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have hsplit :
      (∑ l ∈ leafChildren v, mu.m l) =
        (leafChildren v).card +
          ∑ l ∈ leafChildren v, (mu.m l - 1) := by
    calc
      (∑ l ∈ leafChildren v, mu.m l) =
          ∑ l ∈ leafChildren v, (1 + (mu.m l - 1)) := by
            apply Finset.sum_congr rfl
            intro l hl
            have hm := mu.two_le l (Finset.mem_inter.mp hl).2
            omega
      _ = (leafChildren v).card +
          ∑ l ∈ leafChildren v, (mu.m l - 1) := by
            rw [Finset.sum_add_distrib]
            simp
  have hcard : (leafChildren v).card ≤ (childrenOf v).card :=
    Finset.card_le_card Finset.inter_subset_left
  change (∑ l ∈ s, leafMultiplicity mu l) ≤ gammaInf mu v
  rw [gammaInf]
  omega

@[simp] theorem branchNodesUnder_root (t : PlaneTree) :
    branchNodesUnder (rootV t) = BranchNodes t := by
  ext v
  simp [branchNodesUnder, rootV]

/-- The exact global budget behind `R/N ≳ X*Y`: all leaf mass weighted by
its parent scale is bounded by the root accumulated scale. -/
theorem weightedLeafMass_le_accumulatedRoot {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    weightedLeafMass Nm mu ≤ accumulatedScale Nm mu (rootV t) := by
  have hmaps : ∀ l ∈ (Finset.univ : Finset (HeppLeaf t)),
      parentV l.1 ∈ BranchNodes t := by
    intro l _
    apply parentV_mem_BranchNodes_of_isValid ht
    intro h
    have hzero := mem_Leaves_iff.mp (h ▸ l.2)
    have htwo := mem_BranchNodes_iff.mp hroot
    omega
  rw [weightedLeafMass,
    ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun l => leafMultiplicity mu l * scaleN Nm (parentV l.1))]
  rw [accumulatedScale, branchNodesUnder_root]
  apply Finset.sum_le_sum
  intro v hv
  calc
    (∑ l ∈ (Finset.univ : Finset (HeppLeaf t)).filter
        (fun l => parentV l.1 = v),
        leafMultiplicity mu l * scaleN Nm (parentV l.1)) =
        (∑ l ∈ (Finset.univ : Finset (HeppLeaf t)).filter
          (fun l => parentV l.1 = v), leafMultiplicity mu l) *
            scaleN Nm v := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro l hl
              rw [(Finset.mem_filter.mp hl).2]
    _ ≤ gammaInf mu v * scaleN Nm v :=
      Nat.mul_le_mul_right _ (parentFiberMultiplicity_le_gammaInf hroot mu v)

/-- One `(N,X)` block consumes at least `N m_{N,X}` of the global leaf
budget.  This exact inequality is the bridge from classification to `R`. -/
theorem nxScale_mul_multiplicity_le_weightedLeafMass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (q : NXClass) :
    q.1 * multiplicityNX Nm mu q ≤ weightedLeafMass Nm mu := by
  rw [multiplicityNX, weightedLeafMass, Finset.mul_sum]
  calc
    (∑ l ∈ leavesAtNX Nm mu q, q.1 * leafMultiplicity mu l) =
        ∑ l ∈ leavesAtNX Nm mu q,
          leafMultiplicity mu l * scaleN Nm (parentV l.1) := by
            apply Finset.sum_congr rfl
            intro l hl
            have hclass := (Finset.mem_filter.mp hl).2
            have hN := congrArg Prod.fst hclass
            simp only [singleScaleSigma1] at hN
            rw [hN]
            exact Nat.mul_comm _ _
    _ ≤ ∑ l ∈ (Finset.univ : Finset (HeppLeaf t)),
          leafMultiplicity mu l * scaleN Nm (parentV l.1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro l hl
        exact Finset.mem_univ l)
        (fun _ _ _ => Nat.zero_le _)

/-- Explicit form of the paper's `R/N ≳ X*Y`, used in (5.91):
for every active `(N,Y)` class, `N·Y·X* ≤ R` with constant exactly one. -/
theorem nyClass_scale_mul_Y_mul_maxX_le_R {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t) (R : ℕ)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    q.1 * q.2 * maxXAtNY Nm mu q ≤ R := by
  have hfiber : (nxAtNY Nm mu q).Nonempty := by
    obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
    exact ⟨a, by simp [nxAtNY, ha, haq]⟩
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_mem_eq_sup (nxAtNY Nm mu q) hfiber Prod.snd
  have haNX : a ∈ nxCarrier Nm mu := (Finset.mem_filter.mp ha).1
  have haClass : singleScaleSigma2 Nm mu a = q :=
    (Finset.mem_filter.mp ha).2
  have hXY := (multiplicityNX_bounds Nm mu haNX).1
  rw [haClass] at hXY
  have hN : a.1 = q.1 := by
    simpa [singleScaleSigma2] using congrArg Prod.fst haClass
  change maxXAtNY Nm mu q = a.2 at hmax
  calc
    q.1 * q.2 * maxXAtNY Nm mu q = a.1 * (a.2 * q.2) := by
      rw [hN, hmax]
      ring
    _ ≤ a.1 * multiplicityNX Nm mu a := Nat.mul_le_mul_left _ hXY
    _ ≤ weightedLeafMass Nm mu :=
      nxScale_mul_multiplicity_le_weightedLeafMass Nm mu a
    _ ≤ accumulatedScale Nm mu (rootV t) :=
      weightedLeafMass_le_accumulatedRoot ht hroot Nm mu
    _ ≤ R := hR

/-- Division form consumed by the mixed-edge local estimate: `X*Y ≤ R/N`. -/
theorem nyClass_Y_mul_maxX_le_R_div_scale {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t) (R : ℕ)
    (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    (q.2 : ℝ) * maxXAtNY Nm mu q ≤ (R : ℝ) / q.1 := by
  have hqpos : 0 < q.1 := by
    obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
    obtain ⟨l, _, hla⟩ := Finset.mem_image.mp ha
    have hlaN := congrArg Prod.fst hla
    have haqN := congrArg Prod.fst haq
    simp only [singleScaleSigma1] at hlaN
    simp only [singleScaleSigma2] at haqN
    rw [← haqN, ← hlaN]
    exact scaleN_pos Nm (parentV l.1)
  rw [le_div_iff₀ (by exact_mod_cast hqpos)]
  exact_mod_cast (by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      nyClass_scale_mul_Y_mul_maxX_le_R ht hroot Nm mu R hR hq)

/-! ## Interface to the analytic `XYCluster` estimates

An `(N,Y)` class can contain several `(N,X)` fibers.  The point set used by
Lemma 5.14 is one such `(N,X)` fiber, not their union.  For the coarse
`(N,Y)` interface we canonically choose a fiber attaining `X*`.
-/

theorem nxAtNY_nonempty {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    (nxAtNY Nm mu q).Nonempty := by
  obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
  exact ⟨a, by simp [nxAtNY, ha, haq]⟩

/-- A canonical `(N,X*)` representative of an active `(N,Y)` class. -/
noncomputable def maxNXAtNY {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    NXClass :=
  Classical.choose
    (Finset.exists_mem_eq_sup (nxAtNY Nm mu q)
      (nxAtNY_nonempty Nm mu hq) Prod.snd)

theorem maxNXAtNY_mem {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    maxNXAtNY Nm mu q hq ∈ nxAtNY Nm mu q :=
  (Classical.choose_spec
    (Finset.exists_mem_eq_sup (nxAtNY Nm mu q)
      (nxAtNY_nonempty Nm mu hq) Prod.snd)).1

@[simp] theorem maxNXAtNY_snd {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    (maxNXAtNY Nm mu q hq).2 = maxXAtNY Nm mu q := by
  exact (Classical.choose_spec
    (Finset.exists_mem_eq_sup (nxAtNY Nm mu q)
      (nxAtNY_nonempty Nm mu hq) Prod.snd)).2.symm

@[simp] theorem maxNXAtNY_fst {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    (maxNXAtNY Nm mu q hq).1 = q.1 := by
  have h := congrArg Prod.fst
    (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu q hq)).2
  simpa [singleScaleSigma2] using h

theorem maxNXAtNY_active {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    maxNXAtNY Nm mu q hq ∈ nxCarrier Nm mu :=
  (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu q hq)).1

theorem leavesAtNX_nonempty {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (leavesAtNX Nm mu a).Nonempty := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨l, by simp [leavesAtNX]⟩

theorem one_le_nxClass_X {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    1 ≤ a.2 := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp ha
  simp only [singleScaleSigma1, dyadicFloor]
  exact Nat.one_le_pow (Nat.log 2 (leafMultiplicity mu l)) 2 (by norm_num)

private theorem nxClass_parentScale {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {a : NXClass} {l : HeppLeaf t}
    (hl : l ∈ leavesAtNX Nm mu a) :
    scaleN Nm (parentV l.1) = a.1 := by
  exact congrArg Prod.fst (Finset.mem_filter.mp hl).2

theorem two_le_nxClass_scale {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) : 2 ≤ a.1 := by
  obtain ⟨l, hl⟩ := leavesAtNX_nonempty Nm mu ha
  have hlne : l.1 ≠ rootV t := by
    intro h
    have hzero := mem_Leaves_iff.mp (h ▸ l.2)
    have htwo := mem_BranchNodes_iff.mp hroot
    omega
  have hp := parentV_mem_BranchNodes_of_isValid ht hlne
  have he : 1 ≤ Nm.Nexp (parentV l.1) := Nm.pos _ hp
  rw [← nxClass_parentScale Nm mu hl, scaleN]
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ Nm.Nexp (parentV l.1) :=
      Nat.pow_le_pow_right (by omega) he

/-- The actual lattice scale supplied to Lemma 5.14.  The factor `1/2`
is exactly the separation loss in (5.73). -/
def nxClassNhat (a : NXClass) : ℝ :=
  max 1 ((a.1 : ℝ) / 2)

/-- Embedded point set of one active `(N,X)` fiber. -/
def nxClassPoints {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ)
    (a : NXClass) : Finset (Fin 4 → ℤ) :=
  (leavesAtNX Nm mu a).image z

theorem nxClassNhat_eq_half {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    nxClassNhat a = (a.1 : ℝ) / 2 := by
  rw [nxClassNhat, max_eq_right]
  have htwo : (2 : ℝ) ≤ a.1 := by
    exact_mod_cast two_le_nxClass_scale ht hroot Nm mu ha
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa using htwo)

theorem nxClassPoints_nonempty {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (nxClassPoints Nm mu z a).Nonempty :=
  (leavesAtNX_nonempty Nm mu ha).image z

theorem card_nxClassPoints {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ)
    (hz : Function.Injective z) (a : NXClass) :
    (nxClassPoints Nm mu z a).card = (leavesAtNX Nm mu a).card := by
  exact Finset.card_image_of_injective _ hz

theorem nxClassPoints_separated {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    ∀ x ∈ nxClassPoints Nm mu z a, ∀ y ∈ nxClassPoints Nm mu z a,
      x ≠ y → nxClassNhat a ≤ znorm (x - y) := by
  intro x hx y hy hxy
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hy
  have hll : l ≠ l' := by
    intro h
    subst l'
    exact hxy rfl
  have hsep := parentScale_separation ht hroot Nm z hz hll
  rw [nxClass_parentScale Nm mu hl, nxClass_parentScale Nm mu hl',
    max_self] at hsep
  rw [nxClassNhat_eq_half ht hroot Nm mu ha]
  exact hsep

/-- Paper-facing analytic cluster attached to one active `(N,X)` fiber. -/
noncomputable def nxClassCluster {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) : XYCluster where
  points := nxClassPoints Nm mu z a
  X := a.2
  N := nxClassNhat a
  X_nonneg := by positivity
  one_le_N := le_max_left _ _
  separated := nxClassPoints_separated ht hroot Nm mu z hz ha

/-- The `(N,Y)` coarse representative is its canonical maximal-`X` fiber. -/
noncomputable def nyClassCluster {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) : XYCluster :=
  nxClassCluster ht hroot Nm mu z hz (maxNXAtNY Nm mu q hq)
    (maxNXAtNY_active Nm mu q hq)

@[simp] theorem nxClassCluster_points {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz a ha).points =
      nxClassPoints Nm mu z a := rfl

@[simp] theorem nxClassCluster_X {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz a ha).X = a.2 := rfl

@[simp] theorem nxClassCluster_N {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz a ha).N =
      (a.1 : ℝ) / 2 :=
  nxClassNhat_eq_half ht hroot Nm mu ha

theorem nxClassCluster_card_bounds {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (singleScaleSigma2 Nm mu a).2 ≤
        (nxClassCluster ht hroot Nm mu z hz a ha).points.card ∧
      (nxClassCluster ht hroot Nm mu z hz a ha).points.card <
        2 * (singleScaleSigma2 Nm mu a).2 := by
  rw [nxClassCluster_points,
    card_nxClassPoints Nm mu z hz.1]
  exact sigma2_bucket Nm mu ha

theorem nxClass_X_mul_card_le_multiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) :
    a.2 * (leavesAtNX Nm mu a).card ≤ multiplicityNX Nm mu a := by
  rw [multiplicityNX]
  calc
    a.2 * (leavesAtNX Nm mu a).card =
        ∑ _l ∈ leavesAtNX Nm mu a, a.2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ l ∈ leavesAtNX Nm mu a, leafMultiplicity mu l := by
      apply Finset.sum_le_sum
      intro l hl
      have hclass := (Finset.mem_filter.mp hl).2
      simpa [hclass] using (sigma1_bucket Nm mu l).1

/-- The exact raw form of the root-budget hypothesis needed by the mixed
analytic estimate, for any active `(N,X)` fiber. -/
theorem nxClassCluster_R_dominance_one {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℕ) (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (nxClassCluster ht hroot Nm mu z hz a ha).N *
        (nxClassCluster ht hroot Nm mu z hz a ha).X *
        (nxClassCluster ht hroot Nm mu z hz a ha).Y ≤ (R : ℝ) := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  have hbudgetNat :
      a.1 * (a.2 * (leavesAtNX Nm mu a).card) ≤ R := by
    calc
      a.1 * (a.2 * (leavesAtNX Nm mu a).card) ≤
          a.1 * multiplicityNX Nm mu a :=
        Nat.mul_le_mul_left _ (nxClass_X_mul_card_le_multiplicity Nm mu a)
      _ ≤ weightedLeafMass Nm mu :=
        nxScale_mul_multiplicity_le_weightedLeafMass Nm mu a
      _ ≤ accumulatedScale Nm mu (rootV t) :=
        weightedLeafMass_le_accumulatedRoot ht hroot Nm mu
      _ ≤ R := hR
  have hbudget :
      (a.1 : ℝ) * (a.2 : ℝ) * (leavesAtNX Nm mu a).card ≤ (R : ℝ) := by
    exact_mod_cast (by
      simpa [Nat.mul_assoc] using hbudgetNat)
  have hhalf : (a.1 : ℝ) / 2 ≤ a.1 := by
    have hn : (0 : ℝ) ≤ a.1 := by positivity
    linarith
  rw [show c.N = (a.1 : ℝ) / 2 by
      exact nxClassCluster_N ht hroot Nm mu z hz a ha,
    show c.X = (a.2 : ℝ) by rfl, XYCluster.Y,
    show c.points.card = (leavesAtNX Nm mu a).card by
      exact card_nxClassPoints Nm mu z hz.1 a]
  calc
    (a.1 : ℝ) / 2 * a.2 * (leavesAtNX Nm mu a).card ≤
        (a.1 : ℝ) * a.2 * (leavesAtNX Nm mu a).card := by
      gcongr
    _ ≤ (R : ℝ) := hbudget

/-- The dyadic proxy `YN⁴` and the actual Lemma 5.14 volume
`|L_{N,X}|(N/2)⁴` differ by fixed constants only. -/
theorem nxClassCluster_P_lower {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    (singleScaleSigma3 (singleScaleSigma2 Nm mu a) : ℝ) ≤
      16 * (nxClassCluster ht hroot Nm mu z hz a ha).P := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  have hb := (nxClassCluster_card_bounds ht hroot Nm mu z hz ha).1
  have hcard :
      ((singleScaleSigma2 Nm mu a).2 : ℝ) ≤ c.points.card := by
    exact_mod_cast hb
  have hpow : 0 ≤ (a.1 : ℝ) ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcard hpow
  calc
    (singleScaleSigma3 (singleScaleSigma2 Nm mu a) : ℝ) =
        ((singleScaleSigma2 Nm mu a).2 : ℝ) * (a.1 : ℝ) ^ 4 := by
      simp [singleScaleSigma3, singleScaleSigma2]
    _ ≤ (c.points.card : ℝ) * (a.1 : ℝ) ^ 4 := hmul
    _ = 16 * c.P := by
      rw [XYCluster.P, XYCluster.Y,
        show c.N = (a.1 : ℝ) / 2 by
          exact nxClassCluster_N ht hroot Nm mu z hz a ha]
      ring

theorem nxClassCluster_P_upper {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    8 * (nxClassCluster ht hroot Nm mu z hz a ha).P ≤
      (singleScaleSigma3 (singleScaleSigma2 Nm mu a) : ℝ) := by
  let c := nxClassCluster ht hroot Nm mu z hz a ha
  have hb := (nxClassCluster_card_bounds ht hroot Nm mu z hz ha).2
  have hcard :
      (c.points.card : ℝ) ≤
        2 * (singleScaleSigma2 Nm mu a).2 := by
    exact_mod_cast (le_of_lt hb)
  have hpow : 0 ≤ (a.1 : ℝ) ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcard hpow
  calc
    8 * c.P = ((c.points.card : ℝ) * (a.1 : ℝ) ^ 4) / 2 := by
      rw [XYCluster.P, XYCluster.Y,
        show c.N = (a.1 : ℝ) / 2 by
          exact nxClassCluster_N ht hroot Nm mu z hz a ha]
      ring
    _ ≤ ((2 * (singleScaleSigma2 Nm mu a).2 : ℝ) *
          (a.1 : ℝ) ^ 4) / 2 :=
      div_le_div_of_nonneg_right hmul (by norm_num)
    _ = (singleScaleSigma3 (singleScaleSigma2 Nm mu a) : ℝ) := by
      simp [singleScaleSigma3, singleScaleSigma2]
      ring

@[simp] theorem nyClassCluster_X {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    (nyClassCluster ht hroot Nm mu z hz q hq).X =
      maxXAtNY Nm mu q := by
  simp [nyClassCluster]

@[simp] theorem nyClassCluster_N {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    (nyClassCluster ht hroot Nm mu z hz q hq).N =
      (q.1 : ℝ) / 2 := by
  simp [nyClassCluster]

theorem nyClassCluster_one_le_N {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    1 ≤ (nyClassCluster ht hroot Nm mu z hz q hq).N :=
  (nyClassCluster ht hroot Nm mu z hz q hq).one_le_N

theorem nyClassCluster_separated {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    ∀ x ∈ (nyClassCluster ht hroot Nm mu z hz q hq).points,
      ∀ y ∈ (nyClassCluster ht hroot Nm mu z hz q hq).points,
        x ≠ y →
          (nyClassCluster ht hroot Nm mu z hz q hq).N ≤ znorm (x - y) :=
  (nyClassCluster ht hroot Nm mu z hz q hq).separated

theorem nyClassCluster_points_nonempty {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    (nyClassCluster ht hroot Nm mu z hz q hq).points.Nonempty := by
  exact nxClassPoints_nonempty Nm mu z (maxNXAtNY_active Nm mu q hq)

theorem nyClassCluster_one_le_X {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    1 ≤ (nyClassCluster ht hroot Nm mu z hz q hq).X := by
  rw [nyClassCluster_X]
  exact_mod_cast (by
    simpa using one_le_nxClass_X Nm mu (maxNXAtNY_active Nm mu q hq))

theorem nyClassCluster_card_bounds {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    q.2 ≤ (nyClassCluster ht hroot Nm mu z hz q hq).points.card ∧
      (nyClassCluster ht hroot Nm mu z hz q hq).points.card < 2 * q.2 := by
  let a := maxNXAtNY Nm mu q hq
  have ha : a ∈ nxCarrier Nm mu := maxNXAtNY_active Nm mu q hq
  have hclass : singleScaleSigma2 Nm mu a = q :=
    (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu q hq)).2
  have hb := nxClassCluster_card_bounds ht hroot Nm mu z hz ha
  rw [hclass] at hb
  exact hb

/-- The requested setup-side bridge.  `SingleScaleMixed` can turn this
definition-free inequality into `RNDominance 2 R` by one simplification. -/
theorem nyClassCluster_R_dominance_two {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℕ) (hR : accumulatedScale Nm mu (rootV t) ≤ R)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    (nyClassCluster ht hroot Nm mu z hz q hq).N *
        (nyClassCluster ht hroot Nm mu z hz q hq).X *
        (nyClassCluster ht hroot Nm mu z hz q hq).Y ≤ 2 * (R : ℝ) := by
  have h := nxClassCluster_R_dominance_one ht hroot Nm mu z hz R hR
    (maxNXAtNY_active Nm mu q hq)
  have hR0 : (0 : ℝ) ≤ R := by positivity
  change (nyClassCluster ht hroot Nm mu z hz q hq).N *
      (nyClassCluster ht hroot Nm mu z hz q hq).X *
      (nyClassCluster ht hroot Nm mu z hz q hq).Y ≤ _
  exact h.trans (by nlinarith)

theorem nyClass_P_dyadic {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    IsDyadicNat (singleScaleSigma3 q) :=
  pClass_dyadic Nm mu (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

/-- Constant comparison needed to replace the analytic cluster's actual
`P = |points| N̂⁴` by the paper's dyadic `P = YN⁴`. -/
theorem nyClassCluster_P_comparable {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (q : NYClass) (hq : q ∈ nyCarrier Nm mu) :
    8 * (nyClassCluster ht hroot Nm mu z hz q hq).P ≤
        (singleScaleSigma3 q : ℝ) ∧
      (singleScaleSigma3 q : ℝ) ≤
        16 * (nyClassCluster ht hroot Nm mu z hz q hq).P := by
  let a := maxNXAtNY Nm mu q hq
  have ha : a ∈ nxCarrier Nm mu := maxNXAtNY_active Nm mu q hq
  have hclass : singleScaleSigma2 Nm mu a = q :=
    (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu q hq)).2
  constructor
  · simpa [nyClassCluster, a, hclass] using
      nxClassCluster_P_upper ht hroot Nm mu z hz ha
  · simpa [nyClassCluster, a, hclass] using
      nxClassCluster_P_lower ht hroot Nm mu z hz ha

end

end Anderson4D
