import Anderson4D.HeppTree.Admissible
import Anderson4D.HeppTree.ValidParent

/-! # Simple and compound leaves: paper Def 5.8 and (5.30)–(5.31). -/
namespace Anderson4D
open PlaneTree
open scoped BigOperators
/-- Compound leaves; vertices outside `Leaves t` are ignored. -/
def compoundLeaves (t : PlaneTree) (C : Finset (VPos t)) : Finset (VPos t) :=
  Leaves t ∩ C
/-- Simple leaves are precisely the non-compound leaves. -/
def simpleLeaves (t : PlaneTree) (C : Finset (VPos t)) : Finset (VPos t) :=
  Leaves t \ C
def leafChildren {t : PlaneTree} (v : VPos t) : Finset (VPos t) :=
  childrenOf v ∩ Leaves t
def branchChildren {t : PlaneTree} (v : VPos t) : Finset (VPos t) :=
  childrenOf v ∩ BranchNodes t
/-- Paper (5.30): simple leaves count twice, compound leaves fully. -/
def gamma2 {t : PlaneTree} (mu : Multiplicities t) (C : Finset (VPos t))
    (v : VPos t) : ℕ :=
  (childrenOf v).card + (childrenOf v ∩ simpleLeaves t C).card +
    ∑ l ∈ childrenOf v ∩ compoundLeaves t C, (mu.m l - 1)
/-- Paper (5.30): every leaf child counts with full multiplicity. -/
def gammaInf {t : PlaneTree} (mu : Multiplicities t) (v : VPos t) : ℕ :=
  (childrenOf v).card + ∑ l ∈ leafChildren v, (mu.m l - 1)
theorem simple_union_compound (t : PlaneTree) (C : Finset (VPos t)) :
    simpleLeaves t C ∪ compoundLeaves t C = Leaves t := by
  ext v
  by_cases hv : v ∈ C <;> simp [simpleLeaves, compoundLeaves, hv]
theorem disjoint_simple_compound (t : PlaneTree) (C : Finset (VPos t)) :
    Disjoint (simpleLeaves t C) (compoundLeaves t C) := by
  exact Finset.disjoint_left.mpr fun x hs hc =>
    (Finset.mem_sdiff.mp hs).2 (Finset.mem_inter.mp hc).2
/-- The inequality following (5.30), using `m_l ≥ 2`. -/
theorem gamma2_le_gammaInf {t : PlaneTree} (mu : Multiplicities t)
    (C : Finset (VPos t)) (v : VPos t) :
    gamma2 mu C v ≤ gammaInf mu v := by
  classical
  let S := childrenOf v ∩ simpleLeaves t C
  let K := childrenOf v ∩ compoundLeaves t C
  have hd : Disjoint S K := by
    exact Finset.disjoint_left.mpr fun x hxS hxK =>
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxS).2).2
        (Finset.mem_inter.mp (Finset.mem_inter.mp hxK).2).2
  have hu : S ∪ K = leafChildren v := by
    ext x
    by_cases hx : x ∈ C
    <;> simp [S, K, leafChildren, simpleLeaves, compoundLeaves, hx]
  have hs : S.card ≤ ∑ x ∈ S, (mu.m x - 1) := by
    calc
      S.card = ∑ _x ∈ S, 1 := by simp
      _ ≤ ∑ x ∈ S, (mu.m x - 1) := by
        exact Finset.sum_le_sum fun x hx => by
          have hxleaf : x ∈ Leaves t := by
            exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
          have := mu.two_le x hxleaf
          omega
  have hsum :
      (∑ x ∈ S, (mu.m x - 1)) + (∑ x ∈ K, (mu.m x - 1)) =
        ∑ x ∈ leafChildren v, (mu.m x - 1) := by
    rw [← hu, Finset.sum_union hd]
  unfold gamma2 gammaInf
  change (childrenOf v).card + S.card + (∑ x ∈ K, (mu.m x - 1)) ≤ _
  omega
private theorem valid_get {cs : List PlaneTree} (h : isValidList cs = true)
    (i : Fin cs.length) : (cs.get i).isValid = true := by
  rw [isValidList_eq_map] at h
  simp only [List.all_eq_true, id_eq] at h
  exact h _ (List.mem_map.mpr ⟨_, List.get_mem cs i, rfl⟩)
private theorem childCount_ne_one {t : PlaneTree} {p : Pos}
    (ht : t.isValid = true) (hp : IsPos t p) : childCount t p ≠ 1 := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
      simpa [childCount] using ht.1
  | cons i p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨hi, hp'⟩ := isPos_cons_iff.mp hp
      simp only [isValid, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
      have hv := valid_get ht.2 ⟨i, hi⟩
      simpa [childCount, hi] using ih hv hp'
private theorem leaf_or_branch_of_valid {t : PlaneTree} (ht : t.isValid = true)
    (v : VPos t) : v ∈ Leaves t ∨ v ∈ BranchNodes t := by
  rw [mem_Leaves_iff, mem_BranchNodes_iff]
  have := childCount_ne_one ht v.2
  omega
theorem card_leafChildren_add_branchChildren {t : PlaneTree}
    (ht : t.isValid = true) (v : VPos t) :
    (leafChildren v).card + (branchChildren v).card = (childrenOf v).card := by
  have hd : Disjoint (leafChildren v) (branchChildren v) := by
    exact Finset.disjoint_left.mpr fun x hxL hxB => by
      have h0 := mem_Leaves_iff.mp (Finset.mem_inter.mp hxL).2
      have h2 := mem_BranchNodes_iff.mp (Finset.mem_inter.mp hxB).2
      omega
  rw [← Finset.card_union_of_disjoint hd]
  congr
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).1
    · exact (Finset.mem_inter.mp hx).1
  · intro hx
    rcases leaf_or_branch_of_valid ht x with hxL | hxB
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxL⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxB⟩)
theorem gamma2_allSimple {t : PlaneTree} (mu : Multiplicities t) (v : VPos t) :
    gamma2 mu ∅ v = (childrenOf v).card + (leafChildren v).card := by
  simp [gamma2, simpleLeaves, compoundLeaves, leafChildren]
/-- Collected exponent of `N_v` on the left of paper (5.31). -/
def allSimpleLhsExponent {t : PlaneTree} (v : VPos t) : ℤ :=
  -4 * (childrenOf v).card + 4 - if v = rootV t then 2 else 0
/-- Collected exponent on the right of (5.31), including the parent ratios. -/
def allSimpleRhsExponent {t : PlaneTree} (mu : Multiplicities t) (v : VPos t) : ℤ :=
  -2 * gamma2 mu ∅ v + 2 + (if v = rootV t then 0 else 2) -
    2 * (branchChildren v).card
/-- The nodewise power count printed immediately after (5.31). -/
theorem allSimple_exponent_identity {t : PlaneTree} (ht : t.isValid = true)
    (mu : Multiplicities t) (v : VPos t) :
    allSimpleLhsExponent v = allSimpleRhsExponent mu v := by
  rw [allSimpleLhsExponent, allSimpleRhsExponent, gamma2_allSimple]
  by_cases hv : v = rootV t
  · subst v
    have h := card_leafChildren_add_branchChildren ht (rootV t)
    simp
    omega
  · have h := card_leafChildren_add_branchChildren ht v
    simp [hv]
    omega
/-- Positive-real `zpow` form of (5.31), with parent-ratio powers collected. -/
theorem allSimple_product_identity {t : PlaneTree} (ht : t.isValid = true)
    (mu : Multiplicities t) (N : VPos t → ℝ)
    (_hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ v ∈ BranchNodes t, N v ^ allSimpleLhsExponent v) =
      ∏ v ∈ BranchNodes t, N v ^ allSimpleRhsExponent mu v := by
  apply Finset.prod_congr rfl
  intro v _
  rw [allSimple_exponent_identity ht mu v]

/-- A vertex is a child of `v` exactly when it is non-root and has parent
`v`.  This bridges the path-based `childrenOf` definition with incidence
counting in (5.31). -/
theorem mem_childrenOf_iff_ne_root_and_parentV_eq {t : PlaneTree}
    {v w : VPos t} :
    w ∈ childrenOf v ↔ w ≠ rootV t ∧ parentV w = v := by
  rw [mem_childrenOf]
  constructor
  · rintro ⟨hlen, hpre⟩
    constructor
    · intro hw
      subst w
      simp [rootV] at hlen
    · rcases hpre with ⟨q, hqeq⟩
      have hlenEq := congrArg List.length hqeq
      have hqlen : q.length = 1 := by
        simp at hlenEq
        omega
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hqlen
      apply Subtype.ext
      change w.1.dropLast = v.1
      rw [← hqeq]
      simp
  · rintro ⟨hne, hpar⟩
    have hval : w.1.dropLast = v.1 := congrArg Subtype.val hpar
    constructor
    · rw [← hval, List.length_dropLast]
      have hwlen : 0 < w.1.length :=
        List.length_pos_iff.mpr (ne_root_iff.mp hne)
      omega
    · rw [← hval]
      exact w.1.dropLast_prefix

/-- The branch children of `p` are the fiber over `p` of the parent map on
non-root branch nodes. -/
theorem branchChildren_eq_parentFiber {t : PlaneTree} (p : VPos t) :
    branchChildren p =
      ((BranchNodes t).erase (rootV t)).filter (fun w => parentV w = p) := by
  ext w
  simp only [branchChildren, Finset.mem_inter,
    mem_childrenOf_iff_ne_root_and_parentV_eq, Finset.mem_filter,
    Finset.mem_erase]
  tauto

/-- Parent-incidence regrouping: every denominator scale in the ratio product
is counted once for each branch child. -/
theorem parent_incidence_product {t : PlaneTree} (ht : t.isValid = true)
    (N : VPos t → ℝ) :
    (∏ v ∈ (BranchNodes t).erase (rootV t),
        N (parentV v) ^ (2 : ℤ)) =
      ∏ p ∈ BranchNodes t,
        N p ^ ((2 : ℤ) * (branchChildren p).card) := by
  have hmap : ∀ v ∈ (BranchNodes t).erase (rootV t),
      parentV v ∈ BranchNodes t := by
    intro v hv
    exact parentV_mem_BranchNodes_of_branch ht
      (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
  rw [← Finset.prod_fiberwise_of_maps_to hmap
    (fun v => N (parentV v) ^ (2 : ℤ))]
  apply Finset.prod_congr rfl
  intro p _
  rw [← branchChildren_eq_parentFiber p]
  calc
    (∏ v ∈ branchChildren p, N (parentV v) ^ (2 : ℤ)) =
        ∏ _v ∈ branchChildren p, N p ^ (2 : ℤ) := by
          apply Finset.prod_congr rfl
          intro v hv
          rw [(mem_childrenOf_iff_ne_root_and_parentV_eq.mp
            (Finset.mem_inter.mp hv).1).2]
    _ = N p ^ ((2 : ℤ) * (branchChildren p).card) := by
      rw [Finset.prod_const, ← zpow_natCast, ← zpow_mul]

/-- The numerator of the parent-ratio product contributes power two at every
non-root branch node and power zero at the root. -/
theorem nonroot_branch_product {t : PlaneTree}
    (hroot : rootV t ∈ BranchNodes t) (N : VPos t → ℝ) :
    (∏ v ∈ (BranchNodes t).erase (rootV t), N v ^ (2 : ℤ)) =
      ∏ p ∈ BranchNodes t,
        N p ^ (if p = rootV t then (0 : ℤ) else 2) := by
  rw [← Finset.prod_erase_mul (BranchNodes t)
    (fun p => N p ^ (if p = rootV t then (0 : ℤ) else 2)) hroot]
  simp only [if_pos, zpow_zero, mul_one]
  apply Finset.prod_congr rfl
  intro v hv
  simp [(Finset.mem_erase.mp hv).1]

/-- The raw parent-ratio product regrouped as one power at each branch node.
This is the incidence step implicit in the paper's power count after (5.31). -/
theorem parent_ratio_product {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ v ∈ (BranchNodes t).erase (rootV t),
        (N v / N (parentV v)) ^ (2 : ℤ)) =
      ∏ p ∈ BranchNodes t,
        N p ^ ((if p = rootV t then (0 : ℤ) else 2) -
          (2 : ℤ) * (branchChildren p).card) := by
  calc
    (∏ v ∈ (BranchNodes t).erase (rootV t),
        (N v / N (parentV v)) ^ (2 : ℤ)) =
        (∏ v ∈ (BranchNodes t).erase (rootV t), N v ^ (2 : ℤ)) /
          ∏ v ∈ (BranchNodes t).erase (rootV t),
            N (parentV v) ^ (2 : ℤ) := by
              simp_rw [div_zpow]
              exact Finset.prod_div_distrib _ _
    _ = (∏ p ∈ BranchNodes t,
          N p ^ (if p = rootV t then (0 : ℤ) else 2)) /
        ∏ p ∈ BranchNodes t,
          N p ^ ((2 : ℤ) * (branchChildren p).card) := by
            rw [nonroot_branch_product hroot N,
              parent_incidence_product ht N]
    _ = ∏ p ∈ BranchNodes t,
        N p ^ ((if p = rootV t then (0 : ℤ) else 2) -
          (2 : ℤ) * (branchChildren p).card) := by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [zpow_sub₀ (ne_of_gt (hN p hp))]

/-- The uncollected left side of (5.31), including its extra root factor,
equals the product with the collected left exponent. -/
theorem allSimple_lhs_product_eq_collected {t : PlaneTree}
    (hroot : rootV t ∈ BranchNodes t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ v ∈ BranchNodes t,
        N v ^ ((-4 : ℤ) * ((childrenOf v).card - 1))) *
        N (rootV t) ^ (-2 : ℤ) =
      ∏ v ∈ BranchNodes t, N v ^ allSimpleLhsExponent v := by
  have hind :
      (∏ v ∈ BranchNodes t,
        N v ^ (if v = rootV t then (-2 : ℤ) else 0)) =
          N (rootV t) ^ (-2 : ℤ) := by
    simp [hroot]
  rw [← hind, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  rw [← zpow_add₀ (ne_of_gt (hN v hv))]
  congr 1
  by_cases hvr : v = rootV t <;>
    simp [allSimpleLhsExponent, hvr] <;> ring

/-- The uncollected right side of (5.31), including its parent ratios,
equals the product with the collected right exponent. -/
theorem allSimple_rhs_product_eq_collected {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ v ∈ BranchNodes t,
        N v ^ ((-2 : ℤ) * ((gamma2 mu ∅ v : ℤ) - 1))) *
        (∏ v ∈ (BranchNodes t).erase (rootV t),
          (N v / N (parentV v)) ^ (2 : ℤ)) =
      ∏ v ∈ BranchNodes t, N v ^ allSimpleRhsExponent mu v := by
  rw [parent_ratio_product ht hroot N hN, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  rw [← zpow_add₀ (ne_of_gt (hN v hv))]
  congr 1
  by_cases hvr : v = rootV t <;>
    simp [allSimpleRhsExponent, hvr] <;> ring

/-- Paper (5.31) in its direct, uncollected form.  The hypotheses state that
the Hepp tree is valid, its root is a branch node, and all branch scales are
positive. -/
theorem allSimple_direct_product_identity {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ v ∈ BranchNodes t,
        N v ^ ((-4 : ℤ) * ((childrenOf v).card - 1))) *
        N (rootV t) ^ (-2 : ℤ) =
      (∏ v ∈ BranchNodes t,
        N v ^ ((-2 : ℤ) * ((gamma2 mu ∅ v : ℤ) - 1))) *
        ∏ v ∈ (BranchNodes t).erase (rootV t),
          (N v / N (parentV v)) ^ (2 : ℤ) := by
  calc
    _ = ∏ v ∈ BranchNodes t, N v ^ allSimpleLhsExponent v :=
      allSimple_lhs_product_eq_collected hroot N hN
    _ = ∏ v ∈ BranchNodes t, N v ^ allSimpleRhsExponent mu v :=
      allSimple_product_identity ht mu N hN
    _ = _ := (allSimple_rhs_product_eq_collected ht hroot mu N hN).symm
end Anderson4D
