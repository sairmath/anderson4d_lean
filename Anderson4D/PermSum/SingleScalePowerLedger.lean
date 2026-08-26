import Anderson4D.PermSum.SingleScaleReduction

/-!
# The power ledger in paper equation (5.71)

This file lifts the nodewise exponent identity already proved in
`SingleScaleSetup` to the direct finite-product identity used in Step 1 of
Proposition 5.10.  The distinguished leaf is kept explicit.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Branch nodes whose subtree does not contain the distinguished leaf. -/
def branchesOffLeafPath {t : PlaneTree} (l₀ : HeppLeaf t) :
    Finset (VPos t) :=
  (BranchNodes t).filter fun v => ¬v.1 <+: l₀.1.1

/-- A branch child is off the distinguished path exactly when its subtree
does not contain the distinguished leaf. -/
def branchChildrenOffLeafPath {t : PlaneTree}
    (v : VPos t) (l₀ : HeppLeaf t) : Finset (VPos t) :=
  (branchChildren v).filter fun c => ¬c.1 <+: l₀.1.1

private theorem leaf_ne_root_of_root_branch {t : PlaneTree}
    (hroot : rootV t ∈ BranchNodes t) {l : VPos t}
    (hl : l ∈ Leaves t) :
    l ≠ rootV t := by
  intro h
  have hzero := mem_Leaves_iff.mp hl
  have htwo := mem_BranchNodes_iff.mp hroot
  rw [h] at hzero
  omega

private theorem prod_const_zpow_sum {ι : Type*} [DecidableEq ι]
    (x : ℝ) (hx : x ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    (∏ i ∈ s, x ^ e i) = x ^ ∑ i ∈ s, e i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
        zpow_add₀ hx]

/--
Regroup a product indexed by leaves according to their parent branch.
This is the incidence identity used for both the simple and compound
leaf factors in (5.71).
-/
private theorem leaf_parent_zpow_product
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (N : VPos t → ℝ) (hN : ∀ v ∈ BranchNodes t, 0 < N v)
    (s : Finset (VPos t)) (hs : s ⊆ Leaves t) (e : VPos t → ℤ) :
    (∏ l ∈ s, N (parentV l) ^ e l) =
      ∏ v ∈ BranchNodes t,
        N v ^ ∑ l ∈ s with parentV l = v, e l := by
  have hmap : ∀ l ∈ s, parentV l ∈ BranchNodes t := by
    intro l hl
    exact parentV_mem_BranchNodes_of_isValid ht
      (leaf_ne_root_of_root_branch hroot (hs hl))
  rw [← Finset.prod_fiberwise_of_maps_to hmap
    (fun l => N (parentV l) ^ e l)]
  apply Finset.prod_congr rfl
  intro v hv
  calc
    (∏ l ∈ s with parentV l = v,
        N (parentV l) ^ e l) =
        ∏ l ∈ s with parentV l = v, N v ^ e l := by
      apply Finset.prod_congr rfl
      intro l hl
      rw [(Finset.mem_filter.mp hl).2]
    _ = N v ^ ∑ l ∈ s with parentV l = v, e l :=
      prod_const_zpow_sum (N v) (ne_of_gt (hN v hv))
        (s.filter fun l => parentV l = v) e

private theorem branchChildrenOffLeafPath_eq_parentFiber
    {t : PlaneTree} (v : VPos t) (l₀ : HeppLeaf t) :
    branchChildrenOffLeafPath v l₀ =
      (branchesOffLeafPath l₀).filter fun c => parentV c = v := by
  ext c
  simp only [branchChildrenOffLeafPath, branchesOffLeafPath,
    Finset.mem_filter, branchChildren, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hcChild, hcBranch⟩, hcoff⟩
    exact ⟨⟨hcBranch, hcoff⟩,
      (mem_childrenOf_iff_ne_root_and_parentV_eq.mp hcChild).2⟩
  · rintro ⟨⟨hcBranch, hcoff⟩, hcparent⟩
    have hcne : c ≠ rootV t := by
      intro h
      subst c
      apply hcoff
      change ([] : List ℕ) <+: l₀.1.1
      exact List.nil_prefix
    exact ⟨⟨
      mem_childrenOf_iff_ne_root_and_parentV_eq.mpr ⟨hcne, hcparent⟩,
      hcBranch⟩, hcoff⟩

private theorem branchChildrenOffLeafPath_card
    {t : PlaneTree} (v : VPos t) (l₀ : HeppLeaf t) :
    (branchChildrenOffLeafPath v l₀).card =
      (branchChildren v).card -
        (branchChildrenTowardLeaf v l₀).card := by
  have hpartition :
      branchChildren v =
        branchChildrenOffLeafPath v l₀ ∪
          branchChildrenTowardLeaf v l₀ := by
    ext c
    simp [branchChildrenOffLeafPath, branchChildrenTowardLeaf]
    tauto
  have hdisj :
      Disjoint (branchChildrenOffLeafPath v l₀)
        (branchChildrenTowardLeaf v l₀) := by
    exact Finset.disjoint_left.mpr fun c hcOff hcOn =>
      (Finset.mem_filter.mp hcOff).2 (Finset.mem_filter.mp hcOn).2
  rw [hpartition, Finset.card_union_of_disjoint hdisj]
  omega

private theorem branchesOffLeafPath_mapsTo_parent
    {t : PlaneTree} (ht : t.isValid = true) (l₀ : HeppLeaf t) :
    ∀ v ∈ branchesOffLeafPath l₀, parentV v ∈ BranchNodes t := by
  intro v hv
  have hv' := Finset.mem_filter.mp hv
  apply parentV_mem_BranchNodes_of_branch ht hv'.1
  intro h
  subst v
  apply hv'.2
  change ([] : List ℕ) <+: l₀.1.1
  exact List.nil_prefix

/-- Collected exponent of one branch scale in the last ratio product of
paper (5.71). -/
def branchesOffLeafPathRatioExponent {t : PlaneTree}
    (v : VPos t) (l₀ : HeppLeaf t) : ℤ :=
  ((branchChildren v).card : ℤ) -
    ((branchChildrenTowardLeaf v l₀).card : ℤ) -
      if v.1 <+: l₀.1.1 then 0 else 1

private theorem branchesOffLeafPath_parent_product
    {t : PlaneTree} (ht : t.isValid = true)
    (l₀ : HeppLeaf t) (N : VPos t → ℝ) :
    (∏ v ∈ branchesOffLeafPath l₀, N (parentV v)) =
      ∏ p ∈ BranchNodes t,
        N p ^ ((branchChildrenOffLeafPath p l₀).card : ℤ) := by
  have hmap := branchesOffLeafPath_mapsTo_parent ht l₀
  rw [← Finset.prod_fiberwise_of_maps_to hmap
    (fun v => N (parentV v))]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [← branchChildrenOffLeafPath_eq_parentFiber p l₀]
  calc
    (∏ v ∈ branchChildrenOffLeafPath p l₀, N (parentV v)) =
        ∏ _v ∈ branchChildrenOffLeafPath p l₀, N p := by
      apply Finset.prod_congr rfl
      intro v hv
      exact congrArg N
        (mem_childrenOf_iff_ne_root_and_parentV_eq.mp
          (Finset.mem_inter.mp (Finset.mem_filter.mp hv).1).1).2
    _ = N p ^ ((branchChildrenOffLeafPath p l₀).card : ℤ) := by
      rw [Finset.prod_const, zpow_natCast]

private theorem branchesOffLeafPath_self_product
    {t : PlaneTree} (l₀ : HeppLeaf t) (N : VPos t → ℝ) :
    (∏ v ∈ branchesOffLeafPath l₀, N v) =
      ∏ p ∈ BranchNodes t,
        N p ^ (if p.1 <+: l₀.1.1 then (0 : ℤ) else 1) := by
  unfold branchesOffLeafPath
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases h : p.1 <+: l₀.1.1 <;> simp [h]

/--
The final ratio product in (5.71), regrouped as one integer power at every
branch node.
-/
theorem branchesOffLeafPath_ratio_product
    {t : PlaneTree} (ht : t.isValid = true)
    (l₀ : HeppLeaf t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ v ∈ branchesOffLeafPath l₀, N (parentV v) / N v) =
      ∏ p ∈ BranchNodes t,
        N p ^ branchesOffLeafPathRatioExponent p l₀ := by
  rw [Finset.prod_div_distrib,
    branchesOffLeafPath_parent_product ht l₀ N,
    branchesOffLeafPath_self_product l₀ N,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← zpow_sub₀ (ne_of_gt (hN p hp))]
  congr 1
  have hcard :
      (branchChildrenTowardLeaf p l₀).card ≤
        (branchChildren p).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hcast :
      (((branchChildren p).card -
          (branchChildrenTowardLeaf p l₀).card : ℕ) : ℤ) =
        ((branchChildren p).card : ℤ) -
          ((branchChildrenTowardLeaf p l₀).card : ℤ) := by
    omega
  rw [branchesOffLeafPathRatioExponent,
    branchChildrenOffLeafPath_card, hcast]

private theorem leafParentFiber_eq_children_inter
    {t : PlaneTree} (hroot : rootV t ∈ BranchNodes t)
    (s : Finset (VPos t)) (hs : s ⊆ Leaves t) (v : VPos t) :
    s.filter (fun l => parentV l = v) = childrenOf v ∩ s := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hls, hp⟩
    exact ⟨mem_childrenOf_iff_ne_root_and_parentV_eq.mpr
      ⟨leaf_ne_root_of_root_branch hroot (hs hls), hp⟩, hls⟩
  · rintro ⟨hlc, hls⟩
    exact ⟨hls,
      (mem_childrenOf_iff_ne_root_and_parentV_eq.mp hlc).2⟩

private theorem simpleLeaf_parent_product
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (compound : Finset (VPos t))
    (N : VPos t → ℝ) (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ l ∈ simpleLeaves t compound, N (parentV l) ^ (2 : ℤ)) =
      ∏ v ∈ BranchNodes t,
        N v ^ ((2 : ℤ) *
          (childrenOf v ∩ simpleLeaves t compound).card) := by
  have hs : simpleLeaves t compound ⊆ Leaves t := by
    intro l hl
    exact (Finset.mem_sdiff.mp hl).1
  rw [leaf_parent_zpow_product ht hroot N hN
    (simpleLeaves t compound) hs (fun _ => (2 : ℤ))]
  apply Finset.prod_congr rfl
  intro v _hv
  rw [leafParentFiber_eq_children_inter hroot
    (simpleLeaves t compound) hs v]
  simp [mul_comm]

private theorem compoundLeaf_parent_product
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (N : VPos t → ℝ) (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ l ∈ compoundLeaves t compound,
        N (parentV l) ^ (mu.m l : ℤ)) =
      ∏ v ∈ BranchNodes t,
        N v ^ ∑ l ∈ childrenOf v ∩ compoundLeaves t compound,
          (mu.m l : ℤ) := by
  have hs : compoundLeaves t compound ⊆ Leaves t := by
    intro l hl
    exact (Finset.mem_inter.mp hl).1
  rw [leaf_parent_zpow_product ht hroot N hN
    (compoundLeaves t compound) hs (fun l => (mu.m l : ℤ))]
  apply Finset.prod_congr rfl
  intro v _hv
  rw [leafParentFiber_eq_children_inter hroot
    (compoundLeaves t compound) hs v]

private theorem distinguishedLeaf_parent_product
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t) (l₀ : HeppLeaf t)
    (N : VPos t → ℝ) :
    N (parentV l₀.1) ^ (-1 : ℤ) =
      ∏ v ∈ BranchNodes t,
        N v ^ (if v = parentV l₀.1 then (-1 : ℤ) else 0) := by
  have hp : parentV l₀.1 ∈ BranchNodes t :=
    parentV_mem_BranchNodes_of_isValid ht
      (leaf_ne_root_of_root_branch hroot l₀.2)
  symm
  calc
    (∏ v ∈ BranchNodes t,
        N v ^ (if v = parentV l₀.1 then (-1 : ℤ) else 0)) =
        N (parentV l₀.1) ^
          (if parentV l₀.1 = parentV l₀.1 then (-1 : ℤ) else 0) :=
      Finset.prod_eq_single (s := BranchNodes t)
      (a := parentV l₀.1)
      (f := fun v => N v ^
        (if v = parentV l₀.1 then (-1 : ℤ) else 0))
      (fun b _hb hba => by simp [hba])
      (fun hnot => (hnot hp).elim)
    _ = N (parentV l₀.1) ^ (-1 : ℤ) := by simp

/--
The uncollected right side of (5.71) equals the product carrying the
nodewise exponent `paper571RhsExponent`.
-/
theorem paper571_rhs_product_eq_collected
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (l₀ : HeppLeaf t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ l ∈ simpleLeaves t compound,
        N (parentV l) ^ (2 : ℤ)) *
      (∏ l ∈ compoundLeaves t compound,
        N (parentV l) ^ (mu.m l : ℤ)) *
      N (parentV l₀.1) ^ (-1 : ℤ) *
      (∏ v ∈ branchesOffLeafPath l₀, N (parentV v) / N v) =
        ∏ v ∈ BranchNodes t,
          N v ^ paper571RhsExponent mu compound l₀ v := by
  rw [simpleLeaf_parent_product ht hroot compound N hN,
    compoundLeaf_parent_product ht hroot mu compound N hN,
    distinguishedLeaf_parent_product ht hroot l₀ N,
    branchesOffLeafPath_ratio_product ht l₀ N hN]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  rw [← zpow_add₀ (ne_of_gt (hN v hv)),
    ← zpow_add₀ (ne_of_gt (hN v hv)),
    ← zpow_add₀ (ne_of_gt (hN v hv))]
  congr 1
  unfold paper571RhsExponent branchesOffLeafPathRatioExponent
  push_cast
  have hparentPath :
      v = parentV l₀.1 → v.1 <+: l₀.1.1 := by
    intro hv
    rw [hv]
    have hlne : l₀.1 ≠ rootV t :=
      leaf_ne_root_of_root_branch hroot l₀.2
    exact (mem_childrenOf.mp
      (mem_childrenOf_iff_ne_root_and_parentV_eq.mpr
        ⟨hlne, rfl⟩)).2
  by_cases hpath : v.1 <+: l₀.1.1 <;>
    by_cases hparent : v = parentV l₀.1
  · simp only [if_pos hpath, if_pos hparent]
    ring
  · simp only [if_pos hpath, if_neg hparent]
    ring
  · exact (hpath (hparentPath hparent)).elim
  · simp only [if_neg hpath, if_neg hparent]
    ring

/-- **Paper equation (5.71)** in direct finite-product form. -/
theorem paper571_direct_product_identity
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (l₀ : HeppLeaf t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v) :
    (∏ v ∈ BranchNodes t,
        N v ^ ((gamma2 mu compound v : ℤ) - 1)) =
      (∏ l ∈ simpleLeaves t compound,
        N (parentV l) ^ (2 : ℤ)) *
      (∏ l ∈ compoundLeaves t compound,
        N (parentV l) ^ (mu.m l : ℤ)) *
      N (parentV l₀.1) ^ (-1 : ℤ) *
      ∏ v ∈ branchesOffLeafPath l₀, N (parentV v) / N v := by
  calc
    (∏ v ∈ BranchNodes t,
        N v ^ ((gamma2 mu compound v : ℤ) - 1)) =
        ∏ v ∈ BranchNodes t,
          N v ^ paper571RhsExponent mu compound l₀ v := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [paper571_exponent_identity ht mu compound l₀ hv]
    _ = _ :=
      (paper571_rhs_product_eq_collected
        ht hroot mu compound l₀ N hN).symm

/--
Paper (5.72)'s power inequality.  Squaring the inverse of (5.71) leaves an
extra negative square of the off-path parent ratios; it is at most one
because branch scales increase toward the root.
-/
theorem paper572_branchPower_le_leafPower
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (l₀ : HeppLeaf t) (N : VPos t → ℝ)
    (hN : ∀ v ∈ BranchNodes t, 0 < N v)
    (hmono : ∀ v ∈ BranchNodes t, v ≠ rootV t →
      N v ≤ N (parentV v)) :
    (∏ v ∈ BranchNodes t,
        N v ^ ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))) ≤
      (∏ l ∈ simpleLeaves t compound,
        N (parentV l) ^ (-4 : ℤ)) *
      (∏ l ∈ compoundLeaves t compound,
        N (parentV l) ^ ((-2 : ℤ) * (mu.m l : ℤ))) *
      N (parentV l₀.1) ^ (2 : ℤ) := by
  let A : ℝ :=
    ∏ v ∈ BranchNodes t,
      N v ^ ((gamma2 mu compound v : ℤ) - 1)
  let B : ℝ :=
    (∏ l ∈ simpleLeaves t compound,
      N (parentV l) ^ (2 : ℤ)) *
    (∏ l ∈ compoundLeaves t compound,
      N (parentV l) ^ (mu.m l : ℤ)) *
    N (parentV l₀.1) ^ (-1 : ℤ)
  let Q : ℝ :=
    ∏ v ∈ branchesOffLeafPath l₀, N (parentV v) / N v
  have hABQ : A = B * Q := by
    dsimp only [A, B, Q]
    exact paper571_direct_product_identity
      ht hroot mu compound l₀ N hN
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    apply Finset.one_le_prod
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    have hvne : v ≠ rootV t := by
      intro h
      subst v
      apply hv'.2
      change ([] : List ℕ) <+: l₀.1.1
      exact List.nil_prefix
    rw [one_le_div₀ (hN v hv'.1)]
    exact hmono v hv'.1 hvne
  have hQpow : Q ^ (-2 : ℤ) ≤ 1 :=
    zpow_le_one_of_nonpos₀ hQ (by norm_num)
  have hBpow : 0 ≤ B ^ (-2 : ℤ) := by positivity
  have hinv : A ^ (-2 : ℤ) ≤ B ^ (-2 : ℤ) := by
    rw [hABQ, mul_zpow]
    nlinarith [zpow_nonneg (le_trans zero_le_one hQ) (-2 : ℤ)]
  have hlhs :
      (∏ v ∈ BranchNodes t,
          N v ^ ((-2 : ℤ) *
            ((gamma2 mu compound v : ℤ) - 1))) =
        A ^ (-2 : ℤ) := by
    dsimp only [A]
    rw [← Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro v _hv
    rw [← zpow_mul]
    congr 1
    ring
  have hsimple :
      (∏ l ∈ simpleLeaves t compound,
          N (parentV l) ^ (2 : ℤ)) ^ (-2 : ℤ) =
        ∏ l ∈ simpleLeaves t compound,
          N (parentV l) ^ (-4 : ℤ) := by
    rw [← Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro l _hl
    rw [← zpow_mul]
    congr 1
  have hcompound :
      (∏ l ∈ compoundLeaves t compound,
          N (parentV l) ^ (mu.m l : ℤ)) ^ (-2 : ℤ) =
        ∏ l ∈ compoundLeaves t compound,
          N (parentV l) ^ ((-2 : ℤ) * (mu.m l : ℤ)) := by
    rw [← Finset.prod_zpow]
    apply Finset.prod_congr rfl
    intro l _hl
    rw [← zpow_mul]
    congr 1
    ring
  have hrhs :
      B ^ (-2 : ℤ) =
        (∏ l ∈ simpleLeaves t compound,
          N (parentV l) ^ (-4 : ℤ)) *
        (∏ l ∈ compoundLeaves t compound,
          N (parentV l) ^ ((-2 : ℤ) * (mu.m l : ℤ))) *
        N (parentV l₀.1) ^ (2 : ℤ) := by
    dsimp only [B]
    rw [mul_zpow, mul_zpow, hsimple, hcompound, ← zpow_mul]
    congr 2
  rw [hlhs, ← hrhs]
  exact hinv

/-- Specialization of the (5.72) power ledger to the dyadic Hepp marking. -/
theorem singleScale_branchPower_le_leafPower
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l₀ : HeppLeaf t) :
    (∏ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ^
          ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))) ≤
      (∏ l ∈ simpleLeaves t compound,
        (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ)) *
      (∏ l ∈ compoundLeaves t compound,
        (scaleN Nm (parentV l) : ℝ) ^
          ((-2 : ℤ) * (mu.m l : ℤ))) *
      (scaleN Nm (parentV l₀.1) : ℝ) ^ (2 : ℤ) := by
  apply paper572_branchPower_le_leafPower
    ht hroot mu compound l₀ (fun v => (scaleN Nm v : ℝ))
  · intro v _hv
    exact_mod_cast scaleN_pos Nm v
  · intro v hv hvroot
    have hmark := (Nm.parent_gt v hv hvroot).le
    exact_mod_cast Nat.pow_le_pow_right (by omega) hmark

/--
Quantitative form of the first reduction after (5.69): the missing cube of
the parent-scale-ratio product can be inserted at exponential cost.
-/
theorem one_le_uniformPower_mul_parentScaleRatioCube
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (hscale : SatisfiesSingleScaleCondition Nm mu) :
    1 ≤
      (8 * Real.exp 4) ^ (3 * totalMultiplicity mu) *
        ∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 3 := by
  let I : ℝ :=
    ∏ v ∈ nonrootBranches t, inverseParentScaleRatio Nm v
  let P : ℝ :=
    ∏ v ∈ nonrootBranches t, parentScaleRatio Nm v
  let K : ℝ := 8 * Real.exp 4
  have hI :
      I ≤ K ^ totalMultiplicity mu := by
    simpa only [I, K] using
      prod_inverseParentScaleRatio_le_uniform_power
        ht hroot Nm mu hscale
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact Finset.prod_nonneg fun v _ =>
      inverseParentScaleRatio_nonneg Nm v
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hIcube :
      I ^ 3 ≤ K ^ (3 * totalMultiplicity mu) := by
    calc
      I ^ 3 ≤ (K ^ totalMultiplicity mu) ^ 3 :=
        pow_le_pow_left₀ hI0 hI 3
      _ = K ^ (3 * totalMultiplicity mu) := by
        rw [← pow_mul]
        congr 1
        omega
  have hP0 : 0 ≤ P := by
    dsimp only [P, parentScaleRatio]
    positivity
  have hcancel : I * P = 1 := by
    dsimp only [I, P]
    rw [← Finset.prod_mul_distrib]
    simp only [inverseParentScaleRatio_mul_parentScaleRatio,
      Finset.prod_const_one]
  calc
    (1 : ℝ) = (I * P) ^ 3 := by rw [hcancel]; norm_num
    _ = I ^ 3 * P ^ 3 := by rw [mul_pow]
    _ ≤ K ^ (3 * totalMultiplicity mu) * P ^ 3 :=
      mul_le_mul_of_nonneg_right hIcube (pow_nonneg hP0 3)
    _ =
        (8 * Real.exp 4) ^ (3 * totalMultiplicity mu) *
          ∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 3 := by
      dsimp only [K, P]
      rw [← Finset.prod_pow]

end

end Anderson4D
