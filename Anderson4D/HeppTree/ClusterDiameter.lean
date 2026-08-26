import Anderson4D.HeppTree.Admissible
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Cluster diameter from the Hepp-tree link condition

This file formalizes paper §5.3 Step 4(a), equation (5.22a).  For a vertex
`v`, `tildeScale Nm v` is the sum of

`childCount(t,u) * scaleN(Nm,u)`

over branching descendants `u` of `v` (including `v` when it branches).
The paper writes the same index condition as “`v` is an ancestor of `u`”.
Here ancestry is the prefix relation on vertex-position lists.
-/

namespace Anderson4D

open PlaneTree

/-- Branching descendants of `v`, including `v` itself when it branches. -/
def branchDescendants {t : PlaneTree} (v : VPos t) : Finset (VPos t) :=
  (BranchNodes t).filter fun u => v.1 <+: u.1

@[simp] theorem mem_branchDescendants {t : PlaneTree} {v u : VPos t} :
    u ∈ branchDescendants v ↔
      u ∈ BranchNodes t ∧ v.1 <+: u.1 := by
  simp [branchDescendants]

/-- The accumulated scale from (5.22a).  It is `ℝ`-valued because it is
compared directly with `znorm`; every summand is the coercion of the paper's
integer quantity `#children(u) N_u`. -/
noncomputable def tildeScale {t : PlaneTree} (Nm : HeppMarking t)
    (v : VPos t) : ℝ :=
  ∑ u ∈ branchDescendants v,
    (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ)

theorem tildeScale_nonneg {t : PlaneTree} (Nm : HeppMarking t)
    (v : VPos t) :
    0 ≤ tildeScale Nm v := by
  unfold tildeScale
  positivity

/-- Moving downward in the tree can only remove summands from
`tildeScale`. -/
theorem tildeScale_mono_of_ancestor {t : PlaneTree}
    (Nm : HeppMarking t) {v w : VPos t}
    (hvw : v.1 <+: w.1) :
    tildeScale Nm w ≤ tildeScale Nm v := by
  unfold tildeScale
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    exact mem_branchDescendants.mpr
      ⟨(mem_branchDescendants.mp hu).1,
        hvw.trans (mem_branchDescendants.mp hu).2⟩
  · intro u _ _
    positivity

private theorem cd_isPos_append_singleton {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) {i : ℕ} (hi : i < childCount t p) :
    IsPos t (p ++ [i]) := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      rw [childCount] at hi
      simpa using (isPos_cons_iff.mpr ⟨hi, isPos_nil _⟩)
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨ha, hp'⟩ := isPos_cons_iff.mp hp
      rw [childCount, dif_pos ha] at hi
      rw [List.cons_append, isPos_cons_iff]
      exact ⟨ha, ih hp' hi⟩

private theorem cd_lt_childCount_of_isPos_append {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) {i : ℕ} (hi : IsPos t (p ++ [i])) :
    i < childCount t p := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      rw [childCount]
      simpa using (isPos_cons_iff.mp hi).1
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨ha, hp'⟩ := isPos_cons_iff.mp hp
      have hi' : IsPos cs[a] (p ++ [i]) := by
        convert (isPos_cons_iff.mp hi).2 using 1
        simp
      rw [childCount, dif_pos ha]
      exact ih hp' hi'

/-- Child number `i` of `v`, represented as a vertex position. -/
private def cd_childAt {t : PlaneTree} (v : VPos t)
    (i : Fin (childCount t v.1)) : VPos t :=
  ⟨v.1 ++ [i.1], cd_isPos_append_singleton v.2 i.2⟩

private theorem cd_childAt_mem_childrenOf {t : PlaneTree} (v : VPos t)
    (i : Fin (childCount t v.1)) :
    cd_childAt v i ∈ childrenOf v := by
  rw [mem_childrenOf]
  exact ⟨by simp [cd_childAt], List.prefix_append _ _⟩

private theorem cd_childAt_injective {t : PlaneTree} (v : VPos t) :
    Function.Injective (cd_childAt v) := by
  intro i j h
  have hp : v.1 ++ [i.1] = v.1 ++ [j.1] :=
    congrArg Subtype.val h
  have hs : [i.1] = [j.1] := List.append_inj_right hp rfl
  exact Fin.ext (List.singleton_inj.mp hs)

private theorem cd_child_path {t : PlaneTree} {v c : VPos t}
    (hc : c ∈ childrenOf v) :
    ∃ i : ℕ, c.1 = v.1 ++ [i] := by
  rw [mem_childrenOf] at hc
  let q := c.1.drop v.1.length
  have hq : v.1 ++ q = c.1 :=
    List.prefix_iff_eq_append.mp hc.2
  have hq_len : q.length = 1 := by
    dsimp [q]
    rw [List.length_drop]
    omega
  obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hq_len
  exact ⟨i, by rw [← hq, hi]⟩

private theorem cd_childAt_surj {t : PlaneTree} (v : VPos t)
    {c : VPos t} (hc : c ∈ childrenOf v) :
    ∃ i : Fin (childCount t v.1), cd_childAt v i = c := by
  obtain ⟨i, hi⟩ := cd_child_path hc
  have hipos : IsPos t (v.1 ++ [i]) := hi ▸ c.2
  let j : Fin (childCount t v.1) :=
    ⟨i, cd_lt_childCount_of_isPos_append v.2 hipos⟩
  exact ⟨j, Subtype.ext hi.symm⟩

/-- The finite set `childrenOf v` has the expected cardinality. -/
theorem card_childrenOf (t : PlaneTree) (v : VPos t) :
    (childrenOf v).card = childCount t v.1 := by
  symm
  simpa using
    (Finset.card_bij
      (s := (Finset.univ : Finset (Fin (childCount t v.1))))
      (t := childrenOf v)
      (fun i _ => cd_childAt v i)
      (fun i _ => cd_childAt_mem_childrenOf v i)
      (fun i _ j _ hij => cd_childAt_injective v hij)
      (fun c hc => by
        obtain ⟨i, rfl⟩ := cd_childAt_surj v hc
        exact ⟨i, Finset.mem_univ _, rfl⟩))

private theorem cd_isLink_symm {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    {v c c' : VPos t} (h : IsLink Nm z v c c') :
    IsLink Nm z v c' c := by
  obtain ⟨l, hl, l', hl', hd⟩ := h
  exact ⟨l', hl', l, hl, by simpa [znorm_sub_comm] using hd⟩

private def cd_childLinkRel {t : PlaneTree} (Nm : HeppMarking t)
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t)
    (c c' : VPos t) : Prop :=
  c ∈ childrenOf v ∧ c' ∈ childrenOf v ∧ IsLink Nm z v c c'

private noncomputable def cd_childLinkGraph {t : PlaneTree}
    (Nm : HeppMarking t)
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t) :
    SimpleGraph (VPos t) :=
  SimpleGraph.fromRel (cd_childLinkRel Nm z v)

private theorem cd_adj_iff {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v c c' : VPos t} :
    (cd_childLinkGraph Nm z v).Adj c c' ↔
      c ≠ c' ∧ cd_childLinkRel Nm z v c c' := by
  rw [cd_childLinkGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, h.2.1, h.1,
        cd_isLink_symm h.2.2⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

private theorem cd_reachable_of_linkedChildren
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v c c' : VPos t}
    (hlinked : LinkedChildren Nm z v)
    (hc : c ∈ childrenOf v) (hc' : c' ∈ childrenOf v) :
    (cd_childLinkGraph Nm z v).Reachable c c' := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  apply Relation.reflTransGen_closed
  intro a b hab
  by_cases h : a = b
  · subst b
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      (cd_adj_iff.mpr ⟨h, hab⟩)
  exact hlinked c hc c' hc'

private theorem cd_walk_support_subset_children
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v c c' : VPos t}
    (p : (cd_childLinkGraph Nm z v).Walk c c')
    (hc : c ∈ childrenOf v) :
    ∀ u ∈ p.support, u ∈ childrenOf v := by
  induction p with
  | nil =>
      simpa using hc
  | @cons a b _ hab p ih =>
      have hab' := (cd_adj_iff.mp hab).2
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      intro u hu
      rcases hu with rfl | hu
      · exact hab'.1
      · exact ih hab'.2.1 u hu

private theorem cd_path_length_le_childCount
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v c c' : VPos t}
    {p : (cd_childLinkGraph Nm z v).Walk c c'}
    (hp : p.IsPath) (hc : c ∈ childrenOf v) :
    p.length < childCount t v.1 := by
  have hsubset : p.support.toFinset ⊆ childrenOf v := by
    intro u hu
    exact cd_walk_support_subset_children p hc u
      (List.mem_toFinset.mp hu)
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hp.support_nodup,
    SimpleGraph.Walk.length_support, card_childrenOf] at hcard
  omega

private theorem cd_znorm_add_le (a b : Fin 4 → ℤ) :
    znorm (a + b) ≤ znorm a + znorm b := by
  unfold znorm
  have h : (fun i => (((a + b) i) : ℝ)) =
      (fun i => ((a i : ℤ) : ℝ)) + (fun i => ((b i : ℤ) : ℝ)) := by
    funext i
    simp
  rw [h]
  exact norm_add_le _ _

private theorem cd_znorm_triangle (x y z : Fin 4 → ℤ) :
    znorm (x - z) ≤ znorm (x - y) + znorm (y - z) := by
  have h : x - z = (x - y) + (y - z) := by
    abel
  rw [h]
  exact cd_znorm_add_le _ _

/-- Every leaf below a non-leaf vertex lies below one of its immediate
children. -/
private theorem cd_exists_childAt_of_mem_leavesUnder
    {t : PlaneTree} {v : VPos t} {l : {w // w ∈ Leaves t}}
    (hv : 0 < childCount t v.1) (hl : l ∈ leavesUnder v) :
    ∃ i : Fin (childCount t v.1), l ∈ leavesUnder (cd_childAt v i) := by
  have hne : v.1 ≠ l.1.1 := by
    intro h
    have hzero : childCount t v.1 = 0 := by
      rw [h]
      exact mem_Leaves_iff.mp l.2
    omega
  let q := l.1.1.drop v.1.length
  have hq : v.1 ++ q = l.1.1 :=
    List.prefix_iff_eq_append.mp (mem_leavesUnder.mp hl)
  have hqne : q ≠ [] := by
    intro hnil
    apply hne
    rw [hnil] at hq
    simpa using hq
  obtain ⟨i, q', hqform⟩ := List.exists_cons_of_ne_nil hqne
  rw [hqform] at hq
  have hipos : IsPos t (v.1 ++ [i]) := by
    apply IsPos_of_prefix l.1.2
    rw [← hq]
    simp
  let j : Fin (childCount t v.1) :=
    ⟨i, cd_lt_childCount_of_isPos_append v.2 hipos⟩
  refine ⟨j, ?_⟩
  rw [mem_leavesUnder]
  change v.1 ++ [i] <+: l.1.1
  rw [← hq]
  simp

private theorem cd_walk_distance_le
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v c c' : VPos t}
    {p : (cd_childLinkGraph Nm z v).Walk c c'}
    (hp : p.IsPath)
    (hc : c ∈ childrenOf v)
    (hlocal : ∀ d ∈ childrenOf v,
      ∀ a ∈ leavesUnder d, ∀ b ∈ leavesUnder d,
        znorm (z a - z b) ≤ tildeScale Nm d)
    {l l' : {w // w ∈ Leaves t}}
    (hl : l ∈ leavesUnder c) (hl' : l' ∈ leavesUnder c') :
    znorm (z l - z l') ≤
      ∑ d ∈ p.support.toFinset, tildeScale Nm d
        + (p.length : ℝ) * (scaleN Nm v : ℝ) := by
  induction p generalizing l with
  | nil =>
      simpa using hlocal _ hc l hl l' hl'
  | @cons a b e hab q ih =>
      have hp' :
          q.IsPath ∧ a ∉ q.support :=
        (SimpleGraph.Walk.cons_isPath_iff hab q).mp hp
      have hrel : cd_childLinkRel Nm z v a b :=
        (cd_adj_iff.mp hab).2
      obtain ⟨x, hx, y, hy, hxy⟩ := hrel.2.2
      have hstart :
          znorm (z l - z x) ≤ tildeScale Nm a :=
        hlocal a hrel.1 l hl x hx
      have htail :
          znorm (z y - z l') ≤
            ∑ d ∈ q.support.toFinset, tildeScale Nm d
              + (q.length : ℝ) * (scaleN Nm v : ℝ) :=
        ih hp'.1 hrel.2.1 hy hl'
      have htri₁ := cd_znorm_triangle (z l) (z x) (z l')
      have htri₂ := cd_znorm_triangle (z x) (z y) (z l')
      calc
        znorm (z l - z l') ≤
            tildeScale Nm a + (scaleN Nm v : ℝ) +
              (∑ d ∈ q.support.toFinset, tildeScale Nm d
                + (q.length : ℝ) * (scaleN Nm v : ℝ)) := by
                  linarith
        _ = ∑ d ∈ (SimpleGraph.Walk.cons hab q).support.toFinset,
              tildeScale Nm d
              + ((SimpleGraph.Walk.cons hab q).length : ℝ) *
                (scaleN Nm v : ℝ) := by
                  have ha : a ∉ q.support.toFinset := by
                    simpa using hp'.2
                  simp [ha]
                  ring

private theorem cd_branchDescendants_disjoint_of_children_ne
    {t : PlaneTree} {v c c' : VPos t}
    (hc : c ∈ childrenOf v) (hc' : c' ∈ childrenOf v)
    (hne : c ≠ c') :
    Disjoint (branchDescendants c) (branchDescendants c') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  have hcu := (mem_branchDescendants.mp hu).2
  have hcu' := (mem_branchDescendants.mp hu').2
  have hlen : c.1.length = c'.1.length := by
    rw [(mem_childrenOf.mp hc).1, (mem_childrenOf.mp hc').1]
  apply hne
  apply Subtype.ext
  rw [List.prefix_iff_eq_take] at hcu hcu'
  calc
    c.1 = u.1.take c.1.length := hcu
    _ = u.1.take c'.1.length := by rw [hlen]
    _ = c'.1 := hcu'.symm

private theorem cd_biUnion_branchDescendants_subset_erase
    {t : PlaneTree} {v : VPos t} (S : Finset (VPos t))
    (hS : S ⊆ childrenOf v) :
    S.biUnion branchDescendants ⊆ (branchDescendants v).erase v := by
  intro u hu
  obtain ⟨c, hcS, huc⟩ := Finset.mem_biUnion.mp hu
  have hc := hS hcS
  rw [Finset.mem_erase]
  constructor
  · intro huv
    subst u
    have hle :=
      (mem_branchDescendants.mp huc).2.length_le
    have hlen := (mem_childrenOf.mp hc).1
    omega
  · exact mem_branchDescendants.mpr
      ⟨(mem_branchDescendants.mp huc).1,
        (mem_childrenOf.mp hc).2.trans
          (mem_branchDescendants.mp huc).2⟩

private theorem cd_sum_tildeScale_support_le_erase
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v c c' : VPos t}
    (p : (cd_childLinkGraph Nm z v).Walk c c')
    (hc : c ∈ childrenOf v) :
    ∑ d ∈ p.support.toFinset, tildeScale Nm d ≤
      ∑ u ∈ (branchDescendants v).erase v,
        (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) := by
  have hsupport : p.support.toFinset ⊆ childrenOf v := by
    intro d hd
    exact cd_walk_support_subset_children p hc d
      (List.mem_toFinset.mp hd)
  have hpair :
      (↑p.support.toFinset : Set (VPos t)).PairwiseDisjoint
        branchDescendants := by
    intro a ha b hb hne
    exact cd_branchDescendants_disjoint_of_children_ne
      (hsupport ha) (hsupport hb) hne
  change
    ∑ d ∈ p.support.toFinset,
        ∑ u ∈ branchDescendants d,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) ≤ _
  rw [← Finset.sum_biUnion hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (cd_biUnion_branchDescendants_subset_erase
      p.support.toFinset hsupport)
    (fun _ _ _ => by positivity)

/-- Recursive branch step behind (5.22a): if the diameter estimate is known
inside every immediate child cluster, the `LinkedChildren` condition gives
the estimate at the branch itself.  A simple path in the finite child-link
graph is used, so every child-cluster contribution is charged at most once
and the number of link edges is strictly smaller than `childCount t v.1`. -/
theorem clusterDiameter_branch_step
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t)
    (hadm : IsAdmissible Nm M z)
    (hlocal : ∀ c ∈ childrenOf v,
      ∀ l ∈ leavesUnder c, ∀ l' ∈ leavesUnder c,
        znorm (z l - z l') ≤ tildeScale Nm c)
    {l l' : {w // w ∈ Leaves t}}
    (hl : l ∈ leavesUnder v) (hl' : l' ∈ leavesUnder v) :
    znorm (z l - z l') ≤ tildeScale Nm v := by
  have hcount : 2 ≤ childCount t v.1 :=
    mem_BranchNodes_iff.mp hv
  obtain ⟨i, hli⟩ :=
    cd_exists_childAt_of_mem_leavesUnder (lt_of_lt_of_le Nat.zero_lt_two hcount) hl
  obtain ⟨j, hlj⟩ :=
    cd_exists_childAt_of_mem_leavesUnder (lt_of_lt_of_le Nat.zero_lt_two hcount) hl'
  let c := cd_childAt v i
  let c' := cd_childAt v j
  have hc : c ∈ childrenOf v := cd_childAt_mem_childrenOf v i
  have hc' : c' ∈ childrenOf v := cd_childAt_mem_childrenOf v j
  have hreach :
      (cd_childLinkGraph Nm z v).Reachable c c' :=
    cd_reachable_of_linkedChildren (hadm.linked v hv) hc hc'
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hwalk :
      znorm (z l - z l') ≤
        ∑ d ∈ p.support.toFinset, tildeScale Nm d
          + (p.length : ℝ) * (scaleN Nm v : ℝ) :=
    cd_walk_distance_le hp hc hlocal hli hlj
  have hsum :
      ∑ d ∈ p.support.toFinset, tildeScale Nm d ≤
        ∑ u ∈ (branchDescendants v).erase v,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) :=
    cd_sum_tildeScale_support_le_erase p hc
  have hlength : p.length < childCount t v.1 :=
    cd_path_length_le_childCount hp hc
  have hlength' : (p.length : ℝ) ≤ childCount t v.1 := by
    exact_mod_cast Nat.le_of_lt hlength
  have hmul :
      (p.length : ℝ) * (scaleN Nm v : ℝ) ≤
        (childCount t v.1 : ℝ) * (scaleN Nm v : ℝ) := by
    gcongr
  have hvdesc : v ∈ branchDescendants v :=
    mem_branchDescendants.mpr ⟨hv, List.prefix_rfl⟩
  have hsplit :
      (∑ u ∈ (branchDescendants v).erase v,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ)) +
          (childCount t v.1 : ℝ) * (scaleN Nm v : ℝ) =
        tildeScale Nm v := by
    unfold tildeScale
    exact Finset.sum_erase_add _ _ hvdesc
  linarith

/-- A valid position path has length strictly smaller than the number of
vertices of its tree.  This supplies a well-founded measure for recursion
down immediate children. -/
private theorem cd_isPos_length_lt_size {t : PlaneTree} {p : Pos}
    (hp : IsPos t p) :
    p.length < t.size := by
  induction p generalizing t with
  | nil =>
      obtain ⟨cs⟩ := t
      simp [PlaneTree.size]
  | cons a p ih =>
      obtain ⟨cs⟩ := t
      obtain ⟨ha, hp'⟩ := isPos_cons_iff.mp hp
      let i : Fin cs.length := ⟨a, ha⟩
      have hih₀ : p.length < cs[a].size := ih hp'
      have hih : p.length < (cs.get i).size := by
        simpa [i] using hih₀
      have hmem : (cs.get i).size ∈ cs.map PlaneTree.size :=
        List.mem_map.mpr ⟨cs.get i, List.get_mem cs i, rfl⟩
      have hle : (cs.get i).size ≤
          (cs.map PlaneTree.size).sum :=
        List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
      rw [PlaneTree.size, PlaneTree.sizeList_eq_map]
      simp only [List.length_cons]
      omega

private theorem cd_eq_vertex_of_leaf_under_leaf
    {t : PlaneTree} {v : VPos t} {l : {w // w ∈ Leaves t}}
    (hv : childCount t v.1 = 0) (hl : l ∈ leavesUnder v) :
    l.1 = v := by
  apply Subtype.ext
  by_contra hne
  let q := l.1.1.drop v.1.length
  have hq : v.1 ++ q = l.1.1 :=
    List.prefix_iff_eq_append.mp (mem_leavesUnder.mp hl)
  have hqne : q ≠ [] := by
    intro hnil
    apply hne
    rw [hnil] at hq
    simpa using hq.symm
  obtain ⟨i, q', hqform⟩ := List.exists_cons_of_ne_nil hqne
  rw [hqform] at hq
  have hipos : IsPos t (v.1 ++ [i]) := by
    apply IsPos_of_prefix l.1.2
    rw [← hq]
    simp
  have hi := cd_lt_childCount_of_isPos_append v.2 hipos
  omega

private theorem cd_clusterDiameter_aux
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (k : ℕ) :
    ∀ (v : VPos t), t.size - v.1.length = k →
      ∀ (l l' : {w // w ∈ Leaves t}),
        l ∈ leavesUnder v → l' ∈ leavesUnder v →
          znorm (z l - z l') ≤ tildeScale Nm v := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro v hk l l' hl hl'
      by_cases hzero : childCount t v.1 = 0
      · have hlv : l.1 = v :=
          cd_eq_vertex_of_leaf_under_leaf hzero hl
        have hlv' : l'.1 = v :=
          cd_eq_vertex_of_leaf_under_leaf hzero hl'
        have hll' : l = l' :=
          Subtype.ext (hlv.trans hlv'.symm)
        subst l'
        convert tildeScale_nonneg Nm v using 1
        simp [znorm]
      · by_cases hone : childCount t v.1 = 1
        · have hpos : 0 < childCount t v.1 := Nat.pos_of_ne_zero hzero
          obtain ⟨i, hli⟩ :=
            cd_exists_childAt_of_mem_leavesUnder hpos hl
          obtain ⟨j, hlj⟩ :=
            cd_exists_childAt_of_mem_leavesUnder hpos hl'
          have hij : i = j := by
            apply Fin.ext
            omega
          subst j
          let c := cd_childAt v i
          have hc : c ∈ childrenOf v :=
            cd_childAt_mem_childrenOf v i
          have hmeasure : t.size - c.1.length < k := by
            have hvsize := cd_isPos_length_lt_size v.2
            have hclen := (mem_childrenOf.mp hc).1
            rw [← hk]
            omega
          have hrec :
              znorm (z l - z l') ≤ tildeScale Nm c :=
            ih (t.size - c.1.length) hmeasure c rfl l l' hli hlj
          exact hrec.trans
            (tildeScale_mono_of_ancestor Nm (mem_childrenOf.mp hc).2)
        · have hvbranch : v ∈ BranchNodes t :=
            mem_BranchNodes_iff.mpr (by omega)
          apply clusterDiameter_branch_step hvbranch hadm ?_ hl hl'
          intro c hc a ha b hb
          have hmeasure : t.size - c.1.length < k := by
            have hvsize := cd_isPos_length_lt_size v.2
            have hclen := (mem_childrenOf.mp hc).1
            rw [← hk]
            omega
          exact ih (t.size - c.1.length) hmeasure c rfl a b ha hb

/-- **Cluster diameter bound, paper (5.22a).**  In an admissible embedding,
any two leaves below `v` are separated by at most the accumulated descendant
scale `tildeScale Nm v`.  The statement also covers non-Hepp-valid carriers:
a unary vertex simply inherits the estimate from its unique child. -/
theorem clusterDiameter_le_tildeScale
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (v : VPos t)
    {l l' : {w // w ∈ Leaves t}}
    (hl : l ∈ leavesUnder v) (hl' : l' ∈ leavesUnder v) :
    znorm (z l - z l') ≤ tildeScale Nm v :=
  cd_clusterDiameter_aux hadm (t.size - v.1.length) v rfl l l' hl hl'

end Anderson4D
