import Anderson4D.HeppTree.Automorphism
import Anderson4D.HeppTree.RealizedSets

/-!
# Geometric invariance under Hepp-tree automorphisms

This file proves that the path-based notions used by admissibility are
intrinsic to the parent graph.  In particular automorphisms preserve the
ancestor relation and least common ancestors.  These are the nontrivial
transport facts behind paper Proposition 5.6, Step 1.
-/

namespace Anderson4D

open PlaneTree

/-- Graph-theoretic ancestry: travel through zero or more child edges. -/
def IsAncestor {t : PlaneTree} (v w : VPos t) : Prop :=
  Relation.ReflTransGen (fun a b => b ∈ graphChildren a) v w

theorem IsAncestor.refl {t : PlaneTree} (v : VPos t) :
    IsAncestor v v :=
  Relation.ReflTransGen.refl

private theorem prefix_of_graphChild {t : PlaneTree}
    {v w : VPos t} (h : w ∈ graphChildren v) :
    v.1 <+: w.1 := by
  rw [mem_graphChildren] at h
  have hw0 : w.1 ≠ [] := by
    intro hw
    have hroot : w = rootV t := Subtype.ext hw
    have hp := h.1
    rw [hroot, parentV_rootV] at hp
    exact h.2 (hroot.trans hp)
  have heq : v.1 ++ [w.1.getLast hw0] = w.1 := by
    rw [← h.1]
    exact List.dropLast_append_getLast hw0
  rw [← heq]
  exact List.prefix_append _ _

/-- Graph ancestry is the same as prefix ancestry of position paths. -/
theorem IsAncestor.prefix {t : PlaneTree} {v w : VPos t}
    (h : IsAncestor v w) : v.1 <+: w.1 := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl a => exact List.prefix_rfl
  | single h => exact prefix_of_graphChild h
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem prefix_parent_of_prefix_ne {t : PlaneTree}
    {v w : VPos t} (hpre : v.1 <+: w.1) (hne : v ≠ w) :
    v.1 <+: (parentV w).1 := by
  let s := List.drop v.1.length w.1
  have heq : v.1 ++ s = w.1 :=
    List.prefix_iff_eq_append.mp hpre
  have hs : s ≠ [] := by
    intro hs
    apply hne
    apply Subtype.ext
    simpa [s, hs] using heq
  change v.1 <+: w.1.dropLast
  rw [← heq, List.dropLast_append_of_ne_nil hs]
  exact List.prefix_append _ _

/-- Conversely, every path prefix is a chain of graph-child edges. -/
theorem isAncestor_of_prefix {t : PlaneTree} (v w : VPos t)
    (hpre : v.1 <+: w.1) : IsAncestor v w := by
  generalize hn : w.1.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
      by_cases hvw : v = w
      · subst w
        exact IsAncestor.refl v
      · have hw0 : w.1 ≠ [] := by
          intro hw
          have hv0 : v.1 = [] := by
            exact List.prefix_nil.mp (hw ▸ hpre)
          exact hvw (Subtype.ext (hv0.trans hw.symm))
        have hparentPre : v.1 <+: (parentV w).1 :=
          prefix_parent_of_prefix_ne hpre hvw
        have hlen :
            (parentV w).1.length < n := by
          have hnpos : 0 < n := by
            have hwlen : w.1.length ≠ 0 := by
              simpa using hw0
            omega
          change w.1.dropLast.length < n
          rw [List.length_dropLast, hn]
          omega
        have hchain : IsAncestor v (parentV w) :=
          ih _ hlen (parentV w) hparentPre rfl
        have hneParent : w ≠ parentV w := by
          intro hw
          have hroot :=
            eq_rootV_of_parentV_eq (t := t) hw.symm
          exact hw0 (congrArg Subtype.val hroot)
        exact hchain.tail
          (mem_graphChildren.mpr ⟨rfl, hneParent⟩)

theorem isAncestor_iff_prefix {t : PlaneTree} (v w : VPos t) :
    IsAncestor v w ↔ v.1 <+: w.1 :=
  ⟨IsAncestor.prefix, isAncestor_of_prefix v w⟩

/-- Automorphisms preserve graph ancestry. -/
theorem IsAncestor.map_aut {t : PlaneTree} {v w : VPos t}
    (h : IsAncestor v w) (g : Aut t) :
    IsAncestor (g.1 v) (g.1 w) := by
  refine Relation.ReflTransGen.lift g.1 ?_ v w h
  intro a b hab
  have hb :
      g.1 b ∈ (graphChildren a).image g.1 :=
    Finset.mem_image.mpr ⟨b, hab, rfl⟩
  rw [image_graphChildren_aut] at hb
  exact hb

theorem isAncestor_aut_iff {t : PlaneTree}
    (g : Aut t) (v w : VPos t) :
    IsAncestor (g.1 v) (g.1 w) ↔ IsAncestor v w := by
  constructor
  · intro h
    have := h.map_aut (g⁻¹ : Aut t)
    simpa using this
  · exact fun h => h.map_aut g

private theorem prefix_lcaPath_of_prefix {r p q : List ℕ}
    (hp : r <+: p) (hq : r <+: q) :
    r <+: lcaPath p q := by
  induction r generalizing p q with
  | nil => exact List.nil_prefix
  | cons a r ih =>
      cases p with
      | nil => exact absurd hp (by simp)
      | cons b p =>
          cases q with
          | nil => exact absurd hq (by simp)
          | cons c q =>
              obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.mp hp
              obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.mp hq
              simp only [lcaPath, ↓reduceIte]
              exact List.cons_prefix_cons.mpr
                ⟨rfl, ih hp' hq'⟩

/-! ## Least common ancestors -/

theorem lcaV_ancestor_left {t : PlaneTree} (v w : VPos t) :
    IsAncestor (lcaV v w) v :=
  isAncestor_of_prefix _ _ (lcaPath_prefix_left v.1 w.1)

theorem lcaV_ancestor_right {t : PlaneTree} (v w : VPos t) :
    IsAncestor (lcaV v w) w :=
  isAncestor_of_prefix _ _ (lcaPath_prefix_right v.1 w.1)

/-- Universal property of the least common ancestor. -/
theorem IsAncestor.to_lcaV {t : PlaneTree} {u v w : VPos t}
    (huv : IsAncestor u v) (huw : IsAncestor u w) :
    IsAncestor u (lcaV v w) :=
  isAncestor_of_prefix _ _
    (prefix_lcaPath_of_prefix huv.prefix huw.prefix)

/-- Tree automorphisms preserve least common ancestors. -/
theorem lcaV_aut {t : PlaneTree} (g : Aut t) (v w : VPos t) :
    g.1 (lcaV v w) = lcaV (g.1 v) (g.1 w) := by
  have hxv : IsAncestor (g.1 (lcaV v w)) (g.1 v) :=
    (lcaV_ancestor_left v w).map_aut g
  have hxw : IsAncestor (g.1 (lcaV v w)) (g.1 w) :=
    (lcaV_ancestor_right v w).map_aut g
  have hxy :
      IsAncestor (g.1 (lcaV v w)) (lcaV (g.1 v) (g.1 w)) :=
    hxv.to_lcaV hxw
  have hyv : IsAncestor (lcaV (g.1 v) (g.1 w)) (g.1 v) :=
    lcaV_ancestor_left _ _
  have hyw : IsAncestor (lcaV (g.1 v) (g.1 w)) (g.1 w) :=
    lcaV_ancestor_right _ _
  have hyv' :
      IsAncestor ((g⁻¹ : Aut t).1 (lcaV (g.1 v) (g.1 w))) v := by
    simpa using hyv.map_aut (g⁻¹ : Aut t)
  have hyw' :
      IsAncestor ((g⁻¹ : Aut t).1 (lcaV (g.1 v) (g.1 w))) w := by
    simpa using hyw.map_aut (g⁻¹ : Aut t)
  have hyx' :
      IsAncestor
        ((g⁻¹ : Aut t).1 (lcaV (g.1 v) (g.1 w)))
        (lcaV v w) :=
    hyv'.to_lcaV hyw'
  have hyx :
      IsAncestor (lcaV (g.1 v) (g.1 w)) (g.1 (lcaV v w)) := by
    simpa using hyx'.map_aut g
  apply Subtype.ext
  exact antisymm hxy.prefix hyx.prefix

/-! ## Children and subtree leaves -/

/-- The path-based `childrenOf` is exactly the graph parent fiber. -/
theorem childrenOf_eq_graphChildren {t : PlaneTree} (v : VPos t) :
    childrenOf v = graphChildren v := by
  ext w
  rw [mem_childrenOf, mem_graphChildren]
  constructor
  · rintro ⟨hlen, hpre⟩
    let s := List.drop v.1.length w.1
    have heq : v.1 ++ s = w.1 :=
      List.prefix_iff_eq_append.mp hpre
    have hlens : s.length = 1 := by
      have := congrArg List.length heq
      simp only [List.length_append] at this
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlens
    constructor
    · apply Subtype.ext
      change w.1.dropLast = v.1
      rw [← heq, ha]
      simp
    · intro hwv
      have := congrArg (fun u : VPos t => u.1.length) hwv
      omega
  · rintro ⟨hparent, hne⟩
    have hpre : v.1 <+: w.1 :=
      prefix_of_graphChild (mem_graphChildren.mpr ⟨hparent, hne⟩)
    have hw0 : w.1 ≠ [] := by
      intro hw
      have hroot : w = rootV t := Subtype.ext hw
      rw [hroot, parentV_rootV] at hparent
      exact hne (hroot.trans hparent)
    have hlenParent := congrArg
      (fun u : VPos t => u.1.length) hparent
    change w.1.dropLast.length = v.1.length at hlenParent
    rw [List.length_dropLast] at hlenParent
    constructor
    · have hwpos : 0 < w.1.length := by
        have : w.1.length ≠ 0 := by simpa using hw0
        omega
      omega
    · exact hpre

/-- Automorphisms carry the children finset to the children finset. -/
theorem image_childrenOf_aut {t : PlaneTree}
    (g : Aut t) (v : VPos t) :
    (childrenOf v).image g.1 = childrenOf (g.1 v) := by
  rw [childrenOf_eq_graphChildren, childrenOf_eq_graphChildren,
    image_graphChildren_aut]

/-- Automorphisms carry all leaves below a vertex to all leaves below its
image. -/
theorem image_leavesUnder_aut {t : PlaneTree}
    (g : Aut t) (v : VPos t) :
    (leavesUnder v).image (autLeavesEquiv g) =
      leavesUnder (g.1 v) := by
  ext l
  constructor
  · intro hl
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hl
    rw [mem_leavesUnder] at hl' ⊢
    exact (isAncestor_of_prefix v l'.1 hl').map_aut g |>.prefix
  · intro hl
    let l' := (autLeavesEquiv g).symm l
    refine Finset.mem_image.mpr ⟨l', ?_, Equiv.apply_symm_apply _ l⟩
    rw [mem_leavesUnder]
    have hanc : IsAncestor (g.1 v) l.1 :=
      isAncestor_of_prefix _ _ (mem_leavesUnder.mp hl)
    have hback := hanc.map_aut (g⁻¹ : Aut t)
    simpa [l', autLeavesEquiv] using hback.prefix

/-! ## Admissible embeddings -/

/-- Reindex a leaf embedding by the induced leaf permutation. -/
def smulLeafEmbedding {t : PlaneTree} (g : Aut t)
    (z : LeafEmbedding t) : LeafEmbedding t :=
  reindexLeafEmbedding (autLeavesEquiv g) z

@[simp]
theorem smulLeafEmbedding_apply_aut {t : PlaneTree}
    (g : Aut t) (z : LeafEmbedding t)
    (l : {v // v ∈ Leaves t}) :
    smulLeafEmbedding g z (autLeavesEquiv g l) = z l := by
  simp [smulLeafEmbedding, reindexLeafEmbedding]

/-- One child link is preserved by simultaneous transport of the marking,
embedding, and vertices. -/
theorem IsLink.map_aut {t : PlaneTree} {Nm : HeppMarking t}
    {z : LeafEmbedding t} {v c c' : VPos t}
    (h : IsLink Nm z v c c') (g : Aut t) :
    IsLink (smulHeppMarking g Nm) (smulLeafEmbedding g z)
      (g.1 v) (g.1 c) (g.1 c') := by
  obtain ⟨l, hl, l', hl', hd⟩ := h
  let e := autLeavesEquiv g
  refine ⟨e l, ?_, e l', ?_, ?_⟩
  · have hm :
        e l ∈ (leavesUnder c).image e :=
      Finset.mem_image.mpr ⟨l, hl, rfl⟩
    rwa [image_leavesUnder_aut] at hm
  · have hm :
        e l' ∈ (leavesUnder c').image e :=
      Finset.mem_image.mpr ⟨l', hl', rfl⟩
    rwa [image_leavesUnder_aut] at hm
  · simpa [e, smulLeafEmbedding, reindexLeafEmbedding] using hd

/-- `LinkedChildren` is invariant in the forward direction under a tree
automorphism. -/
theorem LinkedChildren.map_aut {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (h : LinkedChildren Nm z v) (g : Aut t) :
    LinkedChildren (smulHeppMarking g Nm) (smulLeafEmbedding g z)
      (g.1 v) := by
  intro c hc c' hc'
  have hc0 :
      (g⁻¹ : Aut t).1 c ∈ childrenOf v := by
    have hm :
        (g⁻¹ : Aut t).1 c ∈
          (childrenOf (g.1 v)).image (g⁻¹ : Aut t).1 :=
      Finset.mem_image.mpr ⟨c, hc, rfl⟩
    simpa using
      (show (g⁻¹ : Aut t).1 c ∈ childrenOf ((g⁻¹ : Aut t).1 (g.1 v)) by
        rwa [image_childrenOf_aut] at hm)
  have hc0' :
      (g⁻¹ : Aut t).1 c' ∈ childrenOf v := by
    have hm :
        (g⁻¹ : Aut t).1 c' ∈
          (childrenOf (g.1 v)).image (g⁻¹ : Aut t).1 :=
      Finset.mem_image.mpr ⟨c', hc', rfl⟩
    simpa using
      (show (g⁻¹ : Aut t).1 c' ∈ childrenOf ((g⁻¹ : Aut t).1 (g.1 v)) by
        rwa [image_childrenOf_aut] at hm)
  have hmapped :
      Relation.ReflTransGen
        (fun a b =>
          a ∈ childrenOf (g.1 v) ∧ b ∈ childrenOf (g.1 v) ∧
            IsLink (smulHeppMarking g Nm) (smulLeafEmbedding g z)
              (g.1 v) a b)
        (g.1 ((g⁻¹ : Aut t).1 c))
        (g.1 ((g⁻¹ : Aut t).1 c')) := by
    refine Relation.ReflTransGen.lift g.1 ?_
      ((g⁻¹ : Aut t).1 c) ((g⁻¹ : Aut t).1 c')
      (h _ hc0 _ hc0')
    intro a b hab
    refine ⟨?_, ?_, hab.2.2.map_aut g⟩
    · have hm :
          g.1 a ∈ (childrenOf v).image g.1 :=
        Finset.mem_image.mpr ⟨a, hab.1, rfl⟩
      simpa [image_childrenOf_aut] using hm
    · have hm :
          g.1 b ∈ (childrenOf v).image g.1 :=
        Finset.mem_image.mpr ⟨b, hab.2.1, rfl⟩
      simpa [image_childrenOf_aut] using hm
  simpa using hmapped

/-- Admissibility is preserved by simultaneous automorphism transport. -/
theorem IsAdmissible.map_aut {t : PlaneTree}
    {Nm : HeppMarking t} {M : ℕ} {z : LeafEmbedding t}
    (h : IsAdmissible Nm M z) (g : Aut t) :
    IsAdmissible (smulHeppMarking g Nm) M
      (smulLeafEmbedding g z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l l' hll'
    apply (autLeavesEquiv g).symm.injective
    apply h.inj
    exact hll'
  · intro l l' hll'
    let e := autLeavesEquiv g
    have hne : e.symm l ≠ e.symm l' :=
      fun hEq => hll' (e.symm.injective hEq)
    have hsep := h.sep (e.symm l) (e.symm l') hne
    have hlca :
        (g⁻¹ : Aut t).1 (lcaV l.1 l'.1) =
          lcaV (e.symm l).1 (e.symm l').1 := by
      simpa [e, autLeavesEquiv] using
        lcaV_aut (g⁻¹ : Aut t) l.1 l'.1
    change
      (scaleN Nm ((g⁻¹ : Aut t).1 (lcaV l.1 l'.1)) : ℝ) / 2 ≤
        znorm
          (z ((autLeavesEquiv g).symm l) -
            z ((autLeavesEquiv g).symm l'))
    rw [hlca]
    simpa [e] using hsep
  · intro l i
    exact h.bounded ((autLeavesEquiv g).symm l) i
  · intro v hv
    have hv0 :
        (g⁻¹ : Aut t).1 v ∈ BranchNodes t :=
      (aut_mem_BranchNodes_iff (g⁻¹ : Aut t) v).mpr hv
    have hlinked :=
      (h.linked ((g⁻¹ : Aut t).1 v) hv0).map_aut g
    simpa using hlinked

end Anderson4D
