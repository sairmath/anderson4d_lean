import Anderson4D.PermSum.CollapseBoundary
import Anderson4D.PermSum.CollapseData

/-!
# Geometric transport through the Proposition 5.9 collapse

This file connects the structural subtree/contraction operations to the
embedding hypotheses used by Propositions 5.9 and 5.10.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Subtree incidence and scale transport -/

/-- The vertex inclusion of a rooted subtree, packaged as an embedding for
finite-set transport. -/
def subtreeVertexEmbedding {t : PlaneTree} (r : VPos t) :
    VPos (subtreeAt t r.1) ↪ VPos t where
  toFun := subtreeVertex r
  inj' := subtreeVertex_injective r

/-- Prepending the same path to both inputs commutes with their longest
common prefix. -/
theorem lcaPath_append_left (r p q : List ℕ) :
    lcaPath (r ++ p) (r ++ q) = r ++ lcaPath p q := by
  induction r with
  | nil => rfl
  | cons a r ih =>
      simp [lcaPath, ih]

/-- LCA is preserved by the rooted-subtree vertex inclusion. -/
theorem subtreeVertex_lcaV {t : PlaneTree} (r : VPos t)
    (v w : VPos (subtreeAt t r.1)) :
    subtreeVertex r (lcaV v w) =
      lcaV (subtreeVertex r v) (subtreeVertex r w) := by
  apply Subtype.ext
  change r.1 ++ lcaPath v.1 w.1 =
    lcaPath (r.1 ++ v.1) (r.1 ++ w.1)
  exact (lcaPath_append_left r.1 v.1 w.1).symm

/-- Children in a rooted subtree are exactly the original children of the
included vertex. -/
theorem map_childrenOf_subtreeVertex {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    (childrenOf v).map (subtreeVertexEmbedding r) =
      childrenOf (subtreeVertex r v) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, hxw⟩ := Finset.mem_map.mp hx
    rw [← hxw]
    rw [mem_childrenOf] at hw ⊢
    refine ⟨?_, ?_⟩
    · change (r.1 ++ w.1).length = (r.1 ++ v.1).length + 1
      simp only [List.length_append]
      omega
    · change r.1 ++ v.1 <+: r.1 ++ w.1
      have hsuffix := List.prefix_append_drop hw.2
      rw [hsuffix, ← List.append_assoc]
      exact List.prefix_append _ _
  · intro hx
    rw [mem_childrenOf] at hx
    have hrx : r.1 <+: x.1 :=
      (List.prefix_append r.1 v.1).trans hx.2
    let w : VPos (subtreeAt t r.1) :=
      (subtreeVertexEquiv r).symm ⟨x, hrx⟩
    have hwx : subtreeVertex r w = x := by
      exact congrArg (fun y : Descendants r => y.1)
        ((subtreeVertexEquiv r).apply_symm_apply ⟨x, hrx⟩)
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, ?_⟩
    · rw [mem_childrenOf]
      have hprefixed :
          (subtreeVertex r v).1 <+: (subtreeVertex r w).1 := by
        rw [hwx]
        exact hx.2
      have hprefix :
          v.1 <+: w.1 := by
        change r.1 ++ v.1 <+: r.1 ++ w.1 at hprefixed
        simpa using hprefixed.drop r.1.length
      refine ⟨?_, hprefix⟩
      have hlength := hx.1
      rw [← hwx] at hlength
      simp only [subtreeVertex_val, List.length_append] at hlength
      omega
    · simpa [subtreeVertexEmbedding] using hwx

/-- Membership form of `map_childrenOf_subtreeVertex`. -/
theorem mem_childrenOf_subtreeVertex_iff {t : PlaneTree} (r : VPos t)
    (v w : VPos (subtreeAt t r.1)) :
    w ∈ childrenOf v ↔ subtreeVertex r w ∈ childrenOf (subtreeVertex r v) := by
  rw [← map_childrenOf_subtreeVertex r v]
  simp [subtreeVertexEmbedding]

/-- Leaf children transport along the same inclusion. -/
theorem map_leafChildren_subtreeVertex {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    (leafChildren v).map (subtreeVertexEmbedding r) =
      leafChildren (subtreeVertex r v) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, hxw⟩ := Finset.mem_map.mp hx
    rw [leafChildren, Finset.mem_inter] at hw ⊢
    rw [← hxw]
    exact ⟨(mem_childrenOf_subtreeVertex_iff r v w).mp hw.1,
      (mem_Leaves_subtreeVertex_iff r w).mp hw.2⟩
  · intro hx
    rw [leafChildren, Finset.mem_inter] at hx
    have hrx : r.1 <+: x.1 :=
      (List.prefix_append r.1 v.1).trans
        (mem_childrenOf.mp hx.1).2
    let w : VPos (subtreeAt t r.1) :=
      (subtreeVertexEquiv r).symm ⟨x, hrx⟩
    have hwx : subtreeVertex r w = x := by
      exact congrArg (fun y : Descendants r => y.1)
        ((subtreeVertexEquiv r).apply_symm_apply ⟨x, hrx⟩)
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, ?_⟩
    · rw [leafChildren, Finset.mem_inter]
      refine ⟨(mem_childrenOf_subtreeVertex_iff r v w).mpr
        (by rw [hwx]; exact hx.1), ?_⟩
      exact (mem_Leaves_subtreeVertex_iff r w).mpr (by
        rw [hwx]
        exact hx.2)
    · simpa [subtreeVertexEmbedding] using hwx

/-- `γ^∞` is unchanged at every branch of the restricted subtree. -/
theorem gammaInf_restrictMultiplicities {t : PlaneTree}
    (mu : Multiplicities t) (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    gammaInf (restrictMultiplicities mu r) v =
      gammaInf mu (subtreeVertex r v) := by
  unfold gammaInf
  calc
    (childrenOf v).card +
          ∑ l ∈ leafChildren v,
            ((restrictMultiplicities mu r).m l - 1) =
        ((childrenOf v).map (subtreeVertexEmbedding r)).card +
          ∑ l ∈ (leafChildren v).map (subtreeVertexEmbedding r),
            (mu.m l - 1) := by
      rw [Finset.card_map, Finset.sum_map]
      rfl
    _ = (childrenOf (subtreeVertex r v)).card +
          ∑ l ∈ leafChildren (subtreeVertex r v), (mu.m l - 1) := by
      rw [map_childrenOf_subtreeVertex, map_leafChildren_subtreeVertex]

/-- Descendant branch sets transport exactly into the original tree. -/
theorem map_branchNodesUnder_subtreeVertex {t : PlaneTree} (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    (branchNodesUnder v).map (subtreeVertexEmbedding r) =
      branchNodesUnder (subtreeVertex r v) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, hxw⟩ := Finset.mem_map.mp hx
    rw [← hxw]
    rw [branchNodesUnder, Finset.mem_filter] at hw ⊢
    refine ⟨(mem_BranchNodes_subtreeVertex_iff r w).mp hw.1, ?_⟩
    change r.1 ++ v.1 <+: r.1 ++ w.1
    have hsuffix := List.prefix_append_drop hw.2
    rw [hsuffix, ← List.append_assoc]
    exact List.prefix_append _ _
  · intro hx
    rw [branchNodesUnder, Finset.mem_filter] at hx
    have hrx : r.1 <+: x.1 :=
      (List.prefix_append r.1 v.1).trans hx.2
    let w : VPos (subtreeAt t r.1) :=
      (subtreeVertexEquiv r).symm ⟨x, hrx⟩
    have hwx : subtreeVertex r w = x := by
      exact congrArg (fun y : Descendants r => y.1)
        ((subtreeVertexEquiv r).apply_symm_apply ⟨x, hrx⟩)
    apply Finset.mem_map.mpr
    refine ⟨w, ?_, ?_⟩
    · rw [branchNodesUnder, Finset.mem_filter]
      refine ⟨(mem_BranchNodes_subtreeVertex_iff r w).mpr
        (by rw [hwx]; exact hx.1), ?_⟩
      have hprefixed :
          (subtreeVertex r v).1 <+: (subtreeVertex r w).1 := by
        rw [hwx]
        exact hx.2
      change r.1 ++ v.1 <+: r.1 ++ w.1 at hprefixed
      simpa using hprefixed.drop r.1.length
    · simpa [subtreeVertexEmbedding] using hwx

/-- The accumulated scale is unchanged under restriction. -/
theorem accumulatedScale_restrict {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (r : VPos t)
    (v : VPos (subtreeAt t r.1)) :
    accumulatedScale (restrictMarking Nm r)
        (restrictMultiplicities mu r) v =
      accumulatedScale Nm mu (subtreeVertex r v) := by
  unfold accumulatedScale
  calc
    ∑ u ∈ branchNodesUnder v,
        gammaInf (restrictMultiplicities mu r) u *
          scaleN (restrictMarking Nm r) u =
      ∑ u ∈ (branchNodesUnder v).map (subtreeVertexEmbedding r),
        gammaInf mu u * scaleN Nm u := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro u hu
      simp only [gammaInf_restrictMultiplicities,
        scaleN_restrictMarking]
      rfl
    _ = ∑ u ∈ branchNodesUnder (subtreeVertex r v),
        gammaInf mu u * scaleN Nm u := by
      rw [map_branchNodesUnder_subtreeVertex]

/-! ## Restricted single-scale and embedding hypotheses -/

/-- A lowest eligible branch has no eligible proper descendant, hence its
restricted subtree satisfies the single-scale condition of Proposition 5.10. -/
theorem lowestEligible_restrict_singleScale {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {r : VPos t}
    (hr : IsLowestCollapseEligible Nm mu r) :
    SatisfiesSingleScaleCondition
      (restrictMarking Nm r) (restrictMultiplicities mu r) := by
  intro v hv
  have hvData := Finset.mem_erase.mp hv
  have hvRoot : v ≠ rootV (subtreeAt t r.1) := hvData.1
  have hvBranch : v ∈ BranchNodes (subtreeAt t r.1) := hvData.2
  let u : VPos t := subtreeVertex r v
  have huBranch : u ∈ BranchNodes t :=
    (mem_BranchNodes_subtreeVertex_iff r v).mp hvBranch
  have huNeR : u ≠ r := by
    intro h
    apply hvRoot
    apply (subtreeVertex_injective r)
    simpa [u] using h
  have huUnder : u ∈ branchNodesUnder r := by
    rw [branchNodesUnder, Finset.mem_filter]
    exact ⟨huBranch, List.prefix_append r.1 v.1⟩
  have huNeRoot : u ≠ rootV t := by
    intro h
    have hpath : r.1 ++ v.1 = [] := by
      have := congrArg Subtype.val h
      simpa [u, rootV] using this
    have hrPath : r.1 = [] := (List.append_eq_nil_iff.mp hpath).1
    have hrRoot : r = rootV t := by
      apply Subtype.ext
      simpa [rootV] using hrPath
    exact (Finset.mem_erase.mp hr.1.1).1 hrRoot
  have huNonroot : u ∈ nonrootBranches t :=
    Finset.mem_erase.mpr ⟨huNeRoot, huBranch⟩
  have hnotEligible := hr.2 u huUnder huNeR
  have hnotIneq :
      ¬8 * accumulatedScale Nm mu u ≤ scaleN Nm (parentV u) := by
    intro hineq
    exact hnotEligible ⟨huNonroot, hineq⟩
  rw [scaleN_restrictMarking, accumulatedScale_restrict,
    ← parentV_subtreeVertex r v hvRoot]
  change scaleN Nm (parentV u) ≤ 8 * accumulatedScale Nm mu u
  omega

/-- The parent scale of the collapsed root supplies exactly the dyadic
scale and root accumulated-scale bound needed by the restricted P-5.10 call. -/
theorem eligible_restrict_p5Parameters {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {r : VPos t}
    (hr : CollapseEligible Nm mu r) :
    IsDyadicNat (scaleN Nm (parentV r)) ∧
      accumulatedScale (restrictMarking Nm r)
          (restrictMultiplicities mu r)
          (rootV (subtreeAt t r.1)) ≤
        scaleN Nm (parentV r) := by
  constructor
  · exact scaleN_isDyadicNat Nm (parentV r)
  · rw [accumulatedScale_restrict, subtreeVertex_root]
    exact eligible_accumulated_le_parent hr

@[simp]
theorem restrictLeafEquiv_vertex {t : PlaneTree} (r : VPos t)
    (l : HeppLeaf (subtreeAt t r.1)) :
    (restrictLeafEquiv r l).1.1 = subtreeVertex r l.1 :=
  rfl

/-- Restriction preserves separatedness, including injectivity and the exact
LCA scale. -/
theorem isSeparatedEmbedding_restrict {t : PlaneTree}
    (Nm : HeppMarking t) (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) (hz : IsSeparatedEmbedding Nm z) :
    IsSeparatedEmbedding (restrictMarking Nm r)
      (restrictEmbedding z r) := by
  constructor
  · intro l l' hll'
    have horiginal :
        (restrictLeafEquiv r l).1 =
          (restrictLeafEquiv r l').1 := by
      apply hz.1
      exact hll'
    apply (restrictLeafEquiv r).injective
    exact Subtype.ext horiginal
  · intro l l' hne
    have horiginalNe :
        (restrictLeafEquiv r l).1 ≠
          (restrictLeafEquiv r l').1 := by
      intro h
      apply hne
      apply (restrictLeafEquiv r).injective
      exact Subtype.ext h
    have hsep :=
      hz.2 (restrictLeafEquiv r l).1
        (restrictLeafEquiv r l').1 horiginalNe
    simpa only [restrictEmbedding, scaleN_restrictMarking,
      restrictLeafEquiv_vertex, subtreeVertex_lcaV] using hsep

/-- Restriction preserves every subtree-diameter inequality exactly. -/
theorem satisfiesSubtreeDiameter_restrict {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (hz : SatisfiesSubtreeDiameter Nm mu z) :
    SatisfiesSubtreeDiameter (restrictMarking Nm r)
      (restrictMultiplicities mu r) (restrictEmbedding z r) := by
  intro v hv l hl l' hl'
  have hvOriginal :
      subtreeVertex r v ∈ BranchNodes t :=
    (mem_BranchNodes_subtreeVertex_iff r v).mp hv
  have hlOriginal :
      (restrictLeafEquiv r l).1 ∈ leavesUnder (subtreeVertex r v) := by
    rw [mem_leavesUnder]
    have hp := mem_leavesUnder.mp hl
    change r.1 ++ v.1 <+: r.1 ++ l.1.1
    have hsuffix := List.prefix_append_drop hp
    rw [hsuffix, ← List.append_assoc]
    exact List.prefix_append _ _
  have hlOriginal' :
      (restrictLeafEquiv r l').1 ∈ leavesUnder (subtreeVertex r v) := by
    rw [mem_leavesUnder]
    have hp := mem_leavesUnder.mp hl'
    change r.1 ++ v.1 <+: r.1 ++ l'.1.1
    have hsuffix := List.prefix_append_drop hp
    rw [hsuffix, ← List.append_assoc]
    exact List.prefix_append _ _
  have hdiam :=
    hz (subtreeVertex r v) hvOriginal
      (restrictLeafEquiv r l).1 hlOriginal
      (restrictLeafEquiv r l').1 hlOriginal'
  simpa only [restrictEmbedding, accumulatedScale_restrict] using hdiam

/-! ## Contracted embedding -/

/-- Extending the left input below `r` does not change its LCA with a path
outside `r`. -/
theorem lcaPath_append_tail_of_not_prefix (r tail q : List ℕ)
    (hq : ¬r <+: q) :
    lcaPath (r ++ tail) q = lcaPath r q := by
  induction r generalizing q with
  | nil =>
      exact (hq List.nil_prefix).elim
  | cons a r ih =>
      cases q with
      | nil => rfl
      | cons b q =>
          by_cases hab : a = b
          · subst b
            have hq' : ¬r <+: q := by
              intro h
              exact hq (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
            simp [lcaPath, ih q hq']
          · simp [lcaPath, hab]

/-- The original leaf represented by a contracted leaf: the marker is sent
to `lstar`, while outside leaves are unchanged. -/
def contractRepresentativeLeaf {t : PlaneTree} (r : VPos t)
    (lstar : InsideLeaf r) :
    HeppLeaf (contractAt t r.1) → HeppLeaf t :=
  fun l =>
    Sum.elim (fun _ : Unit => lstar.1)
      (fun lout : OutsideLeaf r => lout.1)
      (contractLeafSumEquiv r l)

@[simp]
theorem contractRepresentativeLeaf_marker {t : PlaneTree} (r : VPos t)
    (lstar : InsideLeaf r) :
    contractRepresentativeLeaf r lstar (contractMarkerLeaf r) = lstar.1 := by
  simp [contractRepresentativeLeaf]

@[simp]
theorem contractRepresentativeLeaf_outside {t : PlaneTree} (r : VPos t)
    (lstar : InsideLeaf r) (l : OutsideLeaf r) :
    contractRepresentativeLeaf r lstar (contractOutsideLeaf r l) = l.1 := by
  simp [contractRepresentativeLeaf]

/-- Contracting an embedding is composition with the representative-leaf
map. -/
theorem contractEmbedding_eq_comp_representative {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) :
    contractEmbedding z r lstar =
      z ∘ contractRepresentativeLeaf r lstar :=
  by
    funext l
    cases h : contractLeafSumEquiv r l with
    | inl u =>
        cases u
        simp [contractEmbedding, contractRepresentativeLeaf, h]
    | inr lout =>
        simp [contractEmbedding, contractRepresentativeLeaf, h]

/-- Choosing one inside representative and retaining every outside leaf is
an injective map on the contracted leaf carrier. -/
theorem contractRepresentativeLeaf_injective {t : PlaneTree}
    (r : VPos t) (lstar : InsideLeaf r) :
    Function.Injective (contractRepresentativeLeaf r lstar) := by
  intro l l' h
  apply (contractLeafSumEquiv r).injective
  cases hl : contractLeafSumEquiv r l with
  | inl u =>
      cases u
      cases hl' : contractLeafSumEquiv r l' with
      | inl u' =>
          cases u'
          rfl
      | inr lout =>
          exfalso
          apply lout.2
          have horiginal : lstar.1 = lout.1 := by
            simpa [contractRepresentativeLeaf, hl, hl'] using h
          rw [← horiginal]
          exact lstar.2
  | inr lout =>
      cases hl' : contractLeafSumEquiv r l' with
      | inl u =>
          cases u
          exfalso
          apply lout.2
          have horiginal : lout.1 = lstar.1 := by
            simpa [contractRepresentativeLeaf, hl, hl'] using h
          rw [horiginal]
          exact lstar.2
      | inr lout' =>
          have horiginal : lout.1 = lout'.1 := by
            simpa [contractRepresentativeLeaf, hl, hl'] using h
          exact congrArg Sum.inr (Subtype.ext horiginal)

/-- LCA transport for the marker and an unchanged outside leaf. -/
theorem contractVertex_lcaV_marker_outside {t : PlaneTree}
    (r : VPos t) (lstar : InsideLeaf r) (lout : OutsideLeaf r) :
    contractVertex r.2
        (lcaV (contractMarkerLeaf r).1 (contractOutsideLeaf r lout).1) =
      lcaV lstar.1.1 lout.1.1 := by
  apply Subtype.ext
  change lcaPath r.1 lout.1.1.1 =
    lcaPath lstar.1.1.1 lout.1.1.1
  have hsuffix := List.prefix_append_drop lstar.2
  rw [hsuffix]
  exact (lcaPath_append_tail_of_not_prefix
    r.1 (List.drop r.1.length lstar.1.1.1) lout.1.1.1 lout.2).symm

/-- LCA transport for two unchanged outside leaves. -/
theorem contractVertex_lcaV_outside_outside {t : PlaneTree}
    (r : VPos t) (lout lout' : OutsideLeaf r) :
    contractVertex r.2
        (lcaV (contractOutsideLeaf r lout).1
          (contractOutsideLeaf r lout').1) =
      lcaV lout.1.1 lout'.1.1 := by
  apply Subtype.ext
  rfl

/-- At distinct contracted leaves, the contracted LCA scale is exactly the
original LCA scale of their representatives. -/
theorem scaleN_lca_contractRepresentative_of_ne {t : PlaneTree}
    (Nm : HeppMarking t) (r : VPos t) (lstar : InsideLeaf r)
    {l l' : HeppLeaf (contractAt t r.1)} (hne : l ≠ l') :
    scaleN (contractMarking Nm r) (lcaV l.1 l'.1) =
      scaleN Nm
        (lcaV (contractRepresentativeLeaf r lstar l).1
          (contractRepresentativeLeaf r lstar l').1) := by
  rw [scaleN_contractMarking]
  cases hl : contractLeafSumEquiv r l with
  | inl u =>
      cases u
      have hlMarker : l = contractMarkerLeaf r := by
        apply (contractLeafSumEquiv r).injective
        rw [hl, contractLeafSumEquiv_marker]
      cases hl' : contractLeafSumEquiv r l' with
      | inl u' =>
          cases u'
          have hl'Marker : l' = contractMarkerLeaf r := by
            apply (contractLeafSumEquiv r).injective
            rw [hl', contractLeafSumEquiv_marker]
          exact (hne (hlMarker.trans hl'Marker.symm)).elim
      | inr lout =>
          have hl'Outside : l' = contractOutsideLeaf r lout := by
            apply (contractLeafSumEquiv r).injective
            rw [hl', contractLeafSumEquiv_contractOutsideLeaf]
          subst l
          subst l'
          rw [contractRepresentativeLeaf_marker,
            contractRepresentativeLeaf_outside,
            contractVertex_lcaV_marker_outside]
  | inr lout =>
      have hlOutside : l = contractOutsideLeaf r lout := by
        apply (contractLeafSumEquiv r).injective
        rw [hl, contractLeafSumEquiv_contractOutsideLeaf]
      cases hl' : contractLeafSumEquiv r l' with
      | inl u =>
          cases u
          have hl'Marker : l' = contractMarkerLeaf r := by
            apply (contractLeafSumEquiv r).injective
            rw [hl', contractLeafSumEquiv_marker]
          subst l
          subst l'
          simp only [contractRepresentativeLeaf_outside,
            contractRepresentativeLeaf_marker]
          rw [lcaV_comm (contractOutsideLeaf r lout).1
            (contractMarkerLeaf r).1,
            contractVertex_lcaV_marker_outside,
            lcaV_comm lstar.1.1 lout.1.1]
      | inr lout' =>
          have hl'Outside : l' = contractOutsideLeaf r lout' := by
            apply (contractLeafSumEquiv r).injective
            rw [hl', contractLeafSumEquiv_contractOutsideLeaf]
          subst l
          subst l'
          simp only [contractRepresentativeLeaf_outside]
          rw [contractVertex_lcaV_outside_outside]

/-- The contracted embedding remains separated.  Eligibility is not needed
for this structural fact; it enters the boundary-edge comparison below. -/
theorem isSeparatedEmbedding_contract {t : PlaneTree}
    (Nm : HeppMarking t) (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) (lstar : InsideLeaf r)
    (hz : IsSeparatedEmbedding Nm z) :
    IsSeparatedEmbedding (contractMarking Nm r)
      (contractEmbedding z r lstar) := by
  constructor
  · rw [contractEmbedding_eq_comp_representative]
    exact hz.1.comp (contractRepresentativeLeaf_injective r lstar)
  · intro l l' hne
    have hrepNe :
        contractRepresentativeLeaf r lstar l ≠
          contractRepresentativeLeaf r lstar l' :=
      (contractRepresentativeLeaf_injective r lstar).ne hne
    have hsep :=
      hz.2 (contractRepresentativeLeaf r lstar l)
        (contractRepresentativeLeaf r lstar l') hrepNe
    rw [scaleN_lca_contractRepresentative_of_ne Nm r lstar hne]
    simpa only [contractEmbedding_eq_comp_representative,
      Function.comp_apply] using hsep

/-- The eligible quarter-distance estimate expressed using the contracted
marker and an unchanged contracted outside leaf.  This is the geometric
input for charging every changed boundary edge by `2`. -/
theorem contractEmbedding_boundary_quarter {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    (l lstar : InsideLeaf r) (y : OutsideLeaf r) :
    4 * znorm
        (z l.1 -
          contractEmbedding z r lstar (contractMarkerLeaf r)) ≤
      znorm
        (contractEmbedding z r lstar (contractOutsideLeaf r y) -
          z l.1) := by
  have hy : y.1 ∉ leavesUnder r := by
    rw [mem_leavesUnder]
    exact y.2
  simpa only [contractEmbedding_apply_marker,
    contractEmbedding_apply_outside] using
    (eligible_boundary_quarter ht Nm mu z hsep hdiam hr
      (mem_leavesUnder.mpr l.2)
      (mem_leavesUnder.mpr lstar.2) hy)

/-- A contracted leaf below `v` represents an original leaf below the
unchanged original vertex corresponding to `v`. -/
theorem contractRepresentativeLeaf_mem_leavesUnder {t : PlaneTree}
    (r : VPos t) (lstar : InsideLeaf r)
    (v : VPos (contractAt t r.1))
    (l : HeppLeaf (contractAt t r.1))
    (hl : l ∈ leavesUnder v) :
    contractRepresentativeLeaf r lstar l ∈
      leavesUnder (contractVertex r.2 v) := by
  rw [mem_leavesUnder] at hl ⊢
  cases he : contractLeafSumEquiv r l with
  | inl u =>
      cases u
      have hlMarker : l = contractMarkerLeaf r := by
        apply (contractLeafSumEquiv r).injective
        rw [he, contractLeafSumEquiv_marker]
      subst l
      simp only [contractRepresentativeLeaf_marker]
      change v.1 <+: lstar.1.1.1
      have hvr : v.1 <+: r.1 := by
        simpa [contractMarkerLeaf, contractMarker] using hl
      exact hvr.trans lstar.2
  | inr lout =>
      have hlOutside : l = contractOutsideLeaf r lout := by
        apply (contractLeafSumEquiv r).injective
        rw [he, contractLeafSumEquiv_contractOutsideLeaf]
      subst l
      simp only [contractRepresentativeLeaf_outside]
      change v.1 <+: lout.1.1.1
      rw [← contractVertex_contractOutsideLeaf r lout]
      exact hl

/-- Diameter transport through contraction, isolated at its exact remaining
arithmetic input: the contracted accumulated scale must dominate the
original accumulated scale at every surviving branch.  The leaf geometry
and all carrier transport are discharged here; a later `γ^∞` collapse ledger
can supply `haccumulated`. -/
theorem satisfiesSubtreeDiameter_contract_of_accumulatedScale {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (r : VPos t) (lstar : InsideLeaf r)
    (s : ℕ) (hs : 1 ≤ s)
    (hz : SatisfiesSubtreeDiameter Nm mu z)
    (haccumulated :
      ∀ v ∈ BranchNodes (contractAt t r.1),
        accumulatedScale Nm mu (contractVertex r.2 v) ≤
          accumulatedScale (contractMarking Nm r)
            (contractMultiplicities mu r s hs) v) :
    SatisfiesSubtreeDiameter (contractMarking Nm r)
      (contractMultiplicities mu r s hs)
      (contractEmbedding z r lstar) := by
  intro v hv l hl l' hl'
  have hlOriginal :=
    contractRepresentativeLeaf_mem_leavesUnder r lstar v l hl
  have hlOriginal' :=
    contractRepresentativeLeaf_mem_leavesUnder r lstar v l' hl'
  have hvOriginal :
      contractVertex r.2 v ∈ BranchNodes t := by
    have hvNotPrefix :=
      not_prefix_of_mem_BranchNodes_contractAt r.2 v hv
    have hvNe : v.1 ≠ r.1 := by
      intro h
      exact hvNotPrefix (by rw [h])
    exact (mem_BranchNodes_contractVertex_iff_of_ne r.2 v hvNe).mp hv
  have hdiam :=
    hz (contractVertex r.2 v) hvOriginal
      (contractRepresentativeLeaf r lstar l) hlOriginal
      (contractRepresentativeLeaf r lstar l') hlOriginal'
  calc
    znorm
        (contractEmbedding z r lstar l -
          contractEmbedding z r lstar l') =
      znorm
        (z (contractRepresentativeLeaf r lstar l) -
          z (contractRepresentativeLeaf r lstar l')) := by
        rw [contractEmbedding_eq_comp_representative]
        rfl
    _ ≤ accumulatedScale Nm mu (contractVertex r.2 v) := hdiam
    _ ≤ accumulatedScale (contractMarking Nm r)
          (contractMultiplicities mu r s hs) v :=
      by exact_mod_cast haccumulated v hv

end

end Anderson4D
