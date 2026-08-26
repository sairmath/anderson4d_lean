import Anderson4D.HeppTree.ClusterCover
import Anderson4D.HeppTree.ClusterDiameter
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Recursive connecting networks for admissible Hepp clusters

This file closes the geometric input left abstract in `ClusterCover.lean`.
At a branching vertex, the connected child-link relation is used to join the
already constructed child networks.  The construction charges each child
network once and at most one scale-sized link for every vertex removed from
the finite child-link graph.
-/

namespace Anderson4D

open PlaneTree
open scoped Sym2

universe u v

/-! ## Finite edge-set networks -/

/-- A finite set of undirected edges whose associated simple graph is
connected.  Keeping the edge set as data makes recursive gluing and cost
accounting independent of decidability choices for graph adjacency. -/
structure FiniteMetricNetwork (V : Type u) where
  edges : Finset (Sym2 V)
  connected :
    (SimpleGraph.fromEdgeSet (edges : Set (Sym2 V))).Connected

/-- Cost of a finite network for a symmetric edge weight. -/
def finiteNetworkCost {V : Type u} (d : V → V → ℝ)
    (hsymm : ∀ a b, d a b = d b a)
    (N : FiniteMetricNetwork V) : ℝ :=
  ∑ e ∈ N.edges, sym2Weight d hsymm e

private theorem cn_sym2Weight_map {A : Type u} {B : Type v}
    (d : B → B → ℝ) (hsymm : ∀ a b, d a b = d b a)
    (f : A ↪ B) (e : Sym2 A) :
    sym2Weight d hsymm (f.sym2Map e) =
      sym2Weight (fun a b => d (f a) (f b))
        (fun a b => hsymm (f a) (f b)) e := by
  refine Sym2.inductionOn e ?_
  intro a b
  simp

private theorem cn_sum_union_le {α : Type*} [DecidableEq α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (s t : Finset α) :
    ∑ a ∈ s ∪ t, f a ≤ (∑ a ∈ s, f a) + ∑ a ∈ t, f a := by
  have hst : s ∪ t = s ∪ (t \ s) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [hst, Finset.sum_union Finset.disjoint_sdiff]
  exact add_le_add (le_refl _)
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun a _ _ => hf a))

private theorem cn_sum_biUnion_le {ι α : Type*}
    [DecidableEq ι] [DecidableEq α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (s : Finset ι) (F : ι → Finset α) :
    ∑ a ∈ s.biUnion F, f a ≤
      ∑ i ∈ s, ∑ a ∈ F i, f a := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (cn_sum_union_le f hf (F i) (s.biUnion F)).trans
        (add_le_add (le_refl _) ih)

/-- Transport a finite network along a bijective embedding. -/
private noncomputable def cn_mapNetwork {A : Type u} {B : Type v}
    (N : FiniteMetricNetwork A) (f : A ↪ B)
    (hsurj : Function.Surjective f) : FiniteMetricNetwork B := by
  classical
  let G : SimpleGraph A :=
    SimpleGraph.fromEdgeSet (N.edges : Set (Sym2 A))
  let E : Finset (Sym2 B) := N.edges.map f.sym2Map
  let H : SimpleGraph B :=
    SimpleGraph.fromEdgeSet (E : Set (Sym2 B))
  have hmap : ∀ {a b : A}, G.Adj a b → H.Adj (f a) (f b) := by
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab ⊢
    constructor
    · change s(f a, f b) ∈ E
      apply Finset.mem_map.mpr
      exact ⟨s(a, b), hab.1, by simp⟩
    · exact f.injective.ne hab.2
  let hom : G →g H :=
    { toFun := f
      map_rel' := hmap }
  exact
    { edges := E
      connected := SimpleGraph.Connected.map hom hsurj N.connected }

private theorem cn_mapNetwork_cost {A : Type u} {B : Type v}
    (d : B → B → ℝ) (hsymm : ∀ a b, d a b = d b a)
    (N : FiniteMetricNetwork A) (f : A ↪ B)
    (hsurj : Function.Surjective f) :
    finiteNetworkCost d hsymm (cn_mapNetwork N f hsurj) =
      finiteNetworkCost (fun a b => d (f a) (f b))
        (fun a b => hsymm (f a) (f b)) N := by
  classical
  unfold finiteNetworkCost cn_mapNetwork
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  exact cn_sym2Weight_map d hsymm f e

/-! ## Child-link spanning trees and their geometric bridge edges -/

abbrev ClusterChild {t : PlaneTree} (v : VPos t) :=
  {c : VPos t // c ∈ childrenOf v}

abbrev ClusterLeafAt {t : PlaneTree} (v : VPos t) :=
  {l : {w // w ∈ Leaves t} // l ∈ leavesUnder v}

private theorem cn_isLink_symm {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    {v c c' : VPos t} (h : IsLink Nm z v c c') :
    IsLink Nm z v c' c := by
  obtain ⟨l, hl, l', hl', hd⟩ := h
  exact ⟨l', hl', l, hl, by simpa [znorm_sub_comm] using hd⟩

private noncomputable def cn_childLinkGraph {t : PlaneTree}
    (Nm : HeppMarking t)
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t) :
    SimpleGraph (ClusterChild v) :=
  SimpleGraph.fromRel fun c d => IsLink Nm z v c.1 d.1

private theorem cn_childLinkGraph_adj_iff
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    {c d : ClusterChild v} :
    (cn_childLinkGraph Nm z v).Adj c d ↔
      c ≠ d ∧ IsLink Nm z v c.1 d.1 := by
  rw [cn_childLinkGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, cn_isLink_symm h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

private theorem cn_childLinkGraph_connected
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z) :
    (cn_childLinkGraph Nm z v).Connected := by
  have hvcount : 2 ≤ childCount t v.1 :=
    mem_BranchNodes_iff.mp hv
  have hcount : 0 < (childrenOf v).card := by
    rw [card_childrenOf]
    omega
  have hcne : (childrenOf v).Nonempty :=
    Finset.card_pos.mp hcount
  letI : Nonempty (ClusterChild v) :=
    ⟨⟨hcne.choose, hcne.choose_spec⟩⟩
  refine ⟨?_⟩
  intro c d
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hraw := hadm.linked v hv c.1 c.2 d.1 d.2
  have conv : ∀ {a b : VPos t},
      Relation.ReflTransGen
        (fun x y => x ∈ childrenOf v ∧ y ∈ childrenOf v ∧
          IsLink Nm z v x y) a b →
      ∀ (ha : a ∈ childrenOf v) (hb : b ∈ childrenOf v),
        Relation.ReflTransGen (cn_childLinkGraph Nm z v).Adj
          (⟨a, ha⟩ : ClusterChild v) ⟨b, hb⟩ := by
    intro a b h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro ha hb
        have heq : (⟨b, ha⟩ : ClusterChild v) = ⟨b, hb⟩ := rfl
        rw [← heq]
    | @head a c hab h ih =>
        intro ha hb
        have hc : c ∈ childrenOf v := hab.2.1
        by_cases hac : a = c
        · subst c
          simpa using ih ha hb
        · have hadj : (cn_childLinkGraph Nm z v).Adj
              (⟨a, ha⟩ : ClusterChild v)
              (⟨c, hc⟩ : ClusterChild v) :=
            cn_childLinkGraph_adj_iff.mpr
              ⟨fun heq => hac (congrArg Subtype.val heq), hab.2.2⟩
          exact Relation.ReflTransGen.head hadj (ih hc hb)
  exact conv hraw c.2 d.2

private noncomputable def cn_childSpanningTree
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z) :
    SimpleGraph (ClusterChild v) :=
  Classical.choose
    (cn_childLinkGraph_connected hv hadm).exists_isTree_le

private theorem cn_childSpanningTree_le
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z) :
    cn_childSpanningTree hv hadm ≤ cn_childLinkGraph Nm z v :=
  (Classical.choose_spec
    (cn_childLinkGraph_connected hv hadm).exists_isTree_le).1

private theorem cn_childSpanningTree_isTree
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z) :
    (cn_childSpanningTree hv hadm).IsTree :=
  (Classical.choose_spec
    (cn_childLinkGraph_connected hv hadm).exists_isTree_le).2

/-- A stable finite edge set for the chosen child spanning tree. -/
private noncomputable def cn_treeEdgeFinset
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z) :
    Finset (Sym2 (ClusterChild v)) := by
  classical
  exact (cn_childSpanningTree hv hadm).edgeSet.toFinite.toFinset

@[simp] private theorem cn_mem_treeEdgeFinset
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (e : Sym2 (ClusterChild v)) :
    e ∈ cn_treeEdgeFinset hv hadm ↔
      e ∈ (cn_childSpanningTree hv hadm).edgeSet := by
  classical
  simp [cn_treeEdgeFinset]

private theorem cn_leaf_under_parent_of_under_child
    {t : PlaneTree} {v c : VPos t} (hc : c ∈ childrenOf v)
    {l : {w // w ∈ Leaves t}} (hl : l ∈ leavesUnder c) :
    l ∈ leavesUnder v := by
  rw [mem_leavesUnder] at hl ⊢
  exact (mem_childrenOf.mp hc).2.trans hl

private structure CNTreeEdgeWitness
    {t : PlaneTree} (Nm : HeppMarking t)
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ)
    (v : VPos t) (e : Sym2 (ClusterChild v)) where
  c : ClusterChild v
  d : ClusterChild v
  edge_eq : e = s(c, d)
  c_ne_d : c ≠ d
  l : {w // w ∈ Leaves t}
  r : {w // w ∈ Leaves t}
  l_mem : l ∈ leavesUnder c.1
  r_mem : r ∈ leavesUnder d.1
  dist_le : znorm (z l - z r) ≤ (scaleN Nm v : ℝ)

private theorem cn_exists_treeEdgeWitness
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (e : Sym2 (ClusterChild v))
    (he : e ∈ cn_treeEdgeFinset hv hadm) :
    Nonempty (CNTreeEdgeWitness Nm z v e) := by
  classical
  induction e using Sym2.inductionOn with
  | _ c d =>
      have hTadj : (cn_childSpanningTree hv hadm).Adj c d :=
        (SimpleGraph.mem_edgeSet _).mp
          ((cn_mem_treeEdgeFinset hv hadm _).mp he)
      have hGadj : (cn_childLinkGraph Nm z v).Adj c d :=
        cn_childSpanningTree_le hv hadm hTadj
      have hlink : IsLink Nm z v c.1 d.1 :=
        (cn_childLinkGraph_adj_iff.mp hGadj).2
      obtain ⟨l, hl, r, hr, hdr⟩ := hlink
      exact ⟨⟨c, d, rfl, hTadj.ne, l, r, hl, hr, hdr⟩⟩

private noncomputable def cn_treeEdgeWitness
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (e : cn_treeEdgeFinset hv hadm) :
    CNTreeEdgeWitness Nm z v e.1 :=
  Classical.choice
    (cn_exists_treeEdgeWitness hv hadm e.1 e.2)

private noncomputable def cn_liftedBridgeEdge
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (e : cn_treeEdgeFinset hv hadm) :
    Sym2 (ClusterLeafAt v) :=
  let w := cn_treeEdgeWitness hv hadm e
  s(⟨w.l, cn_leaf_under_parent_of_under_child w.c.2 w.l_mem⟩,
    ⟨w.r, cn_leaf_under_parent_of_under_child w.d.2 w.r_mem⟩)

private theorem cn_clusterLeafDistance_symm
    {t : PlaneTree}
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t)
    (a b : ClusterLeafAt v) :
    clusterLeafDistance z v a b =
      clusterLeafDistance z v b a := by
  exact znorm_sub_comm _ _

private theorem cn_liftedBridgeEdge_weight_le
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (e : cn_treeEdgeFinset hv hadm) :
    sym2Weight (clusterLeafDistance z v)
      (cn_clusterLeafDistance_symm z v)
      (cn_liftedBridgeEdge hv hadm e) ≤
        (scaleN Nm v : ℝ) := by
  change znorm
    (z (cn_treeEdgeWitness hv hadm e).l -
      z (cn_treeEdgeWitness hv hadm e).r) ≤ _
  exact (cn_treeEdgeWitness hv hadm e).dist_le

private noncomputable def cn_branchBridgeEdges
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z) :
    Finset (Sym2 (ClusterLeafAt v)) :=
  (cn_treeEdgeFinset hv hadm).attach.image
    (cn_liftedBridgeEdge hv hadm)

private theorem cn_branchBridgeEdges_weight_le
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z) :
    ∑ e ∈ cn_branchBridgeEdges hv hadm,
        sym2Weight (clusterLeafDistance z v)
          (cn_clusterLeafDistance_symm z v) e ≤
      (childCount t v.1 : ℝ) * (scaleN Nm v : ℝ) := by
  classical
  have h_each : ∀ e ∈ cn_branchBridgeEdges hv hadm,
      sym2Weight (clusterLeafDistance z v)
        (cn_clusterLeafDistance_symm z v) e ≤
          (scaleN Nm v : ℝ) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact cn_liftedBridgeEdge_weight_le hv hadm f
  calc
    ∑ e ∈ cn_branchBridgeEdges hv hadm,
        sym2Weight (clusterLeafDistance z v)
          (cn_clusterLeafDistance_symm z v) e
        ≤ (cn_branchBridgeEdges hv hadm).card •
            (scaleN Nm v : ℝ) :=
      Finset.sum_le_card_nsmul _ _ _ h_each
    _ = ((cn_branchBridgeEdges hv hadm).card : ℝ) *
          (scaleN Nm v : ℝ) := by simp
    _ ≤ ((cn_treeEdgeFinset hv hadm).card : ℝ) *
          (scaleN Nm v : ℝ) := by
      gcongr
      have hi : (cn_branchBridgeEdges hv hadm).card ≤
          (cn_treeEdgeFinset hv hadm).attach.card := by
        unfold cn_branchBridgeEdges
        exact Finset.card_image_le
          (f := cn_liftedBridgeEdge hv hadm)
          (s := (cn_treeEdgeFinset hv hadm).attach)
      simpa using hi
    _ ≤ (childCount t v.1 : ℝ) * (scaleN Nm v : ℝ) := by
      gcongr
      have hcard : (cn_treeEdgeFinset hv hadm).card + 1 =
          Fintype.card (ClusterChild v) := by
        simpa [cn_treeEdgeFinset, SimpleGraph.edgeFinset] using
          (cn_childSpanningTree_isTree hv hadm).card_edgeFinset
      have hchildren :
          Fintype.card (ClusterChild v) = childCount t v.1 := by
        simpa using card_childrenOf t v
      rw [hchildren] at hcard
      exact_mod_cast
        (show (cn_treeEdgeFinset hv hadm).card ≤
          childCount t v.1 by omega)

/-! ## Gluing the child networks at one branch -/

private def cn_childLeafEmbedding {t : PlaneTree} {v : VPos t}
    (c : ClusterChild v) : ClusterLeafAt c.1 ↪ ClusterLeafAt v where
  toFun l :=
    ⟨l.1, cn_leaf_under_parent_of_under_child c.2 l.2⟩
  inj' := by
    intro a b hab
    exact Subtype.ext
      (congrArg (fun x : ClusterLeafAt v => x.1) hab)

private theorem cn_cast_clusterLeafAt_val
    {t : PlaneTree} {c d : VPos t} (h : c = d)
    (l : ClusterLeafAt c) :
    (h ▸ l : ClusterLeafAt d).1 = l.1 := by
  subst d
  rfl

private theorem cn_cast_childClusterLeafAt_val
    {t : PlaneTree} {v : VPos t} {c d : ClusterChild v}
    (h : c = d) (l : ClusterLeafAt c.1) :
    (h ▸ l : ClusterLeafAt d.1).1 = l.1 := by
  subst d
  rfl

private noncomputable def cn_childNetworkEdges
    {t : PlaneTree} {v : VPos t}
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1)) :
    Finset (Sym2 (ClusterLeafAt v)) := by
  classical
  exact Finset.univ.biUnion fun c =>
    (N c).edges.map (cn_childLeafEmbedding c).sym2Map

private theorem cn_clusterWeight_nonneg
    {t : PlaneTree}
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t)
    (e : Sym2 (ClusterLeafAt v)) :
    0 ≤ sym2Weight (clusterLeafDistance z v)
      (cn_clusterLeafDistance_symm z v) e := by
  refine Sym2.inductionOn e ?_
  intro a b
  simpa [clusterLeafDistance, leafDistance] using
    znorm_nonneg (z a.1 - z b.1)

private theorem cn_childNetworkEdges_weight_le
    {t : PlaneTree}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1)) :
    ∑ e ∈ cn_childNetworkEdges N,
        sym2Weight (clusterLeafDistance z v)
          (cn_clusterLeafDistance_symm z v) e ≤
      ∑ c : ClusterChild v,
        finiteNetworkCost (clusterLeafDistance z c.1)
          (cn_clusterLeafDistance_symm z c.1) (N c) := by
  classical
  let w : Sym2 (ClusterLeafAt v) → ℝ :=
    sym2Weight (clusterLeafDistance z v)
      (cn_clusterLeafDistance_symm z v)
  calc
    ∑ e ∈ cn_childNetworkEdges N, w e
        ≤ ∑ c ∈ (Finset.univ : Finset (ClusterChild v)),
            ∑ e ∈ (N c).edges.map
              (cn_childLeafEmbedding c).sym2Map, w e := by
          exact cn_sum_biUnion_le w
            (cn_clusterWeight_nonneg z v) Finset.univ fun c =>
              (N c).edges.map (cn_childLeafEmbedding c).sym2Map
    _ = ∑ c : ClusterChild v,
          finiteNetworkCost (clusterLeafDistance z c.1)
            (cn_clusterLeafDistance_symm z c.1) (N c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_map]
      unfold finiteNetworkCost
      apply Finset.sum_congr rfl
      intro e he
      dsimp [w]
      rw [cn_sym2Weight_map]
      rfl

private noncomputable def cn_branchNetworkEdges
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1)) :
    Finset (Sym2 (ClusterLeafAt v)) :=
  cn_childNetworkEdges N ∪ cn_branchBridgeEdges hv hadm

private theorem cn_child_eq_of_common_leaf
    {t : PlaneTree} {v : VPos t} {c d : VPos t}
    (hc : c ∈ childrenOf v) (hd : d ∈ childrenOf v)
    {l : {w // w ∈ Leaves t}}
    (hlc : l ∈ leavesUnder c) (hld : l ∈ leavesUnder d) :
    c = d := by
  apply Subtype.ext
  have hlen : c.1.length = d.1.length := by
    rw [(mem_childrenOf.mp hc).1, (mem_childrenOf.mp hd).1]
  have hcp := mem_leavesUnder.mp hlc
  have hdp := mem_leavesUnder.mp hld
  rw [List.prefix_iff_eq_take] at hcp hdp
  calc
    c.1 = l.1.1.take c.1.length := hcp
    _ = l.1.1.take d.1.length := by rw [hlen]
    _ = d.1 := hdp.symm

private theorem cn_same_child_reachable
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1))
    (c : ClusterChild v) (a b : ClusterLeafAt c.1) :
    (SimpleGraph.fromEdgeSet
      (cn_branchNetworkEdges hv hadm N :
        Set (Sym2 (ClusterLeafAt v)))).Reachable
      (cn_childLeafEmbedding c a) (cn_childLeafEmbedding c b) := by
  classical
  let G : SimpleGraph (ClusterLeafAt c.1) :=
    SimpleGraph.fromEdgeSet ((N c).edges :
      Set (Sym2 (ClusterLeafAt c.1)))
  let H : SimpleGraph (ClusterLeafAt v) :=
    SimpleGraph.fromEdgeSet
      (cn_branchNetworkEdges hv hadm N :
        Set (Sym2 (ClusterLeafAt v)))
  let f := cn_childLeafEmbedding c
  have hmap : ∀ {x y : ClusterLeafAt c.1},
      G.Adj x y → H.Adj (f x) (f y) := by
    intro x y hxy
    rw [SimpleGraph.fromEdgeSet_adj] at hxy ⊢
    constructor
    · change s(f x, f y) ∈ cn_branchNetworkEdges hv hadm N
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Finset.mem_univ _, ?_⟩
      apply Finset.mem_map.mpr
      exact ⟨s(x, y), hxy.1, by simp [f]⟩
    · exact f.injective.ne hxy.2
  let hom : G →g H :=
    { toFun := f
      map_rel' := hmap }
  exact ((N c).connected a b).map hom

private theorem cn_bridge_adj_of_tree_adj
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1))
    {c d : ClusterChild v}
    (hcd : (cn_childSpanningTree hv hadm).Adj c d) :
    ∃ l : ClusterLeafAt c.1, ∃ r : ClusterLeafAt d.1,
      (SimpleGraph.fromEdgeSet
        (cn_branchNetworkEdges hv hadm N :
          Set (Sym2 (ClusterLeafAt v)))).Adj
        (cn_childLeafEmbedding c l)
        (cn_childLeafEmbedding d r) := by
  classical
  have he : s(c, d) ∈ cn_treeEdgeFinset hv hadm := by
    rw [cn_mem_treeEdgeFinset]
    exact (SimpleGraph.mem_edgeSet _).mpr hcd
  let e : cn_treeEdgeFinset hv hadm := ⟨s(c, d), he⟩
  let w := cn_treeEdgeWitness hv hadm e
  let lp : ClusterLeafAt v :=
    ⟨w.l, cn_leaf_under_parent_of_under_child w.c.2 w.l_mem⟩
  let rp : ClusterLeafAt v :=
    ⟨w.r, cn_leaf_under_parent_of_under_child w.d.2 w.r_mem⟩
  have hlrne : lp ≠ rp := by
    intro hlr
    have hval : w.l = w.r :=
      congrArg (fun x : ClusterLeafAt v => x.1) hlr
    apply w.c_ne_d
    apply Subtype.ext
    apply cn_child_eq_of_common_leaf w.c.2 w.d.2 w.l_mem
    simpa [hval] using w.r_mem
  have hbridge :
      cn_liftedBridgeEdge hv hadm e ∈
        cn_branchBridgeEdges hv hadm := by
    apply Finset.mem_image.mpr
    exact ⟨e, Finset.mem_attach _ _, rfl⟩
  have hadj : (SimpleGraph.fromEdgeSet
      (cn_branchNetworkEdges hv hadm N :
        Set (Sym2 (ClusterLeafAt v)))).Adj lp rp := by
    rw [SimpleGraph.fromEdgeSet_adj]
    constructor
    · change s(lp, rp) ∈ cn_branchNetworkEdges hv hadm N
      apply Finset.mem_union_right
      simpa [cn_liftedBridgeEdge, lp, rp, w] using hbridge
    · exact hlrne
  have hedge : s(c, d) = s(w.c, w.d) := by
    exact w.edge_eq
  rcases Sym2.eq_iff.mp hedge with horient | horient
  · rcases horient with ⟨hc, hd⟩
    let l : ClusterLeafAt c.1 :=
      hc.symm ▸ (⟨w.l, w.l_mem⟩ : ClusterLeafAt w.c.1)
    let r : ClusterLeafAt d.1 :=
      hd.symm ▸ (⟨w.r, w.r_mem⟩ : ClusterLeafAt w.d.1)
    refine ⟨l, r, ?_⟩
    have hlift : cn_childLeafEmbedding c l = lp := by
      apply Subtype.ext
      exact cn_cast_childClusterLeafAt_val hc.symm _
    have hrift : cn_childLeafEmbedding d r = rp := by
      apply Subtype.ext
      exact cn_cast_childClusterLeafAt_val hd.symm _
    rw [hlift, hrift]
    exact hadj
  · rcases horient with ⟨hc, hd⟩
    let l : ClusterLeafAt c.1 :=
      hc.symm ▸ (⟨w.r, w.r_mem⟩ : ClusterLeafAt w.d.1)
    let r : ClusterLeafAt d.1 :=
      hd.symm ▸ (⟨w.l, w.l_mem⟩ : ClusterLeafAt w.c.1)
    refine ⟨l, r, ?_⟩
    have hlift : cn_childLeafEmbedding c l = rp := by
      apply Subtype.ext
      exact cn_cast_childClusterLeafAt_val hc.symm _
    have hrift : cn_childLeafEmbedding d r = lp := by
      apply Subtype.ext
      exact cn_cast_childClusterLeafAt_val hd.symm _
    rw [hlift, hrift]
    exact hadj.symm

private theorem cn_reachable_along_childTree_walk
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1))
    {c d : ClusterChild v}
    (p : (cn_childSpanningTree hv hadm).Walk c d)
    (a : ClusterLeafAt c.1) (b : ClusterLeafAt d.1) :
    (SimpleGraph.fromEdgeSet
      (cn_branchNetworkEdges hv hadm N :
        Set (Sym2 (ClusterLeafAt v)))).Reachable
      (cn_childLeafEmbedding c a)
      (cn_childLeafEmbedding d b) := by
  induction p with
  | nil =>
      exact cn_same_child_reachable hv hadm N _ a b
  | @cons c d e hcd p ih =>
      obtain ⟨l, r, hlr⟩ :=
        cn_bridge_adj_of_tree_adj hv hadm N hcd
      exact (cn_same_child_reachable hv hadm N c a l).trans
        (hlr.reachable.trans (ih r b))

private theorem cn_isPos_append_singleton {t : PlaneTree} {p : Pos}
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

private theorem cn_lt_childCount_of_isPos_append
    {t : PlaneTree} {p : Pos} (hp : IsPos t p) {i : ℕ}
    (hi : IsPos t (p ++ [i])) :
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

private def cn_childAt {t : PlaneTree} (v : VPos t)
    (i : Fin (childCount t v.1)) : VPos t :=
  ⟨v.1 ++ [i.1], cn_isPos_append_singleton v.2 i.2⟩

private theorem cn_childAt_mem_childrenOf {t : PlaneTree}
    (v : VPos t) (i : Fin (childCount t v.1)) :
    cn_childAt v i ∈ childrenOf v := by
  rw [mem_childrenOf]
  exact ⟨by simp [cn_childAt], List.prefix_append _ _⟩

private theorem cn_exists_childAt_of_mem_leavesUnder
    {t : PlaneTree} {v : VPos t} {l : {w // w ∈ Leaves t}}
    (hv : 0 < childCount t v.1) (hl : l ∈ leavesUnder v) :
    ∃ i : Fin (childCount t v.1),
      l ∈ leavesUnder (cn_childAt v i) := by
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
    ⟨i, cn_lt_childCount_of_isPos_append v.2 hipos⟩
  refine ⟨j, ?_⟩
  rw [mem_leavesUnder]
  change v.1 ++ [i] <+: l.1.1
  rw [← hq]
  simp

private theorem cn_branchNetwork_connected
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1)) :
    (SimpleGraph.fromEdgeSet
      (cn_branchNetworkEdges hv hadm N :
        Set (Sym2 (ClusterLeafAt v)))).Connected := by
  have hcount : 2 ≤ childCount t v.1 :=
    mem_BranchNodes_iff.mp hv
  let i₀ : Fin (childCount t v.1) := ⟨0, by omega⟩
  let c₀ : ClusterChild v :=
    ⟨cn_childAt v i₀, cn_childAt_mem_childrenOf v i₀⟩
  let a₀ : ClusterLeafAt c₀.1 := (N c₀).connected.nonempty.some
  letI : Nonempty (ClusterLeafAt v) :=
    ⟨cn_childLeafEmbedding c₀ a₀⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨i, hai⟩ :=
    cn_exists_childAt_of_mem_leavesUnder
      (lt_of_lt_of_le Nat.zero_lt_two hcount) a.2
  obtain ⟨j, hbj⟩ :=
    cn_exists_childAt_of_mem_leavesUnder
      (lt_of_lt_of_le Nat.zero_lt_two hcount) b.2
  let c : ClusterChild v :=
    ⟨cn_childAt v i, cn_childAt_mem_childrenOf v i⟩
  let d : ClusterChild v :=
    ⟨cn_childAt v j, cn_childAt_mem_childrenOf v j⟩
  let ac : ClusterLeafAt c.1 := ⟨a.1, hai⟩
  let bd : ClusterLeafAt d.1 := ⟨b.1, hbj⟩
  obtain ⟨p⟩ :=
    (cn_childSpanningTree_isTree hv hadm).connected c d
  have hp :=
    cn_reachable_along_childTree_walk hv hadm N p ac bd
  have ha : cn_childLeafEmbedding c ac = a := by
    apply Subtype.ext
    rfl
  have hb : cn_childLeafEmbedding d bd = b := by
    apply Subtype.ext
    rfl
  rwa [ha, hb] at hp

private theorem cn_branchDescendants_disjoint_of_children_ne
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

private theorem cn_biUnion_branchDescendants_subset_erase
    {t : PlaneTree} {v : VPos t} :
    (childrenOf v).biUnion branchDescendants ⊆
      (branchDescendants v).erase v := by
  intro u hu
  obtain ⟨c, hc, huc⟩ := Finset.mem_biUnion.mp hu
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

private theorem cn_sum_tildeScale_children_le_erase
    {t : PlaneTree} {Nm : HeppMarking t} {v : VPos t} :
    ∑ c ∈ childrenOf v, tildeScale Nm c ≤
      ∑ u ∈ (branchDescendants v).erase v,
        (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) := by
  have hpair :
      (↑(childrenOf v) : Set (VPos t)).PairwiseDisjoint
        branchDescendants := by
    intro a ha b hb hne
    exact cn_branchDescendants_disjoint_of_children_ne ha hb hne
  change
    ∑ c ∈ childrenOf v,
        ∑ u ∈ branchDescendants c,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) ≤ _
  rw [← Finset.sum_biUnion hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    cn_biUnion_branchDescendants_subset_erase
    (fun _ _ _ => by positivity)

private theorem cn_exists_branchNetwork
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hadm : IsAdmissible Nm M z)
    (N : ∀ c : ClusterChild v,
      FiniteMetricNetwork (ClusterLeafAt c.1))
    (hN : ∀ c : ClusterChild v,
      finiteNetworkCost (clusterLeafDistance z c.1)
        (cn_clusterLeafDistance_symm z c.1) (N c) ≤
          tildeScale Nm c.1) :
    ∃ P : FiniteMetricNetwork (ClusterLeafAt v),
      finiteNetworkCost (clusterLeafDistance z v)
        (cn_clusterLeafDistance_symm z v) P ≤
          tildeScale Nm v := by
  classical
  let P : FiniteMetricNetwork (ClusterLeafAt v) :=
    { edges := cn_branchNetworkEdges hv hadm N
      connected := cn_branchNetwork_connected hv hadm N }
  refine ⟨P, ?_⟩
  let w : Sym2 (ClusterLeafAt v) → ℝ :=
    sym2Weight (clusterLeafDistance z v)
      (cn_clusterLeafDistance_symm z v)
  have hunion :
      ∑ e ∈ cn_branchNetworkEdges hv hadm N, w e ≤
        (∑ e ∈ cn_childNetworkEdges N, w e) +
          ∑ e ∈ cn_branchBridgeEdges hv hadm, w e := by
    exact cn_sum_union_le w (cn_clusterWeight_nonneg z v)
      (cn_childNetworkEdges N) (cn_branchBridgeEdges hv hadm)
  have hchildrenCost :
      ∑ e ∈ cn_childNetworkEdges N, w e ≤
        ∑ c : ClusterChild v, tildeScale Nm c.1 := by
    calc
      ∑ e ∈ cn_childNetworkEdges N, w e
          ≤ ∑ c : ClusterChild v,
              finiteNetworkCost (clusterLeafDistance z c.1)
                (cn_clusterLeafDistance_symm z c.1) (N c) :=
        cn_childNetworkEdges_weight_le N
      _ ≤ ∑ c : ClusterChild v, tildeScale Nm c.1 := by
        apply Finset.sum_le_sum
        intro c hc
        exact hN c
  have hsubtype :
      (∑ c : ClusterChild v, tildeScale Nm c.1) =
        ∑ c ∈ childrenOf v, tildeScale Nm c := by
    symm
    exact Finset.sum_subtype (childrenOf v) (fun _ => Iff.rfl)
      (tildeScale Nm)
  have hchildren :
      ∑ c : ClusterChild v, tildeScale Nm c.1 ≤
        ∑ u ∈ (branchDescendants v).erase v,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ) := by
    rw [hsubtype]
    exact cn_sum_tildeScale_children_le_erase
  have hbridge :
      ∑ e ∈ cn_branchBridgeEdges hv hadm, w e ≤
        (childCount t v.1 : ℝ) * (scaleN Nm v : ℝ) :=
    cn_branchBridgeEdges_weight_le hv hadm
  have hvdesc : v ∈ branchDescendants v :=
    mem_branchDescendants.mpr ⟨hv, List.prefix_rfl⟩
  have hsplit :
      (∑ u ∈ (branchDescendants v).erase v,
          (childCount t u.1 : ℝ) * (scaleN Nm u : ℝ)) +
          (childCount t v.1 : ℝ) * (scaleN Nm v : ℝ) =
        tildeScale Nm v := by
    unfold tildeScale
    exact Finset.sum_erase_add _ _ hvdesc
  change
    ∑ e ∈ cn_branchNetworkEdges hv hadm N, w e ≤
      tildeScale Nm v
  linarith

/-! ## Recursion over the carrier tree -/

private theorem cn_isPos_length_lt_size {t : PlaneTree} {p : Pos}
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

private theorem cn_eq_vertex_of_leaf_under_leaf
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
  have hi := cn_lt_childCount_of_isPos_append v.2 hipos
  omega

private theorem cn_exists_leafNetwork
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hzero : childCount t v.1 = 0) :
    ∃ P : FiniteMetricNetwork (ClusterLeafAt v),
      finiteNetworkCost (clusterLeafDistance z v)
        (cn_clusterLeafDistance_symm z v) P ≤
          tildeScale Nm v := by
  classical
  have hvleaf : v ∈ Leaves t := mem_Leaves_iff.mpr hzero
  let lv : {w // w ∈ Leaves t} := ⟨v, hvleaf⟩
  have hlv : lv ∈ leavesUnder v :=
    self_mem_leavesUnder v hvleaf
  letI : Nonempty (ClusterLeafAt v) := ⟨⟨lv, hlv⟩⟩
  letI : Subsingleton (ClusterLeafAt v) :=
    ⟨by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact (cn_eq_vertex_of_leaf_under_leaf hzero a.2).trans
        (cn_eq_vertex_of_leaf_under_leaf hzero b.2).symm⟩
  have hconn :
      (SimpleGraph.fromEdgeSet
        (∅ : Set (Sym2 (ClusterLeafAt v)))).Connected := by
    rw [SimpleGraph.fromEdgeSet_empty]
    exact SimpleGraph.connected_bot_iff.mpr
      ⟨inferInstance, inferInstance⟩
  let P : FiniteMetricNetwork (ClusterLeafAt v) :=
    { edges := ∅
      connected := by simpa using hconn }
  refine ⟨P, ?_⟩
  simp [finiteNetworkCost, P, tildeScale_nonneg Nm v]

private theorem cn_exists_unaryNetwork
    {t : PlaneTree} {Nm : HeppMarking t}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ} {v : VPos t}
    (hone : childCount t v.1 = 1)
    (hlocal : ∀ c : ClusterChild v,
      ∃ P : FiniteMetricNetwork (ClusterLeafAt c.1),
        finiteNetworkCost (clusterLeafDistance z c.1)
          (cn_clusterLeafDistance_symm z c.1) P ≤
            tildeScale Nm c.1) :
    ∃ P : FiniteMetricNetwork (ClusterLeafAt v),
      finiteNetworkCost (clusterLeafDistance z v)
        (cn_clusterLeafDistance_symm z v) P ≤
          tildeScale Nm v := by
  classical
  have hpos : 0 < childCount t v.1 := by omega
  let i₀ : Fin (childCount t v.1) := ⟨0, hpos⟩
  let c : ClusterChild v :=
    ⟨cn_childAt v i₀, cn_childAt_mem_childrenOf v i₀⟩
  obtain ⟨Nc, hNc⟩ := hlocal c
  let f := cn_childLeafEmbedding c
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨j, haj⟩ :=
      cn_exists_childAt_of_mem_leavesUnder hpos a.2
    have hji : j = i₀ := by
      apply Fin.ext
      omega
    subst j
    let ac : ClusterLeafAt c.1 := ⟨a.1, haj⟩
    refine ⟨ac, ?_⟩
    apply Subtype.ext
    rfl
  let P : FiniteMetricNetwork (ClusterLeafAt v) :=
    cn_mapNetwork Nc f hsurj
  have hPcost :
      finiteNetworkCost (clusterLeafDistance z v)
          (cn_clusterLeafDistance_symm z v) P =
        finiteNetworkCost (clusterLeafDistance z c.1)
          (cn_clusterLeafDistance_symm z c.1) Nc := by
    dsimp [P]
    rw [cn_mapNetwork_cost]
    rfl
  refine ⟨P, ?_⟩
  rw [hPcost]
  exact hNc.trans
    (tildeScale_mono_of_ancestor Nm
      (mem_childrenOf.mp c.2).2)

private theorem cn_finiteMetricNetwork_aux
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (k : ℕ) :
    ∀ (v : VPos t), t.size - v.1.length = k →
      ∃ P : FiniteMetricNetwork (ClusterLeafAt v),
        finiteNetworkCost (clusterLeafDistance z v)
          (cn_clusterLeafDistance_symm z v) P ≤
            tildeScale Nm v := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro v hk
      by_cases hzero : childCount t v.1 = 0
      · exact cn_exists_leafNetwork hzero
      · have hlocal : ∀ c : ClusterChild v,
            ∃ P : FiniteMetricNetwork (ClusterLeafAt c.1),
              finiteNetworkCost (clusterLeafDistance z c.1)
                (cn_clusterLeafDistance_symm z c.1) P ≤
                  tildeScale Nm c.1 := by
          intro c
          have hmeasure : t.size - c.1.1.length < k := by
            have hvsize := cn_isPos_length_lt_size v.2
            have hclen := (mem_childrenOf.mp c.2).1
            rw [← hk]
            omega
          exact ih (t.size - c.1.1.length) hmeasure c.1 rfl
        by_cases hone : childCount t v.1 = 1
        · exact cn_exists_unaryNetwork hone hlocal
        · have hvbranch : v ∈ BranchNodes t :=
            mem_BranchNodes_iff.mpr (by omega)
          let N : ∀ c : ClusterChild v,
              FiniteMetricNetwork (ClusterLeafAt c.1) :=
            fun c => Classical.choose (hlocal c)
          have hN : ∀ c : ClusterChild v,
              finiteNetworkCost (clusterLeafDistance z c.1)
                (cn_clusterLeafDistance_symm z c.1) (N c) ≤
                  tildeScale Nm c.1 :=
            fun c => Classical.choose_spec (hlocal c)
          exact cn_exists_branchNetwork hvbranch hadm N hN

/-- Every admissible embedded cluster has a finite connected leaf network
whose total geometric length is at most its accumulated Hepp scale. -/
theorem exists_finiteMetricNetwork_of_isAdmissible
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (v : VPos t) :
    ∃ P : FiniteMetricNetwork (ClusterLeafAt v),
      finiteNetworkCost (clusterLeafDistance z v)
        (cn_clusterLeafDistance_symm z v) P ≤
          tildeScale Nm v :=
  cn_finiteMetricNetwork_aux hadm
    (t.size - v.1.length) v rfl

/-- The recursive finite edge-set construction supplies the exact connected
network certificate consumed by `ClusterCover`. -/
theorem hasClusterNetwork_of_isAdmissible
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (v : VPos t) :
    HasClusterNetwork Nm z v := by
  classical
  obtain ⟨P, hP⟩ :=
    exists_finiteMetricNetwork_of_isAdmissible hadm v
  let G : SimpleGraph (ClusterLeafAt v) :=
    SimpleGraph.fromEdgeSet
      (P.edges : Set (Sym2 (ClusterLeafAt v)))
  refine ⟨G, P.connected, ?_⟩
  unfold clusterNetworkLength
  apply le_trans ?_ hP
  unfold finiteNetworkCost
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    have heset : e ∈ G.edgeSet := by
      simpa [SimpleGraph.edgeFinset] using he
    dsimp [G] at heset
    rw [SimpleGraph.edgeSet_fromEdgeSet] at heset
    exact heset.1
  · intro e heP heG
    exact cn_clusterWeight_nonneg z v e

/-- **Paper (5.22b).**  Every admissible cluster below `v` has a cover by
embedded leaf centres of radius `R` and cardinality at most
`3 * (1 + tildeScale Nm v / R)`. -/
theorem exists_clusterCover_of_isAdmissible
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (v : VPos t)
    {R : ℝ} (hR : 0 < R) :
    ∃ Q : Finset (Fin 4 → ℤ),
      Q ⊆ (leavesUnder v).image z ∧
      (∀ l ∈ leavesUnder v,
        ∃ q ∈ Q, znorm (z l - q) ≤ R) ∧
      (Q.card : ℝ) ≤
        3 * (1 + tildeScale Nm v / R) :=
  exists_clusterCover_of_network hadm v
    (hasClusterNetwork_of_isAdmissible hadm v) hR

end Anderson4D
