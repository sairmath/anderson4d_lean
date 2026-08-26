import Anderson4D.HeppTree.AutomorphismGeometry
import Anderson4D.ForMathlib.ConnectedParent

/-!
# Parent-function encoding of a connected child-link graph

Paper §5.3, Step 5 chooses a link tree on the children of a branching
vertex and exposes the children from a fixed root.  This file makes that
choice canonical enough for counting:

* the children form the vertices of an undirected simple graph;
* two distinct children are adjacent when `IsLink` holds;
* `LinkedChildren` gives connectedness of this graph;
* `SimpleGraph.parentTowardRoot` orients one shortest-path edge toward a
  fixed root;
* graph distance strictly decreases along the parent map, so sorting by
  distance exposes every parent before its child;
* the parent map is literally an element of the full finite function space
  used by `fullParentWeight`.

`IsLink` itself can hold on the diagonal, so adjacency explicitly includes
`a ≠ b`.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

/-- The finite type of children of a fixed tree vertex. -/
abbrev BranchChild {t : PlaneTree} (v : VPos t) :=
  ↥(childrenOf v)

/-- The link relation is symmetric. -/
theorem isLink_symm {t : PlaneTree} {Nm : HeppMarking t}
    {z : LeafEmbedding t} {v c c' : VPos t}
    (h : IsLink Nm z v c c') :
    IsLink Nm z v c' c := by
  obtain ⟨l, hl, l', hl', hd⟩ := h
  refine ⟨l', hl', l, hl, ?_⟩
  rwa [znorm_sub_comm]

theorem isLink_comm {t : PlaneTree} (Nm : HeppMarking t)
    (z : LeafEmbedding t) (v c c' : VPos t) :
    IsLink Nm z v c c' ↔ IsLink Nm z v c' c :=
  ⟨isLink_symm, isLink_symm⟩

/-- Undirected simple graph of links among the children of `v`. -/
def childLinkGraph {t : PlaneTree} (Nm : HeppMarking t)
    (z : LeafEmbedding t) (v : VPos t) :
    SimpleGraph (BranchChild v) where
  Adj a b := a ≠ b ∧ IsLink Nm z v a.1 b.1
  symm := ⟨by
    intro a b hab
    exact ⟨hab.1.symm, isLink_symm hab.2⟩⟩
  loopless := ⟨by
    intro a ha
    exact ha.1 rfl⟩

@[simp] theorem childLinkGraph_adj {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    {a b : BranchChild v} :
    (childLinkGraph Nm z v).Adj a b ↔
      a ≠ b ∧ IsLink Nm z v a.1 b.1 :=
  Iff.rfl

private theorem linkChain_end_mem
    {t : PlaneTree} {Nm : HeppMarking t} {z : LeafEmbedding t}
    {v a b : VPos t}
    (hchain :
      Relation.ReflTransGen
        (fun x y =>
          x ∈ childrenOf v ∧ y ∈ childrenOf v ∧
            IsLink Nm z v x y) a b)
    (ha : a ∈ childrenOf v) :
    b ∈ childrenOf v := by
  induction hchain using Relation.ReflTransGen.trans_induction_on with
  | refl => exact ha
  | single h => exact h.2.1
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ ha)

private theorem reachable_childLinkGraph_of_chain
    {t : PlaneTree} {Nm : HeppMarking t} {z : LeafEmbedding t}
    {v start finish : VPos t}
    (ha : start ∈ childrenOf v) (hb : finish ∈ childrenOf v)
    (hchain :
      Relation.ReflTransGen
        (fun x y =>
          x ∈ childrenOf v ∧ y ∈ childrenOf v ∧
            IsLink Nm z v x y) start finish) :
    (childLinkGraph Nm z v).Reachable
      (⟨start, ha⟩ : BranchChild v) ⟨finish, hb⟩ := by
  revert ha hb
  induction hchain using Relation.ReflTransGen.trans_induction_on with
  | refl x =>
      intro ha hb
      let A : BranchChild v := ⟨x, ha⟩
      let B : BranchChild v := ⟨x, hb⟩
      have heq : A = B := Subtype.ext rfl
      change (childLinkGraph Nm z v).Reachable A B
      exact heq ▸ ⟨SimpleGraph.Walk.nil⟩
  | single h =>
      intro ha hb
      let A : BranchChild v := ⟨_, ha⟩
      let B : BranchChild v := ⟨_, hb⟩
      change (childLinkGraph Nm z v).Reachable A B
      by_cases hab : A = B
      · exact hab ▸ ⟨SimpleGraph.Walk.nil⟩
      · exact ⟨SimpleGraph.Walk.cons
          (show (childLinkGraph Nm z v).Adj A B from
            ⟨hab, h.2.2⟩)
          SimpleGraph.Walk.nil⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      intro ha hb
      have hm := linkChain_end_mem h₁ ha
      obtain ⟨p⟩ := ih₁ ha hm
      obtain ⟨q⟩ := ih₂ hm hb
      exact ⟨p.append q⟩

/-- A branch vertex has at least one child, packaged as nonemptiness of the
child subtype. -/
theorem branchChild_nonempty {t : PlaneTree} {v : VPos t}
    (hv : v ∈ BranchNodes t) :
    Nonempty (BranchChild v) := by
  have htwo : 2 ≤ childCount t v.1 :=
    mem_BranchNodes_iff.mp hv
  have hcard : 0 < (childrenOf v).card := by
    rw [childrenOf_eq_graphChildren, card_graphChildren_eq_childCount]
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hcard
  exact ⟨⟨c, hc⟩⟩

/-- `LinkedChildren` is precisely enough to make the undirected child-link
graph connected.  Self-steps in its reflexive-transitive chain are discarded
when converting to walks of the irreflexive graph. -/
theorem childLinkGraph_connected {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v) :
    (childLinkGraph Nm z v).Connected := by
  refine
    { preconnected := ?_
      nonempty := branchChild_nonempty hv }
  intro a b
  exact reachable_childLinkGraph_of_chain a.2 b.2
    (hlinked a.1 a.2 b.1 b.2)

/-! ## Shortest-path parent map -/

/-- Orient a chosen shortest-path edge from every child toward the fixed
root child.  The root points to itself. -/
noncomputable def linkParent {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) :
    BranchChild v → BranchChild v :=
  SimpleGraph.parentTowardRoot (childLinkGraph Nm z v)
    (childLinkGraph_connected hv hlinked) root

@[simp] theorem linkParent_root {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) :
    linkParent hv hlinked root root = root := by
  exact SimpleGraph.parentTowardRoot_root
    (childLinkGraph Nm z v) (childLinkGraph_connected hv hlinked) root

/-- Every non-root child is adjacent to its chosen parent. -/
theorem childLinkGraph_adj_linkParent {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) {c : BranchChild v} (hc : c ≠ root) :
    (childLinkGraph Nm z v).Adj c
      (linkParent hv hlinked root c) := by
  exact SimpleGraph.adj_parentTowardRoot
    (childLinkGraph Nm z v) (childLinkGraph_connected hv hlinked) root hc

/-- In particular, the selected parent is linked to its child in the
original geometric relation. -/
theorem isLink_linkParent {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) {c : BranchChild v} (hc : c ≠ root) :
    IsLink Nm z v c.1 (linkParent hv hlinked root c).1 :=
  (childLinkGraph_adj_linkParent hv hlinked root hc).2

/-- A non-root child never points to itself. -/
theorem linkParent_ne_self {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) {c : BranchChild v} (hc : c ≠ root) :
    linkParent hv hlinked root c ≠ c :=
  SimpleGraph.parentTowardRoot_ne_self
    (childLinkGraph Nm z v) (childLinkGraph_connected hv hlinked) root hc

/-- Following a selected parent strictly lowers graph distance to the fixed
root. -/
theorem linkParent_dist_lt {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) {c : BranchChild v} (hc : c ≠ root) :
    (childLinkGraph Nm z v).dist
        (linkParent hv hlinked root c) root
      < (childLinkGraph Nm z v).dist c root :=
  SimpleGraph.dist_parentTowardRoot_lt
    (childLinkGraph Nm z v) (childLinkGraph_connected hv hlinked) root hc

/-! ## Enumeration in increasing graph distance -/

/-- All children, stably sorted by nondecreasing link-graph distance to the
fixed root.  Ties are harmless: the parent distance is strictly smaller. -/
noncomputable def childrenByLinkDistance {t : PlaneTree}
    (Nm : HeppMarking t) (z : LeafEmbedding t) (v : VPos t)
    (root : BranchChild v) : List (BranchChild v) :=
  (Finset.univ : Finset (BranchChild v)).toList.insertionSort
    fun a b =>
      (childLinkGraph Nm z v).dist a root ≤
        (childLinkGraph Nm z v).dist b root

@[simp] theorem mem_childrenByLinkDistance {t : PlaneTree}
    (Nm : HeppMarking t) (z : LeafEmbedding t) (v : VPos t)
    (root c : BranchChild v) :
    c ∈ childrenByLinkDistance Nm z v root := by
  simp [childrenByLinkDistance]

theorem childrenByLinkDistance_nodup {t : PlaneTree}
    (Nm : HeppMarking t) (z : LeafEmbedding t) (v : VPos t)
    (root : BranchChild v) :
    (childrenByLinkDistance Nm z v root).Nodup := by
  have hp :=
    List.perm_insertionSort
      (fun a b : BranchChild v =>
        (childLinkGraph Nm z v).dist a root ≤
          (childLinkGraph Nm z v).dist b root)
      (Finset.univ : Finset (BranchChild v)).toList
  apply hp.nodup_iff.mpr
  exact Finset.nodup_toList _

/-- The distance enumeration is pairwise nondecreasing. -/
theorem childrenByLinkDistance_pairwise {t : PlaneTree}
    (Nm : HeppMarking t) (z : LeafEmbedding t) (v : VPos t)
    (root : BranchChild v) :
    (childrenByLinkDistance Nm z v root).Pairwise
      (fun a b =>
        (childLinkGraph Nm z v).dist a root ≤
          (childLinkGraph Nm z v).dist b root) := by
  exact List.pairwise_insertionSort _ _

/-- In the distance-sorted enumeration, every non-root child's parent occurs
strictly earlier. -/
theorem idxOf_linkParent_lt {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) {c : BranchChild v} (hc : c ≠ root) :
    List.idxOf (linkParent hv hlinked root c)
        (childrenByLinkDistance Nm z v root) <
      List.idxOf c (childrenByLinkDistance Nm z v root) := by
  let L := childrenByLinkDistance Nm z v root
  change List.idxOf (linkParent hv hlinked root c) L <
    List.idxOf c L
  have hpMem : linkParent hv hlinked root c ∈ L := by
    exact mem_childrenByLinkDistance Nm z v root _
  have hcMem : c ∈ L :=
    mem_childrenByLinkDistance Nm z v root c
  have hpBound :
      List.idxOf (linkParent hv hlinked root c) L < L.length :=
    List.idxOf_lt_length_iff.mpr hpMem
  have hcBound : List.idxOf c L < L.length :=
    List.idxOf_lt_length_iff.mpr hcMem
  let ip : Fin L.length :=
    ⟨List.idxOf (linkParent hv hlinked root c) L, hpBound⟩
  let ic : Fin L.length := ⟨List.idxOf c L, hcBound⟩
  have hpGet : L.get ip = linkParent hv hlinked root c :=
    List.idxOf_get hpBound
  have hcGet : L.get ic = c :=
    List.idxOf_get hcBound
  have hidxNe : (ip : ℕ) ≠ (ic : ℕ) := by
    intro heq
    have hip : ip = ic := Fin.ext heq
    have hpc : linkParent hv hlinked root c = c := by
      calc
        linkParent hv hlinked root c = L.get ip := hpGet.symm
        _ = L.get ic := congrArg L.get hip
        _ = c := hcGet
    exact linkParent_ne_self hv hlinked root hc hpc
  have hidxNe' :
      List.idxOf (linkParent hv hlinked root c) L ≠
        List.idxOf c L := by
    simpa [ip, ic] using hidxNe
  by_contra hnot
  have hiclt : ic < ip := by
    change List.idxOf c L <
      List.idxOf (linkParent hv hlinked root c) L
    omega
  have hsorted :=
    (List.pairwise_iff_get.mp
      (childrenByLinkDistance_pairwise Nm z v root)) ic ip hiclt
  change
    (childLinkGraph Nm z v).dist (L.get ic) root ≤
      (childLinkGraph Nm z v).dist (L.get ip) root at hsorted
  rw [hcGet, hpGet] at hsorted
  have hdist := linkParent_dist_lt hv hlinked root hc
  omega

/-! ## Interface to the full parent-function space -/

/-- The selected link parent is already a full parent function, with no
quotient or partial-domain conversion. -/
noncomputable def linkParentFullFunction {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) :
    BranchChild v → BranchChild v :=
  linkParent hv hlinked root

@[simp] theorem linkParentFullFunction_mem_univ {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v) :
    linkParentFullFunction hv hlinked root ∈
      (Finset.univ : Finset (BranchChild v → BranchChild v)) :=
  Finset.mem_univ _

/-- Size of the enlarged, directly countable full-function space. -/
theorem card_branchChild_fullFunctionSpace {t : PlaneTree}
    (v : VPos t) :
    Fintype.card (BranchChild v → BranchChild v) =
      (childrenOf v).card ^ (childrenOf v).card := by
  rw [Fintype.card_fun]
  simp

/-- `fullParentWeight` of the selected map has exactly the expected
root-normalized edge-factor product. -/
theorem fullParentWeight_linkParent {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v)
    {R : Type*} [CommSemiring R]
    (parentWeight childWeight : BranchChild v → R) :
    fullParentWeight root parentWeight childWeight
        (linkParentFullFunction hv hlinked root) =
      ∏ c, if c = root then 1
        else parentWeight (linkParent hv hlinked root c) *
          childWeight c := by
  unfold fullParentWeight
  apply Finset.prod_congr rfl
  intro c _
  by_cases hc : c = root
  · subst c
    simp [linkParentFullFunction]
  · simp [hc, linkParentFullFunction]

/-- Natural weights of the selected parent map are bounded by the
factorized sum over the full function space.  This is the direct handoff to
`sum_fullParentWeight`. -/
theorem fullParentWeight_linkParent_le_all_nat {t : PlaneTree}
    {Nm : HeppMarking t} {z : LeafEmbedding t} {v : VPos t}
    (hv : v ∈ BranchNodes t) (hlinked : LinkedChildren Nm z v)
    (root : BranchChild v)
    (parentWeight childWeight : BranchChild v → ℕ) :
    fullParentWeight root parentWeight childWeight
        (linkParentFullFunction hv hlinked root) ≤
      ∏ c, if c = root then 1
        else (∑ u, parentWeight u) * childWeight c := by
  calc
    fullParentWeight root parentWeight childWeight
        (linkParentFullFunction hv hlinked root)
        ≤ ∑ p : BranchChild v → BranchChild v,
            fullParentWeight root parentWeight childWeight p := by
          exact Finset.single_le_sum
            (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ _)
    _ = _ := sum_fullParentWeight root parentWeight childWeight

end Anderson4D
