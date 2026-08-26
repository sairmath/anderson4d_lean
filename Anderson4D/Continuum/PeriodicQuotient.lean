import Anderson4D.Continuum.PrimitivePeriodicSum
import Anderson4D.ForMathlib.ConnectedParent
import Anderson4D.HeppTree.LatticeNormBridge
import Mathlib.Analysis.MeanInequalities
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Order.Interval.Finset.Fin

/-!
# Periodic quotient graphs for the primitive permutation sum

For a full pairing, identify the two positions of every covariance pair.
The linear word path descends to a connected multigraph on the `n` pair
vertices.  Its simple underlying graph has a spanning tree with `n - 1`
edges.  Lifting labels along those tree edges makes every retained edge an
ordinary no-wrap lattice edge; the other `n` word adjacencies are the
genuine winding/cycle edges and must be treated as skipped edges.

This file develops that quotient interface without comparing a periodic
edge pointwise to the canonical Euclidean edge.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## Mapping connected graphs by a possibly non-injective function -/

namespace SimpleGraph

/-- Mapping vertices may collapse an edge to a point.  After deleting those
loops, reachability is still preserved by `SimpleGraph.map`. -/
theorem reachable_map_function
    {V W : Type*} {G : SimpleGraph V} (f : V → W)
    {u v : V} (h : G.Reachable u v) :
    (G.map f).Reachable (f u) (f v) := by
  rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail b c hxy hyz ih =>
      by_cases heq : f b = f c
      · simpa only [heq] using ih
      · exact ih.tail (_root_.SimpleGraph.map_adj_apply' hyz heq)

/-- A surjective image of a connected graph is connected even when some
source edges collapse to loops. -/
theorem Connected.map_function
    {V W : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (f : V → W) (hf : Function.Surjective f) :
    (G.map f).Connected := by
  letI : Nonempty W := hG.nonempty.map f
  refine ⟨?_⟩
  intro a b
  obtain ⟨u, rfl⟩ := hf a
  obtain ⟨v, rfl⟩ := hf b
  exact reachable_map_function f (hG u v)

end SimpleGraph

/-! ## The word path modulo a full pairing -/

/-- Vertices of the quotient word graph: one canonical lower endpoint per
pair. -/
abbrev PairingVertex {m : ℕ} (κ : PartialPairing (Fin m)) :=
  pairingLowerHalf κ

/-- Quotient map from word positions to their covariance-pair vertex. -/
def pairingVertex
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (i : Fin m) : PairingVertex κ :=
  ⟨pairingAnchor κ i, pairingAnchor_mem_pairingLowerHalf hfull i⟩

@[simp]
theorem pairingVertex_apply
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (i : Fin m) :
    pairingVertex κ hfull (κ i) = pairingVertex κ hfull i := by
  apply Subtype.ext
  exact pairingAnchor_apply κ i

@[simp]
theorem pairingVertex_lower
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (i : PairingVertex κ) :
    pairingVertex κ hfull i.1 = i := by
  apply Subtype.ext
  exact pairingAnchor_eq_self_of_mem_pairingLowerHalf i.2

theorem pairingVertex_surjective
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Function.Surjective (pairingVertex κ hfull) := by
  intro i
  exact ⟨i.1, pairingVertex_lower κ hfull i⟩

/-- The simple graph obtained from the linear word path after identifying
paired positions.  Parallel word edges are deliberately forgotten here;
they reappear below as distinct adjacency indices. -/
def pairingQuotientGraph
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    SimpleGraph (PairingVertex κ) :=
  (SimpleGraph.pathGraph m).map (pairingVertex κ hfull)

theorem pairingQuotientGraph_connected
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    (pairingQuotientGraph κ hfull).Connected := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hpath : (SimpleGraph.pathGraph m).Connected :=
    ⟨SimpleGraph.pathGraph_preconnected m⟩
  exact Anderson4D.SimpleGraph.Connected.map_function hpath
    (pairingVertex κ hfull) (pairingVertex_surjective κ hfull)

/-- A chosen spanning tree of the pairing quotient graph. -/
def pairingQuotientTree
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    SimpleGraph (PairingVertex κ) :=
  Classical.choose
    (pairingQuotientGraph_connected hm κ hfull).exists_isTree_le

theorem pairingQuotientTree_le
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    pairingQuotientTree hm κ hfull ≤
      pairingQuotientGraph κ hfull :=
  (Classical.choose_spec
    (pairingQuotientGraph_connected hm κ hfull).exists_isTree_le).1

theorem pairingQuotientTree_isTree
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    (pairingQuotientTree hm κ hfull).IsTree :=
  (Classical.choose_spec
    (pairingQuotientGraph_connected hm κ hfull).exists_isTree_le).2

theorem pairingQuotientTree_edge_card
    {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    Nat.card
        (pairingQuotientTree (by omega) κ hfull).edgeSet =
      n - 1 := by
  classical
  let T := pairingQuotientTree (m := 2 * n) (by omega) κ hfull
  have htree :=
    pairingQuotientTree_isTree (m := 2 * n)
      (by omega) κ hfull
  have hcard :=
    (_root_.SimpleGraph.isTree_iff_connected_and_card
      (G := T)).mp htree |>.2
  have hvertices :
      Nat.card (PairingVertex κ) = n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe,
      card_pairingLowerHalf_eq κ hfull]
  rw [hvertices] at hcard
  change Nat.card T.edgeSet = n - 1
  omega

/-! ## Choosing the `n - 1` word edges of the quotient spanning tree -/

/-- The unordered pair of quotient vertices carried by one adjacency of the
original word.  It may be diagonal when two paired occurrences are adjacent. -/
def wordQuotientEdge
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (j : AdjacentIndex m) : Sym2 (PairingVertex κ) :=
  s(pairingVertex κ hfull j.1,
    pairingVertex κ hfull (adjacentSucc j))

/-- Every edge of the quotient spanning tree is represented by at least one
actual adjacency index of the original word. -/
theorem exists_wordAdjacency_represents_treeEdge
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (e : (pairingQuotientTree hm κ hfull).edgeSet) :
    ∃ j : AdjacentIndex m,
      wordQuotientEdge κ hfull j = e.1 := by
  have heTree :
      (pairingQuotientTree hm κ hfull).Adj e.1.out.1 e.1.out.2 :=
    (_root_.SimpleGraph.mem_edgeSet _).mp (by
      rw [Sym2.mk, e.1.out_eq]
      exact e.2)
  have heQuot :
      (pairingQuotientGraph κ hfull).Adj e.1.out.1 e.1.out.2 :=
    pairingQuotientTree_le hm κ hfull heTree
  rcases
      (_root_.SimpleGraph.map_adj' (pairingVertex κ hfull)
        (SimpleGraph.pathGraph m) e.1.out.1 e.1.out.2).mp heQuot with
    ⟨hne, i, k, hik, hi, hk⟩
  rw [_root_.SimpleGraph.pathGraph_adj] at hik
  rcases hik with hik | hki
  · let j : AdjacentIndex m :=
      ⟨i, by
        rw [hik]
        exact k.2⟩
    refine ⟨j, ?_⟩
    rw [wordQuotientEdge]
    have hsucc : adjacentSucc j = k := by
      apply Fin.ext
      exact hik
    rw [hsucc, hi, hk]
    rw [Sym2.mk, e.1.out_eq]
  · let j : AdjacentIndex m :=
      ⟨k, by
        rw [hki]
        exact i.2⟩
    refine ⟨j, ?_⟩
    rw [wordQuotientEdge]
    have hsucc : adjacentSucc j = i := by
      apply Fin.ext
      exact hki
    rw [hsucc, hk, hi, Sym2.eq_swap]
    rw [Sym2.mk, e.1.out_eq]

/-- A deterministic representative word adjacency for a quotient-tree edge. -/
def treeEdgeWordRepresentative
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (e : (pairingQuotientTree hm κ hfull).edgeSet) :
    AdjacentIndex m :=
  Classical.choose
    (exists_wordAdjacency_represents_treeEdge hm κ hfull e)

theorem treeEdgeWordRepresentative_spec
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (e : (pairingQuotientTree hm κ hfull).edgeSet) :
    wordQuotientEdge κ hfull
        (treeEdgeWordRepresentative hm κ hfull e) =
      e.1 :=
  Classical.choose_spec
    (exists_wordAdjacency_represents_treeEdge hm κ hfull e)

theorem treeEdgeWordRepresentative_injective
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Function.Injective
      (treeEdgeWordRepresentative hm κ hfull) := by
  intro e e' heq
  apply Subtype.ext
  rw [← treeEdgeWordRepresentative_spec hm κ hfull e,
    ← treeEdgeWordRepresentative_spec hm κ hfull e', heq]

/-- The selected word adjacencies representing the quotient spanning tree. -/
def quotientTreeWordEdges
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Finset (AdjacentIndex m) := by
  classical
  let T := pairingQuotientTree hm κ hfull
  letI : Fintype T.edgeSet := Fintype.ofFinite T.edgeSet
  exact Finset.univ.image
    (treeEdgeWordRepresentative hm κ hfull)

theorem card_quotientTreeWordEdges
    {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    (quotientTreeWordEdges (by omega) κ hfull).card = n - 1 := by
  classical
  let T :=
    pairingQuotientTree (m := 2 * n) (by omega) κ hfull
  letI : Fintype T.edgeSet := Fintype.ofFinite T.edgeSet
  unfold quotientTreeWordEdges
  rw [Finset.card_image_of_injective _
    (treeEdgeWordRepresentative_injective (by omega) κ hfull)]
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact pairingQuotientTree_edge_card hn κ hfull

/-- The genuine winding/cycle adjacencies: every word edge not selected for
the quotient spanning tree. -/
def quotientCycleWordEdges
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Finset (AdjacentIndex m) :=
  Finset.univ \ quotientTreeWordEdges hm κ hfull

/-- A full pairing on `2n` positions has exactly `n` cycle/skipped word
edges after retaining a quotient spanning tree. -/
theorem card_quotientCycleWordEdges
    {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    (quotientCycleWordEdges (by omega) κ hfull).card = n := by
  classical
  unfold quotientCycleWordEdges
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, card_quotientTreeWordEdges hn κ hfull]
  have hadj :
      Fintype.card (AdjacentIndex (2 * n)) = 2 * n - 1 := by
    simpa using Fintype.card_congr (adjacentIndexEquiv (2 * n))
  rw [hadj]
  omega

/-! ## Rooted tree lifts of the pair labels -/

/-- Root pair vertex, chosen as the pair containing word position zero. -/
def pairingQuotientRoot
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    PairingVertex κ :=
  pairingVertex κ hfull ⟨0, hm⟩

/-- The chosen quotient-tree parent. -/
def pairingQuotientParent
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (v : PairingVertex κ) : PairingVertex κ :=
  Anderson4D.SimpleGraph.parentTowardRoot
    (pairingQuotientTree hm κ hfull)
    (pairingQuotientTree_isTree hm κ hfull).connected
    (pairingQuotientRoot hm κ hfull) v

@[simp]
theorem pairingQuotientParent_root
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    pairingQuotientParent hm κ hfull
        (pairingQuotientRoot hm κ hfull) =
      pairingQuotientRoot hm κ hfull := by
  exact Anderson4D.SimpleGraph.parentTowardRoot_root
    (pairingQuotientTree hm κ hfull)
    (pairingQuotientTree_isTree hm κ hfull).connected
    (pairingQuotientRoot hm κ hfull)

theorem pairingQuotientTree_adj_parent
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    {v : PairingVertex κ}
    (hv : v ≠ pairingQuotientRoot hm κ hfull) :
    (pairingQuotientTree hm κ hfull).Adj v
      (pairingQuotientParent hm κ hfull v) := by
  exact Anderson4D.SimpleGraph.adj_parentTowardRoot
    (pairingQuotientTree hm κ hfull)
    (pairingQuotientTree_isTree hm κ hfull).connected
    (pairingQuotientRoot hm κ hfull) hv

theorem pairingQuotientTree_dist_parent_lt
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    {v : PairingVertex κ}
    (hv : v ≠ pairingQuotientRoot hm κ hfull) :
    (pairingQuotientTree hm κ hfull).dist
        (pairingQuotientParent hm κ hfull v)
        (pairingQuotientRoot hm κ hfull) <
      (pairingQuotientTree hm κ hfull).dist v
        (pairingQuotientRoot hm κ hfull) := by
  exact Anderson4D.SimpleGraph.dist_parentTowardRoot_lt
    (pairingQuotientTree hm κ hfull)
    (pairingQuotientTree_isTree hm κ hfull).connected
    (pairingQuotientRoot hm κ hfull) hv

/-- Lift one label per covariance pair recursively from the quotient root.
Every non-root label is replaced by the whole-period translate nearest to
its already lifted parent. -/
noncomputable def quotientTreeLift
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (q : ℤ) (a : PairingVertex κ → Z4)
    (v : PairingVertex κ) : Z4 :=
  if _hv : v = pairingQuotientRoot hm κ hfull then
    a v
  else
    nearestPeriodTranslate q
      (quotientTreeLift hm κ hfull q a
        (pairingQuotientParent hm κ hfull v))
      (a v)
termination_by
  (pairingQuotientTree hm κ hfull).dist v
    (pairingQuotientRoot hm κ hfull)
decreasing_by
  exact pairingQuotientTree_dist_parent_lt hm κ hfull _hv

theorem quotientTreeLift_eq_root
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (q : ℤ) (a : PairingVertex κ → Z4) :
    quotientTreeLift hm κ hfull q a
        (pairingQuotientRoot hm κ hfull) =
      a (pairingQuotientRoot hm κ hfull) := by
  rw [quotientTreeLift]
  simp

theorem quotientTreeLift_eq_nearest_parent
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (q : ℤ) (a : PairingVertex κ → Z4)
    {v : PairingVertex κ}
    (hv : v ≠ pairingQuotientRoot hm κ hfull) :
    quotientTreeLift hm κ hfull q a v =
      nearestPeriodTranslate q
        (quotientTreeLift hm κ hfull q a
          (pairingQuotientParent hm κ hfull v))
        (a v) := by
  rw [quotientTreeLift]
  simp only [hv, ↓reduceDIte]

/-- Every recursively lifted label has the same torus centre as its original
pair label. -/
theorem latticeTorusCenter_quotientTreeLift
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) (v : PairingVertex κ) :
    latticeTorusCenter δ
        (quotientTreeLift hm κ hfull q a v) =
      latticeTorusCenter δ (a v) := by
  by_cases hv : v = pairingQuotientRoot hm κ hfull
  · subst v
    rw [quotientTreeLift_eq_root]
  · rw [quotientTreeLift_eq_nearest_parent hm κ hfull q a hv]
    exact latticeTorusCenter_nearestPeriodTranslate hq _ _

/-- Every rooted quotient-tree edge is an exact no-wrap edge after lifting. -/
theorem quotientTreeLift_parent_noWrap
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) {v : PairingVertex κ}
    (hv : v ≠ pairingQuotientRoot hm κ hfull) :
    LatticeEdgeNoWrap δ
      (quotientTreeLift hm κ hfull q a
        (pairingQuotientParent hm κ hfull v))
      (quotientTreeLift hm κ hfull q a v) := by
  rw [quotientTreeLift_eq_nearest_parent hm κ hfull q a hv]
  exact nearestPeriodTranslate_edgeNoWrap hq _ _

/-- Hence the periodic edge on a rooted tree edge is literally its ordinary
lattice edge weight. -/
theorem periodicCellEdgeWeight_quotientTreeLift_parent
    {δ : ℝ} (hδ : 0 < δ) {q : ℤ}
    (hq : PeriodCompatibleMesh δ q)
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) {v : PairingVertex κ}
    (hv : v ≠ pairingQuotientRoot hm κ hfull) :
    periodicCellEdgeWeight δ
        (quotientTreeLift hm κ hfull q a v)
        (quotientTreeLift hm κ hfull q a
          (pairingQuotientParent hm κ hfull v)) =
      latticeEdgeWeight
        (quotientTreeLift hm κ hfull q a v)
        (quotientTreeLift hm κ hfull q a
          (pairingQuotientParent hm κ hfull v)) := by
  rw [periodicCellEdgeWeight_comm, latticeEdgeWeight_comm]
  apply periodicCellEdgeWeight_eq_latticeEdgeWeight_of_noWrap hδ
  exact latticeTorusCenter_dist_eq_of_edgeNoWrap hδ
    (quotientTreeLift_parent_noWrap hq hm κ hfull a hv)

/-! ## Parent-oriented word edges -/

/-- Non-root pair vertices, the natural carrier of rooted tree edges. -/
def nonrootPairingVertices
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Finset (PairingVertex κ) :=
  Finset.univ.erase (pairingQuotientRoot hm κ hfull)

@[simp]
theorem mem_nonrootPairingVertices
    {m : ℕ} {hm : 0 < m}
    {κ : PartialPairing (Fin m)} {hfull : κ.IsFull}
    {v : PairingVertex κ} :
    v ∈ nonrootPairingVertices hm κ hfull ↔
      v ≠ pairingQuotientRoot hm κ hfull := by
  simp [nonrootPairingVertices]

theorem card_nonrootPairingVertices
    {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    (nonrootPairingVertices (by omega) κ hfull).card = n - 1 := by
  classical
  unfold nonrootPairingVertices
  rw [Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_coe,
    card_pairingLowerHalf_eq κ hfull]

/-- Any rooted quotient-tree edge has an actual word-adjacency witness. -/
theorem exists_wordAdjacency_represents_parentEdge
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (v : PairingVertex κ)
    (hv : v ≠ pairingQuotientRoot hm κ hfull) :
    ∃ j : AdjacentIndex m,
      wordQuotientEdge κ hfull j =
        s(v, pairingQuotientParent hm κ hfull v) := by
  let e : (pairingQuotientTree hm κ hfull).edgeSet :=
    ⟨s(v, pairingQuotientParent hm κ hfull v),
      (_root_.SimpleGraph.mem_edgeSet _).mpr
        (pairingQuotientTree_adj_parent hm κ hfull hv)⟩
  simpa only [e] using
    exists_wordAdjacency_represents_treeEdge hm κ hfull e

/-- Chosen word adjacency for a rooted quotient-tree edge. -/
def parentEdgeWordRepresentative
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (v : ↥(nonrootPairingVertices hm κ hfull)) :
    AdjacentIndex m :=
  Classical.choose
    (exists_wordAdjacency_represents_parentEdge
      hm κ hfull v.1
      (mem_nonrootPairingVertices.mp v.2))

theorem parentEdgeWordRepresentative_spec
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (v : ↥(nonrootPairingVertices hm κ hfull)) :
    wordQuotientEdge κ hfull
        (parentEdgeWordRepresentative hm κ hfull v) =
      s(v.1, pairingQuotientParent hm κ hfull v.1) :=
  Classical.choose_spec
    (exists_wordAdjacency_represents_parentEdge
      hm κ hfull v.1
      (mem_nonrootPairingVertices.mp v.2))

theorem parentEdgeWordRepresentative_injective
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Function.Injective
      (parentEdgeWordRepresentative hm κ hfull) := by
  intro v w hvw
  have hedge :
      s(v.1, pairingQuotientParent hm κ hfull v.1) =
        s(w.1, pairingQuotientParent hm κ hfull w.1) := by
    rw [← parentEdgeWordRepresentative_spec hm κ hfull v,
      ← parentEdgeWordRepresentative_spec hm κ hfull w, hvw]
  rcases Sym2.eq_iff.mp hedge with hsame | hswap
  · apply Subtype.ext
    exact hsame.1
  · have hvroot :
        v.1 ≠ pairingQuotientRoot hm κ hfull :=
      mem_nonrootPairingVertices.mp v.2
    have hwroot :
        w.1 ≠ pairingQuotientRoot hm κ hfull :=
      mem_nonrootPairingVertices.mp w.2
    have hvdist :=
      pairingQuotientTree_dist_parent_lt hm κ hfull hvroot
    have hwdist :=
      pairingQuotientTree_dist_parent_lt hm κ hfull hwroot
    rw [hswap.2, hswap.1] at hvdist
    omega

/-- Parent-oriented selected word adjacencies. -/
def quotientParentWordEdges
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Finset (AdjacentIndex m) :=
  (nonrootPairingVertices hm κ hfull).attach.image
    (parentEdgeWordRepresentative hm κ hfull)

theorem card_quotientParentWordEdges
    {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    (quotientParentWordEdges (by omega) κ hfull).card = n - 1 := by
  classical
  unfold quotientParentWordEdges
  rw [Finset.card_image_of_injective _
    (parentEdgeWordRepresentative_injective (by omega) κ hfull),
    Finset.card_attach, card_nonrootPairingVertices hn κ hfull]

/-- Cycle/skipped adjacencies for the parent-oriented lift. -/
def quotientParentCycleEdges
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    Finset (AdjacentIndex m) :=
  Finset.univ \ quotientParentWordEdges hm κ hfull

theorem card_quotientParentCycleEdges
    {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    (quotientParentCycleEdges (by omega) κ hfull).card = n := by
  classical
  unfold quotientParentCycleEdges
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, card_quotientParentWordEdges hn κ hfull]
  have hadj :
      Fintype.card (AdjacentIndex (2 * n)) = 2 * n - 1 := by
    simpa using Fintype.card_congr (adjacentIndexEquiv (2 * n))
  rw [hadj]
  omega

/-! ## The quotient-tree word and its skipped-chain comparison -/

/-- Literal paired word obtained from the rooted whole-period lifts. -/
def quotientTreeLiftedWord
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (q : ℤ) (a : PairingVertex κ → Z4) :
    Fin m → Z4 :=
  fun i =>
    quotientTreeLift hm κ hfull q a
      (pairingVertex κ hfull i)

theorem quotientTreeLiftedWord_respectsPairing
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (q : ℤ) (a : PairingVertex κ → Z4) :
    RespectsPairing κ
      (quotientTreeLiftedWord hm κ hfull q a) := by
  intro i
  unfold quotientTreeLiftedWord
  rw [pairingVertex_apply]

/-- The quotient-tree word represents the same torus centres as the copied
word before lifting. -/
theorem quotientTreeLiftedWord_center
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) (i : Fin m) :
    latticeTorusCenter δ
        (quotientTreeLiftedWord hm κ hfull q a i) =
      latticeTorusCenter δ
        (copiedPairingLabels κ hfull a i) := by
  unfold quotientTreeLiftedWord copiedPairingLabels pairingVertex
  exact latticeTorusCenter_quotientTreeLift
    hq hm κ hfull a
      ⟨pairingAnchor κ i,
        pairingAnchor_mem_pairingLowerHalf hfull i⟩

/-- Generic lattice chain product in which the edges in `O` are omitted. -/
def latticeWordChainWeightExcept
    {m : ℕ} (O : Finset (AdjacentIndex m))
    (u : Fin m → Z4) : ℝ :=
  ∏ j : AdjacentIndex m,
    if j ∈ O then 1
    else latticeEdgeWeight (u j.1) (u (adjacentSucc j))

theorem latticeWordChainWeightExcept_nonneg
    {m : ℕ} (O : Finset (AdjacentIndex m))
    (u : Fin m → Z4) :
    0 ≤ latticeWordChainWeightExcept O u := by
  unfold latticeWordChainWeightExcept
  apply Finset.prod_nonneg
  intro j hj
  split_ifs
  · exact zero_le_one
  · exact latticeEdgeWeight_nonneg _ _

/-- Periodic chain product on a copied-pair word. -/
def periodicCopiedWordChainWeight
    {m : ℕ} (δ : ℝ)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) : ℝ :=
  ∏ j : AdjacentIndex m,
    periodicCellEdgeWeight δ
      (copiedPairingLabels κ hfull a j.1)
      (copiedPairingLabels κ hfull a (adjacentSucc j))

theorem periodicCellEdgeWeight_le_one
    {δ : ℝ} (hδ : 0 < δ) (x y : Z4) :
    periodicCellEdgeWeight δ x y ≤ 1 := by
  unfold periodicCellEdgeWeight
  apply (div_le_one (by positivity :
    0 < δ ^ 2 + dist
      (latticeTorusCenter δ x) (latticeTorusCenter δ y) ^ 2)).mpr
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- A selected parent edge has identical periodic and ordinary weights on
the quotient-tree lift. -/
theorem periodicCopiedEdge_eq_latticeLifted_of_mem_parentEdges
    {δ : ℝ} (hδ : 0 < δ) {q : ℤ}
    (hq : PeriodCompatibleMesh δ q)
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) {j : AdjacentIndex m}
    (hj : j ∈ quotientParentWordEdges hm κ hfull) :
    periodicCellEdgeWeight δ
        (copiedPairingLabels κ hfull a j.1)
        (copiedPairingLabels κ hfull a (adjacentSucc j)) =
      latticeEdgeWeight
        (quotientTreeLiftedWord hm κ hfull q a j.1)
        (quotientTreeLiftedWord hm κ hfull q a
          (adjacentSucc j)) := by
  obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
  have hvroot :
      v.1 ≠ pairingQuotientRoot hm κ hfull :=
    mem_nonrootPairingVertices.mp v.2
  have hedge :=
    parentEdgeWordRepresentative_spec hm κ hfull v
  rw [hvj] at hedge
  unfold wordQuotientEdge at hedge
  have hperiodCentersLeft :=
    quotientTreeLiftedWord_center hq hm κ hfull a j.1
  have hperiodCentersRight :=
    quotientTreeLiftedWord_center hq hm κ hfull a
      (adjacentSucc j)
  have hperiodic :
      periodicCellEdgeWeight δ
          (copiedPairingLabels κ hfull a j.1)
          (copiedPairingLabels κ hfull a (adjacentSucc j)) =
        periodicCellEdgeWeight δ
          (quotientTreeLiftedWord hm κ hfull q a j.1)
          (quotientTreeLiftedWord hm κ hfull q a
            (adjacentSucc j)) := by
    unfold periodicCellEdgeWeight
    rw [hperiodCentersLeft, hperiodCentersRight]
  rw [hperiodic]
  rcases Sym2.eq_iff.mp hedge with hsame | hswap
  · change
      periodicCellEdgeWeight δ
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull j.1))
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull (adjacentSucc j))) =
        latticeEdgeWeight
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull j.1))
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull (adjacentSucc j)))
    rw [hsame.1, hsame.2]
    exact periodicCellEdgeWeight_quotientTreeLift_parent
      hδ hq hm κ hfull a hvroot
  · change
      periodicCellEdgeWeight δ
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull j.1))
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull (adjacentSucc j))) =
        latticeEdgeWeight
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull j.1))
          (quotientTreeLift hm κ hfull q a
            (pairingVertex κ hfull (adjacentSucc j)))
    rw [hswap.1, hswap.2, periodicCellEdgeWeight_comm,
      latticeEdgeWeight_comm]
    exact periodicCellEdgeWeight_quotientTreeLift_parent
      hδ hq hm κ hfull a hvroot

/-- **Periodic quotient-tree chain bridge.**

The complete periodic copied chain is bounded by the ordinary lattice chain
of a literal paired lift after skipping exactly the quotient cycle edges.
There is no mesh-dependent multiplicative factor. -/
theorem periodicCopiedWordChainWeight_le_quotientTreeLift
    {δ : ℝ} (hδ : 0 < δ) {q : ℤ}
    (hq : PeriodCompatibleMesh δ q)
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) :
    periodicCopiedWordChainWeight δ κ hfull a ≤
      latticeWordChainWeightExcept
        (quotientParentCycleEdges hm κ hfull)
        (quotientTreeLiftedWord hm κ hfull q a) := by
  unfold periodicCopiedWordChainWeight
    latticeWordChainWeightExcept
  apply Finset.prod_le_prod
  · intro j hj
    exact periodicCellEdgeWeight_nonneg _ _ _
  · intro j hj
    by_cases hcycle :
        j ∈ quotientParentCycleEdges hm κ hfull
    · rw [if_pos hcycle]
      exact periodicCellEdgeWeight_le_one hδ _ _
    · rw [if_neg hcycle]
      apply le_of_eq
      apply periodicCopiedEdge_eq_latticeLifted_of_mem_parentEdges
        hδ hq hm κ hfull a
      unfold quotientParentCycleEdges at hcycle
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        not_not] using hcycle

/-! ## Uniform absorption of the canonical copied diameter -/

/-- On the compatible mesh, the canonical torus-grid radius is no larger
than the number of cells in one period. -/
theorem compatible_torusGridRadius_le_cellCount
    {ε : ℝ} (hε : 0 < ε) :
    torusGridRadius (compatibleMeshSize ε) ≤
      compatibleCellCount ε := by
  unfold torusGridRadius
  apply Int.ceil_le.mpr
  let δ := compatibleMeshSize ε
  let q := compatibleCellCount ε
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hperiod : δ * (q : ℝ) = 2 * Real.pi :=
    (compatibleMesh_isPeriodCompatible hε).period_eq
  apply (div_le_iff₀ hδ).mpr
  nlinarith [Real.pi_pos]

/-- Coordinate bound for every label in the canonical copied carrier,
expressed directly in terms of the period cell count. -/
theorem primitiveCanonicalCellCarrier_abs_le_cellCount
    {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    {κ : PartialPairing (Fin (2 * n))}
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalCellCarrier ε n κ) :
    ∀ j i, |y j i| ≤ compatibleCellCount ε := by
  intro j i
  have hbox :=
    (rdec_mem_boundedTuples.mp
      (primitiveCanonicalCellCarrier_mem_bounded hε hy)) j i
  rw [primitiveCopiedBoxRadius_cast hε] at hbox
  exact hbox.trans (compatible_torusGridRadius_le_cellCount hε)

/-- Sup-norm difference bound in an integer box whose half-width is a
positive integer `q`. -/
theorem znorm_sub_le_two_mul_int
    {q : ℤ} (hq : 0 < q) {x y : Z4}
    (hx : ∀ i, |x i| ≤ q) (hy : ∀ i, |y i| ≤ q) :
    znorm (x - y) ≤ 2 * (q : ℝ) := by
  have hqR : 0 ≤ (q : ℝ) := by
    exact_mod_cast hq.le
  have hpos : (0 : ℝ) ≤ 2 * (q : ℝ) := by positivity
  rw [znorm, pi_norm_le_iff_of_nonneg hpos]
  intro i
  have hZ : |x i - y i| ≤ 2 * q := by
    have h1 : |x i - y i| ≤ |x i| + |y i| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (x i) (-(y i))
    have hxi := hx i
    have hyi := hy i
    omega
  have hcast :
      |(x i : ℝ) - (y i : ℝ)| ≤ 2 * (q : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at h ⊢
    simpa using h
  calc
    ‖((x - y) i : ℝ)‖ =
        |(x i : ℝ) - (y i : ℝ)| := by
      rw [Real.norm_eq_abs]
      norm_num [Pi.sub_apply]
    _ ≤ 2 * (q : ℝ) := hcast

/-- The literal diameter of a tuple in the canonical copied carrier is
quadratic in the period cell count, with no hidden box constant. -/
theorem primitiveCanonicalCellDiameter_le_cellCount
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    {κ : PartialPairing (Fin (2 * n))}
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalCellCarrier ε n κ) :
    primitiveTupleDiameterBracketSq (by omega) y ≤
      1 + 4 * (compatibleCellCount ε : ℝ) ^ 2 := by
  have hq := compatibleCellCount_pos hε
  have hcoord :=
    primitiveCanonicalCellCarrier_abs_le_cellCount hε hy
  unfold primitiveTupleDiameterBracketSq
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  have hnorm :
      znorm (y i - y j) ≤
        2 * (compatibleCellCount ε : ℝ) :=
    znorm_sub_le_two_mul_int hq (hcoord i) (hcoord j)
  have hnorm0 := znorm_nonneg (y i - y j)
  unfold latticeBracketSq
  nlinarith [mul_nonneg
    (sub_nonneg.mpr hnorm)
    (add_nonneg hnorm0 (by positivity :
      0 ≤ 2 * (compatibleCellCount ε : ℝ)))]

/-- **Uniform diameter ledger.**  The cell-volume factor `δ²` absorbs the
canonical copied diameter.  The numerical constant is deliberately simple;
most importantly, it is independent of both `ε` and the mesh cardinality. -/
theorem compatibleMesh_sq_mul_primitiveCopiedDiameter_le
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    {κ : PartialPairing (Fin (2 * n))}
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalCellCarrier ε n κ) :
    compatibleMeshSize ε ^ 2 *
        primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) ≤
      20 * Real.pi ^ 2 := by
  let δ := compatibleMeshSize ε
  let q := compatibleCellCount ε
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hq : 0 < q := compatibleCellCount_pos hε
  have hqR : 1 ≤ (q : ℝ) := by
    exact_mod_cast hq
  have hperiod : δ * (q : ℝ) = 2 * Real.pi :=
    (compatibleMesh_isPeriodCompatible hε).period_eq
  have hdiam :
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) ≤
        1 + 4 * (q : ℝ) ^ 2 := by
    rw [← primitiveCopiedCellDiameter_eq_reductionDiameter n hn y]
    exact primitiveCanonicalCellDiameter_le_cellCount hε hn hy
  have hδle : δ ≤ 2 * Real.pi := by
    have hmul :
        0 ≤ δ * ((q : ℝ) - 1) :=
      mul_nonneg hδ.le (sub_nonneg.mpr hqR)
    nlinarith
  have hδsq : δ ^ 2 ≤ 4 * Real.pi ^ 2 := by
    have hmul :
        0 ≤ (2 * Real.pi - δ) * (δ + 2 * Real.pi) :=
      mul_nonneg (sub_nonneg.mpr hδle)
        (add_nonneg hδ.le (by positivity))
    nlinarith
  have hperiodSq :
      δ ^ 2 * (q : ℝ) ^ 2 = (2 * Real.pi) ^ 2 := by
    calc
      δ ^ 2 * (q : ℝ) ^ 2 =
          (δ * (q : ℝ)) ^ 2 := by ring
      _ = (2 * Real.pi) ^ 2 := by rw [hperiod]
  calc
    compatibleMeshSize ε ^ 2 *
        primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) =
        δ ^ 2 *
          primitiveTupleDiameterBracketSq (by omega)
            (primitiveCopiedReductionTuple n hn y) := by rfl
    _ ≤ δ ^ 2 * (1 + 4 * (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiam (sq_nonneg δ)
    _ = δ ^ 2 + 4 * (δ ^ 2 * (q : ℝ) ^ 2) := by ring
    _ = δ ^ 2 + 4 * (2 * Real.pi) ^ 2 := by rw [hperiodSq]
    _ ≤ 20 * Real.pi ^ 2 := by nlinarith

/-! ## The uniform primitive copied-weight bridge -/

/-- List form of the periodic terminal path product. -/
theorem listChainProduct_periodic_eq_terminal
    (δ : ℝ) (y e : Z4) (ys : List Z4) :
    listChainProduct (periodicCellEdgeWeight δ)
        (y :: (ys ++ [e])) =
      periodicTerminalPathWeight δ y e ys := by
  induction ys generalizing y with
  | nil =>
      simp [listChainProduct, periodicTerminalPathWeight]
  | cons a as ih =>
      rw [List.cons_append]
      simp only [listChainProduct, periodicTerminalPathWeight]
      rw [ih]

/-- The periodic word product is exactly the endpoint/internal-list product
used by the copied-cell analytic estimate. -/
theorem periodicCopiedWordChainWeight_eq_terminal
    {δ : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) :
    periodicCopiedWordChainWeight δ κ hfull a =
      periodicTerminalPathWeight δ
        (primitiveFirstCell n hn
          (copiedPairingLabels κ hfull a))
        (primitiveLastCell n hn
          (copiedPairingLabels κ hfull a))
        (primitiveInternalCellLabels n hn
          (copiedPairingLabels κ hfull a)) := by
  unfold periodicCopiedWordChainWeight
  rw [adjacentProduct_eq_listChainProduct,
    ← primitiveOriginalCellList_eq_ofFn]
  exact listChainProduct_periodic_eq_terminal _ _ _ _

/-- Uniform pointwise estimate for a copied-pair label assignment.  The
mesh-volume factor `δ²` pays for the literal canonical diameter, while the
quotient-tree lift leaves exactly `n` skipped word edges and no
mesh-dependent multiplier. -/
theorem compatibleMesh_sq_mul_primitivePeriodicCopiedWeight_le_lift
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4)
    (ha :
      copiedPairingLabels κ hfull a ∈
        primitiveCanonicalCellCarrier ε n κ) :
    compatibleMeshSize ε ^ 2 *
        primitivePeriodicCopiedWeight ε n hn
          (copiedPairingLabels κ hfull a) ≤
      20 * Real.pi ^ 2 *
        latticeWordChainWeightExcept
          (quotientParentCycleEdges (by omega) κ hfull)
          (quotientTreeLiftedWord (by omega) κ hfull
            (compatibleCellCount ε) a) := by
  let y := copiedPairingLabels κ hfull a
  let D :=
    primitiveTupleDiameterBracketSq (by omega)
      (primitiveCopiedReductionTuple n hn y)
  let P :=
    periodicCopiedWordChainWeight
      (compatibleMeshSize ε) κ hfull a
  let L :=
    latticeWordChainWeightExcept
      (quotientParentCycleEdges (by omega) κ hfull)
      (quotientTreeLiftedWord (by omega) κ hfull
        (compatibleCellCount ε) a)
  have hdiam :
      compatibleMeshSize ε ^ 2 * D ≤
        20 * Real.pi ^ 2 := by
    exact compatibleMesh_sq_mul_primitiveCopiedDiameter_le
      hε hn ha
  have hchain : P ≤ L := by
    exact periodicCopiedWordChainWeight_le_quotientTreeLift
      (compatibleMeshSize_pos hε)
      (compatibleMesh_isPeriodCompatible hε)
      (by omega) κ hfull a
  have hP : 0 ≤ P := by
    unfold P periodicCopiedWordChainWeight
    apply Finset.prod_nonneg
    intro j hj
    exact periodicCellEdgeWeight_nonneg _ _ _
  have hconstant : 0 ≤ 20 * Real.pi ^ 2 := by positivity
  have hweight :
      primitivePeriodicCopiedWeight ε n hn y = D * P := by
    unfold primitivePeriodicCopiedWeight D P y
    rw [periodicCopiedWordChainWeight_eq_terminal hn κ hfull a]
  rw [hweight]
  calc
    compatibleMeshSize ε ^ 2 * (D * P) =
        (compatibleMeshSize ε ^ 2 * D) * P := by ring
    _ ≤ (20 * Real.pi ^ 2) * P :=
      mul_le_mul_of_nonneg_right hdiam hP
    _ ≤ (20 * Real.pi ^ 2) * L :=
      mul_le_mul_of_nonneg_left hchain hconstant
    _ = 20 * Real.pi ^ 2 *
        latticeWordChainWeightExcept
          (quotientParentCycleEdges (by omega) κ hfull)
          (quotientTreeLiftedWord (by omega) κ hfull
            (compatibleCellCount ε) a) := by rfl

/-- Carrier-facing form of the preceding theorem: any literal paired tuple
is canonically restricted to one label per covariance pair before lifting. -/
theorem compatibleMesh_sq_mul_primitivePeriodicCopiedWeight_le_quotientLift
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalCellCarrier ε n κ) :
    compatibleMeshSize ε ^ 2 *
        primitivePeriodicCopiedWeight ε n hn y ≤
      20 * Real.pi ^ 2 *
        latticeWordChainWeightExcept
          (quotientParentCycleEdges (by omega) κ hfull)
          (quotientTreeLiftedWord (by omega) κ hfull
            (compatibleCellCount ε)
            (restrictToPairingLowerHalf κ
              ⟨y, (Finset.mem_filter.mp hy).2⟩)) := by
  let yp : {z : Fin (2 * n) → Z4 // RespectsPairing κ z} :=
    ⟨y, (Finset.mem_filter.mp hy).2⟩
  let a := restrictToPairingLowerHalf κ yp
  have hcopy :
      copiedPairingLabels κ hfull a = y := by
    have hright :=
      (copiedPairingLabelsEquiv κ hfull).apply_symm_apply yp
    exact congrArg Subtype.val hright
  have hcarrier :
      copiedPairingLabels κ hfull a ∈
        primitiveCanonicalCellCarrier ε n κ := by
    rw [hcopy]
    exact hy
  simpa only [yp, a, hcopy] using
    compatibleMesh_sq_mul_primitivePeriodicCopiedWeight_le_lift
      hε hn κ hfull a hcarrier

/-! ## Filtered sum and R-51 power ledgers -/

/-- The exact quotient-lifted skipped-chain sum corresponding to a filtered
periodic copied-cell sum.  It retains the original canonical labels as the
finite summation carrier, so this definition introduces neither a fiber
multiplicity nor a carrier-cardinality factor. -/
def primitivePeriodicQuotientLiftRealSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] : ℝ :=
  ∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
      (fun y => P (primitiveCopiedReductionTuple n hn y)),
    latticeWordChainWeightExcept
      (quotientParentCycleEdges (by omega) κ hfull)
      (quotientTreeLiftedWord (by omega) κ hfull
        (compatibleCellCount ε)
        (fun v : PairingVertex κ => y v.1))

theorem primitivePeriodicQuotientLiftRealSum_nonneg
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    0 ≤
      primitivePeriodicQuotientLiftRealSum
        ε n hn κ hfull P := by
  unfold primitivePeriodicQuotientLiftRealSum
  apply Finset.sum_nonneg
  intro y hy
  exact latticeWordChainWeightExcept_nonneg _ _

/-- Sum-level quotient bridge with an arbitrary endpoint/support predicate.
Its constant is uniform in the mesh and does not multiply by the cardinality
of the canonical carrier. -/
theorem compatibleMesh_sq_mul_periodicFilteredRealSum_le_quotient
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    compatibleMeshSize ε ^ 2 *
        primitivePeriodicReductionFilteredRealSum
          ε n hn κ P ≤
      20 * Real.pi ^ 2 *
        primitivePeriodicQuotientLiftRealSum
          ε n hn κ hfull P := by
  rw [primitivePeriodicReductionFilteredRealSum_eq_copied
    hε n hn κ P]
  unfold primitivePeriodicQuotientLiftRealSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hpoint :=
    compatibleMesh_sq_mul_primitivePeriodicCopiedWeight_le_quotientLift
      hε hn κ hfull (Finset.mem_filter.mp hy).1
  change
    compatibleMeshSize ε ^ 2 *
        primitivePeriodicCopiedWeight ε n hn y ≤
      20 * Real.pi ^ 2 *
        latticeWordChainWeightExcept
          (quotientParentCycleEdges (by omega) κ hfull)
          (quotientTreeLiftedWord (by omega) κ hfull
            (compatibleCellCount ε)
            (fun v : PairingVertex κ => y v.1)) at hpoint
  exact hpoint

/-- The exact power shift required by the inserted R-51 cell estimate:
`δ²` absorbs the copied diameter, leaving `δ^(4n-6)` and a universal
constant.  No quantity on the right grows with the compatible cell count. -/
theorem compatibleMesh_pow_mul_periodicFilteredRealSum_le_quotient
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    compatibleMeshSize ε ^ (4 * n - 4) *
        primitivePeriodicReductionFilteredRealSum
          ε n (by omega) κ P ≤
      20 * Real.pi ^ 2 *
        compatibleMeshSize ε ^ (4 * n - 6) *
          primitivePeriodicQuotientLiftRealSum
            ε n (by omega) κ hfull P := by
  let δ := compatibleMeshSize ε
  let S :=
    primitivePeriodicReductionFilteredRealSum
      ε n (by omega) κ P
  let Q :=
    primitivePeriodicQuotientLiftRealSum
      ε n (by omega) κ hfull P
  have hbridge :
      δ ^ 2 * S ≤ 20 * Real.pi ^ 2 * Q := by
    exact compatibleMesh_sq_mul_periodicFilteredRealSum_le_quotient
      hε (by omega) κ hfull P
  have hδpow : 0 ≤ δ ^ (4 * n - 6) :=
    pow_nonneg (compatibleMeshSize_pos hε).le _
  calc
    compatibleMeshSize ε ^ (4 * n - 4) *
        primitivePeriodicReductionFilteredRealSum
          ε n (by omega) κ P =
        δ ^ (4 * n - 6) * (δ ^ 2 * S) := by
      dsimp only [δ, S]
      have hexp : 4 * n - 4 = (4 * n - 6) + 2 := by omega
      rw [hexp, pow_add]
      ring
    _ ≤ δ ^ (4 * n - 6) * (20 * Real.pi ^ 2 * Q) :=
      mul_le_mul_of_nonneg_left hbridge hδpow
    _ = 20 * Real.pi ^ 2 * δ ^ (4 * n - 6) * Q := by ring
    _ = 20 * Real.pi ^ 2 *
        compatibleMeshSize ε ^ (4 * n - 6) *
          primitivePeriodicQuotientLiftRealSum
            ε n (by omega) κ hfull P := by rfl

/-- Extended-real form of the uniform R-51 power ledger. -/
theorem compatibleMesh_pow_mul_periodicFilteredSum_le_quotient
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    ENNReal.ofReal (compatibleMeshSize ε ^ (4 * n - 4)) *
        primitivePeriodicReductionFilteredSum
          ε n (by omega) κ P ≤
      ENNReal.ofReal
          (20 * Real.pi ^ 2 *
            compatibleMeshSize ε ^ (4 * n - 6)) *
        ENNReal.ofReal
          (primitivePeriodicQuotientLiftRealSum
            ε n (by omega) κ hfull P) := by
  rw [primitivePeriodicReductionFilteredSum_eq_ofReal]
  rw [← ENNReal.ofReal_mul
    (pow_nonneg (compatibleMeshSize_pos hε).le _)]
  rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity)
    (pow_nonneg (compatibleMeshSize_pos hε).le _) :
    0 ≤ 20 * Real.pi ^ 2 *
      compatibleMeshSize ε ^ (4 * n - 6))]
  exact ENNReal.ofReal_le_ofReal
    (compatibleMesh_pow_mul_periodicFilteredRealSum_le_quotient
      hε hn κ hfull P)

/-- Scalar-extracted form consumed by the endpoint cell estimate.  The two
nonnegative exhaustive-order coefficients are arbitrary; their common
`δ^(4n-4)` factor is replaced by `δ^(4n-6)` and the universal quotient
constant. -/
theorem primitivePeriodicReductionFilteredSum_scalar_le_quotient
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    (∑ u ∈
        ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
            ((2 * n - 1) + 1)).filter
          (RespectsPairing
            (primitiveReductionPairing n (by omega) κ))).filter P,
        ENNReal.ofReal q *
          (ENNReal.ofReal
              ((a * compatibleMeshSize ε ^ (4 * n - 4)) *
                primitivePeriodicReductionWeight
                  ε n (by omega) u) +
           ENNReal.ofReal
              ((b * compatibleMeshSize ε ^ (4 * n - 4)) *
                primitivePeriodicReductionWeight
                  ε n (by omega) u))) ≤
      ENNReal.ofReal q *
        (ENNReal.ofReal a + ENNReal.ofReal b) *
          ENNReal.ofReal
            (20 * Real.pi ^ 2 *
              compatibleMeshSize ε ^ (4 * n - 6)) *
            ENNReal.ofReal
              (primitivePeriodicQuotientLiftRealSum
                ε n (by omega) κ hfull P) := by
  have hδpow :
      0 ≤ compatibleMeshSize ε ^ (4 * n - 4) :=
    pow_nonneg (compatibleMeshSize_pos hε).le _
  have hfactor :=
    primitivePeriodicReductionFilteredSum_factor
      (a := a * compatibleMeshSize ε ^ (4 * n - 4))
      (b := b * compatibleMeshSize ε ^ (4 * n - 4))
      (q := q)
      (mul_nonneg ha hδpow) (mul_nonneg hb hδpow)
      ε n (by omega) κ P
  rw [hfactor]
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  have hscale :=
    compatibleMesh_pow_mul_periodicFilteredSum_le_quotient
      hε hn κ hfull P
  calc
    ENNReal.ofReal q *
          (ENNReal.ofReal a *
              ENNReal.ofReal
                (compatibleMeshSize ε ^ (4 * n - 4)) +
            ENNReal.ofReal b *
              ENNReal.ofReal
                (compatibleMeshSize ε ^ (4 * n - 4))) *
        primitivePeriodicReductionFilteredSum
          ε n (by omega) κ P =
        (ENNReal.ofReal q *
          (ENNReal.ofReal a + ENNReal.ofReal b)) *
          (ENNReal.ofReal
              (compatibleMeshSize ε ^ (4 * n - 4)) *
            primitivePeriodicReductionFilteredSum
              ε n (by omega) κ P) := by ring
    _ ≤ (ENNReal.ofReal q *
          (ENNReal.ofReal a + ENNReal.ofReal b)) *
        (ENNReal.ofReal
            (20 * Real.pi ^ 2 *
              compatibleMeshSize ε ^ (4 * n - 6)) *
          ENNReal.ofReal
            (primitivePeriodicQuotientLiftRealSum
              ε n (by omega) κ hfull P)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = ENNReal.ofReal q *
        (ENNReal.ofReal a + ENNReal.ofReal b) *
          ENNReal.ofReal
            (20 * Real.pi ^ 2 *
              compatibleMeshSize ε ^ (4 * n - 6)) *
            ENNReal.ofReal
              (primitivePeriodicQuotientLiftRealSum
                ε n (by omega) κ hfull P) := by ring

/-! ## Direct endpoint-integral interface -/

/-- **Uniform R-51 quotient reduction.**

This is the endpoint-fixed cell estimate with the false canonical
pointwise comparison and the old
`carrier.card × windingBoxBase × windingBoxAmplification` fallback removed.
The only remaining finite sum is the literal quotient-tree lift with exactly
`n` skipped edges. -/
theorem primitiveInsertedIntegrand_lintegral_le_periodicQuotientSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n)))
          (hκ : κ ∈ primitiveFullPairings n),
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farBase :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R
          let nearBase :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3)
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
              (ENNReal.ofReal farBase + ENNReal.ofReal nearBase) *
                ENNReal.ofReal
                  (20 * Real.pi ^ 2 * δ ^ (4 * n - 6)) *
                  ENNReal.ofReal
                    (primitivePeriodicQuotientLiftRealSum
                      ε n (by omega) κ
                        (mem_primitiveFullPairings.mp hκ).1
                      (primitiveCopiedEndpointSupported
                        ρ ε n (by omega) z w)) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hendpoint⟩ :=
    primitiveInsertedIntegrand_lintegral_le_periodicEndpointSum ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let farBase :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R
  let nearBase :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3)
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let P :=
    primitiveCopiedEndpointSupported
      ρ ε n (by omega) z w
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hfarBase : 0 ≤ farBase := by
    dsimp only [farBase]
    exact mul_nonneg
      (mul_nonneg
        (by positivity)
        (pow_nonneg
          (mul_nonneg hCcell.le
            (add_nonneg (sq_nonneg R) (pow_nonneg hR.le 4))) _))
      (terminalRadiusFactor_pos hR).le
  have hnearBase : 0 ≤ nearBase := by
    dsimp only [nearBase]
    exact mul_nonneg (by positivity)
      (pow_nonneg
        (mul_nonneg hCcell.le
          (cellChainRadiusFactor_pos R).le) _)
  have hraw :=
    hendpoint n hn G hG κ hκ hε hε1 z w
  have hquotient :=
    primitivePeriodicReductionFilteredSum_scalar_le_quotient
      (q := Q) hfarBase hnearBase hε hn κ hfull P
  exact hraw.trans (by
    simpa only [R, δ, farBase, nearBase, Q, P] using hquotient)

/-! ## Exact full-edge winding lift

The skipped-edge bridge above is useful as a topology ledger, but discarding
all cycle factors is too coarse for the final critical scaling.  The exact
formula retains every cycle edge: relative to the quotient-tree lift, its
right endpoint is translated by the nearest whole-period block. -/

/-- An ordinary lattice chain in which every right endpoint is moved by the
nearest period block relative to its left endpoint. -/
def latticeWindingWordChainWeight
    {m : ℕ} (q : ℤ) (u : Fin m → Z4) : ℝ :=
  ∏ j : AdjacentIndex m,
    latticeEdgeWeight (u j.1)
      (nearestPeriodTranslate q (u j.1) (u (adjacentSucc j)))

theorem latticeWindingWordChainWeight_nonneg
    {m : ℕ} (q : ℤ) (u : Fin m → Z4) :
    0 ≤ latticeWindingWordChainWeight q u := by
  unfold latticeWindingWordChainWeight
  apply Finset.prod_nonneg
  intro j hj
  exact latticeEdgeWeight_nonneg _ _

/-- A periodic edge is exactly the ordinary edge to the nearest
centre-preserving period translate. -/
theorem periodicCellEdgeWeight_eq_lattice_nearestPeriodTranslate
    {δ : ℝ} (hδ : 0 < δ) {q : ℤ}
    (hq : PeriodCompatibleMesh δ q) (x y : Z4) :
    periodicCellEdgeWeight δ x y =
      latticeEdgeWeight x (nearestPeriodTranslate q x y) := by
  let y' := nearestPeriodTranslate q x y
  have hcenter :
      latticeTorusCenter δ y' = latticeTorusCenter δ y :=
    latticeTorusCenter_nearestPeriodTranslate hq x y
  calc
    periodicCellEdgeWeight δ x y =
        periodicCellEdgeWeight δ x y' := by
      unfold periodicCellEdgeWeight
      rw [hcenter]
    _ = latticeEdgeWeight x y' := by
      apply periodicCellEdgeWeight_eq_latticeEdgeWeight_of_noWrap hδ
      exact latticeTorusCenter_dist_eq_of_edgeNoWrap hδ
        (nearestPeriodTranslate_edgeNoWrap hq x y)

/-- **Exact winding-chain identity.**  Unlike the skipped-edge inequality,
this keeps all `2n-1` inverse-square factors and therefore preserves the
critical R-51 power count. -/
theorem periodicCopiedWordChainWeight_eq_quotientWindingLift
    {δ : ℝ} (hδ : 0 < δ) {q : ℤ}
    (hq : PeriodCompatibleMesh δ q)
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) :
    periodicCopiedWordChainWeight δ κ hfull a =
      latticeWindingWordChainWeight q
        (quotientTreeLiftedWord hm κ hfull q a) := by
  unfold periodicCopiedWordChainWeight
    latticeWindingWordChainWeight
  apply Finset.prod_congr rfl
  intro j hj
  have hleft :=
    quotientTreeLiftedWord_center hq hm κ hfull a j.1
  have hright :=
    quotientTreeLiftedWord_center hq hm κ hfull a
      (adjacentSucc j)
  have hperiodic :
      periodicCellEdgeWeight δ
          (copiedPairingLabels κ hfull a j.1)
          (copiedPairingLabels κ hfull a (adjacentSucc j)) =
        periodicCellEdgeWeight δ
          (quotientTreeLiftedWord hm κ hfull q a j.1)
          (quotientTreeLiftedWord hm κ hfull q a
            (adjacentSucc j)) := by
    unfold periodicCellEdgeWeight
    rw [hleft, hright]
  rw [hperiodic]
  exact periodicCellEdgeWeight_eq_lattice_nearestPeriodTranslate
    hδ hq _ _

/-- Exact full statistic for copied pair labels, with the literal diameter
unchanged and every winding edge retained. -/
theorem primitivePeriodicCopiedWeight_copied_eq_quotientWindingLift
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (a : PairingVertex κ → Z4) :
    primitivePeriodicCopiedWeight ε n hn
        (copiedPairingLabels κ hfull a) =
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn
            (copiedPairingLabels κ hfull a)) *
        latticeWindingWordChainWeight (compatibleCellCount ε)
          (quotientTreeLiftedWord (by omega) κ hfull
            (compatibleCellCount ε) a) := by
  unfold primitivePeriodicCopiedWeight
  rw [← periodicCopiedWordChainWeight_eq_terminal hn κ hfull a]
  rw [periodicCopiedWordChainWeight_eq_quotientWindingLift
    (compatibleMeshSize_pos hε)
    (compatibleMesh_isPeriodCompatible hε)
    (by omega) κ hfull a]

/-- Carrier-facing exact winding identity. -/
theorem primitivePeriodicCopiedWeight_eq_quotientWindingLift
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalCellCarrier ε n κ) :
    primitivePeriodicCopiedWeight ε n hn y =
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) *
        latticeWindingWordChainWeight (compatibleCellCount ε)
          (quotientTreeLiftedWord (by omega) κ hfull
            (compatibleCellCount ε)
            (fun v : PairingVertex κ => y v.1)) := by
  let yp : {z : Fin (2 * n) → Z4 // RespectsPairing κ z} :=
    ⟨y, (Finset.mem_filter.mp hy).2⟩
  let a := restrictToPairingLowerHalf κ yp
  have hcopy :
      copiedPairingLabels κ hfull a = y := by
    have hright :=
      (copiedPairingLabelsEquiv κ hfull).apply_symm_apply yp
    exact congrArg Subtype.val hright
  have h :=
    primitivePeriodicCopiedWeight_copied_eq_quotientWindingLift
      hε hn κ hfull a
  rw [hcopy] at h
  change
    primitivePeriodicCopiedWeight ε n hn y =
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n hn y) *
        latticeWindingWordChainWeight (compatibleCellCount ε)
          (quotientTreeLiftedWord (by omega) κ hfull
            (compatibleCellCount ε)
            (fun v : PairingVertex κ => y v.1)) at h
  exact h

/-! ## Exact filtered winding sum -/

/-- Full-edge winding version of the canonical filtered sum.  In contrast
to `primitivePeriodicQuotientLiftRealSum`, this retains both the diameter
and every cycle factor. -/
def primitivePeriodicQuotientWindingRealSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] : ℝ :=
  ∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
      (fun y => P (primitiveCopiedReductionTuple n hn y)),
    primitiveTupleDiameterBracketSq (by omega)
        (primitiveCopiedReductionTuple n hn y) *
      latticeWindingWordChainWeight (compatibleCellCount ε)
        (quotientTreeLiftedWord (by omega) κ hfull
          (compatibleCellCount ε)
          (fun v : PairingVertex κ => y v.1))

theorem primitivePeriodicQuotientWindingRealSum_nonneg
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    0 ≤ primitivePeriodicQuotientWindingRealSum
      ε n hn κ hfull P := by
  unfold primitivePeriodicQuotientWindingRealSum
  apply Finset.sum_nonneg
  intro y hy
  exact mul_nonneg
    (primitiveTupleDiameterBracketSq_nonneg (by omega) _)
    (latticeWindingWordChainWeight_nonneg _ _)

/-- Lossless, arbitrary-filter periodic-to-winding reindexing. -/
theorem primitivePeriodicReductionFilteredRealSum_eq_quotientWinding
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    primitivePeriodicReductionFilteredRealSum ε n hn κ P =
      primitivePeriodicQuotientWindingRealSum
        ε n hn κ hfull P := by
  rw [primitivePeriodicReductionFilteredRealSum_eq_copied
    hε n hn κ P]
  unfold primitivePeriodicQuotientWindingRealSum
  apply Finset.sum_congr rfl
  intro y hy
  exact primitivePeriodicCopiedWeight_eq_quotientWindingLift
    hε hn κ hfull (Finset.mem_filter.mp hy).1

/-- Extended-real form of the exact winding reindexing. -/
theorem primitivePeriodicReductionFilteredSum_eq_quotientWinding
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    primitivePeriodicReductionFilteredSum ε n hn κ P =
      ENNReal.ofReal
        (primitivePeriodicQuotientWindingRealSum
          ε n hn κ hfull P) := by
  rw [primitivePeriodicReductionFilteredSum_eq_ofReal,
    primitivePeriodicReductionFilteredRealSum_eq_quotientWinding
      hε n hn κ hfull P]

/-- Scalar extraction with the correct, unshifted `δ^(4n-4)` power. -/
theorem primitivePeriodicReductionFilteredSum_scalar_eq_quotientWinding
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 2 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    (∑ u ∈
        ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
            ((2 * n - 1) + 1)).filter
          (RespectsPairing
            (primitiveReductionPairing n (by omega) κ))).filter P,
        ENNReal.ofReal q *
          (ENNReal.ofReal
              ((a * compatibleMeshSize ε ^ (4 * n - 4)) *
                primitivePeriodicReductionWeight
                  ε n (by omega) u) +
           ENNReal.ofReal
              ((b * compatibleMeshSize ε ^ (4 * n - 4)) *
                primitivePeriodicReductionWeight
                  ε n (by omega) u))) =
      ENNReal.ofReal q *
        (ENNReal.ofReal a + ENNReal.ofReal b) *
          ENNReal.ofReal
            (compatibleMeshSize ε ^ (4 * n - 4)) *
            ENNReal.ofReal
              (primitivePeriodicQuotientWindingRealSum
                ε n (by omega) κ hfull P) := by
  have hδpow :
      0 ≤ compatibleMeshSize ε ^ (4 * n - 4) :=
    pow_nonneg (compatibleMeshSize_pos hε).le _
  have hfactor :=
    primitivePeriodicReductionFilteredSum_factor
      (a := a * compatibleMeshSize ε ^ (4 * n - 4))
      (b := b * compatibleMeshSize ε ^ (4 * n - 4))
      (q := q)
      (mul_nonneg ha hδpow) (mul_nonneg hb hδpow)
      ε n (by omega) κ P
  rw [hfactor]
  rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  rw [primitivePeriodicReductionFilteredSum_eq_quotientWinding
    hε n (by omega) κ hfull P]
  ring

/-- Correct-scale endpoint R-51 reduction retaining all winding data. -/
theorem primitiveInsertedIntegrand_lintegral_le_periodicWindingSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n)))
          (hκ : κ ∈ primitiveFullPairings n),
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farBase :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R
          let nearBase :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3)
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
              (ENNReal.ofReal farBase + ENNReal.ofReal nearBase) *
                ENNReal.ofReal (δ ^ (4 * n - 4)) *
                  ENNReal.ofReal
                    (primitivePeriodicQuotientWindingRealSum
                      ε n (by omega) κ
                        (mem_primitiveFullPairings.mp hκ).1
                      (primitiveCopiedEndpointSupported
                        ρ ε n (by omega) z w)) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hendpoint⟩ :=
    primitiveInsertedIntegrand_lintegral_le_periodicEndpointSum ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let farBase :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R
  let nearBase :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3)
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let P :=
    primitiveCopiedEndpointSupported
      ρ ε n (by omega) z w
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hfarBase : 0 ≤ farBase := by
    dsimp only [farBase]
    exact mul_nonneg
      (mul_nonneg
        (by positivity)
        (pow_nonneg
          (mul_nonneg hCcell.le
            (add_nonneg (sq_nonneg R) (pow_nonneg hR.le 4))) _))
      (terminalRadiusFactor_pos hR).le
  have hnearBase : 0 ≤ nearBase := by
    dsimp only [nearBase]
    exact mul_nonneg (by positivity)
      (pow_nonneg
        (mul_nonneg hCcell.le
          (cellChainRadiusFactor_pos R).le) _)
  have hraw :=
    hendpoint n hn G hG κ hκ hε hε1 z w
  have hwind :=
    primitivePeriodicReductionFilteredSum_scalar_eq_quotientWinding
      (q := Q) hfarBase hnearBase hε hn κ hfull P
  exact hraw.trans_eq (by
    simpa only [R, δ, farBase, nearBase, Q, P] using hwind)

def r51CutRepresentative
    (q : ℕ) (c : Fin q) (x : ZMod q) : ℤ :=
  if x.val < c.val then (x.val : ℤ) + q else x.val

theorem r51CutRepresentative_ordered_sub
    {q : ℕ} [NeZero q] (c : Fin q) (x y : ZMod q)
    (hxy : x.val ≤ y.val) :
    |r51CutRepresentative q c x -
        r51CutRepresentative q c y| =
      if x.val < c.val ∧ c.val ≤ y.val then
        (q : ℤ) - ((y.val : ℤ) - (x.val : ℤ))
      else
        (y.val : ℤ) - (x.val : ℤ) := by
  unfold r51CutRepresentative
  by_cases hxc : x.val < c.val
  · by_cases hyc : y.val < c.val
    · have hnotcy : ¬ c.val ≤ y.val := Nat.not_le_of_gt hyc
      simp only [hxc, hyc, hnotcy, and_false, ↓reduceIte]
      rw [abs_of_nonpos]
      · ring
      · omega
    · have hcy : c.val ≤ y.val := Nat.le_of_not_gt hyc
      simp only [hxc, hyc, hcy, and_self, ↓reduceIte]
      rw [abs_of_nonneg]
      · ring
      · have hxq : x.val < q := x.val_lt
        have hyq : y.val < q := y.val_lt
        omega
  · have hyc : ¬ y.val < c.val := by omega
    simp only [hxc, hyc, false_and, ↓reduceIte]
    rw [abs_of_nonpos]
    · ring
    · omega

theorem r51_card_ordered_separatingCuts
    {q : ℕ} [NeZero q] (x y : ZMod q) (_hxy : x.val ≤ y.val) :
    ((Finset.univ : Finset (Fin q)).filter
        (fun c => x.val < c.val ∧ c.val ≤ y.val)).card =
      y.val - x.val := by
  have heq :
      ((Finset.univ : Finset (Fin q)).filter
          (fun c => x.val < c.val ∧ c.val ≤ y.val)) =
        Finset.Ioc ⟨x.val, x.val_lt⟩ ⟨y.val, y.val_lt⟩ := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ioc]
    rfl
  rw [heq, Fin.card_Ioc]

def r51ResidueGap {q : ℕ} (x y : ZMod q) : ℕ :=
  Nat.dist x.val y.val

def r51CyclicGap (q : ℕ) (x y : ZMod q) : ℕ :=
  min (r51ResidueGap x y) (q - r51ResidueGap x y)

def r51CutSeparates
    {q : ℕ} (c : Fin q) (x y : ZMod q) : Prop :=
  (x.val < c.val ∧ c.val ≤ y.val) ∨
    (y.val < c.val ∧ c.val ≤ x.val)

instance {q : ℕ} (c : Fin q) (x y : ZMod q) :
    Decidable (r51CutSeparates c x y) :=
  Classical.propDecidable _

theorem r51CutRepresentative_sub_abs
    {q : ℕ} [NeZero q] (c : Fin q) (x y : ZMod q) :
    |r51CutRepresentative q c x -
        r51CutRepresentative q c y| =
      if r51CutSeparates c x y then
        (q : ℤ) - r51ResidueGap x y
      else
        (r51ResidueGap x y : ℤ) := by
  rcases le_total x.val y.val with hxy | hyx
  · rw [r51CutRepresentative_ordered_sub c x y hxy]
    have hnotrev :
        ¬(y.val < c.val ∧ c.val ≤ x.val) := by
      omega
    simp only [r51CutSeparates, hnotrev, or_false]
    rw [show r51ResidueGap x y = y.val - x.val by
      exact Nat.dist_eq_sub_of_le hxy]
    rw [Nat.cast_sub hxy]
  · rw [abs_sub_comm,
      r51CutRepresentative_ordered_sub c y x hyx]
    have hnotfwd :
        ¬(x.val < c.val ∧ c.val ≤ y.val) := by
      omega
    simp only [r51CutSeparates, hnotfwd, false_or]
    rw [show r51ResidueGap x y = x.val - y.val by
      exact Nat.dist_eq_sub_of_le_right hyx]
    rw [Nat.cast_sub hyx]

theorem r51_card_separatingCuts
    {q : ℕ} [NeZero q] (x y : ZMod q) :
    ((Finset.univ : Finset (Fin q)).filter
        (fun c => r51CutSeparates c x y)).card =
      r51ResidueGap x y := by
  rcases le_total x.val y.val with hxy | hyx
  · have hnotrev :
        ∀ c : Fin q, ¬(y.val < c.val ∧ c.val ≤ x.val) := by
      intro c
      omega
    simp only [r51CutSeparates, hnotrev, or_false]
    rw [r51_card_ordered_separatingCuts x y hxy]
    exact (Nat.dist_eq_sub_of_le hxy).symm
  · have hnotfwd :
        ∀ c : Fin q, ¬(x.val < c.val ∧ c.val ≤ y.val) := by
      intro c
      omega
    simp only [r51CutSeparates, hnotfwd, false_or]
    rw [r51_card_ordered_separatingCuts y x hyx]
    exact (Nat.dist_eq_sub_of_le_right hyx).symm

def r51CutIsLong
    {q : ℕ} (c : Fin q) (x y : ZMod q) : Prop :=
  if r51ResidueGap x y ≤ q - r51ResidueGap x y then
    r51CutSeparates c x y
  else
    ¬r51CutSeparates c x y

instance {q : ℕ} (c : Fin q) (x y : ZMod q) :
    Decidable (r51CutIsLong c x y) :=
  Classical.propDecidable _

theorem r51_card_longCuts
    {q : ℕ} [NeZero q] (x y : ZMod q) :
    ((Finset.univ : Finset (Fin q)).filter
        (fun c => r51CutIsLong c x y)).card =
      r51CyclicGap q x y := by
  let d := r51ResidueGap x y
  by_cases h : d ≤ q - d
  · simp only [r51CutIsLong, d, h, ↓reduceIte,
      r51CyclicGap, min_eq_left h]
    exact r51_card_separatingCuts x y
  · have hrev : q - d ≤ d := by omega
    have hcard :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin q)))
        (p := fun c => r51CutSeparates c x y)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    rw [r51_card_separatingCuts x y] at hcard
    simp only [r51CutIsLong, d, h, ↓reduceIte,
      r51CyclicGap, min_eq_right hrev]
    omega

theorem r51ResidueGap_lt
    {q : ℕ} [NeZero q] (x y : ZMod q) :
    r51ResidueGap x y < q := by
  unfold r51ResidueGap
  rcases le_total x.val y.val with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy]
    have hyq : y.val < q := y.val_lt
    omega
  · rw [Nat.dist_eq_sub_of_le_right hyx]
    have hxq : x.val < q := x.val_lt
    omega

theorem r51CyclicGap_mul_two_le
    {q : ℕ} [NeZero q] (x y : ZMod q) :
    2 * r51CyclicGap q x y ≤ q := by
  let d := r51ResidueGap x y
  have hdq : d ≤ q := (r51ResidueGap_lt x y).le
  unfold r51CyclicGap
  omega

theorem r51CyclicGap_eq_natAbs_valMinAbs
    {q : ℕ} [NeZero q] (x y : ZMod q) :
    r51CyclicGap q x y =
      ((x - y).valMinAbs).natAbs := by
  rw [ZMod.valMinAbs_natAbs_eq_min]
  rcases le_total y.val x.val with hyx | hxy
  · rw [ZMod.val_sub hyx]
    simp only [r51CyclicGap, r51ResidueGap,
      Nat.dist_eq_sub_of_le_right hyx]
  · by_cases heq : x = y
    · subst y
      simp [r51CyclicGap, r51ResidueGap]
    · have hxy' : x.val < y.val := by
        exact lt_of_le_of_ne hxy
          (fun h => heq (ZMod.val_injective q h))
      have hsubne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
      have hvalyx : (y - x).val = y.val - x.val :=
        ZMod.val_sub hxy
      have hval :
          (x - y).val = q - (y.val - x.val) := by
        rw [show x - y = -(y - x) by abel,
          ZMod.neg_val, if_neg hsubne, hvalyx]
      rw [hval]
      simp only [r51CyclicGap, r51ResidueGap,
        Nat.dist_eq_sub_of_le hxy]
      have hyq : y.val < q := y.val_lt
      omega

theorem r51CutRepresentative_sub_abs_eq
    {q : ℕ} [NeZero q] (c : Fin q) (x y : ZMod q) :
    |r51CutRepresentative q c x -
        r51CutRepresentative q c y| =
      if r51CutIsLong c x y then
        (q - r51CyclicGap q x y : ℕ)
      else
        r51CyclicGap q x y := by
  let d := r51ResidueGap x y
  have hdq : d ≤ q := (r51ResidueGap_lt x y).le
  rw [r51CutRepresentative_sub_abs]
  by_cases hhalf : d ≤ q - d
  · have hr : r51CyclicGap q x y = d := by
      exact min_eq_left hhalf
    simp only [r51CutIsLong, d, hhalf, ↓reduceIte, hr]
    by_cases hsep : r51CutSeparates c x y
    · simp only [hsep, ↓reduceIte]
      norm_cast
    · simp only [hsep, ↓reduceIte]
  · have hrev : q - d ≤ d := by omega
    have hr : r51CyclicGap q x y = q - d := by
      exact min_eq_right hrev
    simp only [r51CutIsLong, d, hhalf, ↓reduceIte, hr]
    by_cases hsep : r51CutSeparates c x y
    · simp only [hsep, not_true_eq_false, ↓reduceIte]
      norm_cast
    · simp only [hsep, not_false_eq_true, ↓reduceIte]
      norm_cast
      omega

theorem r51_log_long_ratio_average_le
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hrq : r ≤ q) :
    ((r : ℝ) / q) *
        Real.log
          ((1 + ((q - r : ℕ) : ℝ) ^ 2) /
            (1 + (r : ℝ) ^ 2)) ≤
      2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
  have hnum :
      1 + (((q - r : ℕ) : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 := by
    rw [Nat.cast_sub hrq]
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [sq_nonneg ((q : ℝ) - r),
      sq_nonneg ((q : ℝ) - r - 1)]
  have hden : 0 < 1 + (r : ℝ) ^ 2 := by positivity
  have hratio_pos :
      0 <
        (1 + (((q - r : ℕ) : ℝ)) ^ 2) /
          (1 + (r : ℝ) ^ 2) := by positivity
  have hqr_pos : 0 < (q : ℝ) / r := div_pos hqR hrR
  have hratio :
      (1 + (((q - r : ℕ) : ℝ)) ^ 2) /
          (1 + (r : ℝ) ^ 2) ≤
        ((q : ℝ) / r) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hrR)).2
    have hrSq : 0 ≤ (r : ℝ) ^ 2 := sq_nonneg _
    calc
      (1 + (((q - r : ℕ) : ℝ)) ^ 2) * (r : ℝ) ^ 2 ≤
          (q : ℝ) ^ 2 * (r : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hnum hrSq
      _ ≤ (q : ℝ) ^ 2 * (1 + (r : ℝ) ^ 2) := by
        gcongr
        nlinarith
  have hlogratio :
      Real.log
          ((1 + (((q - r : ℕ) : ℝ)) ^ 2) /
            (1 + (r : ℝ) ^ 2)) ≤
        Real.log (((q : ℝ) / r) ^ 2) :=
    Real.strictMonoOn_log.monotoneOn hratio_pos
      (pow_pos hqr_pos 2) hratio
  have hlogqr :
      Real.log ((q : ℝ) / r) ≤ (q : ℝ) / r := by
    have h := Real.log_le_sub_one_of_pos hqr_pos
    linarith
  rw [Real.log_pow] at hlogratio
  have hmul_nonneg : 0 ≤ (r : ℝ) / q :=
    (div_pos hrR hqR).le
  calc
    ((r : ℝ) / q) *
        Real.log
          ((1 + (((q - r : ℕ) : ℝ)) ^ 2) /
            (1 + (r : ℝ) ^ 2)) ≤
      ((r : ℝ) / q) *
        (2 * Real.log ((q : ℝ) / r)) :=
      mul_le_mul_of_nonneg_left hlogratio hmul_nonneg
    _ ≤ ((r : ℝ) / q) * (2 * ((q : ℝ) / r)) := by
      gcongr
    _ = 2 := by field_simp

def r51CyclicBracket
    (q : ℕ) (x y : ZMod q) : ℝ :=
  1 + (r51CyclicGap q x y : ℝ) ^ 2

def r51CutBracket
    {q : ℕ} (c : Fin q) (x y : ZMod q) : ℝ :=
  1 +
    ((|r51CutRepresentative q c x -
        r51CutRepresentative q c y| : ℤ) : ℝ) ^ 2

def r51LongBracket
    (q : ℕ) (x y : ZMod q) : ℝ :=
  1 + (q - r51CyclicGap q x y : ℕ) ^ 2

theorem r51CyclicBracket_pos
    {q : ℕ} (x y : ZMod q) :
    0 < r51CyclicBracket q x y := by
  unfold r51CyclicBracket
  positivity

theorem r51CutBracket_pos
    {q : ℕ} (c : Fin q) (x y : ZMod q) :
    0 < r51CutBracket c x y := by
  unfold r51CutBracket
  positivity

theorem r51LongBracket_pos
    {q : ℕ} (x y : ZMod q) :
    0 < r51LongBracket q x y := by
  unfold r51LongBracket
  positivity

theorem r51CutBracket_eq
    {q : ℕ} [NeZero q] (c : Fin q) (x y : ZMod q) :
    r51CutBracket c x y =
      if r51CutIsLong c x y then
        r51LongBracket q x y
      else
        r51CyclicBracket q x y := by
  unfold r51CutBracket r51LongBracket r51CyclicBracket
  rw [r51CutRepresentative_sub_abs_eq]
  split_ifs <;> norm_cast

theorem r51_log_cutBracket_div_cyclic
    {q : ℕ} [NeZero q] (c : Fin q) (x y : ZMod q) :
    Real.log (r51CutBracket c x y /
        r51CyclicBracket q x y) =
      if r51CutIsLong c x y then
        Real.log (r51LongBracket q x y /
          r51CyclicBracket q x y)
      else
        0 := by
  rw [r51CutBracket_eq]
  split_ifs
  · rfl
  · rw [div_self (ne_of_gt (r51CyclicBracket_pos x y)),
      Real.log_one]

theorem r51_sum_log_cutBracket_div_cyclic
    {q : ℕ} [NeZero q] (x y : ZMod q) :
    (∑ c : Fin q,
        Real.log (r51CutBracket c x y /
          r51CyclicBracket q x y)) =
      (r51CyclicGap q x y : ℝ) *
        Real.log (r51LongBracket q x y /
          r51CyclicBracket q x y) := by
  simp_rw [r51_log_cutBracket_div_cyclic]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  rw [r51_card_longCuts]

theorem r51_sum_log_cutBracket_div_cyclic_le
    {q : ℕ} [NeZero q] (x y : ZMod q) :
    (∑ c : Fin q,
        Real.log (r51CutBracket c x y /
          r51CyclicBracket q x y)) ≤
      2 * q := by
  rw [r51_sum_log_cutBracket_div_cyclic]
  let r := r51CyclicGap q x y
  have hq : 0 < q := NeZero.pos q
  by_cases hr0 : r = 0
  · simp [r, hr0]
  · have hr : 0 < r := Nat.pos_of_ne_zero hr0
    have hrq : r ≤ q := by
      have htwo := r51CyclicGap_mul_two_le x y
      omega
    have havg :=
      r51_log_long_ratio_average_le hq hr hrq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have heq :
        r51LongBracket q x y =
          1 + ((q - r : ℕ) : ℝ) ^ 2 := by rfl
    have heq' :
        r51CyclicBracket q x y =
          1 + (r : ℝ) ^ 2 := by rfl
    rw [heq, heq'] at *
    calc
      (r : ℝ) *
          Real.log
            ((1 + ((q - r : ℕ) : ℝ) ^ 2) /
              (1 + (r : ℝ) ^ 2)) =
          (q : ℝ) *
            (((r : ℝ) / q) *
              Real.log
                ((1 + ((q - r : ℕ) : ℝ) ^ 2) /
                  (1 + (r : ℝ) ^ 2))) := by
        field_simp
      _ ≤ (q : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left havg hqR.le
      _ = 2 * q := by ring

/-! Four-dimensional cut lifts and canonical shortest lifts. -/

abbrev R51Cut (q : ℕ) := Fin 4 → Fin q

def r51CutLift
    (q : ℕ) (c : R51Cut q) (a : Z4) : Z4 :=
  fun i => r51CutRepresentative q (c i) (a i)

def r51MinimalDifference
    (q : ℕ) (a b : Z4) : Z4 :=
  fun i => ((a i - b i : ℤ) : ZMod q).valMinAbs

def r51MinimalTranslate
    (q : ℕ) (a b : Z4) : Z4 :=
  a - r51MinimalDifference q a b

@[simp]
theorem r51_sub_minimalTranslate
    (q : ℕ) (a b : Z4) :
    a - r51MinimalTranslate q a b =
      r51MinimalDifference q a b := by
  unfold r51MinimalTranslate
  abel

theorem r51MinimalTranslate_periodCongruent
    {q : ℕ} [NeZero q] (a b : Z4) :
    PeriodCongruent (q : ℤ)
      (r51MinimalTranslate q a b) b := by
  have hex :
      ∀ i : Fin 4, ∃ k : ℤ,
        (a i - b i) -
            r51MinimalDifference q a b i =
          (q : ℤ) * k := by
    intro i
    have hcast :
        ((r51MinimalDifference q a b i : ℤ) : ZMod q) =
          ((a i - b i : ℤ) : ZMod q) := by
      simp [r51MinimalDifference]
    have hdvd :
        (q : ℤ) ∣
          (a i - b i) -
            r51MinimalDifference q a b i := by
      exact
        (ZMod.intCast_eq_intCast_iff_dvd_sub
          (r51MinimalDifference q a b i)
          (a i - b i) q).mp hcast
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by simpa only [mul_comm] using hk⟩
  choose k hk using hex
  refine ⟨k, ?_⟩
  funext i
  unfold r51MinimalTranslate translateCellIndex
  simp only [Pi.sub_apply]
  have hi := hk i
  linarith

theorem r51CutLift_periodCongruent
    {q : ℕ} [NeZero q] (c : R51Cut q) (a : Z4) :
    PeriodCongruent (q : ℤ) (r51CutLift q c a) a := by
  have hex :
      ∀ i : Fin 4, ∃ k : ℤ,
        r51CutLift q c a i - a i = (q : ℤ) * k := by
    intro i
    have hcast :
        ((r51CutLift q c a i : ℤ) : ZMod q) =
          ((a i : ℤ) : ZMod q) := by
      unfold r51CutLift r51CutRepresentative
      split_ifs
      · simp
      · simp
    have hdvd :
        (q : ℤ) ∣ r51CutLift q c a i - a i := by
      have :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub
          (a := a i) (b := r51CutLift q c a i) q).mp
          hcast.symm
      simpa only [sub_eq_add_neg, add_comm] using this
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by simpa only [mul_comm] using hk⟩
  choose k hk using hex
  refine ⟨k, ?_⟩
  funext i
  unfold translateCellIndex
  have hi := hk i
  linarith

theorem latticeTorusCenter_r51CutLift
    {δ : ℝ} {q : ℕ} [NeZero q]
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (c : R51Cut q) (a : Z4) :
    latticeTorusCenter δ (r51CutLift q c a) =
      latticeTorusCenter δ a := by
  obtain ⟨k, hk⟩ := r51CutLift_periodCongruent c a
  rw [hk]
  exact latticeTorusCenter_translateCellIndex hq k a

theorem latticeTorusCenter_r51MinimalTranslate
    {δ : ℝ} {q : ℕ} [NeZero q]
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (a b : Z4) :
    latticeTorusCenter δ (r51MinimalTranslate q a b) =
      latticeTorusCenter δ b := by
  obtain ⟨k, hk⟩ :=
    r51MinimalTranslate_periodCongruent (q := q) a b
  rw [hk]
  exact latticeTorusCenter_translateCellIndex hq k b

theorem r51MinimalTranslate_edgeNoWrap
    {δ : ℝ} {q : ℕ} [NeZero q]
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (a b : Z4) :
    LatticeEdgeNoWrap δ a
      (r51MinimalTranslate q a b) := by
  have hqR : (0 : ℝ) < q := by
    exact_mod_cast NeZero.pos q
  have hperiod : δ * (q : ℝ) = 2 * Real.pi := by
    simpa using hq.period_eq
  have hδ : 0 < δ := by
    by_contra hnot
    have hδnonpos : δ ≤ 0 := le_of_not_gt hnot
    have := mul_nonpos_of_nonpos_of_nonneg hδnonpos hqR.le
    rw [hperiod] at this
    nlinarith [Real.pi_pos]
  intro i
  rw [r51_sub_minimalTranslate]
  simp only [r51MinimalDifference]
  have hnat :=
    ZMod.natAbs_valMinAbs_le
      (((a i - b i : ℤ) : ZMod q))
  have htwoNat :
      2 *
          (((((a i - b i : ℤ) : ZMod q)).valMinAbs).natAbs) ≤
        q := by
    omega
  have htwo :
      2 *
          ((((((a i - b i : ℤ) : ZMod q)).valMinAbs).natAbs : ℕ) : ℝ) ≤
        (q : ℝ) := by
    exact_mod_cast htwoNat
  rw [abs_mul, abs_of_pos hδ, ← Int.cast_abs,
    Int.abs_eq_natAbs]
  have hmul :
      δ *
          ((((((a i - b i : ℤ) : ZMod q)).valMinAbs).natAbs : ℕ) : ℝ) ≤
        δ * (q : ℝ) / 2 := by
    nlinarith
  change
    δ *
        (((((a i - b i : ℤ) : ZMod q)).valMinAbs).natAbs : ℝ) ≤
      Real.pi
  calc
    _ ≤ δ * (q : ℝ) / 2 := hmul
    _ = Real.pi := by rw [hperiod]; ring

theorem periodicCellEdgeWeight_eq_r51Minimal
    {δ : ℝ} (hδ : 0 < δ) {q : ℕ} [NeZero q]
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (a b : Z4) :
    periodicCellEdgeWeight δ a b =
      latticeEdgeWeight a (r51MinimalTranslate q a b) := by
  have hcenter :=
    latticeTorusCenter_r51MinimalTranslate hq a b
  have hdist :=
    latticeTorusCenter_dist_eq_of_edgeNoWrap hδ
      (r51MinimalTranslate_edgeNoWrap hq a b)
  unfold periodicCellEdgeWeight
  rw [← hcenter, hdist]
  unfold latticeEdgeWeight
  rw [r51_sub_minimalTranslate]
  field_simp [ne_of_gt hδ]

theorem r51MinimalDifference_coord_abs
    {q : ℕ} [NeZero q] (a b : Z4) (i : Fin 4) :
    |r51MinimalDifference q a b i| =
      (r51CyclicGap q
        ((a i : ℤ) : ZMod q)
        ((b i : ℤ) : ZMod q) : ℕ) := by
  unfold r51MinimalDifference
  rw [Int.abs_eq_natAbs]
  norm_cast
  symm
  simpa only [Int.cast_sub] using
    r51CyclicGap_eq_natAbs_valMinAbs
      (((a i : ℤ) : ZMod q))
      (((b i : ℤ) : ZMod q))

theorem r51CutLift_sub_coord_abs
    {q : ℕ} [NeZero q] (c : R51Cut q)
    (a b : Z4) (i : Fin 4) :
    |(r51CutLift q c a - r51CutLift q c b) i| =
      if r51CutIsLong (c i)
          (((a i : ℤ) : ZMod q))
          (((b i : ℤ) : ZMod q)) then
        (q - r51CyclicGap q
          (((a i : ℤ) : ZMod q))
          (((b i : ℤ) : ZMod q)) : ℕ)
      else
        r51CyclicGap q
          (((a i : ℤ) : ZMod q))
          (((b i : ℤ) : ZMod q)) := by
  simp only [Pi.sub_apply, r51CutLift]
  exact r51CutRepresentative_sub_abs_eq
    (c i) ((a i : ℤ) : ZMod q) ((b i : ℤ) : ZMod q)

def r51CoordinateEdgeRatio
    {q : ℕ} (c : R51Cut q) (a b : Z4)
    (i : Fin 4) : ℝ :=
  r51CutBracket (c i)
      (((a i : ℤ) : ZMod q))
      (((b i : ℤ) : ZMod q)) /
    r51CyclicBracket q
      (((a i : ℤ) : ZMod q))
      (((b i : ℤ) : ZMod q))

theorem r51CoordinateEdgeRatio_pos
    {q : ℕ} (c : R51Cut q) (a b : Z4) (i : Fin 4) :
    0 < r51CoordinateEdgeRatio c a b i := by
  unfold r51CoordinateEdgeRatio
  exact div_pos (r51CutBracket_pos _ _ _)
    (r51CyclicBracket_pos _ _)

theorem r51CoordinateEdgeRatio_one_le
    {q : ℕ} [NeZero q] (c : R51Cut q)
    (a b : Z4) (i : Fin 4) :
    1 ≤ r51CoordinateEdgeRatio c a b i := by
  unfold r51CoordinateEdgeRatio
  apply (le_div_iff₀
    (r51CyclicBracket_pos
      (((a i : ℤ) : ZMod q))
      (((b i : ℤ) : ZMod q)))).2
  rw [one_mul, r51CutBracket_eq]
  split_ifs
  · unfold r51LongBracket r51CyclicBracket
    have htwo :=
      r51CyclicGap_mul_two_le
        (((a i : ℤ) : ZMod q))
        (((b i : ℤ) : ZMod q))
    have hle :
        r51CyclicGap q
            (((a i : ℤ) : ZMod q))
            (((b i : ℤ) : ZMod q)) ≤
          q - r51CyclicGap q
            (((a i : ℤ) : ZMod q))
            (((b i : ℤ) : ZMod q)) := by
      omega
    gcongr
  · exact le_rfl

theorem r51CyclicBracket_eq_minimal_coord
    {q : ℕ} [NeZero q] (a b : Z4) (i : Fin 4) :
    r51CyclicBracket q
        (((a i : ℤ) : ZMod q))
        (((b i : ℤ) : ZMod q)) =
      1 + ((r51MinimalDifference q a b i : ℤ) : ℝ) ^ 2 := by
  unfold r51CyclicBracket
  have habs :=
    r51MinimalDifference_coord_abs (q := q) a b i
  have habsR :
      |((r51MinimalDifference q a b i : ℤ) : ℝ)| =
        (r51CyclicGap q
          (((a i : ℤ) : ZMod q))
          (((b i : ℤ) : ZMod q)) : ℝ) := by
    exact_mod_cast habs
  nlinarith [sq_abs
    ((r51MinimalDifference q a b i : ℤ) : ℝ)]

theorem r51CutBracket_eq_cutLift_coord
    {q : ℕ} (c : R51Cut q) (a b : Z4) (i : Fin 4) :
    r51CutBracket (c i)
        (((a i : ℤ) : ZMod q))
        (((b i : ℤ) : ZMod q)) =
      1 +
        (((r51CutLift q c a - r51CutLift q c b) i : ℤ) : ℝ) ^ 2 := by
  unfold r51CutBracket
  change
    1 +
        ((|r51CutRepresentative q (c i)
            (((a i : ℤ) : ZMod q)) -
          r51CutRepresentative q (c i)
            (((b i : ℤ) : ZMod q))| : ℤ) : ℝ) ^ 2 =
      1 +
        ((r51CutRepresentative q (c i)
              (((a i : ℤ) : ZMod q)) -
            r51CutRepresentative q (c i)
              (((b i : ℤ) : ZMod q)) : ℤ) : ℝ) ^ 2
  rw [← sq_abs
    ((r51CutRepresentative q (c i)
          (((a i : ℤ) : ZMod q)) -
        r51CutRepresentative q (c i)
          (((b i : ℤ) : ZMod q)) : ℤ) : ℝ)]
  norm_cast

theorem r51CyclicBracket_le_minimalBracket
    {q : ℕ} [NeZero q] (a b : Z4) (i : Fin 4) :
    r51CyclicBracket q
        (((a i : ℤ) : ZMod q))
        (((b i : ℤ) : ZMod q)) ≤
      latticeBracketSq a (r51MinimalTranslate q a b) := by
  rw [r51CyclicBracket_eq_minimal_coord]
  unfold latticeBracketSq
  rw [r51_sub_minimalTranslate]
  have hcoord :=
    znorm_coord_le (r51MinimalDifference q a b) i
  have hsq :=
    pow_le_pow_left₀
      (abs_nonneg
        ((r51MinimalDifference q a b i : ℤ) : ℝ))
      hcoord 2
  simpa only [sq_abs, add_comm] using add_le_add_left hsq 1

theorem r51_latticeBracketSq_cutLift_le
    {q : ℕ} [NeZero q] (c : R51Cut q)
    (a b : Z4) :
    latticeBracketSq (r51CutLift q c a)
        (r51CutLift q c b) ≤
      4 * latticeBracketSq a
          (r51MinimalTranslate q a b) *
        ∏ i : Fin 4, r51CoordinateEdgeRatio c a b i := by
  let B := latticeBracketSq a (r51MinimalTranslate q a b)
  let P := ∏ i : Fin 4, r51CoordinateEdgeRatio c a b i
  have hB0 : 0 ≤ B := latticeBracketSq_nonneg _ _
  have hP0 : 0 ≤ P := by
    exact Finset.prod_nonneg fun i _ =>
      (r51CoordinateEdgeRatio_pos c a b i).le
  have hratio_le :
      ∀ i : Fin 4, r51CoordinateEdgeRatio c a b i ≤ P := by
    intro i
    classical
    have hone :
        1 ≤ ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          r51CoordinateEdgeRatio c a b j := by
      apply Finset.one_le_prod
      intro j hj
      exact r51CoordinateEdgeRatio_one_le c a b j
    calc
      r51CoordinateEdgeRatio c a b i =
          1 * r51CoordinateEdgeRatio c a b i := by ring
      _ ≤ (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
            r51CoordinateEdgeRatio c a b j) *
          r51CoordinateEdgeRatio c a b i :=
        mul_le_mul_of_nonneg_right hone
          (r51CoordinateEdgeRatio_pos c a b i).le
      _ = P := by
        dsimp only [P]
        exact Finset.prod_erase_mul
          (Finset.univ : Finset (Fin 4))
          (fun j => r51CoordinateEdgeRatio c a b j)
          (Finset.mem_univ i)
  have hcoord :
      ∀ i : Fin 4,
        1 +
            (((r51CutLift q c a -
                r51CutLift q c b) i : ℤ) : ℝ) ^ 2 ≤
          B * P := by
    intro i
    let Bi :=
      r51CyclicBracket q
        (((a i : ℤ) : ZMod q))
        (((b i : ℤ) : ZMod q))
    let Ci :=
      r51CutBracket (c i)
        (((a i : ℤ) : ZMod q))
        (((b i : ℤ) : ZMod q))
    let Ri := r51CoordinateEdgeRatio c a b i
    have hBi : Bi ≤ B :=
      r51CyclicBracket_le_minimalBracket a b i
    have hBi0 : 0 < Bi :=
      r51CyclicBracket_pos _ _
    have hCi0 : 0 ≤ Ci := (r51CutBracket_pos _ _ _).le
    have hRi : Ri ≤ P := hratio_le i
    have hRi0 : 0 ≤ Ri :=
      (r51CoordinateEdgeRatio_pos c a b i).le
    have heq : Ci = Bi * Ri := by
      change Ci = Bi * (Ci / Bi)
      symm
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ Ci (ne_of_gt hBi0)
    rw [← r51CutBracket_eq_cutLift_coord c a b i]
    change Ci ≤ B * P
    rw [heq]
    exact mul_le_mul hBi hRi hRi0 hB0
  let d := r51CutLift q c a - r51CutLift q c b
  change 1 + znorm d ^ 2 ≤ 4 * B * P
  have hsq := znorm_sq_le_zEuclideanNormSq d
  have hsum :
      1 + zEuclideanNormSq d ≤ ∑ _i : Fin 4, B * P := by
    unfold zEuclideanNormSq
    have hone : (1 : ℝ) ≤ ∑ _i : Fin 4, 1 := by norm_num
    calc
      1 + ∑ i : Fin 4, (d i : ℝ) ^ 2 ≤
          ∑ i : Fin 4, 1 +
            ∑ i : Fin 4, (d i : ℝ) ^ 2 := by gcongr
      _ = ∑ i : Fin 4, (1 + (d i : ℝ) ^ 2) := by
        rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i : Fin 4, B * P := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [d] using hcoord i
  calc
    1 + znorm d ^ 2 ≤ 1 + zEuclideanNormSq d := by gcongr
    _ ≤ ∑ _i : Fin 4, B * P := hsum
    _ = 4 * B * P := by simp; ring

theorem r51_vector_log_distortion_le
    {q : ℕ} [NeZero q] (c : R51Cut q)
    (a b : Z4) :
    Real.log
        (latticeBracketSq (r51CutLift q c a)
            (r51CutLift q c b) /
          latticeBracketSq a
            (r51MinimalTranslate q a b)) ≤
      4 +
        ∑ i : Fin 4,
          Real.log (r51CoordinateEdgeRatio c a b i) := by
  let B := latticeBracketSq a (r51MinimalTranslate q a b)
  let C :=
    latticeBracketSq (r51CutLift q c a)
      (r51CutLift q c b)
  let P := ∏ i : Fin 4, r51CoordinateEdgeRatio c a b i
  have hB : 0 < B :=
    lt_of_lt_of_le zero_lt_one
      (one_le_latticeBracketSq _ _)
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one
      (one_le_latticeBracketSq _ _)
  have hP : 0 < P := by
    exact Finset.prod_pos fun i _ =>
      r51CoordinateEdgeRatio_pos c a b i
  have hratio :
      C / B ≤ 4 * P := by
    apply (div_le_iff₀ hB).2
    have hraw := r51_latticeBracketSq_cutLift_le c a b
    dsimp only [B, C, P] at *
    nlinarith
  have hlog :
      Real.log (C / B) ≤ Real.log (4 * P) :=
    Real.strictMonoOn_log.monotoneOn
      (div_pos hC hB) (mul_pos (by norm_num) hP) hratio
  have hlog4 : Real.log (4 : ℝ) ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 4)
    linarith
  calc
    Real.log (C / B) ≤ Real.log (4 * P) := hlog
    _ = Real.log 4 + Real.log P := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hP)]
    _ = Real.log 4 +
        ∑ i : Fin 4,
          Real.log (r51CoordinateEdgeRatio c a b i) := by
      congr 1
      dsimp only [P]
      rw [Real.log_prod]
      intro i hi
      exact ne_of_gt (r51CoordinateEdgeRatio_pos c a b i)
    _ ≤ 4 +
        ∑ i : Fin 4,
          Real.log (r51CoordinateEdgeRatio c a b i) := by
      gcongr

theorem r51_sum_coordinate_log_ratio_le
    {q : ℕ} [NeZero q] (a b : Z4) (i : Fin 4) :
    (∑ c : R51Cut q,
        Real.log (r51CoordinateEdgeRatio c a b i)) ≤
      2 * q ^ 4 := by
  let x : ZMod q := (a i : ℤ)
  let y : ZMod q := (b i : ℤ)
  let f : Fin q → ℝ := fun ci =>
    Real.log (r51CutBracket ci x y /
      r51CyclicBracket q x y)
  let rest := {j : Fin 4 // j ≠ i}
  let e : R51Cut q ≃ Fin q × (rest → Fin q) :=
    Equiv.funSplitAt i (Fin q)
  have hreindex :
      (∑ c : R51Cut q, f (c i)) =
        ∑ p : Fin q × (rest → Fin q), f p.1 := by
    have hcomp :=
      e.sum_comp (fun p : Fin q × (rest → Fin q) => f p.1)
    simpa [e, Equiv.funSplitAt, Equiv.piSplitAt] using hcomp
  have hrestCard : Fintype.card rest = 3 := by
    dsimp only [rest]
    rw [Fintype.card_subtype_compl
      (fun j : Fin 4 => j = i)]
    simp
  have hfunCard :
      Fintype.card (rest → Fin q) = q ^ 3 := by
    rw [Fintype.card_fun, hrestCard, Fintype.card_fin]
  have hone :=
    r51_sum_log_cutBracket_div_cyclic_le x y
  change (∑ c : R51Cut q, f (c i)) ≤ 2 * q ^ 4
  rw [hreindex, Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, hfunCard]
  have hpow0 : (0 : ℝ) ≤ (q : ℝ) ^ 3 := by positivity
  calc
    ∑ x_1 : Fin q, ((q ^ 3 : ℕ) : ℝ) * f x_1 =
        (q : ℝ) ^ 3 * ∑ x_1 : Fin q, f x_1 := by
      simp only [Nat.cast_pow, Finset.mul_sum]
    _ ≤ (q : ℝ) ^ 3 * (2 * q) :=
      mul_le_mul_of_nonneg_left hone hpow0
    _ = 2 * q ^ 4 := by ring

theorem r51_sum_vector_log_distortion_le
    {q : ℕ} [NeZero q] (a b : Z4) :
    (∑ c : R51Cut q,
        Real.log
          (latticeBracketSq (r51CutLift q c a)
              (r51CutLift q c b) /
            latticeBracketSq a
              (r51MinimalTranslate q a b))) ≤
      12 * q ^ 4 := by
  calc
    (∑ c : R51Cut q,
        Real.log
          (latticeBracketSq (r51CutLift q c a)
              (r51CutLift q c b) /
            latticeBracketSq a
              (r51MinimalTranslate q a b))) ≤
      ∑ c : R51Cut q,
        (4 + ∑ i : Fin 4,
          Real.log (r51CoordinateEdgeRatio c a b i)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact r51_vector_log_distortion_le c a b
    _ = (Fintype.card (R51Cut q) : ℝ) * 4 +
        ∑ i : Fin 4,
          ∑ c : R51Cut q,
            Real.log (r51CoordinateEdgeRatio c a b i) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp
    _ ≤ (q ^ 4 : ℝ) * 4 +
        ∑ _i : Fin 4, (2 * q ^ 4 : ℝ) := by
      have hcard : Fintype.card (R51Cut q) = q ^ 4 := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      rw [hcard]
      push_cast
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i hi
      exact r51_sum_coordinate_log_ratio_le a b i
    _ = 12 * q ^ 4 := by
      simp
      ring

/-! The torus-correct diameter and whole-word statistics. -/

theorem r51_minimalBracket_le_cutBracket
    {q : ℕ} [NeZero q] (c : R51Cut q)
    (a b : Z4) :
    latticeBracketSq a (r51MinimalTranslate q a b) ≤
      latticeBracketSq (r51CutLift q c a)
        (r51CutLift q c b) := by
  let dmin := r51MinimalDifference q a b
  let dcut := r51CutLift q c a - r51CutLift q c b
  have hcoord : ∀ i : Fin 4,
      |((dmin i : ℤ) : ℝ)| ≤ |((dcut i : ℤ) : ℝ)| := by
    intro i
    have hmin := r51MinimalDifference_coord_abs
      (q := q) a b i
    have hcut := r51CutLift_sub_coord_abs
      (q := q) c a b i
    let r :=
      r51CyclicGap q
        (((a i : ℤ) : ZMod q))
        (((b i : ℤ) : ZMod q))
    have htwo :
        2 * r ≤ q := r51CyclicGap_mul_two_le _ _
    have hNat :
        r ≤
          (if r51CutIsLong (c i)
              (((a i : ℤ) : ZMod q))
              (((b i : ℤ) : ZMod q)) then
            q - r
          else r) := by
      split_ifs
      · omega
      · exact le_rfl
    have hInt :
        |dmin i| ≤ |dcut i| := by
      rw [hmin, hcut]
      exact_mod_cast hNat
    exact_mod_cast hInt
  have hnorm : znorm dmin ≤ znorm dcut := by
    unfold znorm
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have hc := znorm_coord_le dcut i
    simpa only [znorm, Real.norm_eq_abs] using
      (hcoord i).trans hc
  have hsq :=
    pow_le_pow_left₀ (znorm_nonneg dmin) hnorm 2
  unfold latticeBracketSq
  rw [r51_sub_minimalTranslate]
  change 1 + znorm dmin ^ 2 ≤ 1 + znorm dcut ^ 2
  gcongr

/-- Maximum shortest-lift lattice bracket.  On a compatible mesh this is
exactly `1 + δ⁻²` times the squared torus diameter. -/
def r51PeriodicTupleDiameterBracketSq
    {m : ℕ} (q : ℕ) (hm : 0 < m)
    (y : Fin m → Z4) : ℝ :=
  Finset.univ.sup'
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun i : Fin m =>
      Finset.univ.sup'
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        (fun j : Fin m =>
          latticeBracketSq (y i)
            (r51MinimalTranslate q (y i) (y j))))

theorem one_le_r51PeriodicTupleDiameterBracketSq
    {m q : ℕ} (hm : 0 < m) (y : Fin m → Z4) :
    1 ≤ r51PeriodicTupleDiameterBracketSq q hm y := by
  let i₀ : Fin m := ⟨0, hm⟩
  unfold r51PeriodicTupleDiameterBracketSq
  have hdiag :
      1 ≤ latticeBracketSq (y i₀)
        (r51MinimalTranslate q (y i₀) (y i₀)) :=
    one_le_latticeBracketSq _ _
  exact hdiag.trans
    ((Finset.le_sup'
      (f := fun j : Fin m =>
        latticeBracketSq (y i₀)
          (r51MinimalTranslate q (y i₀) (y j)))
      (by simp : i₀ ∈ (Finset.univ : Finset (Fin m)))).trans
      (Finset.le_sup'
        (f := fun i : Fin m =>
          Finset.univ.sup'
            ⟨i₀, Finset.mem_univ _⟩
            (fun j : Fin m =>
              latticeBracketSq (y i)
                (r51MinimalTranslate q (y i) (y j))))
        (by simp : i₀ ∈ (Finset.univ : Finset (Fin m)))))

theorem r51PeriodicTupleDiameterBracketSq_pos
    {m q : ℕ} (hm : 0 < m) (y : Fin m → Z4) :
    0 < r51PeriodicTupleDiameterBracketSq q hm y :=
  zero_lt_one.trans_le
    (one_le_r51PeriodicTupleDiameterBracketSq hm y)

theorem r51PeriodicTupleDiameterBracketSq_le_cutLift
    {m q : ℕ} [NeZero q] (hm : 0 < m)
    (c : R51Cut q) (y : Fin m → Z4) :
    r51PeriodicTupleDiameterBracketSq q hm y ≤
      primitiveTupleDiameterBracketSq hm
        (fun i => r51CutLift q c (y i)) := by
  unfold r51PeriodicTupleDiameterBracketSq
    primitiveTupleDiameterBracketSq
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  exact (r51_minimalBracket_le_cutBracket c (y i) (y j)).trans
    ((Finset.le_sup'
      (f := fun k : Fin m =>
        latticeBracketSq
          (r51CutLift q c (y i))
          (r51CutLift q c (y k)))
      (by simp : j ∈ (Finset.univ : Finset (Fin m)))).trans
      (Finset.le_sup'
        (f := fun k : Fin m =>
          Finset.univ.sup'
            ⟨⟨0, hm⟩, Finset.mem_univ _⟩
            (fun l : Fin m =>
              latticeBracketSq
                (r51CutLift q c (y k))
                (r51CutLift q c (y l))))
        (by simp : i ∈ (Finset.univ : Finset (Fin m)))))

def r51PeriodicWordChainWeight
    {m : ℕ} (δ : ℝ) (y : Fin m → Z4) : ℝ :=
  ∏ j : AdjacentIndex m,
    periodicCellEdgeWeight δ (y j.1) (y (adjacentSucc j))

def r51LatticeWordChainWeight
    {m : ℕ} (y : Fin m → Z4) : ℝ :=
  ∏ j : AdjacentIndex m,
    latticeEdgeWeight (y j.1) (y (adjacentSucc j))

def r51PeriodicReductionWeight
    {m : ℕ} (q : ℕ) (hm : 0 < m)
    (δ : ℝ) (y : Fin m → Z4) : ℝ :=
  r51PeriodicTupleDiameterBracketSq q hm y *
    r51PeriodicWordChainWeight δ y

def r51LatticeReductionWeight
    {m : ℕ} (hm : 0 < m) (y : Fin m → Z4) : ℝ :=
  primitiveTupleDiameterBracketSq hm y *
    r51LatticeWordChainWeight y

theorem r51PeriodicWordChainWeight_pos
    {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (y : Fin m → Z4) :
    0 < r51PeriodicWordChainWeight δ y := by
  unfold r51PeriodicWordChainWeight periodicCellEdgeWeight
  apply Finset.prod_pos
  intro j hj
  positivity

theorem r51LatticeWordChainWeight_pos
    {m : ℕ} (y : Fin m → Z4) :
    0 < r51LatticeWordChainWeight y := by
  unfold r51LatticeWordChainWeight latticeEdgeWeight
  apply Finset.prod_pos
  intro j hj
  positivity

theorem r51PeriodicReductionWeight_pos
    {m q : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) (y : Fin m → Z4) :
    0 < r51PeriodicReductionWeight q hm δ y :=
  mul_pos (r51PeriodicTupleDiameterBracketSq_pos hm y)
    (r51PeriodicWordChainWeight_pos hδ y)

theorem r51LatticeReductionWeight_pos
    {m : ℕ} (hm : 0 < m) (y : Fin m → Z4) :
    0 < r51LatticeReductionWeight hm y :=
  mul_pos
    (zero_lt_one.trans_le
      (one_le_primitiveTupleDiameterBracketSq hm y))
    (r51LatticeWordChainWeight_pos y)

theorem r51PeriodicWordChainWeight_div_cut_eq
    {m q : ℕ} [NeZero q]
    {δ : ℝ} (hδ : 0 < δ)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (c : R51Cut q) (y : Fin m → Z4) :
    r51PeriodicWordChainWeight δ y /
        r51LatticeWordChainWeight
          (fun i => r51CutLift q c (y i)) =
      ∏ j : AdjacentIndex m,
        latticeBracketSq
            (r51CutLift q c (y j.1))
            (r51CutLift q c (y (adjacentSucc j))) /
          latticeBracketSq (y j.1)
            (r51MinimalTranslate q (y j.1)
              (y (adjacentSucc j))) := by
  unfold r51PeriodicWordChainWeight
    r51LatticeWordChainWeight
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [periodicCellEdgeWeight_eq_r51Minimal hδ hq]
  unfold latticeEdgeWeight latticeBracketSq
  field_simp

theorem r51_log_periodicWordChain_div_cut_eq
    {m q : ℕ} [NeZero q]
    {δ : ℝ} (hδ : 0 < δ)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (c : R51Cut q) (y : Fin m → Z4) :
    Real.log
        (r51PeriodicWordChainWeight δ y /
          r51LatticeWordChainWeight
            (fun i => r51CutLift q c (y i))) =
      ∑ j : AdjacentIndex m,
        Real.log
          (latticeBracketSq
              (r51CutLift q c (y j.1))
              (r51CutLift q c (y (adjacentSucc j))) /
            latticeBracketSq (y j.1)
              (r51MinimalTranslate q (y j.1)
                (y (adjacentSucc j)))) := by
  rw [r51PeriodicWordChainWeight_div_cut_eq hδ hq]
  rw [Real.log_prod]
  intro j hj
  exact ne_of_gt
    (div_pos
      (lt_of_lt_of_le zero_lt_one
        (one_le_latticeBracketSq _ _))
      (lt_of_lt_of_le zero_lt_one
        (one_le_latticeBracketSq _ _)))

theorem r51_log_periodicReduction_div_cut_le
    {m q : ℕ} [NeZero q] (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (c : R51Cut q) (y : Fin m → Z4) :
    Real.log
        (r51PeriodicReductionWeight q hm δ y /
          r51LatticeReductionWeight hm
            (fun i => r51CutLift q c (y i))) ≤
      ∑ j : AdjacentIndex m,
        Real.log
          (latticeBracketSq
              (r51CutLift q c (y j.1))
              (r51CutLift q c (y (adjacentSucc j))) /
            latticeBracketSq (y j.1)
              (r51MinimalTranslate q (y j.1)
                (y (adjacentSucc j)))) := by
  let Dp := r51PeriodicTupleDiameterBracketSq q hm y
  let Dc := primitiveTupleDiameterBracketSq hm
    (fun i => r51CutLift q c (y i))
  let Pp := r51PeriodicWordChainWeight δ y
  let Pc := r51LatticeWordChainWeight
    (fun i => r51CutLift q c (y i))
  have hDp : 0 < Dp :=
    r51PeriodicTupleDiameterBracketSq_pos hm y
  have hDc : 0 < Dc :=
    zero_lt_one.trans_le
      (one_le_primitiveTupleDiameterBracketSq hm _)
  have hPp : 0 < Pp := r51PeriodicWordChainWeight_pos hδ y
  have hPc : 0 < Pc := r51LatticeWordChainWeight_pos _
  have hD : Dp ≤ Dc :=
    r51PeriodicTupleDiameterBracketSq_le_cutLift hm c y
  have hratio :
      (Dp * Pp) / (Dc * Pc) ≤ Pp / Pc := by
    have hDdiv : Dp / Dc ≤ 1 :=
      (div_le_one hDc).2 hD
    have hPdiv : 0 ≤ Pp / Pc := (div_pos hPp hPc).le
    calc
      (Dp * Pp) / (Dc * Pc) =
          (Dp / Dc) * (Pp / Pc) := by
        field_simp
      _ ≤ 1 * (Pp / Pc) :=
        mul_le_mul_of_nonneg_right hDdiv hPdiv
      _ = Pp / Pc := one_mul _
  have hlog :
      Real.log ((Dp * Pp) / (Dc * Pc)) ≤
        Real.log (Pp / Pc) :=
    Real.strictMonoOn_log.monotoneOn
      (div_pos (mul_pos hDp hPp) (mul_pos hDc hPc))
      (div_pos hPp hPc) hratio
  change
    Real.log ((Dp * Pp) / (Dc * Pc)) ≤ _
  exact hlog.trans_eq
    (r51_log_periodicWordChain_div_cut_eq hδ hq c y)

theorem r51_sum_log_periodicReduction_div_cut_le
    {m q : ℕ} [NeZero q] (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (y : Fin m → Z4) :
    (∑ c : R51Cut q,
        Real.log
          (r51PeriodicReductionWeight q hm δ y /
            r51LatticeReductionWeight hm
              (fun i => r51CutLift q c (y i)))) ≤
      12 * (m - 1) * q ^ 4 := by
  calc
    (∑ c : R51Cut q,
        Real.log
          (r51PeriodicReductionWeight q hm δ y /
            r51LatticeReductionWeight hm
              (fun i => r51CutLift q c (y i)))) ≤
      ∑ c : R51Cut q,
        ∑ j : AdjacentIndex m,
          Real.log
            (latticeBracketSq
                (r51CutLift q c (y j.1))
                (r51CutLift q c (y (adjacentSucc j))) /
              latticeBracketSq (y j.1)
                (r51MinimalTranslate q (y j.1)
                  (y (adjacentSucc j)))) := by
      apply Finset.sum_le_sum
      intro c hc
      exact r51_log_periodicReduction_div_cut_le
        hm hδ hq c y
    _ = ∑ j : AdjacentIndex m,
        ∑ c : R51Cut q,
          Real.log
            (latticeBracketSq
                (r51CutLift q c (y j.1))
                (r51CutLift q c (y (adjacentSucc j))) /
              latticeBracketSq (y j.1)
                (r51MinimalTranslate q (y j.1)
                  (y (adjacentSucc j)))) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _j : AdjacentIndex m, (12 * q ^ 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact r51_sum_vector_log_distortion_le
        (y j.1) (y (adjacentSucc j))
    _ = 12 * (m - 1) * q ^ 4 := by
      have hcard :
          Fintype.card (AdjacentIndex m) = m - 1 := by
        simpa using Fintype.card_congr (adjacentIndexEquiv m)
      simp [hcard]
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      ring

/-! Converting the logarithmic cut ledger into an arithmetic average. -/

theorem r51_le_exp_mul_average_of_sum_log_div_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {A K : ℝ} (hA : 0 < A)
    (B : ι → ℝ) (hB : ∀ i, 0 < B i)
    (hlog :
      (∑ i : ι, Real.log (A / B i)) ≤
        (Fintype.card ι : ℝ) * K) :
    A ≤ Real.exp K *
      ((∑ i : ι, B i) / (Fintype.card ι : ℝ)) := by
  let N : ℝ := Fintype.card ι
  let S : ℝ := ∑ i : ι, Real.log (B i)
  have hcard : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr inferInstance
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast hcard
  have hsumlog :
      (∑ i : ι, Real.log (A / B i)) =
        N * Real.log A - S := by
    simp_rw [Real.log_div (ne_of_gt hA) (ne_of_gt (hB _))]
    dsimp only [N, S]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsumlog] at hlog
  have hcenter :
      Real.log A - K ≤ S / N := by
    apply (le_div_iff₀ hN).2
    nlinarith
  have hlogA :
      Real.log A ≤ K + S / N := by linarith
  have hexp :
      A ≤ Real.exp K * Real.exp (S / N) := by
    have hmono := Real.exp_le_exp.mpr hlogA
    rw [Real.exp_log hA, Real.exp_add] at hmono
    exact hmono
  let w : ℝ := N⁻¹
  have hw0 : 0 ≤ w := inv_nonneg.mpr hN.le
  have hwsum :
      (∑ _i : ι, w) = 1 := by
    dsimp only [w, N]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ]
    field_simp
  have hgeom :
      Real.exp (S / N) =
        ∏ i : ι, (B i) ^ w := by
    dsimp only [S]
    rw [Finset.sum_div, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Real.rpow_def_of_pos (hB i)]
    dsimp only [w]
    congr 1
  have hgm :=
    Real.geom_mean_le_arith_mean_weighted
      (Finset.univ : Finset ι)
      (fun _ => w) B
      (fun i hi => hw0)
      (by simpa only [Finset.sum_const, nsmul_eq_mul] using hwsum)
      (fun i hi => (hB i).le)
  have hmean :
      (∏ i : ι, (B i) ^ w) ≤
        (∑ i : ι, B i) / N := by
    calc
      (∏ i : ι, (B i) ^ w) ≤
          ∑ i : ι, w * B i := by
        simpa only using hgm
      _ = (∑ i : ι, B i) / N := by
        dsimp only [w]
        rw [← Finset.mul_sum]
        field_simp
  calc
    A ≤ Real.exp K * Real.exp (S / N) := hexp
    _ = Real.exp K * (∏ i : ι, (B i) ^ w) := by
      rw [hgeom]
    _ ≤ Real.exp K * ((∑ i : ι, B i) / N) :=
      mul_le_mul_of_nonneg_left hmean (Real.exp_pos K).le

theorem r51PeriodicReductionWeight_le_cutAverage
    {m q : ℕ} [NeZero q] (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (y : Fin m → Z4) :
    r51PeriodicReductionWeight q hm δ y ≤
      Real.exp (12 * (m - 1)) *
        ((∑ c : R51Cut q,
            r51LatticeReductionWeight hm
              (fun i => r51CutLift q c (y i))) /
          (q : ℝ) ^ 4) := by
  let A := r51PeriodicReductionWeight q hm δ y
  let B : R51Cut q → ℝ := fun c =>
    r51LatticeReductionWeight hm
      (fun i => r51CutLift q c (y i))
  have hA : 0 < A := r51PeriodicReductionWeight_pos hm hδ y
  have hB : ∀ c, 0 < B c := fun c =>
    r51LatticeReductionWeight_pos hm _
  have hlog :=
    r51_sum_log_periodicReduction_div_cut_le
      hm hδ hq y
  have hcard : Fintype.card (R51Cut q) = q ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hmaster :=
    r51_le_exp_mul_average_of_sum_log_div_le
      hA B hB
      (K := 12 * (m - 1))
      (by
        dsimp only [A, B]
        rw [hcard]
        push_cast
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hlog)
  dsimp only [A, B] at hmaster
  rw [hcard] at hmaster
  push_cast at hmaster
  exact hmaster


/-! ## Uniform finite fibers of a fixed cut lift

Inside the canonical box, two representatives of one residue differ by at
most one period in either direction.  The three-valued code below records
which of the intervals `[-q,0)`, `[0,q)`, and `{q}` contains a coordinate.
Together with its cut lift this code is injective.  Consequently every
tuple fiber has cardinality at most `3^(4m)`, uniformly in the mesh. -/

def r51BoxCode (q : ℕ) (x : ℤ) : Fin 3 :=
  if x < 0 then 0 else if x < q then 1 else 2

theorem r51BoxCode_injective_of_dvd
    {q : ℕ} (hq : 0 < q) {x y : ℤ}
    (hx : |x| ≤ (q : ℤ)) (hy : |y| ≤ (q : ℤ))
    (hdvd : (q : ℤ) ∣ x - y)
    (hcode : r51BoxCode q x = r51BoxCode q y) :
    x = y := by
  have hxlo : -(q : ℤ) ≤ x := (abs_le.mp hx).1
  have hxhi : x ≤ (q : ℤ) := (abs_le.mp hx).2
  have hylo : -(q : ℤ) ≤ y := (abs_le.mp hy).1
  have hyhi : y ≤ (q : ℤ) := (abs_le.mp hy).2
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  unfold r51BoxCode at hcode
  by_cases hxneg : x < 0
  · by_cases hyneg : y < 0
    · have habs : |x - y| < (q : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      have hnatAbs : (x - y).natAbs < q := by
        have hcast :
            ((x - y).natAbs : ℤ) < (q : ℤ) := by
          rw [← Int.abs_eq_natAbs]
          exact habs
        exact_mod_cast hcast
      apply sub_eq_zero.mp
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
      simpa using hnatAbs
    · simp only [hxneg, hyneg, ↓reduceIte] at hcode
      split at hcode <;>
        have := congrArg Fin.val hcode <;> norm_num at this
  · by_cases hyneg : y < 0
    · simp only [hxneg, hyneg, ↓reduceIte] at hcode
      split at hcode <;>
        have := congrArg Fin.val hcode <;> norm_num at this
    · simp only [hxneg, hyneg, ↓reduceIte] at hcode
      by_cases hxq : x < q
      · by_cases hyq : y < q
        · have habs : |x - y| < (q : ℤ) := by
            rw [abs_lt]
            constructor <;> omega
          have hnatAbs : (x - y).natAbs < q := by
            have hcast :
                ((x - y).natAbs : ℤ) < (q : ℤ) := by
              rw [← Int.abs_eq_natAbs]
              exact habs
            exact_mod_cast hcast
          apply sub_eq_zero.mp
          apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
          simpa using hnatAbs
        · simp only [hxq, hyq, ↓reduceIte] at hcode
          have := congrArg Fin.val hcode
          norm_num at this
      · by_cases hyq : y < q
        · simp only [hxq, hyq, ↓reduceIte] at hcode
          have := congrArg Fin.val hcode
          norm_num at this
        · omega

@[simp]
theorem r51CutLift_cast_zmod
    {q : ℕ} [NeZero q] (c : R51Cut q) (a : Z4)
    (i : Fin 4) :
    ((r51CutLift q c a i : ℤ) : ZMod q) =
      ((a i : ℤ) : ZMod q) := by
  unfold r51CutLift r51CutRepresentative
  split_ifs <;> simp

theorem r51CutLift_code_injectiveOn_box
    {q m : ℕ} [NeZero q] (c : R51Cut q) :
    Set.InjOn
      (fun y : Fin m → Z4 =>
        ((fun j => r51CutLift q c (y j)),
          fun j i => r51BoxCode q (y j i)))
      {y | ∀ j i, |y j i| ≤ (q : ℤ)} := by
  intro y₁ hy₁ y₂ hy₂ heq
  have hout := congrArg Prod.fst heq
  have hcode := congrArg Prod.snd heq
  funext j i
  apply r51BoxCode_injective_of_dvd (NeZero.pos q)
    (hy₁ j i) (hy₂ j i)
  · apply
      (ZMod.intCast_eq_intCast_iff_dvd_sub
        (y₂ j i) (y₁ j i) q).mp
    rw [← r51CutLift_cast_zmod c (y₁ j) i,
      ← r51CutLift_cast_zmod c (y₂ j) i]
    exact congrArg (fun a : Z4 => ((a i : ℤ) : ZMod q))
      (congrFun hout j).symm
  · exact congrFun (congrFun hcode j) i

theorem r51CutLift_fiber_card_le
    {q m : ℕ} [NeZero q] (c : R51Cut q)
    (s : Finset (Fin m → Z4))
    (hbox : ∀ y ∈ s, ∀ j i, |y j i| ≤ (q : ℤ))
    (u : Fin m → Z4) :
    (s.filter (fun y =>
        (fun j => r51CutLift q c (y j)) = u)).card ≤
      (3 ^ 4) ^ m := by
  classical
  let t :=
    s.filter (fun y =>
      (fun j => r51CutLift q c (y j)) = u)
  let code : (Fin m → Z4) → (Fin m → Fin 4 → Fin 3) :=
    fun y j i => r51BoxCode q (y j i)
  have hinj : Set.InjOn code t := by
    intro y₁ hy₁ y₂ hy₂ hcode
    have hy₁' := Finset.mem_filter.mp hy₁
    have hy₂' := Finset.mem_filter.mp hy₂
    apply r51CutLift_code_injectiveOn_box c
      (hbox y₁ hy₁'.1) (hbox y₂ hy₂'.1)
    exact Prod.ext (hy₁'.2.trans hy₂'.2.symm) hcode
  have hcard :
      Fintype.card (Fin m → Fin 4 → Fin 3) =
        (3 ^ 4) ^ m := by
    rw [Fintype.card_fun, Fintype.card_fun]
    simp
  change t.card ≤ (3 ^ 4) ^ m
  rw [← hcard, ← Finset.card_univ]
  exact Finset.card_le_card_of_injOn code
    (fun _ _ => Finset.mem_univ _) hinj

theorem r51_sum_cutLift_le_box_sum
    {q m : ℕ} [NeZero q] (c : R51Cut q)
    (s : Finset (Fin m → Z4))
    (hbox : ∀ y ∈ s, ∀ j i, |y j i| ≤ (q : ℤ))
    (B : Finset (Fin m → Z4))
    (hmap :
      ∀ y ∈ s, (fun j => r51CutLift q c (y j)) ∈ B)
    (F : (Fin m → Z4) → ℝ) (hF : ∀ u, 0 ≤ F u) :
    (∑ y ∈ s, F (fun j => r51CutLift q c (y j))) ≤
      ((3 ^ 4) ^ m : ℕ) * ∑ u ∈ B, F u := by
  classical
  let g : (Fin m → Z4) → (Fin m → Z4) :=
    fun y j => r51CutLift q c (y j)
  have hdecomp :
      (∑ y ∈ s, F (g y)) =
        ∑ u ∈ B, ∑ y ∈ s with g y = u, F u := by
    exact
      (Finset.sum_fiberwise_of_maps_to'
        (fun y hy => hmap y hy) F).symm
  rw [hdecomp]
  calc
    (∑ u ∈ B, ∑ y ∈ s with g y = u, F u) =
        ∑ u ∈ B,
          (((s.filter (fun y => g y = u)).card : ℕ) : ℝ) *
            F u := by
      apply Finset.sum_congr rfl
      intro u hu
      simp
    _ ≤ ∑ u ∈ B, (((3 ^ 4) ^ m : ℕ) : ℝ) * F u := by
      apply Finset.sum_le_sum
      intro u hu
      apply mul_le_mul_of_nonneg_right _ (hF u)
      exact_mod_cast r51CutLift_fiber_card_le c s hbox u
    _ = (((3 ^ 4) ^ m : ℕ) : ℝ) * ∑ u ∈ B, F u := by
      rw [Finset.mul_sum]

theorem r51CutLift_coord_abs_le
    {q : ℕ} [NeZero q] (c : R51Cut q) (a : Z4)
    (i : Fin 4) :
    |r51CutLift q c a i| ≤ (2 * q : ℕ) := by
  unfold r51CutLift r51CutRepresentative
  split_ifs
  · rw [abs_of_nonneg]
    · norm_cast
      have := (((a i : ℤ) : ZMod q)).val_lt
      omega
    · omega
  · rw [abs_of_nonneg]
    · norm_cast
      have := (((a i : ℤ) : ZMod q)).val_lt
      omega
    · omega

theorem r51CutLift_tuple_mem_bounded
    {q m : ℕ} [NeZero q] (c : R51Cut q)
    (y : Fin m → Z4) :
    (fun j => r51CutLift q c (y j)) ∈
      rdec_boundedTuples (2 * q) m := by
  rw [rdec_mem_boundedTuples]
  intro j i
  exact_mod_cast r51CutLift_coord_abs_le c (y j) i

theorem r51CutLift_respectsPairing
    {q m : ℕ} [NeZero q] (c : R51Cut q)
    (κ : PartialPairing (Fin m)) (y : Fin m → Z4)
    (hy : RespectsPairing κ y) :
    RespectsPairing κ (fun j => r51CutLift q c (y j)) := by
  intro j
  exact congrArg (r51CutLift q c) (hy j)

theorem r51LatticeReductionWeight_eq_reductionWeight
    (n : ℕ) (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    r51LatticeReductionWeight (by omega) y =
      reductionWeight (2 * n - 1)
        (primitiveCopiedReductionTuple n hn y) := by
  unfold r51LatticeReductionWeight r51LatticeWordChainWeight
    reductionWeight
  rw [primitiveCopiedCellDiameter_eq_reductionDiameter n hn y]
  congr 1
  rw [adjacentProduct_eq_listChainProduct,
    adjacentProduct_eq_listChainProduct,
    primitiveCopiedReductionTuple_ofFn]

theorem primitiveCopiedSourceTuple_injective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (primitiveCopiedSourceTuple n hn) := by
  intro u v huv
  have h := congrArg (primitiveCopiedReductionTuple n hn) huv
  simpa using h

theorem r51_cutLift_cell_sum_le_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) {n q : ℕ} (hn : 1 ≤ n)
    (hq : (q : ℤ) = compatibleCellCount ε) [NeZero q]
    {κ : PartialPairing (Fin (2 * n))}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    (c : R51Cut q) :
    (∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
        r51LatticeReductionWeight (by omega)
          (fun j => r51CutLift q c (y j))) ≤
      ((3 ^ 4) ^ (2 * n) : ℕ) *
        primitiveAcrossLatticeSum (2 * q) (2 * n - 1)
          (pairingLowerHalf
            (primitiveReductionPairing n hn κ)) := by
  classical
  let S := primitiveCanonicalCellCarrier ε n κ
  let T :=
    rdec_boundedTuples (2 * q) ((2 * n - 1) + 1)
  let B : Finset (Fin (2 * n) → Z4) :=
    T.image (primitiveCopiedSourceTuple n hn)
  let κr := primitiveReductionPairing n hn κ
  have hfullr : κr.IsFull :=
    primitiveReductionPairing_isFull hfull
  have hprimitiver : IsPrimitive κr :=
    primitiveReductionPairing_isPrimitive hprimitive
  let A := pairingLowerHalf κr
  let κa : AcrossPairing A :=
    fullPairingToAcross κr hfullr
  have hκamem : κa ∈ primitiveAcrossPairingFinset A :=
    fullPairingToAcross_mem_primitiveAcrossPairingFinset
      hfullr hprimitiver
  let F : (Fin (2 * n) → Z4) → ℝ := fun u =>
    pairedReductionStatistic (2 * n - 1) A κa
      (primitiveCopiedReductionTuple n hn u)
  have hbox :
      ∀ y ∈ S, ∀ j i, |y j i| ≤ (q : ℤ) := by
    intro y hy j i
    have h :=
      primitiveCanonicalCellCarrier_abs_le_cellCount
        hε hy j i
    simpa only [hq] using h
  have hmap :
      ∀ y ∈ S,
        (fun j => r51CutLift q c (y j)) ∈ B := by
    intro y hy
    let u : Fin (2 * n) → Z4 :=
      fun j => r51CutLift q c (y j)
    rw [Finset.mem_image]
    refine
      ⟨primitiveCopiedReductionTuple n hn u, ?_, ?_⟩
    · exact primitiveReductionTupleOfCellTuple_mem_bounded
        (r51CutLift_tuple_mem_bounded c y)
    · simp only [u, primitiveCopiedSourceTuple_reductionTuple]
  have hF : ∀ u, 0 ≤ F u := by
    intro u
    exact pairedReductionStatistic_nonneg _ _ _ _
  have hsum :=
    r51_sum_cutLift_le_box_sum c S hbox B hmap F hF
  have hleft :
      (∑ y ∈ S,
          F (fun j => r51CutLift q c (y j))) =
        ∑ y ∈ S,
          r51LatticeReductionWeight (by omega)
            (fun j => r51CutLift q c (y j)) := by
    apply Finset.sum_congr rfl
    intro y hy
    have hyrespect : RespectsPairing κ y :=
      (Finset.mem_filter.mp hy).2
    have hliftrespect :
        RespectsPairing κ
          (fun j => r51CutLift q c (y j)) :=
      r51CutLift_respectsPairing c κ y hyrespect
    have hreduced :
        RespectsPairing κr
          (primitiveCopiedReductionTuple n hn
            (fun j => r51CutLift q c (y j))) :=
      primitiveCopiedReductionTuple_respectsPairing hliftrespect
    have hiff :=
      respectsPairing_acrossToPartialPairing_iff A κa
        (primitiveCopiedReductionTuple n hn
          (fun j => r51CutLift q c (y j)))
    rw [acrossToPartialPairing_fullPairingToAcross κr hfullr]
      at hiff
    unfold F pairedReductionStatistic
    rw [if_pos (hiff.mp hreduced)]
    exact
      (r51LatticeReductionWeight_eq_reductionWeight
        n hn (fun j => r51CutLift q c (y j))).symm
  have hBsum :
      (∑ u ∈ B, F u) =
        latticeChainSum (2 * q) ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κa) := by
    unfold B T latticeChainSum
    rw [Finset.sum_image
      (primitiveCopiedSourceTuple_injective n hn).injOn]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [F, primitiveCopiedReductionTuple_sourceTuple]
  have hfixed :
      latticeChainSum (2 * q) ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κa) ≤
        primitiveAcrossLatticeSum (2 * q) (2 * n - 1) A := by
    unfold primitiveAcrossLatticeSum
    exact Finset.single_le_sum
      (s := primitiveAcrossPairingFinset A)
      (f := fun κ' =>
        latticeChainSum (2 * q) ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κ'))
      (fun κ' hκ' => by
        unfold latticeChainSum
        apply Finset.sum_nonneg
        intro u hu
        exact pairedReductionStatistic_nonneg _ _ _ _)
      hκamem
  rw [← hleft]
  exact hsum.trans
    (mul_le_mul_of_nonneg_left
      (hBsum.le.trans hfixed)
      (by positivity))

theorem r51_periodic_cell_sum_le_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) {n q : ℕ} (hn : 1 ≤ n)
    (hq : (q : ℤ) = compatibleCellCount ε) [NeZero q]
    {κ : PartialPairing (Fin (2 * n))}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    (∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
        r51PeriodicReductionWeight q (by omega)
          (compatibleMeshSize ε) y) ≤
      Real.exp (12 * (2 * n - 1)) *
        (((3 ^ 4) ^ (2 * n) : ℕ) *
          primitiveAcrossLatticeSum (2 * q) (2 * n - 1)
            (pairingLowerHalf
              (primitiveReductionPairing n hn κ))) := by
  classical
  let S := primitiveCanonicalCellCarrier ε n κ
  let E := Real.exp (12 * (((2 * n : ℕ) - 1 : ℕ) : ℝ))
  let K : ℝ := ((3 ^ 4) ^ (2 * n) : ℕ)
  let L :=
    primitiveAcrossLatticeSum (2 * q) (2 * n - 1)
      (pairingLowerHalf (primitiveReductionPairing n hn κ))
  have hδ : 0 < compatibleMeshSize ε :=
    compatibleMeshSize_pos hε
  have hmesh :
      PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ) := by
    rw [hq]
    exact compatibleMesh_isPeriodCompatible hε
  have hpoint :
      (∑ y ∈ S,
          r51PeriodicReductionWeight q (by omega)
            (compatibleMeshSize ε) y) ≤
        E * ((∑ y ∈ S,
          ∑ c : R51Cut q,
            r51LatticeReductionWeight (by omega)
              (fun j => r51CutLift q c (y j))) /
          (q : ℝ) ^ 4) := by
    calc
      (∑ y ∈ S,
          r51PeriodicReductionWeight q (by omega)
            (compatibleMeshSize ε) y) ≤
        ∑ y ∈ S,
          E * ((∑ c : R51Cut q,
            r51LatticeReductionWeight (by omega)
              (fun j => r51CutLift q c (y j))) /
            (q : ℝ) ^ 4) := by
        apply Finset.sum_le_sum
        intro y hy
        simpa only [E, Nat.cast_sub (by omega : 1 ≤ 2 * n),
          Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
          r51PeriodicReductionWeight_le_cutAverage
            (by omega) hδ hmesh y
      _ = E * ((∑ y ∈ S,
          ∑ c : R51Cut q,
            r51LatticeReductionWeight (by omega)
              (fun j => r51CutLift q c (y j))) /
          (q : ℝ) ^ 4) := by
        rw [Finset.sum_div]
        rw [Finset.mul_sum]
  have hcut :
      (∑ c : R51Cut q,
          ∑ y ∈ S,
            r51LatticeReductionWeight (by omega)
              (fun j => r51CutLift q c (y j))) ≤
        (q : ℝ) ^ 4 * (K * L) := by
    calc
      (∑ c : R51Cut q,
          ∑ y ∈ S,
            r51LatticeReductionWeight (by omega)
              (fun j => r51CutLift q c (y j))) ≤
        ∑ _c : R51Cut q, K * L := by
        apply Finset.sum_le_sum
        intro c hc
        exact r51_cutLift_cell_sum_le_primitiveAcross
          hε hn hq hfull hprimitive c
      _ = (q : ℝ) ^ 4 * (K * L) := by
        have hcard : Fintype.card (R51Cut q) = q ^ 4 := by
          rw [Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin]
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ, hcard]
        push_cast
        rfl
  have hnorm :
      ((∑ y ∈ S,
          ∑ c : R51Cut q,
            r51LatticeReductionWeight (by omega)
              (fun j => r51CutLift q c (y j))) /
          (q : ℝ) ^ 4) ≤ K * L := by
    rw [Finset.sum_comm]
    have hqR : (0 : ℝ) < q := by
      exact_mod_cast NeZero.pos q
    apply (div_le_iff₀ (pow_pos hqR 4)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcut
  have hfinal :=
    hpoint.trans
      (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)
  simpa only [E, K, L, Nat.cast_sub (by omega : 1 ≤ 2 * n),
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hfinal

/-! ## The analytic insertion with the torus-correct diameter

The shortest-lift maximum controls the actual torus diameter of every
compatible cell fiber.  This is the point at which the valid `Dper`
argument replaces the canonical-box diameter of the diagnostic routes
above. -/

theorem r51_minimalBracket_le_periodicTupleDiameter
    {m q : ℕ} (hm : 0 < m) (y : Fin m → Z4)
    (i j : Fin m) :
    latticeBracketSq (y i)
        (r51MinimalTranslate q (y i) (y j)) ≤
      r51PeriodicTupleDiameterBracketSq q hm y := by
  unfold r51PeriodicTupleDiameterBracketSq
  exact
    (Finset.le_sup'
      (f := fun k : Fin m =>
        latticeBracketSq (y i)
          (r51MinimalTranslate q (y i) (y k)))
      (by simp : j ∈ (Finset.univ : Finset (Fin m)))).trans
      (Finset.le_sup'
        (f := fun k : Fin m =>
          Finset.univ.sup'
            ⟨⟨0, hm⟩, Finset.mem_univ _⟩
            (fun l : Fin m =>
              latticeBracketSq (y k)
                (r51MinimalTranslate q (y k) (y l))))
        (by simp : i ∈ (Finset.univ : Finset (Fin m))))

theorem r51_torusTupleDiameterSq_le_periodicCellMaximum
    {m q : ℕ} [Nonempty (Fin m)] [NeZero q]
    (hm : 0 < m) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (y : Fin m → Z4) (x : Fin m → T4)
    (hx : ∀ i, x i ∈ latticeCellNeighborhood δ R (y i)) :
    torusTupleDiameterSq x ≤
      8 * δ ^ 2 *
        (4 * R ^ 2 +
          r51PeriodicTupleDiameterBracketSq q hm y) := by
  unfold torusTupleDiameterSq
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  let yj := r51MinimalTranslate q (y i) (y j)
  let d : ℝ := znorm (y i - yj)
  let D : ℝ := r51PeriodicTupleDiameterBracketSq q hm y
  have hxi :
      dist (x i) (latticeTorusCenter δ (y i)) ≤ R * δ :=
    (show dist (x i) (latticeTorusCenter δ (y i)) < R * δ
      from hx i).le
  have hxj :
      dist (latticeTorusCenter δ (y j)) (x j) ≤ R * δ := by
    rw [dist_comm]
    exact
      (show dist (x j) (latticeTorusCenter δ (y j)) < R * δ
        from hx j).le
  have hcenter :
      latticeTorusCenter δ yj =
        latticeTorusCenter δ (y j) := by
    exact latticeTorusCenter_r51MinimalTranslate hq (y i) (y j)
  have hc :
      dist (latticeTorusCenter δ (y i))
          (latticeTorusCenter δ (y j)) =
        δ * d := by
    rw [← hcenter]
    exact latticeTorusCenter_dist_eq_of_edgeNoWrap hδ
      (r51MinimalTranslate_edgeNoWrap hq (y i) (y j))
  have hdist :
      dist (x i) (x j) ≤ δ * (2 * R + d) := by
    calc
      dist (x i) (x j) ≤
          dist (x i) (latticeTorusCenter δ (y i)) +
            dist (latticeTorusCenter δ (y j)) (x j) +
            dist (latticeTorusCenter δ (y i))
              (latticeTorusCenter δ (y j)) := by
        nlinarith [dist_triangle4 (x i)
          (latticeTorusCenter δ (y i))
          (latticeTorusCenter δ (y j)) (x j)]
      _ ≤ R * δ + R * δ + δ * d := by
        gcongr
        exact hc.le
      _ = δ * (2 * R + d) := by ring
  have hdist0 : 0 ≤ dist (x i) (x j) := dist_nonneg
  have hright0 : 0 ≤ δ * (2 * R + d) := by
    apply mul_nonneg hδ.le
    exact add_nonneg (by positivity) (znorm_nonneg _)
  have hsq :
      dist (x i) (x j) ^ 2 ≤
        (δ * (2 * R + d)) ^ 2 :=
    pow_le_pow_left₀ hdist0 hdist 2
  have htorus :
      torusDistSq (x i - x j) ≤
        4 * dist (x i) (x j) ^ 2 := by
    simpa only [dist_eq_norm] using
      torusDistSq_le_four_mul_sq_norm (x i - x j)
  have hd0 : 0 ≤ d := znorm_nonneg _
  have hD :
      1 + d ^ 2 ≤ D := by
    exact r51_minimalBracket_le_periodicTupleDiameter
      hm y i j
  calc
    torusDistSq (x i - x j) ≤
        4 * dist (x i) (x j) ^ 2 := htorus
    _ ≤ 4 * (δ * (2 * R + d)) ^ 2 := by gcongr
    _ ≤ 8 * δ ^ 2 * (4 * R ^ 2 + D) := by
      nlinarith [sq_nonneg (2 * R - d), sq_nonneg δ]

theorem r51_primitiveInsertedFactor_le_periodicCellMaximum
    {m q : ℕ} [Nonempty (Fin m)] [NeZero q]
    (hm : 0 < m) {ε R : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hq :
      PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ))
    (y : Fin m → Z4) (x : Fin m → T4)
    (hx : ∀ i, x i ∈
      latticeCellNeighborhood (compatibleMeshSize ε) R (y i)) :
    ε ^ 2 + torusTupleDiameterSq x ≤
      (12 + 32 * R ^ 2) * compatibleMeshSize ε ^ 2 *
        r51PeriodicTupleDiameterBracketSq q hm y := by
  let δ := compatibleMeshSize ε
  let D := r51PeriodicTupleDiameterBracketSq q hm y
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hεδ : ε < 2 * δ :=
    lt_two_mul_compatibleMeshSize hε hε1
  have hεsq : ε ^ 2 ≤ 4 * δ ^ 2 := by
    nlinarith [sq_nonneg ε, sq_nonneg δ]
  have hdiam :
      torusTupleDiameterSq x ≤
        8 * δ ^ 2 * (4 * R ^ 2 + D) :=
    r51_torusTupleDiameterSq_le_periodicCellMaximum
      hm hδ hR hq y x hx
  have hDone : 1 ≤ D :=
    one_le_r51PeriodicTupleDiameterBracketSq hm y
  have hD0 : 0 ≤ D := zero_le_one.trans hDone
  dsimp only [δ, D] at *
  nlinarith [sq_nonneg (compatibleMeshSize ε),
    sq_nonneg R,
    mul_nonneg (sq_nonneg R) hD0,
    mul_nonneg (sq_nonneg (compatibleMeshSize ε)) hD0,
    mul_nonneg (sq_nonneg (compatibleMeshSize ε))
      (mul_nonneg (sq_nonneg R) hD0)]

/-- Pointwise copied-fiber estimate with the shortest-lift periodic
diameter.  Its `δ²` factor is retained for the critical power ledger. -/
theorem exists_r51_primitiveInsertedIntegrand_copiedFiber_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))), κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ) →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4)
          (v : Fin (2 * n - 2) → T4),
          pairedCellAssignment κ (compatibleMeshSize ε)
              (primitiveAssemble n hn z w v) = y →
          primitiveCovarianceProduct ρ ε n κ
              (primitiveAssemble n hn z w v) ≠ 0 →
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
          ENNReal.ofReal
              |primitiveInsertedIntegrand ρ ε n hn G κ
                (primitiveAssemble n hn z w v)| ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * C) ^ n *
                  ((12 + 32 * R ^ 2) * δ ^ 2 * D)) *
              terminalSingularProduct z w (List.ofFn v) := by
  obtain ⟨C, hC, hub⟩ :=
    exists_abs_primitiveIntegrand_uniform_bound ρ
  refine ⟨C, hC, ?_⟩
  intro n hn G hG κ hfull ε hε hε1 q instq hq z w y v hfiber hcov
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let x := primitiveAssemble n hn z w v
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
  let Q := (ε⁻¹ ^ (dim : ℕ) * C) ^ n
  let B := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let F := ε ^ 2 + torusTupleDiameterSq x
  let S := primitiveSingularChainProduct n hn x
  have hmem :=
    primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
      ρ κ hfull hε hε1 x hcov
  have hx : ∀ i, x i ∈ latticeCellNeighborhood δ R (y i) := by
    rw [hfiber] at hmem
    simpa only [x, δ, R] using hmem
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact add_nonneg (sq_nonneg ε) (torusTupleDiameterSq_nonneg x)
  have hF : F ≤ B := by
    have hraw :=
      r51_primitiveInsertedFactor_le_periodicCellMaximum
        (by omega : 0 < 2 * n) hε hε1 hR hq y x hx
    simpa only [F, B, D, δ, R] using hraw
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact pow_nonneg
      (mul_nonneg
        (pow_nonneg (inv_nonneg.mpr hε.le) _)
        hC.le) _
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact zero_le_one.trans
      (one_le_r51PeriodicTupleDiameterBracketSq (by omega) _)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (by positivity : 0 ≤ 12 + 32 * R ^ 2)
        (sq_nonneg δ))
      hD0
  have hS0 : 0 ≤ S :=
    primitiveSingularChainProduct_nonneg n hn x
  have hint :
      |primitiveIntegrand ρ ε n hn G κ x| ≤ Q * S := by
    simpa only [Q, S] using
      hub n hn G hG κ hfull hε hε1 x
  have hreal :
      |primitiveInsertedIntegrand ρ ε n hn G κ x| ≤
        (Q * B) * S := by
    calc
      |primitiveInsertedIntegrand ρ ε n hn G κ x| =
          F * |primitiveIntegrand ρ ε n hn G κ x| := by
        unfold primitiveInsertedIntegrand
        rw [abs_mul, abs_of_nonneg hF0]
      _ ≤ F * (Q * S) :=
        mul_le_mul_of_nonneg_left hint hF0
      _ ≤ B * (Q * S) :=
        mul_le_mul_of_nonneg_right hF
          (mul_nonneg hQ0 hS0)
      _ = (Q * B) * S := by ring
  calc
    ENNReal.ofReal
        |primitiveInsertedIntegrand ρ ε n hn G κ x| ≤
        ENNReal.ofReal ((Q * B) * S) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Q * B) *
          terminalSingularProduct z w (List.ofFn v) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hQ0 hB0)]
      change ENNReal.ofReal (Q * B) *
          ENNReal.ofReal
            (primitiveSingularChainProduct n hn
              (primitiveAssemble n hn z w v)) =
        ENNReal.ofReal (Q * B) *
          terminalSingularProduct z w (List.ofFn v)
      rw [primitiveSingularChainProduct_assemble_eq_terminal]

theorem exists_r51_primitiveInsertedIntegrand_copiedFiber_lintegral_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))), κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ) →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4),
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
          let c : Fin (2 * n - 2) → T4 := fun i =>
            latticeTorusCenter δ (y (primitiveInternalIdx n hn i))
          (∫⁻ v in
              (fun q =>
                pairedCellAssignment κ δ
                  (primitiveAssemble n hn z w q)) ⁻¹' {y},
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * C) ^ n *
                  ((12 + 32 * R ^ 2) * δ ^ 2 * D)) *
              terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
  obtain ⟨C, hC, hpointwise⟩ :=
    exists_r51_primitiveInsertedIntegrand_copiedFiber_bound ρ
  refine ⟨C, hC, ?_⟩
  intro n hn G hG κ hfull ε hε hε1 q instq hq z w y
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
  let c : Fin (2 * n - 2) → T4 := fun i =>
    latticeTorusCenter δ (y (primitiveInternalIdx n hn i))
  let fiber : Set (Fin (2 * n - 2) → T4) :=
    (fun q =>
      pairedCellAssignment κ δ
        (primitiveAssemble n hn z w q)) ⁻¹' {y}
  let box : Set (Fin (2 * n - 2) → T4) :=
    Set.univ.pi fun i => Metric.ball (c i) (R * δ)
  let lhs : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)|
  let K :=
    (ε⁻¹ ^ (dim : ℕ) * C) ^ n *
      ((12 + 32 * R ^ 2) * δ ^ 2 * D)
  let rhs : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal K * terminalSingularProduct z w (List.ofFn v)
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  have hfiberMeas : MeasurableSet fiber := by
    dsimp only [fiber, δ]
    exact
      (primitivePairedInternalCells n hn κ
        (compatibleMeshSize ε)
        (compatibleMeshSize_pos hε) z w).measurable_fiber y
  have hboxMeas : MeasurableSet box := by
    dsimp only [box]
    exact MeasurableSet.univ_pi fun _ =>
      measurableSet_ball
  have hterm : Measurable fun v : Fin (2 * n - 2) → T4 =>
      terminalSingularProduct z w (List.ofFn v) := by
    convert (measurable_terminalSingularProduct_ofFn
      (2 * n - 2) w).comp
        (measurable_const.prodMk measurable_id) using 1
    ext v
    rfl
  have hindicator :
      fiber.indicator lhs ≤ box.indicator rhs := by
    intro v
    by_cases hv : v ∈ fiber
    · rw [Set.indicator_of_mem hv]
      have hvfiber :
          pairedCellAssignment κ δ
              (primitiveAssemble n hn z w v) = y := by
        simpa only [fiber, Set.mem_preimage,
          Set.mem_singleton_iff] using hv
      by_cases hcov :
          primitiveCovarianceProduct ρ ε n κ
              (primitiveAssemble n hn z w v) = 0
      · have hz :
            primitiveInsertedIntegrand ρ ε n hn G κ
                (primitiveAssemble n hn z w v) = 0 := by
          unfold primitiveInsertedIntegrand primitiveIntegrand
          rw [hcov, mul_zero, mul_zero]
        simp only [lhs, hz, abs_zero, ENNReal.ofReal_zero, zero_le]
      · have hvbox : v ∈ box := by
          have hm :=
            primitiveInternal_mem_productCell_of_fiber_covariance_ne_zero
              ρ hε hε1 n hn κ hfull z w y v hvfiber hcov
          simpa only [box, c, R, δ] using hm
        rw [Set.indicator_of_mem hvbox]
        simpa only [lhs, rhs, K, R, δ, D] using
          hpointwise n hn G hG κ hfull hε hε1 hq
            z w y v hvfiber hcov
    · simp only [Set.indicator, hv, ↓reduceIte, zero_le]
  calc
    (∫⁻ v in fiber, lhs v ∂μ) =
        ∫⁻ v, fiber.indicator lhs v ∂μ := by
      rw [lintegral_indicator hfiberMeas]
    _ ≤ ∫⁻ v, box.indicator rhs v ∂μ :=
      lintegral_mono hindicator
    _ = ∫⁻ v in box, rhs v ∂μ :=
      lintegral_indicator hboxMeas rhs
    _ = ENNReal.ofReal K *
          ∫⁻ v in box,
            terminalSingularProduct z w (List.ofFn v) ∂μ := by
      dsimp only [rhs]
      rw [lintegral_const_mul (ENNReal.ofReal K) hterm]
    _ = ENNReal.ofReal K *
          terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
      congr 1
      exact terminalSingularProduct_setLIntegral_productCell
        (R * δ) z w (2 * n - 2) c


theorem r51_primitiveCopiedCellMaximumTerminalLIntegral_exhaustive_order :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) (q : ℕ) {ε : ℝ}
        (_hε : 0 < ε)
        (R : ℝ) (_hR : 0 < R)
        (y : Fin (2 * n) → Z4) (z w : T4),
        z ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
            (primitiveFirstCell n (by omega) y) →
        w ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
            (primitiveLastCell n (by omega) y) →
        let δ := compatibleMeshSize ε
        let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
        let W := periodicTerminalPathWeight δ
          (primitiveFirstCell n (by omega) y)
          (primitiveLastCell n (by omega) y)
          (primitiveInternalCellLabels n (by omega) y)
        ENNReal.ofReal
              ((12 + 32 * R ^ 2) * δ ^ 2 * D) *
            terminalCellLIntegral (R * δ) z w
              ((primitiveInternalCellLabels n (by omega) y).map
                (latticeTorusCenter δ)) ≤
          ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
            ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                δ ^ (4 * n - 4) * W) := by
  obtain ⟨C, hC, hcell⟩ :=
    primitiveTerminalCellLIntegral_exhaustive_order
  refine ⟨C, hC, ?_⟩
  intro n hn q ε hε R hR y z w hz hw
  let hn1 : 1 ≤ n := by omega
  let δ := compatibleMeshSize ε
  let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
  let W := periodicTerminalPathWeight δ
    (primitiveFirstCell n hn1 y)
    (primitiveLastCell n hn1 y)
    (primitiveInternalCellLabels n hn1 y)
  let F := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let A :=
    (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 6) * W
  let B :=
    (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 6) * W
  have hchain :=
    hcell n hn hε R hR y z w hz hw
  rw [primitiveUnwrappedTerminalWeight_eq_periodicCopied
    hε n hn1 y] at hchain
  change terminalCellLIntegral (R * δ) z w
      ((primitiveInternalCellLabels n hn1 y).map
        (latticeTorusCenter δ)) ≤
      ENNReal.ofReal A + ENNReal.ofReal B at hchain
  have hδ0 : 0 ≤ δ := (compatibleMeshSize_pos hε).le
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact zero_le_one.trans
      (one_le_r51PeriodicTupleDiameterBracketSq (by omega) _)
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact periodicTerminalPathWeight_nonneg _ _ _ _
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg
      (mul_nonneg
        (by positivity : 0 ≤ 12 + 32 * R ^ 2)
        (sq_nonneg δ))
      hD0
  have hfarBase : 0 ≤ C * (R ^ 2 + R ^ 4) :=
    mul_nonneg hC.le
      (add_nonneg (sq_nonneg R) (by positivity))
  have hnearBase : 0 ≤ C * cellChainRadiusFactor R :=
    mul_nonneg hC.le (cellChainRadiusFactor_pos R).le
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hfarBase _)
          (terminalRadiusFactor_pos hR).le)
        (pow_nonneg hδ0 _))
      hW0
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hnearBase _) (pow_nonneg hδ0 _))
      hW0
  have hFA :
      F * A =
        (12 + 32 * R ^ 2) * D *
          (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) * W := by
    dsimp only [F, A]
    rw [← compatibleCell_inserted_power_ledger δ n hn]
    ring
  have hFB :
      F * B =
        (12 + 32 * R ^ 2) * D *
          (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) * W := by
    dsimp only [F, B]
    rw [← compatibleCell_inserted_power_ledger δ n hn]
    ring
  calc
    ENNReal.ofReal F *
        terminalCellLIntegral (R * δ) z w
          ((primitiveInternalCellLabels n hn1 y).map
            (latticeTorusCenter δ)) ≤
        ENNReal.ofReal F *
          (ENNReal.ofReal A + ENNReal.ofReal B) := by
      simpa only [mul_comm] using
        mul_le_mul_right hchain (ENNReal.ofReal F)
    _ = ENNReal.ofReal (F * A) +
          ENNReal.ofReal (F * B) := by
      rw [mul_add, ENNReal.ofReal_mul hF0,
        ENNReal.ofReal_mul hF0]
    _ = _ := by rw [hFA, hFB]



theorem r51_primitiveInsertedIntegrand_copiedFiber_exhaustive_order
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ) →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4),
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
          let W := periodicTerminalPathWeight δ
            (primitiveFirstCell n (by omega) y)
            (primitiveLastCell n (by omega) y)
            (primitiveInternalCellLabels n (by omega) y)
          (∫⁻ v in
              (fun q =>
                pairedCellAssignment κ δ
                  (primitiveAssemble n (by omega) z w q)) ⁻¹' {y},
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
              (ENNReal.ofReal
                ((12 + 32 * R ^ 2) * D *
                  (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                  terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
               ENNReal.ofReal
                ((12 + 32 * R ^ 2) * D *
                  (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
                  δ ^ (4 * n - 4) * W)) := by
  obtain ⟨Ccov, hCcov, hfiberBound⟩ :=
    exists_r51_primitiveInsertedIntegrand_copiedFiber_lintegral_bound ρ
  obtain ⟨Ccell, hCcell, hcellBound⟩ :=
    r51_primitiveCopiedCellMaximumTerminalLIntegral_exhaustive_order
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 q instq hq z w y
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let hn1 : 1 ≤ n := by omega
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
  let W := periodicTerminalPathWeight δ
    (primitiveFirstCell n hn1 y)
    (primitiveLastCell n hn1 y)
    (primitiveInternalCellLabels n hn1 y)
  let c : Fin (2 * n - 2) → T4 := fun i =>
    latticeTorusCenter δ (y (primitiveInternalIdx n hn1 i))
  let fiber : Set (Fin (2 * n - 2) → T4) :=
    (fun q =>
      pairedCellAssignment κ δ
        (primitiveAssemble n hn1 z w q)) ⁻¹' {y}
  let f : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn1 G κ
        (primitiveAssemble n hn1 z w v)|
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let F := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let A :=
    (12 + 32 * R ^ 2) * D *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4) * W
  let B :=
    (12 + 32 * R ^ 2) * D *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4) * W
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact pow_nonneg
      (mul_nonneg
        (pow_nonneg (inv_nonneg.mpr hε.le) _)
        hCcov.le) _
  have hc :
      List.ofFn c =
        (primitiveInternalCellLabels n hn1 y).map
          (latticeTorusCenter δ) := by
    unfold c primitiveInternalCellLabels
    exact List.ofFn_comp' _ _
  have hpre :
      (∫⁻ v in fiber, f v ∂μ) ≤
        ENNReal.ofReal (Q * F) *
          terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
    simpa only [fiber, f, μ, Q, F, R, δ, D] using
      hfiberBound n hn1 G hG κ hfull hε hε1 hq z w y
  change (∫⁻ v in fiber, f v ∂μ) ≤
    ENNReal.ofReal Q *
      (ENNReal.ofReal A + ENNReal.ofReal B)
  by_cases hsupported :
      ∃ v, v ∈ fiber ∧
        primitiveCovarianceProduct ρ ε n κ
          (primitiveAssemble n hn1 z w v) ≠ 0
  · obtain ⟨v₀, hv₀, hcov₀⟩ := hsupported
    have hvfiber :
        pairedCellAssignment κ δ
            (primitiveAssemble n hn1 z w v₀) = y := by
      simpa only [fiber, Set.mem_preimage,
        Set.mem_singleton_iff] using hv₀
    have hmem :=
      primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
        ρ κ hfull hε hε1
          (primitiveAssemble n hn1 z w v₀) hcov₀
    rw [hvfiber] at hmem
    have hz :
        z ∈ latticeCellNeighborhood δ R
          (primitiveFirstCell n hn1 y) := by
      simpa only [primitiveFirstCell, primitiveAssemble_zero,
        δ, R] using hmem (⟨0, by omega⟩ : Fin (2 * n))
    have hw :
        w ∈ latticeCellNeighborhood δ R
          (primitiveLastCell n hn1 y) := by
      simpa only [primitiveLastCell, primitiveAssemble_last,
        δ, R] using hmem (primitiveLast n hn1)
    have hcell :=
      hcellBound n hn q hε R hR y z w hz hw
    change ENNReal.ofReal F *
        terminalCellLIntegral (R * δ) z w
          ((primitiveInternalCellLabels n hn1 y).map
            (latticeTorusCenter δ)) ≤
        ENNReal.ofReal A + ENNReal.ofReal B at hcell
    calc
      (∫⁻ v in fiber, f v ∂μ) ≤
          ENNReal.ofReal (Q * F) *
            terminalCellLIntegral (R * δ) z w (List.ofFn c) :=
        hpre
      _ = ENNReal.ofReal Q *
          (ENNReal.ofReal F *
            terminalCellLIntegral (R * δ) z w
              ((primitiveInternalCellLabels n hn1 y).map
                (latticeTorusCenter δ))) := by
        rw [ENNReal.ofReal_mul hQ0, hc]
        ring
      _ ≤ ENNReal.ofReal Q *
          (ENNReal.ofReal A + ENNReal.ofReal B) := by
        simpa only [mul_comm] using
          mul_le_mul_right hcell (ENNReal.ofReal Q)
  · have hfiberMeas : MeasurableSet fiber := by
      dsimp only [fiber, δ]
      exact
        (primitivePairedInternalCells n hn1 κ
          (compatibleMeshSize ε)
          (compatibleMeshSize_pos hε) z w).measurable_fiber y
    have hzero : (∫⁻ v in fiber, f v ∂μ) = 0 := by
      apply le_antisymm
      · calc
          (∫⁻ v in fiber, f v ∂μ) ≤
              ∫⁻ _v in fiber, 0 ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hfiberMeas] with v hv
            have hcov :
                primitiveCovarianceProduct ρ ε n κ
                    (primitiveAssemble n hn1 z w v) = 0 := by
              exact not_ne_iff.mp fun hne =>
                hsupported ⟨v, hv, hne⟩
            have hvalue :
                primitiveInsertedIntegrand ρ ε n hn1 G κ
                    (primitiveAssemble n hn1 z w v) = 0 := by
              unfold primitiveInsertedIntegrand primitiveIntegrand
              rw [hcov, mul_zero, mul_zero]
            simp only [f, hvalue, abs_zero, ENNReal.ofReal_zero]
            exact le_rfl
          _ = 0 := by simp
      · exact bot_le
    rw [hzero]
    exact bot_le

theorem r51PeriodicReductionWeight_eq_terminal
    (q : ℕ) (δ : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    r51PeriodicReductionWeight q (by omega) δ y =
      r51PeriodicTupleDiameterBracketSq q (by omega) y *
        periodicTerminalPathWeight δ
          (primitiveFirstCell n hn y)
          (primitiveLastCell n hn y)
          (primitiveInternalCellLabels n hn y) := by
  unfold r51PeriodicReductionWeight r51PeriodicWordChainWeight
  congr 1
  rw [adjacentProduct_eq_listChainProduct,
    ← primitiveOriginalCellList_eq_ofFn]
  exact listChainProduct_periodic_eq_terminal _ _ _ _


theorem r51_primitiveInsertedIntegrand_lintegral_le_periodicCopiedSum_filter
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ) →
        ∀ (z w : T4)
          (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
          [DecidablePred P],
          (∀ y ∈ primitiveCanonicalCellCarrier ε n κ,
            ¬P (primitiveCopiedReductionTuple n (by omega) y) →
              primitiveCopiedFiberContribution ρ ε n (by omega)
                G κ z w y = 0) →
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ∑ u ∈
                ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
                    ((2 * n - 1) + 1)).filter
                  (RespectsPairing
                    (primitiveReductionPairing n (by omega) κ))).filter P,
              ENNReal.ofReal
                  ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
                (ENNReal.ofReal
                    (farCoeff *
                      r51PeriodicReductionWeight q (by omega) δ
                        (primitiveCopiedSourceTuple n (by omega) u)) +
                 ENNReal.ofReal
                    (nearCoeff *
                      r51PeriodicReductionWeight q (by omega) δ
                        (primitiveCopiedSourceTuple n (by omega) u))) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hfiber⟩ :=
    r51_primitiveInsertedIntegrand_copiedFiber_exhaustive_order ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 q instq hq z w P instP hvanish
  let hn1 : 1 ≤ n := by omega
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let farCoeff :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let carrier :=
    ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
        ((2 * n - 1) + 1)).filter
      (RespectsPairing
        (primitiveReductionPairing n hn1 κ))).filter P
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let cellBound :
      (Fin ((2 * n - 1) + 1) → Z4) → ENNReal := fun u =>
    ENNReal.ofReal Q *
      (ENNReal.ofReal
          (farCoeff *
            r51PeriodicReductionWeight q (by omega) δ
              (primitiveCopiedSourceTuple n hn1 u)) +
       ENNReal.ofReal
          (nearCoeff *
            r51PeriodicReductionWeight q (by omega) δ
              (primitiveCopiedSourceTuple n hn1 u)))
  have hdecomp :=
    primitiveInsertedIntegrand_lintegral_eq_boundedPairing_filter
      ρ hε n hn1 G κ z w P hvanish
  change
    (∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn1 G κ
            (primitiveAssemble n hn1 z w v)|
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) =
      ∑ u ∈ carrier,
        primitiveCopiedFiberContribution ρ ε n hn1 G κ z w
          (primitiveCopiedSourceTuple n hn1 u) at hdecomp
  change
    (∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn1 G κ
            (primitiveAssemble n hn1 z w v)|
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
      ∑ u ∈ carrier, cellBound u
  rw [hdecomp]
  apply Finset.sum_le_sum
  intro u hu
  let y := primitiveCopiedSourceTuple n hn1 u
  let D := r51PeriodicTupleDiameterBracketSq q (by omega) y
  let W := periodicTerminalPathWeight δ
    (primitiveFirstCell n hn1 y)
    (primitiveLastCell n hn1 y)
    (primitiveInternalCellLabels n hn1 y)
  have hcell :=
    hfiber n hn G hG κ hκ hε hε1 hq z w y
  have hperiodic :
      r51PeriodicReductionWeight q (by omega) δ
          (primitiveCopiedSourceTuple n hn1 u) = D * W := by
    simpa only [D, W, y] using
      r51PeriodicReductionWeight_eq_terminal q δ n hn1 y
  have hfar :
      (12 + 32 * R ^ 2) * D *
          (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) * W =
        farCoeff *
          r51PeriodicReductionWeight q (by omega) δ
              (primitiveCopiedSourceTuple n hn1 u) := by
    rw [hperiodic]
    dsimp only [farCoeff]
    ring
  have hnear :
      (12 + 32 * R ^ 2) * D *
          (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) * W =
        nearCoeff *
          r51PeriodicReductionWeight q (by omega) δ
              (primitiveCopiedSourceTuple n hn1 u) := by
    rw [hperiodic]
    dsimp only [nearCoeff]
    ring
  simpa only [primitiveCopiedFiberContribution, cellBound,
    Q, R, δ, D, W, y, hfar, hnear] using hcell


theorem r51_primitiveInsertedIntegrand_lintegral_le_periodicEndpointSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ) →
        ∀ (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ∑ u ∈
                ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
                    ((2 * n - 1) + 1)).filter
                  (RespectsPairing
                    (primitiveReductionPairing n (by omega) κ))).filter
                      (primitiveCopiedEndpointSupported
                        ρ ε n (by omega) z w),
              ENNReal.ofReal
                  ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
                (ENNReal.ofReal
                    (farCoeff *
                      r51PeriodicReductionWeight q (by omega) δ
                        (primitiveCopiedSourceTuple n (by omega) u)) +
                 ENNReal.ofReal
                    (nearCoeff *
                      r51PeriodicReductionWeight q (by omega) δ
                        (primitiveCopiedSourceTuple n (by omega) u))) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hsum⟩ :=
    r51_primitiveInsertedIntegrand_lintegral_le_periodicCopiedSum_filter ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 q instq hq z w
  let hn1 : 1 ≤ n := by omega
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  apply hsum n hn G hG κ hκ hε hε1 hq z w
    (primitiveCopiedEndpointSupported ρ ε n hn1 z w)
  intro y hy hunsupported
  apply
    primitiveCopiedFiberContribution_eq_zero_of_not_endpointSupported
      ρ hε hε1 n hn1 G κ hfull z w y
  exact fun hsupported =>
    hunsupported
      (primitiveCopiedEndpointSupported_reductionTuple
        ρ ε n hn1 z w y |>.2 hsupported)

/-! ## Filtered periodic statistic and the P-5.10 interface -/

def r51PeriodicReductionFilteredRealSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (δ : ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] : ℝ :=
  ∑ u ∈
      ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
          ((2 * n - 1) + 1)).filter
        (RespectsPairing
          (primitiveReductionPairing n hn κ))).filter P,
    r51PeriodicReductionWeight q (by omega) δ
      (primitiveCopiedSourceTuple n hn u)

def r51PeriodicReductionFilteredSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (δ : ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] : ENNReal :=
  ∑ u ∈
      ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
          ((2 * n - 1) + 1)).filter
        (RespectsPairing
          (primitiveReductionPairing n hn κ))).filter P,
    ENNReal.ofReal
      (r51PeriodicReductionWeight q (by omega) δ
        (primitiveCopiedSourceTuple n hn u))

theorem r51PeriodicReductionFilteredSum_eq_ofReal
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    r51PeriodicReductionFilteredSum ε n hn q δ κ P =
      ENNReal.ofReal
        (r51PeriodicReductionFilteredRealSum
          ε n hn q δ κ P) := by
  unfold r51PeriodicReductionFilteredSum
    r51PeriodicReductionFilteredRealSum
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro u hu
  exact (r51PeriodicReductionWeight_pos (by omega) hδ _).le

theorem r51PeriodicReductionFilteredRealSum_eq_copied
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (δ : ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    r51PeriodicReductionFilteredRealSum ε n hn q δ κ P =
      ∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
          (fun y => P (primitiveCopiedReductionTuple n hn y)),
        r51PeriodicReductionWeight q (by omega) δ y := by
  symm
  unfold r51PeriodicReductionFilteredRealSum
  simpa only [primitiveCopiedSourceTuple_reductionTuple] using
    sum_copiedLabels_filter_eq_boundedPairing_filter
      hε n hn κ P
        (fun u =>
          r51PeriodicReductionWeight q (by omega) δ
            (primitiveCopiedSourceTuple n hn u))

theorem r51PeriodicReductionFilteredRealSum_le_full
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    r51PeriodicReductionFilteredRealSum ε n hn q δ κ P ≤
      ∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
        r51PeriodicReductionWeight q (by omega) δ y := by
  rw [r51PeriodicReductionFilteredRealSum_eq_copied
    hε n hn q δ κ P]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
  intro y hy hnot
  exact (r51PeriodicReductionWeight_pos (by omega) hδ y).le

theorem r51PeriodicReductionFilteredSum_le_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) {n q : ℕ} (hn : 1 ≤ n)
    (hq : (q : ℤ) = compatibleCellCount ε) [NeZero q]
    {κ : PartialPairing (Fin (2 * n))}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    r51PeriodicReductionFilteredSum ε n hn q
        (compatibleMeshSize ε) κ P ≤
      ENNReal.ofReal
        (Real.exp (12 * (2 * n - 1)) *
          (((3 ^ 4) ^ (2 * n) : ℕ) *
            primitiveAcrossLatticeSum (2 * q) (2 * n - 1)
              (pairingLowerHalf
                (primitiveReductionPairing n hn κ)))) := by
  rw [r51PeriodicReductionFilteredSum_eq_ofReal
    ε n hn q (compatibleMeshSize_pos hε) κ P]
  apply ENNReal.ofReal_le_ofReal
  exact
    (r51PeriodicReductionFilteredRealSum_le_full
      hε n hn q (compatibleMeshSize ε)
        (compatibleMeshSize_pos hε) κ P).trans
      (r51_periodic_cell_sum_le_primitiveAcross
        hε hn hq hfull hprimitive)

theorem r51PeriodicReductionFilteredSum_factor
    {a b Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (δ : ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    (∑ u ∈
        ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
            ((2 * n - 1) + 1)).filter
          (RespectsPairing
            (primitiveReductionPairing n hn κ))).filter P,
        ENNReal.ofReal Q *
          (ENNReal.ofReal
              (a * r51PeriodicReductionWeight q (by omega) δ
                (primitiveCopiedSourceTuple n hn u)) +
           ENNReal.ofReal
              (b * r51PeriodicReductionWeight q (by omega) δ
                (primitiveCopiedSourceTuple n hn u)))) =
      ENNReal.ofReal Q *
        (ENNReal.ofReal a + ENNReal.ofReal b) *
          r51PeriodicReductionFilteredSum ε n hn q δ κ P := by
  unfold r51PeriodicReductionFilteredSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [mul_add, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  ring

/-- Terminal R-51 reduction for an explicit positive natural period count.
The finite cut average and its uniform `3^(8n)` fiber loss are absorbed into
the displayed `latticeBound`; both analytic contributions retain the paper's
critical factor `δ^(4n-4)`. -/
theorem primitiveInsertedIntegrand_lintegral_le_periodicCutLatticeSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          (q : ℤ) = compatibleCellCount ε →
        ∀ (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
          let latticeBound :=
            Real.exp (12 * (2 * n - 1)) *
              (((3 ^ 4) ^ (2 * n) : ℕ) *
                primitiveAcrossLatticeSum (2 * q) (2 * n - 1)
                  (pairingLowerHalf
                    (primitiveReductionPairing n (by omega) κ)))
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal Q *
              (ENNReal.ofReal farCoeff +
                ENNReal.ofReal nearCoeff) *
              ENNReal.ofReal latticeBound := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hendpoint⟩ :=
    r51_primitiveInsertedIntegrand_lintegral_le_periodicEndpointSum ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 q instq hq z w
  let hn1 : 1 ≤ n := by omega
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let farCoeff :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let P :=
    primitiveCopiedEndpointSupported ρ ε n hn1 z w
  let latticeBound :=
    Real.exp (12 * (2 * n - 1)) *
      (((3 ^ 4) ^ (2 * n) : ℕ) *
        primitiveAcrossLatticeSum (2 * q) (2 * n - 1)
          (pairingLowerHalf
            (primitiveReductionPairing n hn1 κ)))
  have hmesh :
      PeriodCompatibleMesh (compatibleMeshSize ε) (q : ℤ) := by
    rw [hq]
    exact compatibleMesh_isPeriodCompatible hε
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp hκ
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hδ : 0 < δ := by
    exact compatibleMeshSize_pos hε
  have hfar : 0 ≤ farCoeff := by
    dsimp only [farCoeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (by positivity)
          (pow_nonneg
            (mul_nonneg hCcell.le
              (add_nonneg (sq_nonneg R)
                (pow_nonneg hR.le 4))) _))
        (terminalRadiusFactor_pos hR).le)
      (pow_nonneg hδ.le _)
  have hnear : 0 ≤ nearCoeff := by
    dsimp only [nearCoeff]
    exact mul_nonneg
      (mul_nonneg
        (by positivity)
        (pow_nonneg
          (mul_nonneg hCcell.le
            (cellChainRadiusFactor_pos R).le) _))
      (pow_nonneg hδ.le _)
  have hraw :=
    hendpoint n hn G hG κ hκ hε hε1 hmesh z w
  have hfactor :=
    r51PeriodicReductionFilteredSum_factor
      (Q := Q) hfar hnear ε n hn1 q δ κ P
  have hstat :
      r51PeriodicReductionFilteredSum ε n hn1 q δ κ P ≤
        ENNReal.ofReal latticeBound := by
    simpa only [δ, latticeBound, hn1] using
      r51PeriodicReductionFilteredSum_le_primitiveAcross
        hε hn1 hq hfull hprimitive P
  calc
    (∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn1 G κ
            (primitiveAssemble n hn1 z w v)|
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
        ∑ u ∈
            ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
                ((2 * n - 1) + 1)).filter
              (RespectsPairing
                (primitiveReductionPairing n hn1 κ))).filter P,
          ENNReal.ofReal Q *
            (ENNReal.ofReal
                (farCoeff *
                  r51PeriodicReductionWeight q (by omega) δ
                    (primitiveCopiedSourceTuple n hn1 u)) +
             ENNReal.ofReal
                (nearCoeff *
                  r51PeriodicReductionWeight q (by omega) δ
                    (primitiveCopiedSourceTuple n hn1 u))) := by
      simpa only [R, δ, farCoeff, nearCoeff, Q, P, hn1] using hraw
    _ = ENNReal.ofReal Q *
          (ENNReal.ofReal farCoeff + ENNReal.ofReal nearCoeff) *
            r51PeriodicReductionFilteredSum ε n hn1 q δ κ P := hfactor
    _ ≤ ENNReal.ofReal Q *
          (ENNReal.ofReal farCoeff + ENNReal.ofReal nearCoeff) *
            ENNReal.ofReal latticeBound := by
      exact mul_le_mul_right hstat _

/-- Canonical specialization of the terminal R-51 reduction.  It chooses
the natural-valued representative of `compatibleCellCount ε`, so callers do
not need to provide the period count or its positivity instance. -/
theorem primitiveInsertedIntegrand_lintegral_le_compatiblePeriodicCutLatticeSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4),
          let q := (compatibleCellCount ε).toNat
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
          let latticeBound :=
            Real.exp (12 * (2 * n - 1)) *
              (((3 ^ 4) ^ (2 * n) : ℕ) *
                primitiveAcrossLatticeSum (2 * q) (2 * n - 1)
                  (pairingLowerHalf
                    (primitiveReductionPairing n (by omega) κ)))
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal Q *
              (ENNReal.ofReal farCoeff +
                ENNReal.ofReal nearCoeff) *
              ENNReal.ofReal latticeBound := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hmain⟩ :=
    primitiveInsertedIntegrand_lintegral_le_periodicCutLatticeSum ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w
  let q := (compatibleCellCount ε).toNat
  have hqcast : (q : ℤ) = compatibleCellCount ε := by
    dsimp only [q]
    exact Int.toNat_of_nonneg
      (compatibleCellCount_pos hε).le
  have hqpos : 0 < q := by
    have hqposZ : (0 : ℤ) < (q : ℤ) := by
      rw [hqcast]
      exact compatibleCellCount_pos hε
    exact_mod_cast hqposZ
  letI : NeZero q := ⟨ne_of_gt hqpos⟩
  exact hmain n hn G hG κ hκ hε hε1 hqcast z w

end

end Anderson4D
