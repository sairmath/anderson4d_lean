import Mathlib

/-!
# Parent maps extracted from finite connected graphs

The Hepp-tree volume argument repeatedly chooses a link tree on the children
of a branch.  For counting, it is enough to orient one shortest-path edge
from every non-root vertex toward a fixed root.  The resulting parent map
strictly lowers graph distance, so the vertices can be exposed in increasing
distance order.  We keep the parent map inside the full function space
`α → α`; summing over that larger space factorizes coordinatewise.
-/

namespace Anderson4D

open scoped BigOperators

namespace SimpleGraph

variable {α : Type*} (G : SimpleGraph α)

/-- A chosen shortest walk from `v` to `root` in a connected graph. -/
noncomputable def shortestWalkToRoot
    (hG : G.Connected) (root v : α) : G.Walk v root :=
  Classical.choose (hG.exists_walk_length_eq_dist v root)

@[simp]
theorem shortestWalkToRoot_length
    (hG : G.Connected) (root v : α) :
    (shortestWalkToRoot G hG root v).length = G.dist v root :=
  Classical.choose_spec (hG.exists_walk_length_eq_dist v root)

/-- The canonical parent of `root` is itself; every other vertex points to
the second vertex of a chosen shortest walk to `root`. -/
noncomputable def parentTowardRoot
    [DecidableEq α] (hG : G.Connected) (root : α) (v : α) : α :=
  if v = root then root else (shortestWalkToRoot G hG root v).snd

@[simp]
theorem parentTowardRoot_root
    [DecidableEq α] (hG : G.Connected) (root : α) :
    parentTowardRoot G hG root root = root := by
  simp [parentTowardRoot]

/-- Every non-root parent edge is an edge of the original graph. -/
theorem adj_parentTowardRoot
    [DecidableEq α] (hG : G.Connected) (root : α)
    {v : α} (hv : v ≠ root) :
    G.Adj v (parentTowardRoot G hG root v) := by
  rw [parentTowardRoot, if_neg hv]
  exact (shortestWalkToRoot G hG root v).adj_snd
    ((shortestWalkToRoot G hG root v).not_nil_of_ne hv)

/-- Following the chosen parent strictly decreases distance to the root. -/
theorem dist_parentTowardRoot_lt
    [DecidableEq α] (hG : G.Connected) (root : α)
    {v : α} (hv : v ≠ root) :
    G.dist (parentTowardRoot G hG root v) root < G.dist v root := by
  let p := shortestWalkToRoot G hG root v
  have hp : ¬p.Nil := p.not_nil_of_ne hv
  have hdist :
      G.dist p.snd root ≤ p.tail.length :=
    G.dist_le p.tail
  have hlen : p.tail.length + 1 = G.dist v root := by
    calc
      p.tail.length + 1 = p.length := p.length_tail_add_one hp
      _ = G.dist v root := shortestWalkToRoot_length G hG root v
  dsimp [p] at hdist hlen
  rw [parentTowardRoot, if_neg hv]
  omega

/-- In particular, a parent chain cannot cycle away from the root. -/
theorem parentTowardRoot_ne_self
    [DecidableEq α] (hG : G.Connected) (root : α)
    {v : α} (hv : v ≠ root) :
    parentTowardRoot G hG root v ≠ v := by
  intro h
  have hlt := dist_parentTowardRoot_lt G hG root hv
  rw [h] at hlt
  exact (Nat.lt_irrefl _ hlt)

end SimpleGraph

/-! ## Coordinatewise sum over the enlarged parent-map space -/

section ParentWeights

variable {α R : Type*} [Fintype α] [DecidableEq α] [CommSemiring R]

/-- Weight of a full parent map.  The root coordinate contributes `1`;
at a non-root vertex `v`, the factor separates into the weight of its
chosen parent and a vertex-local child weight. -/
def fullParentWeight (root : α) (parentWeight childWeight : α → R)
    (p : α → α) : R :=
  ∏ v, if v = root then
      (if p v = root then 1 else 0)
    else parentWeight (p v) * childWeight v

/-- Exact factorization of the sum over all full parent maps. -/
theorem sum_fullParentWeight
    (root : α) (parentWeight childWeight : α → R) :
    ∑ p : α → α, fullParentWeight root parentWeight childWeight p =
      ∏ v, if v = root then 1
        else (∑ u, parentWeight u) * childWeight v := by
  unfold fullParentWeight
  let f : α → α → R := fun v u =>
    if v = root then (if u = root then 1 else 0)
    else parentWeight u * childWeight v
  calc
    (∑ p : α → α,
        ∏ v, if v = root then
            (if p v = root then 1 else 0)
          else parentWeight (p v) * childWeight v)
        = ∑ p : α → α, ∏ v, f v (p v) := rfl
    _ = ∏ v, ∑ u, f v u := (Fintype.prod_sum f).symm
    _ = ∏ v, if v = root then 1
          else (∑ u, parentWeight u) * childWeight v := by
      apply Fintype.prod_congr
      intro v
      by_cases hv : v = root
      · subst v
        simp [f]
      · simp [f, hv, Finset.sum_mul]

/-- Natural-valued restriction to any finite family of parent maps. -/
theorem sum_fullParentWeight_subset_nat
    [DecidableEq (α → α)]
    (root : α) (parentWeight childWeight : α → ℕ)
    (P : Finset (α → α)) :
    ∑ p ∈ P, fullParentWeight root parentWeight childWeight p ≤
      ∏ v, if v = root then 1
        else (∑ u, parentWeight u) * childWeight v := by
  calc
    ∑ p ∈ P, fullParentWeight root parentWeight childWeight p
        ≤ ∑ p : α → α,
            fullParentWeight root parentWeight childWeight p :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ P) (fun _ _ _ => Nat.zero_le _)
    _ = _ := sum_fullParentWeight root parentWeight childWeight

end ParentWeights

end Anderson4D
