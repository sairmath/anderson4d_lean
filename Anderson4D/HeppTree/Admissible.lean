import Anderson4D.HeppTree.Basic
import Anderson4D.PermSum.Local

/-!
# Admissible embeddings of marked Hepp trees (nodes D-adm, L-5.5)

Paper Def 5.4 and Lemma 5.5 of arXiv:2607.10105, in the simple case
(multiplicities deferred).

* `lcaPath`, `lcaV` — least common ancestor of two vertices, via the longest
  common prefix of position paths.
* `scaleN` — the dyadic scale `N_v = 2 ^ Nm.Nexp v` of a vertex under a
  marking (junk off branch nodes, where `Nexp` is unconstrained).
* `leavesUnder`, `childrenOf` — the leaves of the subtree at a vertex, and the
  children of a vertex, as `Finset`s of position-prefix conditions.
* `IsAdmissible` — Def 5.4: injective, leaf-pair separation
  `N_{l ∨ l'} / 2 ≤ |z l − z l'|`, values bounded by `M`, and the children of
  every branch node connected by chains of links; the chain condition
  (Def 5.4(b)) is `Relation.ReflTransGen` of the one-link relation `IsLink`.
* `Realizes` — a marked tree realizes a finite set `Z` if some admissible
  embedding has image exactly `Z`.
* `exists_star_realizes` — Lemma 5.5 in the single-scale case (stage 2'): a
  nonempty bounded set whose pairwise distances lie in the dyadic window
  `[2^N/2, 2^N]` is realized by a star tree with constant marking `N` (or by
  the bare leaf when it is a singleton).
-/

namespace Anderson4D

open PlaneTree

/-! ## Longest common prefix and least common ancestors -/

/-- Longest common prefix of two position paths: the position of the least
common ancestor of the two vertices. -/
def lcaPath : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs => if a = b then a :: lcaPath as bs else []

@[simp] theorem lcaPath_self (p : List ℕ) : lcaPath p p = p := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [lcaPath, ih]

theorem lcaPath_comm (p q : List ℕ) : lcaPath p q = lcaPath q p := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a as ih =>
    cases q with
    | nil => rfl
    | cons b bs =>
      by_cases h : a = b
      · subst h; simp [lcaPath, ih]
      · have h' : ¬b = a := fun hba => h hba.symm
        simp [lcaPath, h, h']

/-- The longest common prefix is a prefix of the first argument. -/
theorem lcaPath_prefix_left (p q : List ℕ) : lcaPath p q <+: p := by
  induction p generalizing q with
  | nil => simp [lcaPath]
  | cons a as ih =>
    cases q with
    | nil => simp [lcaPath]
    | cons b bs =>
      by_cases h : a = b
      · subst h
        simp only [lcaPath]
        exact List.cons_prefix_cons.mpr ⟨rfl, ih bs⟩
      · simp only [lcaPath, if_neg h]
        exact List.nil_prefix

/-- The longest common prefix is a prefix of the second argument. -/
theorem lcaPath_prefix_right (p q : List ℕ) : lcaPath p q <+: q := by
  rw [lcaPath_comm]; exact lcaPath_prefix_left q p

/-- Position validity descends to prefixes: a prefix of a valid position is a
valid position (it is an iterated `dropLast`). -/
theorem IsPos_of_prefix {t : PlaneTree} {p q : Pos} (hp : IsPos t p) (hq : q <+: p) :
    IsPos t q := by
  induction q generalizing p t with
  | nil => exact isPos_nil t
  | cons i q ih =>
    obtain ⟨cs⟩ := t
    cases p with
    | nil => exact absurd (List.prefix_nil.mp hq) (List.cons_ne_nil i q)
    | cons j p =>
      obtain ⟨rfl, hq'⟩ := List.cons_prefix_cons.mp hq
      obtain ⟨hlt, hp'⟩ := isPos_cons_iff.mp hp
      exact isPos_cons_iff.mpr ⟨hlt, ih hp' hq'⟩

/-- The least common ancestor of two vertices (longest common prefix of their
position paths). -/
def lcaV {t : PlaneTree} (v w : VPos t) : VPos t :=
  ⟨lcaPath v.1 w.1, IsPos_of_prefix v.2 (lcaPath_prefix_left v.1 w.1)⟩

theorem lcaV_comm {t : PlaneTree} (v w : VPos t) : lcaV v w = lcaV w v :=
  Subtype.ext (lcaPath_comm v.1 w.1)

@[simp] theorem lcaV_self {t : PlaneTree} (v : VPos t) : lcaV v v = v :=
  Subtype.ext (lcaPath_self v.1)

/-! ## Scales, subtree leaves, children -/

/-- The dyadic scale `N_v = 2 ^ Nm.Nexp v` of a vertex under a marking.  Off
the branch nodes `Nm.Nexp` is unconstrained junk, and so is `scaleN`; all
statements below only inspect it at branch nodes (or under a constant
marking). -/
def scaleN {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) : ℕ := 2 ^ Nm.Nexp v

theorem scaleN_pos {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) :
    0 < scaleN Nm v := Nat.two_pow_pos _

/-- The leaves of the subtree rooted at `v`: leaves whose position extends
`v`'s. -/
def leavesUnder {t : PlaneTree} (v : VPos t) : Finset {w // w ∈ Leaves t} :=
  Finset.univ.filter fun l => v.1 <+: l.1.1

@[simp] theorem mem_leavesUnder {t : PlaneTree} {v : VPos t} {l : {w // w ∈ Leaves t}} :
    l ∈ leavesUnder v ↔ v.1 <+: l.1.1 := by
  simp [leavesUnder]

/-- A leaf belongs to the leaves under itself. -/
theorem self_mem_leavesUnder {t : PlaneTree} (v : VPos t) (hv : v ∈ Leaves t) :
    (⟨v, hv⟩ : {w // w ∈ Leaves t}) ∈ leavesUnder v :=
  mem_leavesUnder.mpr List.prefix_rfl

/-- The children of a vertex: valid positions extending `v`'s by one step. -/
def childrenOf {t : PlaneTree} (v : VPos t) : Finset (VPos t) :=
  Finset.univ.filter fun w => w.1.length = v.1.length + 1 ∧ v.1 <+: w.1

@[simp] theorem mem_childrenOf {t : PlaneTree} {v w : VPos t} :
    w ∈ childrenOf v ↔ w.1.length = v.1.length + 1 ∧ v.1 <+: w.1 := by
  simp [childrenOf]

/-! ## Admissible embeddings (paper Def 5.4, simple case) -/

/-- One link at scale `N_v` (Def 5.4(b)): the subtrees at `c` and `c'` contain
leaves whose embedded points are at distance at most `N_v`. -/
def IsLink {t : PlaneTree} (Nm : HeppMarking t) (z : {v // v ∈ Leaves t} → Fin 4 → ℤ)
    (v c c' : VPos t) : Prop :=
  ∃ l ∈ leavesUnder c, ∃ l' ∈ leavesUnder c', znorm (z l - z l') ≤ (scaleN Nm v : ℝ)

/-- Def 5.4(b): any two children of `v` are joined by a chain of links between
children of `v` — the reflexive-transitive closure of the one-link relation,
restricted to `childrenOf v`. -/
def LinkedChildren {t : PlaneTree} (Nm : HeppMarking t)
    (z : {v // v ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t) : Prop :=
  ∀ c ∈ childrenOf v, ∀ c' ∈ childrenOf v,
    Relation.ReflTransGen
      (fun a b => a ∈ childrenOf v ∧ b ∈ childrenOf v ∧ IsLink Nm z v a b) c c'

/-- Paper Def 5.4 (simple case, multiplicities deferred): an admissible
embedding of the leaves of a marked Hepp tree into `ℤ⁴`.  `(a)`: distinct
leaves are separated by half the scale of their least common ancestor;
`(b)`: the children of every branch node are chained by links at its scale;
all values lie in the box `[-M, M]⁴`. -/
structure IsAdmissible {t : PlaneTree} (Nm : HeppMarking t) (M : ℕ)
    (z : {v // v ∈ Leaves t} → Fin 4 → ℤ) : Prop where
  /-- The embedding is injective. -/
  inj : Function.Injective z
  /-- Def 5.4(a): separation by the scale of the least common ancestor. -/
  sep : ∀ l l', l ≠ l' → (scaleN Nm (lcaV l.1 l'.1) : ℝ) / 2 ≤ znorm (z l - z l')
  /-- All coordinates lie in `[-M, M]`. -/
  bounded : ∀ l i, |z l i| ≤ (M : ℤ)
  /-- Def 5.4(b): links connect the children of every branch node. -/
  linked : ∀ v ∈ BranchNodes t, LinkedChildren Nm z v

/-- A marked Hepp tree realizes the finite set `Z ⊆ ℤ⁴` (with box bound `M`)
if some admissible embedding of its leaves has image exactly `Z`. -/
def Realizes {t : PlaneTree} (Nm : HeppMarking t) (M : ℕ) (Z : Finset (Fin 4 → ℤ)) : Prop :=
  ∃ z : {v // v ∈ Leaves t} → Fin 4 → ℤ,
    IsAdmissible Nm M z ∧ Finset.univ.image z = Z

/-! ## Star trees (single-scale case of Lemma 5.5) -/

/-- The star tree: a root with `n` leaf children. -/
def starTree (n : ℕ) : PlaneTree := node (List.replicate n leaf)

/-- The only valid position in the bare leaf is the root. -/
theorem isPos_leaf_iff {p : Pos} : IsPos leaf p ↔ p = [] := by
  cases p with
  | nil => exact ⟨fun _ => rfl, fun _ => isPos_nil _⟩
  | cons i q =>
    show IsPos (node []) (i :: q) ↔ _
    rw [isPos_cons_iff]
    exact ⟨fun ⟨h, _⟩ => absurd h (by simp), fun h => absurd h (by simp)⟩

/-- Every vertex of the bare leaf is the root. -/
theorem vpos_leaf_eq (v : VPos leaf) : v = rootV leaf :=
  Subtype.ext (isPos_leaf_iff.mp v.2)

/-- The valid positions of the star tree: the root and the `n` leaves. -/
theorem isPos_starTree_iff {n : ℕ} {p : Pos} :
    IsPos (starTree n) p ↔ p = [] ∨ ∃ i < n, p = [i] := by
  cases p with
  | nil => simp [isPos_nil]
  | cons i q =>
    show IsPos (node (List.replicate n leaf)) (i :: q) ↔ _
    rw [isPos_cons_iff]
    simp only [List.length_replicate, List.getElem_replicate, isPos_leaf_iff,
      exists_prop, reduceCtorEq, false_or]
    constructor
    · rintro ⟨hi, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨j, hj, hp⟩
      injection hp with h1 h2
      exact ⟨h1 ▸ hj, h2⟩

/-- The root of the star tree has `n` children. -/
theorem childCount_starTree_nil (n : ℕ) : childCount (starTree n) [] = n := by
  simp [starTree, childCount]

/-- The depth-one vertices of the star tree are childless. -/
theorem childCount_starTree_leaf {n i : ℕ} :
    childCount (starTree n) [i] = 0 := by
  simp [starTree, childCount, leaf]

/-- Companion: a forest of leaves is Hepp-valid. -/
theorem isValidList_replicate_leaf (m : ℕ) :
    isValidList (List.replicate m leaf) = true := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, isValidList, ih]; rfl

/-- The star tree with `n ≠ 1` children is Hepp-valid (no unary vertices). -/
theorem starTree_isValid {n : ℕ} (hn : n ≠ 1) : (starTree n).isValid = true := by
  rw [starTree, isValid, isValidList_replicate_leaf]
  simp [hn]

/-- Companion: a forest of `m` leaves has `m` leaves. -/
theorem leafCountList_replicate_leaf (m : ℕ) :
    leafCountList (List.replicate m leaf) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, leafCountList, ih]
    have h1 : leafCount leaf = 1 := rfl
    omega

/-- The star tree has `n` leaves (as counted by `leafCount`). -/
theorem leafCount_starTree {n : ℕ} (hn : 1 ≤ n) : (starTree n).leafCount = n := by
  rw [starTree, leafCount, leafCountList_replicate_leaf]
  omega

@[simp] theorem mem_Leaves_iff {t : PlaneTree} {v : VPos t} :
    v ∈ Leaves t ↔ childCount t v.1 = 0 := by simp [Leaves]

@[simp] theorem mem_BranchNodes_iff {t : PlaneTree} {v : VPos t} :
    v ∈ BranchNodes t ↔ 2 ≤ childCount t v.1 := by simp [BranchNodes]

theorem root_mem_leaves_leaf : rootV leaf ∈ Leaves leaf := mem_Leaves_iff.mpr rfl

/-- The bare leaf has no branch nodes. -/
theorem branchNodes_leaf : BranchNodes leaf = ∅ := by decide

/-- The `i`-th leaf vertex of the star tree. -/
def starLeafV (n : ℕ) (i : Fin n) : VPos (starTree n) :=
  ⟨[i.1], isPos_starTree_iff.mpr (Or.inr ⟨i.1, i.2, rfl⟩)⟩

theorem starLeafV_injective (n : ℕ) : Function.Injective (starLeafV n) := by
  intro i j h
  have h' : [i.1] = [j.1] := congrArg Subtype.val h
  injection h' with h1 _
  exact Fin.ext h1

/-- The leaves of the star tree are exactly its depth-one vertices. -/
theorem leaves_starTree {n : ℕ} (hn : 2 ≤ n) :
    Leaves (starTree n) = Finset.univ.image (starLeafV n) := by
  ext v
  simp only [mem_Leaves_iff, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hv
    rcases isPos_starTree_iff.mp v.2 with h | ⟨i, hi, hp⟩
    · rw [h, childCount_starTree_nil] at hv; omega
    · exact ⟨⟨i, hi⟩, Subtype.ext hp.symm⟩
  · rintro ⟨i, rfl⟩
    exact childCount_starTree_leaf

theorem card_leaves_starTree {n : ℕ} (hn : 2 ≤ n) :
    (Leaves (starTree n)).card = n := by
  rw [leaves_starTree hn, Finset.card_image_of_injective _ (starLeafV_injective n),
    Finset.card_univ, Fintype.card_fin]

/-- Every branch node of the star tree is the root. -/
theorem branch_star_eq_root {n : ℕ} {v : VPos (starTree n)}
    (hv : v ∈ BranchNodes (starTree n)) : v = rootV (starTree n) := by
  rcases isPos_starTree_iff.mp v.2 with h | ⟨i, hi, hp⟩
  · exact Subtype.ext h
  · rw [mem_BranchNodes_iff, hp, childCount_starTree_leaf] at hv
    omega

/-- The children of the star-tree root are the depth-one positions. -/
theorem mem_childrenOf_root_star {n : ℕ} {c : VPos (starTree n)}
    (hc : c ∈ childrenOf (rootV (starTree n))) : ∃ i < n, c.1 = [i] := by
  rcases isPos_starTree_iff.mp c.2 with h | ⟨i, hi, hp⟩
  · rw [mem_childrenOf, h] at hc
    simp [rootV] at hc
  · exact ⟨i, hi, hp⟩

/-- A depth-one vertex of the star tree is a leaf. -/
theorem starChild_mem_leaves {n : ℕ} {c : VPos (starTree n)} {i : ℕ}
    (hc : c.1 = [i]) : c ∈ Leaves (starTree n) :=
  mem_Leaves_iff.mpr (by rw [hc]; exact childCount_starTree_leaf)

/-- The constant marking `N ≥ 1` on the star tree (its only branch node is
the root, so `parent_gt` is vacuous). -/
def starMarking (n N : ℕ) (hN : 1 ≤ N) : HeppMarking (starTree n) where
  Nexp := fun _ => N
  pos := fun _ _ => hN
  parent_gt := fun _ hv hne => absurd (branch_star_eq_root hv) hne

@[simp] theorem scaleN_starMarking {n N : ℕ} (hN : 1 ≤ N) (v : VPos (starTree n)) :
    (scaleN (starMarking n N hN) v : ℝ) = 2 ^ N := by
  simp [scaleN, starMarking]

/-- Any constant exponent is a Hepp marking of the bare leaf (no branch
nodes, so both constraints are vacuous). -/
def leafMarking (N : ℕ) : HeppMarking leaf where
  Nexp := fun _ => N
  pos := fun v hv => absurd hv (by simp [branchNodes_leaf])
  parent_gt := fun v hv => absurd hv (by simp [branchNodes_leaf])

/-! ## Realization (paper Lemma 5.5, single-scale case) -/

/-- The bare leaf realizes any bounded singleton: all Def 5.4 conditions are
vacuous for a single leaf. -/
theorem realizes_leaf (M N : ℕ) (x₀ : Fin 4 → ℤ) (hbound : ∀ i, |x₀ i| ≤ (M : ℤ)) :
    Realizes (leafMarking N) M {x₀} := by
  refine ⟨fun _ => x₀, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b _
    exact Subtype.ext ((vpos_leaf_eq a.1).trans (vpos_leaf_eq b.1).symm)
  · intro l l' hne
    exact absurd (Subtype.ext ((vpos_leaf_eq l.1).trans (vpos_leaf_eq l'.1).symm)) hne
  · intro l i
    exact hbound i
  · intro v hv
    exact absurd hv (by simp [branchNodes_leaf])
  · have hne : (Finset.univ : Finset {v // v ∈ Leaves leaf}).Nonempty :=
      ⟨⟨rootV leaf, root_mem_leaves_leaf⟩, Finset.mem_univ _⟩
    rw [Finset.image_const hne]

/-- The star tree on `Z.card` leaves with the constant marking `N` realizes
any `Z` with at least two points, all pairwise distances in the dyadic window
`[2^N/2, 2^N]`, and coordinates bounded by `M`. -/
theorem realizes_star (M N : ℕ) (hN : 1 ≤ N) (Z : Finset (Fin 4 → ℤ)) (hn : 2 ≤ Z.card)
    (hbound : ∀ x ∈ Z, ∀ i, |x i| ≤ (M : ℤ))
    (hsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → (2 : ℝ) ^ N / 2 ≤ znorm (x - y))
    (hlink : ∀ x ∈ Z, ∀ y ∈ Z, znorm (x - y) ≤ (2 : ℝ) ^ N) :
    Realizes (starMarking Z.card N hN) M Z := by
  have hcard : (Leaves (starTree Z.card)).card = Z.card := card_leaves_starTree hn
  have e : {v // v ∈ Leaves (starTree Z.card)} ≃ {x // x ∈ Z} :=
    Finset.equivOfCardEq hcard
  have hinj : Function.Injective fun l => ((e l).1 : Fin 4 → ℤ) :=
    fun a b h => e.injective (Subtype.coe_injective h)
  refine ⟨fun l => (e l).1, ⟨hinj, ?_, ?_, ?_⟩, ?_⟩
  · -- (a) separation: the lca scale is the constant 2^N
    intro l l' hne
    rw [scaleN_starMarking]
    exact hsep _ (e l).2 _ (e l').2 fun h => hne (hinj h)
  · -- boundedness
    intro l i
    exact hbound _ (e l).2 i
  · -- (b) links: children of the root are leaves; all pairs directly linked
    intro v hv
    obtain rfl := branch_star_eq_root hv
    intro c hc c' hc'
    obtain ⟨i, hi, hci⟩ := mem_childrenOf_root_star hc
    obtain ⟨j, hj, hcj⟩ := mem_childrenOf_root_star hc'
    have hcl : c ∈ Leaves (starTree Z.card) := starChild_mem_leaves hci
    have hcl' : c' ∈ Leaves (starTree Z.card) := starChild_mem_leaves hcj
    refine Relation.ReflTransGen.single
      ⟨hc, hc', ⟨c, hcl⟩, self_mem_leavesUnder c hcl,
        ⟨c', hcl'⟩, self_mem_leavesUnder c' hcl', ?_⟩
    rw [scaleN_starMarking]
    exact hlink _ (e _).2 _ (e _).2
  · -- image is exactly Z
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, hl⟩
      rw [← hl]; exact (e l).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩

/-- **Lemma 5.5, single-scale case (stage 2')**: a nonempty set `Z ⊆ [-M, M]⁴`
whose pairwise distances all lie in one dyadic window `[2^N/2, 2^N]` is
realized by a valid marked Hepp tree with `Z.card` leaves — the bare leaf if
`Z` is a singleton, else the star tree with constant marking `N` (so every
branch node carries exactly the exponent `N`). -/
theorem exists_star_realizes (M N : ℕ) (hN : 1 ≤ N) (Z : Finset (Fin 4 → ℤ))
    (hZ : Z.Nonempty) (hbound : ∀ x ∈ Z, ∀ i, |x i| ≤ (M : ℤ))
    (hsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → (2 : ℝ) ^ N / 2 ≤ znorm (x - y))
    (hlink : ∀ x ∈ Z, ∀ y ∈ Z, znorm (x - y) ≤ (2 : ℝ) ^ N) :
    ∃ (t : PlaneTree) (_ : t.isValid = true) (Nm : HeppMarking t),
      Realizes Nm M Z ∧ t.leafCount = Z.card ∧ ∀ v ∈ BranchNodes t, Nm.Nexp v = N := by
  rcases Nat.lt_or_ge Z.card 2 with hn | hn
  · have hone : Z.card = 1 := by
      have := Finset.card_pos.mpr hZ
      omega
    obtain ⟨x₀, rfl⟩ := Finset.card_eq_one.mp hone
    refine ⟨leaf, rfl, leafMarking N,
      realizes_leaf M N x₀ (fun i => hbound x₀ (Finset.mem_singleton_self x₀) i), ?_, ?_⟩
    · rw [Finset.card_singleton]
      decide
    · intro v hv
      exact absurd hv (by simp [branchNodes_leaf])
  · exact ⟨starTree Z.card, starTree_isValid (by omega), starMarking Z.card N hN,
      realizes_star M N hN Z hn hbound hsep hlink, leafCount_starTree (by omega),
      fun v _ => rfl⟩

/-! ## Sanity checks (kernel-evaluated) -/

example : lcaPath [0, 1] [0, 2] = [0] := rfl
example : lcaPath [1, 0] [0, 2] = [] := rfl

example : lcaV (t := cherry) ⟨[0], by decide⟩ ⟨[1], by decide⟩ = rootV cherry := by
  decide

#guard (childrenOf (rootV cherry)).card = 2
#guard (leavesUnder (rootV cherry)).card = 2
#guard (childrenOf (rootV (starTree 3))).card = 3
#guard (leavesUnder (t := starTree 3) ⟨[1], by decide⟩).card = 1
#guard (BranchNodes (starTree 3)).card = 1
#guard (starTree 3).isValid && (starTree 3).leafCount == 3

end Anderson4D
