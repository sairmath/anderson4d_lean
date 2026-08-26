import Mathlib

/-!
# Hepp trees: carrier, canonicalization, automorphism group, markings (node D-hepp)

Paper: D-hepp — Hepp trees, markings, the automorphism group

Stable Hepp-tree carrier and the Hepp-specific data of paper Definition 5.1:
branching vertices, leaves, dyadic markings, leaf multiplicities.

* `PlaneTree` — plane rooted trees (nested inductive through `List`); `size`,
  `leafCount`, `isValid` (no unary vertices), injective serialization `key`,
  canonical order-forgotten form `canon`, and the automorphism-count formula
  `autCard` (run factorials on canonically sorted children × children's counts).
* Vertices are position paths (`VPos`); the automorphism group `Aut t` is the
  subgroup of vertex permutations commuting with the total parent map, acting on
  markings with orbit–stabilizer (`card_orbit_mul_card_autMarked`).
* `BranchNodes`, `Leaves`, `HeppMarking`, `Multiplicities` — Def 5.1 data.
* `card_aut_eq_autCard` — the D-hepp cross-check tying both descriptions.

Implementation note: children are sorted with mathlib's structurally
recursive `List.insertionSort` instead of `List.mergeSort`, because `mergeSort`
is defined by well-founded recursion and does not reduce in the kernel; the
carrier needs `decide`/`rfl` to evaluate `autCard`.
All helpers below are structurally recursive.
-/

namespace Anderson4D

/-- Plane rooted tree; `node []` is a leaf. Carrier for Hepp trees (paper
Def 5.1); Hepp validity (branching ⇒ ≥ 2 children) is the separate predicate
`isValid`, and markings/multiplicities are separate data. -/
inductive PlaneTree : Type where
  | node : List PlaneTree → PlaneTree

namespace PlaneTree

mutual
/-- Number of vertices. -/
def size : PlaneTree → ℕ
  | node cs => 1 + sizeList cs
/-- Companion of `size`: total vertex count of a forest. -/
def sizeList : List PlaneTree → ℕ
  | [] => 0
  | c :: cs => size c + sizeList cs
end

/-- `sizeList` is the sum of the children's sizes. -/
theorem sizeList_eq_map (cs : List PlaneTree) : sizeList cs = (cs.map size).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [sizeList, ih, List.map_cons, List.sum_cons]

mutual
/-- Number of leaves; a bare `node []` counts as one leaf. (Children's leaf
counts are all ≥ 1, so the `max 1` only affects the leaf case.) -/
def leafCount : PlaneTree → ℕ
  | node cs => max 1 (leafCountList cs)
/-- Companion of `leafCount`: total leaf count of a forest. -/
def leafCountList : List PlaneTree → ℕ
  | [] => 0
  | c :: cs => leafCount c + leafCountList cs
end

/-- `leafCountList` is the sum of the children's leaf counts. -/
theorem leafCountList_eq_map (cs : List PlaneTree) :
    leafCountList cs = (cs.map leafCount).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [leafCountList, ih, List.map_cons, List.sum_cons]

mutual
/-- Hepp validity: no internal vertex has exactly one child. -/
def isValid : PlaneTree → Bool
  | node cs => (cs.length != 1) && isValidList cs
/-- Companion of `isValid`: validity of every tree in a forest. -/
def isValidList : List PlaneTree → Bool
  | [] => true
  | c :: cs => isValid c && isValidList cs
end

/-- `isValidList` is the conjunction of the children's validities. -/
theorem isValidList_eq_map (cs : List PlaneTree) :
    isValidList cs = (cs.map isValid).all id := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [isValidList, ih, List.map_cons, List.all_cons, id_eq]

mutual
/-- Injective serialization (balanced-parentheses encoding): `0` opens a node
and `1` closes it. Injectivity is proved below using the stack decoder. -/
def key : PlaneTree → List ℕ
  | node cs => 0 :: (keyList cs ++ [1])
/-- Companion of `key`: concatenated keys of a forest. -/
def keyList : List PlaneTree → List ℕ
  | [] => []
  | c :: cs => key c ++ keyList cs
end

/-- `keyList` is the flattened list of the children's keys. -/
theorem keyList_eq_map (cs : List PlaneTree) : keyList cs = (cs.map key).flatten := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [keyList, ih, List.map_cons, List.flatten_cons]

/-- Lexicographic `≤` on serialization keys, as a `Bool` comparator. -/
def lexLe : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true else if b < a then false else lexLe as bs

/-- Key-lexicographic comparison of trees (a decidable total preorder), the
sorting relation for canonicalization. -/
def KeyLe (a b : PlaneTree) : Prop := lexLe (key a) (key b) = true

instance : DecidableRel KeyLe := fun a b =>
  inferInstanceAs (Decidable (lexLe (key a) (key b) = true))

mutual
/-- Canonical (order-forgotten) representative: recursively canonicalize
children, then sort them by key. Two plane trees represent the same unordered
rooted tree iff their canonical forms are equal. -/
def canon : PlaneTree → PlaneTree
  | node cs => node ((canonList cs).insertionSort KeyLe)
/-- Companion of `canon`: canonicalize every tree in a forest. -/
def canonList : List PlaneTree → List PlaneTree
  | [] => []
  | c :: cs => canon c :: canonList cs
end

/-- `canonList` is `List.map canon`. -/
theorem canonList_eq_map (cs : List PlaneTree) : canonList cs = cs.map canon := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [canonList, ih, List.map_cons]

/-- Product of `(run length)!` over maximal runs of key-equal adjacent
elements (intended for canonicalized, i.e. sorted, children lists). -/
def runsProdFactorial : List PlaneTree → ℕ
  | [] => 1
  | c :: cs => go c 1 cs
where
  /-- Tail of `runsProdFactorial`: `go c k ds` scans `ds` with current run
  representative `c` of length `k`. -/
  go : PlaneTree → ℕ → List PlaneTree → ℕ
  | _, k, [] => k.factorial
  | c, k, d :: ds =>
    if key c == key d then go c (k + 1) ds else k.factorial * go d 1 ds

mutual
/-- Order of the automorphism group of the *unordered* rooted tree represented
by a plane tree: permutations of iso-equal children (run factorials on the
canonicalized children) times the children's own automorphism counts
(Prop 5.6's `|Aut(T)|`). Cross-checked against the permutation-subgroup
order in `card_aut_eq_autCard`. -/
def autCard : PlaneTree → ℕ
  | node cs => runsProdFactorial ((canonList cs).insertionSort KeyLe) * autCardList cs
/-- Companion of `autCard`: product of the automorphism counts of a forest. -/
def autCardList : List PlaneTree → ℕ
  | [] => 1
  | c :: cs => autCard c * autCardList cs
end

/-- `autCardList` is the product of the children's automorphism counts. -/
theorem autCardList_eq_map (cs : List PlaneTree) :
    autCardList cs = (cs.map autCard).prod := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [autCardList, ih, List.map_cons, List.prod_cons]

/-! ## Basic examples and compiled-evaluation sanity checks -/

/-- A leaf. -/
def leaf : PlaneTree := node []

/-- A cherry: two leaves. `|Aut| = 2`. -/
def cherry : PlaneTree := node [leaf, leaf]

#guard leaf.size = 1 ∧ cherry.size = 3
#guard cherry.leafCount = 2
#guard leaf.isValid ∧ cherry.isValid
#guard !(node [leaf]).isValid
#guard cherry.autCard = 2
#guard (node [cherry, leaf]).autCard = 2
#guard (node [cherry, cherry]).autCard = 8       -- 2! · 2 · 2
#guard (node [leaf, cherry, leaf]).autCard = 4   -- 2! (two leaf-children) · 2
-- order-forgetting: plane order of children must not matter (compared via `key`)
#guard key (node [cherry, leaf]).canon == key (node [leaf, cherry]).canon
#guard (node [node [cherry, leaf], leaf]).autCard = (node [leaf, node [leaf, cherry]]).autCard

/-! ## Positions (vertex addresses) -/

/-- A vertex address: the path of child indices from the root. -/
abbrev Pos : Type := List ℕ

/-- Validity of a position in a tree (`Bool`-valued, kernel-reducible). -/
def isPos : PlaneTree → Pos → Bool
  | _, [] => true
  | node cs, i :: p => if h : i < cs.length then isPos cs[i] p else false

/-- Position validity, `Prop`-valued. -/
def IsPos (t : PlaneTree) (p : Pos) : Prop := isPos t p = true

instance (t : PlaneTree) : DecidablePred (IsPos t) := fun p =>
  inferInstanceAs (Decidable (isPos t p = true))

/-- The root position is valid in every tree. -/
theorem isPos_nil (t : PlaneTree) : IsPos t [] := by cases t; rfl

/-- Unfolding `IsPos` along one step into child `i`. -/
theorem isPos_cons_iff {cs : List PlaneTree} {i : ℕ} {p : Pos} :
    IsPos (node cs) (i :: p) ↔ ∃ h : i < cs.length, IsPos cs[i] p := by
  by_cases h : i < cs.length
  · have e : isPos (node cs) (i :: p) = isPos cs[i] p := by simp only [isPos, dif_pos h]
    simp only [IsPos, e]; exact ⟨fun hp => ⟨h, hp⟩, fun ⟨_, hp⟩ => hp⟩
  · have e : isPos (node cs) (i :: p) = false := by simp only [isPos, dif_neg h]
    simp only [IsPos, e]
    exact ⟨fun hf => absurd hf (by decide), fun ⟨h', _⟩ => absurd h' h⟩

/-- The parent of a valid vertex is valid; the root maps to itself. -/
theorem IsPos.dropLast {t : PlaneTree} {p : Pos} (h : IsPos t p) : IsPos t p.dropLast := by
  induction p generalizing t with
  | nil => exact h
  | cons i p ih =>
    obtain ⟨cs⟩ := t
    obtain ⟨hi, hp⟩ := isPos_cons_iff.mp h
    cases p with
    | nil => exact isPos_nil _
    | cons j q => exact isPos_cons_iff.mpr ⟨hi, ih hp⟩

-- The list of all valid positions of a tree (root first), with its list-level
-- companion, as mutual *structural* recursion so both stay kernel-reducible
-- (this is what lets `decide` evaluate `|Aut cherry|`).
mutual
/-- All valid positions of `t`, root first. -/
def positions : PlaneTree → List Pos
  | node cs => [] :: (positionsList cs).zipIdx.flatMap fun x => x.1.map (x.2 :: ·)
/-- Companion of `positions` for the children list. -/
def positionsList : List PlaneTree → List (List Pos)
  | [] => []
  | c :: cs => positions c :: positionsList cs
end

/-- `positionsList` is `List.map positions`. -/
theorem positionsList_eq_map (cs : List PlaneTree) :
    positionsList cs = cs.map positions := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [positionsList, ih, List.map_cons]

/-- `positions` enumerates exactly the valid positions. -/
theorem mem_positions : ∀ (t : PlaneTree) (p : Pos), p ∈ positions t ↔ IsPos t p
  | node cs, [] => ⟨fun _ => isPos_nil _, fun _ => by simp [positions]⟩
  | node cs, i :: p => by
    rw [isPos_cons_iff, positions, positionsList_eq_map]
    simp only [List.mem_cons, reduceCtorEq, false_or, List.mem_flatMap, List.mem_map,
      List.mem_zipIdx_iff_getElem?, List.getElem?_map, Option.map_eq_some_iff]
    constructor
    · rintro ⟨⟨ps, j⟩, hzip, r, hr, heq⟩
      dsimp only at hzip hr heq
      obtain ⟨a, ha, rfl⟩ := hzip
      rw [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [List.getElem?_eq_some_iff] at ha
      obtain ⟨hlt, rfl⟩ := ha
      exact ⟨hlt, (mem_positions _ _).mp hr⟩
    · rintro ⟨hlt, hp⟩
      refine ⟨(positions cs[i], i), ⟨cs[i], ?_, rfl⟩, p, ?_, rfl⟩ <;> dsimp only
      · rw [List.getElem?_eq_getElem hlt]
      · exact (mem_positions _ _).mpr hp
termination_by t _ => sizeOf t
decreasing_by
  all_goals
    have hmem := List.sizeOf_lt_of_mem (List.getElem_mem hlt)
    simp only [node.sizeOf_spec]; omega

/-- The (finite) vertex set of `t`: valid positions. -/
abbrev VPos (t : PlaneTree) : Type := {p : Pos // IsPos t p}

instance (t : PlaneTree) : Fintype (VPos t) :=
  Fintype.subtype (positions t).toFinset fun p => by
    rw [List.mem_toFinset]; exact mem_positions t p

/-- The root vertex. -/
def rootV (t : PlaneTree) : VPos t := ⟨[], isPos_nil t⟩

/-- Total parent map on vertices; the root is its own parent. -/
def parentV {t : PlaneTree} (v : VPos t) : VPos t := ⟨v.1.dropLast, v.2.dropLast⟩

/-! ## The automorphism group

A vertex permutation is an automorphism of the *unordered* rooted tree iff it
commutes with the total parent map (a classical, `HEq`-free characterization). -/

/-- A vertex permutation is an automorphism of the unordered rooted tree iff
it commutes with the parent map. -/
def IsAut (t : PlaneTree) (e : Equiv.Perm (VPos t)) : Prop :=
  ∀ v, e (parentV v) = parentV (e v)

instance (t : PlaneTree) : DecidablePred (IsAut t) := fun e =>
  inferInstanceAs (Decidable (∀ v, e (parentV v) = parentV (e v)))

/-- Automorphisms of the unordered rooted tree presented by `t`, as a subgroup
of the vertex permutations. -/
def autSubgroup (t : PlaneTree) : Subgroup (Equiv.Perm (VPos t)) where
  carrier := {e | IsAut t e}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb v => by
    show a (b (parentV v)) = parentV (a (b v)); rw [hb v, ha (b v)]
  inv_mem' := fun {a} ha v => by
    have h1 : a (parentV (a⁻¹ v)) = parentV v := by
      rw [ha (a⁻¹ v)]; exact congrArg parentV (a.apply_symm_apply v)
    calc a⁻¹ (parentV v) = a⁻¹ (a (parentV (a⁻¹ v))) := by rw [h1]
      _ = parentV (a⁻¹ v) := a.symm_apply_apply _

instance (t : PlaneTree) : DecidablePred (· ∈ autSubgroup t) := fun e =>
  decidable_of_iff (IsAut t e) Iff.rfl

/-- The automorphism group of (the unordered tree presented by) `t`. -/
abbrev Aut (t : PlaneTree) : Type := ↥(autSubgroup t)

/-- Every automorphism fixes the root (automatic from parent-commutation). -/
theorem apply_root_eq {t : PlaneTree} (g : Aut t) : g.1 (rootV t) = rootV t := by
  have h : parentV (g.1 (rootV t)) = g.1 (rootV t) := (g.2 (rootV t)).symm
  have hval : (g.1 (rootV t)).1.dropLast = (g.1 (rootV t)).1 := congrArg Subtype.val h
  have hlen := congrArg List.length hval
  rw [List.length_dropLast] at hlen
  apply Subtype.ext
  cases hcase : (g.1 (rootV t)).1 with
  | nil => rfl
  | cons a as => rw [hcase, List.length_cons] at hlen; omega

/-! ## Markings and the action of `Aut` -/

/-- A plain marking: one natural number per vertex (the raw carrier on which
`Aut t` acts; the Def 5.1 constraints are bundled in `HeppMarking`). -/
abbrev Marking (t : PlaneTree) : Type := VPos t → ℕ

/-- `Aut t` acts on markings by precomposition with the inverse vertex
transport (the position transport is just `g.1 : Equiv.Perm (VPos t)`). -/
instance (t : PlaneTree) : MulAction (Aut t) (Marking t) where
  smul g N := fun v => N ((g⁻¹ : Aut t).1 v)
  one_smul N := rfl
  mul_smul g h N := by
    funext v
    show N (((g * h)⁻¹ : Aut t).1 v) = N ((h⁻¹ : Aut t).1 ((g⁻¹ : Aut t).1 v))
    rw [mul_inv_rev, Subgroup.coe_mul, Equiv.Perm.mul_apply]

/-- Unfolding lemma for the action on markings. -/
theorem smul_marking_apply {t : PlaneTree} (g : Aut t) (N : Marking t) (v : VPos t) :
    (g • N) v = N ((g⁻¹ : Aut t).1 v) := rfl

/-- Automorphisms of the marked tree `(T, N)` = the marking stabilizer
(paper's `Aut(T, N)` in Prop 5.6). -/
abbrev AutMarked (t : PlaneTree) (N : Marking t) : Subgroup (Aut t) :=
  MulAction.stabilizer (Aut t) N

instance (t : PlaneTree) (N : Marking t) : DecidablePred (· ∈ AutMarked t N) :=
  fun g => decidable_of_iff (g • N = N) MulAction.mem_stabilizer_iff.symm

instance (t : PlaneTree) (N : Marking t) : Fintype (MulAction.orbit (Aut t) N) :=
  Fintype.ofFinset (Finset.univ.image fun g : Aut t => g • N) fun M => by
    simp [MulAction.mem_orbit_iff, eq_comm]

/-- **Orbit–stabilizer for marked trees** (Prop 5.6 counting step):
`#(orbit of N) · |Aut(T, N)| = |Aut(T)|`. -/
theorem card_orbit_mul_card_autMarked (t : PlaneTree) (N : Marking t) :
    (MulAction.orbit (Aut t) N).toFinset.card * Fintype.card (AutMarked t N)
      = Fintype.card (Aut t) := by
  rw [Set.toFinset_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Aut t) N

/-! ## Sanity checks on the cherry -/

example : positions cherry = [[], [0], [1]] := rfl

/-- The two-leaf cherry has automorphism group of order 2 — proved by `decide`
(the `Fintype` genuinely computes in the kernel here). -/
example : Fintype.card (Aut cherry) = 2 := by decide

/-- A marking separating the two leaves of the cherry (sanity checks only). -/
def testMark : Marking cherry := fun v => if v.1 = [0] then 1 else 0

#guard Fintype.card (Aut cherry) = 2
#guard (MulAction.orbit (Aut cherry) testMark).toFinset.card = 2
#guard Fintype.card (AutMarked cherry testMark) = 1
#guard Fintype.card (AutMarked cherry (fun _ => 0)) = 2
#guard Fintype.card (Aut (node [cherry, leaf])) = 2
#guard Fintype.card (Aut (node [cherry, cherry])) = 8

example :
    (MulAction.orbit (Aut cherry) testMark).toFinset.card
        * Fintype.card (AutMarked cherry testMark)
      = Fintype.card (Aut cherry) :=
  card_orbit_mul_card_autMarked cherry testMark

/-! ## Hepp data (paper Def 5.1): branching vertices, leaves, markings,
multiplicities -/

/-- Number of children of the vertex at position `p` (`0` if `p` is invalid);
`Bool`-free companion of `isPos`, kernel-reducible. -/
def childCount : PlaneTree → Pos → ℕ
  | node cs, [] => cs.length
  | node cs, i :: p => if h : i < cs.length then childCount cs[i] p else 0

/-- Branching vertices: at least two children (paper Def 5.1's branching
nodes; in a Hepp-valid tree every internal vertex is branching). -/
def BranchNodes (t : PlaneTree) : Finset (VPos t) :=
  Finset.univ.filter fun v => 2 ≤ childCount t v.1

/-- Leaves: childless vertices. -/
def Leaves (t : PlaneTree) : Finset (VPos t) :=
  Finset.univ.filter fun v => childCount t v.1 = 0

#guard (BranchNodes cherry).card = 1
#guard (Leaves cherry).card = 2
#guard (BranchNodes (node [cherry, cherry])).card = 3
#guard (Leaves (node [cherry, cherry])).card = 4
#guard (BranchNodes leaf).card = 0 && (Leaves leaf).card = 1
#guard (BranchNodes (node [leaf])).card = 0     -- unary vertex: not branching

/-- A Hepp marking on `t` (paper Def 5.1): dyadic scales `N_n = 2 ^ Nexp n`
attached to the **branching** vertices, with `N_n ≥ 2` and strictly increasing
toward the root (`N_{n⁺} > N_n` for the parent `n⁺`). The exponent function
`Nexp` is stored as a total function on all vertices; its values at
non-branching vertices are junk (unconstrained), and both constraints
quantify over `BranchNodes t` only. Note that in a Hepp-valid tree the parent
of any vertex has ≥ 2 children, so `parent_gt` only ever inspects `Nexp` at
branching vertices. -/
structure HeppMarking (t : PlaneTree) where
  /-- Exponent of the dyadic scale: the paper's `N_n` is `2 ^ Nexp n`. -/
  Nexp : VPos t → ℕ
  /-- Scales are dyadic with exponent `≥ 1`, i.e. `N_n ∈ {2, 4, 8, …}`. -/
  pos : ∀ v ∈ BranchNodes t, 1 ≤ Nexp v
  /-- Strict monotonicity toward the root: the parent's scale is larger. -/
  parent_gt : ∀ v ∈ BranchNodes t, v ≠ rootV t → Nexp (parentV v) > Nexp v

/-- Leaf multiplicities on `t` (paper Def 5.1): `m v ≥ 2` at every leaf;
values at non-leaf vertices are junk (unconstrained). -/
structure Multiplicities (t : PlaneTree) where
  /-- The multiplicity of each leaf. -/
  m : VPos t → ℕ
  /-- Every leaf occurs with multiplicity at least two. -/
  two_le : ∀ v ∈ Leaves t, 2 ≤ m v

/-- Sanity: the constant exponent `1` is a Hepp marking of the cherry (its only
branching vertex is the root, so `parent_gt` is vacuous). -/
example : HeppMarking cherry := ⟨fun _ => 1, by decide, by decide⟩

/-- Sanity: constant multiplicity `2` on the cherry. -/
example : Multiplicities cherry := ⟨fun _ => 2, by decide⟩

/-- Sanity: a genuinely decreasing-from-the-root marking on the two-cherry
tree (root exponent `2`, both cherry vertices exponent `1`). -/
example : HeppMarking (node [cherry, cherry]) :=
  ⟨fun v => if v.1 = [] then 2 else 1, by decide, by decide⟩


/-! ## Proof toolkit for the D-hepp cross-check

Key injectivity (stack decoder), order properties of `KeyLe`, the vertex
calculus of `node` trees (`childV`), tree isomorphisms `Iso` as
parent-commuting vertex bijections, the graft/split equivalence for nodes,
permutations of fibers of a classification, and run-length counting on
canonically sorted lists. All of it feeds `card_aut_eq_autCard`. -/
/-! ### Key injectivity via a stack decoder -/

/-- Stack decoder inverting `key`: token `0` opens a frame, token `1` closes the
top frame into the frame below (children are collected in reverse order). -/
def dec : List ℕ → List (List PlaneTree) → List (List PlaneTree)
  | [], st => st
  | 0 :: xs, st => dec xs ([] :: st)
  | 1 :: xs, ts :: us :: st => dec xs ((node ts.reverse :: us) :: st)
  | _ :: xs, st => dec xs st

mutual
/-- Running the decoder over `key t` pushes `t` onto the top frame. -/
theorem dec_key_append : ∀ (t : PlaneTree) (xs : List ℕ) (acc : List PlaneTree)
    (st : List (List PlaneTree)), dec (key t ++ xs) (acc :: st) = dec xs ((t :: acc) :: st)
  | node cs, xs, acc, st => by
    rw [key, List.cons_append, List.append_assoc]
    show dec (keyList cs ++ ([1] ++ xs)) ([] :: acc :: st) = _
    rw [dec_keyList_append cs ([1] ++ xs) [] (acc :: st)]
    show dec xs ((node (cs.reverse ++ []).reverse :: acc) :: st) = _
    rw [List.append_nil, List.reverse_reverse]
/-- Companion of `dec_key_append` for forests. -/
theorem dec_keyList_append : ∀ (cs : List PlaneTree) (xs : List ℕ) (acc : List PlaneTree)
    (st : List (List PlaneTree)), dec (keyList cs ++ xs) (acc :: st) = dec xs ((cs.reverse ++ acc) :: st)
  | [], _, _, _ => rfl
  | c :: cs, xs, acc, st => by
    rw [keyList, List.append_assoc, dec_key_append c _ acc st,
      dec_keyList_append cs xs (c :: acc) st, List.reverse_cons, List.append_assoc,
      List.singleton_append]
end

/-- The serialization `key` is injective. -/
theorem key_injective : Function.Injective key := by
  intro s t h
  have hs := dec_key_append s [] [] []
  have ht := dec_key_append t [] [] []
  rw [List.append_nil] at hs ht
  rw [h, ht] at hs
  have hs' : ([t] : List PlaneTree) :: [] = [s] :: [] := hs
  injection hs' with h1 _
  injection h1 with h2 _
  exact h2.symm

instance : DecidableEq PlaneTree := fun a b =>
  decidable_of_iff (key a = key b) ⟨fun h => key_injective h, fun h => h ▸ rfl⟩

/-! ### The lexicographic comparator is a total preorder, antisymmetric on keys -/

theorem lexLe_cons_lt {a b : ℕ} {as bs : List ℕ} (h : a < b) :
    lexLe (a :: as) (b :: bs) = true := by rw [lexLe, if_pos h]

theorem lexLe_cons_gt {a b : ℕ} {as bs : List ℕ} (h : b < a) :
    lexLe (a :: as) (b :: bs) = false := by rw [lexLe, if_neg (Nat.lt_asymm h), if_pos h]

theorem lexLe_cons_eq {a : ℕ} {as bs : List ℕ} :
    lexLe (a :: as) (a :: bs) = lexLe as bs := by
  rw [lexLe, if_neg (Nat.lt_irrefl a), if_neg (Nat.lt_irrefl a)]

theorem lexLe_total : ∀ (a b : List ℕ), lexLe a b = true ∨ lexLe b a = true
  | [], _ => Or.inl rfl
  | _ :: _, [] => Or.inr rfl
  | a :: as, b :: bs => by
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact Or.inl (lexLe_cons_lt h)
    · subst h
      rcases lexLe_total as bs with h' | h'
      · exact Or.inl (lexLe_cons_eq.trans h')
      · exact Or.inr (lexLe_cons_eq.trans h')
    · exact Or.inr (lexLe_cons_lt h)

theorem lexLe_trans : ∀ (a b c : List ℕ), lexLe a b = true → lexLe b c = true →
    lexLe a c = true
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by exact absurd h (by rw [lexLe]; exact Bool.false_ne_true)
  | _ :: _, _ :: _, [], _, h => by exact absurd h (by rw [lexLe]; exact Bool.false_ne_true)
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · rcases Nat.lt_trichotomy b c with hbc | hbc | hbc
      · exact lexLe_cons_lt (hab.trans hbc)
      · exact hbc ▸ lexLe_cons_lt hab
      · rw [lexLe_cons_gt hbc] at h2; exact absurd h2 Bool.false_ne_true
    · subst hab
      rcases Nat.lt_trichotomy a c with hbc | hbc | hbc
      · exact lexLe_cons_lt hbc
      · subst hbc
        rw [lexLe_cons_eq] at h1 h2 ⊢
        exact lexLe_trans as bs cs h1 h2
      · rw [lexLe_cons_gt hbc] at h2; exact absurd h2 Bool.false_ne_true
    · rw [lexLe_cons_gt hab] at h1; exact absurd h1 Bool.false_ne_true

theorem lexLe_antisymm : ∀ (a b : List ℕ), lexLe a b = true → lexLe b a = true → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by exact absurd h (by rw [lexLe]; exact Bool.false_ne_true)
  | _ :: _, [], h, _ => by exact absurd h (by rw [lexLe]; exact Bool.false_ne_true)
  | a :: as, b :: bs, h1, h2 => by
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · rw [lexLe_cons_gt hab] at h2; exact absurd h2 Bool.false_ne_true
    · subst hab
      rw [lexLe_cons_eq] at h1 h2
      rw [lexLe_antisymm as bs h1 h2]
    · rw [lexLe_cons_gt hab] at h1; exact absurd h1 Bool.false_ne_true

instance : Std.Total KeyLe := ⟨fun a b => lexLe_total (key a) (key b)⟩
instance : IsTrans PlaneTree KeyLe := ⟨fun a b c => lexLe_trans (key a) (key b) (key c)⟩
instance : Std.Antisymm KeyLe := ⟨fun _ _ h1 h2 => key_injective (lexLe_antisymm _ _ h1 h2)⟩

/-- In a `KeyLe`-pairwise list `c :: d :: ds` with `key c ≠ key d`, the key of
`c` occurs nowhere from `d` on. -/
theorem key_notMem_map_of_pairwise {c d : PlaneTree} {ds : List PlaneTree}
    (h : (c :: d :: ds).Pairwise KeyLe) (hne : key c ≠ key d) :
    key c ∉ (d :: ds).map key := by
  rcases List.pairwise_cons.mp h with ⟨hc, hd⟩
  rcases List.pairwise_cons.mp hd with ⟨hdall, _⟩
  intro hmem
  rcases List.mem_map.mp hmem with ⟨e, he, hkey⟩
  rcases List.mem_cons.mp he with rfl | he
  · exact hne hkey.symm
  · have h1 : lexLe (key c) (key d) = true := hc d (List.mem_cons_self ..)
    have h2 : lexLe (key d) (key c) = true := hkey ▸ hdall e he
    exact hne (key_injective (lexLe_antisymm _ _ h1 h2) ▸ rfl)

/-! ### Vertices of a node: root and child embeddings -/

theorem isPos_cons_lt {cs : List PlaneTree} {i : ℕ} {p : Pos}
    (h : IsPos (node cs) (i :: p)) : i < cs.length :=
  (isPos_cons_iff.mp h).elim fun hi _ => hi

theorem isPos_cons_tail {cs : List PlaneTree} {i : ℕ} {p : Pos}
    (h : IsPos (node cs) (i :: p)) : IsPos (cs.get ⟨i, isPos_cons_lt h⟩) p := by
  obtain ⟨hi, hp⟩ := isPos_cons_iff.mp h
  rw [List.get_eq_getElem]
  exact hp

/-- The vertex of `node cs` at position `i :: v` inside child `i`. -/
def childV {cs : List PlaneTree} (i : Fin cs.length) (v : VPos (cs.get i)) :
    VPos (node cs) :=
  ⟨i.1 :: v.1, isPos_cons_iff.mpr ⟨i.2, List.get_eq_getElem (l := cs) (i := i) ▸ v.2⟩⟩

@[simp] theorem childV_val {cs : List PlaneTree} (i : Fin cs.length) (v : VPos (cs.get i)) :
    (childV i v).1 = i.1 :: v.1 := rfl

theorem childV_ne_root {cs : List PlaneTree} (i : Fin cs.length) (v : VPos (cs.get i)) :
    childV i v ≠ rootV (node cs) :=
  fun h => List.cons_ne_nil _ _ (congrArg Subtype.val h)

theorem childV_inj_idx {cs : List PlaneTree} {i j : Fin cs.length} {v : VPos (cs.get i)}
    {w : VPos (cs.get j)} (h : childV i v = childV j w) : i = j := by
  have hval := congrArg Subtype.val h
  injection hval with h1 _
  exact Fin.ext h1

theorem childV_inj_snd {cs : List PlaneTree} {i : Fin cs.length} {v w : VPos (cs.get i)}
    (h : childV i v = childV i w) : v = w := by
  have hval := congrArg Subtype.val h
  injection hval with _ h2
  exact Subtype.ext h2

theorem vpos_node_cases {cs : List PlaneTree} (P : VPos (node cs) → Prop)
    (hroot : P (rootV (node cs))) (hchild : ∀ i v, P (childV i v)) : ∀ v, P v := by
  rintro ⟨p, hp⟩
  match p, hp with
  | [], hp => exact hroot
  | i :: q, hp => exact hchild ⟨i, isPos_cons_lt hp⟩ ⟨q, isPos_cons_tail hp⟩

theorem ne_root_iff {t : PlaneTree} {v : VPos t} : v ≠ rootV t ↔ v.1 ≠ [] :=
  ⟨fun h hv => h (Subtype.ext hv), fun h hv => h (congrArg Subtype.val hv)⟩

@[simp] theorem parentV_rootV {t : PlaneTree} : parentV (rootV t) = rootV t := rfl

@[simp] theorem parentV_childV_rootV {cs : List PlaneTree} (i : Fin cs.length) :
    parentV (childV i (rootV (cs.get i))) = rootV (node cs) := rfl

theorem parentV_childV {cs : List PlaneTree} (i : Fin cs.length) {v : VPos (cs.get i)}
    (hv : v ≠ rootV (cs.get i)) : parentV (childV i v) = childV i (parentV v) := by
  apply Subtype.ext
  show (i.1 :: v.1).dropLast = i.1 :: v.1.dropLast
  match v, ne_root_iff.mp hv with
  | ⟨_ :: _, _⟩, _ => rfl
  | ⟨[], _⟩, h => exact absurd rfl h

theorem eq_rootV_of_parentV_eq {t : PlaneTree} {v : VPos t} (h : parentV v = v) :
    v = rootV t := by
  apply Subtype.ext
  have hval : v.1.dropLast = v.1 := congrArg Subtype.val h
  have hlen := congrArg List.length hval
  rw [List.length_dropLast] at hlen
  cases hv : v.1 with
  | nil => rfl
  | cons a q => rw [hv, List.length_cons] at hlen; omega

theorem parentV_eq_root_cases {cs : List PlaneTree} {v : VPos (node cs)}
    (h : parentV v = rootV (node cs)) :
    v = rootV (node cs) ∨ ∃ i, v = childV i (rootV (cs.get i)) := by
  have hval : v.1.dropLast = [] := congrArg Subtype.val h
  match v, hval with
  | ⟨[], _⟩, _ => exact Or.inl rfl
  | ⟨[i], hp⟩, _ => exact Or.inr ⟨⟨i, isPos_cons_lt hp⟩, Subtype.ext rfl⟩
  | ⟨i :: a :: q, hp⟩, hval => simp at hval

theorem exists_childV_of_parentV_eq {ds : List PlaneTree} {x : VPos (node ds)}
    {j : Fin ds.length} {u : VPos (ds.get j)} (h : parentV x = childV j u) :
    ∃ u', x = childV j u' := by
  have hval : x.1.dropLast = j.1 :: u.1 := congrArg Subtype.val h
  have hne : x.1 ≠ [] := fun h0 => List.cons_ne_nil _ _ ((h0 ▸ hval).symm)
  have hx : x.1 = j.1 :: (u.1 ++ [x.1.getLast hne]) := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [hval, List.cons_append]
  have hx2 : IsPos (node ds) (j.1 :: (u.1 ++ [x.1.getLast hne])) := hx ▸ x.2
  exact ⟨⟨u.1 ++ [x.1.getLast hne], isPos_cons_tail hx2⟩, Subtype.ext hx⟩

/-! ### Isomorphisms of unordered rooted trees -/

/-- An isomorphism between the unordered rooted trees presented by `s` and `t`:
a parent-commuting bijection of vertices (for `s = t` this is exactly the
defining property of `autSubgroup`). -/
def Iso (s t : PlaneTree) : Type :=
  {e : VPos s ≃ VPos t // ∀ v, e (parentV v) = parentV (e v)}

instance (s t : PlaneTree) : Finite (Iso s t) := Subtype.finite

namespace Iso

theorem ext {s t : PlaneTree} {e f : Iso s t} (h : ∀ v, e.1 v = f.1 v) : e = f :=
  Subtype.ext (Equiv.ext h)

/-- The identity isomorphism. -/
def refl (t : PlaneTree) : Iso t t := ⟨Equiv.refl _, fun _ => rfl⟩

/-- Composition of isomorphisms. -/
def trans {s t u : PlaneTree} (e : Iso s t) (f : Iso t u) : Iso s u :=
  ⟨e.1.trans f.1, fun v => by simp only [Equiv.trans_apply, e.2 v, f.2 (e.1 v)]⟩

/-- Inverse of an isomorphism. -/
def symm {s t : PlaneTree} (e : Iso s t) : Iso t s :=
  ⟨e.1.symm, fun v => by
    have h := e.2 (e.1.symm v)
    rw [Equiv.apply_symm_apply] at h
    rw [← h, Equiv.symm_apply_apply]⟩

/-- Transport along an equality of trees. -/
def ofEq {s t : PlaneTree} (h : s = t) : Iso s t := h ▸ refl s

/-- Transport an isomorphism along equalities of its endpoints. -/
def congr {s t s' t' : PlaneTree} (hs : s = s') (ht : t = t') (e : Iso s t) : Iso s' t' :=
  (ofEq hs.symm).trans (e.trans (ofEq ht))

@[simp] theorem refl_apply {t : PlaneTree} (v : VPos t) : (refl t).1 v = v := rfl

@[simp] theorem trans_apply {s t u : PlaneTree} (e : Iso s t) (f : Iso t u) (v : VPos s) :
    (e.trans f).1 v = f.1 (e.1 v) := rfl

@[simp] theorem symm_apply_apply {s t : PlaneTree} (e : Iso s t) (v : VPos s) :
    e.symm.1 (e.1 v) = v := e.1.symm_apply_apply v

@[simp] theorem apply_symm_apply {s t : PlaneTree} (e : Iso s t) (v : VPos t) :
    e.1 (e.symm.1 v) = v := e.1.apply_symm_apply v

@[simp] theorem symm_symm {s t : PlaneTree} (e : Iso s t) : e.symm.symm = e :=
  Subtype.ext (Equiv.symm_symm e.1)

/-- Isomorphisms send the root to the root. -/
theorem root_eq {s t : PlaneTree} (e : Iso s t) : e.1 (rootV s) = rootV t := by
  apply eq_rootV_of_parentV_eq
  have h := e.2 (rootV s)
  rw [parentV_rootV] at h
  exact h.symm

theorem apply_ne_root {s t : PlaneTree} (e : Iso s t) {v : VPos s} (hv : v ≠ rootV s) :
    e.1 v ≠ rootV t := by
  intro h
  apply hv
  have h2 := congrArg e.symm.1 h
  rw [symm_apply_apply] at h2
  rw [h2]
  exact root_eq e.symm

end Iso

/-- Automorphisms are exactly the self-isomorphisms. -/
def isoAutEquiv (t : PlaneTree) : Iso t t ≃ Aut t :=
  Equiv.subtypeEquivRight fun _ => ⟨fun h => h, fun h => h⟩

/-! ### Splitting a node's vertex set into root and child parts; grafting -/

/-- The vertices of `node cs` are the root plus the vertices of the children. -/
def vposNodeEquiv (cs : List PlaneTree) :
    VPos (node cs) ≃ Option ((i : Fin cs.length) × VPos (cs.get i)) where
  toFun v :=
    match v with
    | ⟨[], _⟩ => none
    | ⟨i :: q, hp⟩ => some ⟨⟨i, isPos_cons_lt hp⟩, ⟨q, isPos_cons_tail hp⟩⟩
  invFun x :=
    match x with
    | none => rootV (node cs)
    | some ⟨i, v⟩ => childV i v
  left_inv v := by
    match v with
    | ⟨[], _⟩ => rfl
    | ⟨i :: q, hp⟩ => rfl
  right_inv x := by
    match x with
    | none => rfl
    | some ⟨i, v⟩ => rfl

@[simp] theorem vposNodeEquiv_root (cs : List PlaneTree) :
    vposNodeEquiv cs (rootV (node cs)) = none := rfl

@[simp] theorem vposNodeEquiv_childV {cs : List PlaneTree} (i : Fin cs.length)
    (v : VPos (cs.get i)) : vposNodeEquiv cs (childV i v) = some ⟨i, v⟩ := rfl

@[simp] theorem vposNodeEquiv_symm_none (cs : List PlaneTree) :
    (vposNodeEquiv cs).symm none = rootV (node cs) := rfl

@[simp] theorem vposNodeEquiv_symm_some {cs : List PlaneTree} (i : Fin cs.length)
    (v : VPos (cs.get i)) : (vposNodeEquiv cs).symm (some ⟨i, v⟩) = childV i v := rfl

/-- Carrier bijection of a graft: permute children by `π`, act inside child `i`
by `F i`. -/
def graftCarrier {cs ds : List PlaneTree} (π : Fin cs.length ≃ Fin ds.length)
    (F : ∀ i, Iso (cs.get i) (ds.get (π i))) : VPos (node cs) ≃ VPos (node ds) :=
  (vposNodeEquiv cs).trans
    ((Equiv.optionCongr (Equiv.sigmaCongr π fun i => (F i).1)).trans (vposNodeEquiv ds).symm)

@[simp] theorem graftCarrier_root {cs ds : List PlaneTree} (π : Fin cs.length ≃ Fin ds.length)
    (F : ∀ i, Iso (cs.get i) (ds.get (π i))) :
    graftCarrier π F (rootV (node cs)) = rootV (node ds) := rfl

@[simp] theorem graftCarrier_childV {cs ds : List PlaneTree} (π : Fin cs.length ≃ Fin ds.length)
    (F : ∀ i, Iso (cs.get i) (ds.get (π i))) (i : Fin cs.length) (v : VPos (cs.get i)) :
    graftCarrier π F (childV i v) = childV (π i) ((F i).1 v) := rfl

/-- Graft a permutation of the children together with per-child isomorphisms
into an isomorphism of the nodes. -/
def graft {cs ds : List PlaneTree} (π : Fin cs.length ≃ Fin ds.length)
    (F : ∀ i, Iso (cs.get i) (ds.get (π i))) : Iso (node cs) (node ds) := by
  refine ⟨graftCarrier π F, ?_⟩
  intro v
  induction v using vpos_node_cases with
  | hroot => rw [parentV_rootV, graftCarrier_root, parentV_rootV]
  | hchild i w =>
    by_cases hw : w = rootV (cs.get i)
    · subst hw
      rw [parentV_childV_rootV, graftCarrier_root, graftCarrier_childV, Iso.root_eq,
        parentV_childV_rootV]
    · rw [parentV_childV i hw, graftCarrier_childV, graftCarrier_childV, (F i).2 w,
        parentV_childV (π i) ((F i).apply_ne_root hw)]

@[simp] theorem graft_apply_root {cs ds : List PlaneTree} (π : Fin cs.length ≃ Fin ds.length)
    (F : ∀ i, Iso (cs.get i) (ds.get (π i))) :
    (graft π F).1 (rootV (node cs)) = rootV (node ds) := rfl

@[simp] theorem graft_apply_childV {cs ds : List PlaneTree} (π : Fin cs.length ≃ Fin ds.length)
    (F : ∀ i, Iso (cs.get i) (ds.get (π i))) (i : Fin cs.length) (v : VPos (cs.get i)) :
    (graft π F).1 (childV i v) = childV (π i) ((F i).1 v) := rfl

/-! ### Splitting an isomorphism of nodes into child data -/

theorem vpos_node_cases_or {cs : List PlaneTree} (v : VPos (node cs)) :
    v = rootV (node cs) ∨ ∃ i w, v = childV i w :=
  vpos_node_cases (fun v => v = rootV (node cs) ∨ ∃ i w, v = childV i w)
    (Or.inl rfl) (fun i w => Or.inr ⟨i, w, rfl⟩) v

section Split
variable {cs ds : List PlaneTree}

/-- An isomorphism of nodes maps depth-one vertices to depth-one vertices. -/
theorem exists_childIdx (e : Iso (node cs) (node ds)) (i : Fin cs.length) :
    ∃ j, e.1 (childV i (rootV (cs.get i))) = childV j (rootV (ds.get j)) := by
  have hpar : parentV (e.1 (childV i (rootV (cs.get i)))) = rootV (node ds) := by
    rw [← e.2, parentV_childV_rootV, Iso.root_eq]
  rcases parentV_eq_root_cases hpar with h | ⟨j, hj⟩
  · exact absurd h (e.apply_ne_root (childV_ne_root i (rootV (cs.get i))))
  · exact ⟨j, hj⟩

/-- Index of the child onto which `e` maps child `i`. -/
noncomputable def childIdx (e : Iso (node cs) (node ds)) (i : Fin cs.length) : Fin ds.length :=
  (exists_childIdx e i).choose

theorem childIdx_spec (e : Iso (node cs) (node ds)) (i : Fin cs.length) :
    e.1 (childV i (rootV (cs.get i)))
      = childV (childIdx e i) (rootV (ds.get (childIdx e i))) :=
  (exists_childIdx e i).choose_spec

/-- `e` maps the whole subtree below child `i` into the subtree below child
`childIdx e i`. -/
theorem exists_childV_image (e : Iso (node cs) (node ds)) (i : Fin cs.length)
    (v : VPos (cs.get i)) : ∃ w, e.1 (childV i v) = childV (childIdx e i) w := by
  induction hn : v.1.length generalizing v with
  | zero =>
    have hv : v = rootV (cs.get i) := Subtype.ext (List.length_eq_zero_iff.mp hn)
    subst hv
    exact ⟨_, childIdx_spec e i⟩
  | succ n ih =>
    have hvne : v ≠ rootV (cs.get i) := by
      rw [ne_root_iff]
      intro h0
      rw [h0] at hn
      exact Nat.succ_ne_zero n hn.symm
    obtain ⟨w', hw'⟩ := ih (parentV v)
      (by show v.1.dropLast.length = n; rw [List.length_dropLast, hn]; omega)
    have hpar : parentV (e.1 (childV i v)) = childV (childIdx e i) w' := by
      rw [← e.2, parentV_childV i hvne, hw']
    exact exists_childV_of_parentV_eq hpar

/-- The action of `e` inside child `i`, expressed in child `childIdx e i`. -/
noncomputable def childMap (e : Iso (node cs) (node ds)) (i : Fin cs.length)
    (v : VPos (cs.get i)) : VPos (ds.get (childIdx e i)) :=
  (exists_childV_image e i v).choose

theorem childMap_spec (e : Iso (node cs) (node ds)) (i : Fin cs.length) (v : VPos (cs.get i)) :
    e.1 (childV i v) = childV (childIdx e i) (childMap e i v) :=
  (exists_childV_image e i v).choose_spec

theorem childMap_root (e : Iso (node cs) (node ds)) (i : Fin cs.length) :
    childMap e i (rootV (cs.get i)) = rootV (ds.get (childIdx e i)) := by
  have h1 := childMap_spec e i (rootV (cs.get i))
  rw [childIdx_spec e i] at h1
  exact (childV_inj_snd h1).symm

theorem childIdx_symm_childIdx (e : Iso (node cs) (node ds)) (i : Fin cs.length) :
    childIdx e.symm (childIdx e i) = i := by
  have h2 := childIdx_spec e.symm (childIdx e i)
  rw [← childIdx_spec e i, Iso.symm_apply_apply] at h2
  exact (childV_inj_idx h2).symm

/-- The permutation of children induced by an isomorphism of nodes. -/
noncomputable def childEquiv (e : Iso (node cs) (node ds)) : Fin cs.length ≃ Fin ds.length where
  toFun := childIdx e
  invFun := childIdx e.symm
  left_inv := childIdx_symm_childIdx e
  right_inv j := by
    have h := childIdx_symm_childIdx e.symm j
    rwa [Iso.symm_symm] at h

end Split

section Split2
variable {cs ds : List PlaneTree}

theorem exists_childMap_preimage (e : Iso (node cs) (node ds)) (i : Fin cs.length)
    (w : VPos (ds.get (childIdx e i))) :
    ∃ v : VPos (cs.get i), e.1 (childV i v) = childV (childIdx e i) w := by
  have hne : e.symm.1 (childV (childIdx e i) w) ≠ rootV (node cs) :=
    e.symm.apply_ne_root (childV_ne_root _ _)
  rcases vpos_node_cases_or (e.symm.1 (childV (childIdx e i) w)) with h | ⟨i', v', hv'⟩
  · exact absurd h hne
  · have himg : e.1 (childV i' v') = childV (childIdx e i) w := by
      rw [← hv', Iso.apply_symm_apply]
    have hidx : childIdx e i = childIdx e i' := by
      have h2 := childMap_spec e i' v'
      rw [himg] at h2
      exact childV_inj_idx h2
    have hii : i' = i := by
      have h3 := congrArg (childIdx e.symm) hidx
      rw [childIdx_symm_childIdx, childIdx_symm_childIdx] at h3
      exact h3.symm
    subst hii
    exact ⟨v', himg⟩

/-- The isomorphism induced by `e` from child `i` onto child `childEquiv e i`. -/
noncomputable def childIso (e : Iso (node cs) (node ds)) (i : Fin cs.length) :
    Iso (cs.get i) (ds.get (childEquiv e i)) := by
  refine ⟨{ toFun := childMap e i
            invFun := fun w => (exists_childMap_preimage e i w).choose
            left_inv := ?_, right_inv := ?_ }, ?_⟩
  · intro v
    have hch := (exists_childMap_preimage e i (childMap e i v)).choose_spec
    exact childV_inj_snd (e.1.injective (hch.trans (childMap_spec e i v).symm))
  · intro w
    have hch := (exists_childMap_preimage e i w).choose_spec
    rw [childMap_spec e i _] at hch
    exact childV_inj_snd hch
  · intro v
    show childMap e i (parentV v) = parentV (childMap e i v)
    by_cases hv : v = rootV (cs.get i)
    · subst hv
      rw [parentV_rootV, childMap_root, parentV_rootV]
    · have hMapNe : childMap e i v ≠ rootV (ds.get (childIdx e i)) := by
        intro h0
        apply hv
        have hsp := childMap_spec e i v
        rw [h0, ← childIdx_spec e i] at hsp
        exact childV_inj_snd (e.1.injective hsp)
      have h1 := childMap_spec e i (parentV v)
      have h2 : e.1 (childV i (parentV v))
          = childV (childIdx e i) (parentV (childMap e i v)) := by
        rw [← parentV_childV i hv, e.2, childMap_spec e i v,
          parentV_childV (childIdx e i) hMapNe]
      rw [h1] at h2
      exact childV_inj_snd h2

@[simp] theorem childIso_apply (e : Iso (node cs) (node ds)) (i : Fin cs.length)
    (v : VPos (cs.get i)) : (childIso e i).1 v = childMap e i v := rfl

@[simp] theorem childEquiv_apply (e : Iso (node cs) (node ds)) (i : Fin cs.length) :
    childEquiv e i = childIdx e i := rfl

/-- Splitting is a section of grafting. -/
theorem graft_childEquiv_childIso (e : Iso (node cs) (node ds)) :
    graft (childEquiv e) (childIso e) = e := by
  apply Iso.ext
  intro v
  induction v using vpos_node_cases with
  | hroot => rw [graft_apply_root, Iso.root_eq]
  | hchild i w =>
    rw [graft_apply_childV, childIso_apply]
    show childV (childIdx e i) (childMap e i w) = e.1 (childV i w)
    exact (childMap_spec e i w).symm

end Split2

section Count
variable {cs ds : List PlaneTree}

theorem graft_injective :
    Function.Injective (fun x : Σ π : Fin cs.length ≃ Fin ds.length,
      ∀ i, Iso (cs.get i) (ds.get (π i)) => graft x.1 x.2) := by
  rintro ⟨π, F⟩ ⟨π', F'⟩ h
  have hπ : π = π' := by
    apply Equiv.ext
    intro i
    have h1 := congrArg (fun e : Iso (node cs) (node ds) =>
      e.1 (childV i (rootV (cs.get i)))) h
    rw [graft_apply_childV, graft_apply_childV, Iso.root_eq, Iso.root_eq] at h1
    exact childV_inj_idx h1
  subst hπ
  suffices hF : F = F' by rw [hF]
  funext i
  apply Iso.ext
  intro v
  have h1 := congrArg (fun e : Iso (node cs) (node ds) => e.1 (childV i v)) h
  rw [graft_apply_childV, graft_apply_childV] at h1
  exact childV_inj_snd h1

theorem graft_surjective :
    Function.Surjective (fun x : Σ π : Fin cs.length ≃ Fin ds.length,
      ∀ i, Iso (cs.get i) (ds.get (π i)) => graft x.1 x.2) := fun e =>
  ⟨⟨childEquiv e, childIso e⟩, graft_childEquiv_childIso e⟩

/-- Master counting step: isomorphisms of nodes are counted by a child
permutation together with per-child isomorphisms. -/
theorem nat_card_iso_node :
    Nat.card (Iso (node cs) (node ds))
      = ∑ π : Fin cs.length ≃ Fin ds.length,
          ∏ i, Nat.card (Iso (cs.get i) (ds.get (π i))) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨graft_injective (cs := cs) (ds := ds),
    graft_surjective⟩), Nat.card_sigma]
  exact Finset.sum_congr rfl fun π _ => Nat.card_pi

end Count

/-- Torsor step: a single isomorphism `s ≅ t` makes the isomorphisms a torsor
under the self-isomorphisms of `s`. -/
theorem nat_card_iso_of_nonempty {s t : PlaneTree} (h : Nonempty (Iso s t)) :
    Nat.card (Iso s t) = Nat.card (Iso s s) := by
  obtain ⟨e0⟩ := h
  refine Nat.card_congr ⟨fun f => f.trans e0.symm, fun g => g.trans e0, ?_, ?_⟩
  · intro f
    apply Iso.ext
    intro v
    simp
  · intro g
    apply Iso.ext
    intro v
    simp

/-! ### Permutations of the children list give isomorphisms -/

/-- Extend an index bijection by fixing a new head index `0`. -/
def finExtend {n m : ℕ} (σ : Fin n ≃ Fin m) : Fin (n + 1) ≃ Fin (m + 1) where
  toFun := Fin.cases 0 fun i => (σ i).succ
  invFun := Fin.cases 0 fun j => (σ.symm j).succ
  left_inv i := by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => show Fin.cases 0 _ (σ i).succ = i.succ; simp
  right_inv j := by
    induction j using Fin.cases with
    | zero => rfl
    | succ j => show Fin.cases 0 _ (σ.symm j).succ = j.succ; simp

/-- A permutation of a list of trees induces an isomorphism of the nodes. -/
theorem iso_of_perm : ∀ {l l' : List PlaneTree}, l.Perm l' →
    Nonempty (Iso (node l) (node l'))
  | _, _, List.Perm.nil => ⟨Iso.refl _⟩
  | _, _, List.Perm.cons x h => by
    obtain ⟨e⟩ := iso_of_perm h
    exact ⟨graft (finExtend (childEquiv e)) (Fin.cases (Iso.refl x) fun i => childIso e i)⟩
  | _, _, List.Perm.swap x y l => by
    have h0 : (Equiv.swap (0 : Fin (l.length + 2)) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have h1 : (Equiv.swap (0 : Fin (l.length + 2)) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    have hs : ∀ i : Fin l.length,
        (Equiv.swap (0 : Fin (l.length + 2)) 1) i.succ.succ = i.succ.succ := by
      intro i
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · exact Fin.succ_ne_zero _
      · intro heq
        have hv := congrArg Fin.val heq
        rw [Fin.val_one] at hv
        simp only [Fin.val_succ] at hv
        omega
    exact ⟨graft (Equiv.swap 0 1)
      (Fin.cases (Iso.congr rfl (congrArg _ h0.symm) (Iso.refl y))
        (Fin.cases (Iso.congr rfl (congrArg _ h1.symm) (Iso.refl x))
          fun i => Iso.congr rfl (congrArg _ (hs i).symm) (Iso.refl (l.get i))))⟩
  | _, _, List.Perm.trans h1 h2 => by
    obtain ⟨e1⟩ := iso_of_perm h1
    obtain ⟨e2⟩ := iso_of_perm h2
    exact ⟨e1.trans e2⟩

/-! ### Counting values of a list function via index fibers -/

theorem count_ofFn {β : Type} [BEq β] [LawfulBEq β] [DecidableEq β] :
    ∀ {n : ℕ} (g : Fin n → β) (b : β),
      (List.ofFn g).count b = (Finset.univ.filter fun i => g i = b).card
  | 0, g, b => by simp
  | n + 1, g, b => by
    rw [List.ofFn_succ, List.count_cons, count_ofFn (fun i => g i.succ) b,
      Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    simp only [beq_iff_eq]
    omega

theorem map_eq_ofFn {α β : Type} (l : List α) (f : α → β) :
    l.map f = List.ofFn fun i => f (l.get i) := by
  conv_lhs => rw [← List.ofFn_getElem (xs := l), List.map_ofFn]
  rfl

theorem count_map_get {α β : Type} [BEq β] [LawfulBEq β] [DecidableEq β]
    (l : List α) (f : α → β) (b : β) :
    (l.map f).count b = (Finset.univ.filter fun i : Fin l.length => f (l.get i) = b).card := by
  rw [map_eq_ofFn, count_ofFn]

/-- `canonList` entries. -/
theorem canonList_length (cs : List PlaneTree) : (canonList cs).length = cs.length := by
  rw [canonList_eq_map, List.length_map]

theorem canonList_getElem (cs : List PlaneTree) (i : ℕ) (h : i < (canonList cs).length)
    (h' : i < cs.length) : (canonList cs)[i] = canon cs[i] := by
  simp only [canonList_eq_map, List.getElem_map]

/-- Canonicalization does not change the unordered tree. -/
theorem nonempty_iso_canon : ∀ t : PlaneTree, Nonempty (Iso t (canon t))
  | node cs => by
    have F : ∀ i : Fin cs.length,
        Iso (cs.get i) ((canonList cs).get (finCongr (canonList_length cs).symm i)) := by
      intro i
      have hne := nonempty_iso_canon (cs.get i)
      exact Iso.congr rfl
        (canonList_getElem cs i.1 (by rw [canonList_length]; exact i.2) i.2).symm hne.some
    have h1 : Iso (node cs) (node (canonList cs)) :=
      graft (finCongr (canonList_length cs).symm) F
    have h2 : Nonempty (Iso (node (canonList cs))
        (node ((canonList cs).insertionSort KeyLe))) :=
      iso_of_perm (List.perm_insertionSort KeyLe (canonList cs)).symm
    exact ⟨h1.trans h2.some⟩
termination_by t => sizeOf t
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

/-- Isomorphic trees have equal canonical forms. -/
theorem canon_eq_of_iso : ∀ (s t : PlaneTree), Iso s t → canon s = canon t
  | node as, node bs, e => by
    have hchild : ∀ i : Fin as.length,
        canon (as.get i) = canon (bs.get (childEquiv e i)) :=
      fun i => canon_eq_of_iso (as.get i) (bs.get (childEquiv e i)) (childIso e i)
    show node ((canonList as).insertionSort KeyLe)
      = node ((canonList bs).insertionSort KeyLe)
    congr 1
    apply List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _)
      (List.pairwise_insertionSort _ _)
    refine ((List.perm_insertionSort _ _).trans ?_).trans
      (List.perm_insertionSort KeyLe (canonList bs)).symm
    rw [canonList_eq_map, canonList_eq_map, List.perm_iff_count]
    intro a
    rw [count_map_get, count_map_get]
    refine Finset.card_bij (fun i _ => childEquiv e i) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, (hchild i).symm.trans hi.2⟩
    · intro i _ j _ hij
      exact (childEquiv e).injective hij
    · intro j hj
      rw [Finset.mem_filter] at hj
      refine ⟨(childEquiv e).symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [hchild ((childEquiv e).symm j), Equiv.apply_symm_apply]
        exact hj.2
      · exact Equiv.apply_symm_apply _ _
termination_by s _ => sizeOf s
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem as i)
  simp only [node.sizeOf_spec]
  omega

/-! ### Permutations preserving a classification -/

section FiberPerm
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq κ] (f : ι → κ)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem fiberPerm_congr (u : ∀ k : κ, Equiv.Perm {i // f i = k}) {k k' : κ} (h : k = k')
    (x : ι) (hx : f x = k) (hx' : f x = k') :
    ((u k) ⟨x, hx⟩).1 = ((u k') ⟨x, hx'⟩).1 := by subst h; rfl

/-- Assemble a family of fiber permutations into a permutation of the base. -/
def assemblePerm (u : ∀ k : κ, Equiv.Perm {i // f i = k}) : Equiv.Perm ι where
  toFun i := ((u (f i)) ⟨i, rfl⟩).1
  invFun i := ((u (f i)).symm ⟨i, rfl⟩).1
  left_inv i := by
    have hfi : f (((u (f i)) ⟨i, rfl⟩).1) = f i := ((u (f i)) ⟨i, rfl⟩).2
    have step1 := fiberPerm_congr f (fun k => (u k).symm) hfi (((u (f i)) ⟨i, rfl⟩).1) rfl hfi
    have step2 : (⟨((u (f i)) ⟨i, rfl⟩).1, hfi⟩ : {x // f x = f i}) = (u (f i)) ⟨i, rfl⟩ :=
      Subtype.ext rfl
    dsimp only
    rw [step1, step2, Equiv.symm_apply_apply]
  right_inv i := by
    have hfi : f (((u (f i)).symm ⟨i, rfl⟩).1) = f i := ((u (f i)).symm ⟨i, rfl⟩).2
    have step1 := fiberPerm_congr f u hfi (((u (f i)).symm ⟨i, rfl⟩).1) rfl hfi
    have step2 : (⟨((u (f i)).symm ⟨i, rfl⟩).1, hfi⟩ : {x // f x = f i})
        = (u (f i)).symm ⟨i, rfl⟩ := Subtype.ext rfl
    dsimp only
    rw [step1, step2, Equiv.apply_symm_apply]

/-- Permutations preserving the classification `f` are families of
permutations of the fibers of `f`. -/
def fiberPermEquiv : {π : Equiv.Perm ι // ∀ i, f (π i) = f i}
    ≃ ∀ k : κ, Equiv.Perm {i // f i = k} where
  toFun πh k := (πh.1).subtypePerm fun x => by rw [πh.2 x]
  invFun u := ⟨assemblePerm f u, fun i => ((u (f i)) ⟨i, rfl⟩).2⟩
  left_inv πh := Subtype.ext (Equiv.ext fun i => rfl)
  right_inv u := by
    funext k
    apply Equiv.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    show assemblePerm f u x = ((u k) ⟨x, hx⟩).1
    exact fiberPerm_congr f u hx x rfl hx

theorem nat_card_fiber_perms [Fintype κ] :
    Nat.card {π : Equiv.Perm ι // ∀ i, f (π i) = f i}
      = ∏ k : κ, (Nat.card {i // f i = k}).factorial := by
  rw [Nat.card_congr (fiberPermEquiv f), Nat.card_pi]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm]

theorem nat_card_pres_perms {κ' : Type} [DecidableEq κ'] (g : ι → κ') :
    Nat.card {π : Equiv.Perm ι // ∀ i, g (π i) = g i}
      = ∏ k ∈ Finset.univ.image g, (Nat.card {i // g i = k}).factorial := by
  let g' : ι → ↥(Finset.univ.image g) :=
    fun i => ⟨g i, Finset.mem_image_of_mem g (Finset.mem_univ i)⟩
  have h1 : {π : Equiv.Perm ι // ∀ i, g (π i) = g i}
      ≃ {π : Equiv.Perm ι // ∀ i, g' (π i) = g' i} :=
    Equiv.subtypeEquivRight fun π =>
      ⟨fun h i => Subtype.ext (h i), fun h i => congrArg Subtype.val (h i)⟩
  rw [Nat.card_congr h1, nat_card_fiber_perms g']
  have h2 : ∀ k : ↥(Finset.univ.image g),
      (Nat.card {i // g' i = k}).factorial = (Nat.card {i // g i = k.1}).factorial := by
    intro k
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩)
  simp only [h2]
  exact Finset.prod_coe_sort (Finset.univ.image g)
    (fun x => (Nat.card {i // g i = x}).factorial)

end FiberPerm

/-! ### Runs of key-equal elements in a sorted list -/

theorem go_pairwise : ∀ (ds : List PlaneTree) (c : PlaneTree) (k : ℕ),
    (c :: ds).Pairwise KeyLe →
    runsProdFactorial.go c k ds
      = (k + ((ds.map key).count (key c))).factorial
        * ∏ j ∈ ((ds.map key).toFinset).erase (key c), ((ds.map key).count j).factorial
  | [], c, k, _ => by simp [runsProdFactorial.go]
  | d :: ds, c, k, h => by
    have hcd : KeyLe c d := (List.pairwise_cons.mp h).1 d (List.mem_cons_self ..)
    have htail : (d :: ds).Pairwise KeyLe := (List.pairwise_cons.mp h).2
    by_cases hkey : key c = key d
    · have hgo : runsProdFactorial.go c k (d :: ds) = runsProdFactorial.go c (k + 1) ds := by
        rw [runsProdFactorial.go, if_pos (beq_iff_eq.mpr hkey)]
      have hcds : (c :: ds).Pairwise KeyLe := by
        rw [List.pairwise_cons] at h ⊢
        exact ⟨fun b hb => h.1 b (List.mem_cons_of_mem d hb), (List.pairwise_cons.mp h.2).2⟩
      rw [hgo, go_pairwise ds c (k + 1) hcds, List.map_cons]
      have h1 : ((key d :: ds.map key).count (key c)) = (ds.map key).count (key c) + 1 := by
        rw [List.count_cons, if_pos (beq_iff_eq.mpr hkey.symm)]
      have h2 : (key d :: ds.map key).toFinset.erase (key c)
          = (ds.map key).toFinset.erase (key c) := by
        rw [List.toFinset_cons, ← hkey, Finset.erase_insert_eq_erase]
      have h3 : ∏ j ∈ (ds.map key).toFinset.erase (key c),
            ((key d :: ds.map key).count j).factorial
          = ∏ j ∈ (ds.map key).toFinset.erase (key c), ((ds.map key).count j).factorial :=
        Finset.prod_congr rfl fun j hj => by
          rw [List.count_cons, if_neg (fun hcon =>
            (Finset.mem_erase.mp hj).1 ((beq_iff_eq.mp hcon).symm.trans hkey.symm)),
            Nat.add_zero]
      rw [h1, h2, h3]
      congr 2
      omega
    · have hgo : runsProdFactorial.go c k (d :: ds)
          = k.factorial * runsProdFactorial.go d 1 ds := by
        rw [runsProdFactorial.go, if_neg (by simp [beq_iff_eq, hkey])]
      have hnotmem : key c ∉ (key d :: ds.map key) := by
        have hn := key_notMem_map_of_pairwise h hkey
        rwa [List.map_cons] at hn
      rw [hgo, go_pairwise ds d 1 htail, List.map_cons]
      have h1 : ((key d :: ds.map key).count (key c)) = 0 :=
        List.count_eq_zero_of_not_mem hnotmem
      have h2 : (key d :: ds.map key).toFinset.erase (key c)
          = (key d :: ds.map key).toFinset :=
        Finset.erase_eq_of_notMem (by rwa [List.mem_toFinset])
      have hmem : key d ∈ (key d :: ds.map key).toFinset := by
        rw [List.mem_toFinset]; exact List.mem_cons_self ..
      have h4 : (key d :: ds.map key).count (key d) = 1 + (ds.map key).count (key d) := by
        rw [List.count_cons, if_pos (beq_iff_eq.mpr rfl)]; omega
      have h5 : (key d :: ds.map key).toFinset.erase (key d)
          = (ds.map key).toFinset.erase (key d) := by
        rw [List.toFinset_cons, Finset.erase_insert_eq_erase]
      have h6 : ∏ j ∈ (ds.map key).toFinset.erase (key d),
            ((key d :: ds.map key).count j).factorial
          = ∏ j ∈ (ds.map key).toFinset.erase (key d), ((ds.map key).count j).factorial :=
        Finset.prod_congr rfl fun j hj => by
          rw [List.count_cons, if_neg (fun hcon =>
            (Finset.mem_erase.mp hj).1 ((beq_iff_eq.mp hcon).symm)), Nat.add_zero]
      rw [h1, Nat.add_zero, h2, ← Finset.mul_prod_erase _ _ hmem, h4, h5, h6]

/-- `runsProdFactorial` of a `KeyLe`-pairwise list is the product of the
factorials of the key multiplicities. -/
theorem runsProdFactorial_pairwise {l : List PlaneTree} (h : l.Pairwise KeyLe) :
    runsProdFactorial l
      = ∏ j ∈ (l.map key).toFinset, ((l.map key).count j).factorial := by
  match l with
  | [] => simp [runsProdFactorial]
  | c :: ds =>
    rw [runsProdFactorial, go_pairwise ds c 1 h, List.map_cons]
    have hmem : key c ∈ (key c :: ds.map key).toFinset := by
      rw [List.mem_toFinset]; exact List.mem_cons_self ..
    have h4 : (key c :: ds.map key).count (key c) = 1 + (ds.map key).count (key c) := by
      rw [List.count_cons, if_pos (beq_iff_eq.mpr rfl)]; omega
    have h5 : (key c :: ds.map key).toFinset.erase (key c)
        = (ds.map key).toFinset.erase (key c) := by
      rw [List.toFinset_cons, Finset.erase_insert_eq_erase]
    have h6 : ∏ j ∈ (ds.map key).toFinset.erase (key c),
          ((key c :: ds.map key).count j).factorial
        = ∏ j ∈ (ds.map key).toFinset.erase (key c), ((ds.map key).count j).factorial :=
      Finset.prod_congr rfl fun j hj => by
        rw [List.count_cons, if_neg (fun hcon =>
          (Finset.mem_erase.mp hj).1 ((beq_iff_eq.mp hcon).symm)), Nat.add_zero]
    rw [← Finset.mul_prod_erase _ _ hmem, h4, h5, h6]

/-! ### Assembly helpers -/

theorem prod_ite_zero {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (a : Fin n → ℕ) :
    (∏ i, if p i then a i else 0) = if (∀ i, p i) then ∏ i, a i else 0 := by
  by_cases hall : ∀ i, p i
  · rw [if_pos hall]
    exact Finset.prod_congr rfl fun i _ => if_pos (hall i)
  · rw [if_neg hall]
    rw [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem nat_card_subtype_filter {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    Nat.card {x // P x} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_ite_eq_card_mul {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (C : ℕ) :
    (∑ x, if P x then C else 0) = Nat.card {x // P x} * C := by
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, nat_card_subtype_filter]

/-- The product of the children's `autCard`s over `Fin`-indices. -/
theorem prod_autCard_get (cs : List PlaneTree) :
    (∏ i : Fin cs.length, autCard (cs.get i)) = autCardList cs := by
  rw [autCardList_eq_map, map_eq_ofFn, List.prod_ofFn]

/-- The canon-class-preserving permutation count is the run-factorial product
of the canonically sorted children. -/
theorem pres_card_eq_runs (cs : List PlaneTree) :
    Nat.card {π : Fin cs.length ≃ Fin cs.length // ∀ i, canon (cs.get (π i)) = canon (cs.get i)}
      = runsProdFactorial ((canonList cs).insertionSort KeyLe) := by
  show Nat.card {π : Equiv.Perm (Fin cs.length) //
    ∀ i, canon (cs.get (π i)) = canon (cs.get i)} = _
  rw [nat_card_pres_perms (fun i => canon (cs.get i)),
    runsProdFactorial_pairwise (List.pairwise_insertionSort KeyLe (canonList cs))]
  have hperm : (((canonList cs).insertionSort KeyLe).map key).Perm
      (cs.map (key ∘ canon)) := by
    have h1 := (List.perm_insertionSort KeyLe (canonList cs)).map key
    have h2 : (canonList cs).map key = cs.map (key ∘ canon) := by
      rw [canonList_eq_map, List.map_map]
    rwa [h2] at h1
  have hset : (((canonList cs).insertionSort KeyLe).map key).toFinset
      = (cs.map (key ∘ canon)).toFinset :=
    Finset.ext fun a => by rw [List.mem_toFinset, List.mem_toFinset, hperm.mem_iff]
  have hcnt : ∀ j, (((canonList cs).insertionSort KeyLe).map key).count j
      = (cs.map (key ∘ canon)).count j := hperm.count_eq
  rw [hset]
  simp only [hcnt]
  refine Finset.prod_bij (fun k _ => key k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨i, _, rfl⟩ := hk
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨cs.get i, List.get_mem cs i, rfl⟩
  · intro k1 _ k2 _ hk
    exact key_injective hk
  · intro j hj
    rw [List.mem_toFinset] at hj
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hj
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    exact ⟨canon (cs.get i), Finset.mem_image_of_mem _ (Finset.mem_univ i), rfl⟩
  · intro k hk
    congr 1
    rw [count_map_get, nat_card_subtype_filter]
    congr 1
    apply Finset.filter_congr
    intro i _
    show (canon (cs.get i) = k) ↔ ((key ∘ canon) (cs.get i) = key k)
    exact ⟨fun h => by rw [Function.comp_apply, h], fun h => key_injective h⟩

/-! ## The D-hepp cross-check: `|Aut t| = t.autCard` -/

/-- Blueprint obligation (D-hepp cross-check).

The order of the automorphism group realized as parent-commuting vertex
permutations (`Aut`) equals the recursive product formula `autCard` (run
factorials on canonically sorted children × the children's own counts).
Proof: strong induction on `t`; an automorphism of
`node cs` fixes the root, permutes the depth-1 vertices by some `σ` with
`canon cs[σ i] = canon cs[i]` and restricts to subtree isomorphisms, giving an
equivalence of `Aut (node cs)` with (canon-class-preserving `σ`) × (a family of
subtree isomorphism sets, each of cardinality `autCard cs[i]`); the `σ`-factor
has `runsProdFactorial` many elements by key-injectivity. Kernel-checked
instances follow below. -/
theorem card_aut_eq_autCard : ∀ t : PlaneTree, Fintype.card (Aut t) = t.autCard
  | node cs => by
    have IH : ∀ i : Fin cs.length, Fintype.card (Aut (cs.get i)) = (cs.get i).autCard :=
      fun i => card_aut_eq_autCard (cs.get i)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (isoAutEquiv (node cs)),
      nat_card_iso_node]
    have hfac : ∀ (π : Fin cs.length ≃ Fin cs.length) (i : Fin cs.length),
        Nat.card (Iso (cs.get i) (cs.get (π i)))
          = if canon (cs.get (π i)) = canon (cs.get i) then autCard (cs.get i) else 0 := by
      intro π i
      by_cases hc : canon (cs.get (π i)) = canon (cs.get i)
      · rw [if_pos hc]
        have hne : Nonempty (Iso (cs.get i) (cs.get (π i))) :=
          ⟨((nonempty_iso_canon (cs.get i)).some.trans (Iso.ofEq hc.symm)).trans
            (nonempty_iso_canon (cs.get (π i))).some.symm⟩
        rw [nat_card_iso_of_nonempty hne, Nat.card_congr (isoAutEquiv (cs.get i)),
          Nat.card_eq_fintype_card, IH i]
      · rw [if_neg hc]
        have hemp : IsEmpty (Iso (cs.get i) (cs.get (π i))) := by
          by_contra hcon
          rw [not_isEmpty_iff] at hcon
          exact hc (canon_eq_of_iso _ _ hcon.some).symm
        exact Nat.card_of_isEmpty
    have hsum : ∀ π : Fin cs.length ≃ Fin cs.length,
        (∏ i, Nat.card (Iso (cs.get i) (cs.get (π i))))
          = if (∀ i, canon (cs.get (π i)) = canon (cs.get i))
            then ∏ i, autCard (cs.get i) else 0 := by
      intro π
      simp only [hfac]
      exact prod_ite_zero _ _
    simp only [hsum]
    rw [sum_ite_eq_card_mul, pres_card_eq_runs, prod_autCard_get, autCard]
termination_by t => sizeOf t
decreasing_by
  have hmem := List.sizeOf_lt_of_mem (List.get_mem cs i)
  simp only [node.sizeOf_spec]
  omega

/-- Cross-check instance, kernel-checked: the cherry, `|Aut| = 2 = autCard`. -/
example : Fintype.card (Aut cherry) = cherry.autCard := by decide

-- Cross-check instance, kernel-checked: the two-cherry tree,
-- `|Aut| = 8 = 2! · 2 · 2 = autCard` (all 5040 vertex permutations examined).
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : Fintype.card (Aut (node [cherry, cherry])) = (node [cherry, cherry]).autCard := by
  decide

end PlaneTree

end Anderson4D
