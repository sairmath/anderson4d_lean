import Anderson4D.Combinatorics.AcrossPairing
import Anderson4D.Combinatorics.Pairing
import Anderson4D.Combinatorics.TreeCountReal
import Anderson4D.HeppTree.Admissible
import Anderson4D.PermSum.Words

/-!
# Master decomposition of the lattice chain sum over marked Hepp trees (node R-decomp)

Paper (5.6)–(5.11) of arXiv:2607.10105, packaging the counting sum (5.5) into
tree-indexed pieces, in the `paperSum` normalization.

* `rdec_boundedTuples`, `latticeChainSum` — the (5.5)-type sum over `n`-tuples
  of lattice points in the box `[-M, M]⁴`.
* `RealizesTuple`, `realizedTuples` — the realization class of a marked Hepp
  tree `(t, Nm, mu)` (Def 5.4, multiplicity form): tuples `y = z ∘ w` for an
  admissible embedding `z` and an assignment word `w` with letter
  multiplicities `mu.m` (`validWords`).
* `card_realizedTuples_le` — trivial volume bound (sharp (5.6)–(5.7) form is
  node P-5.6).
* `rdec_exists_realizing_marked_tree` — the general multi-scale Lemma 5.5
  (single-linkage dyadic merging), proved by recursion on cluster partitions.
* `exists_realizing_tree` — every bounded tuple with all values repeated
  (`m_ℓ ≥ 2` of Def 5.1 forces repetition) lies in some realization class with
  at most `n` leaves.
* `rdec_treeEnum`, `latticeChainSum_le_treeSum` — the (5.10)-shaped weak
  bridge: the repeated-tuple part of the chain sum is dominated by the sum
  over valid trees with at most `n` leaves of their realized-tuple sums.
-/

namespace Anderson4D

open PlaneTree

/-! ## The bounded-tuple sum (5.5) -/

/-- Tuples of `n` lattice points with every coordinate in `[-M, M]`. -/
noncomputable def rdec_boundedTuples (M n : ℕ) : Finset (Fin n → Fin 4 → ℤ) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M

@[simp] theorem rdec_mem_boundedTuples {M n : ℕ} {y : Fin n → Fin 4 → ℤ} :
    y ∈ rdec_boundedTuples M n ↔ ∀ j i, |y j i| ≤ (M : ℤ) := by
  simp [rdec_boundedTuples, abs_le]

/-- The lattice chain sum (5.5): a statistic `F` summed over all bounded tuples. -/
noncomputable def latticeChainSum (M n : ℕ) (F : (Fin n → Fin 4 → ℤ) → ℝ) : ℝ :=
  ∑ y ∈ rdec_boundedTuples M n, F y

/-- The box volume count: there are `(2M+1)^{4n}` bounded tuples. -/
theorem rdec_card_boundedTuples (M n : ℕ) :
    (rdec_boundedTuples M n).card = (2 * M + 1) ^ (4 * n) := by
  have hIcc : (Finset.Icc (-(M : ℤ)) M).card = 2 * M + 1 := by
    rw [Int.card_Icc]; omega
  simp only [rdec_boundedTuples, Fintype.card_piFinset, hIcc, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [pow_mul]

/-- Bounded tuples in which every value occurs at least twice.  Def 5.1's leaf
multiplicities `m_ℓ ≥ 2` mean realization classes only contain such tuples
(in the paper these are the tuples surviving the expectation of the
mean-zero chain). -/
noncomputable def rdec_repeatedTuples (M n : ℕ) : Finset (Fin n → Fin 4 → ℤ) :=
  (rdec_boundedTuples M n).filter fun y =>
    ∀ j, 2 ≤ (Finset.univ.filter fun k => y k = y j).card

@[simp] theorem rdec_mem_repeatedTuples {M n : ℕ} {y : Fin n → Fin 4 → ℤ} :
    y ∈ rdec_repeatedTuples M n ↔
      y ∈ rdec_boundedTuples M n ∧
        ∀ j, 2 ≤ (Finset.univ.filter fun k => y k = y j).card := by
  simp [rdec_repeatedTuples]

/-! ## Realization classes (Def 5.4, multiplicity form) -/

/-- The tuple `y` is realized by the marked tree `(t, Nm, mu)`: some
admissible embedding `z` of the leaves and some assignment word
`w : Fin n → Leaves t` whose letter multiplicities are `mu.m` (membership in
`validWords`, the word structure of §5.5) write `y` as `y j = z (w j)`.
Since every leaf multiplicity is `≥ 2 ≥ 1`, every leaf is hit by `w`, so the
value multiset of `y` is exactly `⋃_ℓ {mu.m ℓ copies of z ℓ}` (Def 5.4,
multiplicity version). -/
def RealizesTuple (t : PlaneTree) (Nm : HeppMarking t) (mu : Multiplicities t)
    (M : ℕ) {n : ℕ} (y : Fin n → Fin 4 → ℤ) : Prop :=
  ∃ (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (w : Fin n → {l // l ∈ Leaves t}),
    IsAdmissible Nm M z ∧
      w ∈ validWords (fun l : {l // l ∈ Leaves t} => mu.m l.1) ∧
      ∀ j, y j = z (w j)

open Classical in
/-- The realization class of `(t, Nm, mu)` inside the bounded tuples. -/
noncomputable def realizedTuples (t : PlaneTree) (Nm : HeppMarking t)
    (mu : Multiplicities t) (M n : ℕ) : Finset (Fin n → Fin 4 → ℤ) :=
  (rdec_boundedTuples M n).filter fun y => RealizesTuple t Nm mu M y

theorem mem_realizedTuples {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {M n : ℕ} {y : Fin n → Fin 4 → ℤ} :
    y ∈ realizedTuples t Nm mu M n ↔
      y ∈ rdec_boundedTuples M n ∧ RealizesTuple t Nm mu M y := by
  classical
  simp [realizedTuples]

/-- Trivial volume-facing bound: a realization class has at most `(2M+1)^{4n}`
tuples.  The sharp (5.6)–(5.7) denominator form is deferred to node P-5.6. -/
theorem card_realizedTuples_le (t : PlaneTree) (Nm : HeppMarking t)
    (mu : Multiplicities t) (M n : ℕ) :
    (realizedTuples t Nm mu M n).card ≤ (2 * M + 1) ^ (4 * n) := by
  classical
  rw [realizedTuples, ← rdec_card_boundedTuples M n]
  exact Finset.card_filter_le _ _

/-! ## Metric helpers -/

/-- Distinct integer vectors are at sup-distance at least `1`. -/
theorem rdec_one_le_znorm {x y : Fin 4 → ℤ} (h : x ≠ y) : (1 : ℝ) ≤ znorm (x - y) := by
  have hne : ∃ i, x i ≠ y i := by
    by_contra hall
    push Not at hall
    exact h (funext hall)
  obtain ⟨i, hi⟩ := hne
  have h1 : (1 : ℤ) ≤ |x i - y i| := Int.one_le_abs (sub_ne_zero.mpr hi)
  have h2 : (1 : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    simpa using this
  exact h2.trans (znorm_sub_coord x y i)

/-- Points of the box `[-M, M]⁴` are at sup-distance at most `2^{M+1}`. -/
theorem rdec_znorm_le_pow {M : ℕ} {x y : Fin 4 → ℤ} (hx : ∀ i, |x i| ≤ (M : ℤ))
    (hy : ∀ i, |y i| ≤ (M : ℤ)) : znorm (x - y) ≤ (2 : ℝ) ^ (M + 1) := by
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by positivity
  rw [znorm, pi_norm_le_iff_of_nonneg hpos]
  intro i
  have hZ : |x i - y i| ≤ (2 * M : ℤ) := by
    have h1 : |x i - y i| ≤ |x i| + |y i| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (x i) (-(y i))
    have h2 := hx i
    have h3 := hy i
    omega
  have hcast : |(x i : ℝ) - (y i : ℝ)| ≤ ((2 * M : ℕ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).mpr hZ
    push_cast at this ⊢
    simpa using this
  have hfin : ((2 * M : ℕ) : ℝ) ≤ (2 : ℝ) ^ (M + 1) := by
    have hM : 2 * M ≤ 2 ^ (M + 1) := by
      have := Nat.lt_two_pow_self (n := M)
      calc 2 * M ≤ 2 * 2 ^ M := by omega
        _ = 2 ^ (M + 1) := (pow_succ' 2 M).symm
    calc ((2 * M : ℕ) : ℝ) ≤ ((2 ^ (M + 1) : ℕ) : ℝ) := by exact_mod_cast hM
      _ = (2 : ℝ) ^ (M + 1) := by push_cast; ring
  calc ‖((x - y) i : ℝ)‖ = |(x i : ℝ) - (y i : ℝ)| := by
        rw [Real.norm_eq_abs]; norm_num [Pi.sub_apply]
    _ ≤ ((2 * M : ℕ) : ℝ) := hcast
    _ ≤ (2 : ℝ) ^ (M + 1) := hfin

/-! ## Realizability with bounded branch exponents (the Lemma 5.5 invariant) -/

/-- `C` is realized by some valid marked Hepp tree with `C.card` leaves whose
branch exponents are all `< N` (the recursion invariant of Lemma 5.5). -/
def rdec_RealizableBelow (M : ℕ) (C : Finset (Fin 4 → ℤ)) (N : ℕ) : Prop :=
  ∃ t : PlaneTree, t.isValid = true ∧ ∃ Nm : HeppMarking t,
    Realizes Nm M C ∧ t.leafCount = C.card ∧ ∀ v ∈ BranchNodes t, Nm.Nexp v < N

theorem rdec_RealizableBelow.mono {M : ℕ} {C : Finset (Fin 4 → ℤ)} {N N' : ℕ}
    (h : rdec_RealizableBelow M C N) (hN : N ≤ N') : rdec_RealizableBelow M C N' := by
  obtain ⟨t, hv, Nm, hr, hc, hb⟩ := h
  exact ⟨t, hv, Nm, hr, hc, fun v hv' => lt_of_lt_of_le (hb v hv') hN⟩

/-- Singletons are realizable below every exponent bound, by the bare leaf. -/
theorem rdec_realizableBelow_singleton (M N : ℕ) (x : Fin 4 → ℤ)
    (hx : ∀ i, |x i| ≤ (M : ℤ)) : rdec_RealizableBelow M {x} N := by
  refine ⟨leaf, rfl, leafMarking 0, realizes_leaf M 0 x hx, ?_, ?_⟩
  · rw [Finset.card_singleton]; decide
  · intro v hv
    exact absurd hv (by simp [branchNodes_leaf])

/-! ## Vertex transport into a `node` (assembly plumbing) -/

theorem rdec_childCount_cons {cs : List PlaneTree} {i : ℕ} {p : Pos}
    (h : i < cs.length) : childCount (node cs) (i :: p) = childCount cs[i] p := by
  simp [childCount, h]

theorem rdec_childCount_childV {cs : List PlaneTree} (i : Fin cs.length)
    (v : VPos (cs.get i)) :
    childCount (node cs) (childV i v).1 = childCount (cs.get i) v.1 := by
  rw [childV_val, rdec_childCount_cons i.2]
  rfl

theorem rdec_root_mem_branchNodes {cs : List PlaneTree} (h : 2 ≤ cs.length) :
    rootV (node cs) ∈ BranchNodes (node cs) :=
  mem_BranchNodes_iff.mpr h

theorem rdec_childV_mem_leaves {cs : List PlaneTree} (i : Fin cs.length)
    (v : VPos (cs.get i)) :
    childV i v ∈ Leaves (node cs) ↔ v ∈ Leaves (cs.get i) := by
  rw [mem_Leaves_iff, mem_Leaves_iff, rdec_childCount_childV]

theorem rdec_childV_mem_branchNodes {cs : List PlaneTree} (i : Fin cs.length)
    (v : VPos (cs.get i)) :
    childV i v ∈ BranchNodes (node cs) ↔ v ∈ BranchNodes (cs.get i) := by
  rw [mem_BranchNodes_iff, mem_BranchNodes_iff, rdec_childCount_childV]

theorem rdec_lcaPath_cons_eq (a : ℕ) (p q : List ℕ) :
    lcaPath (a :: p) (a :: q) = a :: lcaPath p q := by
  simp [lcaPath]

theorem rdec_lcaPath_cons_ne {a b : ℕ} (h : a ≠ b) (p q : List ℕ) :
    lcaPath (a :: p) (b :: q) = [] := by
  simp [lcaPath, h]

theorem rdec_lcaV_childV {cs : List PlaneTree} (i : Fin cs.length)
    (v w : VPos (cs.get i)) :
    lcaV (childV i v) (childV i w) = childV i (lcaV v w) :=
  Subtype.ext (rdec_lcaPath_cons_eq i.1 v.1 w.1)

theorem rdec_lcaV_childV_ne {cs : List PlaneTree} {i j : Fin cs.length} (hij : i ≠ j)
    (v : VPos (cs.get i)) (w : VPos (cs.get j)) :
    lcaV (childV i v) (childV j w) = rootV (node cs) :=
  Subtype.ext (rdec_lcaPath_cons_ne (fun h => hij (Fin.ext h)) v.1 w.1)

theorem rdec_mem_childrenOf_root {cs : List PlaneTree} {w : VPos (node cs)} :
    w ∈ childrenOf (rootV (node cs)) ↔
      ∃ i : Fin cs.length, w = childV i (rootV (cs.get i)) := by
  rw [mem_childrenOf]
  constructor
  · rintro ⟨hlen, -⟩
    obtain ⟨p, hp⟩ := w
    match p, hp, hlen with
    | [i], hp, _ => exact ⟨⟨i, isPos_cons_lt hp⟩, Subtype.ext rfl⟩
    | [], _, hlen => exact absurd hlen (by simp [rootV])
    | a :: b :: q, _, hlen => exact absurd hlen (by simp [rootV])
  · rintro ⟨i, rfl⟩
    exact ⟨rfl, List.nil_prefix⟩

theorem rdec_mem_childrenOf_childV {cs : List PlaneTree} {i : Fin cs.length}
    {u : VPos (cs.get i)} {c : VPos (node cs)} :
    c ∈ childrenOf (childV i u) ↔ ∃ w ∈ childrenOf u, c = childV i w := by
  rw [mem_childrenOf]
  constructor
  · rintro ⟨hlen, hpre⟩
    obtain ⟨p, hp⟩ := c
    match p, hp, hlen, hpre with
    | [], _, _, hpre =>
      exact absurd (List.prefix_nil.mp hpre) (List.cons_ne_nil _ _)
    | a :: q, hp, hlen, hpre =>
      obtain ⟨ha, hq⟩ := List.cons_prefix_cons.mp hpre
      subst ha
      refine ⟨⟨q, isPos_cons_tail hp⟩, mem_childrenOf.mpr ⟨?_, hq⟩, Subtype.ext rfl⟩
      simpa using hlen
  · rintro ⟨w, hw, rfl⟩
    rw [mem_childrenOf] at hw
    refine ⟨by simpa using hw.1, List.cons_prefix_cons.mpr ⟨rfl, hw.2⟩⟩

/-! ## Assembling a marking on `node cs` -/

/-- The exponent function on `node cs`: `N` at the root, the child's own
exponents inside child `i`. -/
def rdec_nodeNexp {cs : List PlaneTree}
    (Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i)) (N : ℕ) :
    VPos (node cs) → ℕ
  | ⟨[], _⟩ => N
  | ⟨i :: p, hp⟩ => (Nms ⟨i, isPos_cons_lt hp⟩).Nexp ⟨p, isPos_cons_tail hp⟩

@[simp] theorem rdec_nodeNexp_root {cs : List PlaneTree}
    (Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i)) (N : ℕ) :
    rdec_nodeNexp Nms N (rootV (node cs)) = N := rfl

@[simp] theorem rdec_nodeNexp_childV {cs : List PlaneTree}
    (Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i)) (N : ℕ)
    (i : Fin cs.length) (v : VPos (cs.get i)) :
    rdec_nodeNexp Nms N (childV i v) = (Nms i).Nexp v := rfl

/-- The assembled Hepp marking on `node cs`: root exponent `N`, child markings
inside the children.  Requires every child branch exponent `< N`. -/
def rdec_nodeMarking {cs : List PlaneTree} {N : ℕ} (hN : 1 ≤ N)
    (Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i))
    (hbelow : ∀ i : Fin cs.length, ∀ v ∈ BranchNodes (cs.get i), (Nms i).Nexp v < N) :
    HeppMarking (node cs) where
  Nexp := rdec_nodeNexp Nms N
  pos := by
    refine vpos_node_cases
      (fun v => v ∈ BranchNodes (node cs) → 1 ≤ rdec_nodeNexp Nms N v) ?_ ?_
    · intro _
      exact hN
    · intro i w hw
      rw [rdec_nodeNexp_childV]
      exact (Nms i).pos w ((rdec_childV_mem_branchNodes i w).mp hw)
  parent_gt := by
    refine vpos_node_cases
      (fun v => v ∈ BranchNodes (node cs) → v ≠ rootV (node cs) →
        rdec_nodeNexp Nms N (parentV v) > rdec_nodeNexp Nms N v) ?_ ?_
    · intro _ hne
      exact absurd rfl hne
    · intro i w hw _
      by_cases hwr : w = rootV (cs.get i)
      · subst hwr
        rw [parentV_childV_rootV, rdec_nodeNexp_root, rdec_nodeNexp_childV]
        exact hbelow i _ ((rdec_childV_mem_branchNodes i _).mp hw)
      · rw [parentV_childV i hwr, rdec_nodeNexp_childV, rdec_nodeNexp_childV]
        exact (Nms i).parent_gt w ((rdec_childV_mem_branchNodes i w).mp hw) hwr

/-! ## Assembling the leaf embedding on `node cs` -/

/-- A leaf of child `i`, embedded as a leaf of the `node`. -/
def rdec_leafUp {cs : List PlaneTree} (i : Fin cs.length)
    (w : {l // l ∈ Leaves (cs.get i)}) : {l // l ∈ Leaves (node cs)} :=
  ⟨childV i w.1, (rdec_childV_mem_leaves i w.1).mpr w.2⟩

/-- Every leaf of a nonempty `node` comes from a child. -/
theorem rdec_leafUp_surj {cs : List PlaneTree} (hlen : 1 ≤ cs.length)
    (l : {l // l ∈ Leaves (node cs)}) : ∃ i w, l = rdec_leafUp i w := by
  obtain ⟨⟨p, hp⟩, hl⟩ := l
  match p, hp, hl with
  | [], _, hl =>
    rw [mem_Leaves_iff] at hl
    have hcs : cs.length = 0 := hl
    omega
  | i :: q, hp, hl =>
    rw [mem_Leaves_iff, rdec_childCount_cons (isPos_cons_lt hp)] at hl
    exact ⟨⟨i, isPos_cons_lt hp⟩, ⟨⟨q, isPos_cons_tail hp⟩, mem_Leaves_iff.mpr hl⟩,
      Subtype.ext (Subtype.ext rfl)⟩

/-- The assembled leaf embedding: on the leaves of child `i` use `zs i`
(junk value `0` at the impossible root-leaf case). -/
def rdec_nodeEmb {cs : List PlaneTree}
    (zs : ∀ i : Fin cs.length, {l // l ∈ Leaves (cs.get i)} → Fin 4 → ℤ) :
    {l // l ∈ Leaves (node cs)} → Fin 4 → ℤ
  | ⟨⟨[], _⟩, _⟩ => 0
  | ⟨⟨i :: p, hp⟩, hl⟩ => zs ⟨i, isPos_cons_lt hp⟩
      ⟨⟨p, isPos_cons_tail hp⟩, by
        rw [mem_Leaves_iff] at hl ⊢
        rw [rdec_childCount_cons (isPos_cons_lt hp)] at hl
        exact hl⟩

@[simp] theorem rdec_nodeEmb_leafUp {cs : List PlaneTree}
    (zs : ∀ i : Fin cs.length, {l // l ∈ Leaves (cs.get i)} → Fin 4 → ℤ)
    (i : Fin cs.length) (w : {l // l ∈ Leaves (cs.get i)}) :
    rdec_nodeEmb zs (rdec_leafUp i w) = zs i w := rfl

/-- Transport of `leavesUnder` along `rdec_leafUp`. -/
theorem rdec_leafUp_mem_leavesUnder {cs : List PlaneTree} {i : Fin cs.length}
    {a : VPos (cs.get i)} {w : {l // l ∈ Leaves (cs.get i)}}
    (hw : w ∈ leavesUnder a) : rdec_leafUp i w ∈ leavesUnder (childV i a) := by
  rw [mem_leavesUnder] at hw ⊢
  exact List.cons_prefix_cons.mpr ⟨rfl, hw⟩

private theorem rdec_isValidList_iff (cs : List PlaneTree) :
    isValidList cs = true ↔ ∀ i : Fin cs.length, (cs.get i).isValid = true := by
  induction cs with
  | nil => simp [isValidList]
  | cons c cs ih =>
    rw [isValidList, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i
      match i with
      | ⟨0, _⟩ => exact h1
      | ⟨k + 1, hk⟩ => exact h2 ⟨k, by simp only [List.length_cons] at hk; omega⟩
    · intro h
      refine ⟨h ⟨0, by simp⟩, fun i => h ⟨i.1 + 1, ?_⟩⟩
      have := i.2
      simp only [List.length_cons]
      omega

private theorem rdec_leafCountList_eq_sum (cs : List PlaneTree) :
    leafCountList cs = ∑ i : Fin cs.length, (cs.get i).leafCount := by
  induction cs with
  | nil => simp [leafCountList]
  | cons c cs ih =>
    rw [leafCountList, ih]
    show c.leafCount + ∑ i, (cs.get i).leafCount
      = ∑ i : Fin (cs.length + 1), ((c :: cs).get i).leafCount
    rw [Fin.sum_univ_succ]
    exact congrArg₂ HAdd.hAdd rfl (Finset.sum_congr rfl fun i _ => rfl)

theorem rdec_scaleN_node_root {cs : List PlaneTree} {N : ℕ} (hN : 1 ≤ N)
    (Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i))
    (hbelow : ∀ i, ∀ v ∈ BranchNodes (cs.get i), (Nms i).Nexp v < N) :
    scaleN (rdec_nodeMarking hN Nms hbelow) (rootV (node cs)) = 2 ^ N := rfl

theorem rdec_scaleN_node_childV {cs : List PlaneTree} {N : ℕ} (hN : 1 ≤ N)
    (Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i))
    (hbelow : ∀ i, ∀ v ∈ BranchNodes (cs.get i), (Nms i).Nexp v < N)
    (i : Fin cs.length) (v : VPos (cs.get i)) :
    scaleN (rdec_nodeMarking hN Nms hbelow) (childV i v) = scaleN (Nms i) v := rfl

private theorem rdec_nodeEmb_inj {cs : List PlaneTree}
    {zs : ∀ i : Fin cs.length, {l // l ∈ Leaves (cs.get i)} → Fin 4 → ℤ}
    {Cs : Fin cs.length → Finset (Fin 4 → ℤ)} (hlen : 1 ≤ cs.length)
    (hinj : ∀ i, Function.Injective (zs i))
    (himg : ∀ i, Finset.univ.image (zs i) = Cs i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Cs i) (Cs j)) :
    Function.Injective (rdec_nodeEmb zs) := by
  intro l l' heq
  obtain ⟨i, w, rfl⟩ := rdec_leafUp_surj hlen l
  obtain ⟨j, w', rfl⟩ := rdec_leafUp_surj hlen l'
  rw [rdec_nodeEmb_leafUp, rdec_nodeEmb_leafUp] at heq
  by_cases hij : i = j
  · subst hij
    rw [hinj i heq]
  · exfalso
    have h1 : zs i w ∈ Cs i := by
      rw [← himg i]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have h2 : zs j w' ∈ Cs j := by
      rw [← himg j]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [heq] at h1
    exact Finset.disjoint_left.mp (hdisj i j hij) h1 h2

private theorem rdec_nodeEmb_image {cs : List PlaneTree}
    {zs : ∀ i : Fin cs.length, {l // l ∈ Leaves (cs.get i)} → Fin 4 → ℤ}
    {Cs : Fin cs.length → Finset (Fin 4 → ℤ)} (hlen : 1 ≤ cs.length)
    (himg : ∀ i, Finset.univ.image (zs i) = Cs i) :
    Finset.univ.image (rdec_nodeEmb zs) = Finset.univ.biUnion Cs := by
  ext x
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, rfl⟩
    obtain ⟨i, w, rfl⟩ := rdec_leafUp_surj hlen l
    rw [rdec_nodeEmb_leafUp]
    refine ⟨i, ?_⟩
    rw [← himg i]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · rintro ⟨i, hx⟩
    rw [← himg i] at hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨rdec_leafUp i w, rdec_nodeEmb_leafUp zs i w⟩

/-- Chains between children of a branch node of a child transport into the
assembled tree. -/
private theorem rdec_linked_childV {cs : List PlaneTree} {N : ℕ} (hN : 1 ≤ N)
    {Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i)}
    {hbelow : ∀ i, ∀ v ∈ BranchNodes (cs.get i), (Nms i).Nexp v < N}
    {zs : ∀ i : Fin cs.length, {l // l ∈ Leaves (cs.get i)} → Fin 4 → ℤ}
    (i : Fin cs.length) (u : VPos (cs.get i))
    (h : LinkedChildren (Nms i) (zs i) u) :
    LinkedChildren (rdec_nodeMarking hN Nms hbelow) (rdec_nodeEmb zs) (childV i u) := by
  intro c hc c' hc'
  obtain ⟨a, ha, rfl⟩ := rdec_mem_childrenOf_childV.mp hc
  obtain ⟨b, hb, rfl⟩ := rdec_mem_childrenOf_childV.mp hc'
  refine Relation.ReflTransGen.lift (childV i) ?_ _ _ (h a ha b hb)
  rintro x y ⟨hx, hy, l₀, hl₀, l₀', hl₀', hd⟩
  refine ⟨rdec_mem_childrenOf_childV.mpr ⟨x, hx, rfl⟩,
    rdec_mem_childrenOf_childV.mpr ⟨y, hy, rfl⟩,
    rdec_leafUp i l₀, rdec_leafUp_mem_leavesUnder hl₀,
    rdec_leafUp i l₀', rdec_leafUp_mem_leavesUnder hl₀', ?_⟩
  rw [rdec_nodeEmb_leafUp, rdec_nodeEmb_leafUp, rdec_scaleN_node_childV]
  exact hd

/-- Cluster chains at scale `2^N` transport to link chains between the root's
children in the assembled tree. -/
private theorem rdec_linked_root {cs : List PlaneTree} {N : ℕ} (hN : 1 ≤ N)
    {Nms : ∀ i : Fin cs.length, HeppMarking (cs.get i)}
    {hbelow : ∀ i, ∀ v ∈ BranchNodes (cs.get i), (Nms i).Nexp v < N}
    {zs : ∀ i : Fin cs.length, {l // l ∈ Leaves (cs.get i)} → Fin 4 → ℤ}
    {Cs : Fin cs.length → Finset (Fin 4 → ℤ)}
    (himg : ∀ i, Finset.univ.image (zs i) = Cs i)
    (hconn : ∀ i j : Fin cs.length, Relation.ReflTransGen
      (fun a b => ∃ x ∈ Cs a, ∃ y ∈ Cs b, znorm (x - y) ≤ (2 : ℝ) ^ N) i j) :
    LinkedChildren (rdec_nodeMarking hN Nms hbelow) (rdec_nodeEmb zs)
      (rootV (node cs)) := by
  intro c hc c' hc'
  obtain ⟨i, rfl⟩ := rdec_mem_childrenOf_root.mp hc
  obtain ⟨j, rfl⟩ := rdec_mem_childrenOf_root.mp hc'
  refine Relation.ReflTransGen.lift
    (fun k : Fin cs.length => childV k (rootV (cs.get k))) ?_ _ _ (hconn i j)
  rintro a b ⟨x, hx, y', hy', hd⟩
  refine ⟨rdec_mem_childrenOf_root.mpr ⟨a, rfl⟩,
    rdec_mem_childrenOf_root.mpr ⟨b, rfl⟩, ?_⟩
  rw [← himg a] at hx
  rw [← himg b] at hy'
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨w', -, rfl⟩ := Finset.mem_image.mp hy'
  refine ⟨rdec_leafUp a w, ?_, rdec_leafUp b w', ?_, ?_⟩
  · rw [mem_leavesUnder]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
  · rw [mem_leavesUnder]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
  · rw [rdec_nodeEmb_leafUp, rdec_nodeEmb_leafUp, rdec_scaleN_node_root]
    refine le_of_le_of_eq hd ?_
    push_cast
    ring

/-- **Assembly step of Lemma 5.5.**  Nonempty clusters `Cs i`, realized by
valid marked trees with branch exponents `< N`, pairwise disjoint and
`2^N/2`-separated, and chain-linked at scale `2^N`, are jointly realized by
the `node` of their trees with root exponent `N` — hence realizable below
`N + 1`. -/
theorem rdec_assemble {M N : ℕ} (hN : 1 ≤ N) (cs : List PlaneTree)
    (hlen : 2 ≤ cs.length) (Cs : Fin cs.length → Finset (Fin 4 → ℤ))
    (hCne : ∀ i, (Cs i).Nonempty)
    (hdata : ∀ i : Fin cs.length, (cs.get i).isValid = true ∧
      ∃ Nm : HeppMarking (cs.get i), Realizes Nm M (Cs i) ∧
        (cs.get i).leafCount = (Cs i).card ∧
        ∀ v ∈ BranchNodes (cs.get i), Nm.Nexp v < N)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Cs i) (Cs j))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Cs i, ∀ y ∈ Cs j, (2 : ℝ) ^ N / 2 ≤ znorm (x - y))
    (hconn : ∀ i j : Fin cs.length, Relation.ReflTransGen
      (fun a b => ∃ x ∈ Cs a, ∃ y ∈ Cs b, znorm (x - y) ≤ (2 : ℝ) ^ N) i j) :
    rdec_RealizableBelow M (Finset.univ.biUnion Cs) (N + 1) := by
  choose hval Nms hreal hcount hbelow using hdata
  choose zs hadm himg using hreal
  have hone : 1 ≤ cs.length := by omega
  have hinj : ∀ i, Function.Injective (zs i) := fun i => (hadm i).inj
  have hmem : ∀ i (w : {l // l ∈ Leaves (cs.get i)}), zs i w ∈ Cs i := fun i w => by
    rw [← himg i]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  refine ⟨node cs, ?_, rdec_nodeMarking hN Nms hbelow,
    ⟨rdec_nodeEmb zs, ⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · -- validity
    rw [isValid, Bool.and_eq_true]
    refine ⟨?_, (rdec_isValidList_iff cs).mpr hval⟩
    simp only [bne_iff_ne, ne_eq]
    omega
  · -- injectivity
    exact rdec_nodeEmb_inj hone hinj himg hdisj
  · -- separation (Def 5.4(a))
    intro l l' hne
    obtain ⟨i, w, rfl⟩ := rdec_leafUp_surj hone l
    obtain ⟨j, w', rfl⟩ := rdec_leafUp_surj hone l'
    rw [rdec_nodeEmb_leafUp, rdec_nodeEmb_leafUp]
    by_cases hij : i = j
    · subst hij
      have hww : w ≠ w' := fun h => hne (by rw [h])
      have hsep' := (hadm i).sep w w' hww
      show (scaleN _ (lcaV (childV i w.1) (childV i w'.1)) : ℝ) / 2 ≤ _
      rw [rdec_lcaV_childV, rdec_scaleN_node_childV]
      exact hsep'
    · show (scaleN _ (lcaV (childV i w.1) (childV j w'.1)) : ℝ) / 2 ≤ _
      rw [rdec_lcaV_childV_ne hij, rdec_scaleN_node_root]
      have hcast : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; ring
      rw [hcast]
      exact hsep i j hij _ (hmem i w) _ (hmem j w')
  · -- boundedness
    intro l i₀
    obtain ⟨i, w, rfl⟩ := rdec_leafUp_surj hone l
    rw [rdec_nodeEmb_leafUp]
    exact (hadm i).bounded w i₀
  · -- links (Def 5.4(b))
    refine vpos_node_cases
      (fun v => v ∈ BranchNodes (node cs) →
        LinkedChildren (rdec_nodeMarking hN Nms hbelow) (rdec_nodeEmb zs) v) ?_ ?_
    · intro _
      exact rdec_linked_root hN himg hconn
    · intro i u hu
      exact rdec_linked_childV hN i u
        ((hadm i).linked u ((rdec_childV_mem_branchNodes i u).mp hu))
  · -- image
    exact rdec_nodeEmb_image hone himg
  · -- leaf count
    rw [Finset.card_biUnion fun i _ j _ hij => hdisj i j hij]
    have hpos : 1 ≤ ∑ i, (Cs i).card := by
      have h0 : (Cs ⟨0, by omega⟩).card ≠ 0 :=
        Finset.card_ne_zero.mpr (hCne ⟨0, by omega⟩)
      have hle : (Cs ⟨0, by omega⟩).card ≤ ∑ i, (Cs i).card :=
        Finset.single_le_sum (f := fun i => (Cs i).card)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
      omega
    rw [leafCount, rdec_leafCountList_eq_sum,
      Finset.sum_congr rfl fun i _ => hcount i]
    exact max_eq_right hpos
  · -- branch exponents ≤ N < N + 1
    refine vpos_node_cases
      (fun v => v ∈ BranchNodes (node cs) →
        (rdec_nodeMarking hN Nms hbelow).Nexp v < N + 1) ?_ ?_
    · intro _
      show N < N + 1
      omega
    · intro i u hu
      have := hbelow i u ((rdec_childV_mem_branchNodes i u).mp hu)
      show (Nms i).Nexp u < N + 1
      omega

/-! ## Single-linkage components of a cluster family -/

/-- One link between clusters of the family `P` at scale `2^N`. -/
def rdec_Step (P : Finset (Finset (Fin 4 → ℤ))) (N : ℕ)
    (C D : Finset (Fin 4 → ℤ)) : Prop :=
  C ∈ P ∧ D ∈ P ∧ ∃ x ∈ C, ∃ y ∈ D, znorm (x - y) ≤ (2 : ℝ) ^ N

/-- Chain-reachability between clusters of `P` at scale `2^N`. -/
def rdec_Reach (P : Finset (Finset (Fin 4 → ℤ))) (N : ℕ)
    (C D : Finset (Fin 4 → ℤ)) : Prop :=
  Relation.ReflTransGen (rdec_Step P N) C D

theorem rdec_Step.symm {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C D : Finset (Fin 4 → ℤ)} (h : rdec_Step P N C D) : rdec_Step P N D C := by
  obtain ⟨hC, hD, x, hx, y, hy, hd⟩ := h
  exact ⟨hD, hC, y, hy, x, hx, by rwa [znorm_sub_comm]⟩

theorem rdec_Reach.trans {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C D E : Finset (Fin 4 → ℤ)} (h1 : rdec_Reach P N C D)
    (h2 : rdec_Reach P N D E) : rdec_Reach P N C E :=
  Relation.ReflTransGen.trans h1 h2

theorem rdec_Reach.symm {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C D : Finset (Fin 4 → ℤ)} (h : rdec_Reach P N C D) : rdec_Reach P N D C := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hbc.symm) ih

open Classical in
/-- The single-linkage component of `C` in the family `P` at scale `2^N`. -/
noncomputable def rdec_comp (P : Finset (Finset (Fin 4 → ℤ))) (N : ℕ)
    (C : Finset (Fin 4 → ℤ)) : Finset (Finset (Fin 4 → ℤ)) :=
  P.filter fun D => rdec_Reach P N C D

theorem rdec_mem_comp {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C D : Finset (Fin 4 → ℤ)} :
    D ∈ rdec_comp P N C ↔ D ∈ P ∧ rdec_Reach P N C D := by
  classical
  simp [rdec_comp]

theorem rdec_self_mem_comp {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C : Finset (Fin 4 → ℤ)} (hC : C ∈ P) : C ∈ rdec_comp P N C :=
  rdec_mem_comp.mpr ⟨hC, Relation.ReflTransGen.refl⟩

theorem rdec_comp_subset {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C : Finset (Fin 4 → ℤ)} : rdec_comp P N C ⊆ P :=
  fun _ hD => (rdec_mem_comp.mp hD).1

theorem rdec_comp_eq_of_mem {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C D : Finset (Fin 4 → ℤ)} (hD : D ∈ rdec_comp P N C) :
    rdec_comp P N D = rdec_comp P N C := by
  obtain ⟨hDP, hCD⟩ := rdec_mem_comp.mp hD
  ext E
  rw [rdec_mem_comp, rdec_mem_comp]
  exact ⟨fun ⟨hE, hDE⟩ => ⟨hE, hCD.trans hDE⟩,
    fun ⟨hE, hCE⟩ => ⟨hE, hCD.symm.trans hCE⟩⟩

/-- Any two members of one component are chain-connected. -/
theorem rdec_reach_of_mem_comp {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C D E : Finset (Fin 4 → ℤ)} (hD : D ∈ rdec_comp P N C)
    (hE : E ∈ rdec_comp P N C) : rdec_Reach P N D E :=
  ((rdec_mem_comp.mp hD).2.symm).trans (rdec_mem_comp.mp hE).2

/-- Members of distinct components are never directly linked. -/
theorem rdec_no_step_of_comp_ne {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C C' D D' : Finset (Fin 4 → ℤ)} (hD : D ∈ rdec_comp P N C)
    (hD' : D' ∈ rdec_comp P N C') (hne : rdec_comp P N C ≠ rdec_comp P N C')
    (hstep : rdec_Step P N D D') : False := by
  have h1 : rdec_comp P N D = rdec_comp P N C := rdec_comp_eq_of_mem hD
  have h2 : rdec_comp P N D' = rdec_comp P N C' := rdec_comp_eq_of_mem hD'
  have h3 : D' ∈ rdec_comp P N D :=
    rdec_mem_comp.mpr ⟨hstep.2.1, Relation.ReflTransGen.single hstep⟩
  rw [h1] at h3
  have h4 := rdec_comp_eq_of_mem h3
  rw [h2] at h4
  exact hne h4.symm

/-- The fiber of the component map over `rdec_comp P N C` is the component. -/
private theorem rdec_filter_comp_eq {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C : Finset (Fin 4 → ℤ)} :
    (P.filter fun D => rdec_comp P N D = rdec_comp P N C) = rdec_comp P N C := by
  ext D
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hD, hcomp⟩
    have hself : D ∈ rdec_comp P N D := rdec_self_mem_comp hD
    rwa [hcomp] at hself
  · intro hD
    exact ⟨rdec_comp_subset hD, rdec_comp_eq_of_mem hD⟩

/-- If some component has at least two members, there are strictly fewer
components than clusters. -/
private theorem rdec_card_image_comp_lt {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C₀ : Finset (Fin 4 → ℤ)} (hC₀ : C₀ ∈ P) (h2 : 2 ≤ (rdec_comp P N C₀).card) :
    (P.image fun C => rdec_comp P N C).card < P.card := by
  classical
  have hcard := Finset.card_eq_sum_card_image (fun C => rdec_comp P N C) P
  have hlt : (P.image fun C => rdec_comp P N C).card <
      ∑ K ∈ P.image fun C => rdec_comp P N C,
        (P.filter fun D => rdec_comp P N D = K).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_lt_sum ?_ ?_
    · intro K hK
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hK
      rw [rdec_filter_comp_eq]
      exact Finset.card_pos.mpr ⟨C, rdec_self_mem_comp (N := N) hC⟩
    · refine ⟨rdec_comp P N C₀, Finset.mem_image_of_mem _ hC₀, ?_⟩
      rw [rdec_filter_comp_eq]
      omega
  rw [hcard]
  exact hlt

/-- Function-indexed form of the assembly step (hides the `List.ofFn`
plumbing): `m ≥ 2` clusters, each realizable below `N`, pairwise disjoint and
`2^N/2`-separated, chain-linked at scale `2^N`, are jointly realizable below
`N + 1`. -/
theorem rdec_assemble' {M N : ℕ} (hN : 1 ≤ N) {m : ℕ} (hm : 2 ≤ m)
    (Cs : Fin m → Finset (Fin 4 → ℤ)) (hCne : ∀ i, (Cs i).Nonempty)
    (hdata : ∀ i : Fin m, ∃ t : PlaneTree, t.isValid = true ∧
      ∃ Nm : HeppMarking t, Realizes Nm M (Cs i) ∧ t.leafCount = (Cs i).card ∧
        ∀ v ∈ BranchNodes t, Nm.Nexp v < N)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Cs i) (Cs j))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ Cs i, ∀ y ∈ Cs j, (2 : ℝ) ^ N / 2 ≤ znorm (x - y))
    (hconn : ∀ i j : Fin m, Relation.ReflTransGen
      (fun a b => ∃ x ∈ Cs a, ∃ y ∈ Cs b, znorm (x - y) ≤ (2 : ℝ) ^ N) i j) :
    rdec_RealizableBelow M (Finset.univ.biUnion Cs) (N + 1) := by
  choose T hTval hTrest using hdata
  have hlength : (List.ofFn T).length = m := List.length_ofFn
  have hget : ∀ j : Fin (List.ofFn T).length,
      (List.ofFn T).get j = T (Fin.cast hlength j) := fun j => List.get_ofFn T j
  have hdata' : ∀ j : Fin (List.ofFn T).length, ((List.ofFn T).get j).isValid = true ∧
      ∃ Nm : HeppMarking ((List.ofFn T).get j),
        Realizes Nm M (Cs (Fin.cast hlength j)) ∧
        ((List.ofFn T).get j).leafCount = (Cs (Fin.cast hlength j)).card ∧
        ∀ v ∈ BranchNodes ((List.ofFn T).get j), Nm.Nexp v < N := by
    intro j
    rw [hget j]
    exact ⟨hTval _, hTrest _⟩
  have hcast_inj : ∀ {i j : Fin (List.ofFn T).length},
      Fin.cast hlength i = Fin.cast hlength j → i = j := by
    intro i j h
    have hv : (Fin.cast hlength i).val = (Fin.cast hlength j).val := congrArg Fin.val h
    exact Fin.ext hv
  have hconn' : ∀ i j : Fin (List.ofFn T).length, Relation.ReflTransGen
      (fun a b => ∃ x ∈ Cs (Fin.cast hlength a), ∃ y ∈ Cs (Fin.cast hlength b),
        znorm (x - y) ≤ (2 : ℝ) ^ N) i j := by
    intro i j
    have hstep : ∀ a b, (∃ x ∈ Cs a, ∃ y ∈ Cs b, znorm (x - y) ≤ (2 : ℝ) ^ N) →
        ∃ x ∈ Cs (Fin.cast hlength (Fin.cast hlength.symm a)),
          ∃ y ∈ Cs (Fin.cast hlength (Fin.cast hlength.symm b)),
            znorm (x - y) ≤ (2 : ℝ) ^ N := fun a b hab => hab
    exact Relation.ReflTransGen.lift (Fin.cast hlength.symm) hstep _ _
      (hconn (Fin.cast hlength i) (Fin.cast hlength j))
  have hkey := rdec_assemble hN (List.ofFn T) (by omega)
    (fun j => Cs (Fin.cast hlength j)) (fun j => hCne _) hdata'
    (fun i j hij => hdisj _ _ fun h => hij (hcast_inj h))
    (fun i j hij x hx y hy => hsep _ _ (fun h => hij (hcast_inj h)) x hx y hy)
    hconn'
  have hbi : (Finset.univ.biUnion fun j : Fin (List.ofFn T).length =>
      Cs (Fin.cast hlength j)) = Finset.univ.biUnion Cs := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨j, hj⟩ => ⟨_, hj⟩, fun ⟨i, hi⟩ => ⟨Fin.cast hlength.symm i, hi⟩⟩
  rwa [hbi] at hkey

/-- Merging one multi-cluster component of `P` at scale `N` via the assembly
step: the union of the component is realizable below `N + 1`. -/
private theorem rdec_merge_component {M N : ℕ} (hN : 1 ≤ N)
    (P : Finset (Finset (Fin 4 → ℤ))) (C : Finset (Fin 4 → ℤ))
    (h2 : 2 ≤ (rdec_comp P N C).card)
    (hPne : ∀ D ∈ P, D.Nonempty)
    (hPdisj : ∀ D ∈ P, ∀ D' ∈ P, D ≠ D' → Disjoint D D')
    (hPsep : ∀ D ∈ P, ∀ D' ∈ P, D ≠ D' → ∀ x ∈ D, ∀ y ∈ D',
      (2 : ℝ) ^ N / 2 ≤ znorm (x - y))
    (hPrel : ∀ D ∈ P, rdec_RealizableBelow M D N) :
    rdec_RealizableBelow M ((rdec_comp P N C).biUnion id) (N + 1) := by
  have hcard : Fintype.card {D // D ∈ rdec_comp P N C} = (rdec_comp P N C).card :=
    Fintype.card_coe _
  let eK : {D // D ∈ rdec_comp P N C} ≃ Fin (rdec_comp P N C).card :=
    Fintype.equivFinOfCardEq hcard
  have hsub : ∀ i, (eK.symm i).1 ∈ P := fun i => rdec_comp_subset (eK.symm i).2
  have hval_ne : ∀ {i j}, i ≠ j → (eK.symm i).1 ≠ (eK.symm j).1 :=
    fun hij h => hij (eK.symm.injective (Subtype.ext h))
  have hconn : ∀ i j : Fin (rdec_comp P N C).card, Relation.ReflTransGen
      (fun a b => ∃ x ∈ (eK.symm a).1, ∃ y ∈ (eK.symm b).1,
        znorm (x - y) ≤ (2 : ℝ) ^ N) i j := by
    intro i j
    have hreach : rdec_Reach P N (eK.symm i).1 (eK.symm j).1 :=
      rdec_reach_of_mem_comp (eK.symm i).2 (eK.symm j).2
    have main : ∀ D, rdec_Reach P N (eK.symm i).1 D →
        ∀ hD : D ∈ rdec_comp P N C,
        Relation.ReflTransGen
          (fun a b => ∃ x ∈ (eK.symm a).1, ∃ y ∈ (eK.symm b).1,
            znorm (x - y) ≤ (2 : ℝ) ^ N) i (eK ⟨D, hD⟩) := by
      intro D hreachD
      induction hreachD with
      | refl =>
        intro hD
        have hsub' : (⟨(eK.symm i).1, hD⟩ : {D // D ∈ rdec_comp P N C}) = eK.symm i :=
          Subtype.ext rfl
        rw [hsub', Equiv.apply_symm_apply]
      | tail hab hbc ih =>
        intro hD
        obtain ⟨hbP, hD'P, x, hx, y', hy', hd⟩ := hbc
        have hbK := rdec_mem_comp.mpr ⟨hbP, hab⟩
        rw [rdec_comp_eq_of_mem (eK.symm i).2] at hbK
        refine Relation.ReflTransGen.tail (ih hbK) ?_
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact ⟨x, hx, y', hy', hd⟩
    have hfin := main _ hreach (eK.symm j).2
    have hsub2 : (⟨(eK.symm j).1, (eK.symm j).2⟩ : {D // D ∈ rdec_comp P N C})
        = eK.symm j := Subtype.ext rfl
    rwa [hsub2, Equiv.apply_symm_apply] at hfin
  have hkey := rdec_assemble' hN h2 (fun i => (eK.symm i).1)
    (fun i => hPne _ (hsub i))
    (fun i => hPrel _ (hsub i))
    (fun i j hij => hPdisj _ (hsub i) _ (hsub j) (hval_ne hij))
    (fun i j hij x hx y hy => hPsep _ (hsub i) _ (hsub j) (hval_ne hij) x hx y hy)
    hconn
  have hbi : (Finset.univ.biUnion fun i => (eK.symm i).1)
      = (rdec_comp P N C).biUnion id := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨_, (eK.symm i).2, hi⟩
    · rintro ⟨D, hD, hx⟩
      refine ⟨eK ⟨D, hD⟩, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact hx
  rwa [hbi] at hkey

/-! ## The component family: hypotheses propagate from scale `N` to `N + 1` -/

private theorem rdec_biUnion_image_comp (P : Finset (Finset (Fin 4 → ℤ))) (N : ℕ) :
    ((P.image fun C => (rdec_comp P N C).biUnion id).biUnion id) = P.biUnion id := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_image, id_eq]
  constructor
  · rintro ⟨E, ⟨C, hC, rfl⟩, hx⟩
    rw [Finset.mem_biUnion] at hx
    obtain ⟨D, hD, hx⟩ := hx
    exact ⟨D, rdec_comp_subset hD, hx⟩
  · rintro ⟨C, hC, hx⟩
    exact ⟨(rdec_comp P N C).biUnion id, ⟨C, hC, rfl⟩,
      Finset.mem_biUnion.mpr ⟨C, rdec_self_mem_comp hC, hx⟩⟩

private theorem rdec_comp_family_ne {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    (hne : ∀ C ∈ P, C.Nonempty) :
    ∀ E ∈ P.image fun C => (rdec_comp P N C).biUnion id, E.Nonempty := by
  intro E hE
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨x, hx⟩ := hne C hC
  exact ⟨x, Finset.mem_biUnion.mpr ⟨C, rdec_self_mem_comp hC, hx⟩⟩

private theorem rdec_comp_family_bound {M : ℕ} {P : Finset (Finset (Fin 4 → ℤ))}
    {N : ℕ} (hbound : ∀ C ∈ P, ∀ x ∈ C, ∀ i, |x i| ≤ (M : ℤ)) :
    ∀ E ∈ P.image fun C => (rdec_comp P N C).biUnion id,
      ∀ x ∈ E, ∀ i, |x i| ≤ (M : ℤ) := by
  intro E hE x hx i
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨D, hD, hx⟩ := Finset.mem_biUnion.mp hx
  exact hbound D (rdec_comp_subset hD) x hx i

private theorem rdec_comp_ne_of_union_ne {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    {C C' : Finset (Fin 4 → ℤ)}
    (h : (rdec_comp P N C).biUnion id ≠ (rdec_comp P N C').biUnion id) :
    rdec_comp P N C ≠ rdec_comp P N C' :=
  fun hcompeq => h (by rw [hcompeq])

private theorem rdec_comp_family_disj {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ}
    (hdisj : ∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint C C') :
    ∀ E ∈ P.image fun C => (rdec_comp P N C).biUnion id,
      ∀ E' ∈ P.image fun C => (rdec_comp P N C).biUnion id,
        E ≠ E' → Disjoint E E' := by
  intro E hE E' hE' hEE'
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hE'
  have hcne := rdec_comp_ne_of_union_ne hEE'
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨D, hD, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨D', hD', hx'⟩ := Finset.mem_biUnion.mp hx'
  have hDne : D ≠ D' := by
    rintro rfl
    exact hcne ((rdec_comp_eq_of_mem hD).symm.trans (rdec_comp_eq_of_mem hD'))
  exact Finset.disjoint_left.mp
    (hdisj D (rdec_comp_subset hD) D' (rdec_comp_subset hD') hDne) hx hx'

private theorem rdec_comp_family_sep {P : Finset (Finset (Fin 4 → ℤ))} {N : ℕ} :
    ∀ E ∈ P.image fun C => (rdec_comp P N C).biUnion id,
      ∀ E' ∈ P.image fun C => (rdec_comp P N C).biUnion id,
        E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', (2 : ℝ) ^ (N + 1) / 2 ≤ znorm (x - y) := by
  intro E hE E' hE' hEE' x hx y hy
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hE'
  have hcne := rdec_comp_ne_of_union_ne hEE'
  obtain ⟨D, hD, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨D', hD', hy⟩ := Finset.mem_biUnion.mp hy
  have hgt : (2 : ℝ) ^ N < znorm (x - y) := by
    by_contra hle
    push Not at hle
    exact rdec_no_step_of_comp_ne hD hD' hcne
      ⟨rdec_comp_subset hD, rdec_comp_subset hD', x, hx, y, hy, hle⟩
  have h2 : (2 : ℝ) ^ (N + 1) / 2 = (2 : ℝ) ^ N := by ring
  rw [h2]
  exact hgt.le

private theorem rdec_comp_family_rel {M : ℕ} {P : Finset (Finset (Fin 4 → ℤ))}
    {N : ℕ} (hN : 1 ≤ N) (hne : ∀ C ∈ P, C.Nonempty)
    (hdisj : ∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint C C')
    (hsep : ∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → ∀ x ∈ C, ∀ y ∈ C',
      (2 : ℝ) ^ N / 2 ≤ znorm (x - y))
    (hrel : ∀ C ∈ P, rdec_RealizableBelow M C N) :
    ∀ E ∈ P.image fun C => (rdec_comp P N C).biUnion id,
      rdec_RealizableBelow M E (N + 1) := by
  intro E hE
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hE
  rcases lt_or_ge (rdec_comp P N C).card 2 with hlt | hge
  · have hone : (rdec_comp P N C).card = 1 := by
      have := Finset.card_pos.mpr ⟨C, rdec_self_mem_comp (N := N) hC⟩
      omega
    obtain ⟨D, hD⟩ := Finset.card_eq_one.mp hone
    have hCD : C = D := by
      have hself := rdec_self_mem_comp (N := N) hC
      rw [hD] at hself
      exact Finset.mem_singleton.mp hself
    have hun : (rdec_comp P N C).biUnion id = C := by
      rw [hD, ← hCD]
      simp
    rw [hun]
    exact (hrel C hC).mono (by omega)
  · exact rdec_merge_component hN P C hge hne hdisj hsep hrel

/-- **Recursion of Lemma 5.5** (single-linkage dyadic merging, fuel-indexed):
the union of a pairwise-disjoint, `2^N/2`-separated family of nonempty
bounded clusters, each realizable below `N`, is realized by a single valid
marked Hepp tree with the right number of leaves. -/
private theorem rdec_merge_rec (M : ℕ) : ∀ fuel N : ℕ,
    ∀ P : Finset (Finset (Fin 4 → ℤ)),
    P.card + (M + 1 - N) ≤ fuel → 1 ≤ N → P.Nonempty →
    (∀ C ∈ P, C.Nonempty) →
    (∀ C ∈ P, ∀ x ∈ C, ∀ i, |x i| ≤ (M : ℤ)) →
    (∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → Disjoint C C') →
    (∀ C ∈ P, ∀ C' ∈ P, C ≠ C' → ∀ x ∈ C, ∀ y ∈ C',
      (2 : ℝ) ^ N / 2 ≤ znorm (x - y)) →
    (∀ C ∈ P, rdec_RealizableBelow M C N) →
    ∃ t : PlaneTree, t.isValid = true ∧ ∃ Nm : HeppMarking t,
      Realizes Nm M (P.biUnion id) ∧ t.leafCount = (P.biUnion id).card := by
  intro fuel
  induction fuel with
  | zero =>
    intro N P hfuel _ hPne _ _ _ _ _
    obtain ⟨C, hC⟩ := hPne
    have := Finset.card_pos.mpr ⟨C, hC⟩
    omega
  | succ fuel ih =>
    intro N P hfuel hN hPne hne hbound hdisj hsep hrel
    by_cases hcard : P.card = 1
    · obtain ⟨C, rfl⟩ := Finset.card_eq_one.mp hcard
      obtain ⟨t, hv, Nm, hr, hc, -⟩ := hrel C (Finset.mem_singleton_self C)
      have hun : ({C} : Finset (Finset (Fin 4 → ℤ))).biUnion id = C := by simp
      rw [hun]
      exact ⟨t, hv, Nm, hr, hc⟩
    · have h1 : 1 < P.card := by
        have := Finset.card_pos.mpr hPne
        omega
      by_cases hmerge : ∃ C₀ ∈ P, 2 ≤ (rdec_comp P N C₀).card
      · -- merge case: pass to the component family, recurse at scale N + 1
        obtain ⟨C₀, hC₀, hcomp₀⟩ := hmerge
        have himgfact : (P.image fun C => (rdec_comp P N C).biUnion id)
            = (P.image fun C => rdec_comp P N C).image fun K => K.biUnion id := by
          rw [Finset.image_image]
          rfl
        have hP'card : (P.image fun C => (rdec_comp P N C).biUnion id).card
            < P.card := by
          rw [himgfact]
          exact lt_of_le_of_lt Finset.card_image_le
            (rdec_card_image_comp_lt hC₀ hcomp₀)
        have hfin := ih (N + 1) (P.image fun C => (rdec_comp P N C).biUnion id)
          (by omega) (by omega) (hPne.image _)
          (rdec_comp_family_ne hne) (rdec_comp_family_bound hbound)
          (rdec_comp_family_disj hdisj) rdec_comp_family_sep
          (rdec_comp_family_rel hN hne hdisj hsep hrel)
        rwa [rdec_biUnion_image_comp P N] at hfin
      · -- no-merge case: all components are singletons; recurse at N + 1
        push Not at hmerge
        have hnostep : ∀ C ∈ P, ∀ C' ∈ P, C ≠ C' →
            ∀ x ∈ C, ∀ y ∈ C', (2 : ℝ) ^ N < znorm (x - y) := by
          intro C hC C' hC' hne' x hx y hy
          by_contra hle
          push Not at hle
          have hC'in : C' ∈ rdec_comp P N C :=
            rdec_mem_comp.mpr
              ⟨hC', Relation.ReflTransGen.single ⟨hC, hC', x, hx, y, hy, hle⟩⟩
          have h2' : 1 < (rdec_comp P N C).card :=
            Finset.one_lt_card.mpr ⟨C, rdec_self_mem_comp (N := N) hC, C', hC'in, hne'⟩
          have := hmerge C hC
          omega
        have hNM : N < M + 1 := by
          obtain ⟨C, hC, C', hC', hne'⟩ := Finset.one_lt_card.mp h1
          obtain ⟨x, hx⟩ := hne C hC
          obtain ⟨y', hy'⟩ := hne C' hC'
          have hlt := hnostep C hC C' hC' hne' x hx y' hy'
          have hle := rdec_znorm_le_pow (hbound C hC x hx) (hbound C' hC' y' hy')
          exact (pow_lt_pow_iff_right₀ one_lt_two).mp (lt_of_lt_of_le hlt hle)
        refine ih (N + 1) P (by omega) (by omega) hPne hne hbound hdisj ?_ ?_
        · intro C hC C' hC' hne' x hx y hy
          have hgt := hnostep C hC C' hC' hne' x hx y hy
          have h2 : (2 : ℝ) ^ (N + 1) / 2 = (2 : ℝ) ^ N := by ring
          rw [h2]
          exact hgt.le
        · intro C hC
          exact (hrel C hC).mono (by omega)

/-- **General multi-scale Lemma 5.5** (blueprint node L-5.5, set form): every
nonempty finite `Z ⊆ [-M, M]⁴` is realized by a valid marked Hepp tree with
exactly `Z.card` leaves.  Proof: single-linkage dyadic merging — start from
singletons at scale `2`, at each scale form chain components of clusters and
merge every multi-cluster component under a new root (`rdec_assemble`), then
increase the scale; the box diameter bound `2^{M+1}` forces termination. -/
theorem rdec_exists_realizing_marked_tree (M : ℕ) (Z : Finset (Fin 4 → ℤ))
    (hZ : Z.Nonempty) (hbound : ∀ x ∈ Z, ∀ i, |x i| ≤ (M : ℤ)) :
    ∃ t : PlaneTree, t.isValid = true ∧ ∃ Nm : HeppMarking t,
      Realizes Nm M Z ∧ t.leafCount = Z.card := by
  have hbi : (Z.image fun x => ({x} : Finset (Fin 4 → ℤ))).biUnion id = Z := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, id_eq]
    constructor
    · rintro ⟨E, ⟨x₀, hx₀, rfl⟩, hx⟩
      rw [Finset.mem_singleton] at hx
      exact hx ▸ hx₀
    · intro hx
      exact ⟨{x}, ⟨x, hx, rfl⟩, Finset.mem_singleton_self x⟩
  have hsingle : ∀ C ∈ Z.image fun x => ({x} : Finset (Fin 4 → ℤ)),
      ∃ x₀ ∈ Z, C = {x₀} := by
    intro C hC
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨x₀, hx₀, rfl⟩
  have hfin := rdec_merge_rec M
    ((Z.image fun x => ({x} : Finset (Fin 4 → ℤ))).card + M) 1
    (Z.image fun x => ({x} : Finset (Fin 4 → ℤ))) (by omega) le_rfl (hZ.image _)
    (fun C hC => by
      obtain ⟨x₀, -, rfl⟩ := hsingle C hC
      exact Finset.singleton_nonempty x₀)
    (fun C hC x hx i => by
      obtain ⟨x₀, hx₀, rfl⟩ := hsingle C hC
      rw [Finset.mem_singleton] at hx
      exact hx ▸ hbound x₀ hx₀ i)
    (fun C hC C' hC' hne => by
      obtain ⟨x₀, -, rfl⟩ := hsingle C hC
      obtain ⟨x₁, -, rfl⟩ := hsingle C' hC'
      rw [Finset.disjoint_singleton]
      exact fun h => hne (by rw [h]))
    (fun C hC C' hC' hne x hx y hy => by
      obtain ⟨x₀, -, rfl⟩ := hsingle C hC
      obtain ⟨x₁, -, rfl⟩ := hsingle C' hC'
      rw [Finset.mem_singleton] at hx hy
      subst hx; subst hy
      have hxy : x ≠ y := fun h => hne (by rw [h])
      have := rdec_one_le_znorm hxy
      have h21 : (2 : ℝ) ^ 1 / 2 = 1 := by norm_num
      rw [h21]
      exact this)
    (fun C hC => by
      obtain ⟨x₀, hx₀, rfl⟩ := hsingle C hC
      exact rdec_realizableBelow_singleton M 1 x₀ (hbound x₀ hx₀))
  rwa [hbi] at hfin

/-- **Structural realization for R-decomp** (paper Lemma 5.5, multiplicity
form, plus the "fix `T`" step of (5.6)): every bounded tuple all of whose
values occur at least twice belongs to the realization class of some valid
marked tree with at most `n` leaves.  The repetition hypothesis `hrep` is
forced by Def 5.1's `m_ℓ ≥ 2`: a tuple with a once-occurring value lies in no
realization class (in the paper such tuples are killed by the expectation of
the mean-zero chain before (5.6)). -/
theorem exists_realizing_tree (M n : ℕ) (hn : 1 ≤ n) (y : Fin n → Fin 4 → ℤ)
    (hy : y ∈ rdec_boundedTuples M n)
    (hrep : ∀ j, 2 ≤ (Finset.univ.filter fun k => y k = y j).card) :
    ∃ (t : PlaneTree) (_ : t.isValid = true) (Nm : HeppMarking t)
      (mu : Multiplicities t),
      y ∈ realizedTuples t Nm mu M n ∧ t.leafCount ≤ n := by
  have hZne : (Finset.univ.image y).Nonempty :=
    ⟨y ⟨0, hn⟩, Finset.mem_image_of_mem y (Finset.mem_univ _)⟩
  have hZbound : ∀ x ∈ Finset.univ.image y, ∀ i, |x i| ≤ (M : ℤ) := by
    intro x hx i
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact rdec_mem_boundedTuples.mp hy j i
  obtain ⟨t, hv, Nm, ⟨z, hadm, himg⟩, hcount⟩ :=
    rdec_exists_realizing_marked_tree M (Finset.univ.image y) hZne hZbound
  have hw : ∀ j, ∃ l : {l // l ∈ Leaves t}, z l = y j := by
    intro j
    have hyj : y j ∈ Finset.univ.image z := by
      rw [himg]
      exact Finset.mem_image_of_mem y (Finset.mem_univ _)
    obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hyj
    exact ⟨l, hl⟩
  choose w hwspec using hw
  have hfib2 : ∀ l : {l // l ∈ Leaves t},
      2 ≤ (Finset.univ.filter fun j => w j = l).card := by
    intro l
    have hzl : z l ∈ Finset.univ.image y := by
      rw [← himg]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    obtain ⟨j₀, -, hj₀⟩ := Finset.mem_image.mp hzl
    have hEq : (Finset.univ.filter fun j => w j = l)
        = Finset.univ.filter fun j => y j = y j₀ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro rfl
        rw [← hwspec j, hj₀]
      · intro hj
        exact hadm.inj ((hwspec j).trans (hj.trans hj₀))
    rw [hEq]
    exact hrep j₀
  refine ⟨t, hv, Nm,
    ⟨fun v => (Finset.univ.filter fun j => (w j).1 = v).card, ?_⟩, ?_, ?_⟩
  · -- Def 5.1: multiplicity ≥ 2 at every leaf
    intro v hv'
    have hEq : (Finset.univ.filter fun j => (w j).1 = v)
        = Finset.univ.filter fun j => w j = ⟨v, hv'⟩ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [hEq]
    exact hfib2 ⟨v, hv'⟩
  · rw [mem_realizedTuples]
    refine ⟨hy, z, w, hadm, ?_, fun j => (hwspec j).symm⟩
    rw [validWords, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun l => ?_⟩
    show (Finset.univ.filter fun j => w j = l).card
      = (Finset.univ.filter fun j => (w j).1 = l.1).card
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  · rw [hcount]
    calc (Finset.univ.image y).card ≤ Finset.univ.card := Finset.card_image_le
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]

/-! ## Finiteness of valid trees with bounded leaf count
(real-carrier port of `Combinatorics/TreeCount`, paper Lemma 5.2) -/

private theorem rdec_size_lt_of_mem {c : PlaneTree} {cs : List PlaneTree}
    (hc : c ∈ cs) : c.size < (node cs).size := by
  have h1 : c.size ∈ cs.map size := List.mem_map.mpr ⟨c, hc, rfl⟩
  have h2 : c.size ≤ (cs.map size).sum :=
    List.single_le_sum (fun x _ => Nat.zero_le x) _ h1
  have h3 : (node cs).size = 1 + sizeList cs := rfl
  rw [h3, sizeList_eq_map]
  omega

private theorem rdec_planeTreeInduction {motive : PlaneTree → Prop}
    (ind : ∀ cs : List PlaneTree, (∀ c ∈ cs, motive c) → motive (node cs)) :
    ∀ t, motive t
  | node cs => ind cs fun c _hc => rdec_planeTreeInduction ind c
termination_by t => t.size
decreasing_by exact rdec_size_lt_of_mem _hc

private theorem rdec_isValidList_iff_mem (cs : List PlaneTree) :
    isValidList cs = true ↔ ∀ c ∈ cs, c.isValid = true := by
  induction cs with
  | nil => simp [isValidList]
  | cons c cs ih =>
    rw [isValidList, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact h1
      · exact h2 d hd
    · intro h
      exact ⟨h c (List.mem_cons_self ..), fun d hd => h d (List.mem_cons_of_mem c hd)⟩

private theorem rdec_isValid_node_iff {cs : List PlaneTree} :
    (node cs).isValid = true ↔ cs.length ≠ 1 ∧ ∀ c ∈ cs, c.isValid = true := by
  rw [isValid, Bool.and_eq_true, rdec_isValidList_iff_mem]
  simp [bne_iff_ne]

theorem rdec_one_le_leafCount (t : PlaneTree) : 1 ≤ t.leafCount := by
  obtain ⟨cs⟩ := t
  exact le_max_left 1 _

private theorem rdec_sum_size_add_length_le (cs : List PlaneTree)
    (h : ∀ c ∈ cs, c.size + 1 ≤ 2 * c.leafCount) :
    (cs.map size).sum + cs.length ≤ 2 * (cs.map leafCount).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have h1 := h c (List.mem_cons_self ..)
    have h2 := ih fun d hd => h d (List.mem_cons_of_mem c hd)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Paper Lemma 5.2, size part, for the real carrier. -/
theorem rdec_size_add_one_le_of_isValid :
    ∀ t : PlaneTree, t.isValid = true → t.size + 1 ≤ 2 * t.leafCount := by
  intro t
  induction t using rdec_planeTreeInduction with
  | ind cs ih =>
    intro ht
    rw [rdec_isValid_node_iff] at ht
    obtain ⟨hlen, hall⟩ := ht
    have hsum := rdec_sum_size_add_length_le cs fun c hc => ih c hc (hall c hc)
    have hsize : (node cs).size = 1 + (cs.map size).sum := by
      rw [size, sizeList_eq_map]
    have hleaf : (node cs).leafCount = max 1 (cs.map leafCount).sum := by
      rw [leafCount, leafCountList_eq_map]
    cases cs with
    | nil =>
      rw [hsize, hleaf]
      simp
    | cons c cs' =>
      have hone := rdec_one_le_leafCount c
      rw [hsize, hleaf]
      simp only [List.map_cons, List.sum_cons] at hsum ⊢
      simp only [List.length_cons] at hsum hlen
      omega

private theorem rdec_flatten_key_length (cs : List PlaneTree)
    (h : ∀ c ∈ cs, (key c).length = 2 * c.size) :
    (keyList cs).length = 2 * (cs.map size).sum := by
  induction cs with
  | nil => simp [keyList]
  | cons c cs ih =>
    have h1 := h c (List.mem_cons_self ..)
    have h2 := ih fun d hd => h d (List.mem_cons_of_mem c hd)
    rw [keyList]
    simp only [List.length_append, List.map_cons, List.sum_cons]
    omega

private theorem rdec_key_length : ∀ t : PlaneTree, (key t).length = 2 * t.size := by
  intro t
  induction t using rdec_planeTreeInduction with
  | ind cs ih =>
    have hf := rdec_flatten_key_length cs ih
    rw [key, size, sizeList_eq_map]
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega

private theorem rdec_key_mem : ∀ t : PlaneTree, ∀ x ∈ key t, x = 0 ∨ x = 1 := by
  intro t
  induction t using rdec_planeTreeInduction with
  | ind cs ih =>
    intro x hx
    rw [key] at hx
    rcases List.mem_cons.mp hx with h0 | hx1
    · exact Or.inl h0
    rcases List.mem_append.mp hx1 with h2 | h3
    · rw [keyList_eq_map] at h2
      obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp h2
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hl
      exact ih c hc x hxl
    · exact Or.inr (List.mem_singleton.mp h3)

private theorem rdec_key_length_le {r : ℕ} {t : PlaneTree} (hv : t.isValid = true)
    (hl : t.leafCount ≤ r) : (key t).length ≤ 4 * r := by
  have h1 := rdec_size_add_one_le_of_isValid t hv
  have h2 := rdec_key_length t
  omega

/-- Paper Lemma 5.2 finiteness, real carrier: valid trees with at most `r`
leaves form a finite set (explicit injection of keys into
`Fin (4r+1) × (Fin (4r) → Bool)`, using the stack-decoder `key_injective`). -/
theorem rdec_finite_validTrees (r : ℕ) :
    {t : PlaneTree | t.isValid = true ∧ t.leafCount ≤ r}.Finite := by
  let Φ : {t : PlaneTree | t.isValid = true ∧ t.leafCount ≤ r} →
      Fin (4 * r + 1) × (Fin (4 * r) → Bool) :=
    fun t =>
      ⟨⟨(key t.1).length, Nat.lt_succ_of_le (rdec_key_length_le t.2.1 t.2.2)⟩,
        fun i => (key t.1).getD i 0 == 1⟩
  have hΦ : Function.Injective Φ := by
    intro t t' h
    rw [Prod.ext_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hlen : (key t.1).length = (key t'.1).length := congrArg Fin.val h1
    have hkey : key t.1 = key t'.1 := by
      apply List.ext_getElem hlen
      intro i hi hi'
      have hiF : i < 4 * r := lt_of_lt_of_le hi (rdec_key_length_le t.2.1 t.2.2)
      have hEq : ((key t.1).getD i 0 == 1) = ((key t'.1).getD i 0 == 1) :=
        congrFun h2 ⟨i, hiF⟩
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at hEq
      have hx := rdec_key_mem t.1 _ (List.getElem_mem hi)
      have hy := rdec_key_mem t'.1 _ (List.getElem_mem hi')
      rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        rw [hx, hy] at hEq ⊢ <;> simp_all
    exact Subtype.ext (PlaneTree.key_injective hkey)
  have hfin : Finite ↥{t : PlaneTree | t.isValid = true ∧ t.leafCount ≤ r} :=
    Finite.of_injective Φ hΦ
  exact Set.toFinite _

/-- The enumeration of valid Hepp trees with at most `n` leaves, using the
quantitative real-carrier implementation of paper Lemma 5.2. -/
noncomputable abbrev rdec_treeEnum (n : ℕ) : Finset PlaneTree :=
  validTreesAtMost n

@[simp] theorem rdec_mem_treeEnum {n : ℕ} {t : PlaneTree} :
    t ∈ rdec_treeEnum n ↔ t.isValid = true ∧ t.leafCount ≤ n :=
  mem_validTreesAtMost

/-- The concrete tree family used by R-decomp has exponentially bounded
cardinality, with explicit constant `4^4`. -/
theorem rdec_card_treeEnum_le (n : ℕ) :
    (rdec_treeEnum n).card ≤ 4 ^ (4 * n) :=
  card_validTreesAtMost_le n

/-! ## The (5.10)-shaped bridge: chain sum ≤ tree-indexed sum -/

open Classical in
/-- Bounded tuples realized by `t` for **some** marking and multiplicities:
the `t`-slice of the master decomposition. -/
noncomputable def rdec_treeRealized (t : PlaneTree) (M n : ℕ) :
    Finset (Fin n → Fin 4 → ℤ) :=
  (rdec_boundedTuples M n).filter fun y =>
    ∃ (Nm : HeppMarking t) (mu : Multiplicities t), RealizesTuple t Nm mu M y

theorem rdec_mem_treeRealized {t : PlaneTree} {M n : ℕ} {y : Fin n → Fin 4 → ℤ} :
    y ∈ rdec_treeRealized t M n ↔ y ∈ rdec_boundedTuples M n ∧
      ∃ (Nm : HeppMarking t) (mu : Multiplicities t), RealizesTuple t Nm mu M y := by
  classical
  simp [rdec_treeRealized]

private theorem rdec_sum_le_sum_biUnion {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (g : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion g, f b ≤ ∑ a ∈ s, ∑ b ∈ g a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hunion :
        g a ∪ s.biUnion g = g a ∪ (s.biUnion g \ g a) := by
      ext b
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    have hdisj : Disjoint (g a) (s.biUnion g \ g a) :=
      Finset.disjoint_sdiff
    have hrest :
        ∑ b ∈ s.biUnion g \ g a, f b ≤ ∑ b ∈ s.biUnion g, f b :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun b _ _ => hf b)
    calc
      ∑ b ∈ g a ∪ s.biUnion g, f b
          = ∑ b ∈ g a, f b + ∑ b ∈ s.biUnion g \ g a, f b := by
              rw [hunion, Finset.sum_union hdisj]
      _ ≤ ∑ b ∈ g a, f b + ∑ b ∈ s.biUnion g, f b :=
        by linarith
      _ ≤ ∑ b ∈ g a, f b + ∑ x ∈ s, ∑ b ∈ g x, f b :=
        by linarith

/-- Every bounded repeated tuple occurs in at least one valid-tree slice.
This is the finite-cover form of Lemma 5.5 used by the master resummation. -/
theorem rdec_repeatedTuples_subset_treeUnion (M n : ℕ) (hn : 1 ≤ n) :
    rdec_repeatedTuples M n ⊆
      (rdec_treeEnum n).biUnion fun t => rdec_treeRealized t M n := by
  intro y hy
  rw [rdec_mem_repeatedTuples] at hy
  obtain ⟨t, hv, Nm, mu, hreal, hleaf⟩ :=
    exists_realizing_tree M n hn y hy.1 hy.2
  rw [Finset.mem_biUnion]
  refine ⟨t, rdec_mem_treeEnum.mpr ⟨hv, hleaf⟩, ?_⟩
  rw [rdec_mem_treeRealized]
  exact ⟨(mem_realizedTuples.mp hreal).1, Nm, mu, (mem_realizedTuples.mp hreal).2⟩

/-- **Weak master bridge for (5.6).**  If the statistic vanishes on tuples
with a once-occurring value (as the mean-zero pairing expansion does), its
full bounded lattice sum is dominated by the sum of its valid-tree slices.
Slices may overlap, hence the inequality and the nonnegativity hypothesis. -/
theorem latticeChainSum_le_treeSum (M n : ℕ) (hn : 1 ≤ n)
    (F : (Fin n → Fin 4 → ℤ) → ℝ) (hF : ∀ y, 0 ≤ F y)
    (hzero : ∀ y ∈ rdec_boundedTuples M n,
      y ∉ rdec_repeatedTuples M n → F y = 0) :
    latticeChainSum M n F ≤
      ∑ t ∈ rdec_treeEnum n, ∑ y ∈ rdec_treeRealized t M n, F y := by
  have heq : latticeChainSum M n F =
      ∑ y ∈ rdec_repeatedTuples M n, F y := by
    rw [latticeChainSum]
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  rw [heq]
  exact (Finset.sum_le_sum_of_subset_of_nonneg
      (rdec_repeatedTuples_subset_treeUnion M n hn)
      (fun y _ _ => hF y)).trans
    (rdec_sum_le_sum_biUnion (rdec_treeEnum n)
      (fun t => rdec_treeRealized t M n) F hF)

/-! ## Exact finite-incidence denominator (paper (5.6)) -/

section Incidence

variable {δ β : Type*}

/-- The realization data in `D` incident to `y`.  In the paper `δ` is the
restricted pair `(N_n, m_l)`; embedding witnesses are deliberately absent. -/
def realizationFiber (D : Finset δ) (R : δ → β → Prop) [DecidableRel R]
    (y : β) : Finset δ :=
  D.filter fun d => R d y

/-- The symmetry denominator in (5.6): the number of realization-data pairs
incident to `y`. -/
def symDenom (D : Finset δ) (R : δ → β → Prop) [DecidableRel R]
    (y : β) : ℕ :=
  (realizationFiber D R y).card

theorem symDenom_pos_iff (D : Finset δ) (R : δ → β → Prop) [DecidableRel R]
    (y : β) :
    0 < symDenom D R y ↔ ∃ d ∈ D, R d y := by
  rw [symDenom, Finset.card_pos]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩
  · rintro ⟨d, hd, hR⟩
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, hR⟩⟩

/-- The symmetry denominator depends only on the incidence predicate.  This
is the generic permutation-invariance step used in (5.6)–(5.8). -/
theorem symDenom_eq_of_iff (D : Finset δ) (R : δ → β → Prop)
    [DecidableRel R] {y y' : β}
    (h : ∀ d ∈ D, (R d y ↔ R d y')) :
    symDenom D R y = symDenom D R y' := by
  apply congrArg Finset.card
  ext d
  by_cases hd : d ∈ D
  · simp [realizationFiber, hd, h d hd]
  · simp [realizationFiber, hd]

/-- **Finite-incidence resummation, paper (5.6).**  Dividing every incidence
by its fiber cardinality counts each covered `y` exactly once. -/
theorem sum_eq_sum_incidence_div (D : Finset δ) (Y : Finset β)
    (R : δ → β → Prop) [DecidableRel R] (F : β → ℝ)
    (hcover : ∀ y ∈ Y, ∃ d ∈ D, R d y) :
    ∑ y ∈ Y, F y =
      ∑ d ∈ D, ∑ y ∈ Y.filter (R d), F y / symDenom D R y := by
  classical
  have hpos : ∀ y ∈ Y, (0 : ℝ) < symDenom D R y := by
    intro y hy
    exact_mod_cast (symDenom_pos_iff D R y).mpr (hcover y hy)
  symm
  calc
    ∑ d ∈ D, ∑ y ∈ Y.filter (R d), F y / symDenom D R y
        = ∑ d ∈ D, ∑ y ∈ Y,
            if R d y then F y / symDenom D R y else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              rw [Finset.sum_filter]
    _ = ∑ y ∈ Y, ∑ d ∈ D,
          if R d y then F y / symDenom D R y else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ y ∈ Y, ∑ d ∈ realizationFiber D R y,
          F y / symDenom D R y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [realizationFiber, Finset.sum_filter]
    _ = ∑ y ∈ Y, F y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard :
              ((realizationFiber D R y).card : ℝ) = symDenom D R y := by
            rfl
          rw [hcard]
          exact mul_div_cancel₀ (F y) (ne_of_gt (hpos y hy))

end Incidence

end Anderson4D
