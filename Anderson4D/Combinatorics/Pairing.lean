import Mathlib

/-!
# L0 combinatorics: partial pairings and fully paired subintervals

Paper: D-pair — Def 2.2 / Def 2.3 — pairings, intervals, primitivity

Formalization of Definitions 2.2–2.3 of Deng–Shen (arXiv:2607.10105), PAPER_MAP
nodes **D-pair** and **D-int**, together with the operations on pairings that the
proof of Prop 3.4 and the Dyck-word bookkeeping of §4.1 require (node D-RI's
interval-removal step, Def 3.1(2)).

## Design

* A partial pairing of a finite index type `ι` is represented as an **involution**
  `κ : ι → ι` (`PartialPairing`): the singles of the paper are its fixed points
  (`PartialPairing.singles`), the pairs are its 2-cycles, recorded as unordered
  pairs (`PartialPairing.pairs : Finset (Sym2 ι)`).
* The ordered layer (subintervals of the paper's `[1, m]`) is developed on
  `ι := Fin m` with intervals `Finset.Icc a b`.  `IsFullyPairedOn κ B` says that
  `B` contains no single and is closed under `κ`; `IsPrimitive` says that no
  *proper* fully paired subinterval exists (paper Def 2.3; for a primitive full
  pairing the whole of `[1, m]` is still fully paired).  The selector of paper
  Def 3.1(2) — the smallest-length, leftmost fully paired subinterval, the whole
  interval being allowed — is `leastFullyPairedSubinterval`, with hypothesis
  `HasFullyPairedSubinterval` (no properness requirement); the properness-aware
  variant used to characterize primitivity is `HasProperFullyPairedSubinterval`.
* Interval removal (Def 3.1(2a)) is implemented **on the complement subtype**:
  `PartialPairing.removeInterval` produces a pairing of
  `{i : Fin m // i ∉ Finset.Icc a b}`, avoiding `Fin` re-indexing arithmetic in
  the primary API.  The transported version on `Fin (m - (Icc a b).card)` is
  provided as `removeIntervalFin` via the order isomorphism `complOrderIso`.

Everything in this file is fully proved; the enumeration instances are computable
and the expected small cardinalities are checked both by `#guard` and by
kernel-reduced `decide` examples.
-/

namespace Anderson4D

/-- **Paper Def 2.2 (node D-pair).**  A *partial pairing* of the index type `ι`
is an involution `κ : ι → ι`.  Indices with `κ i = i` are the *singles*; the
2-cycles `{i, κ i}` (for `κ i ≠ i`) are the *pairs*. -/
structure PartialPairing (ι : Type*) where
  /-- The underlying involutive map. -/
  toFun : ι → ι
  /-- The map is an involution. -/
  involutive : Function.Involutive toFun

namespace PartialPairing

variable {ι : Type*}

instance : FunLike (PartialPairing ι) ι ι where
  coe := PartialPairing.toFun
  coe_injective := fun κ₁ κ₂ h => by cases κ₁; cases κ₂; congr

@[simp]
theorem coe_mk (f : ι → ι) (hf : Function.Involutive f) :
    ⇑(⟨f, hf⟩ : PartialPairing ι) = f := rfl

@[ext]
theorem ext {κ₁ κ₂ : PartialPairing ι} (h : ∀ i, κ₁ i = κ₂ i) : κ₁ = κ₂ :=
  DFunLike.ext _ _ h

@[simp]
theorem apply_apply (κ : PartialPairing ι) (i : ι) : κ (κ i) = i :=
  κ.involutive i

theorem injective (κ : PartialPairing ι) : Function.Injective ⇑κ :=
  κ.involutive.injective

theorem surjective (κ : PartialPairing ι) : Function.Surjective ⇑κ :=
  κ.involutive.surjective

theorem bijective (κ : PartialPairing ι) : Function.Bijective ⇑κ :=
  κ.involutive.bijective

/-- An involution moves `i` to `j` iff it moves `j` to `i`. -/
theorem apply_eq_iff (κ : PartialPairing ι) {i j : ι} : κ i = j ↔ i = κ j :=
  ⟨fun h => by rw [← h, apply_apply], fun h => by rw [h, apply_apply]⟩

/-- The permutation underlying a partial pairing. -/
def toPerm (κ : PartialPairing ι) : Equiv.Perm ι :=
  κ.involutive.toPerm κ.toFun

@[simp]
theorem coe_toPerm (κ : PartialPairing ι) : ⇑κ.toPerm = ⇑κ := rfl

/-- The identity involution: the empty pairing, in which every index is a
single. -/
protected def id : PartialPairing ι := ⟨fun i => i, fun _ => rfl⟩

instance : Inhabited (PartialPairing ι) := ⟨PartialPairing.id⟩

@[simp]
theorem id_apply (i : ι) : PartialPairing.id i = i := rfl

/-- If `κ` maps `B` into `B`, then it maps the complement of `B` into the
complement of `B` (using `κ ∘ κ = id`). -/
theorem apply_notMem (κ : PartialPairing ι) {B : Finset ι}
    (hB : ∀ j ∈ B, κ j ∈ B) {i : ι} (hi : i ∉ B) : κ i ∉ B := fun hmem =>
  hi (by simpa using hB (κ i) hmem)

/-- Restrict a partial pairing to the complement of a `κ`-closed finset,
as a pairing of the complement subtype.  This is the engine behind interval
removal (paper Def 3.1(2a)). -/
def restrictCompl (κ : PartialPairing ι) {B : Finset ι}
    (hB : ∀ j ∈ B, κ j ∈ B) : PartialPairing {i : ι // i ∉ B} where
  toFun i := ⟨κ i.1, κ.apply_notMem hB i.2⟩
  involutive i := Subtype.ext (κ.apply_apply i.1)

@[simp]
theorem restrictCompl_apply_coe (κ : PartialPairing ι) {B : Finset ι}
    (hB : ∀ j ∈ B, κ j ∈ B) (i : {i : ι // i ∉ B}) :
    (κ.restrictCompl hB i : ι) = κ i.1 := rfl

/-- Transport of partial pairings along an equivalence of index types
(conjugation), as an equivalence.  Used to move the induced pairing of
`removeInterval` to a `Fin` index set, and later for the pairing
manipulations in the proof of Prop 3.4. -/
def congr {ι' : Type*} (e : ι ≃ ι') : PartialPairing ι ≃ PartialPairing ι' where
  toFun κ := ⟨fun j => e (κ (e.symm j)), fun j => by simp⟩
  invFun κ' := ⟨fun i => e.symm (κ' (e i)), fun i => by simp⟩
  left_inv κ := by ext i; simp
  right_inv κ' := by ext j; simp

@[simp]
theorem congr_apply_apply {ι' : Type*} (e : ι ≃ ι') (κ : PartialPairing ι)
    (j : ι') : congr e κ j = e (κ (e.symm j)) := rfl

section Finite

variable [Fintype ι] [DecidableEq ι]

/-- The singles of a partial pairing: its fixed points (paper Def 2.2, the
set `S`). -/
def singles (κ : PartialPairing ι) : Finset ι :=
  Finset.univ.filter fun i => κ i = i

/-- The indices moved by the pairing: the union of its pairs (complement of
the singles). -/
def pairSupport (κ : PartialPairing ι) : Finset ι :=
  Finset.univ.filter fun i => κ i ≠ i

@[simp]
theorem mem_singles {κ : PartialPairing ι} {i : ι} :
    i ∈ κ.singles ↔ κ i = i := by simp [singles]

@[simp]
theorem mem_pairSupport {κ : PartialPairing ι} {i : ι} :
    i ∈ κ.pairSupport ↔ κ i ≠ i := by simp [pairSupport]

theorem apply_mem_pairSupport {κ : PartialPairing ι} {i : ι}
    (hi : i ∈ κ.pairSupport) : κ i ∈ κ.pairSupport := by
  rw [mem_pairSupport] at hi ⊢
  intro h
  exact hi (by rw [← κ.apply_apply i, h, h])

theorem singles_union_pairSupport (κ : PartialPairing ι) :
    κ.singles ∪ κ.pairSupport = Finset.univ := by
  ext i
  simp only [Finset.mem_union, mem_singles, mem_pairSupport, Finset.mem_univ,
    iff_true]
  exact eq_or_ne (κ i) i

theorem disjoint_singles_pairSupport (κ : PartialPairing ι) :
    Disjoint κ.singles κ.pairSupport :=
  Finset.disjoint_left.mpr fun _ hi hi' => mem_pairSupport.mp hi' (mem_singles.mp hi)

theorem card_singles_add_card_pairSupport (κ : PartialPairing ι) :
    κ.singles.card + κ.pairSupport.card = Fintype.card ι := by
  rw [← Finset.card_union_of_disjoint κ.disjoint_singles_pairSupport,
    κ.singles_union_pairSupport, Finset.card_univ]

/-- The pairs of a partial pairing, as unordered pairs (paper Def 2.2, the
set `P`). -/
def pairs (κ : PartialPairing ι) : Finset (Sym2 ι) :=
  κ.pairSupport.image fun i => s(i, κ i)

theorem mem_pairs {κ : PartialPairing ι} {p : Sym2 ι} :
    p ∈ κ.pairs ↔ ∃ i, κ i ≠ i ∧ s(i, κ i) = p := by
  simp [pairs]

/-- The fiber of the pair `{a, κ a}` inside the pair support is exactly
`{a, κ a}`. -/
theorem pairSupport_filter_eq_pair {κ : PartialPairing ι} {a : ι}
    (ha : κ a ≠ a) :
    (κ.pairSupport.filter fun i => s(i, κ i) = s(a, κ a)) = {a, κ a} := by
  ext i
  simp only [Finset.mem_filter, mem_pairSupport, Finset.mem_insert,
    Finset.mem_singleton, Sym2.eq_iff]
  constructor
  · rintro ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨ha, Or.inl ⟨rfl, rfl⟩⟩
    · refine ⟨fun h => ha ?_, Or.inr ⟨rfl, κ.apply_apply a⟩⟩
      rw [κ.apply_apply] at h
      exact h.symm

/-- The pairs partition the pair support into 2-cycles: counting version. -/
theorem card_pairSupport (κ : PartialPairing ι) :
    κ.pairSupport.card = 2 * κ.pairs.card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun i => s(i, κ i)) (t := κ.pairs)
    (fun i hi => Finset.mem_image_of_mem _ hi)]
  have h2 : ∀ p ∈ κ.pairs,
      (κ.pairSupport.filter fun i => s(i, κ i) = p).card = 2 := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    rw [pairSupport_filter_eq_pair (mem_pairSupport.mp ha)]
    exact Finset.card_pair fun h => mem_pairSupport.mp ha h.symm
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]
  omega

theorem even_card_pairSupport (κ : PartialPairing ι) :
    Even κ.pairSupport.card :=
  ⟨κ.pairs.card, by rw [card_pairSupport]; omega⟩

/-- Counting form of Def 2.2: `#S + 2 #P = m`. -/
theorem card_singles_add_two_mul_card_pairs (κ : PartialPairing ι) :
    κ.singles.card + 2 * κ.pairs.card = Fintype.card ι := by
  rw [← card_pairSupport]
  exact κ.card_singles_add_card_pairSupport

end Finite

/-- **Paper Def 2.2 (node D-pair).**  A partial pairing is *full* if it has no
singles: every index belongs to a pair. -/
def IsFull (κ : PartialPairing ι) : Prop := ∀ i, κ i ≠ i

instance [Fintype ι] [DecidableEq ι] : DecidablePred (IsFull (ι := ι)) := fun κ =>
  decidable_of_iff (∀ i, κ i ≠ i) Iff.rfl

theorem isFull_iff_singles_eq_empty [Fintype ι] [DecidableEq ι]
    {κ : PartialPairing ι} : κ.IsFull ↔ κ.singles = ∅ := by
  simp [IsFull, singles, Finset.filter_eq_empty_iff]

theorem isFull_iff_pairSupport_eq_univ [Fintype ι] [DecidableEq ι]
    {κ : PartialPairing ι} : κ.IsFull ↔ κ.pairSupport = Finset.univ := by
  simp [IsFull, pairSupport, Finset.filter_eq_self]

/-- A full pairing forces an even number of indices. -/
theorem IsFull.even_card [Fintype ι] [DecidableEq ι] {κ : PartialPairing ι}
    (hκ : κ.IsFull) : Even (Fintype.card ι) := by
  refine ⟨κ.pairs.card, ?_⟩
  have h1 := κ.card_singles_add_two_mul_card_pairs
  rw [isFull_iff_singles_eq_empty.mp hκ, Finset.card_empty] at h1
  omega

/-- A partial pairing is the same data as an involutive self-map. -/
def equivInvolutive : PartialPairing ι ≃ {f : ι → ι // Function.Involutive f} where
  toFun κ := ⟨κ.toFun, κ.involutive⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype ι] [DecidableEq ι] : DecidableEq (PartialPairing ι) :=
  fun _ _ => decidable_of_iff _ DFunLike.ext_iff.symm

instance {α : Type*} [Fintype α] [DecidableEq α] :
    DecidablePred (Function.Involutive : (α → α) → Prop) := fun f =>
  decidable_of_iff (∀ x, f (f x) = x) Iff.rfl

instance [Fintype ι] [DecidableEq ι] : Fintype (PartialPairing ι) :=
  Fintype.ofEquiv _ equivInvolutive.symm

end PartialPairing

-- Cardinality sanity checks (computable enumeration): the involutions of a
-- 2-element set are the identity and the swap; a 4-element set carries
-- 10 involutions, 3 of which are fixed-point-free (full pairings).
#guard Fintype.card (PartialPairing (Fin 2)) = 2
#guard Fintype.card (PartialPairing (Fin 4)) = 10
#guard (Finset.univ.filter fun κ : PartialPairing (Fin 2) => κ.IsFull).card = 1
#guard (Finset.univ.filter fun κ : PartialPairing (Fin 4) => κ.IsFull).card = 3

-- The same counts, kernel-checked: `decide` reduces (no `native_decide`).
example : Fintype.card (PartialPairing (Fin 2)) = 2 := by decide
example : Fintype.card (PartialPairing (Fin 4)) = 10 := by decide
example :
    (Finset.univ.filter fun κ : PartialPairing (Fin 2) => κ.IsFull).card = 1 := by
  decide
example :
    (Finset.univ.filter fun κ : PartialPairing (Fin 4) => κ.IsFull).card = 3 := by
  decide

/-! ## The ordered layer: fully paired subintervals of `Fin m`

Paper Def 2.3 (node D-int).  Subintervals of `[1, m]` are `Finset.Icc a b`
with `a b : Fin m`, `a ≤ b`. -/

variable {m : ℕ}

/-- **Paper Def 2.3 (node D-int).**  `B` is *fully paired* under `κ` if it
contains no single of `κ` and is closed under `κ` (so the pairs meeting `B`
lie entirely inside `B`).  Stated for an arbitrary finset `B`; the paper's
notion is the special case `B = Finset.Icc a b`. -/
def IsFullyPairedOn (κ : PartialPairing (Fin m)) (B : Finset (Fin m)) : Prop :=
  (∀ i ∈ B, κ i ≠ i) ∧ ∀ i ∈ B, κ i ∈ B

instance (κ : PartialPairing (Fin m)) (B : Finset (Fin m)) :
    Decidable (IsFullyPairedOn κ B) :=
  decidable_of_iff ((∀ i ∈ B, κ i ≠ i) ∧ ∀ i ∈ B, κ i ∈ B) Iff.rfl

namespace IsFullyPairedOn

variable {κ : PartialPairing (Fin m)} {B B₁ B₂ : Finset (Fin m)}

theorem ne_of_mem (h : IsFullyPairedOn κ B) {i : Fin m} (hi : i ∈ B) :
    κ i ≠ i := h.1 i hi

theorem apply_mem (h : IsFullyPairedOn κ B) {i : Fin m} (hi : i ∈ B) :
    κ i ∈ B := h.2 i hi

theorem apply_notMem (h : IsFullyPairedOn κ B) {i : Fin m} (hi : i ∉ B) :
    κ i ∉ B := κ.apply_notMem h.2 hi

/-- The intersection of two fully paired sets is fully paired. -/
theorem inter (h₁ : IsFullyPairedOn κ B₁) (h₂ : IsFullyPairedOn κ B₂) :
    IsFullyPairedOn κ (B₁ ∩ B₂) := by
  constructor
  · intro i hi
    exact h₁.1 i (Finset.mem_inter.mp hi).1
  · intro i hi
    obtain ⟨hi₁, hi₂⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_inter.mpr ⟨h₁.2 i hi₁, h₂.2 i hi₂⟩

/-- The union of two fully paired sets is fully paired. -/
theorem union (h₁ : IsFullyPairedOn κ B₁) (h₂ : IsFullyPairedOn κ B₂) :
    IsFullyPairedOn κ (B₁ ∪ B₂) := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact h₁.1 i hi
    · exact h₂.1 i hi
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (h₁.2 i hi)
    · exact Finset.mem_union_right _ (h₂.2 i hi)

end IsFullyPairedOn

@[simp]
theorem isFullyPairedOn_empty (κ : PartialPairing (Fin m)) :
    IsFullyPairedOn κ ∅ :=
  ⟨fun i hi => absurd hi (Finset.notMem_empty i),
    fun i hi => absurd hi (Finset.notMem_empty i)⟩

theorem isFullyPairedOn_univ_iff {κ : PartialPairing (Fin m)} :
    IsFullyPairedOn κ Finset.univ ↔ κ.IsFull := by
  simp [IsFullyPairedOn, PartialPairing.IsFull]

/-- Structural lemma for the §4.1 Dyck-word bookkeeping: two fully paired
subintervals always have fully paired intersection and union (this
strengthens the paper's silent "disjoint or nested or overlapping" case
analysis: in the overlapping case both `∩` and `∪` are again fully
paired). -/
theorem isFullyPairedOn_Icc_inter_union {κ : PartialPairing (Fin m)}
    {a b c d : Fin m} (h₁ : IsFullyPairedOn κ (Finset.Icc a b))
    (h₂ : IsFullyPairedOn κ (Finset.Icc c d)) :
    IsFullyPairedOn κ (Finset.Icc a b ∩ Finset.Icc c d) ∧
      IsFullyPairedOn κ (Finset.Icc a b ∪ Finset.Icc c d) :=
  ⟨h₁.inter h₂, h₁.union h₂⟩

/-- `κ` admits a fully paired subinterval, the whole index interval being
allowed.  This is the hypothesis of the Def 3.1(2) selector
`leastFullyPairedSubinterval`. -/
def HasFullyPairedSubinterval (κ : PartialPairing (Fin m)) : Prop :=
  ∃ a b : Fin m, a ≤ b ∧ IsFullyPairedOn κ (Finset.Icc a b)

instance (κ : PartialPairing (Fin m)) : Decidable (HasFullyPairedSubinterval κ) :=
  decidable_of_iff (∃ a b : Fin m, a ≤ b ∧ IsFullyPairedOn κ (Finset.Icc a b))
    Iff.rfl

/-- `κ` admits a *proper* fully paired subinterval (one that is not the whole
index interval).  Its negation is primitivity, paper Def 2.3. -/
def HasProperFullyPairedSubinterval (κ : PartialPairing (Fin m)) : Prop :=
  ∃ a b : Fin m, a ≤ b ∧ Finset.Icc a b ≠ Finset.univ ∧
    IsFullyPairedOn κ (Finset.Icc a b)

instance (κ : PartialPairing (Fin m)) :
    Decidable (HasProperFullyPairedSubinterval κ) :=
  decidable_of_iff (∃ a b : Fin m, a ≤ b ∧ Finset.Icc a b ≠ Finset.univ ∧
    IsFullyPairedOn κ (Finset.Icc a b)) Iff.rfl

theorem HasProperFullyPairedSubinterval.hasFullyPairedSubinterval
    {κ : PartialPairing (Fin m)} (h : HasProperFullyPairedSubinterval κ) :
    HasFullyPairedSubinterval κ := by
  obtain ⟨a, b, hab, -, hfp⟩ := h
  exact ⟨a, b, hab, hfp⟩

/-- **Paper Def 2.3 (node D-int).**  A partial pairing of `Fin m` is
*primitive* if it has no proper fully paired subinterval: every fully paired
subinterval is the whole of `Fin m`.  (For a primitive *full* pairing the
whole interval is itself fully paired, so primitivity does not exclude it.) -/
def IsPrimitive (κ : PartialPairing (Fin m)) : Prop :=
  ∀ a b : Fin m, a ≤ b → IsFullyPairedOn κ (Finset.Icc a b) →
    Finset.Icc a b = Finset.univ

instance (κ : PartialPairing (Fin m)) : Decidable (IsPrimitive κ) :=
  decidable_of_iff (∀ a b : Fin m, a ≤ b → IsFullyPairedOn κ (Finset.Icc a b) →
    Finset.Icc a b = Finset.univ) Iff.rfl

theorem isPrimitive_iff_not_hasProperFullyPairedSubinterval
    {κ : PartialPairing (Fin m)} :
    IsPrimitive κ ↔ ¬HasProperFullyPairedSubinterval κ := by
  constructor
  · rintro hp ⟨a, b, hab, hne, hfp⟩
    exact hne (hp a b hab hfp)
  · intro h a b hab hfp
    by_contra hne
    exact h ⟨a, b, hab, hne, hfp⟩

theorem Icc_zero_last_eq_univ : Finset.Icc (0 : Fin (m + 1)) (Fin.last m) =
    Finset.univ := by
  ext i
  simp [Finset.mem_Icc, Fin.zero_le i, Fin.le_last i]

/-- A full pairing of a nonempty index interval always has a fully paired
subinterval, namely the whole interval — the situation in which the Def 3.1
induction keeps running until the interval itself is removed. -/
theorem PartialPairing.IsFull.hasFullyPairedSubinterval
    {κ : PartialPairing (Fin (m + 1))} (hκ : κ.IsFull) :
    HasFullyPairedSubinterval κ :=
  ⟨0, Fin.last m, Fin.zero_le _, by
    rw [Icc_zero_last_eq_univ]
    exact isFullyPairedOn_univ_iff.mpr hκ⟩

/-! ## The Def 3.1(2) selector: smallest, leftmost fully paired subinterval -/

/-- Endpoint pairs `(a, b)`, `a ≤ b`, of fully paired subintervals of `κ`. -/
def fpIntervals (κ : PartialPairing (Fin m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => p.1 ≤ p.2 ∧ IsFullyPairedOn κ (Finset.Icc p.1 p.2)

theorem mem_fpIntervals {κ : PartialPairing (Fin m)} {p : Fin m × Fin m} :
    p ∈ fpIntervals κ ↔ p.1 ≤ p.2 ∧ IsFullyPairedOn κ (Finset.Icc p.1 p.2) := by
  simp [fpIntervals]

theorem fpIntervals_nonempty_iff {κ : PartialPairing (Fin m)} :
    (fpIntervals κ).Nonempty ↔ HasFullyPairedSubinterval κ := by
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_fpIntervals] at hp
    exact ⟨p.1, p.2, hp.1, hp.2⟩
  · rintro ⟨a, b, hab, hfp⟩
    exact ⟨(a, b), mem_fpIntervals.mpr ⟨hab, hfp⟩⟩

/-- The minimal length `b - a` over all fully paired subintervals
`Finset.Icc a b` of `κ`. -/
def minPairedLength (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) : ℕ :=
  ((fpIntervals κ).image fun p => (p.2 : ℕ) - (p.1 : ℕ)).min'
    ((fpIntervals_nonempty_iff.mpr h).image _)

/-- Minimality of `minPairedLength`. -/
theorem minPairedLength_le {κ : PartialPairing (Fin m)}
    (h : HasFullyPairedSubinterval κ) {a b : Fin m} (hab : a ≤ b)
    (hfp : IsFullyPairedOn κ (Finset.Icc a b)) :
    minPairedLength κ h ≤ (b : ℕ) - (a : ℕ) := by
  apply Finset.min'_le
  exact Finset.mem_image_of_mem _
    ((mem_fpIntervals (p := (a, b))).mpr ⟨hab, hfp⟩)

/-- Fully paired subintervals achieving the minimal length. -/
def minCands (κ : PartialPairing (Fin m)) (h : HasFullyPairedSubinterval κ) :
    Finset (Fin m × Fin m) :=
  (fpIntervals κ).filter fun p => (p.2 : ℕ) - (p.1 : ℕ) = minPairedLength κ h

theorem mem_minCands {κ : PartialPairing (Fin m)}
    {h : HasFullyPairedSubinterval κ} {p : Fin m × Fin m} :
    p ∈ minCands κ h ↔ (p.1 ≤ p.2 ∧ IsFullyPairedOn κ (Finset.Icc p.1 p.2)) ∧
      (p.2 : ℕ) - (p.1 : ℕ) = minPairedLength κ h := by
  simp only [minCands, Finset.mem_filter, mem_fpIntervals]

theorem minCands_nonempty (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) : (minCands κ h).Nonempty := by
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((fpIntervals κ).image fun p => (p.2 : ℕ) - (p.1 : ℕ))
      ((fpIntervals_nonempty_iff.mpr h).image _))
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpe⟩⟩

/-- The left endpoint selected by paper Def 3.1(2): leftmost among the
minimal-length fully paired subintervals. -/
def leastLeft (κ : PartialPairing (Fin m)) (h : HasFullyPairedSubinterval κ) :
    Fin m :=
  ((minCands κ h).image Prod.fst).min' ((minCands_nonempty κ h).image _)

theorem exists_leastLeft_snd (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) :
    ∃ b, (leastLeft κ h, b) ∈ minCands κ h := by
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((minCands κ h).image Prod.fst)
      ((minCands_nonempty κ h).image _))
  have hpe' : p.1 = leastLeft κ h := hpe
  have hpp : (leastLeft κ h, p.2) = p := by rw [← hpe']
  exact ⟨p.2, hpp ▸ hp⟩

/-- Leftmost-ness of `leastLeft` among minimal-length fully paired
subintervals. -/
theorem leastLeft_le {κ : PartialPairing (Fin m)}
    (h : HasFullyPairedSubinterval κ) {a b : Fin m} (hab : a ≤ b)
    (hfp : IsFullyPairedOn κ (Finset.Icc a b))
    (hlen : (b : ℕ) - (a : ℕ) = minPairedLength κ h) : leastLeft κ h ≤ a := by
  apply Finset.min'_le
  exact Finset.mem_image_of_mem _
    ((mem_minCands (p := (a, b))).mpr ⟨⟨hab, hfp⟩, hlen⟩)

theorem leastLeft_add_minPairedLength_lt (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) :
    (leastLeft κ h : ℕ) + minPairedLength κ h < m := by
  obtain ⟨b, hb⟩ := exists_leastLeft_snd κ h
  rw [mem_minCands] at hb
  obtain ⟨⟨hab, -⟩, hlen⟩ := hb
  have h1 : (leastLeft κ h : ℕ) ≤ (b : ℕ) := hab
  have h2 : (b : ℕ) < m := b.isLt
  have h3 : (b : ℕ) - (leastLeft κ h : ℕ) = minPairedLength κ h := hlen
  omega

/-- **Paper Def 3.1(2) selector.**  Among all fully paired subintervals of `κ`
(the whole interval allowed), the one of smallest length and, among those, the
leftmost; returned as its pair of endpoints `(a, b)`. -/
def leastFullyPairedSubinterval (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) : Fin m × Fin m :=
  (leastLeft κ h,
    ⟨(leastLeft κ h : ℕ) + minPairedLength κ h,
      leastLeft_add_minPairedLength_lt κ h⟩)

theorem leastFullyPairedSubinterval_fst (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) :
    (leastFullyPairedSubinterval κ h).1 = leastLeft κ h := rfl

theorem leastFullyPairedSubinterval_mem (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) :
    leastFullyPairedSubinterval κ h ∈ minCands κ h := by
  obtain ⟨b, hb⟩ := exists_leastLeft_snd κ h
  have hb' := hb
  rw [mem_minCands] at hb'
  obtain ⟨⟨hab, -⟩, hlen⟩ := hb'
  have h1 : (leastLeft κ h : ℕ) ≤ (b : ℕ) := hab
  have h3 : (b : ℕ) - (leastLeft κ h : ℕ) = minPairedLength κ h := hlen
  have hbe : b = ⟨(leastLeft κ h : ℕ) + minPairedLength κ h,
      leastLeft_add_minPairedLength_lt κ h⟩ := by
    apply Fin.ext
    show (b : ℕ) = (leastLeft κ h : ℕ) + minPairedLength κ h
    omega
  show (leastLeft κ h,
    (⟨(leastLeft κ h : ℕ) + minPairedLength κ h,
      leastLeft_add_minPairedLength_lt κ h⟩ : Fin m)) ∈ minCands κ h
  rw [← hbe]
  exact hb

/-- The selected subinterval is a genuine interval: `a ≤ b`. -/
theorem leastFullyPairedSubinterval_fst_le_snd (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) :
    (leastFullyPairedSubinterval κ h).1 ≤ (leastFullyPairedSubinterval κ h).2 := by
  have h1 := leastFullyPairedSubinterval_mem κ h
  rw [mem_minCands] at h1
  exact h1.1.1

/-- The selected subinterval is fully paired. -/
theorem leastFullyPairedSubinterval_isFullyPairedOn (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) :
    IsFullyPairedOn κ (Finset.Icc (leastFullyPairedSubinterval κ h).1
      (leastFullyPairedSubinterval κ h).2) := by
  have h1 := leastFullyPairedSubinterval_mem κ h
  rw [mem_minCands] at h1
  exact h1.1.2

/-- The selected subinterval has the minimal length. -/
theorem leastFullyPairedSubinterval_length (κ : PartialPairing (Fin m))
    (h : HasFullyPairedSubinterval κ) :
    ((leastFullyPairedSubinterval κ h).2 : ℕ) -
      ((leastFullyPairedSubinterval κ h).1 : ℕ) = minPairedLength κ h := by
  have h1 := leastFullyPairedSubinterval_mem κ h
  rw [mem_minCands] at h1
  exact h1.2

/-- Uniqueness: a fully paired subinterval of minimal length whose left
endpoint is the selected one *is* the selected subinterval. -/
theorem eq_leastFullyPairedSubinterval {κ : PartialPairing (Fin m)}
    (h : HasFullyPairedSubinterval κ) {a b : Fin m} (hab : a ≤ b)
    (_hfp : IsFullyPairedOn κ (Finset.Icc a b))
    (hlen : (b : ℕ) - (a : ℕ) = minPairedLength κ h)
    (hfst : a = leastLeft κ h) :
    (a, b) = leastFullyPairedSubinterval κ h := by
  have h1 : (a : ℕ) ≤ (b : ℕ) := hab
  refine Prod.ext_iff.mpr ⟨hfst, Fin.ext ?_⟩
  show (b : ℕ) = (leastLeft κ h : ℕ) + minPairedLength κ h
  rw [← hfst]
  omega

/-- The selected subinterval is also smallest with respect to inclusion: a
fully paired subinterval contained in it coincides with it. -/
theorem leastFullyPairedSubinterval_inclusion_minimal
    {κ : PartialPairing (Fin m)} (h : HasFullyPairedSubinterval κ)
    {c d : Fin m} (hcd : c ≤ d) (hfp : IsFullyPairedOn κ (Finset.Icc c d))
    (hsub : Finset.Icc c d ⊆ Finset.Icc (leastFullyPairedSubinterval κ h).1
      (leastFullyPairedSubinterval κ h).2) :
    Finset.Icc c d = Finset.Icc (leastFullyPairedSubinterval κ h).1
      (leastFullyPairedSubinterval κ h).2 := by
  have hlen := leastFullyPairedSubinterval_length κ h
  rw [Finset.Icc_subset_Icc_iff hcd] at hsub
  obtain ⟨hAc, hdB⟩ := hsub
  have hmin : minPairedLength κ h ≤ (d : ℕ) - (c : ℕ) :=
    minPairedLength_le h hcd hfp
  have h1 : ((leastFullyPairedSubinterval κ h).1 : ℕ) ≤ (c : ℕ) := hAc
  have h2 : (d : ℕ) ≤ ((leastFullyPairedSubinterval κ h).2 : ℕ) := hdB
  have h3 : (c : ℕ) ≤ (d : ℕ) := hcd
  have h4 : (c : ℕ) = ((leastFullyPairedSubinterval κ h).1 : ℕ) ∧
      (d : ℕ) = ((leastFullyPairedSubinterval κ h).2 : ℕ) := by omega
  rw [Fin.ext h4.1, Fin.ext h4.2]

/-! ## Interval removal (paper Def 3.1(2a))

Primary version: the induced pairing on the complement **subtype**
`{i : Fin m // i ∉ Finset.Icc a b}` — no `Fin` re-indexing arithmetic.  The
re-indexed version on `Fin (m - (Finset.Icc a b).card)` is obtained by
transporting along the order isomorphism `complOrderIso`. -/

namespace PartialPairing

/-- Remove a fully paired subinterval from a pairing: the induced pairing on
the complement subtype.  Well-defined because a fully paired set is
`κ`-closed, hence so is its complement. -/
def removeInterval (κ : PartialPairing (Fin m)) {a b : Fin m}
    (h : IsFullyPairedOn κ (Finset.Icc a b)) :
    PartialPairing {i : Fin m // i ∉ Finset.Icc a b} :=
  κ.restrictCompl h.2

@[simp]
theorem removeInterval_apply_coe (κ : PartialPairing (Fin m)) {a b : Fin m}
    (h : IsFullyPairedOn κ (Finset.Icc a b))
    (i : {i : Fin m // i ∉ Finset.Icc a b}) :
    (κ.removeInterval h i : Fin m) = κ i.1 := rfl

end PartialPairing

/-- The complement subtype of `B : Finset (Fin m)`, rephrased as the coercion
of the finset `Bᶜ`. -/
def notMemOrderIso (B : Finset (Fin m)) :
    {i : Fin m // i ∉ B} ≃o {i : Fin m // i ∈ Bᶜ} where
  toEquiv := Equiv.subtypeEquivRight fun i => (Finset.mem_compl (a := i)).symm
  map_rel_iff' := Iff.rfl

/-- The order isomorphism between the complement of `B : Finset (Fin m)` and
`Fin (m - B.card)`, given by the unique monotone enumeration. -/
def complOrderIso (B : Finset (Fin m)) :
    {i : Fin m // i ∉ B} ≃o Fin (m - B.card) :=
  (notMemOrderIso B).trans
    (Bᶜ.orderIsoOfFin (by rw [Finset.card_compl, Fintype.card_fin])).symm

/-- Interval removal, re-indexed over `Fin (m - (Finset.Icc a b).card)` by the
monotone enumeration of the complement.  `removeInterval` (the subtype
version) is the primary API; this is the transported form. -/
def removeIntervalFin (κ : PartialPairing (Fin m)) {a b : Fin m}
    (h : IsFullyPairedOn κ (Finset.Icc a b)) :
    PartialPairing (Fin (m - (Finset.Icc a b).card)) :=
  PartialPairing.congr (complOrderIso (Finset.Icc a b)).toEquiv
    (κ.removeInterval h)

theorem removeIntervalFin_def (κ : PartialPairing (Fin m)) {a b : Fin m}
    (h : IsFullyPairedOn κ (Finset.Icc a b)) :
    removeIntervalFin κ h =
      PartialPairing.congr (complOrderIso (Finset.Icc a b)).toEquiv
        (κ.removeInterval h) := rfl

/-- Specification of `removeIntervalFin`: it is the conjugate of `κ` (restricted
to the complement) under the monotone enumeration `complOrderIso`. -/
theorem removeIntervalFin_apply (κ : PartialPairing (Fin m)) {a b : Fin m}
    (h : IsFullyPairedOn κ (Finset.Icc a b))
    (i : {i : Fin m // i ∉ Finset.Icc a b}) :
    removeIntervalFin κ h (complOrderIso (Finset.Icc a b) i) =
      complOrderIso (Finset.Icc a b) ⟨κ i.1, κ.apply_notMem h.2 i.2⟩ := by
  show (complOrderIso (Finset.Icc a b)).toEquiv
      ((κ.removeInterval h) ((complOrderIso (Finset.Icc a b)).toEquiv.symm
        ((complOrderIso (Finset.Icc a b)).toEquiv i))) =
    (complOrderIso (Finset.Icc a b)).toEquiv ⟨κ i.1, κ.apply_notMem h.2 i.2⟩
  rw [Equiv.symm_apply_apply]
  rfl

end Anderson4D
