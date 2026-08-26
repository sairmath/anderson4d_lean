import Anderson4D.PermSum.SingleScalePosition
import Anderson4D.PermSum.SingleScaleAnchorChoice

/-!
# Anchored reindexing for the arrangement Fubini step

The two outward elimination runs must enumerate every non-anchor position
exactly once while retaining the same labeled copy at the anchor.  This file
packages that positional fact as an actual equivalence of `Fin (n + 1)`.

The equivalence sends position zero to the anchor and then follows the
flattened left/right schedule.  Precomposition therefore reindexes labeled
arrangements bijectively; in particular this operation cannot introduce an
extra factorial or duplicate the anchor.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Read a length-`n` list as a function on `Fin n`. -/
def scheduleTail {α : Type*} {n : ℕ}
    (order : List α) (hlen : order.length = n) : Fin n → α :=
  fun i => order.get (Fin.cast hlen.symm i)

theorem scheduleTail_injective {α : Type*} {n : ℕ}
    (order : List α) (hlen : order.length = n)
    (hnodup : order.Nodup) :
    Function.Injective (scheduleTail order hlen) := by
  intro i j hij
  apply Fin.cast_injective hlen.symm
  exact hnodup.injective_get hij

theorem scheduleTail_mem {α : Type*} {n : ℕ}
    (order : List α) (hlen : order.length = n) (i : Fin n) :
    scheduleTail order hlen i ∈ order := by
  exact order.get_mem (Fin.cast hlen.symm i)

/--
The function which places `anchor` first and then reads the supplied
schedule.  The hypotheses say precisely that the schedule lists every
non-anchor position once.
-/
def anchoredScheduleFunction {n : ℕ}
    (anchor : Fin (n + 1)) (order : List (Fin (n + 1)))
    (hlen : order.length = n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cons anchor (scheduleTail order hlen)

theorem anchoredScheduleFunction_injective {n : ℕ}
    (anchor : Fin (n + 1)) (order : List (Fin (n + 1)))
    (hlen : order.length = n) (hnodup : order.Nodup)
    (hcover : ∀ i : Fin (n + 1), i ∈ order ↔ i ≠ anchor) :
    Function.Injective
      (anchoredScheduleFunction anchor order hlen) := by
  rw [anchoredScheduleFunction, Fin.cons_injective_iff]
  constructor
  · rintro ⟨i, hi⟩
    have hmem : scheduleTail order hlen i ∈ order :=
      scheduleTail_mem order hlen i
    exact (hcover _).mp hmem hi
  · exact scheduleTail_injective order hlen hnodup

/--
The anchored schedule is a genuine permutation of the position type.
Using an `Equiv` here, rather than a quotient or a cardinality identity,
lets later sums be reindexed without any multiplicity factor.
-/
noncomputable def anchoredScheduleEquiv {n : ℕ}
    (anchor : Fin (n + 1)) (order : List (Fin (n + 1)))
    (hlen : order.length = n) (hnodup : order.Nodup)
    (hcover : ∀ i : Fin (n + 1), i ∈ order ↔ i ≠ anchor) :
    Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.ofBijective
    (anchoredScheduleFunction anchor order hlen)
    ((Fintype.bijective_iff_injective_and_card
      (anchoredScheduleFunction anchor order hlen)).2
        ⟨anchoredScheduleFunction_injective
            anchor order hlen hnodup hcover, rfl⟩)

/--
Version of `anchoredScheduleEquiv` whose target is an arbitrary finite type
of cardinality `n+1`.  This avoids relying on a syntactic presentation of
the paper length as a successor.
-/
noncomputable def anchoredScheduleEquivTo
    {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ}
    (anchor : β) (order : List β) (hlen : order.length = n)
    (hnodup : order.Nodup)
    (hcover : ∀ b : β, b ∈ order ↔ b ≠ anchor)
    (hcard : Fintype.card β = n + 1) :
    Fin (n + 1) ≃ β :=
  Equiv.ofBijective
    (Fin.cons anchor (scheduleTail order hlen))
    ((Fintype.bijective_iff_injective_and_card
      (Fin.cons anchor (scheduleTail order hlen))).2
        ⟨by
          rw [Fin.cons_injective_iff]
          constructor
          · rintro ⟨i, hi⟩
            exact ((hcover _).mp
              (scheduleTail_mem order hlen i)) hi
          · exact scheduleTail_injective order hlen hnodup,
          by simp [hcard]⟩)

@[simp] theorem anchoredScheduleEquivTo_zero
    {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ}
    (anchor : β) (order : List β) (hlen : order.length = n)
    (hnodup : order.Nodup)
    (hcover : ∀ b : β, b ∈ order ↔ b ≠ anchor)
    (hcard : Fintype.card β = n + 1) :
    anchoredScheduleEquivTo
      anchor order hlen hnodup hcover hcard 0 = anchor :=
  rfl

@[simp] theorem anchoredScheduleEquivTo_succ
    {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ}
    (anchor : β) (order : List β) (hlen : order.length = n)
    (hnodup : order.Nodup)
    (hcover : ∀ b : β, b ∈ order ↔ b ≠ anchor)
    (hcard : Fintype.card β = n + 1) (i : Fin n) :
    anchoredScheduleEquivTo
      anchor order hlen hnodup hcover hcard i.succ =
        scheduleTail order hlen i :=
  rfl

@[simp] theorem anchoredScheduleEquiv_zero {n : ℕ}
    (anchor : Fin (n + 1)) (order : List (Fin (n + 1)))
    (hlen : order.length = n) (hnodup : order.Nodup)
    (hcover : ∀ i : Fin (n + 1), i ∈ order ↔ i ≠ anchor) :
    anchoredScheduleEquiv anchor order hlen hnodup hcover 0 = anchor := by
  rfl

@[simp] theorem anchoredScheduleEquiv_succ {n : ℕ}
    (anchor : Fin (n + 1)) (order : List (Fin (n + 1)))
    (hlen : order.length = n) (hnodup : order.Nodup)
    (hcover : ∀ i : Fin (n + 1), i ∈ order ↔ i ≠ anchor)
    (i : Fin n) :
    anchoredScheduleEquiv anchor order hlen hnodup hcover i.succ =
      scheduleTail order hlen i := by
  rfl

/-- The concrete outward order used by the one-parity schedule. -/
def finAnchorOutwardOrderWithPhases {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    List (Fin (n + 1)) :=
  (finAnchorPositionScheduleWithPhases
    leftPhase rightPhase anchor).flatMap PositionBlock.entries

@[simp] theorem length_finAnchorOutwardOrderWithPhases {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    (finAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor).length = n := by
  simpa [finAnchorOutwardOrderWithPhases] using
    length_flatten_finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor

theorem nodup_finAnchorOutwardOrderWithPhases {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    (finAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor).Nodup := by
  exact nodup_flatten_finAnchorPositionScheduleWithPhases
    leftPhase rightPhase anchor

@[simp] theorem mem_finAnchorOutwardOrderWithPhases_iff {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor i : Fin (n + 1)) :
    i ∈ finAnchorOutwardOrderWithPhases
        leftPhase rightPhase anchor ↔
      i ≠ anchor := by
  exact mem_flatten_finAnchorPositionScheduleWithPhases_iff
    leftPhase rightPhase anchor i

/--
Concrete permutation which reads the anchor first and then all positions in
the exact left-outward/right-outward block order.
-/
noncomputable def finAnchorOutwardEquivWithPhases {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    Fin (n + 1) ≃ Fin (n + 1) :=
  anchoredScheduleEquiv anchor
    (finAnchorOutwardOrderWithPhases leftPhase rightPhase anchor)
    (length_finAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor)
    (nodup_finAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor)
    (mem_finAnchorOutwardOrderWithPhases_iff
      leftPhase rightPhase anchor)

@[simp] theorem finAnchorOutwardEquivWithPhases_zero {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    finAnchorOutwardEquivWithPhases
      leftPhase rightPhase anchor 0 = anchor := by
  rfl

/-- Precompose an arrangement by a permutation of its positions. -/
def reindexArrangement {ι β : Type*}
    (e : ι ≃ ι) (σ : ι ≃ β) : ι ≃ β :=
  e.trans σ

/-- Position reindexing is itself a bijection on the arrangement carrier. -/
def arrangementReindexEquiv {ι β : Type*}
    (e : ι ≃ ι) : (ι ≃ β) ≃ (ι ≃ β) where
  toFun σ := reindexArrangement e σ
  invFun σ := reindexArrangement e.symm σ
  left_inv σ := by
    ext i
    simp [reindexArrangement]
  right_inv σ := by
    ext i
    simp [reindexArrangement]

/--
Change the position type of an arrangement by precomposition.  Unlike
`arrangementReindexEquiv`, the two position types may merely be equivalent;
this is used below to replace the paper length `m` by `(m - 1) + 1`.
-/
def arrangementDomainEquiv {ι κ β : Type*}
    (e : ι ≃ κ) : (κ ≃ β) ≃ (ι ≃ β) where
  toFun σ := e.trans σ
  invFun σ := e.symm.trans σ
  left_inv σ := by
    ext i
    simp
  right_inv σ := by
    ext i
    simp

@[simp] theorem arrangementDomainEquiv_apply {ι κ β : Type*}
    (e : ι ≃ κ) (σ : κ ≃ β) (i : ι) :
    arrangementDomainEquiv e σ i = σ (e i) :=
  rfl

@[simp] theorem arrangementReindexEquiv_apply {ι β : Type*}
    (e : ι ≃ ι) (σ : ι ≃ β) (i : ι) :
    arrangementReindexEquiv e σ i = σ (e i) :=
  rfl

@[simp] theorem arrangementReindexEquiv_symm_apply {ι β : Type*}
    (e : ι ≃ ι) (σ : ι ≃ β) (i : ι) :
    (arrangementReindexEquiv e).symm σ i = σ (e.symm i) :=
  rfl

/-- Reindex a fixed active `(N,X)` word by the same position permutation. -/
def reindexNXWord {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin m ≃ Fin m)
    (x : Fin m → ActiveNXClass Nm mu) :
    Fin m → ActiveNXClass Nm mu :=
  fun i => x (e i)

@[simp] theorem reindexNXWord_symm_apply
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin m ≃ Fin m) (x : Fin m → ActiveNXClass Nm mu) :
    reindexNXWord Nm mu e.symm (reindexNXWord Nm mu e x) = x := by
  funext i
  simp [reindexNXWord]

@[simp] theorem arrangementNXWord_reindex
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin (totalMultiplicity mu) ≃ Fin (totalMultiplicity mu))
    (σ : HeppArrangement mu) :
    arrangementNXWord Nm mu (reindexArrangement e σ) =
      reindexNXWord Nm mu e (arrangementNXWord Nm mu σ) := by
  rfl

theorem reindexArrangement_mem_arrangementsAtNXWord_iff
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin (totalMultiplicity mu) ≃ Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (σ : HeppArrangement mu) :
    reindexArrangement e σ ∈
        arrangementsAtNXWord Nm mu (reindexNXWord Nm mu e x) ↔
      σ ∈ arrangementsAtNXWord Nm mu x := by
  rw [mem_arrangementsAtNXWord_iff, mem_arrangementsAtNXWord_iff,
    arrangementNXWord_reindex]
  constructor
  · intro h
    funext i
    have hi := congrFun h (e.symm i)
    simpa [reindexNXWord] using hi
  · intro h
    subst x
    rfl

/--
The fixed-class-word arrangement fiber is carried bijectively to the
reindexed class-word fiber.  This is the fiberwise form needed after the
outer finite-Fubini decomposition.
-/
noncomputable def arrangementsAtNXWordReindexEquiv
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin (totalMultiplicity mu) ≃ Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    {σ : HeppArrangement mu //
      σ ∈ arrangementsAtNXWord Nm mu x} ≃
      {σ : HeppArrangement mu //
        σ ∈ arrangementsAtNXWord Nm mu
          (reindexNXWord Nm mu e x)} where
  toFun σ :=
    ⟨reindexArrangement e σ.1,
      (reindexArrangement_mem_arrangementsAtNXWord_iff
        Nm mu e x σ.1).2 σ.2⟩
  invFun σ :=
    ⟨reindexArrangement e.symm σ.1, by
      have h :=
        (reindexArrangement_mem_arrangementsAtNXWord_iff
          Nm mu e.symm (reindexNXWord Nm mu e x) σ.1).2 σ.2
      simpa using h⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp [reindexArrangement]
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp [reindexArrangement]

@[simp] theorem arrangementsAtNXWordReindexEquiv_pullback
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin (totalMultiplicity mu) ≃ Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (σ : {σ : HeppArrangement mu //
      σ ∈ arrangementsAtNXWord Nm mu x}) :
    reindexArrangement e.symm
        ((arrangementsAtNXWordReindexEquiv Nm mu e x σ).1) =
      σ.1 := by
  apply Equiv.ext
  intro i
  simp [arrangementsAtNXWordReindexEquiv, reindexArrangement]

private theorem sum_finset_eq_sum_members {α : Type*}
    [Fintype α] [DecidableEq α]
    (s : Finset α) (F : α → ℝ) :
    (∑ x ∈ s, F x) = ∑ x : {x // x ∈ s}, F x.1 := by
  rw [← Finset.sum_attach]
  rw [Finset.attach_eq_univ]

/--
Exact fiberwise sum reindexing.  The right-hand fiber has the class word in
anchored order, and its summand is pulled back to the original position
order.  No multiplicity coefficient appears.
-/
theorem sum_arrangementsAtNXWord_reindex
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin (totalMultiplicity mu) ≃ Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (F : HeppArrangement mu → ℝ) :
    (∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ) =
      ∑ τ ∈ arrangementsAtNXWord Nm mu
          (reindexNXWord Nm mu e x),
        F (reindexArrangement e.symm τ) := by
  classical
  calc
    (∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ) =
        ∑ σ : {σ : HeppArrangement mu //
          σ ∈ arrangementsAtNXWord Nm mu x}, F σ.1 :=
      sum_finset_eq_sum_members
        (arrangementsAtNXWord Nm mu x) (fun σ => F σ)
    _ =
        ∑ τ : {τ : HeppArrangement mu //
          τ ∈ arrangementsAtNXWord Nm mu
            (reindexNXWord Nm mu e x)},
          F (reindexArrangement e.symm τ.1) := by
      simpa only [arrangementsAtNXWordReindexEquiv_pullback] using
        (Equiv.sum_comp
          (arrangementsAtNXWordReindexEquiv Nm mu e x)
          (fun τ => F (reindexArrangement e.symm τ.1)))
    _ =
        ∑ τ ∈ arrangementsAtNXWord Nm mu
            (reindexNXWord Nm mu e x),
          F (reindexArrangement e.symm τ) :=
      (sum_finset_eq_sum_members
        (arrangementsAtNXWord Nm mu
          (reindexNXWord Nm mu e x))
        (fun τ => F (reindexArrangement e.symm τ))).symm

/--
Exact finite-Fubini reindexing of the full arrangement sum.  There is no
cardinality coefficient: the right side is merely the same carrier read in
anchored schedule order.
-/
theorem sum_arrangements_reindex {ι β : Type*}
    [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]
    (e : ι ≃ ι) (F : (ι ≃ β) → ℝ) :
    (∑ σ : ι ≃ β, F σ) =
      ∑ σ : ι ≃ β, F ((arrangementReindexEquiv e).symm σ) := by
  exact (Equiv.sum_comp (arrangementReindexEquiv e).symm F).symm

/--
Concrete anchored specialization.  The summation variable on the right has
its zeroth labeled copy equal to the original arrangement's anchor copy.
-/
theorem sum_arrangements_finAnchorOutward_reindex
    {t : PlaneTree} {mu : Multiplicities t} {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (F : (Fin (n + 1) ≃ HeppLabeledCopy mu) → ℝ) :
    (∑ σ : Fin (n + 1) ≃ HeppLabeledCopy mu, F σ) =
      ∑ σ : Fin (n + 1) ≃ HeppLabeledCopy mu,
        F ((arrangementReindexEquiv
          (finAnchorOutwardEquivWithPhases
            leftPhase rightPhase anchor)).symm σ) :=
  sum_arrangements_reindex
    (finAnchorOutwardEquivWithPhases
      leftPhase rightPhase anchor) F

/-! ## The non-vacuous paper-length carrier -/

/-- The labeled-copy carrier has exactly the paper word length. -/
@[simp] theorem card_heppLabeledCopy {t : PlaneTree}
    (mu : Multiplicities t) :
    Fintype.card (HeppLabeledCopy mu) = totalMultiplicity mu := by
  simp [HeppLabeledCopy, totalMultiplicity]

/-- Number of positions remaining after the distinguished anchor is fixed. -/
def paperTailLength {t : PlaneTree} (mu : Multiplicities t) : ℕ :=
  totalMultiplicity mu - 1

@[simp] theorem one_le_paperTailLength {t : PlaneTree}
    (mu : Multiplicities t) :
  1 ≤ paperTailLength mu := by
  have htwo := two_le_totalMultiplicity mu
  unfold paperTailLength
  omega

@[simp] theorem paperTailLength_add_one {t : PlaneTree}
    (mu : Multiplicities t) :
    paperTailLength mu + 1 = totalMultiplicity mu := by
  have htwo := two_le_totalMultiplicity mu
  simp [paperTailLength, Nat.sub_add_cancel (by omega : 1 ≤ totalMultiplicity mu)]

/-- Canonical cast from the head-plus-tail positions to the paper positions. -/
def paperPositionEquiv {t : PlaneTree} (mu : Multiplicities t) :
    Fin (paperTailLength mu + 1) ≃ Fin (totalMultiplicity mu) :=
  (Fin.castOrderIso (paperTailLength_add_one mu)).toEquiv

/--
Every paper arrangement may therefore be read, non-vacuously, as one head
followed by exactly `paperTailLength` tail positions.
-/
def paperArrangementEquivHeadTailPositions {t : PlaneTree}
    (mu : Multiplicities t) :
    HeppArrangement mu ≃
      (Fin (paperTailLength mu + 1) ≃ HeppLabeledCopy mu) :=
  arrangementDomainEquiv (paperPositionEquiv mu)

@[simp] theorem card_heppLabeledCopy_eq_paperTailLength_add_one
    {t : PlaneTree} (mu : Multiplicities t) :
    Fintype.card (HeppLabeledCopy mu) = paperTailLength mu + 1 := by
  rw [card_heppLabeledCopy, paperTailLength_add_one]

/-- The actual left-outward/right-outward list on paper positions. -/
def paperFinAnchorOutwardOrderWithPhases {t : PlaneTree}
    {mu : Multiplicities t} (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu)) :
    List (Fin (totalMultiplicity mu)) :=
  (finAnchorPositionScheduleWithPhases
    leftPhase rightPhase anchor).flatMap PositionBlock.entries

@[simp] theorem length_paperFinAnchorOutwardOrderWithPhases
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu)) :
    (paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor).length = paperTailLength mu := by
  simpa [paperFinAnchorOutwardOrderWithPhases, paperTailLength] using
    length_flatten_finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor

theorem nodup_paperFinAnchorOutwardOrderWithPhases
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu)) :
    (paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor).Nodup := by
  exact nodup_flatten_finAnchorPositionScheduleWithPhases
    leftPhase rightPhase anchor

@[simp] theorem mem_paperFinAnchorOutwardOrderWithPhases_iff
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor i : Fin (totalMultiplicity mu)) :
    i ∈ paperFinAnchorOutwardOrderWithPhases
        leftPhase rightPhase anchor ↔
      i ≠ anchor := by
  exact mem_flatten_finAnchorPositionScheduleWithPhases_iff
    leftPhase rightPhase anchor i

/--
Concrete paper-position equivalence: zero is the anchor and the tail is
exactly the schedule used by `finAnchorNXCoarseRunsWithPhases`.
-/
noncomputable def paperFinAnchorOutwardEquivWithPhases
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu)) :
    Fin (paperTailLength mu + 1) ≃
      Fin (totalMultiplicity mu) :=
  anchoredScheduleEquivTo anchor
    (paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor)
    (length_paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor)
    (nodup_paperFinAnchorOutwardOrderWithPhases
      leftPhase rightPhase anchor)
    (mem_paperFinAnchorOutwardOrderWithPhases_iff
      leftPhase rightPhase anchor)
    (by simp)

@[simp] theorem paperFinAnchorOutwardEquivWithPhases_zero
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu)) :
    paperFinAnchorOutwardEquivWithPhases
      leftPhase rightPhase anchor 0 = anchor :=
  rfl

@[simp] theorem paperFinAnchorOutwardEquivWithPhases_succ
    {t : PlaneTree} {mu : Multiplicities t}
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (i : Fin (paperTailLength mu)) :
    paperFinAnchorOutwardEquivWithPhases
      leftPhase rightPhase anchor i.succ =
        scheduleTail
          (paperFinAnchorOutwardOrderWithPhases
            leftPhase rightPhase anchor)
          (length_paperFinAnchorOutwardOrderWithPhases
            leftPhase rightPhase anchor) i :=
  rfl

/-! ## Exposing the anchored head and the outward tail -/

/--
An anchor copy followed by an injective list of all remaining copies.  The
first field is required not to occur in the tail; together with tail
injectivity this is exactly injectivity of `Fin.cons`.
-/
structure AnchoredTailAssignment (β : Type*) (n : ℕ) where
  anchorCopy : β
  outwardCopies : Fin n → β
  anchor_not_range : anchorCopy ∉ Set.range outwardCopies
  outward_injective : Function.Injective outwardCopies

/--
When the codomain has `n+1` elements, arrangements are exactly an anchor
copy followed by an injective tail avoiding that anchor.  This is the
carrier-level finite-Fubini decomposition before class conditions or
weights are imposed.
-/
noncomputable def arrangementEquivAnchoredTail
    {β : Type*} [Fintype β] {n : ℕ}
    (hcard : Fintype.card β = n + 1) :
    (Fin (n + 1) ≃ β) ≃ AnchoredTailAssignment β n where
  toFun σ :=
    { anchorCopy := σ 0
      outwardCopies := fun i => σ i.succ
      anchor_not_range := by
        rintro ⟨i, hi⟩
        have hpos : (i.succ : Fin (n + 1)) = 0 :=
          σ.injective hi
        have := congrArg Fin.val hpos
        simp at this
      outward_injective := by
        intro i j hij
        exact Fin.succ_injective _ (σ.injective hij) }
  invFun p :=
    Equiv.ofBijective
      (Fin.cons p.anchorCopy p.outwardCopies)
      ((Fintype.bijective_iff_injective_and_card
        (Fin.cons p.anchorCopy p.outwardCopies)).2
          ⟨(Fin.cons_injective_iff).2
              ⟨p.anchor_not_range, p.outward_injective⟩,
            by simp [hcard]⟩)
  left_inv σ := by
    apply Equiv.ext
    intro i
    cases i using Fin.cases <;> simp
  right_inv p := by
    cases p
    rfl

/-- Class constraints on an anchored-tail assignment. -/
def ClassifiedAnchoredTailAssignment
    {β α : Type*} {n : ℕ}
    (classify : β → α) (x : Fin (n + 1) → α) :=
  {p : AnchoredTailAssignment β n //
    classify p.anchorCopy = x 0 ∧
      ∀ i : Fin n, classify (p.outwardCopies i) = x i.succ}

/--
Fiberwise version of `arrangementEquivAnchoredTail`: a classified
arrangement is exactly a classified anchor copy and classified outward
tail.  The class condition is pointwise and no counting factor is used.
-/
noncomputable def classifiedArrangementEquivAnchoredTail
    {β α : Type*} [Fintype β] {n : ℕ}
    (hcard : Fintype.card β = n + 1)
    (classify : β → α) (x : Fin (n + 1) → α) :
    {σ : Fin (n + 1) ≃ β // ∀ i, classify (σ i) = x i} ≃
      ClassifiedAnchoredTailAssignment classify x where
  toFun σ :=
    ⟨arrangementEquivAnchoredTail hcard σ.1, by
      constructor
      · exact σ.2 0
      · intro i
        exact σ.2 i.succ⟩
  invFun p :=
    ⟨(arrangementEquivAnchoredTail hcard).symm p.1, by
      intro i
      cases i using Fin.cases with
      | zero =>
          exact p.2.1
      | succ i =>
          exact p.2.2 i⟩
  left_inv σ := by
    apply Subtype.ext
    exact (arrangementEquivAnchoredTail hcard).symm_apply_apply σ.1
  right_inv p := by
    apply Subtype.ext
    exact (arrangementEquivAnchoredTail hcard).apply_symm_apply p.1

/-! ## Exact conditioned tuple sums -/

/-- Values of a prescribed class which are not in the used set. -/
def classifiedAvailableValues
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    (classify : β → α) (used : Finset β) (a : α) : Finset β :=
  Finset.univ.filter (fun b => classify b = a) \ used

@[simp] theorem mem_classifiedAvailableValues_iff
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    (classify : β → α) (used : Finset β) (a : α) (b : β) :
    b ∈ classifiedAvailableValues classify used a ↔
      classify b = a ∧ b ∉ used := by
  simp [classifiedAvailableValues]

/--
A tuple has the prescribed class word, is injective, and avoids all
previously used values.
-/
def ClassTupleAdmissible
    {β α : Type*} {n : ℕ}
    (classify : β → α) (used : Finset β)
    (classes : Fin n → α) (f : Fin n → β) : Prop :=
  (∀ i, classify (f i) = classes i) ∧
    Function.Injective f ∧
      ∀ i, f i ∉ used

/--
At equal finite cardinalities, an admissible full tuple with no previously
used values is exactly a classified arrangement.  This equivalence rules out
the vacuous unequal-cardinality case before the weighted Fubini identity is
specialized to the paper carrier.
-/
noncomputable def classTupleEquivClassifiedArrangement
    {β α : Type*} [Fintype β] [DecidableEq β] {n : ℕ}
    (hcard : Fintype.card β = n + 1)
    (classify : β → α) (classes : Fin (n + 1) → α) :
    {f : Fin (n + 1) → β //
      ClassTupleAdmissible classify ∅ classes f} ≃
      {σ : Fin (n + 1) ≃ β //
        ∀ i, classify (σ i) = classes i} where
  toFun f := by
    have hbij : Function.Bijective f.1 :=
      (Fintype.bijective_iff_injective_and_card f.1).2
        ⟨f.2.2.1, by simp [hcard]⟩
    exact ⟨Equiv.ofBijective f.1 hbij, f.2.1⟩
  invFun σ :=
    ⟨σ.1, σ.2, σ.1.injective, by simp⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv σ := by
    apply Subtype.ext
    exact Equiv.ofBijective_coe

theorem classTupleAdmissible_cons_iff
    {β α : Type*} [DecidableEq β] {n : ℕ}
    (classify : β → α) (used : Finset β)
    (classes : Fin (n + 1) → α)
    (b : β) (tail : Fin n → β) :
    ClassTupleAdmissible classify used classes (Fin.cons b tail) ↔
      classify b = classes 0 ∧ b ∉ used ∧
        ClassTupleAdmissible classify (insert b used)
          (Fin.tail classes) tail := by
  constructor
  · intro h
    refine ⟨h.1 0, h.2.2 0, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change classify (tail i) = classes i.succ
      exact h.1 i.succ
    · exact (Fin.cons_injective_iff.mp h.2.1).2
    · intro i
      simp only [Finset.mem_insert, not_or]
      constructor
      · intro hib
        have heq :
            (i.succ : Fin (n + 1)) = 0 :=
          h.2.1 hib
        have := congrArg Fin.val heq
        simp at this
      · simpa using h.2.2 i.succ
  · rintro ⟨hclass, hused, htail⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero =>
          simpa using hclass
      | succ i =>
          change classify (tail i) = classes i.succ
          exact htail.1 i
    · apply (Fin.cons_injective_iff).2
      constructor
      · rintro ⟨i, hi⟩
        exact (htail.2.2 i) (by simp [hi])
      · exact htail.2.1
    · intro i
      cases i using Fin.cases with
      | zero =>
          simpa using hused
      | succ i =>
          exact fun hi => htail.2.2 i (Finset.mem_insert_of_mem hi)

/--
The exact finite sum over injective classified tuples avoiding `used`.
Writing it as a full Fintype sum with an indicator makes reindexing by
`Fin.consEquiv` transparent.
-/
noncomputable def classifiedTupleSum
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    {n : ℕ} (classify : β → α) (used : Finset β)
    (classes : Fin n → α) (F : (Fin n → β) → ℝ) : ℝ := by
  classical
  exact ∑ f : Fin n → β,
    if ClassTupleAdmissible classify used classes f then F f else 0

@[simp] theorem classifiedTupleSum_zero
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    (classify : β → α) (used : Finset β)
    (classes : Fin 0 → α) (F : (Fin 0 → β) → ℝ) :
    classifiedTupleSum classify used classes F = F Fin.elim0 := by
  classical
  have hadm :
      ClassTupleAdmissible classify used classes
        (Fin.elim0 : Fin 0 → β) := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
  simp [classifiedTupleSum,
    Subsingleton.elim (α := Fin 0 → β) _ Fin.elim0, hadm]

/--
With no used values and matching cardinalities, the full-tuple indicator sum
is the sum over classified arrangements.  This is the exact bridge between
the arrangement fiber and the recursive conditioned tuple sum.
-/
theorem classifiedTupleSum_empty_eq_sum_classifiedArrangements
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    {n : ℕ} (hcard : Fintype.card β = n + 1)
    (classify : β → α) (classes : Fin (n + 1) → α)
    (F : (Fin (n + 1) → β) → ℝ) :
    classifiedTupleSum classify ∅ classes F =
      ∑ σ : {σ : Fin (n + 1) ≃ β //
        ∀ i, classify (σ i) = classes i},
        F σ.1 := by
  classical
  let admissible : Finset (Fin (n + 1) → β) :=
    Finset.univ.filter fun f =>
      ClassTupleAdmissible classify ∅ classes f
  calc
    classifiedTupleSum classify ∅ classes F =
        ∑ f ∈ admissible, F f := by
      simp [classifiedTupleSum, admissible, Finset.sum_filter]
    _ = ∑ f : {f : Fin (n + 1) → β //
          ClassTupleAdmissible classify ∅ classes f}, F f.1 := by
      apply Finset.sum_subtype
      intro f
      simp [admissible]
    _ = ∑ σ : {σ : Fin (n + 1) ≃ β //
          ∀ i, classify (σ i) = classes i},
          F σ.1 := by
      simpa [classTupleEquivClassifiedArrangement] using
        (Equiv.sum_comp
          (classTupleEquivClassifiedArrangement
            hcard classify classes)
          (fun σ : {σ : Fin (n + 1) ≃ β //
            ∀ i, classify (σ i) = classes i} => F σ.1))

/--
One exact finite-Fubini step: expose the head copy in its conditioned class
fiber, insert it into `used`, and continue with the tail.  This is an
identity, not an overcount.
-/
theorem classifiedTupleSum_succ
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    {n : ℕ} (classify : β → α) (used : Finset β)
    (classes : Fin (n + 1) → α)
    (F : (Fin (n + 1) → β) → ℝ) :
    classifiedTupleSum classify used classes F =
      ∑ b ∈ classifiedAvailableValues classify used (classes 0),
        classifiedTupleSum classify (insert b used)
          (Fin.tail classes) (fun tail => F (Fin.cons b tail)) := by
  classical
  unfold classifiedTupleSum
  rw [← Equiv.sum_comp
    (Fin.consEquiv (fun _ : Fin (n + 1) => β))]
  rw [Fintype.sum_prod_type]
  change
    (∑ b : β, ∑ tail : Fin n → β,
      if ClassTupleAdmissible classify used classes
          (Fin.cons b tail) then
        F (Fin.cons b tail)
      else 0) = _
  simp_rw [classTupleAdmissible_cons_iff]
  have hcarrier :
      classifiedAvailableValues classify used (classes 0) =
        Finset.univ.filter fun b =>
          classify b = classes 0 ∧ b ∉ used := by
    ext b
    simp [classifiedAvailableValues]
  rw [hcarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hclass : classify b = classes 0
  · by_cases hused : b ∉ used
    · simp [hclass, hused]
    · simp [hclass, hused]
  · simp [hclass]

theorem classifiedTupleSum_succ_succ
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    {n : ℕ} (classify : β → α) (used : Finset β)
    (classes : Fin (n + 2) → α)
    (F : (Fin (n + 2) → β) → ℝ) :
    classifiedTupleSum classify used classes F =
      ∑ b ∈ classifiedAvailableValues classify used (classes 0),
        ∑ c ∈ classifiedAvailableValues classify (insert b used)
            (classes 1),
          classifiedTupleSum classify (insert c (insert b used))
            (Fin.tail (Fin.tail classes))
            (fun tail => F (Fin.cons b (Fin.cons c tail))) := by
  rw [classifiedTupleSum_succ]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [classifiedTupleSum_succ]
  rfl

/--
Exact head/tail decomposition of a classified arrangement fiber.  The head
is chosen once, the recursive tail avoids it, and no factorial coefficient
or duplicate anchor is introduced.
-/
theorem sum_classifiedArrangements_eq_anchor_classifiedTuple
    {β α : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    {n : ℕ} (hcard : Fintype.card β = n + 1)
    (classify : β → α) (classes : Fin (n + 1) → α)
    (F : (Fin (n + 1) → β) → ℝ) :
    (∑ σ : {σ : Fin (n + 1) ≃ β //
        ∀ i, classify (σ i) = classes i},
        F σ.1) =
      ∑ b ∈ classifiedAvailableValues classify ∅ (classes 0),
        classifiedTupleSum classify {b} (Fin.tail classes)
          (fun tail => F (Fin.cons b tail)) := by
  rw [← classifiedTupleSum_empty_eq_sum_classifiedArrangements
    hcard classify classes F]
  exact classifiedTupleSum_succ classify ∅ classes F

/-- Active `(N,X)` classifier on the actual labeled-copy carrier. -/
def labeledCopyActiveNXClass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    HeppLabeledCopy mu → ActiveNXClass Nm mu :=
  fun c => leafActiveNX Nm mu c.1

/-- The underlying paper `(N,X)` classifier used by the local eliminator. -/
def labeledCopyNXClass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    HeppLabeledCopy mu → NXClass :=
  fun c => singleScaleSigma1 Nm mu c.1

/--
After any position reindexing, a fixed `(N,X)` arrangement fiber is exactly
the corresponding subtype of pointwise-classified arrangements.
-/
noncomputable def arrangementsAtNXWordDomainEquiv
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin n ≃ Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu) :
    {σ : HeppArrangement mu //
      σ ∈ arrangementsAtNXWord Nm mu x} ≃
      {τ : Fin n ≃ HeppLabeledCopy mu //
        ∀ i, labeledCopyNXClass Nm mu (τ i) = (x (e i)).1} where
  toFun σ :=
    ⟨e.trans σ.1, by
      intro i
      have hi := congrFun
        ((mem_arrangementsAtNXWord_iff Nm mu x σ.1).mp σ.2) (e i)
      have hiVal :
          (arrangementNXWord Nm mu σ.1 (e i)).1 =
            (x (e i)).1 :=
        congrArg
          (fun a : ActiveNXClass Nm mu => a.1) hi
      simpa [labeledCopyNXClass, arrangementNXWord,
        inducedWord, leafActiveNX] using hiVal⟩
  invFun τ :=
    ⟨e.symm.trans τ.1,
      (mem_arrangementsAtNXWord_iff Nm mu x _).2 <| by
        funext j
        have hj := τ.2 (e.symm j)
        apply Subtype.ext
        change singleScaleSigma1 Nm mu (τ.1 (e.symm j)).1 =
          (x j).1
        simpa [labeledCopyNXClass] using hj⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp
  right_inv τ := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    simp

/--
Exact weighted head/tail Fubini formula for an actual fixed `(N,X)` word
fiber.  The arbitrary equivalence `e` will be instantiated by the concrete
outward schedule; its zeroth position is the distinguished anchor.
-/
theorem sum_arrangementsAtNXWord_eq_anchor_classifiedTuple
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (e : Fin (paperTailLength mu + 1) ≃
      Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (F : (Fin (totalMultiplicity mu) →
      HeppLabeledCopy mu) → ℝ) :
    (∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ) =
      ∑ b ∈ classifiedAvailableValues
          (labeledCopyNXClass Nm mu) ∅ (x (e 0)).1,
        classifiedTupleSum
          (labeledCopyNXClass Nm mu) {b}
          (fun i : Fin (paperTailLength mu) => (x (e i.succ)).1)
          (fun tail : Fin (paperTailLength mu) →
              HeppLabeledCopy mu =>
            F (fun j =>
              @Fin.cons (paperTailLength mu)
                (fun _ => HeppLabeledCopy mu) b tail (e.symm j))) := by
  classical
  let classes : Fin (paperTailLength mu + 1) →
      NXClass := fun i => (x (e i)).1
  let G : (Fin (paperTailLength mu + 1) →
      HeppLabeledCopy mu) → ℝ :=
    fun f => F (fun j => f (e.symm j))
  calc
    (∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ) =
        ∑ σ : {σ : HeppArrangement mu //
          σ ∈ arrangementsAtNXWord Nm mu x}, F σ.1 :=
      sum_finset_eq_sum_members
        (arrangementsAtNXWord Nm mu x)
        (fun σ : HeppArrangement mu => F σ)
    _ = ∑ τ : {τ :
          Fin (paperTailLength mu + 1) ≃ HeppLabeledCopy mu //
          ∀ i, labeledCopyNXClass Nm mu (τ i) = classes i},
          G τ.1 := by
      simpa [classes, G, arrangementsAtNXWordDomainEquiv] using
        (Equiv.sum_comp
          (arrangementsAtNXWordDomainEquiv Nm mu e x)
          (fun τ : {τ :
            Fin (paperTailLength mu + 1) ≃ HeppLabeledCopy mu //
            ∀ i, labeledCopyNXClass Nm mu (τ i) = (x (e i)).1} =>
              F (fun j => τ.1 (e.symm j))))
    _ = ∑ b ∈ classifiedAvailableValues
          (labeledCopyNXClass Nm mu) ∅ (classes 0),
        classifiedTupleSum
          (labeledCopyNXClass Nm mu) {b}
          (Fin.tail classes)
          (fun tail => G (Fin.cons b tail)) := by
      exact sum_classifiedArrangements_eq_anchor_classifiedTuple
        (card_heppLabeledCopy_eq_paperTailLength_add_one mu)
        (labeledCopyNXClass Nm mu) classes G
    _ = _ := by
      rfl

/-- The generic conditioned carrier is definitionally the project carrier
`conditionedCopiesAtNX` on labeled copies. -/
theorem classifiedAvailableValues_labeledCopyNXClass
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (used : Finset (HeppLabeledCopy mu)) (a : NXClass) :
    classifiedAvailableValues
        (labeledCopyNXClass Nm mu) used a =
      conditionedCopiesAtNX Nm mu used a := by
  rfl

/--
Concrete fixed-fiber Fubini formula in the exact outward order used by the
two shared-state elimination runs.  Its outer carrier is already the
project's conditioned `(N,X)` copy carrier.
-/
theorem
    sum_arrangementsAtNXWord_eq_finAnchorOutward_classifiedTuple
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (totalMultiplicity mu))
    (x : Fin (totalMultiplicity mu) → ActiveNXClass Nm mu)
    (F : (Fin (totalMultiplicity mu) →
      HeppLabeledCopy mu) → ℝ) :
    (∑ σ ∈ arrangementsAtNXWord Nm mu x, F σ) =
      ∑ b ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1,
        classifiedTupleSum
          (labeledCopyNXClass Nm mu) {b}
          (fun i : Fin (paperTailLength mu) =>
            (x ((paperFinAnchorOutwardEquivWithPhases
              leftPhase rightPhase anchor) i.succ)).1)
          (fun tail : Fin (paperTailLength mu) →
              HeppLabeledCopy mu =>
            F (fun j =>
              @Fin.cons (paperTailLength mu)
                (fun _ => HeppLabeledCopy mu) b tail
                ((paperFinAnchorOutwardEquivWithPhases
                  leftPhase rightPhase anchor).symm j))) := by
  simpa [classifiedAvailableValues_labeledCopyNXClass] using
    (sum_arrangementsAtNXWord_eq_anchor_classifiedTuple
      Nm mu
      (paperFinAnchorOutwardEquivWithPhases
        leftPhase rightPhase anchor)
      x F)

end XYCluster

end

end Anderson4D
