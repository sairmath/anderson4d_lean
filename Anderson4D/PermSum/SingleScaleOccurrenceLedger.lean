import Anderson4D.PermSum.SingleScaleCopyGlue
import Anderson4D.PermSum.SingleScaleFactorial
import Anderson4D.PermSum.SingleScaleInnerAssembly
import Anderson4D.PermSum.SingleScaleKernelSchedule

/-!
# The occurrence ledger in the single-scale estimate

This file isolates the phase-independent bookkeeping used immediately after
(5.88).  The statistic `paperNXSkippedOccurrenceCount O x a` is the literal
paper statistic: it counts skipped adjacency indices whose **right endpoint**
has `(N,X)` class `a`.  It therefore depends only on the class word and the
omitted-edge set, not on a summation phase, parity choice, or anchor.

The main results are:

* the pointwise ledger `s_{N,X} ≤ m_{N,X}`;
* the exact global ledger `∑ s_{N,X} = |O|`;
* an exact regrouping of the two occurrence factors in (5.88) by `(N,X)`;
* the resulting factorial bound (5.89);
* an exact count of the labeled-copy choices in an anchor fiber.

The right-endpoint convention here is intentionally distinct from the
orientation-dependent incoming-edge convention used by an outward summation
schedule.  No class-by-class identification of those two conventions is
asserted.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## The literal right-endpoint occurrence statistic -/

/-- Number of positions of an active `(N,X)` word which have underlying
class `a`. -/
def nxWordOccurrenceCount {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {m : ℕ}
    (x : Fin m → ActiveNXClass Nm mu) (a : NXClass) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter fun i => (x i).1 = a).card

/-- Paper's `s_{N,X}` below (5.88): skipped adjacencies classified by the
class of their right endpoint `j+1`. -/
def paperNXSkippedOccurrenceCount {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) (a : NXClass) : ℕ :=
  (O.filter fun j => (x (adjacentSucc j)).1 = a).card

/-- The successor map on adjacency indices is injective. -/
theorem adjacentSucc_injective {m : ℕ} :
    Function.Injective (@adjacentSucc m) := by
  intro i j hij
  apply Subtype.ext
  apply Fin.ext
  simpa [adjacentSucc] using congrArg Fin.val hij

/--
Occurrence count for an arbitrary assignment of each skipped adjacency to
one word position.  The outward elimination will instantiate `q` by the
endpoint farther from the anchor.
-/
def assignedNXSkippedOccurrenceCount
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {m : ℕ}
    (q : AdjacentIndex m → Fin m)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) (a : NXClass) : ℕ :=
  (O.filter fun j => (x (q j)).1 = a).card

/-- An injective edge-to-position assignment cannot charge a class more
often than that class occurs in the full word. -/
theorem assignedNXSkippedOccurrenceCount_le_wordOccurrenceCount
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {m : ℕ}
    (q : AdjacentIndex m → Fin m) (hq : Function.Injective q)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) (a : NXClass) :
    assignedNXSkippedOccurrenceCount q O x a ≤
      nxWordOccurrenceCount x a := by
  let s := O.filter fun j => (x (q j)).1 = a
  let p := (Finset.univ : Finset (Fin m)).filter fun i => (x i).1 = a
  have himage : s.image q ⊆ p := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  calc
    assignedNXSkippedOccurrenceCount q O x a = s.card := rfl
    _ = (s.image q).card :=
      (Finset.card_image_of_injective s hq).symm
    _ ≤ p.card := Finset.card_le_card himage
    _ = nxWordOccurrenceCount x a := rfl

/-- A valid active class word contains `m_{N,X}` occurrences of every
active class. -/
theorem nxWordOccurrenceCount_eq_multiplicityNX
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) :
    nxWordOccurrenceCount x a = multiplicityNX Nm mu a := by
  let aa : ActiveNXClass Nm mu := ⟨a, ha⟩
  have hvalid :
      ((Finset.univ : Finset (Fin m)).filter fun i => x i = aa).card =
        activeNXMultiplicity Nm mu aa :=
    (Finset.mem_filter.mp hx).2 aa
  have hfilter :
      ((Finset.univ : Finset (Fin m)).filter fun i => (x i).1 = a) =
        (Finset.univ.filter fun i => x i = aa) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact Subtype.ext hi
    · intro hi
      exact congrArg Subtype.val hi
  rw [nxWordOccurrenceCount, hfilter, hvalid]
  rfl

/-- Every skipped right-endpoint occurrence is an occurrence of the same
class in the whole word. -/
theorem paperNXSkippedOccurrenceCount_le_wordOccurrenceCount
    {t : PlaneTree} {Nm : HeppMarking t} {mu : Multiplicities t} {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) (a : NXClass) :
    paperNXSkippedOccurrenceCount O x a ≤ nxWordOccurrenceCount x a := by
  let s := O.filter fun j => (x (adjacentSucc j)).1 = a
  let p := (Finset.univ : Finset (Fin m)).filter fun i => (x i).1 = a
  have himage : s.image adjacentSucc ⊆ p := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hclass := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclass⟩
  calc
    paperNXSkippedOccurrenceCount O x a = s.card := rfl
    _ = (s.image adjacentSucc).card :=
      (Finset.card_image_of_injective s adjacentSucc_injective).symm
    _ ≤ p.card := Finset.card_le_card himage
    _ = nxWordOccurrenceCount x a := rfl

/-- The pointwise occurrence ledger used by factorial absorption:
`s_{N,X} ≤ m_{N,X}`. -/
theorem paperNXSkippedOccurrenceCount_le_multiplicityNX
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) :
    paperNXSkippedOccurrenceCount O x a ≤ multiplicityNX Nm mu a := by
  calc
    paperNXSkippedOccurrenceCount O x a ≤ nxWordOccurrenceCount x a :=
      paperNXSkippedOccurrenceCount_le_wordOccurrenceCount O x a
    _ = multiplicityNX Nm mu a :=
      nxWordOccurrenceCount_eq_multiplicityNX Nm mu x hx a ha

/-- The generic assigned occurrence ledger satisfies
`s_{N,X} ≤ m_{N,X}` whenever the edge-to-position assignment is injective. -/
theorem assignedNXSkippedOccurrenceCount_le_multiplicityNX
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (q : AdjacentIndex m → Fin m) (hq : Function.Injective q)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) :
    assignedNXSkippedOccurrenceCount q O x a ≤
      multiplicityNX Nm mu a := by
  calc
    assignedNXSkippedOccurrenceCount q O x a ≤
        nxWordOccurrenceCount x a :=
      assignedNXSkippedOccurrenceCount_le_wordOccurrenceCount
        q hq O x a
    _ = multiplicityNX Nm mu a :=
      nxWordOccurrenceCount_eq_multiplicityNX Nm mu x hx a ha

/-- Exact global occurrence ledger: every omitted adjacency contributes
once, to the class of its right endpoint. -/
theorem sum_paperNXSkippedOccurrenceCount
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) :
    (∑ a ∈ nxCarrier Nm mu, paperNXSkippedOccurrenceCount O x a) =
      O.card := by
  have hmap : ∀ j ∈ O, (x (adjacentSucc j)).1 ∈ nxCarrier Nm mu := by
    intro j _hj
    exact (x (adjacentSucc j)).2
  simpa only [paperNXSkippedOccurrenceCount] using
    (Finset.card_eq_sum_card_fiberwise
      (s := O) (t := nxCarrier Nm mu)
      (f := fun j => (x (adjacentSucc j)).1) hmap).symm

/-- Every skipped edge contributes once for any assigned-position
convention; injectivity is not needed for this total ledger. -/
theorem sum_assignedNXSkippedOccurrenceCount
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (q : AdjacentIndex m → Fin m)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) :
    (∑ a ∈ nxCarrier Nm mu,
      assignedNXSkippedOccurrenceCount q O x a) = O.card := by
  have hmap : ∀ j ∈ O, (x (q j)).1 ∈ nxCarrier Nm mu := by
    intro j _hj
    exact (x (q j)).2
  simpa only [assignedNXSkippedOccurrenceCount] using
    (Finset.card_eq_sum_card_fiberwise
      (s := O) (t := nxCarrier Nm mu)
      (f := fun j => (x (q j)).1) hmap).symm

/-! ## Exact regrouping of the occurrence factors in (5.88) -/

/-- The phase-independent factor `X Y^(1/2)` contributed by one occurrence
of an `(N,X)` class in (5.88). -/
def paper588OccurrenceAtom {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (a : NXClass) : ℝ :=
  (a.2 : ℝ) * Real.sqrt ((singleScaleSigma2 Nm mu a).2 : ℝ)

/-- The factor `(XY)^(-1/2)` contributed when an adjacency is omitted. -/
def paper588SkippedAtom {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (a : NXClass) : ℝ :=
  (Real.sqrt (((a.2 * (singleScaleSigma2 Nm mu a).2 : ℕ) : ℝ)))⁻¹

/-- The two common occurrence products on the left of the per-fiber
factorial comparison following (5.88). -/
def paper588WordOccurrenceFactor {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) : ℝ :=
  (∏ i : Fin m, paper588OccurrenceAtom Nm mu (x i).1) *
    ∏ j ∈ O, paper588SkippedAtom Nm mu (x (adjacentSucc j)).1

/-- Regroup an arbitrary position product by the underlying active
`(N,X)` class. -/
theorem prod_word_eq_prod_pow_occurrenceCount
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (x : Fin m → ActiveNXClass Nm mu) (f : NXClass → ℝ) :
    (∏ i : Fin m, f (x i).1) =
      ∏ a ∈ nxCarrier Nm mu, f a ^ nxWordOccurrenceCount x a := by
  have hmap : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      (x i).1 ∈ nxCarrier Nm mu := by
    intro i _hi
    exact (x i).2
  rw [← Finset.prod_fiberwise_of_maps_to hmap (fun i => f (x i).1)]
  apply Finset.prod_congr rfl
  intro a ha
  rw [nxWordOccurrenceCount]
  calc
    (∏ i ∈ (Finset.univ.filter fun i => (x i).1 = a),
        f (x i).1) =
        ∏ _i ∈ (Finset.univ.filter fun i => (x i).1 = a), f a := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
    _ = f a ^ ((Finset.univ.filter fun i => (x i).1 = a).card) := by
      simp

/-- Regroup an arbitrary skipped-edge product by the right-endpoint class. -/
theorem prod_skippedEdges_eq_prod_pow_skippedOccurrenceCount
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) (f : NXClass → ℝ) :
    (∏ j ∈ O, f (x (adjacentSucc j)).1) =
      ∏ a ∈ nxCarrier Nm mu,
        f a ^ paperNXSkippedOccurrenceCount O x a := by
  have hmap : ∀ j ∈ O, (x (adjacentSucc j)).1 ∈ nxCarrier Nm mu := by
    intro j _hj
    exact (x (adjacentSucc j)).2
  rw [← Finset.prod_fiberwise_of_maps_to hmap
    (fun j => f (x (adjacentSucc j)).1)]
  apply Finset.prod_congr rfl
  intro a ha
  rw [paperNXSkippedOccurrenceCount]
  calc
    (∏ j ∈ (O.filter fun j => (x (adjacentSucc j)).1 = a),
        f (x (adjacentSucc j)).1) =
        ∏ _j ∈ (O.filter fun j => (x (adjacentSucc j)).1 = a), f a := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
    _ =
        f a ^ ((O.filter fun j => (x (adjacentSucc j)).1 = a).card) := by
      simp

/-- Regroup a skipped-edge product for an arbitrary assigned-position
convention. -/
theorem prod_assignedSkippedEdges_eq_prod_pow_occurrenceCount
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (q : AdjacentIndex m → Fin m)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) (f : NXClass → ℝ) :
    (∏ j ∈ O, f (x (q j)).1) =
      ∏ a ∈ nxCarrier Nm mu,
        f a ^ assignedNXSkippedOccurrenceCount q O x a := by
  have hmap : ∀ j ∈ O, (x (q j)).1 ∈ nxCarrier Nm mu := by
    intro j _hj
    exact (x (q j)).2
  rw [← Finset.prod_fiberwise_of_maps_to hmap
    (fun j => f (x (q j)).1)]
  apply Finset.prod_congr rfl
  intro a ha
  rw [assignedNXSkippedOccurrenceCount]
  calc
    (∏ j ∈ (O.filter fun j => (x (q j)).1 = a),
        f (x (q j)).1) =
        ∏ _j ∈ (O.filter fun j => (x (q j)).1 = a), f a := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [(Finset.mem_filter.mp hj).2]
    _ = f a ^ ((O.filter fun j => (x (q j)).1 = a).card) := by
      simp

/-- Occurrence factor with a caller-specified assignment of skipped edges
to word positions. -/
def assigned588WordOccurrenceFactor {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (q : AdjacentIndex m → Fin m)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) : ℝ :=
  (∏ i : Fin m, paper588OccurrenceAtom Nm mu (x i).1) *
    ∏ j ∈ O, paper588SkippedAtom Nm mu (x (q j)).1

/-- Exact `(N,X)` regrouping for an assigned skipped-edge convention. -/
theorem assigned588WordOccurrenceFactor_eq_classProduct
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (q : AdjacentIndex m → Fin m)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu)) :
    assigned588WordOccurrenceFactor Nm mu q O x =
      ∏ a ∈ nxCarrier Nm mu,
        singleScalePrintedFiberFactor
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a)
          (assignedNXSkippedOccurrenceCount q O x a) := by
  rw [assigned588WordOccurrenceFactor,
    prod_word_eq_prod_pow_occurrenceCount
      Nm mu x (paper588OccurrenceAtom Nm mu),
    prod_assignedSkippedEdges_eq_prod_pow_occurrenceCount
      Nm mu q O x (paper588SkippedAtom Nm mu),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  rw [nxWordOccurrenceCount_eq_multiplicityNX Nm mu x hx a ha]
  rfl

/-- Generic factorial absorption for any injective skipped-edge assignment. -/
theorem assigned588WordOccurrenceFactor_le_factorial
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (q : AdjacentIndex m → Fin m) (hq : Function.Injective q)
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (s : ℕ) (hm : totalMultiplicity mu = m) (hs : O.card = s) :
    assigned588WordOccurrenceFactor Nm mu q O x ≤
      (2 * Real.exp 1) ^ m *
        Real.sqrt ((m - s).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
  rw [assigned588WordOccurrenceFactor_eq_classProduct Nm mu q O x hx]
  apply prod_singleScalePrintedFiberFactor_le_of_ledgers
      Nm mu (assignedNXSkippedOccurrenceCount q O x) m s
  · intro a ha
    exact assignedNXSkippedOccurrenceCount_le_multiplicityNX
      Nm mu q hq O x hx a ha
  · exact hm
  · rw [sum_assignedNXSkippedOccurrenceCount Nm mu q O x, hs]

/-- Exact `(N,X)`-fiber regrouping of the occurrence part of (5.88). -/
theorem paper588WordOccurrenceFactor_eq_classProduct
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu)) :
    paper588WordOccurrenceFactor Nm mu O x =
      ∏ a ∈ nxCarrier Nm mu,
        singleScalePrintedFiberFactor
          a.2 (singleScaleSigma2 Nm mu a).2
          (multiplicityNX Nm mu a)
          (paperNXSkippedOccurrenceCount O x a) := by
  rw [paper588WordOccurrenceFactor,
    prod_word_eq_prod_pow_occurrenceCount
      Nm mu x (paper588OccurrenceAtom Nm mu),
    prod_skippedEdges_eq_prod_pow_skippedOccurrenceCount
      Nm mu O x (paper588SkippedAtom Nm mu),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a ha
  rw [nxWordOccurrenceCount_eq_multiplicityNX Nm mu x hx a ha]
  rfl

/-- The phase-independent occurrence/factorial ledger: the literal common
factor in (5.88) is bounded by the factorial expression in (5.89). -/
theorem paper588WordOccurrenceFactor_le_factorial
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t) {m : ℕ}
    (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (s : ℕ) (hm : totalMultiplicity mu = m) (hs : O.card = s) :
    paper588WordOccurrenceFactor Nm mu O x ≤
      (2 * Real.exp 1) ^ m *
        Real.sqrt ((m - s).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
  rw [paper588WordOccurrenceFactor_eq_classProduct Nm mu O x hx]
  apply prod_singleScalePrintedFiberFactor_le_of_ledgers
      Nm mu (paperNXSkippedOccurrenceCount O x) m s
  · intro a ha
    exact paperNXSkippedOccurrenceCount_le_multiplicityNX Nm mu O x hx a ha
  · exact hm
  · rw [sum_paperNXSkippedOccurrenceCount Nm mu O x, hs]

/-! ## The independent anchor-copy counting cost -/

namespace XYCluster

/-! ## The phase-independent outward occurrence ledger -/

/-- Skipped occurrences charged to the unique endpoint farther from the
anchor, exactly as in the outward kernel schedule. -/
def outwardNXSkippedOccurrenceCount
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {m : ℕ}
    (anchor : Fin m) (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) (a : NXClass) : ℕ :=
  assignedNXSkippedOccurrenceCount
    (outwardEdgeTargetPosition anchor) O x a

def outward588WordOccurrenceFactor
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {m : ℕ}
    (anchor : Fin m) (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) : ℝ :=
  assigned588WordOccurrenceFactor Nm mu
    (outwardEdgeTargetPosition anchor) O x

theorem outwardNXSkippedOccurrenceCount_le_multiplicityNX
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {m : ℕ}
    (anchor : Fin m) (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (a : NXClass) (ha : a ∈ nxCarrier Nm mu) :
    outwardNXSkippedOccurrenceCount anchor O x a ≤
      multiplicityNX Nm mu a := by
  exact assignedNXSkippedOccurrenceCount_le_multiplicityNX
    Nm mu (outwardEdgeTargetPosition anchor)
    (outwardEdgeTargetPosition_injective anchor) O x hx a ha

theorem sum_outwardNXSkippedOccurrenceCount
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {m : ℕ}
    (anchor : Fin m) (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu) :
    (∑ a ∈ nxCarrier Nm mu,
      outwardNXSkippedOccurrenceCount anchor O x a) = O.card := by
  exact sum_assignedNXSkippedOccurrenceCount Nm mu
    (outwardEdgeTargetPosition anchor) O x

/--
The occurrence factor actually produced by the anchored outward schedule
obeys the same factorial estimate as the paper's right-endpoint factor.
-/
theorem outward588WordOccurrenceFactor_le_factorial
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) {m : ℕ}
    (anchor : Fin m) (O : Finset (AdjacentIndex m))
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (s : ℕ) (hm : totalMultiplicity mu = m) (hs : O.card = s) :
    outward588WordOccurrenceFactor Nm mu anchor O x ≤
      (2 * Real.exp 1) ^ m *
        Real.sqrt ((m - s).factorial : ℝ) *
        ∏ l : HeppLeaf t,
          Real.sqrt ((leafMultiplicity mu l).factorial : ℝ) := by
  exact assigned588WordOccurrenceFactor_le_factorial
    Nm mu (outwardEdgeTargetPosition anchor)
    (outwardEdgeTargetPosition_injective anchor) O x hx s hm hs

/-- A full `(N,X)` fiber contains exactly `m_{N,X}` labeled copies. -/
theorem card_labeledCopiesAtNX_eq_multiplicityNX
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) :
    (labeledCopiesAtNX Nm mu a).card = multiplicityNX Nm mu a := by
  let z : HeppLeaf t → Fin 4 → ℤ := fun _l _i => 0
  have h :=
    sum_labeledCopiesAtNX_eq_nxCopyWeightedSum
      Nm mu z a (fun _u => (1 : ℝ))
  have hreal :
      ((labeledCopiesAtNX Nm mu a).card : ℝ) =
        (multiplicityNX Nm mu a : ℝ) := by
    simpa [nxCopyWeightedSum, multiplicityNX] using h
  exact_mod_cast hreal

/-- Deleting already exposed copies can only reduce the cardinality of a
fiber, so every conditioned choice set has size at most `m_{N,X}`. -/
theorem card_conditionedCopiesAtNX_le_multiplicityNX
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (used : Finset (HeppLabeledCopy mu)) (a : NXClass) :
    (conditionedCopiesAtNX Nm mu used a).card ≤
      multiplicityNX Nm mu a := by
  calc
    (conditionedCopiesAtNX Nm mu used a).card ≤
        (labeledCopiesAtNX Nm mu a).card :=
      Finset.card_le_card (conditionedCopiesAtNX_subset Nm mu used a)
    _ = multiplicityNX Nm mu a :=
      card_labeledCopiesAtNX_eq_multiplicityNX Nm mu a

/-- With no previously used copies, conditioning leaves the full fiber. -/
@[simp] theorem conditionedCopiesAtNX_empty
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) :
    conditionedCopiesAtNX Nm mu ∅ a = labeledCopiesAtNX Nm mu a := by
  simp [conditionedCopiesAtNX]

/-- Exact count for the independent choice of the copy at an anchor
position. -/
theorem card_anchorCopyChoices_eq_multiplicityNX
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {m : ℕ} (x : Fin m → ActiveNXClass Nm mu) (anchor : Fin m) :
    (conditionedCopiesAtNX Nm mu ∅ (x anchor).1).card =
      multiplicityNX Nm mu (x anchor).1 := by
  rw [conditionedCopiesAtNX_empty,
    card_labeledCopiesAtNX_eq_multiplicityNX]

/-- A uniformly bounded summand over the independent anchor-copy choices
costs at most the exact anchor multiplicity. -/
theorem sum_anchorCopyChoices_le_multiplicity_mul
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {m : ℕ} (x : Fin m → ActiveNXClass Nm mu) (anchor : Fin m)
    (F : HeppLabeledCopy mu → ℝ) (K : ℝ)
    (hF : ∀ c ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1, F c ≤ K) :
    (∑ c ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1, F c) ≤
      (multiplicityNX Nm mu (x anchor).1 : ℝ) * K := by
  calc
    (∑ c ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1, F c) ≤
        ∑ _c ∈ conditionedCopiesAtNX Nm mu ∅ (x anchor).1, K :=
      Finset.sum_le_sum fun c hc => hF c hc
    _ =
        ((conditionedCopiesAtNX Nm mu ∅ (x anchor).1).card : ℝ) * K := by
      simp
    _ = (multiplicityNX Nm mu (x anchor).1 : ℝ) * K := by
      rw [card_anchorCopyChoices_eq_multiplicityNX]

/-- The number of possible anchor copies never exceeds the total number of
labeled copies. -/
theorem card_anchorCopyChoices_le_totalMultiplicity
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    {m : ℕ} (x : Fin m → ActiveNXClass Nm mu) (anchor : Fin m) :
    (conditionedCopiesAtNX Nm mu ∅ (x anchor).1).card ≤
      totalMultiplicity mu := by
  rw [card_anchorCopyChoices_eq_multiplicityNX]
  calc
    multiplicityNX Nm mu (x anchor).1 ≤
        ∑ a ∈ nxCarrier Nm mu, multiplicityNX Nm mu a := by
      exact Finset.single_le_sum
        (fun _a _ha => Nat.zero_le _)
        (x anchor).2
    _ = totalMultiplicity mu := sum_multiplicityNX Nm mu

end XYCluster

end

end Anderson4D
