import Anderson4D.PermSum.SingleScaleOuter
import Anderson4D.Combinatorics.FactorialBounds

/-!
# The simple/compound majority split in the outer single-scale sum

This file formalizes the part of Step 3 of Proposition 5.10 which starts at
paper (5.82).  The classification is made on the *canonical maximal-`X`
fiber* of every active `(N,Y)` class, namely `maxNXAtNY`; it is not made on
the whole `(N,Y)` fiber.

There is a small but essential normalization hidden in the prose following
(5.82).  The simple estimate (5.83) uses `m_l > 2`, although Proposition 5.10
only assumes `m_l ≥ 2`.  We therefore declare every simple leaf of
multiplicity two compound for this local classification.  The tie rule is:

* a tie is assigned to the simple class;
* otherwise the strict majority decides.

The relabeling is harmless only at exponential cost: a relabeled leaf
replaces the simple factor `N^(2(m_l-2)) = 1` by `(2!)^(1/4) ≤ 2`.
The theorem `normalizedMajorityPayoff_le` records this cost explicitly.

The principal results below are:

* `fixedP_majority_partition_le`, the actual fixed-`P` specialization of
  (5.82);
* `simpleMajority_exponent_payoff`, a denominator-free form of (5.83);
* `simpleMajority_multinomial_le_ordered`, the exact (5.84) inequality once
  the simple classes have been enumerated in increasing scale order;
* `compoundMajority_factorial_certificate`, an eighth-power, integral form
  of (5.85), with an explicit exponential loss;
* `fixedP_majority_multinomial_le_originalPayoff`, the complete fixed-`P`
  assembly of (5.82)--(5.86), including disjoint canonical-fiber flattening
  and the multiplicity-two normalization.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## The canonical maximal fiber and the normalized leaf types -/

/--
The paper's set `L_{N,X*}` for an `(N,Y)` class.  It is empty off the active
carrier, which makes the definition total without adding a proof argument to
all later finite sets.
-/
noncomputable def maxFiberAtNY {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (q : NYClass) : Finset (HeppLeaf t) :=
  if hq : q ∈ nyCarrier Nm mu then
    leavesAtNX Nm mu (maxNXAtNY Nm mu q hq)
  else
    ∅

theorem maxFiberAtNY_eq {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    maxFiberAtNY Nm mu q =
      leavesAtNX Nm mu (maxNXAtNY Nm mu q hq) := by
  simp [maxFiberAtNY, hq]

/--
The local normalization needed for the sentence "for such leaves
`m_l > 2`" in the proof of (5.83).
-/
def isNormalizedCompound {t : PlaneTree}
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (l : HeppLeaf t) : Prop :=
  l.1 ∈ compound ∨ leafMultiplicity mu l = 2

instance {t : PlaneTree} (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l : HeppLeaf t) :
    Decidable (isNormalizedCompound mu compound l) := by
  unfold isNormalizedCompound
  infer_instance

def normalizedSimpleMaxFiber {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    Finset (HeppLeaf t) :=
  (maxFiberAtNY Nm mu q).filter fun l =>
    ¬isNormalizedCompound mu compound l

def normalizedCompoundMaxFiber {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    Finset (HeppLeaf t) :=
  (maxFiberAtNY Nm mu q).filter fun l =>
    isNormalizedCompound mu compound l

theorem normalizedFiber_union {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    normalizedSimpleMaxFiber Nm mu compound q ∪
        normalizedCompoundMaxFiber Nm mu compound q =
      maxFiberAtNY Nm mu q := by
  ext l
  by_cases h : isNormalizedCompound mu compound l
  · simp [normalizedSimpleMaxFiber, normalizedCompoundMaxFiber, h]
  · simp [normalizedSimpleMaxFiber, normalizedCompoundMaxFiber, h]

theorem normalizedFiber_disjoint {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    Disjoint (normalizedSimpleMaxFiber Nm mu compound q)
      (normalizedCompoundMaxFiber Nm mu compound q) := by
  exact Finset.disjoint_left.mpr fun l hs hc =>
    (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp hc).2

theorem normalizedFiber_card {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    (normalizedSimpleMaxFiber Nm mu compound q).card +
        (normalizedCompoundMaxFiber Nm mu compound q).card =
      (maxFiberAtNY Nm mu q).card := by
  rw [← Finset.card_union_of_disjoint
    (normalizedFiber_disjoint Nm mu compound q), normalizedFiber_union]

theorem normalizedSimple_multiplicity_gt_two {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass)
    {l : HeppLeaf t} (hl : l ∈ normalizedSimpleMaxFiber Nm mu compound q) :
    2 < leafMultiplicity mu l := by
  have hnot := (Finset.mem_filter.mp hl).2
  have htwo := mu.two_le l.1 l.2
  simp only [isNormalizedCompound, not_or] at hnot
  change 2 ≤ leafMultiplicity mu l at htwo
  omega

/-! ## The actual majority classifier (tie goes to simple) -/

def isSimpleMajorityAtNY {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) : Prop :=
  (normalizedCompoundMaxFiber Nm mu compound q).card ≤
    (normalizedSimpleMaxFiber Nm mu compound q).card

instance {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    Decidable (isSimpleMajorityAtNY Nm mu compound q) := by
  unfold isSimpleMajorityAtNY
  infer_instance

/--
`false` means simple majority and `true` means compound majority.  Thus an
exact tie is deterministically sent to `false`.
-/
def majorityTagAtNY {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) : Bool :=
  if isSimpleMajorityAtNY Nm mu compound q then false else true

def simpleMajorityAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) : Finset NYClass :=
  boolFiber (nyAtP Nm mu P) (majorityTagAtNY Nm mu compound) false

def compoundMajorityAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) : Finset NYClass :=
  boolFiber (nyAtP Nm mu P) (majorityTagAtNY Nm mu compound) true

theorem simpleMajorityAtP_union_compoundMajorityAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    simpleMajorityAtP Nm mu compound P ∪
        compoundMajorityAtP Nm mu compound P =
      nyAtP Nm mu P :=
  boolFiber_union _ _

theorem simpleMajorityAtP_disjoint_compoundMajorityAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Disjoint (simpleMajorityAtP Nm mu compound P)
      (compoundMajorityAtP Nm mu compound P) :=
  boolFiber_disjoint _ _

theorem mem_simpleMajorityAtP_iff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) (q : NYClass) :
    q ∈ simpleMajorityAtP Nm mu compound P ↔
      q ∈ nyAtP Nm mu P ∧ isSimpleMajorityAtNY Nm mu compound q := by
  simp only [simpleMajorityAtP, boolFiber, Finset.mem_filter,
    majorityTagAtNY]
  by_cases h : isSimpleMajorityAtNY Nm mu compound q
  · simp [h]
  · simp [h]

theorem mem_compoundMajorityAtP_iff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) (q : NYClass) :
    q ∈ compoundMajorityAtP Nm mu compound P ↔
      q ∈ nyAtP Nm mu P ∧
        (normalizedSimpleMaxFiber Nm mu compound q).card <
          (normalizedCompoundMaxFiber Nm mu compound q).card := by
  simp only [compoundMajorityAtP, boolFiber, Finset.mem_filter,
    majorityTagAtNY]
  by_cases h : isSimpleMajorityAtNY Nm mu compound q
  · have hnlt :
        ¬(normalizedSimpleMaxFiber Nm mu compound q).card <
          (normalizedCompoundMaxFiber Nm mu compound q).card :=
      Nat.not_lt_of_ge h
    simp [h, hnlt]
  · have hlt :
        (normalizedSimpleMaxFiber Nm mu compound q).card <
          (normalizedCompoundMaxFiber Nm mu compound q).card := by
      exact Nat.lt_of_not_ge h
    simp [h, hlt]

/-! ### The canonical increasing-`N` enumeration at fixed `P` -/

theorem nyClass_N_pos {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    0 < q.1 := by
  obtain ⟨k, hk⟩ := (nyClass_dyadic Nm mu hq).1
  rw [hk]
  positivity

/-- At fixed `P = YN⁴`, the `N` coordinate determines `(N,Y)`. -/
theorem nyAtP_fst_injOn {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ) :
    Set.InjOn Prod.fst (nyAtP Nm mu P : Set NYClass) := by
  intro q hq r hr hN
  have hqActive : q ∈ nyCarrier Nm mu := (Finset.mem_filter.mp hq).1
  have hqP := (Finset.mem_filter.mp hq).2
  have hrP := (Finset.mem_filter.mp hr).2
  apply Prod.ext hN
  have heq :
      q.2 * q.1 ^ 4 = r.2 * q.1 ^ 4 := by
    simpa [singleScaleSigma3, hN] using hqP.trans hrP.symm
  exact Nat.eq_of_mul_eq_mul_right
    (pow_pos (nyClass_N_pos Nm mu hqActive) 4) heq

theorem simpleMajorityAtP_fst_injOn {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Set.InjOn Prod.fst
      (simpleMajorityAtP Nm mu compound P : Set NYClass) := by
  intro q hq r hr hN
  exact nyAtP_fst_injOn Nm mu P
    (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hr).1 hN

/-- A finite set on which `Prod.fst` is injective is equivalent to its image
of first coordinates. -/
noncomputable def fstImageEquiv
    (s : Finset (ℕ × ℕ))
    (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ))) :
    {q // q ∈ s} ≃ {N // N ∈ s.image Prod.fst} :=
  Equiv.ofBijective
    (fun q : {q // q ∈ s} =>
      (⟨q.1.1, Finset.mem_image.mpr ⟨q.1, q.2, rfl⟩⟩ :
        {N // N ∈ s.image Prod.fst}))
    ⟨by
      intro q r h
      apply Subtype.ext
      apply hinj q.2 r.2
      exact congrArg Subtype.val h,
    by
      intro N
      obtain ⟨q, hq, hqN⟩ := Finset.mem_image.mp N.2
      refine ⟨⟨q, hq⟩, ?_⟩
      apply Subtype.ext
      exact hqN⟩

@[simp] theorem fstImageEquiv_apply_val
    (s : Finset (ℕ × ℕ))
    (hinj : Set.InjOn Prod.fst (s : Set (ℕ × ℕ)))
    (q : {q // q ∈ s}) :
    (fstImageEquiv s hinj q).1 = q.1.1 :=
  rfl

/--
The actual increasing-`N` enumeration used in (5.83)--(5.84).  It is obtained
by sorting the image of the first coordinate and transporting back through
`fstImageEquiv`.
-/
noncomputable def simpleMajorityIncreasingEquiv {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Fin (simpleMajorityAtP Nm mu compound P).card ≃
      {q // q ∈ simpleMajorityAtP Nm mu compound P} := by
  let s := simpleMajorityAtP Nm mu compound P
  let hinj : Set.InjOn Prod.fst (s : Set NYClass) :=
    simpleMajorityAtP_fst_injOn Nm mu compound P
  let hcard : (s.image Prod.fst).card = s.card :=
    Finset.card_image_of_injOn hinj
  exact ((s.image Prod.fst).orderIsoOfFin hcard).toEquiv.trans
    (fstImageEquiv s hinj).symm

theorem simpleMajorityIncreasingEquiv_fst_strictMono {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    StrictMono (fun i =>
      (simpleMajorityIncreasingEquiv Nm mu compound P i).1.1) := by
  let s := simpleMajorityAtP Nm mu compound P
  let hinj : Set.InjOn Prod.fst (s : Set NYClass) :=
    simpleMajorityAtP_fst_injOn Nm mu compound P
  let hcard : (s.image Prod.fst).card = s.card :=
    Finset.card_image_of_injOn hinj
  let eN := (s.image Prod.fst).orderIsoOfFin hcard
  let eQ := fstImageEquiv s hinj
  intro i j hij
  have hN : (eN i).1 < (eN j).1 := eN.lt_iff_lt.mpr hij
  have hi :
      (simpleMajorityIncreasingEquiv Nm mu compound P i).1.1 =
        (eN i).1 := by
    have h := eQ.apply_symm_apply (eN i)
    exact congrArg Subtype.val h
  have hj :
      (simpleMajorityIncreasingEquiv Nm mu compound P j).1.1 =
        (eN j).1 := by
    have h := eQ.apply_symm_apply (eN j)
    exact congrArg Subtype.val h
  change
    (simpleMajorityIncreasingEquiv Nm mu compound P i).1.1 <
      (simpleMajorityIncreasingEquiv Nm mu compound P j).1.1
  rw [hi, hj]
  exact hN

/-- A strictly increasing sequence of positive powers of two grows at least
as `2^(i+1)`. -/
theorem pow_two_succ_le_of_strictMono_dyadic
    {r : ℕ} (N : Fin r → ℕ) (hmono : StrictMono N)
    (hdyadic : ∀ i, IsDyadicNat (N i))
    (htwo : ∀ i, 2 ≤ N i) :
    ∀ i, 2 ^ (i.val + 1) ≤ N i := by
  have hexact : ∀ i, N i = 2 ^ Nat.log 2 (N i) := by
    intro i
    obtain ⟨k, hk⟩ := hdyadic i
    rw [hk, Nat.log_pow Nat.one_lt_two]
  have hlogMono :
      StrictMono (fun i : Fin r => Nat.log 2 (N i)) := by
    intro i j hij
    have hN := hmono hij
    by_contra hnot
    have hle :
        Nat.log 2 (N j) ≤ Nat.log 2 (N i) := Nat.le_of_not_gt hnot
    have hpow :
        2 ^ Nat.log 2 (N j) ≤ 2 ^ Nat.log 2 (N i) :=
      Nat.pow_le_pow_right (by omega) hle
    rw [← hexact j, ← hexact i] at hpow
    omega
  intro i
  have hlogLower : i.val + 1 ≤ Nat.log 2 (N i) := by
    cases r with
    | zero => exact Fin.elim0 i
    | succ n =>
        refine Fin.induction
          (motive := fun k : Fin (n + 1) =>
            k.val + 1 ≤ Nat.log 2 (N k))
          ?_ (fun j ih => ?_) i
        · have hp : 0 < Nat.log 2 (N 0) :=
            Nat.log_pos Nat.one_lt_two (htwo 0)
          exact hp
        · have hs := hlogMono (Fin.castSucc_lt_succ (i := j))
          change Nat.log 2 (N j.castSucc) <
            Nat.log 2 (N j.succ) at hs
          change j.val + 1 ≤ Nat.log 2 (N j.castSucc) at ih
          change j.val + 2 ≤ Nat.log 2 (N j.succ)
          omega
  rw [hexact i]
  exact Nat.pow_le_pow_right (by omega) hlogLower

theorem simpleMajorityIncreasingEquiv_scale_lower {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    ∀ i, 2 ^ (i.val + 1) ≤
      (simpleMajorityIncreasingEquiv Nm mu compound P i).1.1 := by
  let e := simpleMajorityIncreasingEquiv Nm mu compound P
  have hmono : StrictMono (fun i => (e i).1.1) :=
    simpleMajorityIncreasingEquiv_fst_strictMono Nm mu compound P
  have hactive : ∀ i, (e i).1 ∈ nyCarrier Nm mu := by
    intro i
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp (e i).2).1).1
  have hdyadic : ∀ i, IsDyadicNat ((e i).1.1) := by
    intro i
    exact (nyClass_dyadic Nm mu (hactive i)).1
  have htwo : ∀ i, 2 ≤ (e i).1.1 := by
    intro i
    have h := two_le_nxClass_scale ht hroot Nm mu
      (maxNXAtNY_active Nm mu (e i).1 (hactive i))
    rwa [maxNXAtNY_fst Nm mu (e i).1 (hactive i)] at h
  exact pow_two_succ_le_of_strictMono_dyadic
    (fun i => (e i).1.1) hmono hdyadic htwo

/-! ## Cardinal majority payoffs on the maximal fiber -/

theorem maxFiberAtNY_card_lower {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu) :
    q.2 ≤ (maxFiberAtNY Nm mu q).card := by
  rw [maxFiberAtNY_eq Nm mu hq]
  have ha := maxNXAtNY_active Nm mu q hq
  have hb := (sigma2_bucket Nm mu ha).1
  have hclass :=
    (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu q hq)).2
  rwa [hclass] at hb

theorem simpleMajority_card_payoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu)
    (hS : isSimpleMajorityAtNY Nm mu compound q) :
    q.2 ≤ 2 * (normalizedSimpleMaxFiber Nm mu compound q).card := by
  have hcard := normalizedFiber_card Nm mu compound q
  have hlower := maxFiberAtNY_card_lower Nm mu hq
  unfold isSimpleMajorityAtNY at hS
  omega

theorem compoundMajority_card_payoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu)
    (hC : ¬isSimpleMajorityAtNY Nm mu compound q) :
    q.2 ≤ 2 * (normalizedCompoundMaxFiber Nm mu compound q).card := by
  have hcard := normalizedFiber_card Nm mu compound q
  have hlower := maxFiberAtNY_card_lower Nm mu hq
  unfold isSimpleMajorityAtNY at hC
  omega

/-! ## Paper (5.82) with the actual classifier -/

/--
Paper (5.82), now specialized to the majority predicate defined from the
canonical `maxNXAtNY` fiber.  The exponent is exactly `m_P`.
-/
theorem fixedP_majority_partition_le {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Nat.multinomial (nyAtP Nm mu P) (multiplicityNY Nm mu) ≤
      2 ^ multiplicityP Nm mu P *
        Nat.multinomial (simpleMajorityAtP Nm mu compound P)
          (multiplicityNY Nm mu) *
        Nat.multinomial (compoundMajorityAtP Nm mu compound P)
          (multiplicityNY Nm mu) := by
  have h := multinomial_bool_partition_le
    (nyAtP Nm mu P) (multiplicityNY Nm mu)
    (majorityTagAtNY Nm mu compound)
  simpa [simpleMajorityAtP, compoundMajorityAtP,
    multiplicityP_eq_fiber_sum] using h

/-! ## The simple payoff: denominator-free (5.83) -/

def simpleScaleExponent {t : PlaneTree}
    (mu : Multiplicities t) (l : HeppLeaf t) : ℕ :=
  2 * (leafMultiplicity mu l - 2)

def simpleMajorityExponent {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) : ℕ :=
  ∑ l ∈ normalizedSimpleMaxFiber Nm mu compound q,
    simpleScaleExponent mu l

theorem mem_maxFiberAtNY_class {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu)
    {l : HeppLeaf t} (hl : l ∈ maxFiberAtNY Nm mu q) :
    singleScaleSigma1 Nm mu l = maxNXAtNY Nm mu q hq := by
  rw [maxFiberAtNY_eq Nm mu hq] at hl
  exact (Finset.mem_filter.mp hl).2

theorem mem_maxFiberAtNY_parent_scale {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu)
    {l : HeppLeaf t} (hl : l ∈ maxFiberAtNY Nm mu q) :
    scaleN Nm (parentV l.1) = q.1 := by
  have hclass := mem_maxFiberAtNY_class Nm mu hq hl
  have hfst := congrArg Prod.fst hclass
  simpa [singleScaleSigma1] using
    hfst.trans (maxNXAtNY_fst Nm mu q hq)

theorem mem_maxFiberAtNY_dyadicFloor {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu)
    {l : HeppLeaf t} (hl : l ∈ maxFiberAtNY Nm mu q) :
    dyadicFloor (leafMultiplicity mu l) = maxXAtNY Nm mu q := by
  have hclass := mem_maxFiberAtNY_class Nm mu hq hl
  have hsnd := congrArg Prod.snd hclass
  simpa [singleScaleSigma1] using
    hsnd.trans (maxNXAtNY_snd Nm mu q hq)

theorem maxX_le_two_mul_simpleScaleExponent {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu) {l : HeppLeaf t}
    (hl : l ∈ normalizedSimpleMaxFiber Nm mu compound q) :
    maxXAtNY Nm mu q ≤ 2 * simpleScaleExponent mu l := by
  have hlfiber : l ∈ maxFiberAtNY Nm mu q :=
    (Finset.mem_filter.mp hl).1
  have hfloor := (sigma1_bucket Nm mu l).1
  have hfloor' :
      dyadicFloor (leafMultiplicity mu l) ≤ leafMultiplicity mu l := by
    simpa [singleScaleSigma1] using hfloor
  rw [mem_maxFiberAtNY_dyadicFloor Nm mu hq hlfiber] at hfloor'
  have hgt := normalizedSimple_multiplicity_gt_two Nm mu compound q hl
  rw [simpleScaleExponent]
  omega

/--
The exponent inequality in (5.83):
`X* Y ≤ 4 ∑_{simple in L_{N,X*}} 2(m_l-2)`.
-/
theorem simpleMajority_exponent_payoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu)
    (hS : isSimpleMajorityAtNY Nm mu compound q) :
    maxXAtNY Nm mu q * q.2 ≤
      4 * simpleMajorityExponent Nm mu compound q := by
  let s := normalizedSimpleMaxFiber Nm mu compound q
  have hpoint : ∀ l ∈ s,
      maxXAtNY Nm mu q ≤ 2 * simpleScaleExponent mu l := by
    intro l hl
    exact maxX_le_two_mul_simpleScaleExponent Nm mu compound hq hl
  have hsum :
      s.card * maxXAtNY Nm mu q ≤
        2 * simpleMajorityExponent Nm mu compound q := by
    calc
      s.card * maxXAtNY Nm mu q =
          ∑ _l ∈ s, maxXAtNY Nm mu q := by simp
      _ ≤ ∑ l ∈ s, 2 * simpleScaleExponent mu l :=
        Finset.sum_le_sum hpoint
      _ = 2 * simpleMajorityExponent Nm mu compound q := by
        rw [simpleMajorityExponent, Finset.mul_sum]
  have hcard := simpleMajority_card_payoff Nm mu compound hq hS
  dsimp [s] at hsum
  nlinarith

def simpleMajorityScaleProduct {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) : ℝ :=
  ∏ l ∈ normalizedSimpleMaxFiber Nm mu compound q,
    (scaleN Nm (parentV l.1) : ℝ) ^ simpleScaleExponent mu l

theorem simpleMajorityScaleProduct_eq {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu) :
    simpleMajorityScaleProduct Nm mu compound q =
      (q.1 : ℝ) ^ simpleMajorityExponent Nm mu compound q := by
  rw [simpleMajorityScaleProduct, simpleMajorityExponent]
  calc
    (∏ l ∈ normalizedSimpleMaxFiber Nm mu compound q,
        (scaleN Nm (parentV l.1) : ℝ) ^ simpleScaleExponent mu l) =
        ∏ l ∈ normalizedSimpleMaxFiber Nm mu compound q,
          (q.1 : ℝ) ^ simpleScaleExponent mu l := by
      apply Finset.prod_congr rfl
      intro l hl
      rw [mem_maxFiberAtNY_parent_scale Nm mu hq
        (Finset.mem_filter.mp hl).1]
    _ = (q.1 : ℝ) ^
        (∑ l ∈ normalizedSimpleMaxFiber Nm mu compound q,
          simpleScaleExponent mu l) :=
      Finset.prod_pow_eq_pow_sum _ _ _

/--
Real-power form of (5.83).  Raising the simple scale product to the fourth
power pays `N^(X*Y)`.
-/
theorem simpleMajority_scale_payoff_fourth {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu)
    (hS : isSimpleMajorityAtNY Nm mu compound q) :
    (q.1 : ℝ) ^ (maxXAtNY Nm mu q * q.2) ≤
      (simpleMajorityScaleProduct Nm mu compound q) ^ 4 := by
  have ha := maxNXAtNY_active Nm mu q hq
  have hN : (1 : ℝ) ≤ q.1 := by
    have htwo := two_le_nxClass_scale ht hroot Nm mu ha
    rw [maxNXAtNY_fst Nm mu q hq] at htwo
    exact_mod_cast (show 1 ≤ q.1 by omega)
  have hexp := simpleMajority_exponent_payoff Nm mu compound hq hS
  rw [simpleMajorityScaleProduct_eq Nm mu compound hq, ← pow_mul]
  exact pow_le_pow_right₀ hN (by omega)

/-! ## Paper (5.84), with an explicit increasing enumeration -/

/--
The exact (5.84) inequality along an explicitly supplied enumeration `e`.
The inequality itself holds for every enumeration; in the paper `e` is then
chosen to enumerate the fixed-`P` classes by increasing `N`.
-/
theorem simpleMajority_multinomial_le_ordered
    (α : ℝ) (hα : 1 < α)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (e : Fin r ≃ ι) (m : ι → ℕ) :
    (Nat.multinomial Finset.univ m : ℝ) ≤
      α ^ (∑ i : Fin r, (i.val + 1) * m (e i)) *
        (α / (α - 1)) ^ (∑ i : ι, m i) := by
  have h50 := multinomial_le_pow_mul_pow α hα
    r (m ∘ e)
  have hmulti :
      Nat.multinomial Finset.univ (m ∘ e) =
        Nat.multinomial Finset.univ m :=
    multinomial_comp_equiv e m
  have hsum :
      (∑ i : Fin r, (m ∘ e) i) =
        ∑ i : ι, m i := by
    simpa [Function.comp_apply] using Equiv.sum_comp e m
  rw [hmulti, hsum] at h50
  simpa [Function.comp_apply] using h50

/--
Fixed-`P` specialization of (5.84).  The carrier is the actual simple
majority class from (5.82), and `e` is the paper's chosen ordering of it.
-/
theorem fixedP_simpleMajority_multinomial_le_ordered
    (α : ℝ) (hα : 1 < α)
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) {r : ℕ}
    (e : Fin r ≃
      {q // q ∈ simpleMajorityAtP Nm mu compound P}) :
    (Nat.multinomial (simpleMajorityAtP Nm mu compound P)
        (multiplicityNY Nm mu) : ℝ) ≤
      α ^ (∑ i : Fin r, (i.val + 1) *
        multiplicityNY Nm mu (e i).1) *
        (α / (α - 1)) ^
          (∑ q ∈ simpleMajorityAtP Nm mu compound P,
            multiplicityNY Nm mu q) := by
  let s := simpleMajorityAtP Nm mu compound P
  let m : {q // q ∈ s} → ℕ := fun q => multiplicityNY Nm mu q.1
  have h84 := simpleMajority_multinomial_le_ordered α hα e m
  have hmulti :
      Nat.multinomial Finset.univ m =
        Nat.multinomial s (multiplicityNY Nm mu) :=
    multinomial_subtype_eq s (multiplicityNY Nm mu)
  have hsum :
      (∑ q : {q // q ∈ s}, m q) =
        ∑ q ∈ s, multiplicityNY Nm mu q := by
    calc
      (∑ q : {q // q ∈ s}, m q) =
          ∑ q ∈ s.attach, multiplicityNY Nm mu q.1 := by
        rw [Finset.attach_eq_univ]
      _ = ∑ q ∈ s, multiplicityNY Nm mu q :=
        Finset.sum_attach s (multiplicityNY Nm mu)
  rw [hmulti, hsum] at h84
  simpa [s, m] using h84

/-- (5.84) instantiated with the canonical increasing-`N` enumeration. -/
theorem fixedP_simpleMajority_multinomial_le_increasing
    (α : ℝ) (hα : 1 < α)
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (Nat.multinomial (simpleMajorityAtP Nm mu compound P)
        (multiplicityNY Nm mu) : ℝ) ≤
      α ^ (∑ i : Fin (simpleMajorityAtP Nm mu compound P).card,
        (i.val + 1) *
          multiplicityNY Nm mu
            (simpleMajorityIncreasingEquiv Nm mu compound P i).1) *
        (α / (α - 1)) ^
          (∑ q ∈ simpleMajorityAtP Nm mu compound P,
            multiplicityNY Nm mu q) := by
  exact fixedP_simpleMajority_multinomial_le_ordered α hα
    Nm mu compound P (simpleMajorityIncreasingEquiv Nm mu compound P)

/-! ### Closing the simple-majority factor with an explicit uniform `α` -/

/--
An explicit choice close enough to one for the absorption after (5.84).
The denominator is deliberately a power of two.
-/
def outerMajorityAlpha : ℝ :=
  65 / 64

theorem one_lt_outerMajorityAlpha :
    1 < outerMajorityAlpha := by
  norm_num [outerMajorityAlpha]

theorem outerMajorityAlpha_div_sub_one :
    outerMajorityAlpha / (outerMajorityAlpha - 1) = 65 := by
  norm_num [outerMajorityAlpha]

theorem outerMajorityAlpha_pow_32_le_two :
    outerMajorityAlpha ^ 32 ≤ 2 := by
  norm_num [outerMajorityAlpha]

/--
Pointwise absorption of the weighted `α` factor in (5.84) by the simple
scale payoff from (5.83).
-/
theorem simpleMajority_weighted_alpha_point_le {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ)
    (i : Fin (simpleMajorityAtP Nm mu compound P).card) :
    outerMajorityAlpha ^
        ((i.val + 1) *
          multiplicityNY Nm mu
            (simpleMajorityIncreasingEquiv Nm mu compound P i).1) ≤
      simpleMajorityScaleProduct Nm mu compound
        (simpleMajorityIncreasingEquiv Nm mu compound P i).1 := by
  let e := simpleMajorityIncreasingEquiv Nm mu compound P
  let q : NYClass := (e i).1
  let I := i.val + 1
  let A := maxXAtNY Nm mu q * q.2
  let m := multiplicityNY Nm mu q
  let S := simpleMajorityScaleProduct Nm mu compound q
  have hmem : q ∈ simpleMajorityAtP Nm mu compound P := (e i).2
  have hqP : q ∈ nyAtP Nm mu P :=
    (mem_simpleMajorityAtP_iff Nm mu compound P q).mp hmem |>.1
  have hq : q ∈ nyCarrier Nm mu := (Finset.mem_filter.mp hqP).1
  have hS : isSimpleMajorityAtNY Nm mu compound q :=
    (mem_simpleMajorityAtP_iff Nm mu compound P q).mp hmem |>.2
  have hm : m ≤ 8 * A := by
    have h := (multiplicityNY_bounds Nm mu hq).2
    simpa [m, A, Nat.mul_assoc] using h
  have hN :
      (2 : ℝ) ^ I ≤ (q.1 : ℝ) := by
    exact_mod_cast
      (simpleMajorityIncreasingEquiv_scale_lower
        ht hroot Nm mu compound P i)
  have hpay : (q.1 : ℝ) ^ A ≤ S ^ 4 := by
    simpa [A, S] using
      simpleMajority_scale_payoff_fourth
        ht hroot Nm mu compound hq hS
  have hα1 : (1 : ℝ) ≤ outerMajorityAlpha :=
    one_lt_outerMajorityAlpha.le
  have hα0 : (0 : ℝ) ≤ outerMajorityAlpha := hα1.trans' zero_le_one
  have hexp : 4 * (I * m) ≤ 32 * (I * A) := by
    nlinarith
  have hfourth :
      (outerMajorityAlpha ^ (I * m)) ^ 4 ≤ S ^ 4 := by
    calc
      (outerMajorityAlpha ^ (I * m)) ^ 4 =
          outerMajorityAlpha ^ (4 * (I * m)) := by
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ outerMajorityAlpha ^ (32 * (I * A)) :=
        pow_le_pow_right₀ hα1 hexp
      _ = (outerMajorityAlpha ^ 32) ^ (I * A) := by
        rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ (I * A) :=
        pow_le_pow_left₀ (pow_nonneg hα0 32)
          outerMajorityAlpha_pow_32_le_two _
      _ = ((2 : ℝ) ^ I) ^ A := by
        rw [← pow_mul]
      _ ≤ (q.1 : ℝ) ^ A :=
        pow_le_pow_left₀ (by positivity) hN A
      _ ≤ S ^ 4 := hpay
  have hleft : 0 ≤ outerMajorityAlpha ^ (I * m) := by positivity
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    rw [simpleMajorityScaleProduct]
    positivity
  have hrooted :
      outerMajorityAlpha ^ (I * m) ≤ S :=
    (pow_le_pow_iff_left₀ hleft hSnonneg (by norm_num : (4 : ℕ) ≠ 0)).mp
      hfourth
  simpa [e, q, I, m, S] using hrooted

set_option maxHeartbeats 800000 in
/--
The completed simple-majority estimate from (5.83)--(5.84).  The remaining
factor is exactly the product of the local normalized simple scale payoffs;
all combinatorial loss is `65` to the total simple mass.
-/
theorem fixedP_simpleMajority_multinomial_le_scaleProduct {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (Nat.multinomial (simpleMajorityAtP Nm mu compound P)
        (multiplicityNY Nm mu) : ℝ) ≤
      65 ^ (∑ q ∈ simpleMajorityAtP Nm mu compound P,
          multiplicityNY Nm mu q) *
        ∏ q ∈ simpleMajorityAtP Nm mu compound P,
          simpleMajorityScaleProduct Nm mu compound q := by
  let s := simpleMajorityAtP Nm mu compound P
  let e := simpleMajorityIncreasingEquiv Nm mu compound P
  have h84 := fixedP_simpleMajority_multinomial_le_increasing
    outerMajorityAlpha one_lt_outerMajorityAlpha Nm mu compound P
  rw [outerMajorityAlpha_div_sub_one] at h84
  have hweighted :
      outerMajorityAlpha ^
          (∑ i : Fin s.card, (i.val + 1) *
            multiplicityNY Nm mu (e i).1) ≤
        ∏ q ∈ s, simpleMajorityScaleProduct Nm mu compound q := by
    calc
      outerMajorityAlpha ^
          (∑ i : Fin s.card, (i.val + 1) *
            multiplicityNY Nm mu (e i).1) =
          ∏ i : Fin s.card,
            outerMajorityAlpha ^ ((i.val + 1) *
              multiplicityNY Nm mu (e i).1) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ i : Fin s.card,
          simpleMajorityScaleProduct Nm mu compound (e i).1 := by
        apply Finset.prod_le_prod
        · intro i hi
          exact pow_nonneg
            (le_of_lt ((by norm_num : (0 : ℝ) < 1).trans
              one_lt_outerMajorityAlpha)) _
        · intro i hi
          exact simpleMajority_weighted_alpha_point_le
            ht hroot Nm mu compound P i
      _ = ∏ q : {q // q ∈ s},
          simpleMajorityScaleProduct Nm mu compound q.1 := by
        simpa [Function.comp_apply] using
          Equiv.prod_comp e
            (fun q : {q // q ∈ s} =>
              simpleMajorityScaleProduct Nm mu compound q.1)
      _ = ∏ q ∈ s,
          simpleMajorityScaleProduct Nm mu compound q := by
        rw [← Finset.attach_eq_univ]
        exact Finset.prod_attach s
          (simpleMajorityScaleProduct Nm mu compound)
  calc
    (Nat.multinomial s (multiplicityNY Nm mu) : ℝ) ≤
        outerMajorityAlpha ^
            (∑ i : Fin s.card, (i.val + 1) *
              multiplicityNY Nm mu (e i).1) *
          65 ^ (∑ q ∈ s, multiplicityNY Nm mu q) := by
      simpa [s, e] using h84
    _ ≤ (∏ q ∈ s, simpleMajorityScaleProduct Nm mu compound q) *
          65 ^ (∑ q ∈ s, multiplicityNY Nm mu q) :=
      mul_le_mul_of_nonneg_right hweighted (pow_nonneg (by norm_num) _)
    _ = 65 ^ (∑ q ∈ s, multiplicityNY Nm mu q) *
          ∏ q ∈ s, simpleMajorityScaleProduct Nm mu compound q := by
      ring

/-! ## The compound carrier grouped by `X*` -/

def compoundXCarrierAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) : Finset ℕ :=
  (compoundMajorityAtP Nm mu compound P).image fun q =>
    maxXAtNY Nm mu q

def compoundAtPX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) : Finset NYClass :=
  (compoundMajorityAtP Nm mu compound P).filter fun q =>
    maxXAtNY Nm mu q = X

def compoundMultiplicityPX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) : ℕ :=
  ∑ q ∈ compoundAtPX Nm mu compound P X, multiplicityNY Nm mu q

def compoundYMassPX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) : ℕ :=
  ∑ q ∈ compoundAtPX Nm mu compound P X, q.2

theorem compoundAtPX_subset_nyAtPX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) :
    compoundAtPX Nm mu compound P X ⊆ nyAtPX Nm mu P X := by
  intro q hq
  rw [compoundAtPX] at hq
  rw [nyAtPX, Finset.mem_filter]
  exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1,
    (Finset.mem_filter.mp hq).2⟩

theorem compoundAtPX_active {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {P X : ℕ} {q : NYClass}
    (hq : q ∈ compoundAtPX Nm mu compound P X) :
    q ∈ nyCarrier Nm mu :=
  nyAtPX_active Nm mu
    (compoundAtPX_subset_nyAtPX Nm mu compound P X hq)

theorem compoundAtPX_maxX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {P X : ℕ} {q : NYClass}
    (hq : q ∈ compoundAtPX Nm mu compound P X) :
    maxXAtNY Nm mu q = X :=
  (Finset.mem_filter.mp hq).2

theorem compoundMajorityAtP_mapsTo_X {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ)
    {q : NYClass} (hq : q ∈ compoundMajorityAtP Nm mu compound P) :
    maxXAtNY Nm mu q ∈ compoundXCarrierAtP Nm mu compound P :=
  Finset.mem_image_of_mem _ hq

theorem compoundMass_eq_sum_PX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (∑ q ∈ compoundMajorityAtP Nm mu compound P,
        multiplicityNY Nm mu q) =
      ∑ X ∈ compoundXCarrierAtP Nm mu compound P,
        compoundMultiplicityPX Nm mu compound P X := by
  symm
  simpa [compoundMultiplicityPX, compoundAtPX] using
    (Finset.sum_fiberwise_of_maps_to
      (s := compoundMajorityAtP Nm mu compound P)
      (t := compoundXCarrierAtP Nm mu compound P)
      (g := fun q => maxXAtNY Nm mu q)
      (fun q hq => compoundMajorityAtP_mapsTo_X
        Nm mu compound P hq)
      (multiplicityNY Nm mu))

theorem compoundMultiplicityPX_bounds {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) :
    X * compoundYMassPX Nm mu compound P X ≤
        compoundMultiplicityPX Nm mu compound P X ∧
      compoundMultiplicityPX Nm mu compound P X ≤
        8 * X * compoundYMassPX Nm mu compound P X := by
  constructor
  · rw [compoundMultiplicityPX, compoundYMassPX, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have hb := (multiplicityNY_bounds Nm mu
      (compoundAtPX_active Nm mu compound hq)).1
    rwa [compoundAtPX_maxX Nm mu compound hq] at hb
  · rw [compoundMultiplicityPX, compoundYMassPX]
    calc
      (∑ q ∈ compoundAtPX Nm mu compound P X,
          multiplicityNY Nm mu q) ≤
          ∑ q ∈ compoundAtPX Nm mu compound P X,
            8 * X * q.2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hb := (multiplicityNY_bounds Nm mu
          (compoundAtPX_active Nm mu compound hq)).2
        rwa [compoundAtPX_maxX Nm mu compound hq] at hb
      _ = 8 * X *
          ∑ q ∈ compoundAtPX Nm mu compound P X, q.2 := by
        rw [Finset.mul_sum]

theorem compoundXCarrier_dyadic {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {P X : ℕ}
    (hX : X ∈ compoundXCarrierAtP Nm mu compound P) :
    IsDyadicNat X := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hX
  have hactive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have ha := maxNXAtNY_active Nm mu q hactive
  rw [← maxNXAtNY_snd Nm mu q hactive]
  exact (nxClass_dyadic Nm mu ha).2

theorem compoundXCarrier_pos {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {P X : ℕ}
    (hX : X ∈ compoundXCarrierAtP Nm mu compound P) :
    0 < X := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hX
  have hactive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one
    (one_le_maxXAtNY Nm mu hactive)

theorem two_le_nxClass_X_of_active {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    2 ≤ a.2 := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
  have hm : 2 ≤ leafMultiplicity mu l := mu.two_le l.1 l.2
  have hlog : 1 ≤ Nat.log 2 (leafMultiplicity mu l) :=
    Nat.log_pos Nat.one_lt_two hm
  simp only [singleScaleSigma1, dyadicFloor]
  calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ Nat.log 2 (leafMultiplicity mu l) :=
      Nat.pow_le_pow_right (by omega) hlog

theorem compoundXCarrier_two_le {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {P X : ℕ}
    (hX : X ∈ compoundXCarrierAtP Nm mu compound P) :
    2 ≤ X := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hX
  have hactive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  rw [← maxNXAtNY_snd Nm mu q hactive]
  exact two_le_nxClass_X_of_active Nm mu
    (maxNXAtNY_active Nm mu q hactive)

/-- Increasing enumeration of the distinct compound `X*` values. -/
noncomputable def compoundXIncreasingEquiv {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Fin (compoundXCarrierAtP Nm mu compound P).card ≃
      {X // X ∈ compoundXCarrierAtP Nm mu compound P} :=
  (compoundXCarrierAtP Nm mu compound P).orderIsoOfFin rfl

theorem compoundXIncreasingEquiv_scale_lower {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    ∀ i, 2 ^ (i.val + 1) ≤
      (compoundXIncreasingEquiv Nm mu compound P i).1 := by
  let s := compoundXCarrierAtP Nm mu compound P
  let e := compoundXIncreasingEquiv Nm mu compound P
  have hmono : StrictMono (fun i => (e i).1) := by
    intro i j hij
    exact ((s.orderIsoOfFin rfl).lt_iff_lt).mpr hij
  have hdyadic : ∀ i, IsDyadicNat ((e i).1) := by
    intro i
    exact compoundXCarrier_dyadic Nm mu compound (e i).2
  have htwo : ∀ i, 2 ≤ (e i).1 := by
    intro i
    exact compoundXCarrier_two_le Nm mu compound (e i).2
  exact pow_two_succ_le_of_strictMono_dyadic
    (fun i => (e i).1) hmono hdyadic htwo

theorem compound_fixedP_multinomial_decomposition {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Nat.multinomial (compoundMajorityAtP Nm mu compound P)
        (multiplicityNY Nm mu) =
      Nat.multinomial (compoundXCarrierAtP Nm mu compound P)
          (compoundMultiplicityPX Nm mu compound P) *
        ∏ X ∈ compoundXCarrierAtP Nm mu compound P,
          Nat.multinomial (compoundAtPX Nm mu compound P X)
            (multiplicityNY Nm mu) := by
  unfold compoundMultiplicityPX compoundAtPX
  exact multinomial_fiberwise
      (compoundMajorityAtP Nm mu compound P)
      (compoundXCarrierAtP Nm mu compound P)
      (fun q => maxXAtNY Nm mu q) (multiplicityNY Nm mu)
      (fun q hq => compoundMajorityAtP_mapsTo_X
        Nm mu compound P hq)

theorem compoundMultiplicityNY_lacunary_fixed_X {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) :
    Lacunary 4 (compoundAtPX Nm mu compound P X)
      (multiplicityNY Nm mu) := by
  intro Z hZ
  have hfull :=
    multiplicityNY_lacunary_fixed_P_X Nm mu P X Z hZ
  apply (Finset.card_le_card ?_).trans hfull
  intro q hq
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨compoundAtPX_subset_nyAtPX Nm mu compound P X hq.1, hq.2⟩

theorem compoundWithinPX_multinomial_product_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)) (P : ℕ),
        ((∏ X ∈ compoundXCarrierAtP Nm mu compound P,
            Nat.multinomial (compoundAtPX Nm mu compound P X)
              (multiplicityNY Nm mu) : ℕ) : ℝ) ≤
          C ^ (∑ q ∈ compoundMajorityAtP Nm mu compound P,
            multiplicityNY Nm mu q) := by
  obtain ⟨C, hC, hbound⟩ :=
    multinomial_le_pow_of_lacunary_finset 4 (by omega)
  refine ⟨C, hC, ?_⟩
  intro t Nm mu compound P
  calc
    ((∏ X ∈ compoundXCarrierAtP Nm mu compound P,
        Nat.multinomial (compoundAtPX Nm mu compound P X)
          (multiplicityNY Nm mu) : ℕ) : ℝ) =
        ∏ X ∈ compoundXCarrierAtP Nm mu compound P,
          (Nat.multinomial (compoundAtPX Nm mu compound P X)
            (multiplicityNY Nm mu) : ℝ) := by push_cast; rfl
    _ ≤ ∏ X ∈ compoundXCarrierAtP Nm mu compound P,
        C ^ compoundMultiplicityPX Nm mu compound P X := by
      apply Finset.prod_le_prod
      · intro X hX
        positivity
      · intro X hX
        simpa [compoundMultiplicityPX] using
          hbound (compoundAtPX Nm mu compound P X)
            (multiplicityNY Nm mu)
            (compoundMultiplicityNY_lacunary_fixed_X
              Nm mu compound P X)
    _ = C ^ (∑ X ∈ compoundXCarrierAtP Nm mu compound P,
        compoundMultiplicityPX Nm mu compound P X) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = C ^ (∑ q ∈ compoundMajorityAtP Nm mu compound P,
        multiplicityNY Nm mu q) := by
      rw [compoundMass_eq_sum_PX]

def compoundOuterAlpha : ℝ :=
  129 / 128

theorem one_lt_compoundOuterAlpha :
    1 < compoundOuterAlpha := by
  norm_num [compoundOuterAlpha]

theorem compoundOuterAlpha_div_sub_one :
    compoundOuterAlpha / (compoundOuterAlpha - 1) = 129 := by
  norm_num [compoundOuterAlpha]

theorem compoundOuterAlpha_pow_64_le_two :
    compoundOuterAlpha ^ 64 ≤ 2 := by
  norm_num [compoundOuterAlpha]

def compoundBlockPayoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) : ℝ :=
  (X : ℝ) ^
    (((X * compoundYMassPX Nm mu compound P X : ℕ) : ℝ) / 8)

theorem compoundBlockPayoff_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P X : ℕ) :
    0 ≤ compoundBlockPayoff Nm mu compound P X :=
  Real.rpow_nonneg (by positivity) _

set_option maxHeartbeats 1000000 in
/-- Pointwise absorption used in the last application of (5.50) in (5.86). -/
theorem compoundOuter_weighted_alpha_point_le {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ)
    (i : Fin (compoundXCarrierAtP Nm mu compound P).card) :
    compoundOuterAlpha ^
        ((i.val + 1) *
          compoundMultiplicityPX Nm mu compound P
            (compoundXIncreasingEquiv Nm mu compound P i).1) ≤
      compoundBlockPayoff Nm mu compound P
        (compoundXIncreasingEquiv Nm mu compound P i).1 := by
  let e := compoundXIncreasingEquiv Nm mu compound P
  let X := (e i).1
  let I := i.val + 1
  let A := X * compoundYMassPX Nm mu compound P X
  let mass := compoundMultiplicityPX Nm mu compound P X
  let L := compoundOuterAlpha ^ (I * mass)
  let Q := compoundBlockPayoff Nm mu compound P X
  have hmass : mass ≤ 8 * A := by
    simpa [mass, A, Nat.mul_assoc] using
      (compoundMultiplicityPX_bounds Nm mu compound P X).2
  have hX :
      (2 : ℝ) ^ I ≤ (X : ℝ) := by
    exact_mod_cast
      (compoundXIncreasingEquiv_scale_lower Nm mu compound P i)
  have hα1 : (1 : ℝ) ≤ compoundOuterAlpha :=
    one_lt_compoundOuterAlpha.le
  have hα0 : (0 : ℝ) ≤ compoundOuterAlpha :=
    (zero_le_one.trans hα1)
  have hexp : 8 * (I * mass) ≤ 64 * (I * A) := by
    nlinarith
  have hQ8 : Q ^ (8 : ℕ) = (X : ℝ) ^ A := by
    dsimp only [Q]
    rw [compoundBlockPayoff]
    change (((X : ℝ) ^ ((A : ℝ) / 8)) ^ (8 : ℕ)) =
      (X : ℝ) ^ A
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hL8 : L ^ (8 : ℕ) ≤ Q ^ (8 : ℕ) := by
    rw [hQ8]
    calc
      L ^ (8 : ℕ) =
          compoundOuterAlpha ^ (8 * (I * mass)) := by
        dsimp only [L]
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ compoundOuterAlpha ^ (64 * (I * A)) :=
        pow_le_pow_right₀ hα1 hexp
      _ = (compoundOuterAlpha ^ 64) ^ (I * A) := by
        rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ (I * A) :=
        pow_le_pow_left₀ (pow_nonneg hα0 64)
          compoundOuterAlpha_pow_64_le_two _
      _ = ((2 : ℝ) ^ I) ^ A := by
        rw [← pow_mul]
      _ ≤ (X : ℝ) ^ A :=
        pow_le_pow_left₀ (by positivity) hX A
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact compoundBlockPayoff_nonneg Nm mu compound P X
  have hroot : L ≤ Q :=
    (pow_le_pow_iff_left₀ hL0 hQ0 (by norm_num : (8 : ℕ) ≠ 0)).mp hL8
  simpa [e, X, I, mass, L, Q] using hroot

set_option maxHeartbeats 600000 in
/-- The block-mass multinomial in (5.86), with an explicit constant `129`. -/
theorem compoundBlock_multinomial_le_payoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (Nat.multinomial (compoundXCarrierAtP Nm mu compound P)
        (compoundMultiplicityPX Nm mu compound P) : ℝ) ≤
      129 ^ (∑ X ∈ compoundXCarrierAtP Nm mu compound P,
          compoundMultiplicityPX Nm mu compound P X) *
        ∏ X ∈ compoundXCarrierAtP Nm mu compound P,
          compoundBlockPayoff Nm mu compound P X := by
  let s := compoundXCarrierAtP Nm mu compound P
  let e := compoundXIncreasingEquiv Nm mu compound P
  let mass : {X // X ∈ s} → ℕ :=
    fun X => compoundMultiplicityPX Nm mu compound P X.1
  have h50 := simpleMajority_multinomial_le_ordered
    compoundOuterAlpha one_lt_compoundOuterAlpha e mass
  have hmulti :
      Nat.multinomial Finset.univ mass =
        Nat.multinomial s (compoundMultiplicityPX Nm mu compound P) :=
    multinomial_subtype_eq s (compoundMultiplicityPX Nm mu compound P)
  have hsum :
      (∑ X : {X // X ∈ s}, mass X) =
        ∑ X ∈ s, compoundMultiplicityPX Nm mu compound P X := by
    calc
      (∑ X : {X // X ∈ s}, mass X) =
          ∑ X ∈ s.attach, compoundMultiplicityPX Nm mu compound P X.1 := by
        rw [Finset.attach_eq_univ]
      _ = ∑ X ∈ s, compoundMultiplicityPX Nm mu compound P X :=
        Finset.sum_attach s (compoundMultiplicityPX Nm mu compound P)
  rw [hmulti, hsum, compoundOuterAlpha_div_sub_one] at h50
  have hweighted :
      compoundOuterAlpha ^
          (∑ i : Fin s.card, (i.val + 1) *
            compoundMultiplicityPX Nm mu compound P (e i).1) ≤
        ∏ X ∈ s, compoundBlockPayoff Nm mu compound P X := by
    calc
      compoundOuterAlpha ^
          (∑ i : Fin s.card, (i.val + 1) *
            compoundMultiplicityPX Nm mu compound P (e i).1) =
          ∏ i : Fin s.card,
            compoundOuterAlpha ^ ((i.val + 1) *
              compoundMultiplicityPX Nm mu compound P (e i).1) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ i : Fin s.card,
          compoundBlockPayoff Nm mu compound P (e i).1 := by
        apply Finset.prod_le_prod
        · intro i hi
          exact pow_nonneg
            (le_of_lt ((by norm_num : (0 : ℝ) < 1).trans
              one_lt_compoundOuterAlpha)) _
        · intro i hi
          exact compoundOuter_weighted_alpha_point_le
            Nm mu compound P i
      _ = ∏ X : {X // X ∈ s},
          compoundBlockPayoff Nm mu compound P X.1 := by
        simpa [Function.comp_apply] using
          Equiv.prod_comp e
            (fun X : {X // X ∈ s} =>
              compoundBlockPayoff Nm mu compound P X.1)
      _ = ∏ X ∈ s, compoundBlockPayoff Nm mu compound P X := by
        rw [← Finset.attach_eq_univ]
        exact Finset.prod_attach s (compoundBlockPayoff Nm mu compound P)
  calc
    (Nat.multinomial s (compoundMultiplicityPX Nm mu compound P) : ℝ) ≤
        compoundOuterAlpha ^
            (∑ i : Fin s.card, (i.val + 1) *
              compoundMultiplicityPX Nm mu compound P (e i).1) *
          129 ^ (∑ X ∈ s,
            compoundMultiplicityPX Nm mu compound P X) := by
      simpa [s, e, mass] using h50
    _ ≤ (∏ X ∈ s, compoundBlockPayoff Nm mu compound P X) *
          129 ^ (∑ X ∈ s,
            compoundMultiplicityPX Nm mu compound P X) :=
      mul_le_mul_of_nonneg_right hweighted (pow_nonneg (by norm_num) _)
    _ = 129 ^ (∑ X ∈ s,
          compoundMultiplicityPX Nm mu compound P X) *
        ∏ X ∈ s, compoundBlockPayoff Nm mu compound P X := by
      ring

/-!
After the lacunary within-block factors, (5.86) is now reduced to the explicit
block payoff.  The next theorem packages both parts.
-/
set_option maxHeartbeats 600000 in
theorem compoundMajority_multinomial_le_blockPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)) (P : ℕ),
        (Nat.multinomial (compoundMajorityAtP Nm mu compound P)
          (multiplicityNY Nm mu) : ℝ) ≤
          C ^ (∑ q ∈ compoundMajorityAtP Nm mu compound P,
            multiplicityNY Nm mu q) *
            ∏ X ∈ compoundXCarrierAtP Nm mu compound P,
              compoundBlockPayoff Nm mu compound P X := by
  obtain ⟨C₁, hC₁, hinner⟩ := compoundWithinPX_multinomial_product_le
  let C := 129 * C₁
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro t Nm mu compound P
  let M := ∑ q ∈ compoundMajorityAtP Nm mu compound P,
    multiplicityNY Nm mu q
  let B := ∏ X ∈ compoundXCarrierAtP Nm mu compound P,
    compoundBlockPayoff Nm mu compound P X
  have houter := compoundBlock_multinomial_le_payoff Nm mu compound P
  have hinner' := hinner Nm mu compound P
  rw [← compoundMass_eq_sum_PX] at houter
  change
    (Nat.multinomial (compoundXCarrierAtP Nm mu compound P)
        (compoundMultiplicityPX Nm mu compound P) : ℝ) ≤
      129 ^ M * B at houter
  push_cast at hinner'
  change
    (∏ X ∈ compoundXCarrierAtP Nm mu compound P,
      (Nat.multinomial (compoundAtPX Nm mu compound P X)
        (multiplicityNY Nm mu) : ℝ)) ≤ C₁ ^ M at hinner'
  rw [compound_fixedP_multinomial_decomposition]
  push_cast
  calc
    (Nat.multinomial (compoundXCarrierAtP Nm mu compound P)
          (compoundMultiplicityPX Nm mu compound P) : ℝ) *
        (∏ X ∈ compoundXCarrierAtP Nm mu compound P,
          (Nat.multinomial (compoundAtPX Nm mu compound P X)
            (multiplicityNY Nm mu) : ℝ)) ≤
        (129 ^ M * B) * C₁ ^ M :=
      mul_le_mul houter hinner'
        (by
          apply Finset.prod_nonneg
          intro X hX
          positivity)
        (by
          dsimp [B]
          apply mul_nonneg (by positivity)
          apply Finset.prod_nonneg
          intro X hX
          exact compoundBlockPayoff_nonneg Nm mu compound P X)
    _ = C ^ M * B := by
      dsimp [C]
      rw [mul_pow]
      ring

/-! ## The compound payoff: (5.85) and (5.86) -/

def compoundMajorityMass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) : ℕ :=
  ∑ l ∈ normalizedCompoundMaxFiber Nm mu compound q,
    leafMultiplicity mu l

def compoundMajorityFactorialProduct {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) : ℕ :=
  ∏ l ∈ normalizedCompoundMaxFiber Nm mu compound q,
    (leafMultiplicity mu l).factorial

theorem maxX_le_leafMultiplicity_of_mem_maxFiber {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu)
    {l : HeppLeaf t} (hl : l ∈ maxFiberAtNY Nm mu q) :
    maxXAtNY Nm mu q ≤ leafMultiplicity mu l := by
  have h := (sigma1_bucket Nm mu l).1
  have h' :
      dyadicFloor (leafMultiplicity mu l) ≤ leafMultiplicity mu l := by
    simpa [singleScaleSigma1] using h
  rwa [mem_maxFiberAtNY_dyadicFloor Nm mu hq hl] at h'

theorem compoundMajorityMass_le_multiplicityNY {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu) :
    compoundMajorityMass Nm mu compound q ≤ multiplicityNY Nm mu q := by
  let a := maxNXAtNY Nm mu q hq
  have hsubset :
      normalizedCompoundMaxFiber Nm mu compound q ⊆
        leavesAtNX Nm mu a := by
    intro l hl
    have hbase := (Finset.mem_filter.mp hl).1
    simpa [a, maxFiberAtNY_eq Nm mu hq] using hbase
  calc
    compoundMajorityMass Nm mu compound q =
        ∑ l ∈ normalizedCompoundMaxFiber Nm mu compound q,
          leafMultiplicity mu l := rfl
    _ ≤ ∑ l ∈ leavesAtNX Nm mu a, leafMultiplicity mu l :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ => Nat.zero_le _)
    _ = multiplicityNX Nm mu a := rfl
    _ ≤ ∑ b ∈ nxAtNY Nm mu q, multiplicityNX Nm mu b := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (maxNXAtNY_mem Nm mu q hq)
    _ = multiplicityNY Nm mu q := rfl

theorem compound_point_factorial_payoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu) {l : HeppLeaf t}
    (hl : l ∈ normalizedCompoundMaxFiber Nm mu compound q) :
    maxXAtNY Nm mu q ^ maxXAtNY Nm mu q ≤
      4 ^ leafMultiplicity mu l * (leafMultiplicity mu l).factorial := by
  have hX := maxX_le_leafMultiplicity_of_mem_maxFiber Nm mu hq
    (Finset.mem_filter.mp hl).1
  calc
    maxXAtNY Nm mu q ^ maxXAtNY Nm mu q ≤
        4 ^ maxXAtNY Nm mu q *
          (maxXAtNY Nm mu q).factorial :=
      pow_self_le_four_pow_mul_factorial _
    _ ≤ 4 ^ leafMultiplicity mu l *
          (leafMultiplicity mu l).factorial := by
      exact Nat.mul_le_mul
        (Nat.pow_le_pow_right (by omega) hX)
        (Nat.factorial_le hX)

theorem compound_product_factorial_payoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu) :
    maxXAtNY Nm mu q ^
        (maxXAtNY Nm mu q *
          (normalizedCompoundMaxFiber Nm mu compound q).card) ≤
      4 ^ compoundMajorityMass Nm mu compound q *
        compoundMajorityFactorialProduct Nm mu compound q := by
  let s := normalizedCompoundMaxFiber Nm mu compound q
  calc
    maxXAtNY Nm mu q ^
        (maxXAtNY Nm mu q * s.card) =
        ∏ _l ∈ s,
          (maxXAtNY Nm mu q ^ maxXAtNY Nm mu q) := by
      rw [Finset.prod_const, pow_mul]
    _ ≤ ∏ l ∈ s,
        (4 ^ leafMultiplicity mu l *
          (leafMultiplicity mu l).factorial) := by
      apply Finset.prod_le_prod
      · intro l hl
        exact Nat.zero_le _
      · intro l hl
        exact compound_point_factorial_payoff Nm mu compound hq hl
    _ = 4 ^ compoundMajorityMass Nm mu compound q *
        compoundMajorityFactorialProduct Nm mu compound q := by
      rw [compoundMajorityMass, compoundMajorityFactorialProduct,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/--
An eighth-power, denominator-free form of paper (5.85):

`X^(X Y) ≤ 16^m_{N,Y} (∏_{compound in L_{N,X*}} m_l!)²`.

Taking eighth roots gives the printed quarter-factorial payoff, with an
exponential loss.  Keeping the statement integral avoids hiding positivity or
rounding obligations in `Real.rpow`.
-/
theorem compoundMajority_factorial_certificate {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu)
    (hC : ¬isSimpleMajorityAtNY Nm mu compound q) :
    maxXAtNY Nm mu q ^ (maxXAtNY Nm mu q * q.2) ≤
      16 ^ multiplicityNY Nm mu q *
        (compoundMajorityFactorialProduct Nm mu compound q) ^ 2 := by
  let X := maxXAtNY Nm mu q
  let c := (normalizedCompoundMaxFiber Nm mu compound q).card
  let mass := compoundMajorityMass Nm mu compound q
  let F := compoundMajorityFactorialProduct Nm mu compound q
  have hX : 1 ≤ X := one_le_maxXAtNY Nm mu hq
  have hcard : q.2 ≤ 2 * c := by
    exact compoundMajority_card_payoff Nm mu compound hq hC
  have hprod : X ^ (X * c) ≤ 4 ^ mass * F := by
    exact compound_product_factorial_payoff Nm mu compound hq
  have hexp : X * q.2 ≤ 2 * (X * c) := by
    calc
      X * q.2 ≤ X * (2 * c) := Nat.mul_le_mul_left X hcard
      _ = 2 * (X * c) := by ring
  have hpow : X ^ (X * q.2) ≤ (X ^ (X * c)) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hX (by omega)
  have hsquare :
      (X ^ (X * c)) ^ 2 ≤ (4 ^ mass * F) ^ 2 :=
    Nat.pow_le_pow_left hprod 2
  have hmass : mass ≤ multiplicityNY Nm mu q :=
    compoundMajorityMass_le_multiplicityNY Nm mu compound hq
  calc
    X ^ (X * q.2) ≤ (X ^ (X * c)) ^ 2 := hpow
    _ ≤ (4 ^ mass * F) ^ 2 := hsquare
    _ = 16 ^ mass * F ^ 2 := by
      rw [mul_pow, ← pow_mul]
      congr 1
      calc
        4 ^ (mass * 2) = (4 ^ 2) ^ mass := by
          rw [← pow_mul]
          congr 1
          omega
        _ = 16 ^ mass := by norm_num
    _ ≤ 16 ^ multiplicityNY Nm mu q * F ^ 2 := by
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) hmass)

def compoundMajorityQuarterProduct {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) : ℝ :=
  ∏ l ∈ normalizedCompoundMaxFiber Nm mu compound q,
    ((leafMultiplicity mu l).factorial : ℝ) ^ (1 / 4 : ℝ)

/-- Explicit exponential loss used when taking the eighth root of the
integral (5.85) certificate. -/
def compoundMajorityRootLoss (m : ℕ) : ℝ :=
  ((16 : ℝ) ^ m) ^ (1 / 8 : ℝ)

theorem quarterFactorial_pow_eight (k : ℕ) :
    (((k.factorial : ℝ) ^ (1 / 4 : ℝ)) ^ (8 : ℕ)) =
      (k.factorial : ℝ) ^ (2 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem compoundMajorityQuarterProduct_pow_eight {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    (compoundMajorityQuarterProduct Nm mu compound q) ^ (8 : ℕ) =
      (compoundMajorityFactorialProduct Nm mu compound q : ℝ) ^ 2 := by
  rw [compoundMajorityQuarterProduct, ← Finset.prod_pow]
  calc
    (∏ l ∈ normalizedCompoundMaxFiber Nm mu compound q,
        (((leafMultiplicity mu l).factorial : ℝ) ^
          (1 / 4 : ℝ)) ^ (8 : ℕ)) =
        ∏ l ∈ normalizedCompoundMaxFiber Nm mu compound q,
          ((leafMultiplicity mu l).factorial : ℝ) ^ (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro l hl
      exact quarterFactorial_pow_eight (leafMultiplicity mu l)
    _ = (∏ l ∈ normalizedCompoundMaxFiber Nm mu compound q,
          ((leafMultiplicity mu l).factorial : ℝ)) ^ (2 : ℕ) := by
      rw [Finset.prod_pow]
    _ = (compoundMajorityFactorialProduct Nm mu compound q : ℝ) ^ 2 := by
      rw [compoundMajorityFactorialProduct]
      push_cast
      rfl

theorem compoundMajorityRootLoss_pow_eight (m : ℕ) :
    (compoundMajorityRootLoss m) ^ (8 : ℕ) = (16 : ℝ) ^ m := by
  rw [compoundMajorityRootLoss, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

theorem compoundMajorityRootLoss_nonneg (m : ℕ) :
    0 ≤ compoundMajorityRootLoss m :=
  Real.rpow_nonneg (by positivity) _

theorem compoundMajorityQuarterProduct_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (q : NYClass) :
    0 ≤ compoundMajorityQuarterProduct Nm mu compound q := by
  rw [compoundMajorityQuarterProduct]
  positivity

/--
The printed quarter-power form of (5.85), with an explicit exponential
loss.  This discharges the real-root/positivity boundary of the integral
certificate above.
-/
theorem compoundMajority_quarter_payoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) {q : NYClass}
    (hq : q ∈ nyCarrier Nm mu)
    (hC : ¬isSimpleMajorityAtNY Nm mu compound q) :
    (maxXAtNY Nm mu q : ℝ) ^
        (((maxXAtNY Nm mu q * q.2 : ℕ) : ℝ) / 8) ≤
      compoundMajorityRootLoss (multiplicityNY Nm mu q) *
        compoundMajorityQuarterProduct Nm mu compound q := by
  let X := maxXAtNY Nm mu q
  let A := X * q.2
  let m := multiplicityNY Nm mu q
  let F := compoundMajorityFactorialProduct Nm mu compound q
  let Q := compoundMajorityQuarterProduct Nm mu compound q
  let L := (X : ℝ) ^ ((A : ℝ) / 8)
  let E := compoundMajorityRootLoss m
  have hcertNat := compoundMajority_factorial_certificate
    Nm mu compound hq hC
  have hcert :
      (X : ℝ) ^ A ≤ (16 : ℝ) ^ m * (F : ℝ) ^ 2 := by
    exact_mod_cast hcertNat
  have hL8 : L ^ (8 : ℕ) = (X : ℝ) ^ A := by
    dsimp [L]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hR8 :
      (E * Q) ^ (8 : ℕ) = (16 : ℝ) ^ m * (F : ℝ) ^ 2 := by
    rw [mul_pow, show E ^ (8 : ℕ) = (16 : ℝ) ^ m by
      simpa [E] using compoundMajorityRootLoss_pow_eight m,
      show Q ^ (8 : ℕ) = (F : ℝ) ^ 2 by
        simpa [Q, F] using
          compoundMajorityQuarterProduct_pow_eight Nm mu compound q]
  have hpow : L ^ (8 : ℕ) ≤ (E * Q) ^ (8 : ℕ) := by
    rw [hL8, hR8]
    exact hcert
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg (by positivity) _
  have hR0 : 0 ≤ E * Q :=
    mul_nonneg (by simpa [E] using compoundMajorityRootLoss_nonneg m)
      (by simpa [Q] using
        compoundMajorityQuarterProduct_nonneg Nm mu compound q)
  have hroot :
      L ≤ E * Q :=
    (pow_le_pow_iff_left₀ hL0 hR0 (by norm_num : (8 : ℕ) ≠ 0)).mp hpow
  simpa [X, A, m, Q, L, E] using hroot

theorem compoundMajorityRootLoss_le_two_pow (m : ℕ) :
    compoundMajorityRootLoss m ≤ (2 : ℝ) ^ m := by
  have hE0 := compoundMajorityRootLoss_nonneg m
  have h20 : 0 ≤ (2 : ℝ) ^ m := by positivity
  apply (pow_le_pow_iff_left₀ hE0 h20 (by norm_num : (8 : ℕ) ≠ 0)).mp
  rw [compoundMajorityRootLoss_pow_eight, ← pow_mul]
  calc
    (16 : ℝ) ^ m ≤ (256 : ℝ) ^ m :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) m
    _ = (2 : ℝ) ^ (m * 8) := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, ← pow_mul]
      congr 1
      omega

def compoundClassScalePayoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (q : NYClass) : ℝ :=
  (maxXAtNY Nm mu q : ℝ) ^
    (((maxXAtNY Nm mu q * q.2 : ℕ) : ℝ) / 8)

theorem compoundBlockPayoff_eq_class_product {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ)
    {X : ℕ} (hX : X ∈ compoundXCarrierAtP Nm mu compound P) :
    compoundBlockPayoff Nm mu compound P X =
      ∏ q ∈ compoundAtPX Nm mu compound P X,
        compoundClassScalePayoff Nm mu q := by
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast compoundXCarrier_pos Nm mu compound hX
  rw [compoundBlockPayoff, compoundYMassPX]
  calc
    (X : ℝ) ^
        (((X * ∑ q ∈ compoundAtPX Nm mu compound P X, q.2 : ℕ) : ℝ) / 8) =
        (X : ℝ) ^
          (∑ q ∈ compoundAtPX Nm mu compound P X,
            (((X * q.2 : ℕ) : ℝ) / 8)) := by
      congr 1
      push_cast
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = ∏ q ∈ compoundAtPX Nm mu compound P X,
          (X : ℝ) ^ (((X * q.2 : ℕ) : ℝ) / 8) :=
      Real.rpow_sum_of_pos hXpos
        (fun q : NYClass => (((X * q.2 : ℕ) : ℝ) / 8))
        (compoundAtPX Nm mu compound P X)
    _ = ∏ q ∈ compoundAtPX Nm mu compound P X,
        compoundClassScalePayoff Nm mu q := by
      apply Finset.prod_congr rfl
      intro q hq
      rw [compoundClassScalePayoff,
        compoundAtPX_maxX Nm mu compound hq]

theorem compoundBlockPayoff_product_eq_classProduct {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (∏ X ∈ compoundXCarrierAtP Nm mu compound P,
        compoundBlockPayoff Nm mu compound P X) =
      ∏ q ∈ compoundMajorityAtP Nm mu compound P,
        compoundClassScalePayoff Nm mu q := by
  calc
    (∏ X ∈ compoundXCarrierAtP Nm mu compound P,
        compoundBlockPayoff Nm mu compound P X) =
        ∏ X ∈ compoundXCarrierAtP Nm mu compound P,
          ∏ q ∈ compoundAtPX Nm mu compound P X,
            compoundClassScalePayoff Nm mu q := by
      apply Finset.prod_congr rfl
      intro X hX
      exact compoundBlockPayoff_eq_class_product Nm mu compound P hX
    _ = ∏ q ∈ compoundMajorityAtP Nm mu compound P,
        compoundClassScalePayoff Nm mu q := by
      simpa [compoundAtPX] using
        (Finset.prod_fiberwise_of_maps_to
          (s := compoundMajorityAtP Nm mu compound P)
          (t := compoundXCarrierAtP Nm mu compound P)
          (g := fun q => maxXAtNY Nm mu q)
          (fun q hq => compoundMajorityAtP_mapsTo_X
            Nm mu compound P hq)
          (compoundClassScalePayoff Nm mu))

theorem compoundClassScalePayoff_le_quarter {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ)
    {q : NYClass} (hq : q ∈ compoundMajorityAtP Nm mu compound P) :
    compoundClassScalePayoff Nm mu q ≤
      compoundMajorityRootLoss (multiplicityNY Nm mu q) *
        compoundMajorityQuarterProduct Nm mu compound q := by
  have hmem :=
    (mem_compoundMajorityAtP_iff Nm mu compound P q).mp hq
  have hactive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp hmem.1).1
  have hC : ¬isSimpleMajorityAtNY Nm mu compound q := by
    unfold isSimpleMajorityAtNY
    omega
  simpa [compoundClassScalePayoff] using
    compoundMajority_quarter_payoff Nm mu compound hactive hC

theorem compoundClassPayoff_product_le_quarter {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (∏ q ∈ compoundMajorityAtP Nm mu compound P,
        compoundClassScalePayoff Nm mu q) ≤
      2 ^ (∑ q ∈ compoundMajorityAtP Nm mu compound P,
          multiplicityNY Nm mu q) *
        ∏ q ∈ compoundMajorityAtP Nm mu compound P,
          compoundMajorityQuarterProduct Nm mu compound q := by
  let s := compoundMajorityAtP Nm mu compound P
  calc
    (∏ q ∈ s, compoundClassScalePayoff Nm mu q) ≤
        ∏ q ∈ s,
          (compoundMajorityRootLoss (multiplicityNY Nm mu q) *
            compoundMajorityQuarterProduct Nm mu compound q) := by
      apply Finset.prod_le_prod
      · intro q hq
        exact Real.rpow_nonneg (by positivity) _
      · intro q hq
        exact compoundClassScalePayoff_le_quarter Nm mu compound P hq
    _ = (∏ q ∈ s,
          compoundMajorityRootLoss (multiplicityNY Nm mu q)) *
        ∏ q ∈ s,
          compoundMajorityQuarterProduct Nm mu compound q := by
      rw [Finset.prod_mul_distrib]
    _ ≤ (∏ q ∈ s, (2 : ℝ) ^ multiplicityNY Nm mu q) *
        ∏ q ∈ s,
          compoundMajorityQuarterProduct Nm mu compound q := by
      apply mul_le_mul_of_nonneg_right
      · apply Finset.prod_le_prod
        · intro q hq
          exact compoundMajorityRootLoss_nonneg _
        · intro q hq
          exact compoundMajorityRootLoss_le_two_pow _
      · apply Finset.prod_nonneg
        intro q hq
        exact compoundMajorityQuarterProduct_nonneg Nm mu compound q
    _ = 2 ^ (∑ q ∈ s, multiplicityNY Nm mu q) *
        ∏ q ∈ s,
          compoundMajorityQuarterProduct Nm mu compound q := by
      rw [Finset.prod_pow_eq_pow_sum]

/--
Completed compound-majority estimate (5.85)--(5.86), before the final
disjoint-leaf product embedding into the frozen Proposition 5.10 payoff.
-/
theorem fixedP_compoundMajority_multinomial_le_quarterProduct :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)) (P : ℕ),
        (Nat.multinomial (compoundMajorityAtP Nm mu compound P)
          (multiplicityNY Nm mu) : ℝ) ≤
          C ^ (∑ q ∈ compoundMajorityAtP Nm mu compound P,
            multiplicityNY Nm mu q) *
            ∏ q ∈ compoundMajorityAtP Nm mu compound P,
              compoundMajorityQuarterProduct Nm mu compound q := by
  obtain ⟨C₁, hC₁, hblock⟩ :=
    compoundMajority_multinomial_le_blockPayoff
  let C := 2 * C₁
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro t Nm mu compound P
  let M := ∑ q ∈ compoundMajorityAtP Nm mu compound P,
    multiplicityNY Nm mu q
  let Q := ∏ q ∈ compoundMajorityAtP Nm mu compound P,
    compoundMajorityQuarterProduct Nm mu compound q
  have hb := hblock Nm mu compound P
  rw [compoundBlockPayoff_product_eq_classProduct] at hb
  have hq := compoundClassPayoff_product_le_quarter Nm mu compound P
  change
    (∏ q ∈ compoundMajorityAtP Nm mu compound P,
      compoundClassScalePayoff Nm mu q) ≤ 2 ^ M * Q at hq
  calc
    (Nat.multinomial (compoundMajorityAtP Nm mu compound P)
        (multiplicityNY Nm mu) : ℝ) ≤
        C₁ ^ M *
          ∏ q ∈ compoundMajorityAtP Nm mu compound P,
            compoundClassScalePayoff Nm mu q := by
      simpa [M] using hb
    _ ≤ C₁ ^ M * (2 ^ M * Q) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = C ^ M * Q := by
      dsimp [C]
      rw [mul_pow]
      ring

set_option maxHeartbeats 800000 in
/--
The fixed-`P` assembly of (5.82)--(5.86).  The two majority pieces are
recombined with a single constant to the full mass `m_P`; the remaining
factors are exactly the normalized simple and compound leaf-local payoffs.
-/
theorem fixedP_majority_multinomial_le_localPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)) (P : ℕ),
        (Nat.multinomial (nyAtP Nm mu P)
          (multiplicityNY Nm mu) : ℝ) ≤
          C ^ multiplicityP Nm mu P *
            (∏ q ∈ simpleMajorityAtP Nm mu compound P,
              simpleMajorityScaleProduct Nm mu compound q) *
            ∏ q ∈ compoundMajorityAtP Nm mu compound P,
              compoundMajorityQuarterProduct Nm mu compound q := by
  obtain ⟨C₁, hC₁, hcompound⟩ :=
    fixedP_compoundMajority_multinomial_le_quarterProduct
  let C : ℝ := 2 * 65 * C₁
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro t ht hroot Nm mu compound P
  let s := simpleMajorityAtP Nm mu compound P
  let c := compoundMajorityAtP Nm mu compound P
  let MS := ∑ q ∈ s, multiplicityNY Nm mu q
  let MC := ∑ q ∈ c, multiplicityNY Nm mu q
  let M := multiplicityP Nm mu P
  let S := ∏ q ∈ s, simpleMajorityScaleProduct Nm mu compound q
  let Q := ∏ q ∈ c, compoundMajorityQuarterProduct Nm mu compound q
  let AS : ℝ :=
    Nat.multinomial s (multiplicityNY Nm mu)
  let AC : ℝ :=
    Nat.multinomial c (multiplicityNY Nm mu)
  have hmass : MS + MC = M := by
    dsimp [MS, MC, M, s, c]
    rw [← Finset.sum_union
      (simpleMajorityAtP_disjoint_compoundMajorityAtP
        Nm mu compound P)]
    rw [simpleMajorityAtP_union_compoundMajorityAtP,
      ← multiplicityP_eq_fiber_sum]
  have hMS : MS ≤ M := by omega
  have hMC : MC ≤ M := by omega
  have hpart :
      (Nat.multinomial (nyAtP Nm mu P)
          (multiplicityNY Nm mu) : ℝ) ≤
        2 ^ M * AS * AC := by
    dsimp [M, AS, AC, s, c]
    exact_mod_cast fixedP_majority_partition_le Nm mu compound P
  have hs : AS ≤ 65 ^ MS * S := by
    simpa [AS, MS, S, s] using
      fixedP_simpleMajority_multinomial_le_scaleProduct
        ht hroot Nm mu compound P
  have hc : AC ≤ C₁ ^ MC * Q := by
    simpa [AC, MC, Q, c] using hcompound Nm mu compound P
  have hS0 : 0 ≤ S := by
    dsimp [S]
    apply Finset.prod_nonneg
    intro q hq
    rw [simpleMajorityScaleProduct]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    apply Finset.prod_nonneg
    intro q hq
    exact compoundMajorityQuarterProduct_nonneg Nm mu compound q
  have hAS0 : 0 ≤ AS := by positivity
  have hAC0 : 0 ≤ AC := by positivity
  have h65pow : (65 : ℝ) ^ MS ≤ 65 ^ M :=
    pow_le_pow_right₀ (by norm_num) hMS
  have hCpow : C₁ ^ MC ≤ C₁ ^ M :=
    pow_le_pow_right₀ hC₁ hMC
  calc
    (Nat.multinomial (nyAtP Nm mu P)
        (multiplicityNY Nm mu) : ℝ) ≤
        2 ^ M * AS * AC := hpart
    _ ≤ 2 ^ M * (65 ^ MS * S) * AC := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (by positivity)) hAC0
    _ ≤ 2 ^ M * (65 ^ MS * S) * (C₁ ^ MC * Q) := by
      exact mul_le_mul_of_nonneg_left hc
        (mul_nonneg (by positivity)
          (mul_nonneg (by positivity) hS0))
    _ = 2 ^ M * 65 ^ MS * C₁ ^ MC * (S * Q) := by ring
    _ ≤ 2 ^ M * 65 ^ M * C₁ ^ M * (S * Q) := by
      apply mul_le_mul_of_nonneg_right
      · calc
          2 ^ M * 65 ^ MS * C₁ ^ MC ≤
              2 ^ M * 65 ^ M * C₁ ^ MC :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h65pow (by positivity))
              (by positivity)
          _ ≤ 2 ^ M * 65 ^ M * C₁ ^ M :=
            mul_le_mul_of_nonneg_left hCpow
              (mul_nonneg (by positivity) (by positivity))
      · exact mul_nonneg hS0 hQ0
    _ = C ^ M * S * Q := by
      dsimp [C]
      rw [mul_pow, mul_pow]
      ring

/-! ## Honest treatment of the `m_l = 2` normalization -/

def quarterFactorial (k : ℕ) : ℝ :=
  (k.factorial : ℝ) ^ (1 / 4 : ℝ)

def originalOuterLeafPayoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l : HeppLeaf t) : ℝ :=
  if l.1 ∈ compound then
    quarterFactorial (leafMultiplicity mu l)
  else
    (scaleN Nm (parentV l.1) : ℝ) ^ simpleScaleExponent mu l

def normalizedOuterLeafPayoff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l : HeppLeaf t) : ℝ :=
  if isNormalizedCompound mu compound l then
    quarterFactorial (leafMultiplicity mu l)
  else
    (scaleN Nm (parentV l.1) : ℝ) ^ simpleScaleExponent mu l

theorem quarterFactorial_two_le_two :
    quarterFactorial 2 ≤ 2 := by
  change (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2
  calc
    (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

theorem normalizedOuterLeafPayoff_le_two_mul_original {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l : HeppLeaf t) :
    normalizedOuterLeafPayoff Nm mu compound l ≤
      2 * originalOuterLeafPayoff Nm mu compound l := by
  by_cases hc : l.1 ∈ compound
  · simp [normalizedOuterLeafPayoff, originalOuterLeafPayoff,
      isNormalizedCompound, hc]
    have hnonneg : 0 ≤ quarterFactorial (leafMultiplicity mu l) := by
      exact Real.rpow_nonneg (by positivity) _
    linarith
  · by_cases hm : leafMultiplicity mu l = 2
    · simp [normalizedOuterLeafPayoff, originalOuterLeafPayoff,
        isNormalizedCompound, hc, hm, simpleScaleExponent]
      exact quarterFactorial_two_le_two
    · simp only [normalizedOuterLeafPayoff, originalOuterLeafPayoff,
        isNormalizedCompound, hc, hm, or_false, if_false]
      have hnonneg :
          0 ≤ (scaleN Nm (parentV l.1) : ℝ) ^
            simpleScaleExponent mu l := by positivity
      linarith

theorem normalizedOuterLeafPayoff_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l : HeppLeaf t) :
    0 ≤ normalizedOuterLeafPayoff Nm mu compound l := by
  rw [normalizedOuterLeafPayoff]
  split
  · exact Real.rpow_nonneg (by positivity) _
  · positivity

theorem quarterFactorial_one_le (k : ℕ) :
    1 ≤ quarterFactorial k := by
  have hk : 1 ≤ k.factorial := by
    have := Nat.factorial_pos k
    omega
  exact Real.one_le_rpow
    (by exact_mod_cast hk) (by norm_num)

theorem normalizedOuterLeafPayoff_one_le {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l : HeppLeaf t) :
    1 ≤ normalizedOuterLeafPayoff Nm mu compound l := by
  rw [normalizedOuterLeafPayoff]
  split
  · exact quarterFactorial_one_le (leafMultiplicity mu l)
  · apply one_le_pow₀
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (scaleN_pos Nm (parentV l.1)).ne'

theorem mem_maxFiberAtNY_nyClass {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q : NYClass} (hq : q ∈ nyCarrier Nm mu)
    {l : HeppLeaf t} (hl : l ∈ maxFiberAtNY Nm mu q) :
    singleScaleSigma2 Nm mu (singleScaleSigma1 Nm mu l) = q := by
  rw [mem_maxFiberAtNY_class Nm mu hq hl]
  exact (Finset.mem_filter.mp (maxNXAtNY_mem Nm mu q hq)).2

theorem maxFiberAtNY_disjoint_of_ne {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {q r : NYClass} (hq : q ∈ nyCarrier Nm mu)
    (hr : r ∈ nyCarrier Nm mu) (hqr : q ≠ r) :
    Disjoint (maxFiberAtNY Nm mu q) (maxFiberAtNY Nm mu r) := by
  apply Finset.disjoint_left.mpr
  intro l hlq hlr
  apply hqr
  exact (mem_maxFiberAtNY_nyClass Nm mu hq hlq).symm.trans
    (mem_maxFiberAtNY_nyClass Nm mu hr hlr)

def simpleMajorityLeafCarrierAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) : Finset (HeppLeaf t) :=
  (simpleMajorityAtP Nm mu compound P).biUnion fun q =>
    normalizedSimpleMaxFiber Nm mu compound q

def compoundMajorityLeafCarrierAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) : Finset (HeppLeaf t) :=
  (compoundMajorityAtP Nm mu compound P).biUnion fun q =>
    normalizedCompoundMaxFiber Nm mu compound q

def majorityLeafCarrierAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) : Finset (HeppLeaf t) :=
  simpleMajorityLeafCarrierAtP Nm mu compound P ∪
    compoundMajorityLeafCarrierAtP Nm mu compound P

theorem simpleMajorityMaxFibers_pairwiseDisjoint {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Set.PairwiseDisjoint
      (↑(simpleMajorityAtP Nm mu compound P))
      (normalizedSimpleMaxFiber Nm mu compound) := by
  intro q hq r hr hqr
  have hqActive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp
      ((mem_simpleMajorityAtP_iff Nm mu compound P q).mp hq).1).1
  have hrActive : r ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp
      ((mem_simpleMajorityAtP_iff Nm mu compound P r).mp hr).1).1
  exact (maxFiberAtNY_disjoint_of_ne Nm mu hqActive hrActive hqr).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem compoundMajorityMaxFibers_pairwiseDisjoint {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Set.PairwiseDisjoint
      (↑(compoundMajorityAtP Nm mu compound P))
      (normalizedCompoundMaxFiber Nm mu compound) := by
  intro q hq r hr hqr
  have hqActive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp
      ((mem_compoundMajorityAtP_iff Nm mu compound P q).mp hq).1).1
  have hrActive : r ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp
      ((mem_compoundMajorityAtP_iff Nm mu compound P r).mp hr).1).1
  exact (maxFiberAtNY_disjoint_of_ne Nm mu hqActive hrActive hqr).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem simpleMajorityLeafCarrier_disjoint_compound {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    Disjoint (simpleMajorityLeafCarrierAtP Nm mu compound P)
      (compoundMajorityLeafCarrierAtP Nm mu compound P) := by
  apply Finset.disjoint_left.mpr
  intro l hls hlc
  rcases Finset.mem_biUnion.mp hls with ⟨q, hq, hlq⟩
  rcases Finset.mem_biUnion.mp hlc with ⟨r, hr, hlr⟩
  have hqActive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp
      ((mem_simpleMajorityAtP_iff Nm mu compound P q).mp hq).1).1
  have hrActive : r ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp
      ((mem_compoundMajorityAtP_iff Nm mu compound P r).mp hr).1).1
  have hqr : q = r := by
    exact (mem_maxFiberAtNY_nyClass Nm mu hqActive
      (Finset.mem_filter.mp hlq).1).symm.trans
      (mem_maxFiberAtNY_nyClass Nm mu hrActive
        (Finset.mem_filter.mp hlr).1)
  subst r
  exact (Finset.disjoint_left.mp
    (simpleMajorityAtP_disjoint_compoundMajorityAtP
      Nm mu compound P)) hq hr

theorem simpleMajorityScaleProduct_product_eq_leafCarrier {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (∏ q ∈ simpleMajorityAtP Nm mu compound P,
        simpleMajorityScaleProduct Nm mu compound q) =
      ∏ l ∈ simpleMajorityLeafCarrierAtP Nm mu compound P,
        normalizedOuterLeafPayoff Nm mu compound l := by
  rw [simpleMajorityLeafCarrierAtP,
    Finset.prod_biUnion
      (simpleMajorityMaxFibers_pairwiseDisjoint Nm mu compound P)]
  apply Finset.prod_congr rfl
  intro q hq
  rw [simpleMajorityScaleProduct]
  apply Finset.prod_congr rfl
  intro l hl
  rw [normalizedOuterLeafPayoff]
  exact (if_neg (Finset.mem_filter.mp hl).2).symm

theorem compoundMajorityQuarterProduct_product_eq_leafCarrier {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (∏ q ∈ compoundMajorityAtP Nm mu compound P,
        compoundMajorityQuarterProduct Nm mu compound q) =
      ∏ l ∈ compoundMajorityLeafCarrierAtP Nm mu compound P,
        normalizedOuterLeafPayoff Nm mu compound l := by
  rw [compoundMajorityLeafCarrierAtP,
    Finset.prod_biUnion
      (compoundMajorityMaxFibers_pairwiseDisjoint Nm mu compound P)]
  apply Finset.prod_congr rfl
  intro q hq
  rw [compoundMajorityQuarterProduct]
  apply Finset.prod_congr rfl
  intro l hl
  rw [normalizedOuterLeafPayoff, quarterFactorial]
  exact (if_pos (Finset.mem_filter.mp hl).2).symm

theorem localMajorityPayoff_eq_leafCarrierProduct {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (∏ q ∈ simpleMajorityAtP Nm mu compound P,
        simpleMajorityScaleProduct Nm mu compound q) *
      (∏ q ∈ compoundMajorityAtP Nm mu compound P,
        compoundMajorityQuarterProduct Nm mu compound q) =
      ∏ l ∈ majorityLeafCarrierAtP Nm mu compound P,
        normalizedOuterLeafPayoff Nm mu compound l := by
  rw [simpleMajorityScaleProduct_product_eq_leafCarrier,
    compoundMajorityQuarterProduct_product_eq_leafCarrier,
    majorityLeafCarrierAtP,
    Finset.prod_union
      (simpleMajorityLeafCarrier_disjoint_compound
        Nm mu compound P)]

theorem simpleMajorityLeafCarrier_subset_leavesAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    simpleMajorityLeafCarrierAtP Nm mu compound P ⊆
      leavesAtP Nm mu P := by
  intro l hl
  rcases Finset.mem_biUnion.mp hl with ⟨q, hq, hlq⟩
  have hqP :=
    ((mem_simpleMajorityAtP_iff Nm mu compound P q).mp hq).1
  have hqActive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp hqP).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ l, ?_⟩
  rw [mem_maxFiberAtNY_nyClass Nm mu hqActive
    (Finset.mem_filter.mp hlq).1]
  exact (Finset.mem_filter.mp hqP).2

theorem compoundMajorityLeafCarrier_subset_leavesAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    compoundMajorityLeafCarrierAtP Nm mu compound P ⊆
      leavesAtP Nm mu P := by
  intro l hl
  rcases Finset.mem_biUnion.mp hl with ⟨q, hq, hlq⟩
  have hqP :=
    ((mem_compoundMajorityAtP_iff Nm mu compound P q).mp hq).1
  have hqActive : q ∈ nyCarrier Nm mu :=
    (Finset.mem_filter.mp hqP).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ l, ?_⟩
  rw [mem_maxFiberAtNY_nyClass Nm mu hqActive
    (Finset.mem_filter.mp hlq).1]
  exact (Finset.mem_filter.mp hqP).2

theorem majorityLeafCarrier_subset_leavesAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    majorityLeafCarrierAtP Nm mu compound P ⊆
      leavesAtP Nm mu P := by
  rw [majorityLeafCarrierAtP]
  exact Finset.union_subset
    (simpleMajorityLeafCarrier_subset_leavesAtP Nm mu compound P)
    (compoundMajorityLeafCarrier_subset_leavesAtP Nm mu compound P)

theorem localMajorityPayoff_le_normalizedLeavesAtP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (P : ℕ) :
    (∏ q ∈ simpleMajorityAtP Nm mu compound P,
        simpleMajorityScaleProduct Nm mu compound q) *
      (∏ q ∈ compoundMajorityAtP Nm mu compound P,
        compoundMajorityQuarterProduct Nm mu compound q) ≤
      ∏ l ∈ leavesAtP Nm mu P,
        normalizedOuterLeafPayoff Nm mu compound l := by
  rw [localMajorityPayoff_eq_leafCarrierProduct]
  apply Finset.prod_le_prod_of_subset_of_one_le
    (majorityLeafCarrier_subset_leavesAtP Nm mu compound P)
  · intro l hl
    exact normalizedOuterLeafPayoff_nonneg Nm mu compound l
  · intro l hl hnot
    exact normalizedOuterLeafPayoff_one_le Nm mu compound l

theorem originalOuterLeafPayoff_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (l : HeppLeaf t) :
    0 ≤ originalOuterLeafPayoff Nm mu compound l := by
  rw [originalOuterLeafPayoff]
  split
  · exact Real.rpow_nonneg (by positivity) _
  · positivity

/--
The multiplicity-two normalization bound on an arbitrary leaf carrier.
Keeping the carrier explicit is essential before multiplying the fixed-`P`
estimates over distinct values of `P`.
-/
theorem normalizedMajorityPayoff_finset_le {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (s : Finset (HeppLeaf t)) :
    (∏ l ∈ s, normalizedOuterLeafPayoff Nm mu compound l) ≤
      2 ^ s.card *
        ∏ l ∈ s, originalOuterLeafPayoff Nm mu compound l := by
  calc
    (∏ l ∈ s, normalizedOuterLeafPayoff Nm mu compound l) ≤
        ∏ l ∈ s,
          (2 * originalOuterLeafPayoff Nm mu compound l) := by
      apply Finset.prod_le_prod
      · intro l hl
        exact normalizedOuterLeafPayoff_nonneg Nm mu compound l
      · intro l hl
        exact normalizedOuterLeafPayoff_le_two_mul_original
          Nm mu compound l
    _ = 2 ^ s.card *
        ∏ l ∈ s, originalOuterLeafPayoff Nm mu compound l := by
      rw [Finset.prod_mul_distrib]
      simp

theorem leavesAtP_card_le_multiplicityP {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (P : ℕ) :
    (leavesAtP Nm mu P).card ≤ multiplicityP Nm mu P := by
  rw [multiplicityP_eq_leaf_sum]
  calc
    (leavesAtP Nm mu P).card =
        ∑ _l ∈ leavesAtP Nm mu P, 1 := by simp
    _ ≤ ∑ l ∈ leavesAtP Nm mu P, leafMultiplicity mu l := by
      apply Finset.sum_le_sum
      intro l hl
      have htwo := mu.two_le l.1 l.2
      change 1 ≤ mu.m l.1
      omega

set_option maxHeartbeats 800000 in
/--
The completed fixed-`P` outer-majority estimate (5.82)--(5.86), including
the canonical-fiber disjointness ledger and the honest `m_l = 2`
normalization.  No selected fiber is duplicated, and the final payoff is
restricted to the paper's exact carrier `L_P`.
-/
theorem fixedP_majority_multinomial_le_originalPayoff :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {t : PlaneTree} (_ht : t.isValid = true)
        (_hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (compound : Finset (VPos t)) (P : ℕ),
        (Nat.multinomial (nyAtP Nm mu P)
          (multiplicityNY Nm mu) : ℝ) ≤
          C ^ multiplicityP Nm mu P *
            ∏ l ∈ leavesAtP Nm mu P,
              originalOuterLeafPayoff Nm mu compound l := by
  obtain ⟨C₁, hC₁, hlocal⟩ :=
    fixedP_majority_multinomial_le_localPayoff
  let C : ℝ := 2 * C₁
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro t ht hroot Nm mu compound P
  let M := multiplicityP Nm mu P
  let S := ∏ q ∈ simpleMajorityAtP Nm mu compound P,
    simpleMajorityScaleProduct Nm mu compound q
  let Q := ∏ q ∈ compoundMajorityAtP Nm mu compound P,
    compoundMajorityQuarterProduct Nm mu compound q
  let R := ∏ l ∈ leavesAtP Nm mu P,
    normalizedOuterLeafPayoff Nm mu compound l
  let O := ∏ l ∈ leavesAtP Nm mu P,
    originalOuterLeafPayoff Nm mu compound l
  have hfirst :
      (Nat.multinomial (nyAtP Nm mu P)
          (multiplicityNY Nm mu) : ℝ) ≤ C₁ ^ M * S * Q := by
    simpa [M, S, Q] using hlocal ht hroot Nm mu compound P
  have hSQ : S * Q ≤ R := by
    simpa [S, Q, R] using
      localMajorityPayoff_le_normalizedLeavesAtP
        Nm mu compound P
  have hnorm :
      R ≤ 2 ^ (leavesAtP Nm mu P).card * O := by
    simpa [R, O] using
      normalizedMajorityPayoff_finset_le
        Nm mu compound (leavesAtP Nm mu P)
  have hcard :
      (leavesAtP Nm mu P).card ≤ M := by
    simpa [M] using leavesAtP_card_le_multiplicityP Nm mu P
  have htwo :
      (2 : ℝ) ^ (leavesAtP Nm mu P).card ≤ 2 ^ M :=
    pow_le_pow_right₀ (by norm_num) hcard
  have hO0 : 0 ≤ O := by
    dsimp [O]
    apply Finset.prod_nonneg
    intro l hl
    exact originalOuterLeafPayoff_nonneg Nm mu compound l
  calc
    (Nat.multinomial (nyAtP Nm mu P)
        (multiplicityNY Nm mu) : ℝ) ≤ C₁ ^ M * S * Q := hfirst
    _ = C₁ ^ M * (S * Q) := by ring
    _ ≤ C₁ ^ M * R :=
      mul_le_mul_of_nonneg_left hSQ
        (pow_nonneg (zero_le_one.trans hC₁) _)
    _ ≤ C₁ ^ M * (2 ^ (leavesAtP Nm mu P).card * O) :=
      mul_le_mul_of_nonneg_left hnorm
        (pow_nonneg (zero_le_one.trans hC₁) _)
    _ ≤ C₁ ^ M * (2 ^ M * O) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right htwo hO0)
        (pow_nonneg (zero_le_one.trans hC₁) _)
    _ = C ^ M * O := by
      dsimp [C]
      rw [mul_pow]
      ring

/--
Relabeling the multiplicity-two simple leaves costs at most `2^|L|`.
This is the explicit constant absorption omitted in the prose of the paper.
-/
theorem normalizedMajorityPayoff_le {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    (∏ l : HeppLeaf t, normalizedOuterLeafPayoff Nm mu compound l) ≤
      2 ^ Fintype.card (HeppLeaf t) *
        ∏ l : HeppLeaf t, originalOuterLeafPayoff Nm mu compound l := by
  calc
    (∏ l : HeppLeaf t, normalizedOuterLeafPayoff Nm mu compound l) ≤
        ∏ l : HeppLeaf t,
          (2 * originalOuterLeafPayoff Nm mu compound l) := by
      apply Finset.prod_le_prod
      · intro l hl
        exact normalizedOuterLeafPayoff_nonneg Nm mu compound l
      · intro l hl
        exact normalizedOuterLeafPayoff_le_two_mul_original
          Nm mu compound l
    _ = 2 ^ Fintype.card (HeppLeaf t) *
        ∏ l : HeppLeaf t, originalOuterLeafPayoff Nm mu compound l := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simp

/-!
## Downstream integration boundary

Equations (5.83)--(5.86), their recombination with (5.82), canonical-fiber
disjointness, and the `m_l = 2` normalization are all closed above by
`fixedP_majority_multinomial_le_originalPayoff`.

The next assembly file must first compose this `(N,Y)`-multinomial bound with
`fixedP_multinomial_le_outerNY`, whose left side is the required `(N,X)`
multinomial.  It must then multiply the resulting fixed-`P` bound over the
finite outer `P` carrier and identify the disjoint `leavesAtP` products with
the single global leaf product in Proposition 5.10.  These two interface
steps are downstream of, rather than missing steps in, (5.83)--(5.86).
-/

end

end Anderson4D
