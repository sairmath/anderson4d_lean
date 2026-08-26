import Anderson4D.Continuum.PrimitiveR51Assembly

/-!
# Period-lift reindexing for the primitive lattice reduction

The compatible-cell proof unwraps consecutive torus cells by integral
period blocks.  Consequently copied endpoints of a covariance pair need no
longer be literally equal as points of `Z4`; they are equal modulo the
compatible cell count.  This file records that loss exactly.

It also supplies the missing lossless conversion from an arbitrary full
`PartialPairing` to an `AcrossPairing` over its canonical lower-endpoint
half.  Thus the only remaining obstruction to feeding the unwrapped sum to
`primitiveAcrossLatticeSum` is the nonzero period defect, not a mismatch
between the two pairing representations.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators ENNReal

/-! ## Congruence modulo period-cell blocks -/

/-- Two lattice labels differ by an integral number of `q`-cell period
blocks in every coordinate. -/
def PeriodCongruent (q : ℤ) (a b : Z4) : Prop :=
  ∃ k : Z4, a = translateCellIndex q k b

instance (q : ℤ) (a b : Z4) : Decidable (PeriodCongruent q a b) := by
  classical
  exact Classical.propDecidable _

theorem periodCongruent_refl (q : ℤ) (a : Z4) :
    PeriodCongruent q a a := by
  refine ⟨0, ?_⟩
  ext i
  simp [translateCellIndex]

theorem periodCongruent_symm {q : ℤ} {a b : Z4}
    (h : PeriodCongruent q a b) :
    PeriodCongruent q b a := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨-k, ?_⟩
  ext i
  simp only [translateCellIndex, Pi.neg_apply]
  ring

theorem periodCongruent_trans {q : ℤ} {a b c : Z4}
    (hab : PeriodCongruent q a b)
    (hbc : PeriodCongruent q b c) :
    PeriodCongruent q a c := by
  obtain ⟨k, rfl⟩ := hab
  obtain ⟨l, rfl⟩ := hbc
  refine ⟨k + l, ?_⟩
  ext i
  simp only [translateCellIndex, Pi.add_apply]
  ring

theorem periodCongruent_iff {q : ℤ} {a b : Z4} :
    PeriodCongruent q a b ↔ PeriodCongruent q b a :=
  ⟨periodCongruent_symm, periodCongruent_symm⟩

/-- Pointwise period lift of a lattice tuple. -/
def IsPeriodLift {m : ℕ} (q : ℤ)
    (u y : Fin m → Z4) : Prop :=
  ∀ i, PeriodCongruent q (u i) (y i)

/-- Pairing compatibility after forgetting integral period blocks. -/
def RespectsPairingModuloPeriod {m : ℕ} (q : ℤ)
    (κ : PartialPairing (Fin m)) (u : Fin m → Z4) : Prop :=
  ∀ i, PeriodCongruent q (u (κ i)) (u i)

instance {m : ℕ} (q : ℤ) (κ : PartialPairing (Fin m))
    (u : Fin m → Z4) :
    Decidable (RespectsPairingModuloPeriod q κ u) :=
  inferInstanceAs
    (Decidable (∀ i, PeriodCongruent q (u (κ i)) (u i)))

theorem IsPeriodLift.respectsPairingModuloPeriod
    {m : ℕ} {q : ℤ} {κ : PartialPairing (Fin m)}
    {u y : Fin m → Z4}
    (hu : IsPeriodLift q u y) (hy : RespectsPairing κ y) :
    RespectsPairingModuloPeriod q κ u := by
  intro i
  exact periodCongruent_trans
    (periodCongruent_trans (hu (κ i))
      (by simpa [hy i] using periodCongruent_refl q (y i)))
    (periodCongruent_symm (hu i))

theorem nearestPeriodTranslate_periodCongruent
    (q : ℤ) (a b : Z4) :
    PeriodCongruent q (nearestPeriodTranslate q a b) b := by
  refine ⟨fun i => round ((((a - b) i : ℤ) : ℝ) / (q : ℝ)), rfl⟩

/-- Recursive path unwrapping is pointwise a period lift of the original
path.  No positivity or nonvanishing hypothesis is needed. -/
theorem unwrapLatticePath_forall₂_periodCongruent
    (q : ℤ) (a : Z4) (ys : List Z4) :
    List.Forall₂ (PeriodCongruent q)
      (unwrapLatticePath q a ys) ys := by
  induction ys generalizing a with
  | nil =>
      exact List.Forall₂.nil
  | cons b bs ih =>
      exact List.Forall₂.cons
        (nearestPeriodTranslate_periodCongruent q a b)
        (ih (nearestPeriodTranslate q a b))

/-- The complete primitive unwrapped path, including its fixed endpoints,
is pointwise congruent to the canonical copied-cell path. -/
theorem primitiveUnwrappedCellList_forall₂_periodCongruent
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    List.Forall₂ (PeriodCongruent (compatibleCellCount ε))
      (primitiveUnwrappedCellList ε n hn y)
      (primitiveOriginalCellList n hn y) := by
  unfold primitiveUnwrappedCellList primitiveOriginalCellList
  apply List.Forall₂.cons
  · exact periodCongruent_refl _ _
  · apply List.rel_append
    · exact unwrapLatticePath_forall₂_periodCongruent
        (compatibleCellCount ε) (primitiveFirstCell n hn y)
        (primitiveInternalCellLabels n hn y)
    · exact List.Forall₂.cons
        (nearestPeriodTranslate_periodCongruent
          (compatibleCellCount ε)
          (walkEnd (primitiveFirstCell n hn y)
            (primitiveUnwrappedInternal ε n hn y))
          (primitiveLastCell n hn y))
        List.Forall₂.nil

/-- Tuple form of the preceding period-lift statement. -/
theorem primitiveUnwrappedCellTuple_isPeriodLift
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    IsPeriodLift (compatibleCellCount ε)
      (primitiveUnwrappedCellTuple ε n hn y) y := by
  intro i
  have hrel :
      List.Forall₂ (PeriodCongruent (compatibleCellCount ε))
        (List.ofFn (primitiveUnwrappedCellTuple ε n hn y))
        (List.ofFn y) := by
    rw [primitiveUnwrappedCellTuple_ofFn,
      ← primitiveOriginalCellList_eq_ofFn]
    exact
      primitiveUnwrappedCellList_forall₂_periodCongruent ε n hn y
  have hi := hrel.get (i := i.val) (by simp) (by simp)
  convert hi using 1 <;> simp only [List.get_ofFn] <;>
    apply congrArg <;> apply Fin.ext <;> rfl

/-- The exact compatibility retained by the unwrapped tuple.  This replaces
the false claim that path unwrapping preserves `RespectsPairing` literally. -/
theorem primitiveUnwrappedCellTuple_respectsPairingModuloPeriod
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (y : Fin (2 * n) → Z4) (hy : RespectsPairing κ y) :
    RespectsPairingModuloPeriod (compatibleCellCount ε) κ
      (primitiveUnwrappedCellTuple ε n hn y) :=
  (primitiveUnwrappedCellTuple_isPeriodLift ε n hn y)
    |>.respectsPairingModuloPeriod hy

/-! ## Full partial pairings as across pairings -/

/-- Canonical choice of one endpoint from every pair: the smaller endpoint. -/
def pairingLowerHalf {m : ℕ} (κ : PartialPairing (Fin m)) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => i < κ i

@[simp] theorem mem_pairingLowerHalf
    {m : ℕ} {κ : PartialPairing (Fin m)} {i : Fin m} :
    i ∈ pairingLowerHalf κ ↔ i < κ i := by
  simp [pairingLowerHalf]

theorem apply_notMem_pairingLowerHalf
    {m : ℕ} (κ : PartialPairing (Fin m))
    {i : Fin m} (hi : i ∈ pairingLowerHalf κ) :
    κ i ∉ pairingLowerHalf κ := by
  rw [mem_pairingLowerHalf] at hi ⊢
  simpa only [κ.apply_apply] using (not_lt_of_ge hi.le)

theorem apply_mem_pairingLowerHalf_of_notMem
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull)
    {i : Fin m} (hi : i ∉ pairingLowerHalf κ) :
    κ i ∈ pairingLowerHalf κ := by
  rw [mem_pairingLowerHalf] at hi ⊢
  rw [κ.apply_apply]
  exact lt_of_le_of_ne (le_of_not_gt hi) (hfull i)

/-- A full pairing, oriented from each smaller endpoint to its larger mate. -/
def fullPairingToAcross
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    AcrossPairing (pairingLowerHalf κ) where
  toFun i :=
    ⟨κ i.1, Finset.mem_compl.mpr
      (apply_notMem_pairingLowerHalf κ i.2)⟩
  invFun j :=
    ⟨κ j.1, apply_mem_pairingLowerHalf_of_notMem κ hfull
      (Finset.mem_compl.mp j.2)⟩
  left_inv i := by
    apply Subtype.ext
    exact κ.apply_apply i.1
  right_inv j := by
    apply Subtype.ext
    exact κ.apply_apply j.1

/-- Extending the canonical across pairing recovers the original full
partial pairing literally. -/
theorem acrossToPartialPairing_fullPairingToAcross
    {m : ℕ} (κ : PartialPairing (Fin m)) (hfull : κ.IsFull) :
    acrossToPartialPairing (pairingLowerHalf κ)
      (fullPairingToAcross κ hfull) = κ := by
  ext i
  by_cases hi : i ∈ pairingLowerHalf κ
  · rw [acrossToPartialPairing_apply_mem _ _ hi]
    rfl
  · rw [acrossToPartialPairing_apply_notMem _ _ hi]
    rfl

theorem fullPairingToAcross_isPrimitive
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    IsPrimitiveAcross (pairingLowerHalf κ)
      (fullPairingToAcross κ hfull) := by
  unfold IsPrimitiveAcross
  rwa [acrossToPartialPairing_fullPairingToAcross κ hfull]

theorem fullPairingToAcross_mem_primitiveAcrossPairingFinset
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    fullPairingToAcross κ hfull ∈
      primitiveAcrossPairingFinset (pairingLowerHalf κ) :=
  mem_primitiveAcrossPairingFinset.mpr
    (fullPairingToAcross_isPrimitive hfull hprimitive)

/-- Every primitive full partial pairing occurs in the all-cuts across
carrier.  The map is injective because extending an across pairing recovers
the source pairing. -/
theorem sum_primitiveFullPairings_le_sum_across
    {m : ℕ} (F : PartialPairing (Fin m) → ℝ)
    (hF : ∀ κ, 0 ≤ F κ) :
    (∑ κ ∈
        (Finset.univ.filter fun κ : PartialPairing (Fin m) =>
          κ.IsFull ∧ IsPrimitive κ),
        F κ) ≤
      ∑ A : Finset (Fin m),
        ∑ κ ∈ primitiveAcrossPairingFinset A,
          F (acrossToPartialPairing A κ) := by
  classical
  let s :=
    Finset.univ.filter fun κ : PartialPairing (Fin m) =>
      κ.IsFull ∧ IsPrimitive κ
  let T : Finset ((A : Finset (Fin m)) × AcrossPairing A) :=
    Finset.univ.sigma fun A => primitiveAcrossPairingFinset A
  let lift :
      ↥s →
        ((A : Finset (Fin m)) × AcrossPairing A) :=
    fun κ =>
      ⟨pairingLowerHalf κ.1,
        fullPairingToAcross κ.1 (Finset.mem_filter.mp κ.2).2.1⟩
  have hlift_mem :
      ∀ κ : ↥s, lift κ ∈ T := by
    intro κ
    have hk := Finset.mem_filter.mp κ.2
    simp only [lift, T, Finset.mem_sigma,
      Finset.mem_univ, true_and]
    exact fullPairingToAcross_mem_primitiveAcrossPairingFinset
      hk.2.1 hk.2.2
  have hlift_inj : Function.Injective lift := by
    intro κ κ' heq
    have hk := (Finset.mem_filter.mp κ.2).2.1
    have hk' := (Finset.mem_filter.mp κ'.2).2.1
    have heq' := congrArg
      (fun d : ((A : Finset (Fin m)) × AcrossPairing A) =>
        acrossToPartialPairing d.1 d.2) heq
    apply Subtype.ext
    simpa only [lift,
      acrossToPartialPairing_fullPairingToAcross] using heq'
  have himage :
      Finset.image lift Finset.univ ⊆ T :=
    Finset.image_subset_iff.mpr fun κ _hκ => hlift_mem κ
  calc
    (∑ κ ∈ s, F κ) =
        ∑ κ : ↥s, F κ := by
      exact (Finset.sum_attach s F).symm
    _ = ∑ d ∈ Finset.image lift Finset.univ,
          F (acrossToPartialPairing d.1 d.2) := by
      rw [Finset.sum_image hlift_inj.injOn]
      apply Finset.sum_congr rfl
      intro κ _hκ
      simp only [lift,
        acrossToPartialPairing_fullPairingToAcross]
    _ ≤ ∑ d ∈ T,
          F (acrossToPartialPairing d.1 d.2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro d hdT hdnot
      exact hF _
    _ = ∑ A : Finset (Fin m),
          ∑ κ ∈ primitiveAcrossPairingFinset A,
            F (acrossToPartialPairing A κ) := by
      simp only [T, Finset.sum_sigma]
    _ = _ := rfl

/-- The literal `PartialPairing` version of the bounded primitive lattice
sum, before choosing a half for each full pairing. -/
def primitivePartialLatticeSum (M q : ℕ) : ℝ :=
  ∑ κ ∈
      (Finset.univ.filter fun κ : PartialPairing (Fin (q + 1)) =>
        κ.IsFull ∧ IsPrimitive κ),
    latticeChainSum M (q + 1) fun y =>
      if RespectsPairing κ y then reductionWeight q y else 0

/-- Complete full-pairing-to-half assembly at lattice level.  Summing over
all cuts can only overcount, and every primitive full pairing is represented
by its canonical lower-endpoint cut. -/
theorem primitivePartialLatticeSum_le_sum_primitiveAcrossLatticeSum
    (M q : ℕ) :
    primitivePartialLatticeSum M q ≤
      ∑ A : Finset (Fin (q + 1)),
        primitiveAcrossLatticeSum M q A := by
  let F : PartialPairing (Fin (q + 1)) → ℝ := fun κ =>
    latticeChainSum M (q + 1) fun y =>
      if RespectsPairing κ y then reductionWeight q y else 0
  have hF : ∀ κ, 0 ≤ F κ := by
    intro κ
    unfold F latticeChainSum
    apply Finset.sum_nonneg
    intro y hy
    split_ifs
    · exact reductionWeight_nonneg q y
    · exact le_rfl
  have hsum := sum_primitiveFullPairings_le_sum_across F hF
  unfold primitivePartialLatticeSum
  change
    (∑ κ ∈
        (Finset.univ.filter fun κ : PartialPairing (Fin (q + 1)) =>
          κ.IsFull ∧ IsPrimitive κ),
      F κ) ≤ _
  refine hsum.trans_eq ?_
  apply Finset.sum_congr rfl
  intro A hA
  unfold primitiveAcrossLatticeSum
  apply Finset.sum_congr rfl
  intro κ hκ
  unfold F pairedReductionStatistic latticeChainSum
  apply Finset.sum_congr rfl
  intro y hy
  change
    (if RespectsPairing (acrossToPartialPairing A κ) y then
      reductionWeight q y else 0) =
    (if RespectsWord A y κ then reductionWeight q y else 0)
  have hiff :=
    respectsPairing_acrossToPartialPairing_iff A κ y
  by_cases h : RespectsPairing (acrossToPartialPairing A κ) y
  · simp only [h, hiff.mp h, ↓reduceIte]
  · have hw : ¬RespectsWord A y κ := fun hw => h (hiff.mpr hw)
    simp only [h, hw, ↓reduceIte]

/-! ## The finite period-lift image and its exact fibers -/

/-- Canonical copied-cell carrier for one partial pairing. -/
def primitiveCanonicalCellCarrier
    (ε : ℝ) (n : ℕ) (κ : PartialPairing (Fin (2 * n))) :
    Finset (Fin (2 * n) → Z4) :=
  (Fintype.piFinset fun _ : Fin (2 * n) =>
    torusGrid (compatibleMeshSize ε)).filter (RespectsPairing κ)

/-- Image of the canonical copied-cell carrier under chain unwrapping. -/
def primitivePeriodLiftImage
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    Finset (Fin (2 * n) → Z4) :=
  (primitiveCanonicalCellCarrier ε n κ).image
    (primitiveUnwrappedCellTuple ε n hn)

@[simp] theorem mem_primitivePeriodLiftImage
    {ε : ℝ} {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    {u : Fin (2 * n) → Z4} :
    u ∈ primitivePeriodLiftImage ε n hn κ ↔
      ∃ y ∈ primitiveCanonicalCellCarrier ε n κ,
        primitiveUnwrappedCellTuple ε n hn y = u := by
  simp [primitivePeriodLiftImage]

theorem mem_primitivePeriodLiftImage_respectsModuloPeriod
    {ε : ℝ} {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    {u : Fin (2 * n) → Z4}
    (hu : u ∈ primitivePeriodLiftImage ε n hn κ) :
    RespectsPairingModuloPeriod (compatibleCellCount ε) κ u := by
  obtain ⟨y, hy, rfl⟩ := mem_primitivePeriodLiftImage.mp hu
  exact primitiveUnwrappedCellTuple_respectsPairingModuloPeriod
    ε n hn κ y (Finset.mem_filter.mp hy).2

/-- Cast a `Fin (2n)` tuple to the arithmetically equal carrier expected by
`reductionWeight (2n-1)`. -/
def primitiveReductionTupleOfCellTuple
    (n : ℕ) (hn : 1 ≤ n) (u : Fin (2 * n) → Z4) :
    Fin ((2 * n - 1) + 1) → Z4 :=
  fun i => u (Fin.cast (by omega) i)

@[simp] theorem primitiveReductionTupleOfCellTuple_unwrapped
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    primitiveReductionTupleOfCellTuple n hn
        (primitiveUnwrappedCellTuple ε n hn y) =
      primitiveUnwrappedReductionTuple ε n hn y := by
  rfl

/-- Exact multiplicity of one unwrapped tuple in the finite canonical
copied-cell carrier.  Boundary representatives are intentionally retained,
so this fiber need not have cardinality one. -/
def primitivePeriodLiftFiberMultiplicity
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (u : Fin (2 * n) → Z4) : ℕ :=
  ((primitiveCanonicalCellCarrier ε n κ).filter fun y =>
    primitiveUnwrappedCellTuple ε n hn y = u).card

/-- Exact finite fiber decomposition of the R-51 remainder.  This is a real
reindexing identity; it neither assumes injectivity at fundamental-domain
boundaries nor replaces the desired estimate by a certificate. -/
theorem primitiveUnwrappedReductionCellSum_eq_periodLiftFibers
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    primitiveUnwrappedReductionCellSum ε n hn κ =
      ∑ u ∈ primitivePeriodLiftImage ε n hn κ,
        (primitivePeriodLiftFiberMultiplicity ε n hn κ u : ENNReal) *
          ENNReal.ofReal
            (reductionWeight (2 * n - 1)
              (primitiveReductionTupleOfCellTuple n hn u)) := by
  classical
  unfold primitiveUnwrappedReductionCellSum
  change
    (∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
      ENNReal.ofReal
        (reductionWeight (2 * n - 1)
          (primitiveReductionTupleOfCellTuple n hn
            (primitiveUnwrappedCellTuple ε n hn y)))) = _
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := primitiveCanonicalCellCarrier ε n κ)
    (t := primitivePeriodLiftImage ε n hn κ)
    (g := primitiveUnwrappedCellTuple ε n hn)
    (fun y hy => Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    (fun y =>
      ENNReal.ofReal
        (reductionWeight (2 * n - 1)
          (primitiveReductionTupleOfCellTuple n hn
            (primitiveUnwrappedCellTuple ε n hn y))))]
  apply Finset.sum_congr rfl
  intro u hu
  unfold primitivePeriodLiftFiberMultiplicity
  calc
    (∑ y ∈ primitiveCanonicalCellCarrier ε n κ with
        primitiveUnwrappedCellTuple ε n hn y = u,
        ENNReal.ofReal
          (reductionWeight (2 * n - 1)
            (primitiveReductionTupleOfCellTuple n hn
              (primitiveUnwrappedCellTuple ε n hn y)))) =
      ∑ _y ∈
          (primitiveCanonicalCellCarrier ε n κ).filter fun y =>
            primitiveUnwrappedCellTuple ε n hn y = u,
        ENNReal.ofReal
          (reductionWeight (2 * n - 1)
            (primitiveReductionTupleOfCellTuple n hn u)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [(Finset.mem_filter.mp hy).2]
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Although unwrapped representatives can leave every a priori fixed box,
their finite image is contained in some honest `rdec_boundedTuples` box.
The bound is extracted from the actual finite image, not postulated. -/
theorem exists_primitivePeriodLiftImage_bounded
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    ∃ M : ℕ, ∀ u ∈ primitivePeriodLiftImage ε n hn κ,
      u ∈ rdec_boundedTuples M (2 * n) := by
  classical
  let S := primitivePeriodLiftImage ε n hn κ
  let β :=
    {u : Fin (2 * n) → Z4 // u ∈ S} ×
      Fin (2 * n) × Fin dim
  obtain ⟨M, hM⟩ :=
    Finite.exists_le
      (fun p : β => (p.1.1 p.2.1 p.2.2).natAbs)
  refine ⟨M, ?_⟩
  intro u hu
  rw [rdec_mem_boundedTuples]
  intro j i
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hM (⟨u, hu⟩, j, i)

end

end Anderson4D
