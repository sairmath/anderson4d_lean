import Anderson4D.Continuum.PrimitivePeriodReindex

/-!
# Winding-sector normalization for the primitive reduction

An unwrapped compatible-mesh path remembers occurrence-wise period lifts.
Paired occurrences are therefore congruent modulo the period count, but
need not be literally equal.  Here we normalize each pair to its canonical
anchor occurrence.  This produces a tuple consumed by the existing
`AcrossPairing` layer.

The normalization does not preserve the lattice weight.  We record an
explicit finite-box amplification, then sum the genuine canonical cell
carrier into a finite enlargement of `primitiveAcrossLatticeSum` in which
all (rather than only primitive) across pairings are retained.  No
certificate or assumed estimate is used.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators ENNReal

/-! ## Literal pairing normalization -/

/-- Replace both occurrences of every pair by the label at their common
canonical anchor. -/
def normalizePairingTuple {m : ℕ}
    (κ : PartialPairing (Fin m)) (u : Fin m → Z4) :
    Fin m → Z4 :=
  fun i => u (pairingAnchor κ i)

theorem normalizePairingTuple_respectsPairing
    {m : ℕ} (κ : PartialPairing (Fin m))
    (u : Fin m → Z4) :
    RespectsPairing κ (normalizePairingTuple κ u) := by
  intro i
  unfold normalizePairingTuple
  rw [pairingAnchor_apply]

theorem normalizePairingTuple_isPeriodLift
    {m : ℕ} {q : ℤ} {κ : PartialPairing (Fin m)}
    {u : Fin m → Z4}
    (hu : RespectsPairingModuloPeriod q κ u) :
    IsPeriodLift q (normalizePairingTuple κ u) u := by
  intro i
  unfold normalizePairingTuple pairingAnchor
  split_ifs with h
  · exact periodCongruent_refl q (u i)
  · exact hu i

theorem normalizePairingTuple_mem_bounded
    {m M : ℕ} {κ : PartialPairing (Fin m)}
    {u : Fin m → Z4}
    (hu : u ∈ rdec_boundedTuples M m) :
    normalizePairingTuple κ u ∈ rdec_boundedTuples M m := by
  rw [rdec_mem_boundedTuples] at hu ⊢
  intro j i
  exact hu (pairingAnchor κ j) i

/-! ## Explicit finite-box weight amplification -/

/-- A common upper bound for every Japanese bracket squared between two
points of `[-M,M]⁴`.  The deliberately coarse `2^(M+1)` form reuses the
project's decomposition bound and makes the loss manifestly exponential. -/
def windingBoxBase (M : ℕ) : ℝ :=
  1 + ((2 : ℝ) ^ (M + 1)) ^ 2

theorem windingBoxBase_pos (M : ℕ) :
    0 < windingBoxBase M := by
  unfold windingBoxBase
  positivity

theorem latticeBracketSq_le_windingBoxBase
    {M : ℕ} {x y : Z4}
    (hx : ∀ i, |x i| ≤ (M : ℤ))
    (hy : ∀ i, |y i| ≤ (M : ℤ)) :
    latticeBracketSq x y ≤ windingBoxBase M := by
  have hnorm := rdec_znorm_le_pow hx hy
  have hnorm0 : 0 ≤ znorm (x - y) := znorm_nonneg _
  unfold latticeBracketSq windingBoxBase
  nlinarith [sq_nonneg ((2 : ℝ) ^ (M + 1) - znorm (x - y))]

theorem one_le_latticeBracketSq (x y : Z4) :
    1 ≤ latticeBracketSq x y := by
  unfold latticeBracketSq
  nlinarith [sq_nonneg (znorm (x - y))]

theorem latticeEdgeWeight_le_one (x y : Z4) :
  latticeEdgeWeight x y ≤ 1 := by
  unfold latticeEdgeWeight
  exact (inv_le_one₀ (by
    nlinarith [sq_nonneg (znorm (x - y))])).mpr
      (by nlinarith [sq_nonneg (znorm (x - y))])

theorem windingBoxBase_inv_le_latticeEdgeWeight
    {M : ℕ} {x y : Z4}
    (hx : ∀ i, |x i| ≤ (M : ℤ))
    (hy : ∀ i, |y i| ≤ (M : ℤ)) :
    (windingBoxBase M)⁻¹ ≤ latticeEdgeWeight x y := by
  unfold latticeEdgeWeight
  exact (inv_le_inv₀ (windingBoxBase_pos M)
    (lt_of_lt_of_le zero_lt_one
      (one_le_latticeBracketSq x y))).mpr
    (latticeBracketSq_le_windingBoxBase hx hy)

/-- Lower bound for the full adjacent-edge product in a box. -/
def windingBoxEdgeFloor (M q : ℕ) : ℝ :=
  ∏ _j : AdjacentIndex (q + 1), (windingBoxBase M)⁻¹

theorem windingBoxEdgeFloor_pos (M q : ℕ) :
    0 < windingBoxEdgeFloor M q := by
  unfold windingBoxEdgeFloor
  apply Finset.prod_pos
  intro j hj
  exact inv_pos.mpr (windingBoxBase_pos M)

theorem windingBoxEdgeFloor_eq_pow (M q : ℕ) :
    windingBoxEdgeFloor M q = (windingBoxBase M)⁻¹ ^ q := by
  unfold windingBoxEdgeFloor
  rw [show (∏ _j : AdjacentIndex (q + 1),
      (windingBoxBase M)⁻¹) =
      (windingBoxBase M)⁻¹ ^
        Fintype.card (AdjacentIndex (q + 1)) by simp]
  congr 1
  simpa using Fintype.card_congr (adjacentIndexEquiv (q + 1))

/-- Explicit loss for replacing an arbitrary bounded tuple by a bounded
literally paired tuple. -/
def windingBoxAmplification (M q : ℕ) : ℝ :=
  windingBoxBase M / windingBoxEdgeFloor M q

theorem windingBoxAmplification_nonneg (M q : ℕ) :
    0 ≤ windingBoxAmplification M q := by
  unfold windingBoxAmplification
  exact div_nonneg (windingBoxBase_pos M).le
    (windingBoxEdgeFloor_pos M q).le

theorem windingBoxAmplification_eq_pow (M q : ℕ) :
    windingBoxAmplification M q = windingBoxBase M ^ (q + 1) := by
  rw [windingBoxAmplification, windingBoxEdgeFloor_eq_pow]
  rw [inv_pow, div_inv_eq_mul, ← pow_succ']

theorem reductionWeight_le_windingBoxBase
    {M q : ℕ} {y : Fin (q + 1) → Z4}
    (hy : y ∈ rdec_boundedTuples M (q + 1)) :
    reductionWeight q y ≤ windingBoxBase M := by
  rw [rdec_mem_boundedTuples] at hy
  unfold reductionWeight
  have hdiam :
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (q + 1) =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin (q + 1) =>
                latticeBracketSq (y i) (y j))) ≤
        windingBoxBase M := by
    apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    exact latticeBracketSq_le_windingBoxBase (hy i) (hy j)
  have hedge :
      (∏ j : AdjacentIndex (q + 1),
        latticeEdgeWeight (y j.1) (y (adjacentSucc j))) ≤ 1 := by
    apply Finset.prod_le_one
    · intro j hj
      exact latticeEdgeWeight_nonneg _ _
    · intro j hj
      exact latticeEdgeWeight_le_one _ _
  have hdiam0 :
      0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (q + 1) =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun j : Fin (q + 1) =>
              latticeBracketSq (y i) (y j))) := by
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) y
  calc
    _ ≤ windingBoxBase M * 1 :=
      mul_le_mul hdiam hedge
        (Finset.prod_nonneg fun j _ => latticeEdgeWeight_nonneg _ _)
        (windingBoxBase_pos M).le
    _ = windingBoxBase M := mul_one _

theorem windingBoxEdgeFloor_le_reductionWeight
    {M q : ℕ} {y : Fin (q + 1) → Z4}
    (hy : y ∈ rdec_boundedTuples M (q + 1)) :
    windingBoxEdgeFloor M q ≤ reductionWeight q y := by
  rw [rdec_mem_boundedTuples] at hy
  unfold reductionWeight windingBoxEdgeFloor
  have hedge :
      (∏ _j : AdjacentIndex (q + 1), (windingBoxBase M)⁻¹) ≤
        ∏ j : AdjacentIndex (q + 1),
          latticeEdgeWeight (y j.1) (y (adjacentSucc j)) := by
    apply Finset.prod_le_prod
    · intro j hj
      exact inv_nonneg.mpr (windingBoxBase_pos M).le
    · intro j hj
      exact windingBoxBase_inv_le_latticeEdgeWeight
        (hy j.1) (hy (adjacentSucc j))
  have hone :
      1 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (q + 1) =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun j : Fin (q + 1) =>
              latticeBracketSq (y i) (y j))) := by
    let i : Fin (q + 1) := 0
    exact (one_le_latticeBracketSq (y i) (y i)).trans
      ((Finset.le_sup'
        (f := fun j : Fin (q + 1) =>
          latticeBracketSq (y i) (y j)) (by simp)).trans
        (Finset.le_sup'
          (f := fun i : Fin (q + 1) =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun j : Fin (q + 1) =>
                latticeBracketSq (y i) (y j))) (by simp)))
  have hfloor0 :
      0 ≤ ∏ _j : AdjacentIndex (q + 1),
        (windingBoxBase M)⁻¹ := by
    exact Finset.prod_nonneg fun _j _ =>
      inv_nonneg.mpr (windingBoxBase_pos M).le
  calc
    _ ≤ 1 *
        (∏ j : AdjacentIndex (q + 1),
          latticeEdgeWeight (y j.1) (y (adjacentSucc j))) := by
      simpa only [one_mul] using hedge
    _ ≤ _ := mul_le_mul hone le_rfl
      (Finset.prod_nonneg fun j _ => latticeEdgeWeight_nonneg _ _)
      (primitiveTupleDiameterBracketSq_nonneg (by omega) y)

/-- Any two tuples in the same finite box have comparable reduction
weights with the explicit exponential loss above. -/
theorem reductionWeight_le_windingBoxAmplification_mul
    {M q : ℕ} {u v : Fin (q + 1) → Z4}
    (hu : u ∈ rdec_boundedTuples M (q + 1))
    (hv : v ∈ rdec_boundedTuples M (q + 1)) :
    reductionWeight q u ≤
      windingBoxAmplification M q * reductionWeight q v := by
  have huB := reductionWeight_le_windingBoxBase hu
  have hvF := windingBoxEdgeFloor_le_reductionWeight hv
  have hF : 0 < windingBoxEdgeFloor M q :=
    windingBoxEdgeFloor_pos M q
  have hA : 0 ≤ windingBoxAmplification M q :=
    windingBoxAmplification_nonneg M q
  calc
    reductionWeight q u ≤ windingBoxBase M := huB
    _ = windingBoxAmplification M q *
        windingBoxEdgeFloor M q := by
      unfold windingBoxAmplification
      field_simp
    _ ≤ windingBoxAmplification M q *
        reductionWeight q v :=
      mul_le_mul_of_nonneg_left hvF hA

/-! ## Reduction-index transport and the enlarged across sum -/

/-- Arithmetic equivalence between the cell tuple and the literal carrier
of `reductionWeight (2n-1)`. -/
def primitiveReductionIndexEquiv (n : ℕ) (hn : 1 ≤ n) :
    Fin (2 * n) ≃ Fin ((2 * n - 1) + 1) :=
  finCongr (by omega)

theorem primitiveReductionIndexEquiv_le_iff
    (n : ℕ) (hn : 1 ≤ n) (i j : Fin (2 * n)) :
    primitiveReductionIndexEquiv n hn i ≤
        primitiveReductionIndexEquiv n hn j ↔
      i ≤ j := by
  rfl

theorem primitiveReductionIndexEquiv_symm_le_iff
    (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin ((2 * n - 1) + 1)) :
    (primitiveReductionIndexEquiv n hn).symm i ≤
        (primitiveReductionIndexEquiv n hn).symm j ↔
      i ≤ j := by
  rfl

/-- Transport a paper pairing to the literal reduction-weight carrier. -/
def primitiveReductionPairing
    (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    PartialPairing (Fin ((2 * n - 1) + 1)) :=
  PartialPairing.congr (primitiveReductionIndexEquiv n hn) κ

theorem primitiveReductionPairing_isFull
    {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    (hκ : κ.IsFull) :
    (primitiveReductionPairing n hn κ).IsFull := by
  intro i
  unfold primitiveReductionPairing
  simp only [PartialPairing.congr_apply_apply]
  intro h
  have h' := congrArg (primitiveReductionIndexEquiv n hn).symm h
  exact hκ ((primitiveReductionIndexEquiv n hn).symm i) (by
    simpa using h')

theorem primitiveReductionPairing_isPrimitive
    {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    (hκ : IsPrimitive κ) :
    IsPrimitive (primitiveReductionPairing n hn κ) := by
  intro a b hab hfp
  let e := primitiveReductionIndexEquiv n hn
  let a' : Fin (2 * n) := e.symm a
  let b' : Fin (2 * n) := e.symm b
  have hab' : a' ≤ b' := by
    exact hab
  have hfp' : IsFullyPairedOn κ (Finset.Icc a' b') := by
    constructor
    · intro i hi
      have hei : e i ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc] at hi ⊢
        constructor
        · rw [← e.apply_symm_apply a,
            primitiveReductionIndexEquiv_le_iff]
          exact hi.1
        · rw [← e.apply_symm_apply b,
            primitiveReductionIndexEquiv_le_iff]
          exact hi.2
      have hne := hfp.1 (e i) hei
      simpa [primitiveReductionPairing, e] using hne
    · intro i hi
      have hei : e i ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc] at hi ⊢
        constructor
        · rw [← e.apply_symm_apply a,
            primitiveReductionIndexEquiv_le_iff]
          exact hi.1
        · rw [← e.apply_symm_apply b,
            primitiveReductionIndexEquiv_le_iff]
          exact hi.2
      have hmem := hfp.2 (e i) hei
      rw [Finset.mem_Icc] at hmem ⊢
      change e (e.symm a) ≤ e (κ i) ∧ e (κ i) ≤ b at hmem
      constructor
      · rw [← e.apply_symm_apply a,
          primitiveReductionIndexEquiv_le_iff] at hmem
        exact hmem.1
      · rw [← e.apply_symm_apply b,
          primitiveReductionIndexEquiv_le_iff] at hmem
        exact hmem.2
  have hwhole := hκ a' b' hab' hfp'
  ext i
  simp only [Finset.mem_Icc, Finset.mem_univ, iff_true]
  have hi : e.symm i ∈ Finset.Icc a' b' := by
    rw [hwhole]
    exact Finset.mem_univ _
  rw [Finset.mem_Icc] at hi
  constructor
  · exact
      (primitiveReductionIndexEquiv_symm_le_iff n hn a i).mp hi.1
  · exact
      (primitiveReductionIndexEquiv_symm_le_iff n hn i b).mp hi.2

theorem primitiveReductionTupleOfCellTuple_mem_bounded
    {n M : ℕ} {hn : 1 ≤ n}
    {u : Fin (2 * n) → Z4}
    (hu : u ∈ rdec_boundedTuples M (2 * n)) :
    primitiveReductionTupleOfCellTuple n hn u ∈
      rdec_boundedTuples M ((2 * n - 1) + 1) := by
  rw [rdec_mem_boundedTuples] at hu ⊢
  intro j i
  exact hu (Fin.cast (by omega) j) i

/-- The finite enlargement of `primitiveAcrossLatticeSum` obtained by
retaining every across pairing, including the nonprimitive ones. -/
def allAcrossLatticeSum
    (M q : ℕ) (A : Finset (Fin (q + 1))) : ℝ :=
  ∑ κ : AcrossPairing A,
    latticeChainSum M (q + 1) (pairedReductionStatistic q A κ)

theorem allAcrossLatticeSum_nonneg
    (M q : ℕ) (A : Finset (Fin (q + 1))) :
    0 ≤ allAcrossLatticeSum M q A := by
  unfold allAcrossLatticeSum
  apply Finset.sum_nonneg
  intro κ hκ
  unfold latticeChainSum
  apply Finset.sum_nonneg
  intro y hy
  exact pairedReductionStatistic_nonneg q A κ y

/-- The exact nonprimitive remainder introduced by the enlarged carrier. -/
def nonprimitiveAcrossLatticeSum
    (M q : ℕ) (A : Finset (Fin (q + 1))) : ℝ :=
  ∑ κ ∈ (Finset.univ.filter fun κ : AcrossPairing A =>
      ¬IsPrimitiveAcross A κ),
    latticeChainSum M (q + 1) (pairedReductionStatistic q A κ)

theorem nonprimitiveAcrossLatticeSum_nonneg
    (M q : ℕ) (A : Finset (Fin (q + 1))) :
    0 ≤ nonprimitiveAcrossLatticeSum M q A := by
  unfold nonprimitiveAcrossLatticeSum
  apply Finset.sum_nonneg
  intro κ hκ
  unfold latticeChainSum
  apply Finset.sum_nonneg
  intro y hy
  exact pairedReductionStatistic_nonneg q A κ y

/-- Exact ledger for the finite enlargement: no other terms are hidden. -/
theorem allAcrossLatticeSum_eq_primitive_add_nonprimitive
    (M q : ℕ) (A : Finset (Fin (q + 1))) :
    allAcrossLatticeSum M q A =
      primitiveAcrossLatticeSum M q A +
        nonprimitiveAcrossLatticeSum M q A := by
  unfold allAcrossLatticeSum primitiveAcrossLatticeSum
    primitiveAcrossPairingFinset nonprimitiveAcrossLatticeSum
  exact (Finset.sum_filter_add_sum_filter_not
    Finset.univ (IsPrimitiveAcross A)
    (fun κ =>
      latticeChainSum M (q + 1)
        (pairedReductionStatistic q A κ))).symm

/-! ## Genuine winding-sector sum assembly -/

/-- Real-valued version of the finite unwrapped cell sum. -/
def primitiveUnwrappedReductionCellRealSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) : ℝ :=
  ∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
    reductionWeight (2 * n - 1)
      (primitiveUnwrappedReductionTuple ε n hn y)

theorem primitiveUnwrappedReductionCellSum_eq_ofReal_realSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    primitiveUnwrappedReductionCellSum ε n hn κ =
      ENNReal.ofReal
        (primitiveUnwrappedReductionCellRealSum ε n hn κ) := by
  unfold primitiveUnwrappedReductionCellSum
    primitiveUnwrappedReductionCellRealSum
    primitiveCanonicalCellCarrier
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro y hy
  exact reductionWeight_nonneg _ _

/-- Every actual period-lift fiber is bounded by the canonical copied-cell
carrier cardinality. -/
theorem primitivePeriodLiftFiberMultiplicity_le_carrier
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (u : Fin (2 * n) → Z4) :
    primitivePeriodLiftFiberMultiplicity ε n hn κ u ≤
      (primitiveCanonicalCellCarrier ε n κ).card := by
  unfold primitivePeriodLiftFiberMultiplicity
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The number of winding sectors is bounded by the same genuine finite
carrier. -/
theorem card_primitivePeriodLiftImage_le_carrier
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    (primitivePeriodLiftImage ε n hn κ).card ≤
      (primitiveCanonicalCellCarrier ε n κ).card := by
  unfold primitivePeriodLiftImage
  exact Finset.card_image_le

/-- Every normalized tuple contributes to the enlarged across sum associated
with the canonical lower half of the transported pairing. -/
theorem normalized_reductionWeight_le_allAcrossLatticeSum
    {n M : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    (hfull : κ.IsFull)
    {u : Fin ((2 * n - 1) + 1) → Z4}
    (hu : u ∈ rdec_boundedTuples M ((2 * n - 1) + 1)) :
    reductionWeight (2 * n - 1)
        (normalizePairingTuple
          (primitiveReductionPairing n hn κ) u) ≤
      allAcrossLatticeSum M (2 * n - 1)
        (pairingLowerHalf
          (primitiveReductionPairing n hn κ)) := by
  let κr := primitiveReductionPairing n hn κ
  have hfullr : κr.IsFull :=
    primitiveReductionPairing_isFull hfull
  let A := pairingLowerHalf κr
  let κa : AcrossPairing A :=
    fullPairingToAcross κr hfullr
  let v := normalizePairingTuple κr u
  have hvbox :
      v ∈ rdec_boundedTuples M ((2 * n - 1) + 1) :=
    normalizePairingTuple_mem_bounded hu
  have hvrespect : RespectsPairing κr v :=
    normalizePairingTuple_respectsPairing κr u
  have hvword : RespectsWord A v κa := by
    apply
      (respectsPairing_acrossToPartialPairing_iff A κa v).mp
    rw [acrossToPartialPairing_fullPairingToAcross κr hfullr]
    exact hvrespect
  have hfixed :
      reductionWeight (2 * n - 1) v ≤
        latticeChainSum M ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κa) := by
    unfold latticeChainSum
    have hnonneg :
        ∀ w ∈ rdec_boundedTuples M ((2 * n - 1) + 1),
          0 ≤ pairedReductionStatistic (2 * n - 1) A κa w := by
      intro w hw
      exact pairedReductionStatistic_nonneg _ _ _ _
    have hone := Finset.single_le_sum hnonneg hvbox
    unfold pairedReductionStatistic at hone
    simp only [hvword, ↓reduceIte] at hone
    exact hone
  have hacross :
      latticeChainSum M ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κa) ≤
        allAcrossLatticeSum M (2 * n - 1) A := by
    unfold allAcrossLatticeSum
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (AcrossPairing A)))
      (f := fun κ' =>
        latticeChainSum M ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κ'))
      (fun κ' hκ' => by
        unfold latticeChainSum
        apply Finset.sum_nonneg
        intro w hw
        exact pairedReductionStatistic_nonneg _ _ _ _)
      (Finset.mem_univ κa)
  exact hfixed.trans hacross

/-- Primitive version of the preceding pointwise assembly.  Transport along
the arithmetic index equivalence preserves primitivity, so the canonical
across pairing is an actual member of the existing primitive carrier. -/
theorem normalized_reductionWeight_le_primitiveAcrossLatticeSum
    {n M : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    {u : Fin ((2 * n - 1) + 1) → Z4}
    (hu : u ∈ rdec_boundedTuples M ((2 * n - 1) + 1)) :
    reductionWeight (2 * n - 1)
        (normalizePairingTuple
          (primitiveReductionPairing n hn κ) u) ≤
      primitiveAcrossLatticeSum M (2 * n - 1)
        (pairingLowerHalf
          (primitiveReductionPairing n hn κ)) := by
  let κr := primitiveReductionPairing n hn κ
  have hfullr : κr.IsFull :=
    primitiveReductionPairing_isFull hfull
  have hprimitiver : IsPrimitive κr :=
    primitiveReductionPairing_isPrimitive hprimitive
  let A := pairingLowerHalf κr
  let κa : AcrossPairing A :=
    fullPairingToAcross κr hfullr
  let v := normalizePairingTuple κr u
  have hvbox :
      v ∈ rdec_boundedTuples M ((2 * n - 1) + 1) :=
    normalizePairingTuple_mem_bounded hu
  have hvrespect : RespectsPairing κr v :=
    normalizePairingTuple_respectsPairing κr u
  have hvword : RespectsWord A v κa := by
    apply
      (respectsPairing_acrossToPartialPairing_iff A κa v).mp
    rw [acrossToPartialPairing_fullPairingToAcross κr hfullr]
    exact hvrespect
  have hκamem : κa ∈ primitiveAcrossPairingFinset A := by
    apply mem_primitiveAcrossPairingFinset.mpr
    exact fullPairingToAcross_isPrimitive hfullr hprimitiver
  have hfixed :
      reductionWeight (2 * n - 1) v ≤
        latticeChainSum M ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κa) := by
    unfold latticeChainSum
    have hnonneg :
        ∀ w ∈ rdec_boundedTuples M ((2 * n - 1) + 1),
          0 ≤ pairedReductionStatistic (2 * n - 1) A κa w := by
      intro w hw
      exact pairedReductionStatistic_nonneg _ _ _ _
    have hone := Finset.single_le_sum hnonneg hvbox
    unfold pairedReductionStatistic at hone
    simp only [hvword, ↓reduceIte] at hone
    exact hone
  have hacross :
      latticeChainSum M ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κa) ≤
        primitiveAcrossLatticeSum M (2 * n - 1) A := by
    unfold primitiveAcrossLatticeSum
    exact Finset.single_le_sum
      (s := primitiveAcrossPairingFinset A)
      (f := fun κ' =>
        latticeChainSum M ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κ'))
      (fun κ' hκ' => by
        unfold latticeChainSum
        apply Finset.sum_nonneg
        intro w hw
        exact pairedReductionStatistic_nonneg _ _ _ _)
      hκamem
  exact hfixed.trans hacross

/-- **Winding-sector bridge.**

For a genuine full pairing, the complete unwrapped cell sum is bounded by
an explicitly finite carrier cardinality, the explicit exponential box
amplification, and the existing across lattice machine enlarged only by its
displayed nonprimitive remainder. -/
theorem exists_primitiveUnwrappedReductionCellRealSum_le_allAcross
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    ∃ M : ℕ,
      primitiveUnwrappedReductionCellRealSum ε n hn κ ≤
        ((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
          windingBoxAmplification M (2 * n - 1) *
          allAcrossLatticeSum M (2 * n - 1)
            (pairingLowerHalf
              (primitiveReductionPairing n hn κ)) := by
  obtain ⟨M, hM⟩ :=
    exists_primitivePeriodLiftImage_bounded ε n hn κ
  refine ⟨M, ?_⟩
  unfold primitiveUnwrappedReductionCellRealSum
  let A : ℝ := windingBoxAmplification M (2 * n - 1)
  let S : ℝ :=
    allAcrossLatticeSum M (2 * n - 1)
      (pairingLowerHalf (primitiveReductionPairing n hn κ))
  calc
    (∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
        reductionWeight (2 * n - 1)
          (primitiveUnwrappedReductionTuple ε n hn y)) ≤
      ∑ _y ∈ primitiveCanonicalCellCarrier ε n κ, A * S := by
        apply Finset.sum_le_sum
        intro y hy
        let u := primitiveUnwrappedCellTuple ε n hn y
        let ur := primitiveReductionTupleOfCellTuple n hn u
        let v := normalizePairingTuple
          (primitiveReductionPairing n hn κ) ur
        have huImage :
            u ∈ primitivePeriodLiftImage ε n hn κ :=
          Finset.mem_image.mpr ⟨y, hy, rfl⟩
        have hubox : u ∈ rdec_boundedTuples M (2 * n) :=
          hM u huImage
        have hurbox :
            ur ∈ rdec_boundedTuples M ((2 * n - 1) + 1) :=
          primitiveReductionTupleOfCellTuple_mem_bounded hubox
        have hvbox :
            v ∈ rdec_boundedTuples M ((2 * n - 1) + 1) :=
          normalizePairingTuple_mem_bounded hurbox
        have hcompare :
            reductionWeight (2 * n - 1) ur ≤
              A * reductionWeight (2 * n - 1) v := by
          exact reductionWeight_le_windingBoxAmplification_mul
            hurbox hvbox
        have hvsum :
            reductionWeight (2 * n - 1) v ≤ S := by
          exact normalized_reductionWeight_le_allAcrossLatticeSum
            hfull hurbox
        exact hcompare.trans
          (mul_le_mul_of_nonneg_left hvsum
            (windingBoxAmplification_nonneg M (2 * n - 1)))
    _ = ((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
          A * S := by
      simp
      ring
    _ = _ := rfl

theorem primitiveUnwrappedReductionCellSum_le_ofReal_allAcross
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    ∃ M : ℕ,
      primitiveUnwrappedReductionCellSum ε n hn κ ≤
        ENNReal.ofReal
          (((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
            windingBoxAmplification M (2 * n - 1) *
            allAcrossLatticeSum M (2 * n - 1)
              (pairingLowerHalf
                (primitiveReductionPairing n hn κ))) := by
  obtain ⟨M, hM⟩ :=
    exists_primitiveUnwrappedReductionCellRealSum_le_allAcross
      ε n hn κ hfull
  refine ⟨M, ?_⟩
  rw [primitiveUnwrappedReductionCellSum_eq_ofReal_realSum]
  exact ENNReal.ofReal_le_ofReal hM

/-- Fully expanded endpoint of the winding-sector reduction.  The
amplification is the displayed power `base^(2n)`, and the enlarged across
carrier is split exactly into the existing primitive sum plus its explicit
nonprimitive remainder. -/
theorem primitiveUnwrappedReductionCellSum_le_primitive_add_remainder
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull) :
    ∃ M : ℕ,
      primitiveUnwrappedReductionCellSum ε n hn κ ≤
        ENNReal.ofReal
          (((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
            windingBoxBase M ^ (2 * n) *
            (primitiveAcrossLatticeSum M (2 * n - 1)
                (pairingLowerHalf
                  (primitiveReductionPairing n hn κ)) +
              nonprimitiveAcrossLatticeSum M (2 * n - 1)
                (pairingLowerHalf
                  (primitiveReductionPairing n hn κ)))) := by
  obtain ⟨M, hM⟩ :=
    primitiveUnwrappedReductionCellSum_le_ofReal_allAcross
      ε n hn κ hfull
  refine ⟨M, ?_⟩
  rw [windingBoxAmplification_eq_pow,
    allAcrossLatticeSum_eq_primitive_add_nonprimitive] at hM
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)] using hM

theorem primitiveUnwrappedReductionCellSum_le_primitive_add_remainder_of_mem
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (hκ : κ ∈ primitiveFullPairings n) :
    ∃ M : ℕ,
      primitiveUnwrappedReductionCellSum ε n hn κ ≤
        ENNReal.ofReal
          (((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
            windingBoxBase M ^ (2 * n) *
            (primitiveAcrossLatticeSum M (2 * n - 1)
                (pairingLowerHalf
                  (primitiveReductionPairing n hn κ)) +
              nonprimitiveAcrossLatticeSum M (2 * n - 1)
                (pairingLowerHalf
                  (primitiveReductionPairing n hn κ)))) :=
  primitiveUnwrappedReductionCellSum_le_primitive_add_remainder
    ε n hn κ (mem_primitiveFullPairings.mp hκ).1

/-- Real-valued winding-sector bridge directly into the existing primitive
across sum. -/
theorem exists_primitiveUnwrappedReductionCellRealSum_le_primitiveAcross
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    ∃ M : ℕ,
      primitiveUnwrappedReductionCellRealSum ε n hn κ ≤
        ((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
          windingBoxAmplification M (2 * n - 1) *
          primitiveAcrossLatticeSum M (2 * n - 1)
            (pairingLowerHalf
              (primitiveReductionPairing n hn κ)) := by
  obtain ⟨M, hM⟩ :=
    exists_primitivePeriodLiftImage_bounded ε n hn κ
  refine ⟨M, ?_⟩
  unfold primitiveUnwrappedReductionCellRealSum
  let A : ℝ := windingBoxAmplification M (2 * n - 1)
  let S : ℝ :=
    primitiveAcrossLatticeSum M (2 * n - 1)
      (pairingLowerHalf (primitiveReductionPairing n hn κ))
  calc
    (∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
        reductionWeight (2 * n - 1)
          (primitiveUnwrappedReductionTuple ε n hn y)) ≤
      ∑ _y ∈ primitiveCanonicalCellCarrier ε n κ, A * S := by
        apply Finset.sum_le_sum
        intro y hy
        let u := primitiveUnwrappedCellTuple ε n hn y
        let ur := primitiveReductionTupleOfCellTuple n hn u
        let v := normalizePairingTuple
          (primitiveReductionPairing n hn κ) ur
        have huImage :
            u ∈ primitivePeriodLiftImage ε n hn κ :=
          Finset.mem_image.mpr ⟨y, hy, rfl⟩
        have hubox : u ∈ rdec_boundedTuples M (2 * n) :=
          hM u huImage
        have hurbox :
            ur ∈ rdec_boundedTuples M ((2 * n - 1) + 1) :=
          primitiveReductionTupleOfCellTuple_mem_bounded hubox
        have hvbox :
            v ∈ rdec_boundedTuples M ((2 * n - 1) + 1) :=
          normalizePairingTuple_mem_bounded hurbox
        have hcompare :
            reductionWeight (2 * n - 1) ur ≤
              A * reductionWeight (2 * n - 1) v := by
          exact reductionWeight_le_windingBoxAmplification_mul
            hurbox hvbox
        have hvsum :
            reductionWeight (2 * n - 1) v ≤ S := by
          exact normalized_reductionWeight_le_primitiveAcrossLatticeSum
            hfull hprimitive hurbox
        exact hcompare.trans
          (mul_le_mul_of_nonneg_left hvsum
            (windingBoxAmplification_nonneg M (2 * n - 1)))
    _ = ((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
          A * S := by
      simp
      ring
    _ = _ := rfl

/-- Final direct ENNReal bridge for every member of
`primitiveFullPairings`: the unwrapped R-51 sum is controlled by the
existing primitive across lattice sum, with every loss explicit. -/
theorem primitiveUnwrappedReductionCellSum_le_primitiveAcross
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (hκ : κ ∈ primitiveFullPairings n) :
    ∃ M : ℕ,
      primitiveUnwrappedReductionCellSum ε n hn κ ≤
        ENNReal.ofReal
          (((primitiveCanonicalCellCarrier ε n κ).card : ℝ) *
            windingBoxBase M ^ (2 * n) *
            primitiveAcrossLatticeSum M (2 * n - 1)
              (pairingLowerHalf
                (primitiveReductionPairing n hn κ))) := by
  obtain ⟨hfull, hprimitive⟩ :=
    mem_primitiveFullPairings.mp hκ
  obtain ⟨M, hM⟩ :=
    exists_primitiveUnwrappedReductionCellRealSum_le_primitiveAcross
      ε n hn κ hfull hprimitive
  refine ⟨M, ?_⟩
  rw [primitiveUnwrappedReductionCellSum_eq_ofReal_realSum]
  apply ENNReal.ofReal_le_ofReal
  rw [windingBoxAmplification_eq_pow] at hM
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)] using hM

end

end Anderson4D
