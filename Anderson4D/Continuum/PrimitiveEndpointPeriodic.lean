import Anderson4D.Continuum.PeriodicQuotient
import Anderson4D.Continuum.PrimitiveEndpointFinal

/-!
# Endpoint-preserving periodic reduction

This file joins the periodic cut average from `PeriodicQuotient` to the
endpoint-preserving primitive lattice estimate.  The primitive pairings are
aggregated by their lower-half cut *before* the finite cut lift is enlarged
to a complete lattice box.  This ordering is essential: enlarging one fixed
pairing to the complete across-pairing sum and only then summing the source
pairings would introduce an extra factorial multiplicity.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

/-! ## Endpoint-supported lattice statistics -/

/-- The common, pairing-independent canonical torus-grid carrier. -/
def primitiveCanonicalGrid (ε : ℝ) (n : ℕ) :
    Finset (Fin (2 * n) → Z4) :=
  Fintype.piFinset fun _ : Fin (2 * n) =>
    torusGrid (compatibleMeshSize ε)

/-- Endpoint support transported to an arbitrary lattice lift. -/
def primitiveEndpointSupport
    {n : ℕ} (hn : 1 ≤ n) (δ R : ℝ) (z w : T4)
    (y : Fin (2 * n) → Z4) : Prop :=
  z ∈ latticeCellNeighborhood δ R
      (y (primitiveEndpointLeft n hn)) ∧
    w ∈ latticeCellNeighborhood δ R
      (y (primitiveEndpointRight n hn))

noncomputable instance primitiveEndpointSupport_decidable
    {n : ℕ} (hn : 1 ≤ n) (δ R : ℝ) (z w : T4)
    (y : Fin (2 * n) → Z4) :
    Decidable (primitiveEndpointSupport hn δ R z w y) :=
  Classical.propDecidable _

@[simp]
theorem primitiveCanonicalEndpointSupported_iff_endpointSupport
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z w : T4) (y : Fin (2 * n) → Z4) :
    primitiveCanonicalEndpointSupported ρ ε n hn z w y ↔
      primitiveEndpointSupport hn (compatibleMeshSize ε)
        (1 + 4 * ρ.radius) z w y := by
  rfl

/-- Sum of all compatible primitive across pairings on one lattice tuple,
with the two continuum endpoints kept in their cell neighbourhoods. -/
def primitiveEndpointSupportedStatistic
    {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (δ R : ℝ) (z w : T4)
    (y : Fin (2 * n) → Z4) : ℝ :=
  if primitiveEndpointSupport hn δ R z w y then
    ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
      primitiveDirectReductionWeight hn y
  else 0

theorem primitiveEndpointSupportedStatistic_nonneg
    {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (δ R : ℝ) (z w : T4)
    (y : Fin (2 * n) → Z4) :
    0 ≤ primitiveEndpointSupportedStatistic hn A δ R z w y := by
  unfold primitiveEndpointSupportedStatistic
  split
  · exact mul_nonneg (Nat.cast_nonneg _)
      (primitiveDirectReductionWeight_nonneg hn y)
  · exact le_rfl

/-- Endpoint-supported version of the lattice sum in paper (5.5). -/
def primitiveEndpointSupportedLatticeSum
    (M n : ℕ) (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (δ R : ℝ) (z w : T4) : ℝ :=
  latticeChainSum M (2 * n)
    (primitiveEndpointSupportedStatistic hn A δ R z w)

/-! ## Elementary transport through one periodic cut -/

theorem r51LatticeReductionWeight_eq_primitiveDirect
    {n : ℕ} (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    r51LatticeReductionWeight (by omega) y =
      primitiveDirectReductionWeight hn y := by
  rfl

theorem primitiveEndpointSupport_r51CutLift_iff
    {n q : ℕ} [NeZero q] (hn : 1 ≤ n)
    {δ R : ℝ} (hq : PeriodCompatibleMesh δ (q : ℤ))
    (c : R51Cut q) (z w : T4)
    (y : Fin (2 * n) → Z4) :
    primitiveEndpointSupport hn δ R z w
        (fun j => r51CutLift q c (y j)) ↔
      primitiveEndpointSupport hn δ R z w y := by
  unfold primitiveEndpointSupport latticeCellNeighborhood
  rw [latticeTorusCenter_r51CutLift hq,
    latticeTorusCenter_r51CutLift hq]

theorem RespectsWord.r51CutLift
    {m q : ℕ} [NeZero q]
    {A : Finset (Fin m)} {κ : AcrossPairing A}
    {y : Fin m → Z4} (hy : RespectsWord A y κ)
    (c : R51Cut q) :
    RespectsWord A (fun j => r51CutLift q c (y j)) κ := by
  intro j
  exact congrArg (fun a => Anderson4D.r51CutLift q c a) (hy j)

theorem primitiveCompatibleAcrossPairings_card_le_cutLift
    {m q : ℕ} [NeZero q]
    (A : Finset (Fin m)) (y : Fin m → Z4)
    (c : R51Cut q) :
    (primitiveCompatibleAcrossPairings A y).card ≤
      (primitiveCompatibleAcrossPairings A
        (fun j => r51CutLift q c (y j))).card := by
  apply Finset.card_le_card
  intro κ hκ
  have hk :=
    mem_primitiveCompatibleAcrossPairings.mp hκ
  exact mem_primitiveCompatibleAcrossPairings.mpr
    ⟨hk.1.r51CutLift c, hk.2⟩

theorem primitiveCanonicalGrid_coord_abs_le_cellCount
    {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalGrid ε n) :
    ∀ j i, |y j i| ≤ compatibleCellCount ε := by
  intro j i
  have hyj :
      y j ∈ torusGrid (compatibleMeshSize ε) := by
    exact (Fintype.mem_piFinset.mp hy) j
  exact
    (mem_torusGrid_compatible_abs_le hε hyj i).trans
      (by
        rw [primitiveCopiedBoxRadius_cast hε]
        exact compatible_torusGridRadius_le_cellCount hε)

/-! ## Aggregate primitive pairings before the box enlargement -/

/-- Literal fixed-cut source sum, retaining the endpoint filter. -/
def primitiveCutEndpointPairingSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    {q : ℕ} [NeZero q] (c : R51Cut q)
    (δ R : ℝ) (z w : T4) : ℝ :=
  ∑ κ ∈ primitiveFullPairings n,
    ∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
        (primitiveEndpointSupport hn δ R z w),
      r51LatticeReductionWeight (by omega)
        (fun j => r51CutLift q c (y j))

/-- For one cut and one lower-half set, the sum over primitive across
pairings is bounded by the endpoint-supported statistic of the lifted
tuple.  Primitivity is retained and no complete-pairing enlargement is
performed here. -/
theorem sum_primitiveAcross_cutLift_le_supportedGrid
    {ε : ℝ}
    {n q : ℕ} [NeZero q] (hn : 1 ≤ n)
    {δ R : ℝ} (hq : PeriodCompatibleMesh δ (q : ℤ))
    (c : R51Cut q) (A : Finset (Fin (2 * n)))
    (z w : T4) :
    (∑ κ ∈ primitiveAcrossPairingFinset A,
        ∑ y ∈
            (primitiveCanonicalCellCarrier ε n
              (acrossToPartialPairing A κ)).filter
              (primitiveEndpointSupport hn δ R z w),
          r51LatticeReductionWeight (by omega)
            (fun j => r51CutLift q c (y j))) ≤
      ∑ y ∈ primitiveCanonicalGrid ε n,
        primitiveEndpointSupportedStatistic hn A δ R z w
          (fun j => r51CutLift q c (y j)) := by
  classical
  simp_rw [primitiveCanonicalCellCarrier, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro y hygrid
  by_cases hs : primitiveEndpointSupport hn δ R z w y
  · have hslift :
        primitiveEndpointSupport hn δ R z w
          (fun j => r51CutLift q c (y j)) :=
        (primitiveEndpointSupport_r51CutLift_iff
          hn hq c z w y).2 hs
    let P : Finset (AcrossPairing A) :=
      (primitiveAcrossPairingFinset A).filter
        fun κ => RespectsWord A y κ
    have hP :
        P = primitiveCompatibleAcrossPairings A y := by
      ext κ
      simp only [P, Finset.mem_filter,
        mem_primitiveAcrossPairingFinset,
        mem_primitiveCompatibleAcrossPairings]
      aesop
    have hweight :
        0 ≤ r51LatticeReductionWeight (by omega)
          (fun j => r51CutLift q c (y j)) :=
      (r51LatticeReductionWeight_pos (by omega) _).le
    calc
      (∑ κ ∈ primitiveAcrossPairingFinset A,
          if RespectsPairing (acrossToPartialPairing A κ) y then
            if primitiveEndpointSupport hn δ R z w y then
              r51LatticeReductionWeight (by omega)
                (fun j => r51CutLift q c (y j))
            else 0
          else 0) =
          ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            r51LatticeReductionWeight (by omega)
              (fun j => r51CutLift q c (y j)) := by
        rw [← hP]
        simp only [hs, ↓reduceIte,
          respectsPairing_acrossToPartialPairing_iff]
        rw [← Finset.sum_filter]
        simp [P]
      _ ≤
          ((primitiveCompatibleAcrossPairings A
            (fun j => r51CutLift q c (y j))).card : ℝ) *
              r51LatticeReductionWeight (by omega)
                (fun j => r51CutLift q c (y j)) := by
        apply mul_le_mul_of_nonneg_right _ hweight
        exact_mod_cast
          primitiveCompatibleAcrossPairings_card_le_cutLift A y c
      _ =
          primitiveEndpointSupportedStatistic hn A δ R z w
            (fun j => r51CutLift q c (y j)) := by
        rw [primitiveEndpointSupportedStatistic, if_pos hslift,
          r51LatticeReductionWeight_eq_primitiveDirect hn]
  · have hslift :
        ¬primitiveEndpointSupport hn δ R z w
          (fun j => r51CutLift q c (y j)) := by
        simpa only [primitiveEndpointSupport_r51CutLift_iff
          hn hq c z w y] using hs
    simp [hs, primitiveEndpointSupportedStatistic, hslift]

/-- Correct fixed-cut bridge.  The source primitive pairings first inject
into the all-cuts across carrier.  Only after this aggregation is the cut
lift enlarged to the common `[-2q,2q]` lattice box, incurring the uniform
`3^(8n)` fiber loss exactly once. -/
theorem primitiveCutEndpointPairingSum_le_supportedLattice
    {ε : ℝ} (hε : 0 < ε)
    {n q : ℕ} [NeZero q] (hn : 1 ≤ n)
    (hqε : (q : ℤ) = compatibleCellCount ε)
    {δ R : ℝ} (hq : PeriodCompatibleMesh δ (q : ℤ))
    (c : R51Cut q) (z w : T4) :
    primitiveCutEndpointPairingSum ε n hn c δ R z w ≤
      (((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
        ∑ A : Finset (Fin (2 * n)),
          primitiveEndpointSupportedLatticeSum
            (2 * q) n hn A δ R z w := by
  classical
  let Grid := primitiveCanonicalGrid ε n
  let B := rdec_boundedTuples (2 * q) (2 * n)
  let F :=
    fun A : Finset (Fin (2 * n)) =>
      fun u : Fin (2 * n) → Z4 =>
        primitiveEndpointSupportedStatistic hn A δ R z w u
  have hpair :
      primitiveCutEndpointPairingSum ε n hn c δ R z w ≤
        ∑ A : Finset (Fin (2 * n)),
          ∑ y ∈ Grid, F A (fun j => r51CutLift q c (y j)) := by
    let W : PartialPairing (Fin (2 * n)) → ℝ := fun κ =>
      ∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
          (primitiveEndpointSupport hn δ R z w),
        r51LatticeReductionWeight (by omega)
          (fun j => r51CutLift q c (y j))
    have hW : ∀ κ, 0 ≤ W κ := by
      intro κ
      unfold W
      apply Finset.sum_nonneg
      intro y hy
      exact (r51LatticeReductionWeight_pos (by omega) _).le
    have hall := sum_primitiveFullPairings_le_sum_across W hW
    have hall' :
        (∑ κ ∈ primitiveFullPairings n, W κ) ≤
          ∑ A : Finset (Fin (2 * n)),
            ∑ κ ∈ primitiveAcrossPairingFinset A,
              W (acrossToPartialPairing A κ) := by
      simpa only [primitiveFullPairings] using hall
    unfold primitiveCutEndpointPairingSum
    change
      (∑ κ ∈ primitiveFullPairings n, W κ) ≤ _
    refine hall'.trans ?_
    apply Finset.sum_le_sum
    intro A hA
    simpa only [Grid, F] using
      sum_primitiveAcross_cutLift_le_supportedGrid
        hn hq c A z w
  have hbox :
      ∀ y ∈ Grid, ∀ j i, |y j i| ≤ (q : ℤ) := by
    intro y hy j i
    rw [hqε]
    exact_mod_cast
      primitiveCanonicalGrid_coord_abs_le_cellCount hε hy j i
  have hmap :
      ∀ y ∈ Grid,
        (fun j => r51CutLift q c (y j)) ∈ B := by
    intro y hy
    exact r51CutLift_tuple_mem_bounded c y
  calc
    primitiveCutEndpointPairingSum ε n hn c δ R z w ≤
        ∑ A : Finset (Fin (2 * n)),
          ∑ y ∈ Grid, F A (fun j => r51CutLift q c (y j)) :=
      hpair
    _ ≤ ∑ A : Finset (Fin (2 * n)),
        (((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
          ∑ u ∈ B, F A u := by
      apply Finset.sum_le_sum
      intro A hA
      exact r51_sum_cutLift_le_box_sum
        c Grid hbox B hmap (F A)
          (primitiveEndpointSupportedStatistic_nonneg
            hn A δ R z w)
    _ = (((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
        ∑ A : Finset (Fin (2 * n)),
          primitiveEndpointSupportedLatticeSum
            (2 * q) n hn A δ R z w := by
      simp only [Finset.mul_sum, B, F,
        primitiveEndpointSupportedLatticeSum, latticeChainSum]

/-! ## The cut average after summing all primitive pairings -/

/-- Periodic endpoint-filtered reduction sum over the complete primitive
pairing carrier. -/
def primitivePeriodicEndpointPairingSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (δ R : ℝ) (z w : T4) : ℝ :=
  ∑ κ ∈ primitiveFullPairings n,
    ∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
        (primitiveEndpointSupport hn δ R z w),
      r51PeriodicReductionWeight q (by omega) δ y

/-- The endpoint-filtered reduction statistic from `PeriodicQuotient`,
summed over primitive pairings, is exactly the real periodic endpoint sum
used below. -/
theorem sum_r51PeriodicReductionFilteredRealSum_endpoint_eq
    {ε : ℝ} (hε : 0 < ε)
    (ρ : SmoothCutoff) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (z w : T4) :
    (∑ κ ∈ primitiveFullPairings n,
        r51PeriodicReductionFilteredRealSum
          ε n hn q (compatibleMeshSize ε) κ
            (primitiveCopiedEndpointSupported
              ρ ε n hn z w)) =
      primitivePeriodicEndpointPairingSum
        ε n hn q (compatibleMeshSize ε)
          (1 + 4 * ρ.radius) z w := by
  classical
  unfold primitivePeriodicEndpointPairingSum
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [r51PeriodicReductionFilteredRealSum_eq_copied
    hε n hn q (compatibleMeshSize ε) κ
      (primitiveCopiedEndpointSupported ρ ε n hn z w)]
  congr 1

theorem r51PeriodicReductionFilteredRealSum_nonneg
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P] :
    0 ≤
      r51PeriodicReductionFilteredRealSum
        ε n hn q δ κ P := by
  unfold r51PeriodicReductionFilteredRealSum
  apply Finset.sum_nonneg
  intro u hu
  exact (r51PeriodicReductionWeight_pos (by omega) hδ _).le

/-- `ENNReal` form of
`sum_r51PeriodicReductionFilteredRealSum_endpoint_eq`, suited to the
Tonelli bound for the primitive kernel. -/
theorem sum_r51PeriodicReductionFilteredSum_endpoint_eq
    {ε : ℝ} (hε : 0 < ε)
    (ρ : SmoothCutoff) (n : ℕ) (hn : 1 ≤ n)
    (q : ℕ) (z w : T4) :
    (∑ κ ∈ primitiveFullPairings n,
        r51PeriodicReductionFilteredSum
          ε n hn q (compatibleMeshSize ε) κ
            (primitiveCopiedEndpointSupported
              ρ ε n hn z w)) =
      ENNReal.ofReal
        (primitivePeriodicEndpointPairingSum
          ε n hn q (compatibleMeshSize ε)
            (1 + 4 * ρ.radius) z w) := by
  classical
  simp_rw [r51PeriodicReductionFilteredSum_eq_ofReal
    ε n hn q (compatibleMeshSize_pos hε)]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [sum_r51PeriodicReductionFilteredRealSum_endpoint_eq
      hε ρ n hn q z w]
  · intro κ hκ
    exact
      r51PeriodicReductionFilteredRealSum_nonneg
        ε n hn q (compatibleMeshSize_pos hε) κ
          (primitiveCopiedEndpointSupported ρ ε n hn z w)

/-- The arithmetic-geometric cut average commutes with the complete
primitive-pairing sum. -/
theorem primitivePeriodicEndpointPairingSum_le_cutAverage
    {ε δ : ℝ} (hδ : 0 < δ)
    {n q : ℕ} [NeZero q] (hn : 1 ≤ n)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (R : ℝ) (z w : T4) :
    primitivePeriodicEndpointPairingSum
        ε n hn q δ R z w ≤
      Real.exp (12 * (2 * n - 1)) *
        ((∑ c : R51Cut q,
            primitiveCutEndpointPairingSum
              ε n hn c δ R z w) / (q : ℝ) ^ 4) := by
  classical
  let E : ℝ := Real.exp (12 * (2 * n - 1))
  let K := primitiveFullPairings n
  let S := fun κ : PartialPairing (Fin (2 * n)) =>
    (primitiveCanonicalCellCarrier ε n κ).filter
      (primitiveEndpointSupport hn δ R z w)
  let W := fun (c : R51Cut q) (y : Fin (2 * n) → Z4) =>
    r51LatticeReductionWeight (by omega)
      (fun j => r51CutLift q c (y j))
  have hpoint :
      ∀ y : Fin (2 * n) → Z4,
        r51PeriodicReductionWeight q (by omega) δ y ≤
          E * ((∑ c : R51Cut q, W c y) / (q : ℝ) ^ 4) := by
    intro y
    simpa only [E, W, Nat.cast_sub (by omega : 1 ≤ 2 * n),
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      r51PeriodicReductionWeight_le_cutAverage
        (by omega) hδ hq y
  have htriple :
      (∑ κ ∈ K, ∑ y ∈ S κ, ∑ c : R51Cut q, W c y) =
        ∑ c : R51Cut q, ∑ κ ∈ K, ∑ y ∈ S κ, W c y := by
    calc
      (∑ κ ∈ K, ∑ y ∈ S κ, ∑ c : R51Cut q, W c y) =
          ∑ κ ∈ K, ∑ c : R51Cut q, ∑ y ∈ S κ, W c y := by
        apply Finset.sum_congr rfl
        intro κ hκ
        rw [Finset.sum_comm]
      _ = ∑ c : R51Cut q, ∑ κ ∈ K, ∑ y ∈ S κ, W c y := by
        rw [Finset.sum_comm]
  calc
    primitivePeriodicEndpointPairingSum
        ε n hn q δ R z w =
        ∑ κ ∈ K, ∑ y ∈ S κ,
          r51PeriodicReductionWeight q (by omega) δ y := by
      rfl
    _ ≤ ∑ κ ∈ K, ∑ y ∈ S κ,
        E * ((∑ c : R51Cut q, W c y) / (q : ℝ) ^ 4) := by
      apply Finset.sum_le_sum
      intro κ hκ
      apply Finset.sum_le_sum
      intro y hy
      exact hpoint y
    _ = E *
        ((∑ κ ∈ K, ∑ y ∈ S κ,
            ∑ c : R51Cut q, W c y) / (q : ℝ) ^ 4) := by
      simp_rw [Finset.sum_div, Finset.mul_sum]
    _ = E *
        ((∑ c : R51Cut q, ∑ κ ∈ K,
            ∑ y ∈ S κ, W c y) / (q : ℝ) ^ 4) := by
      rw [htriple]
    _ = Real.exp (12 * (2 * n - 1)) *
        ((∑ c : R51Cut q,
            primitiveCutEndpointPairingSum
              ε n hn c δ R z w) / (q : ℝ) ^ 4) := by
      rfl

/-- The cut count cancels the averaging denominator after the fixed-cut
endpoint-preserving lattice bridge. -/
theorem primitivePeriodicEndpointPairingSum_le_supportedLattice
    {ε : ℝ} (hε : 0 < ε)
    {n q : ℕ} [NeZero q] (hn : 1 ≤ n)
    (hqε : (q : ℤ) = compatibleCellCount ε)
    {δ : ℝ} (hδ : 0 < δ)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (R : ℝ) (z w : T4) :
    primitivePeriodicEndpointPairingSum
        ε n hn q δ R z w ≤
      Real.exp (12 * (2 * n - 1)) *
        ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
          ∑ A : Finset (Fin (2 * n)),
            primitiveEndpointSupportedLatticeSum
              (2 * q) n hn A δ R z w) := by
  let E : ℝ := Real.exp (12 * (2 * n - 1))
  let L : ℝ :=
    (((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
      ∑ A : Finset (Fin (2 * n)),
        primitiveEndpointSupportedLatticeSum
          (2 * q) n hn A δ R z w
  have haverage :
      primitivePeriodicEndpointPairingSum
          ε n hn q δ R z w ≤
        E * ((∑ c : R51Cut q,
          primitiveCutEndpointPairingSum
            ε n hn c δ R z w) / (q : ℝ) ^ 4) := by
    simpa only [E] using
      primitivePeriodicEndpointPairingSum_le_cutAverage
        (ε := ε) hδ hn hq R z w
  have hcut :
      (∑ c : R51Cut q,
          primitiveCutEndpointPairingSum ε n hn c δ R z w) ≤
        (q : ℝ) ^ 4 * L := by
    calc
      (∑ c : R51Cut q,
          primitiveCutEndpointPairingSum ε n hn c δ R z w) ≤
          ∑ _c : R51Cut q, L := by
        apply Finset.sum_le_sum
        intro c hc
        exact
          primitiveCutEndpointPairingSum_le_supportedLattice
            hε hn hqε hq c z w
      _ = (q : ℝ) ^ 4 * L := by
        have hcard : Fintype.card (R51Cut q) = q ^ 4 := by
          rw [Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin]
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_univ, hcard]
        push_cast
        rfl
  have hnorm :
      ((∑ c : R51Cut q,
          primitiveCutEndpointPairingSum ε n hn c δ R z w) /
          (q : ℝ) ^ 4) ≤ L := by
    have hqR : (0 : ℝ) < q := by
      exact_mod_cast NeZero.pos q
    apply (div_le_iff₀ (pow_pos hqR 4)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcut
  simpa only [E, L] using
    haverage.trans
      (mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le)

/-! ## Regroup the supported lattice sum by its two endpoints -/

/-- Endpoint pairs which actually occur in the finite lattice box. -/
def primitiveEndpointPairCarrier
    (M n : ℕ) (hn : 1 ≤ n) : Finset (Z4 × Z4) :=
  (rdec_boundedTuples M (2 * n)).image fun y =>
    (y (primitiveEndpointLeft n hn),
      y (primitiveEndpointRight n hn))

/-- Continuum endpoint support written directly on a pair of lattice
labels. -/
def primitiveEndpointPairSupported
    (δ R : ℝ) (z w : T4) (p : Z4 × Z4) : Prop :=
  z ∈ latticeCellNeighborhood δ R p.1 ∧
    w ∈ latticeCellNeighborhood δ R p.2

noncomputable instance primitiveEndpointPairSupported_decidable
    (δ R : ℝ) (z w : T4) (p : Z4 × Z4) :
    Decidable (primitiveEndpointPairSupported δ R z w p) :=
  Classical.propDecidable _

/-- The geometric endpoint bracket left after the combinatorial sum. -/
def primitiveEndpointBracketSum
    (M n : ℕ) (hn : 1 ≤ n)
    (δ R : ℝ) (z w : T4) : ℝ :=
  ∑ p ∈ (primitiveEndpointPairCarrier M n hn).filter
      (primitiveEndpointPairSupported δ R z w),
    latticeBracketInvFourth p.1 p.2

theorem primitiveEndpointBracketSum_nonneg
    (M n : ℕ) (hn : 1 ≤ n)
    (δ R : ℝ) (z w : T4) :
    0 ≤ primitiveEndpointBracketSum M n hn δ R z w := by
  unfold primitiveEndpointBracketSum
  apply Finset.sum_nonneg
  intro p hp
  exact latticeBracketInvFourth_nonneg p.1 p.2

theorem primitiveEndpointPairSupported_bracket_le
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    {z w : T4} {p : Z4 × Z4}
    (hp : primitiveEndpointPairSupported δ R z w p) :
    latticeBracketInvFourth p.1 p.2 ≤
      (9 * (1 + 4 * R ^ 2)) ^ 2 * δ ^ 4 *
        (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2 := by
  let d : ℝ := znorm (p.1 - p.2)
  let B : ℝ := 1 + d ^ 2
  let T : ℝ := torusDistSq (z - w) + δ ^ 2
  let A : ℝ := 9 * (1 + 4 * R ^ 2) * δ ^ 2
  have hd0 : 0 ≤ d := znorm_nonneg _
  have hB : 0 < B := by
    dsimp only [B]
    nlinarith [sq_nonneg d]
  have hT : 0 < T := by
    dsimp only [T]
    have htorus0 := torusDistSq_nonneg (z - w)
    nlinarith [sq_pos_of_pos hδ]
  have hcenters :
      dist (latticeTorusCenter δ p.1)
          (latticeTorusCenter δ p.2) ≤ δ * d := by
    simpa only [d] using
      dist_latticeTorusCenter_le hδ.le p.1 p.2
  have hdist :
      dist z w ≤ δ * (2 * R + d) := by
    calc
      dist z w ≤
          dist z (latticeTorusCenter δ p.1) +
            dist (latticeTorusCenter δ p.1)
              (latticeTorusCenter δ p.2) +
            dist (latticeTorusCenter δ p.2) w :=
        dist_triangle4 _ _ _ _
      _ ≤ R * δ + δ * d + R * δ := by
        apply add_le_add
        · exact add_le_add hp.1.le hcenters
        · simpa only [dist_comm] using hp.2.le
      _ = δ * (2 * R + d) := by ring
  have hright0 : 0 ≤ δ * (2 * R + d) := by
    positivity
  have htorus :
      torusDistSq (z - w) ≤
        4 * (δ * (2 * R + d)) ^ 2 := by
    calc
      torusDistSq (z - w) ≤ 4 * ‖z - w‖ ^ 2 :=
        torusDistSq_le_four_mul_sq_norm (z - w)
      _ = 4 * dist z w ^ 2 := by
        rw [dist_eq_norm]
      _ ≤ 4 * (δ * (2 * R + d)) ^ 2 := by
        gcongr
  have hsquare :
      (2 * R + d) ^ 2 ≤
        2 * ((2 * R) ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (2 * R - d)]
  have hprod :
      2 * ((2 * R) ^ 2 + d ^ 2) ≤
        2 * (1 + 4 * R ^ 2) * (1 + d ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg d)]
  have htorus' :
      torusDistSq (z - w) ≤
        8 * δ ^ 2 * (1 + 4 * R ^ 2) * B := by
    calc
      torusDistSq (z - w) ≤
          4 * (δ * (2 * R + d)) ^ 2 := htorus
      _ = 4 * δ ^ 2 * (2 * R + d) ^ 2 := by ring
      _ ≤ 4 * δ ^ 2 *
          (2 * ((2 * R) ^ 2 + d ^ 2)) := by
        gcongr
      _ ≤ 4 * δ ^ 2 *
          (2 * (1 + 4 * R ^ 2) * (1 + d ^ 2)) := by
        gcongr
      _ = 8 * δ ^ 2 * (1 + 4 * R ^ 2) * B := by
        dsimp only [B]
        ring
  have hTB : T ≤ A * B := by
    have hfac : 1 ≤ 1 + 4 * R ^ 2 := by
      nlinarith [sq_nonneg R]
    have hBone : 1 ≤ B := by
      dsimp only [B]
      nlinarith [sq_nonneg d]
    have hδle :
        δ ^ 2 ≤ δ ^ 2 * (1 + 4 * R ^ 2) * B := by
      calc
        δ ^ 2 = δ ^ 2 * 1 * 1 := by ring
        _ ≤ δ ^ 2 * (1 + 4 * R ^ 2) * B := by
          gcongr
    calc
      T ≤ 8 * δ ^ 2 * (1 + 4 * R ^ 2) * B +
          δ ^ 2 := by
        dsimp only [T]
        exact add_le_add htorus' (le_refl _)
      _ ≤ 8 * δ ^ 2 * (1 + 4 * R ^ 2) * B +
          δ ^ 2 * (1 + 4 * R ^ 2) * B :=
        add_le_add (le_refl _) hδle
      _ = A * B := by
        dsimp only [A]
        ring
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hinv : B⁻¹ ≤ A * T⁻¹ := by
    have hdiv : T / B ≤ A :=
      (div_le_iff₀ hB).2 (by
        simpa only [mul_comm] using hTB)
    apply (le_div_iff₀ hT).2
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using hdiv
  have hinvSq :
      B⁻¹ ^ 2 ≤ (A * T⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hB.le) hinv 2
  unfold latticeBracketInvFourth
  calc
    ((1 + znorm (p.1 - p.2) ^ 2) ^ 2)⁻¹ =
        B⁻¹ ^ 2 := by
      rw [inv_pow]
    _ ≤ (A * T⁻¹) ^ 2 := hinvSq
    _ = (9 * (1 + 4 * R ^ 2)) ^ 2 * δ ^ 4 *
        (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2 := by
      dsimp only [A, T]
      ring

/-! ## Uniformly many endpoint labels on one periodic mesh -/

theorem torusGridRadius_le_periodCount
    {δ : ℝ} {q : ℕ} [NeZero q]
    (hq : PeriodCompatibleMesh δ (q : ℤ)) :
    torusGridRadius δ ≤ (q : ℤ) := by
  unfold torusGridRadius
  apply Int.ceil_le.mpr
  have hqR : (0 : ℝ) < ((q : ℤ) : ℝ) := by
    exact_mod_cast hq.cellCount_pos
  have hδ : 0 < δ := by
    nlinarith [hq.period_eq, Real.pi_pos]
  apply (div_le_iff₀ hδ).2
  nlinarith [hq.period_eq, Real.pi_pos]

theorem torusFloorCell_coord_abs_le_periodCount
    {δ : ℝ} {q : ℕ} [NeZero q]
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (z : T4) (i : Fin 4) :
    |torusFloorCell δ z i| ≤ (q : ℤ) := by
  have hδ : 0 < δ := by
    have hqR : (0 : ℝ) < ((q : ℤ) : ℝ) := by
      exact_mod_cast hq.cellCount_pos
    nlinarith [hq.period_eq, Real.pi_pos]
  have hz := torusFloorCell_mem_torusGrid hδ z
  unfold torusGrid at hz
  rw [Fintype.mem_piFinset] at hz
  have hi := Finset.mem_Icc.mp (hz i)
  rw [abs_le]
  constructor
  · exact
      (neg_le_neg (torusGridRadius_le_periodCount hq)).trans hi.1
  · exact hi.2.trans (torusGridRadius_le_periodCount hq)

theorem torus_mem_latticeCellNeighborhood_floor
    {δ : ℝ} (hδ : 0 < δ) (z : T4) :
    z ∈ latticeCellNeighborhood δ 1 (torusFloorCell δ z) := by
  have hnear :
      ‖torusLift z -
          cellRepresentative δ (torusFloorCell δ z)‖ < δ := by
    exact norm_sub_cellRepresentative_lt hδ (torusLift z)
  unfold latticeCellNeighborhood latticeTorusCenter
  rw [Metric.mem_ball]
  calc
    dist z
        (periodizeR4
          (cellRepresentative δ (torusFloorCell δ z))) =
        dist (periodizeR4 (torusLift z))
          (periodizeR4
            (cellRepresentative δ (torusFloorCell δ z))) := by
      rw [periodizeR4_torusLift]
    _ ≤ ‖torusLift z -
          cellRepresentative δ (torusFloorCell δ z)‖ :=
      dist_periodizeR4_le_norm_sub _ _
    _ < 1 * δ := by simpa using hnear

/-- Period-translation code used by `nearestPeriodTranslate`. -/
def primitiveEndpointPeriodCode
    (q : ℕ) (x a : Z4) : Z4 :=
  fun i => round ((((x - a) i : ℤ) : ℝ) / (q : ℝ))

theorem primitiveEndpointPeriodCode_mem_ball_four
    {q : ℕ} [NeZero q] {x a : Z4}
    (hx : ∀ i, |x i| ≤ (2 * q : ℕ))
    (ha : ∀ i, |a i| ≤ (q : ℤ)) :
    primitiveEndpointPeriodCode q x a ∈
      latticeBallNat 0 4 := by
  rw [mem_latticeBallNat]
  have hnorm :
      znorm (primitiveEndpointPeriodCode q x a) ≤ 4 := by
    rw [znorm, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    have hxZ : |x i| ≤ (2 * q : ℤ) := by
      exact_mod_cast hx i
    have haZ := ha i
    have hdiffZ : |x i - a i| ≤ (3 * q : ℕ) := by
      rw [abs_le] at hxZ haZ ⊢
      constructor <;> omega
    have hdiffR :
        |(((x - a) i : ℤ) : ℝ)| ≤ 3 * (q : ℝ) := by
      simpa only [Pi.sub_apply] using
        (show
          |((x i - a i : ℤ) : ℝ)| ≤ 3 * (q : ℝ) by
            exact_mod_cast hdiffZ)
    have hqR : (0 : ℝ) < q := by
      exact_mod_cast NeZero.pos q
    let r : ℝ := (((x - a) i : ℤ) : ℝ) / (q : ℝ)
    have hr : |r| ≤ 3 := by
      dsimp only [r]
      rw [abs_div, abs_of_pos hqR]
      exact (div_le_iff₀ hqR).2 (by simpa using hdiffR)
    have herr : |r - (round r : ℤ)| ≤ (1 : ℝ) / 2 :=
      abs_sub_round r
    have hround :
        |(((round r : ℤ) : ℝ))| ≤ 4 := by
      calc
        |(((round r : ℤ) : ℝ))| =
            |r - (r - ((round r : ℤ) : ℝ))| := by ring_nf
        _ ≤ |r| + |r - ((round r : ℤ) : ℝ)| :=
          by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le r 0 (r - ((round r : ℤ) : ℝ))
        _ ≤ 3 + (1 : ℝ) / 2 := add_le_add hr herr
        _ ≤ 4 := by norm_num
    simpa only [primitiveEndpointPeriodCode,
      Real.norm_eq_abs] using hround
  simpa using hnorm

/-- The bounded set of period translates which can be nearest to a point
of `[-2q,2q]⁴` when the canonical anchor lies in `[-q,q]⁴`. -/
def primitiveEndpointPeriodCenters
    (q : ℕ) (δ : ℝ) (z : T4) : Finset Z4 :=
  (latticeBallNat (0 : Z4) 4).image fun k =>
    translateCellIndex (q : ℤ) k (torusFloorCell δ z)

theorem card_primitiveEndpointPeriodCenters_le
    (q : ℕ) (δ : ℝ) (z : T4) :
    (primitiveEndpointPeriodCenters q δ z).card ≤ 10000 := by
  calc
    (primitiveEndpointPeriodCenters q δ z).card ≤
        (latticeBallNat (0 : Z4) 4).card := by
      unfold primitiveEndpointPeriodCenters
      exact Finset.card_image_le
    _ ≤ 16 * (4 + 1) ^ 4 :=
      card_latticeBallNat_le 0 4
    _ = 10000 := by norm_num

/-- Uniform endpoint-label cover; the radius is the support radius plus
the one-cell error of the canonical floor anchor. -/
def primitiveEndpointLabelCover
    (q : ℕ) (δ R : ℝ) (z : T4) : Finset Z4 :=
  latticeBallUnion
    (primitiveEndpointPeriodCenters q δ z) (R + 1)

theorem mem_primitiveEndpointLabelCover
    {q : ℕ} [NeZero q]
    {δ R : ℝ}
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    {z : T4} {x : Z4}
    (hxbox : ∀ i, |x i| ≤ (2 * q : ℕ))
    (hx : z ∈ latticeCellNeighborhood δ R x) :
    x ∈ primitiveEndpointLabelCover q δ R z := by
  let a := torusFloorCell δ z
  let k := primitiveEndpointPeriodCode q x a
  let x' := translateCellIndex (q : ℤ) k a
  have hδ : 0 < δ := by
    have hqR : (0 : ℝ) < ((q : ℤ) : ℝ) := by
      exact_mod_cast hq.cellCount_pos
    nlinarith [hq.period_eq, Real.pi_pos]
  have ha : ∀ i, |a i| ≤ (q : ℤ) :=
    fun i => torusFloorCell_coord_abs_le_periodCount hq z i
  have hk : k ∈ latticeBallNat (0 : Z4) 4 :=
    primitiveEndpointPeriodCode_mem_ball_four hxbox ha
  have hx'center :
      latticeTorusCenter δ x' = latticeTorusCenter δ a := by
    dsimp only [x']
    exact latticeTorusCenter_translateCellIndex hq k a
  have hnearest :
      nearestPeriodTranslate (q : ℤ) x a = x' := by
    rfl
  have hdistEq :
      dist (latticeTorusCenter δ x)
          (latticeTorusCenter δ x') =
        δ * znorm (x - x') := by
    rw [← hnearest]
    exact latticeTorusCenter_dist_eq_of_edgeNoWrap hδ
      (nearestPeriodTranslate_edgeNoWrap hq x a)
  have haNear :=
    torus_mem_latticeCellNeighborhood_floor hδ z
  have hxNear :
      dist z (latticeTorusCenter δ x) < R * δ := by
    simpa only [latticeCellNeighborhood, Metric.mem_ball] using hx
  have haNear' :
      dist z (latticeTorusCenter δ a) < 1 * δ := by
    simpa only [latticeCellNeighborhood, Metric.mem_ball, a] using
      haNear
  have hclose :
      dist (latticeTorusCenter δ x)
          (latticeTorusCenter δ x') < (R + 1) * δ := by
    calc
      dist (latticeTorusCenter δ x)
          (latticeTorusCenter δ x') ≤
          dist (latticeTorusCenter δ x) z +
            dist z (latticeTorusCenter δ x') :=
        dist_triangle _ _ _
      _ < R * δ + 1 * δ := by
        apply add_lt_add
        · simpa only [dist_comm] using hxNear
        · simpa only [hx'center] using haNear'
      _ = (R + 1) * δ := by ring
  have hball : znorm (x - x') ≤ R + 1 := by
    rw [hdistEq] at hclose
    have := (lt_of_lt_of_le hclose (le_refl _)).le
    nlinarith
  unfold primitiveEndpointLabelCover
  rw [mem_latticeBallUnion]
  refine ⟨x', ?_, hball⟩
  unfold primitiveEndpointPeriodCenters
  rw [Finset.mem_image]
  exact ⟨k, hk, rfl⟩

theorem card_primitiveEndpointLabelCover_le
    {R : ℝ} (hR : 0 ≤ R)
    (q : ℕ) (δ : ℝ) (z : T4) :
    ((primitiveEndpointLabelCover q δ R z).card : ℝ) ≤
      160000 * (R + 2) ^ 4 := by
  have hcenters :
      ((primitiveEndpointPeriodCenters q δ z).card : ℝ) ≤
        10000 := by
    exact_mod_cast
      card_primitiveEndpointPeriodCenters_le q δ z
  calc
    ((primitiveEndpointLabelCover q δ R z).card : ℝ) ≤
        16 *
          ((primitiveEndpointPeriodCenters q δ z).card : ℝ) *
            (1 + (R + 1)) ^ 4 := by
      exact card_latticeBallUnion_le
        (primitiveEndpointPeriodCenters q δ z) (R + 1)
    _ ≤ 16 * 10000 * (1 + (R + 1)) ^ 4 := by
      gcongr
    _ = 160000 * (R + 2) ^ 4 := by ring

/-- The two endpoint labels range over a uniformly bounded product cover,
independently of the period count. -/
theorem card_primitiveEndpointSupportedPairs_le
    {q n : ℕ} [NeZero q] (hn : 1 ≤ n)
    {δ R : ℝ} (hR : 0 ≤ R)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (z w : T4) :
    (((primitiveEndpointPairCarrier (2 * q) n hn).filter
      (primitiveEndpointPairSupported δ R z w)).card : ℝ) ≤
        (160000 * (R + 2) ^ 4) ^ 2 := by
  let S :=
    (primitiveEndpointPairCarrier (2 * q) n hn).filter
      (primitiveEndpointPairSupported δ R z w)
  let Z := primitiveEndpointLabelCover q δ R z
  let W := primitiveEndpointLabelCover q δ R w
  have hsub : S ⊆ Z ×ˢ W := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨y, hybox, hyp⟩ :=
      Finset.mem_image.mp hp'.1
    have hybound := rdec_mem_boundedTuples.mp hybox
    have hp1box : ∀ i, |p.1 i| ≤ (2 * q : ℕ) := by
      intro i
      rw [← hyp]
      exact_mod_cast hybound (primitiveEndpointLeft n hn) i
    have hp2box : ∀ i, |p.2 i| ≤ (2 * q : ℕ) := by
      intro i
      rw [← hyp]
      exact_mod_cast hybound (primitiveEndpointRight n hn) i
    rw [Finset.mem_product]
    exact
      ⟨mem_primitiveEndpointLabelCover hq hp1box hp'.2.1,
        mem_primitiveEndpointLabelCover hq hp2box hp'.2.2⟩
  have hcard :
      (S.card : ℝ) ≤ ((Z ×ˢ W).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hZ :
      (Z.card : ℝ) ≤ 160000 * (R + 2) ^ 4 :=
    card_primitiveEndpointLabelCover_le hR q δ z
  have hW :
      (W.card : ℝ) ≤ 160000 * (R + 2) ^ 4 :=
    card_primitiveEndpointLabelCover_le hR q δ w
  calc
    (((primitiveEndpointPairCarrier (2 * q) n hn).filter
        (primitiveEndpointPairSupported δ R z w)).card : ℝ) =
        (S.card : ℝ) := by rfl
    _ ≤ ((Z ×ˢ W).card : ℝ) := hcard
    _ = (Z.card : ℝ) * (W.card : ℝ) := by
      rw [Finset.card_product]
      push_cast
      rfl
    _ ≤ (160000 * (R + 2) ^ 4) *
          (160000 * (R + 2) ^ 4) := by
      exact mul_le_mul hZ hW
        (Nat.cast_nonneg _) (by positivity)
    _ = (160000 * (R + 2) ^ 4) ^ 2 := by ring

/-- Final geometric estimate for the endpoint bracket sum. -/
theorem primitiveEndpointBracketSum_le_globalDecay
    {q n : ℕ} [NeZero q] (hn : 1 ≤ n)
    {δ R : ℝ} (hR : 0 ≤ R)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (z w : T4) :
    primitiveEndpointBracketSum
        (2 * q) n hn δ R z w ≤
      (160000 * (R + 2) ^ 4) ^ 2 *
        ((9 * (1 + 4 * R ^ 2)) ^ 2 * δ ^ 4 *
          (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2) := by
  let S :=
    (primitiveEndpointPairCarrier (2 * q) n hn).filter
      (primitiveEndpointPairSupported δ R z w)
  let G :=
    (9 * (1 + 4 * R ^ 2)) ^ 2 * δ ^ 4 *
      (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2
  have hδ : 0 < δ := by
    have hqR : (0 : ℝ) < ((q : ℤ) : ℝ) := by
      exact_mod_cast hq.cellCount_pos
    nlinarith [hq.period_eq, Real.pi_pos]
  have hG : 0 ≤ G := by
    dsimp only [G]
    positivity
  unfold primitiveEndpointBracketSum
  change (∑ p ∈ S, latticeBracketInvFourth p.1 p.2) ≤ _
  calc
    (∑ p ∈ S, latticeBracketInvFourth p.1 p.2) ≤
        ∑ _p ∈ S, G := by
      apply Finset.sum_le_sum
      intro p hp
      exact
        primitiveEndpointPairSupported_bracket_le
          hδ hR (Finset.mem_filter.mp hp).2
    _ = (S.card : ℝ) * G := by simp
    _ ≤ (160000 * (R + 2) ^ 4) ^ 2 * G := by
      apply mul_le_mul_of_nonneg_right _ hG
      exact card_primitiveEndpointSupportedPairs_le
        hn hR hq z w
    _ = _ := by rfl

theorem primitiveEndpointSupport_iff_pairSupported
    {n : ℕ} (hn : 1 ≤ n)
    (δ R : ℝ) (z w : T4)
    (y : Fin (2 * n) → Z4) :
    primitiveEndpointSupport hn δ R z w y ↔
      primitiveEndpointPairSupported δ R z w
        (y (primitiveEndpointLeft n hn),
          y (primitiveEndpointRight n hn)) := by
  rfl

/-- Exact endpoint-fiber decomposition of the supported lattice sum. -/
theorem primitiveEndpointSupportedLatticeSum_eq_endpointPairs
    (M n : ℕ) (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n)))
    (δ R : ℝ) (z w : T4) :
    primitiveEndpointSupportedLatticeSum M n hn A δ R z w =
      ∑ p ∈ primitiveEndpointPairCarrier M n hn,
        if primitiveEndpointPairSupported δ R z w p then
          primitiveEndpointLatticeSum M n hn A p.1 p.2
        else 0 := by
  classical
  let B := rdec_boundedTuples M (2 * n)
  let g : (Fin (2 * n) → Z4) → Z4 × Z4 := fun y =>
    (y (primitiveEndpointLeft n hn),
      y (primitiveEndpointRight n hn))
  let F : (Fin (2 * n) → Z4) → ℝ := fun y =>
    ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
      primitiveDirectReductionWeight hn y
  let H : (Fin (2 * n) → Z4) → ℝ := fun y =>
    if primitiveEndpointSupport hn δ R z w y then F y else 0
  unfold primitiveEndpointSupportedLatticeSum latticeChainSum
  change (∑ y ∈ B, H y) = _
  symm
  calc
    (∑ p ∈ primitiveEndpointPairCarrier M n hn,
        if primitiveEndpointPairSupported δ R z w p then
          primitiveEndpointLatticeSum M n hn A p.1 p.2
        else 0) =
        ∑ p ∈ primitiveEndpointPairCarrier M n hn,
          ∑ y ∈ B,
            if primitiveEndpointPairSupported δ R z w p then
              if g y = p then F y else 0
            else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hs : primitiveEndpointPairSupported δ R z w p
      · simp only [hs, ↓reduceIte]
        unfold primitiveEndpointLatticeSum latticeChainSum
        apply Finset.sum_congr rfl
        intro y hy
        unfold primitiveEndpointLatticeStatistic
        have hiff :
            (y (primitiveEndpointLeft n hn) = p.1 ∧
                y (primitiveEndpointRight n hn) = p.2) ↔
              g y = p := by
          constructor
          · intro h
            apply Prod.ext
            · exact h.1
            · exact h.2
          · intro h
            exact
              ⟨congrArg Prod.fst h,
                congrArg Prod.snd h⟩
        by_cases hend :
            y (primitiveEndpointLeft n hn) = p.1 ∧
              y (primitiveEndpointRight n hn) = p.2
        · have hgy : g y = p := hiff.mp hend
          simp [hend, hgy, F]
        · have hgy : g y ≠ p := (not_congr hiff).mp hend
          simp [hend, hgy, F]
      · simp [hs]
    _ = ∑ y ∈ B,
        ∑ p ∈ primitiveEndpointPairCarrier M n hn,
          if primitiveEndpointPairSupported δ R z w p then
            if g y = p then F y else 0
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ y ∈ B, H y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hgmem :
          g y ∈ primitiveEndpointPairCarrier M n hn := by
        rw [primitiveEndpointPairCarrier, Finset.mem_image]
        exact ⟨y, hy, rfl⟩
      rw [Finset.sum_eq_single (g y)]
      · by_cases hs :
            primitiveEndpointSupport hn δ R z w y
        · have hspair :
              primitiveEndpointPairSupported δ R z w (g y) := by
            simpa only [g] using
              (primitiveEndpointSupport_iff_pairSupported
                hn δ R z w y).1 hs
          simp [hspair, hs, H]
        · have hspair :
              ¬primitiveEndpointPairSupported δ R z w (g y) := by
            simpa only [g] using
              (not_congr
                (primitiveEndpointSupport_iff_pairSupported
                  hn δ R z w y)).mp hs
          simp [hspair, hs, H]
      · intro p hp hne
        have hne' : g y ≠ p := Ne.symm hne
        simp [hne']
      · intro hnot
        exact False.elim (hnot hgmem)

/-- The endpoint-independent coefficient supplied by the final Hepp-tree
assembly. -/
def primitiveEndpointUniformCoefficient
    (C : ℝ) (M n K : ℕ) : ℝ :=
  ((4 ^ (4 * (2 * n)) : ℕ) : ℝ) *
    ((8 * (K + 1) : ℝ) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) +
      (16 * volumeEstimateFinalConstant) ^ (2 * n) *
        ((((2 ^ n : ℕ) : ℝ) *
            ((32 * (4 * C) * (K + 1)) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (n - 2)))) +
          (((n * n : ℕ) : ℝ) *
            ((256 * (4 * C) * (K + 1)) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (n - 2))))))

theorem primitiveEndpointUniformCoefficient_nonneg
    {C : ℝ} (hC : 0 ≤ C) (M n K : ℕ) :
    0 ≤ primitiveEndpointUniformCoefficient C M n K := by
  unfold primitiveEndpointUniformCoefficient
  have hvol : 0 ≤ volumeEstimateFinalConstant := by
    unfold volumeEstimateFinalConstant
    positivity
  positivity

theorem primitiveEndpointLatticeSum_le_coefficient_mul_bracket
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointLatticeSum M n (by omega) A x₀ x₁ ≤
      primitiveEndpointUniformCoefficient C M n K *
        latticeBracketInvFourth x₀ x₁ := by
  have h :=
    primitiveEndpointLatticeSum_le_uniformTreeBound
      hC hn hnL A x₀ x₁
  unfold primitiveEndpointUniformCoefficient
  calc
    primitiveEndpointLatticeSum M n (by omega) A x₀ x₁ ≤
        ((4 ^ (4 * (2 * n)) : ℕ) : ℝ) *
          (latticeBracketInvFourth x₀ x₁ *
            ((8 * (K + 1) : ℝ) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) +
              (16 * volumeEstimateFinalConstant) ^ (2 * n) *
                ((((2 ^ n : ℕ) : ℝ) *
                    ((32 * (4 * C) * (K + 1)) ^ n *
                      (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                        (n - 2)))) +
                  (((n * n : ℕ) : ℝ) *
                    ((256 * (4 * C) * (K + 1)) ^ n *
                      (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                        (n - 2))))))) := h
    _ = _ := by ring

/-- Apply the fixed-endpoint tree estimate after the exact endpoint-fiber
decomposition. -/
theorem primitiveEndpointSupportedLatticeSum_le_bracketSum
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (A : Finset (Fin (2 * n)))
    (δ R : ℝ) (z w : T4) :
    primitiveEndpointSupportedLatticeSum
        M n (by omega) A δ R z w ≤
      primitiveEndpointUniformCoefficient C M n K *
        primitiveEndpointBracketSum
          M n (by omega) δ R z w := by
  rw [primitiveEndpointSupportedLatticeSum_eq_endpointPairs]
  unfold primitiveEndpointBracketSum
  calc
    (∑ p ∈ primitiveEndpointPairCarrier M n (by omega),
        if primitiveEndpointPairSupported δ R z w p then
          primitiveEndpointLatticeSum M n (by omega) A p.1 p.2
        else 0) =
        ∑ p ∈
            (primitiveEndpointPairCarrier M n (by omega)).filter
              (primitiveEndpointPairSupported δ R z w),
          primitiveEndpointLatticeSum
            M n (by omega) A p.1 p.2 := by
      rw [Finset.sum_filter]
    _ ≤ ∑ p ∈
          (primitiveEndpointPairCarrier M n (by omega)).filter
            (primitiveEndpointPairSupported δ R z w),
        primitiveEndpointUniformCoefficient C M n K *
          latticeBracketInvFourth p.1 p.2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact
        primitiveEndpointLatticeSum_le_coefficient_mul_bracket
          hC hn hnL A p.1 p.2
    _ = primitiveEndpointUniformCoefficient C M n K *
          ∑ p ∈
            (primitiveEndpointPairCarrier M n (by omega)).filter
              (primitiveEndpointPairSupported δ R z w),
            latticeBracketInvFourth p.1 p.2 := by
      rw [Finset.mul_sum]

/-- Sum over the `2^(2n)` lower-half choices without reintroducing any
pairing multiplicity. -/
theorem sum_primitiveEndpointSupportedLatticeSum_le
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (δ R : ℝ) (z w : T4) :
    (∑ A : Finset (Fin (2 * n)),
        primitiveEndpointSupportedLatticeSum
          M n (by omega) A δ R z w) ≤
      (((2 ^ (2 * n) : ℕ) : ℝ) *
        primitiveEndpointUniformCoefficient C M n K) *
          primitiveEndpointBracketSum
            M n (by omega) δ R z w := by
  calc
    (∑ A : Finset (Fin (2 * n)),
        primitiveEndpointSupportedLatticeSum
          M n (by omega) A δ R z w) ≤
        ∑ _A : Finset (Fin (2 * n)),
          primitiveEndpointUniformCoefficient C M n K *
            primitiveEndpointBracketSum
              M n (by omega) δ R z w := by
      apply Finset.sum_le_sum
      intro A hA
      exact
        primitiveEndpointSupportedLatticeSum_le_bracketSum
          hC hn hnL A δ R z w
    _ = (((2 ^ (2 * n) : ℕ) : ℝ) *
          primitiveEndpointUniformCoefficient C M n K) *
            primitiveEndpointBracketSum
              M n (by omega) δ R z w := by
      simp only [Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Fintype.card_finset,
        Fintype.card_fin]
      push_cast
      ring

/-- Complete endpoint-preserving R-51 estimate at the periodic real-sum
level.  All losses are explicit and the global inserted decay remains
visible. -/
theorem primitivePeriodicEndpointPairingSum_le_globalDecay
    {C : ℝ} (hC : PermSumEstimate C)
    {ε : ℝ} (hε : 0 < ε)
    {n q K : ℕ} [NeZero q] (hn : 2 ≤ n)
    (hqε : (q : ℤ) = compatibleCellCount ε)
    {δ R : ℝ} (hR : 0 ≤ R)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (hnL : n ≤ K * (Nat.log 2 (4 * (2 * q)) + 1))
    (z w : T4) :
    primitivePeriodicEndpointPairingSum
        ε n (by omega) q δ R z w ≤
      Real.exp (12 * (2 * n - 1)) *
        ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
          ((((2 ^ (2 * n) : ℕ) : ℝ) *
              primitiveEndpointUniformCoefficient
                C (2 * q) n K) *
            ((160000 * (R + 2) ^ 4) ^ 2 *
              ((9 * (1 + 4 * R ^ 2)) ^ 2 * δ ^ 4 *
                (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2)))) := by
  have hδ : 0 < δ := by
    have hqR : (0 : ℝ) < ((q : ℤ) : ℝ) := by
      exact_mod_cast hq.cellCount_pos
    nlinarith [hq.period_eq, Real.pi_pos]
  have hperiod :=
    primitivePeriodicEndpointPairingSum_le_supportedLattice
      hε (by omega : 1 ≤ n) hqε hδ hq R z w
  have hsum :=
    sum_primitiveEndpointSupportedLatticeSum_le
      hC hn hnL δ R z w
  have hbracket :=
    primitiveEndpointBracketSum_le_globalDecay
      (by omega : 1 ≤ n) hR hq z w
  have hE : 0 ≤ Real.exp (12 * (2 * n - 1)) :=
    (Real.exp_pos _).le
  have hfiber :
      0 ≤ (((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hcoeff :
      0 ≤ (((2 ^ (2 * n) : ℕ) : ℝ) *
        primitiveEndpointUniformCoefficient C (2 * q) n K) :=
    mul_nonneg (Nat.cast_nonneg _)
      (primitiveEndpointUniformCoefficient_nonneg hC.1.le _ _ _)
  calc
    primitivePeriodicEndpointPairingSum
        ε n (by omega) q δ R z w ≤
      Real.exp (12 * (2 * n - 1)) *
        ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
          ∑ A : Finset (Fin (2 * n)),
            primitiveEndpointSupportedLatticeSum
              (2 * q) n (by omega) A δ R z w) := hperiod
    _ ≤ Real.exp (12 * (2 * n - 1)) *
        ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
          ((((2 ^ (2 * n) : ℕ) : ℝ) *
              primitiveEndpointUniformCoefficient C (2 * q) n K) *
            primitiveEndpointBracketSum
              (2 * q) n (by omega) δ R z w)) := by
      apply mul_le_mul_of_nonneg_left _ hE
      apply mul_le_mul_of_nonneg_left _ hfiber
      exact hsum
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hE
      apply mul_le_mul_of_nonneg_left _ hfiber
      exact mul_le_mul_of_nonneg_left hbracket hcoeff

/-- Named right-hand side of the endpoint-preserving periodic R-51
estimate.  Naming it keeps the continuum and coupling ledgers independent
of the (already closed) Hepp-tree expression. -/
def primitiveR51GlobalDecayBound
    (C : ℝ) (n q K : ℕ) (δ R : ℝ) (z w : T4) : ℝ :=
  Real.exp (12 * (2 * n - 1)) *
    ((((3 ^ 4) ^ (2 * n) : ℕ) : ℝ) *
      ((((2 ^ (2 * n) : ℕ) : ℝ) *
          primitiveEndpointUniformCoefficient
            C (2 * q) n K) *
        ((160000 * (R + 2) ^ 4) ^ 2 *
          ((9 * (1 + 4 * R ^ 2)) ^ 2 * δ ^ 4 *
            (torusDistSq (z - w) + δ ^ 2)⁻¹ ^ 2))))

theorem primitivePeriodicEndpointPairingSum_le_r51GlobalDecayBound
    {C : ℝ} (hC : PermSumEstimate C)
    {ε : ℝ} (hε : 0 < ε)
    {n q K : ℕ} [NeZero q] (hn : 2 ≤ n)
    (hqε : (q : ℤ) = compatibleCellCount ε)
    {δ R : ℝ} (hR : 0 ≤ R)
    (hq : PeriodCompatibleMesh δ (q : ℤ))
    (hnL : n ≤ K * (Nat.log 2 (4 * (2 * q)) + 1))
    (z w : T4) :
    primitivePeriodicEndpointPairingSum
        ε n (by omega) q δ R z w ≤
      primitiveR51GlobalDecayBound C n q K δ R z w := by
  simpa only [primitiveR51GlobalDecayBound] using
    primitivePeriodicEndpointPairingSum_le_globalDecay
      hC hε hn hqε hR hq hnL z w

/-! ## Return to the continuum primitive integrals -/

/-- Sum the cellwise Tonelli estimate over the complete primitive pairing
carrier before applying the endpoint-preserving periodic bound.  In
particular, this theorem does not pay a copy of the all-pairings lattice
estimate for each source pairing. -/
theorem sum_primitiveInsertedIntegrand_lintegral_le_periodicEndpointPairingSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          PeriodCompatibleMesh
            (compatibleMeshSize ε) (q : ℤ) →
        ∀ (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
          (∑ κ ∈ primitiveFullPairings n,
              ∫⁻ v,
                ENNReal.ofReal
                  |primitiveInsertedIntegrand
                    ρ ε n (by omega) G κ
                      (primitiveAssemble
                        n (by omega) z w v)|
                ∂MeasureTheory.Measure.pi
                  fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal Q *
              (ENNReal.ofReal farCoeff +
                ENNReal.ofReal nearCoeff) *
              ENNReal.ofReal
                (primitivePeriodicEndpointPairingSum
                  ε n (by omega) q δ R z w) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hraw⟩ :=
    r51_primitiveInsertedIntegrand_lintegral_le_periodicEndpointSum ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG ε hε hε1 q instq hq z w
  let hn1 : 1 ≤ n := by omega
  let R : ℝ := 1 + 4 * ρ.radius
  let δ : ℝ := compatibleMeshSize ε
  let farCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q : ℝ := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let P :=
    primitiveCopiedEndpointSupported ρ ε n hn1 z w
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hδ : 0 < δ := by
    exact compatibleMeshSize_pos hε
  have hfar : 0 ≤ farCoeff := by
    dsimp only [farCoeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (by positivity)
          (pow_nonneg
            (mul_nonneg hCcell.le
              (add_nonneg (sq_nonneg R)
                (pow_nonneg hR.le 4))) _))
        (terminalRadiusFactor_pos hR).le)
      (pow_nonneg hδ.le _)
  have hnear : 0 ≤ nearCoeff := by
    dsimp only [nearCoeff]
    exact mul_nonneg
      (mul_nonneg
        (by positivity)
        (pow_nonneg
          (mul_nonneg hCcell.le
            (cellChainRadiusFactor_pos R).le) _))
      (pow_nonneg hδ.le _)
  have hterm :
      ∀ κ ∈ primitiveFullPairings n,
        (∫⁻ v,
            ENNReal.ofReal
              |primitiveInsertedIntegrand
                ρ ε n hn1 G κ
                  (primitiveAssemble n hn1 z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure) ≤
          ENNReal.ofReal Q *
            (ENNReal.ofReal farCoeff +
              ENNReal.ofReal nearCoeff) *
            r51PeriodicReductionFilteredSum
              ε n hn1 q δ κ P := by
    intro κ hκ
    have hk :=
      hraw n hn G hG κ hκ hε hε1 hq z w
    have hfactor :=
      r51PeriodicReductionFilteredSum_factor
        (Q := Q) hfar hnear ε n hn1 q δ κ P
    calc
      (∫⁻ v,
          ENNReal.ofReal
            |primitiveInsertedIntegrand
              ρ ε n hn1 G κ
                (primitiveAssemble n hn1 z w v)|
          ∂MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure) ≤
        ∑ u ∈
            ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
              ((2 * n - 1) + 1)).filter
                (RespectsPairing
                  (primitiveReductionPairing n hn1 κ))).filter P,
          ENNReal.ofReal Q *
            (ENNReal.ofReal
                (farCoeff *
                  r51PeriodicReductionWeight
                    q (by omega) δ
                      (primitiveCopiedSourceTuple
                        n hn1 u)) +
              ENNReal.ofReal
                (nearCoeff *
                  r51PeriodicReductionWeight
                    q (by omega) δ
                      (primitiveCopiedSourceTuple
                        n hn1 u))) := by
          simpa only [R, δ, farCoeff, nearCoeff,
            Q, P, hn1] using hk
      _ = ENNReal.ofReal Q *
          (ENNReal.ofReal farCoeff +
            ENNReal.ofReal nearCoeff) *
          r51PeriodicReductionFilteredSum
            ε n hn1 q δ κ P := hfactor
  calc
    (∑ κ ∈ primitiveFullPairings n,
        ∫⁻ v,
          ENNReal.ofReal
            |primitiveInsertedIntegrand
              ρ ε n hn1 G κ
                (primitiveAssemble n hn1 z w v)|
          ∂MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure) ≤
      ∑ κ ∈ primitiveFullPairings n,
        ENNReal.ofReal Q *
          (ENNReal.ofReal farCoeff +
            ENNReal.ofReal nearCoeff) *
          r51PeriodicReductionFilteredSum
            ε n hn1 q δ κ P := by
      apply Finset.sum_le_sum
      intro κ hκ
      exact hterm κ hκ
    _ = ENNReal.ofReal Q *
        (ENNReal.ofReal farCoeff +
          ENNReal.ofReal nearCoeff) *
        (∑ κ ∈ primitiveFullPairings n,
          r51PeriodicReductionFilteredSum
            ε n hn1 q δ κ P) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal Q *
        (ENNReal.ofReal farCoeff +
          ENNReal.ofReal nearCoeff) *
        ENNReal.ofReal
          (primitivePeriodicEndpointPairingSum
            ε n hn1 q δ R z w) := by
      rw [sum_r51PeriodicReductionFilteredSum_endpoint_eq
        hε ρ n hn1 q z w]

/-- Complete inserted R-51 bound at the continuum-integrand level, with
all covariance, cell, periodic-cut, endpoint, and Hepp-tree factors kept
explicit. -/
theorem sum_primitiveInsertedIntegrand_lintegral_le_r51GlobalDecayBound
    {C : ℝ} (hC : PermSumEstimate C)
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          (q : ℤ) = compatibleCellCount ε →
        ∀ (K : ℕ),
          n ≤ K * (Nat.log 2 (4 * (2 * q)) + 1) →
        ∀ (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
          (∑ κ ∈ primitiveFullPairings n,
              ∫⁻ v,
                ENNReal.ofReal
                  |primitiveInsertedIntegrand
                    ρ ε n (by omega) G κ
                      (primitiveAssemble
                        n (by omega) z w v)|
                ∂MeasureTheory.Measure.pi
                  fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal Q *
              (ENNReal.ofReal farCoeff +
                ENNReal.ofReal nearCoeff) *
              ENNReal.ofReal
                (primitiveR51GlobalDecayBound
                  C n q K δ R z w) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hperiod⟩ :=
    sum_primitiveInsertedIntegrand_lintegral_le_periodicEndpointPairingSum
      ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG ε hε hε1 q instq hqε K hnL z w
  let hn1 : 1 ≤ n := by omega
  let R : ℝ := 1 + 4 * ρ.radius
  let δ : ℝ := compatibleMeshSize ε
  let farCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q : ℝ := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  have hmesh :
      PeriodCompatibleMesh δ (q : ℤ) := by
    dsimp only [δ]
    rw [hqε]
    exact compatibleMesh_isPeriodCompatible hε
  have hsum :=
    hperiod n hn G hG hε hε1 hmesh z w
  have hR : 0 ≤ R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hdecay :
      primitivePeriodicEndpointPairingSum
          ε n hn1 q δ R z w ≤
        primitiveR51GlobalDecayBound
          C n q K δ R z w := by
    exact
      primitivePeriodicEndpointPairingSum_le_r51GlobalDecayBound
        hC hε hn hqε hR hmesh hnL z w
  have hdecayE :
      ENNReal.ofReal
          (primitivePeriodicEndpointPairingSum
            ε n hn1 q δ R z w) ≤
        ENNReal.ofReal
          (primitiveR51GlobalDecayBound
            C n q K δ R z w) :=
    ENNReal.ofReal_le_ofReal hdecay
  calc
    (∑ κ ∈ primitiveFullPairings n,
        ∫⁻ v,
          ENNReal.ofReal
            |primitiveInsertedIntegrand
              ρ ε n hn1 G κ
                (primitiveAssemble n hn1 z w v)|
          ∂MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure) ≤
      ENNReal.ofReal Q *
        (ENNReal.ofReal farCoeff +
          ENNReal.ofReal nearCoeff) *
        ENNReal.ofReal
          (primitivePeriodicEndpointPairingSum
            ε n hn1 q δ R z w) := by
      simpa only [R, δ, farCoeff, nearCoeff,
        Q, hn1] using hsum
    _ ≤ ENNReal.ofReal Q *
        (ENNReal.ofReal farCoeff +
          ENNReal.ofReal nearCoeff) *
        ENNReal.ofReal
          (primitiveR51GlobalDecayBound
            C n q K δ R z w) := by
      exact mul_le_mul_right hdecayE _

/-- The absolute value of the Bochner sum defining the inserted primitive
kernel is controlled by the same summed `lintegral`.  This uses only the
universal norm bound for the Bochner integral; no sign, integrability, or
separate measurability assumption is hidden here. -/
theorem ofReal_abs_primitiveKernelInserted_le_lintegralSum
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    ENNReal.ofReal
        |primitiveKernelInserted ρ lam ε n hn G z w| ≤
      ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
        ∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveInsertedIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure := by
  have hcoupling :
      0 ≤ lamEps lam ε ^ (2 * n) :=
    (even_two_mul n).pow_nonneg _
  unfold primitiveKernelInserted
  rw [abs_mul, abs_of_nonneg hcoupling,
    ENNReal.ofReal_mul hcoupling]
  apply mul_le_mul_right
  calc
    ENNReal.ofReal
        |∑ κ ∈ primitiveFullPairings n,
          ∫ v : Fin (2 * n - 2) → T4,
            primitiveInsertedIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v)
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure| =
      ‖∑ κ ∈ primitiveFullPairings n,
          ∫ v : Fin (2 * n - 2) → T4,
            primitiveInsertedIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v)
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
    _ ≤
        ∑ κ ∈ primitiveFullPairings n,
          ‖∫ v : Fin (2 * n - 2) → T4,
              primitiveInsertedIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)
              ∂MeasureTheory.Measure.pi
                fun _ : Fin (2 * n - 2) => paperMeasure‖ₑ :=
      enorm_sum_le _ _
    _ ≤
        ∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveInsertedIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure := by
      apply Finset.sum_le_sum
      intro κ hκ
      have hnorm :=
        MeasureTheory.enorm_integral_le_lintegral_enorm
          (μ := MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure)
          (fun v =>
            primitiveInsertedIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v))
      simpa only [Real.enorm_eq_ofReal_abs] using hnorm

/-- Explicit all-factor inserted-kernel estimate obtained by composing the
Bochner norm inequality with the completed endpoint-preserving R-51
reduction. -/
theorem ofReal_abs_primitiveKernelInserted_le_r51GlobalDecayBound
    {C : ℝ} (hC : PermSumEstimate C)
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ {q : ℕ} [NeZero q],
          (q : ℤ) = compatibleCellCount ε →
        ∀ (K : ℕ),
          n ≤ K * (Nat.log 2 (4 * (2 * q)) + 1) →
        ∀ (lam : ℝ) (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let farCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (12 + 32 * R ^ 2) *
              (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
          ENNReal.ofReal
              |primitiveKernelInserted
                ρ lam ε n (by omega) G z w| ≤
            ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
              (ENNReal.ofReal Q *
                (ENNReal.ofReal farCoeff +
                  ENNReal.ofReal nearCoeff) *
                ENNReal.ofReal
                  (primitiveR51GlobalDecayBound
                    C n q K δ R z w)) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hglobal⟩ :=
    sum_primitiveInsertedIntegrand_lintegral_le_r51GlobalDecayBound
      hC ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG ε hε hε1 q instq hqε K hnL lam z w
  let hn1 : 1 ≤ n := by omega
  let R : ℝ := 1 + 4 * ρ.radius
  let δ : ℝ := compatibleMeshSize ε
  let farCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q : ℝ := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  have hbochner :=
    ofReal_abs_primitiveKernelInserted_le_lintegralSum
      ρ lam ε n hn1 G z w
  have hsum :=
    hglobal n hn G hG hε hε1 hqε K hnL z w
  calc
    ENNReal.ofReal
        |primitiveKernelInserted
          ρ lam ε n hn1 G z w| ≤
      ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
        ∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveInsertedIntegrand
                ρ ε n hn1 G κ
                  (primitiveAssemble n hn1 z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure :=
      hbochner
    _ ≤ ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
        (ENNReal.ofReal Q *
          (ENNReal.ofReal farCoeff +
            ENNReal.ofReal nearCoeff) *
          ENNReal.ofReal
            (primitiveR51GlobalDecayBound
              C n q K δ R z w)) := by
      apply mul_le_mul_right
      simpa only [R, δ, farCoeff, nearCoeff,
        Q, hn1] using hsum

/-! ## Recovering the non-inserted kernel -/

/-- The insertion dominates the squared separation of the two fixed
endpoints, pointwise in every internal-variable assignment. -/
theorem endpointFactor_mul_abs_primitiveIntegrand_le_inserted
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (z w : T4) (v : Fin (2 * n - 2) → T4) :
    (ε ^ 2 + torusDistSq (z - w)) *
        |primitiveIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn z w v)| ≤
      |primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)| := by
  let x := primitiveAssemble n hn z w v
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  have hdiam :
      torusDistSq (z - w) ≤ torusTupleDiameterSq x := by
    simpa only [x, primitiveAssemble_zero,
      primitiveAssemble_last] using
      torusDistSq_sub_le_torusTupleDiameterSq
        x (⟨0, by omega⟩ : Fin (2 * n))
          (primitiveLast n hn)
  have hleft :
      0 ≤ ε ^ 2 + torusDistSq (z - w) :=
    add_nonneg (sq_nonneg ε)
      (torusDistSq_nonneg (z - w))
  have hright :
      0 ≤ ε ^ 2 + torusTupleDiameterSq x :=
    add_nonneg (sq_nonneg ε)
      (torusTupleDiameterSq_nonneg x)
  unfold primitiveInsertedIntegrand
  rw [abs_mul, abs_of_nonneg hright]
  exact mul_le_mul_of_nonneg_right
    (add_le_add le_rfl hdiam) (abs_nonneg _)

/-- Summed `lintegral` form of the endpoint-insertion comparison. -/
theorem endpointFactor_mul_sum_primitiveIntegrand_lintegral_le_inserted
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    ENNReal.ofReal (ε ^ 2 + torusDistSq (z - w)) *
        (∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure) ≤
      ∑ κ ∈ primitiveFullPairings n,
        ∫⁻ v,
          ENNReal.ofReal
            |primitiveInsertedIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v)|
          ∂MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure := by
  let D : ℝ := ε ^ 2 + torusDistSq (z - w)
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (sq_nonneg ε)
      (torusDistSq_nonneg (z - w))
  calc
    ENNReal.ofReal D *
        (∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure) =
      ∑ κ ∈ primitiveFullPairings n,
        ENNReal.ofReal D *
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure := by
      rw [Finset.mul_sum]
    _ ≤
      ∑ κ ∈ primitiveFullPairings n,
        ∫⁻ v,
          ENNReal.ofReal D *
            ENNReal.ofReal
              |primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
          ∂MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure := by
      apply Finset.sum_le_sum
      intro κ hκ
      exact MeasureTheory.lintegral_const_mul_le _ _
    _ ≤
      ∑ κ ∈ primitiveFullPairings n,
        ∫⁻ v,
          ENNReal.ofReal
            |primitiveInsertedIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v)|
          ∂MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure := by
      apply Finset.sum_le_sum
      intro κ hκ
      apply MeasureTheory.lintegral_mono
      intro v
      change
        ENNReal.ofReal D *
            ENNReal.ofReal
              |primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)| ≤
          ENNReal.ofReal
            |primitiveInsertedIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v)|
      rw [← ENNReal.ofReal_mul hD]
      apply ENNReal.ofReal_le_ofReal
      exact
        endpointFactor_mul_abs_primitiveIntegrand_le_inserted
          ρ ε n hn G κ z w v

/-- Bochner norm bound for the non-inserted primitive kernel. -/
theorem ofReal_abs_primitiveKernel_le_lintegralSum
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    ENNReal.ofReal
        |primitiveKernel ρ lam ε n hn G z w| ≤
      ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
        ∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure := by
  have hcoupling :
      0 ≤ lamEps lam ε ^ (2 * n) :=
    (even_two_mul n).pow_nonneg _
  unfold primitiveKernel
  rw [abs_mul, abs_of_nonneg hcoupling,
    ENNReal.ofReal_mul hcoupling]
  apply mul_le_mul_right
  calc
    ENNReal.ofReal
        |∑ κ ∈ primitiveFullPairings n,
          ∫ v : Fin (2 * n - 2) → T4,
            primitiveIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v)
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure| =
      ‖∑ κ ∈ primitiveFullPairings n,
          ∫ v : Fin (2 * n - 2) → T4,
            primitiveIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v)
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
    _ ≤
        ∑ κ ∈ primitiveFullPairings n,
          ‖∫ v : Fin (2 * n - 2) → T4,
              primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)
              ∂MeasureTheory.Measure.pi
                fun _ : Fin (2 * n - 2) => paperMeasure‖ₑ :=
      enorm_sum_le _ _
    _ ≤
        ∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure := by
      apply Finset.sum_le_sum
      intro κ hκ
      have hnorm :=
        MeasureTheory.enorm_integral_le_lintegral_enorm
          (μ := MeasureTheory.Measure.pi
            fun _ : Fin (2 * n - 2) => paperMeasure)
          (fun v =>
            primitiveIntegrand
              ρ ε n hn G κ
                (primitiveAssemble n hn z w v))
      simpa only [Real.enorm_eq_ofReal_abs] using hnorm

/-- The ordinary kernel is reduced to the inserted Tonelli sum after
multiplication by its endpoint factor. -/
theorem endpointFactor_mul_ofReal_abs_primitiveKernel_le_insertedSum
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    ENNReal.ofReal (ε ^ 2 + torusDistSq (z - w)) *
        ENNReal.ofReal
          |primitiveKernel ρ lam ε n hn G z w| ≤
      ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
        ∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveInsertedIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure := by
  have hkernel :=
    ofReal_abs_primitiveKernel_le_lintegralSum
      ρ lam ε n hn G z w
  have hinsertion :=
    endpointFactor_mul_sum_primitiveIntegrand_lintegral_le_inserted
      ρ ε n hn G z w
  calc
    ENNReal.ofReal (ε ^ 2 + torusDistSq (z - w)) *
        ENNReal.ofReal
          |primitiveKernel ρ lam ε n hn G z w| ≤
      ENNReal.ofReal (ε ^ 2 + torusDistSq (z - w)) *
        (ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
          ∑ κ ∈ primitiveFullPairings n,
            ∫⁻ v,
              ENNReal.ofReal
                |primitiveIntegrand
                  ρ ε n hn G κ
                    (primitiveAssemble n hn z w v)|
              ∂MeasureTheory.Measure.pi
                fun _ : Fin (2 * n - 2) => paperMeasure) := by
      apply mul_le_mul_right
      exact hkernel
    _ = ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
        (ENNReal.ofReal (ε ^ 2 + torusDistSq (z - w)) *
          ∑ κ ∈ primitiveFullPairings n,
            ∫⁻ v,
              ENNReal.ofReal
                |primitiveIntegrand
                  ρ ε n hn G κ
                    (primitiveAssemble n hn z w v)|
              ∂MeasureTheory.Measure.pi
                fun _ : Fin (2 * n - 2) => paperMeasure) := by
      ring
    _ ≤ ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
        ∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveInsertedIntegrand
                ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂MeasureTheory.Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure := by
      apply mul_le_mul_right
      exact hinsertion

end

end Anderson4D
