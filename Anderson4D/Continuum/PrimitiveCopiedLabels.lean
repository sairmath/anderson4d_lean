import Anderson4D.Continuum.PrimitiveWindingSector

/-!
# Copied paired labels in the bounded lattice box

This file implements the finite reindexing used literally in paper §5.1:
choose the label at one endpoint of each covariance pair, copy it to the
other endpoint, and retain the resulting tuple in one bounded box.  No
occurrence-wise path unwrapping is used.

The main conclusions have no fiber-cardinality or winding amplification:
the copied-label carrier embeds injectively into the bounded tuple carrier
used by the lattice estimate, and its full primitive-pairing sum is bounded
by the existing all-cuts primitive across-pairing sum.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators ENNReal

/-! ## The paper's finite box -/

/-- Natural half-width of the canonical copied-label box. -/
def primitiveCopiedBoxRadius (ε : ℝ) : ℕ :=
  (torusGridRadius (compatibleMeshSize ε)).natAbs

theorem compatible_torusGridRadius_nonneg
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤ torusGridRadius (compatibleMeshSize ε) := by
  unfold torusGridRadius
  apply Int.ceil_nonneg
  exact div_nonneg Real.pi_pos.le (compatibleMeshSize_pos hε).le

theorem primitiveCopiedBoxRadius_cast
    {ε : ℝ} (hε : 0 < ε) :
    (primitiveCopiedBoxRadius ε : ℤ) =
      torusGridRadius (compatibleMeshSize ε) := by
  unfold primitiveCopiedBoxRadius
  exact Int.natAbs_of_nonneg
    (compatible_torusGridRadius_nonneg hε)

/-- Every label in the canonical torus grid lies in the single natural
integer box consumed by `rdec_boundedTuples`. -/
theorem mem_torusGrid_compatible_abs_le
    {ε : ℝ} (hε : 0 < ε) {y : Z4}
    (hy : y ∈ torusGrid (compatibleMeshSize ε)) :
    ∀ i, |y i| ≤ (primitiveCopiedBoxRadius ε : ℤ) := by
  unfold torusGrid at hy
  rw [Fintype.mem_piFinset] at hy
  intro i
  rw [primitiveCopiedBoxRadius_cast hε, abs_le]
  exact Finset.mem_Icc.mp (hy i)

/-- Tuple form of the preceding bounded-box inclusion. -/
theorem primitiveCanonicalCellCarrier_mem_bounded
    {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    {κ : PartialPairing (Fin (2 * n))}
    {y : Fin (2 * n) → Z4}
    (hy : y ∈ primitiveCanonicalCellCarrier ε n κ) :
    y ∈ rdec_boundedTuples (primitiveCopiedBoxRadius ε) (2 * n) := by
  rw [rdec_mem_boundedTuples]
  intro j i
  have hyGrid :
      y j ∈ torusGrid (compatibleMeshSize ε) := by
    have hpi := (Finset.mem_filter.mp hy).1
    exact (Fintype.mem_piFinset.mp hpi) j
  exact mem_torusGrid_compatible_abs_le hε hyGrid i

/-! ## Choose once, copy to the paired occurrence -/

theorem pairingAnchor_mem_pairingLowerHalf
    {m : ℕ} {κ : PartialPairing (Fin m)}
    (hfull : κ.IsFull) (i : Fin m) :
    pairingAnchor κ i ∈ pairingLowerHalf κ := by
  rw [mem_pairingLowerHalf]
  unfold pairingAnchor
  split_ifs with h
  · exact lt_of_le_of_ne h (hfull i).symm
  · rw [κ.apply_apply]
    exact lt_of_not_ge h

theorem pairingAnchor_eq_self_of_mem_pairingLowerHalf
    {m : ℕ} {κ : PartialPairing (Fin m)}
    {i : Fin m} (hi : i ∈ pairingLowerHalf κ) :
    pairingAnchor κ i = i := by
  have hlt : i < κ i := mem_pairingLowerHalf.mp hi
  simp [pairingAnchor, hlt.le]

/-- A full pairing on `2n` positions has exactly `n` independently chosen
labels; the other `n` labels are literal copies. -/
theorem card_pairingLowerHalf_eq
    {n : ℕ} (κ : PartialPairing (Fin (2 * n)))
    (hfull : κ.IsFull) :
    (pairingLowerHalf κ).card = n := by
  have h :=
    card_primitiveCovarianceRepresentatives κ hfull
  simpa [pairingLowerHalf,
    PartialPairing.isFull_iff_pairSupport_eq_univ.mp hfull] using h

/-- Extend labels chosen only at the smaller endpoint of each pair by
copying the chosen value to its mate. -/
def copiedPairingLabels
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hfull : κ.IsFull) (a : pairingLowerHalf κ → Z4) :
    Fin m → Z4 :=
  fun i => a
    ⟨pairingAnchor κ i,
      pairingAnchor_mem_pairingLowerHalf hfull i⟩

theorem copiedPairingLabels_respectsPairing
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hfull : κ.IsFull) (a : pairingLowerHalf κ → Z4) :
    RespectsPairing κ (copiedPairingLabels κ hfull a) := by
  intro i
  unfold copiedPairingLabels
  congr 1
  apply Subtype.ext
  exact pairingAnchor_apply κ i

/-- Restriction to the canonical smaller endpoint of each pair. -/
def restrictToPairingLowerHalf
    {m : ℕ} (κ : PartialPairing (Fin m))
    (y : {y : Fin m → Z4 // RespectsPairing κ y}) :
    pairingLowerHalf κ → Z4 :=
  fun i => y.1 i.1

/-- Literal formulation of the paper's copied-label sentence: for a full
pairing, choosing one label per lower endpoint is equivalent to a full tuple
satisfying `y_{κ(i)} = y_i`. -/
def copiedPairingLabelsEquiv
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hfull : κ.IsFull) :
    (pairingLowerHalf κ → Z4) ≃
      {y : Fin m → Z4 // RespectsPairing κ y} where
  toFun a :=
    ⟨copiedPairingLabels κ hfull a,
      copiedPairingLabels_respectsPairing κ hfull a⟩
  invFun y := restrictToPairingLowerHalf κ y
  left_inv a := by
    funext i
    change
      a ⟨pairingAnchor κ i.1,
        pairingAnchor_mem_pairingLowerHalf hfull i.1⟩ = a i
    apply congrArg a
    apply Subtype.ext
    exact pairingAnchor_eq_self_of_mem_pairingLowerHalf i.2
  right_inv y := by
    apply Subtype.ext
    funext i
    change y.1 (pairingAnchor κ i) = y.1 i
    unfold pairingAnchor
    split_ifs
    · rfl
    · exact y.2 i

/-! ## Lossless arithmetic reindexing -/

/-- The copied tuple, cast to the arithmetically equal carrier on which
`reductionWeight (2n-1)` is defined. -/
abbrev primitiveCopiedReductionTuple
    (n : ℕ) (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    Fin ((2 * n - 1) + 1) → Z4 :=
  primitiveReductionTupleOfCellTuple n hn y

theorem primitiveCopiedReductionTuple_injective
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (primitiveCopiedReductionTuple n hn) := by
  intro y y' h
  funext i
  have hi := congrFun h
    (Fin.cast (by omega : 2 * n = (2 * n - 1) + 1) i)
  simpa [primitiveCopiedReductionTuple,
    primitiveReductionTupleOfCellTuple] using hi

/-- Inverse arithmetic cast, from the reduction carrier back to the paper's
`Fin (2n)` labels. -/
def primitiveCopiedSourceTuple
    (n : ℕ) (hn : 1 ≤ n)
    (u : Fin ((2 * n - 1) + 1) → Z4) :
    Fin (2 * n) → Z4 :=
  fun i => u (primitiveReductionIndexEquiv n hn i)

@[simp]
theorem primitiveCopiedSourceTuple_reductionTuple
    (n : ℕ) (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    primitiveCopiedSourceTuple n hn
      (primitiveCopiedReductionTuple n hn y) = y := by
  funext i
  simp [primitiveCopiedSourceTuple, primitiveCopiedReductionTuple,
    primitiveReductionTupleOfCellTuple, primitiveReductionIndexEquiv]

@[simp]
theorem primitiveCopiedReductionTuple_sourceTuple
    (n : ℕ) (hn : 1 ≤ n)
    (u : Fin ((2 * n - 1) + 1) → Z4) :
    primitiveCopiedReductionTuple n hn
      (primitiveCopiedSourceTuple n hn u) = u := by
  funext i
  simp [primitiveCopiedSourceTuple, primitiveCopiedReductionTuple,
    primitiveReductionTupleOfCellTuple, primitiveReductionIndexEquiv]

/-- Image of the copied-label carrier on the literal reduction carrier. -/
def primitiveCopiedReductionCarrier
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    Finset (Fin ((2 * n - 1) + 1) → Z4) :=
  (primitiveCanonicalCellCarrier ε n κ).image
    (primitiveCopiedReductionTuple n hn)

@[simp]
theorem mem_primitiveCopiedReductionCarrier
    {ε : ℝ} {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    {u : Fin ((2 * n - 1) + 1) → Z4} :
    u ∈ primitiveCopiedReductionCarrier ε n hn κ ↔
      ∃ y ∈ primitiveCanonicalCellCarrier ε n κ,
        primitiveCopiedReductionTuple n hn y = u := by
  simp [primitiveCopiedReductionCarrier]

/-- Reindexing preserves the copied-pair equalities literally. -/
theorem primitiveCopiedReductionTuple_respectsPairing
    {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    {y : Fin (2 * n) → Z4}
    (hy : RespectsPairing κ y) :
    RespectsPairing (primitiveReductionPairing n hn κ)
      (primitiveCopiedReductionTuple n hn y) := by
  intro i
  simpa [primitiveReductionPairing, primitiveReductionIndexEquiv,
    primitiveCopiedReductionTuple, primitiveReductionTupleOfCellTuple]
    using hy ((primitiveReductionIndexEquiv n hn).symm i)

theorem primitiveCopiedReductionCarrier_respectsPairing
    {ε : ℝ} {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))}
    {u : Fin ((2 * n - 1) + 1) → Z4}
    (hu : u ∈ primitiveCopiedReductionCarrier ε n hn κ) :
    RespectsPairing (primitiveReductionPairing n hn κ) u := by
  obtain ⟨y, hy, rfl⟩ :=
    mem_primitiveCopiedReductionCarrier.mp hu
  exact primitiveCopiedReductionTuple_respectsPairing
    (Finset.mem_filter.mp hy).2

/-- The copied carrier enters the bounded lattice box injectively, with no
winding-sector multiplicity. -/
theorem primitiveCopiedReductionCarrier_subset_bounded
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {hn : 1 ≤ n}
    {κ : PartialPairing (Fin (2 * n))} :
    primitiveCopiedReductionCarrier ε n hn κ ⊆
      rdec_boundedTuples (primitiveCopiedBoxRadius ε)
        ((2 * n - 1) + 1) := by
  intro u hu
  obtain ⟨y, hy, rfl⟩ :=
    mem_primitiveCopiedReductionCarrier.mp hu
  exact primitiveReductionTupleOfCellTuple_mem_bounded
    (primitiveCanonicalCellCarrier_mem_bounded hε hy)

/-- Exact carrier identity: after the arithmetic cast, the paper's copied
grid is precisely the bounded box filtered by the transported pairing
constraint. -/
theorem primitiveCopiedReductionCarrier_eq_filter_bounded
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} {hn : 1 ≤ n}
    (κ : PartialPairing (Fin (2 * n))) :
    primitiveCopiedReductionCarrier ε n hn κ =
      (rdec_boundedTuples (primitiveCopiedBoxRadius ε)
        ((2 * n - 1) + 1)).filter
          (RespectsPairing (primitiveReductionPairing n hn κ)) := by
  ext u
  constructor
  · intro hu
    rw [Finset.mem_filter]
    exact
      ⟨primitiveCopiedReductionCarrier_subset_bounded hε hu,
        primitiveCopiedReductionCarrier_respectsPairing hu⟩
  · intro hu
    obtain ⟨hubox, hurespect⟩ := Finset.mem_filter.mp hu
    let y := primitiveCopiedSourceTuple n hn u
    have hyGrid :
        y ∈ Fintype.piFinset
          (fun _ : Fin (2 * n) =>
            torusGrid (compatibleMeshSize ε)) := by
      rw [Fintype.mem_piFinset]
      intro j
      unfold torusGrid
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have hbound :=
        (rdec_mem_boundedTuples.mp hubox)
          (primitiveReductionIndexEquiv n hn j) i
      rw [primitiveCopiedBoxRadius_cast hε] at hbound
      exact (abs_le.mp hbound)
    have hyRespect : RespectsPairing κ y := by
      intro i
      have hi :=
        hurespect (primitiveReductionIndexEquiv n hn i)
      simpa [y, primitiveCopiedSourceTuple,
        primitiveReductionPairing] using hi
    rw [mem_primitiveCopiedReductionCarrier]
    refine ⟨y, Finset.mem_filter.mpr ⟨hyGrid, hyRespect⟩, ?_⟩
    exact primitiveCopiedReductionTuple_sourceTuple n hn u

/-- Exact fiber multiplicity of the copied-label arithmetic reindexing. -/
def primitiveCopiedReductionFiberMultiplicity
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (u : Fin ((2 * n - 1) + 1) → Z4) : ℕ :=
  ((primitiveCanonicalCellCarrier ε n κ).filter fun y =>
    primitiveCopiedReductionTuple n hn y = u).card

theorem primitiveCopiedReductionFiberMultiplicity_eq_ite
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (u : Fin ((2 * n - 1) + 1) → Z4) :
    primitiveCopiedReductionFiberMultiplicity ε n hn κ u =
      if u ∈ primitiveCopiedReductionCarrier ε n hn κ then 1 else 0 := by
  classical
  by_cases hu :
      u ∈ primitiveCopiedReductionCarrier ε n hn κ
  · obtain ⟨y, hy, hyu⟩ :=
      mem_primitiveCopiedReductionCarrier.mp hu
    have hfilter :
        (primitiveCanonicalCellCarrier ε n κ).filter
            (fun z => primitiveCopiedReductionTuple n hn z = u) =
          {y} := by
      ext z
      constructor
      · intro hz
        have hz' := Finset.mem_filter.mp hz
        have heq :
            primitiveCopiedReductionTuple n hn z =
              primitiveCopiedReductionTuple n hn y :=
          hz'.2.trans hyu.symm
        have : z = y :=
          primitiveCopiedReductionTuple_injective n hn heq
        simpa only [Finset.mem_singleton] using this
      · intro hz
        have : z = y := Finset.mem_singleton.mp hz
        subst z
        exact Finset.mem_filter.mpr ⟨hy, hyu⟩
    simp only [primitiveCopiedReductionFiberMultiplicity, hu,
      if_true, hfilter, Finset.card_singleton]
  · have hfilter :
        (primitiveCanonicalCellCarrier ε n κ).filter
            (fun y => primitiveCopiedReductionTuple n hn y = u) =
          ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨y, hy⟩
      apply hu
      exact mem_primitiveCopiedReductionCarrier.mpr
        ⟨y, (Finset.mem_filter.mp hy).1,
          (Finset.mem_filter.mp hy).2⟩
    simp only [primitiveCopiedReductionFiberMultiplicity, hu,
      if_false, hfilter, Finset.card_empty]

theorem primitiveCopiedReductionFiberMultiplicity_le_one
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (u : Fin ((2 * n - 1) + 1) → Z4) :
    primitiveCopiedReductionFiberMultiplicity ε n hn κ u ≤ 1 := by
  rw [primitiveCopiedReductionFiberMultiplicity_eq_ite]
  split <;> omega

/-- Lossless reindexing remains exact after imposing any decidable support
predicate on the reduction tuple.  In particular, the continuous layer may
retain its fixed-endpoint (or bounded endpoint-neighbourhood) constraint
instead of enlarging to all translations in the box. -/
theorem sum_copiedLabels_filter_eq_boundedPairing_filter
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P]
    (f : (Fin ((2 * n - 1) + 1) → Z4) → ℝ) :
    (∑ y ∈ (primitiveCanonicalCellCarrier ε n κ).filter
          (fun y => P (primitiveCopiedReductionTuple n hn y)),
        f (primitiveCopiedReductionTuple n hn y)) =
      ∑ u ∈
          ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
              ((2 * n - 1) + 1)).filter
            (RespectsPairing (primitiveReductionPairing n hn κ))).filter P,
        f u := by
  let s :=
    (primitiveCanonicalCellCarrier ε n κ).filter
      (fun y => P (primitiveCopiedReductionTuple n hn y))
  let g := primitiveCopiedReductionTuple n hn
  have himage :
      s.image g =
        (primitiveCopiedReductionCarrier ε n hn κ).filter P := by
    ext u
    constructor
    · intro hu
      obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp hu
      have hy' := Finset.mem_filter.mp hy
      rw [Finset.mem_filter]
      refine
        ⟨mem_primitiveCopiedReductionCarrier.mpr
            ⟨y, hy'.1, hyu⟩, ?_⟩
      rw [← hyu]
      exact hy'.2
    · intro hu
      have hu' := Finset.mem_filter.mp hu
      obtain ⟨y, hy, hyu⟩ :=
        mem_primitiveCopiedReductionCarrier.mp hu'.1
      rw [Finset.mem_image]
      refine ⟨y, Finset.mem_filter.mpr ⟨hy, ?_⟩, hyu⟩
      rw [hyu]
      exact hu'.2
  calc
    (∑ y ∈
        (primitiveCanonicalCellCarrier ε n κ).filter
          (fun y => P (primitiveCopiedReductionTuple n hn y)),
        f (primitiveCopiedReductionTuple n hn y)) =
        ∑ u ∈ s.image g, f u := by
      rw [Finset.sum_image
        (primitiveCopiedReductionTuple_injective n hn).injOn]
    _ = ∑ u ∈
          (primitiveCopiedReductionCarrier ε n hn κ).filter P,
        f u := by rw [himage]
    _ = _ := by
      rw [primitiveCopiedReductionCarrier_eq_filter_bounded hε]

/-! ## Finite sums without amplification -/

/-- The exact real-valued copied-label sum for one pairing. -/
def primitiveCopiedReductionCellRealSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) : ℝ :=
  ∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
    reductionWeight (2 * n - 1)
      (primitiveCopiedReductionTuple n hn y)

theorem primitiveCopiedReductionCellRealSum_eq_carrier
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    primitiveCopiedReductionCellRealSum ε n hn κ =
      ∑ u ∈ primitiveCopiedReductionCarrier ε n hn κ,
        reductionWeight (2 * n - 1) u := by
  unfold primitiveCopiedReductionCellRealSum
    primitiveCopiedReductionCarrier
  rw [Finset.sum_image
    (primitiveCopiedReductionTuple_injective n hn).injOn]

/-- Exact fixed-pairing reindexing into the bounded lattice sum. -/
theorem primitiveCopiedReductionCellRealSum_eq_latticeChainSum
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    primitiveCopiedReductionCellRealSum ε n hn κ =
      latticeChainSum (primitiveCopiedBoxRadius ε)
        ((2 * n - 1) + 1) (fun u =>
          if RespectsPairing (primitiveReductionPairing n hn κ) u then
            reductionWeight (2 * n - 1) u
          else 0) := by
  rw [primitiveCopiedReductionCellRealSum_eq_carrier,
    primitiveCopiedReductionCarrier_eq_filter_bounded hε]
  unfold latticeChainSum
  rw [Finset.sum_filter]

/-- For a fixed paper pairing, the copied-label sum is a literal subsum of
the bounded lattice sum for the transported pairing.  There is no
fiber-cardinality multiplier and no comparison of unrelated weights. -/
theorem primitiveCopiedReductionCellRealSum_le_latticeChainSum
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    primitiveCopiedReductionCellRealSum ε n hn κ ≤
      latticeChainSum (primitiveCopiedBoxRadius ε)
        ((2 * n - 1) + 1) (fun u =>
          if RespectsPairing (primitiveReductionPairing n hn κ) u then
            reductionWeight (2 * n - 1) u
          else 0) := by
  rw [primitiveCopiedReductionCellRealSum_eq_carrier]
  let S := primitiveCopiedReductionCarrier ε n hn κ
  let B :=
    rdec_boundedTuples (primitiveCopiedBoxRadius ε)
      ((2 * n - 1) + 1)
  let F : (Fin ((2 * n - 1) + 1) → Z4) → ℝ := fun u =>
    if RespectsPairing (primitiveReductionPairing n hn κ) u then
      reductionWeight (2 * n - 1) u
    else 0
  calc
    (∑ u ∈ S, reductionWeight (2 * n - 1) u) =
        ∑ u ∈ S, F u := by
      apply Finset.sum_congr rfl
      intro u hu
      have hrespect :
          RespectsPairing (primitiveReductionPairing n hn κ) u :=
        primitiveCopiedReductionCarrier_respectsPairing hu
      simp only [F, hrespect, ↓reduceIte]
    _ ≤ ∑ u ∈ B, F u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (primitiveCopiedReductionCarrier_subset_bounded hε)
      intro u huB huS
      unfold F
      split_ifs
      · exact reductionWeight_nonneg _ _
      · exact le_rfl
    _ = _ := rfl

/-- The fixed-pairing copied sum enters its canonical primitive across
carrier without any `M`- or `ε`-dependent prefactor. -/
theorem primitiveCopiedReductionCellRealSum_le_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    {κ : PartialPairing (Fin (2 * n))}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    primitiveCopiedReductionCellRealSum ε n hn κ ≤
      primitiveAcrossLatticeSum (primitiveCopiedBoxRadius ε)
        (2 * n - 1)
        (pairingLowerHalf (primitiveReductionPairing n hn κ)) := by
  let κr := primitiveReductionPairing n hn κ
  have hfullr : κr.IsFull :=
    primitiveReductionPairing_isFull hfull
  have hprimitiver : IsPrimitive κr :=
    primitiveReductionPairing_isPrimitive hprimitive
  let A := pairingLowerHalf κr
  let κa : AcrossPairing A :=
    fullPairingToAcross κr hfullr
  have hκamem : κa ∈ primitiveAcrossPairingFinset A :=
    fullPairingToAcross_mem_primitiveAcrossPairingFinset
      hfullr hprimitiver
  have hfixed :=
    primitiveCopiedReductionCellRealSum_le_latticeChainSum
      hε n hn κ
  have hreindex :
      latticeChainSum (primitiveCopiedBoxRadius ε)
          ((2 * n - 1) + 1) (fun u =>
            if RespectsPairing κr u then
              reductionWeight (2 * n - 1) u
            else 0) =
        latticeChainSum (primitiveCopiedBoxRadius ε)
          ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κa) := by
    unfold latticeChainSum
    apply Finset.sum_congr rfl
    intro u hu
    unfold pairedReductionStatistic
    have hiff := respectsPairing_acrossToPartialPairing_iff A κa u
    rw [acrossToPartialPairing_fullPairingToAcross κr hfullr] at hiff
    by_cases h : RespectsPairing κr u
    · simp only [h, hiff.mp h, ↓reduceIte]
    · have hw : ¬RespectsWord A u κa := fun hw => h (hiff.mpr hw)
      simp only [h, hw, ↓reduceIte]
  rw [hreindex] at hfixed
  exact hfixed.trans
    (Finset.single_le_sum
      (s := primitiveAcrossPairingFinset A)
      (f := fun κ' =>
        latticeChainSum (primitiveCopiedBoxRadius ε)
          ((2 * n - 1) + 1)
          (pairedReductionStatistic (2 * n - 1) A κ'))
      (fun κ' hκ' => by
        unfold latticeChainSum
        apply Finset.sum_nonneg
        intro u hu
        exact pairedReductionStatistic_nonneg _ _ _ _)
      hκamem)

/-! ## The full primitive-pairing carrier -/

/-- Paper (5.5), before fixing the lower-endpoint set `A`: sum the copied
bounded-box statistic over every primitive full pairing. -/
def primitiveCopiedPrimitiveRealSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n) : ℝ :=
  ∑ κ ∈ primitiveFullPairings n,
    primitiveCopiedReductionCellRealSum ε n hn κ

/-- Lossless passage from all source pairings to the literal
`PartialPairing` bounded-lattice carrier.  The outer transport is injective,
so this step introduces no pairing-count factor either. -/
theorem primitiveCopiedPrimitiveRealSum_le_partialLatticeSum
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    primitiveCopiedPrimitiveRealSum ε n hn ≤
      primitivePartialLatticeSum (primitiveCopiedBoxRadius ε)
        (2 * n - 1) := by
  let s := primitiveFullPairings n
  let g :
      PartialPairing (Fin (2 * n)) →
        PartialPairing (Fin ((2 * n - 1) + 1)) :=
    primitiveReductionPairing n hn
  let T :
      Finset (PartialPairing (Fin ((2 * n - 1) + 1))) :=
    Finset.univ.filter fun κ => κ.IsFull ∧ IsPrimitive κ
  let F :
      PartialPairing (Fin ((2 * n - 1) + 1)) → ℝ := fun κ =>
    latticeChainSum (primitiveCopiedBoxRadius ε)
      ((2 * n - 1) + 1) fun u =>
        if RespectsPairing κ u then
          reductionWeight (2 * n - 1) u
        else 0
  have hg : Function.Injective g := by
    intro κ κ' h
    exact
      (PartialPairing.congr
        (primitiveReductionIndexEquiv n hn)).injective
        (by simpa only [g, primitiveReductionPairing] using h)
  have hsub : s.image g ⊆ T := by
    intro κr hκr
    obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hκr
    have hk := mem_primitiveFullPairings.mp hκ
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact
      ⟨primitiveReductionPairing_isFull hk.1,
        primitiveReductionPairing_isPrimitive hk.2⟩
  have hF : ∀ κr, 0 ≤ F κr := by
    intro κr
    unfold F latticeChainSum
    apply Finset.sum_nonneg
    intro u hu
    split_ifs
    · exact reductionWeight_nonneg _ _
    · exact le_rfl
  unfold primitiveCopiedPrimitiveRealSum
  change (∑ κ ∈ s,
      primitiveCopiedReductionCellRealSum ε n hn κ) ≤ _
  calc
    (∑ κ ∈ s,
        primitiveCopiedReductionCellRealSum ε n hn κ) ≤
        ∑ κ ∈ s, F (g κ) := by
      apply Finset.sum_le_sum
      intro κ hκ
      exact
        primitiveCopiedReductionCellRealSum_le_latticeChainSum
          hε n hn κ
    _ = ∑ κr ∈ s.image g, F κr := by
      rw [Finset.sum_image hg.injOn]
    _ ≤ ∑ κr ∈ T, F κr := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro κr hκrT hκrImage
      exact hF κr
    _ = primitivePartialLatticeSum
          (primitiveCopiedBoxRadius ε) (2 * n - 1) := by
      rfl

/-- Final copied-label finite reindexing: the full primitive sum is bounded
by the existing all-cuts across-pairing machine with coefficient exactly
one.  The only overcount is the paper's harmless choice of `A`; no factor
depends on the box radius or on `ε`. -/
theorem primitiveCopiedPrimitiveRealSum_le_sum_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    primitiveCopiedPrimitiveRealSum ε n hn ≤
      ∑ A : Finset (Fin ((2 * n - 1) + 1)),
        primitiveAcrossLatticeSum (primitiveCopiedBoxRadius ε)
          (2 * n - 1) A :=
  (primitiveCopiedPrimitiveRealSum_le_partialLatticeSum
      hε n hn).trans
    (primitivePartialLatticeSum_le_sum_primitiveAcrossLatticeSum
      (primitiveCopiedBoxRadius ε) (2 * n - 1))

/-! ## `ENNReal` form consumed by the cell-integral layer -/

/-- Nonnegative extended-real form of one copied-pairing sum. -/
def primitiveCopiedReductionCellSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) : ENNReal :=
  ∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
    ENNReal.ofReal
      (reductionWeight (2 * n - 1)
        (primitiveCopiedReductionTuple n hn y))

theorem primitiveCopiedReductionCellSum_eq_ofReal
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    primitiveCopiedReductionCellSum ε n hn κ =
      ENNReal.ofReal
        (primitiveCopiedReductionCellRealSum ε n hn κ) := by
  unfold primitiveCopiedReductionCellSum
    primitiveCopiedReductionCellRealSum
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro y hy
  exact reductionWeight_nonneg _ _

/-- Drop-in scalar ledger for a direct copied-cell proof of paper (5.3). -/
theorem primitiveCopiedReductionCellSum_factor
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    (∑ y ∈ primitiveCanonicalCellCarrier ε n κ,
        ENNReal.ofReal q *
          (ENNReal.ofReal
              (a * reductionWeight (2 * n - 1)
                (primitiveCopiedReductionTuple n hn y)) +
           ENNReal.ofReal
              (b * reductionWeight (2 * n - 1)
                (primitiveCopiedReductionTuple n hn y)))) =
      ENNReal.ofReal q *
        (ENNReal.ofReal a + ENNReal.ofReal b) *
          primitiveCopiedReductionCellSum ε n hn κ := by
  unfold primitiveCopiedReductionCellSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [mul_add, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  ring

theorem primitiveCopiedReductionCellSum_le_ofReal_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n)
    {κ : PartialPairing (Fin (2 * n))}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    primitiveCopiedReductionCellSum ε n hn κ ≤
      ENNReal.ofReal
        (primitiveAcrossLatticeSum (primitiveCopiedBoxRadius ε)
          (2 * n - 1)
          (pairingLowerHalf
            (primitiveReductionPairing n hn κ))) := by
  rw [primitiveCopiedReductionCellSum_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal
    (primitiveCopiedReductionCellRealSum_le_primitiveAcross
      hε hn hfull hprimitive)

/-- Extended-real sum over all primitive pairings. -/
def primitiveCopiedPrimitiveSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n) : ENNReal :=
  ∑ κ ∈ primitiveFullPairings n,
    primitiveCopiedReductionCellSum ε n hn κ

theorem primitiveCopiedPrimitiveSum_eq_ofReal
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    primitiveCopiedPrimitiveSum ε n hn =
      ENNReal.ofReal
        (primitiveCopiedPrimitiveRealSum ε n hn) := by
  unfold primitiveCopiedPrimitiveSum primitiveCopiedPrimitiveRealSum
  simp_rw [primitiveCopiedReductionCellSum_eq_ofReal]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro κ hκ
  unfold primitiveCopiedReductionCellRealSum
  exact Finset.sum_nonneg fun y hy => reductionWeight_nonneg _ _

theorem primitiveCopiedPrimitiveSum_le_ofReal_sum_primitiveAcross
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) :
    primitiveCopiedPrimitiveSum ε n hn ≤
      ENNReal.ofReal
        (∑ A : Finset (Fin ((2 * n - 1) + 1)),
          primitiveAcrossLatticeSum (primitiveCopiedBoxRadius ε)
            (2 * n - 1) A) := by
  rw [primitiveCopiedPrimitiveSum_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal
    (primitiveCopiedPrimitiveRealSum_le_sum_primitiveAcross
      hε n hn)

/-!
## Analytic boundary

The finite step is lossless.  A direct proof of the paper's cell estimate
(5.3) uses
`primitiveCopiedReductionTuple n hn y`, while retaining the endpoint support
predicate supplied by the endpoint-fixed integral.  The current theorem
`primitiveInsertedIntegrand_fiber_exhaustive_order` instead produces
`primitiveUnwrappedReductionTuple`; its weight cannot be transported to the
copied tuple uniformly because path unwrapping destroys literal pairing.
`sum_copiedLabels_filter_eq_boundedPairing_filter` is the corresponding
finite regrouping identity.
-/

end

end Anderson4D
