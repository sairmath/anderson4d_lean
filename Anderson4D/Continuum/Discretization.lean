import Anderson4D.Continuum.SingularChain
import Anderson4D.DetParametrix.Core.Kernels
import Anderson4D.PermSum.Statements

/-!
# Cell discretization for the primitive-pairing estimate

This file contains the geometric and measure-theoretic interface used in
paper §5.1, equations (5.1)--(5.5).  It deliberately separates three facts:

* the coordinatewise floor map and its half-open cells;
* the compact-support consequence of a nonzero covariance factor;
* a finite measurable-cell lemma which turns a nonnegative integral into a
  lattice sum, with all measurability and integrability assumptions visible.

The last lemma is an exact decomposition/majorization statement, rather than
an assumption carrying the desired lattice estimate.  The analytic estimate
inside one product cell (paper (5.3)) is supplied separately by
`Continuum/SingularChain.lean`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

/-! ## The `ε`-grid on `ℝ⁴` and the torus -/

/-- Coordinatewise integer part of `ε⁻¹x`, paper §5.1. -/
def floorCell (ε : ℝ) (x : R4) : Z4 :=
  fun i => ⌊ε⁻¹ * x i⌋

/-- The lower-left representative `εy` of the cell indexed by `y`. -/
def cellRepresentative (ε : ℝ) (y : Z4) : R4 :=
  fun i => ε * (y i : ℝ)

/-- The half-open Euclidean cell `εy ≤ x < ε(y+1)`, coordinatewise. -/
def euclideanCell (ε : ℝ) (y : Z4) : Set R4 :=
  Set.univ.pi fun i : Fin dim =>
    Set.Ico (ε * (y i : ℝ)) (ε * ((y i : ℝ) + 1))

theorem measurableSet_euclideanCell (ε : ℝ) (y : Z4) :
    MeasurableSet (euclideanCell ε y) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- On a positive grid, membership in the half-open cell is exactly the
coordinatewise floor equation. -/
theorem mem_euclideanCell_iff_floorCell
    {ε : ℝ} (hε : 0 < ε) (x : R4) (y : Z4) :
    x ∈ euclideanCell ε y ↔ floorCell ε x = y := by
  constructor
  · intro hx
    funext i
    have hi := hx i (Set.mem_univ i)
    apply Int.floor_eq_iff.mpr
    constructor
    · rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hε).mpr (by simpa [mul_comm] using hi.1)
    · rw [← div_eq_inv_mul]
      exact (div_lt_iff₀ hε).mpr (by simpa [mul_comm] using hi.2)
  · intro hxy i _
    have hi : floorCell ε x i = y i := congrFun hxy i
    change ⌊ε⁻¹ * x i⌋ = y i at hi
    have hbounds := Int.floor_eq_iff.mp hi
    change ε * (y i : ℝ) ≤ x i ∧ x i < ε * ((y i : ℝ) + 1)
    constructor
    · have hmul := (le_div_iff₀ hε).mp
        (show (y i : ℝ) ≤ x i / ε by
          simpa only [div_eq_inv_mul] using hbounds.1)
      simpa only [mul_comm] using hmul
    · have hmul := (div_lt_iff₀ hε).mp
        (show x i / ε < (y i : ℝ) + 1 by
          simpa only [div_eq_inv_mul] using hbounds.2)
      simpa only [mul_comm] using hmul

/-- A point is within one mesh size (in the fixed sup norm) of its cell
representative. -/
theorem norm_sub_cellRepresentative_lt
    {ε : ℝ} (hε : 0 < ε) (x : R4) :
    ‖x - cellRepresentative ε (floorCell ε x)‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro i
  have hlo : ((⌊x i / ε⌋ : ℤ) : ℝ) ≤ x i / ε :=
    Int.floor_le _
  have hhi : x i / ε < ((⌊x i / ε⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hlo' : 0 ≤ x i - ε * ((⌊ε⁻¹ * x i⌋ : ℤ) : ℝ) := by
    have hmul := (le_div_iff₀ hε).mp hlo
    rw [div_eq_inv_mul] at hmul
    simpa only [mul_comm, sub_nonneg] using hmul
  have hhi' : x i - ε * ((⌊ε⁻¹ * x i⌋ : ℤ) : ℝ) < ε := by
    have hmul := (div_lt_iff₀ hε).mp hhi
    rw [div_eq_inv_mul] at hmul
    linarith
  simpa only [Pi.sub_apply, cellRepresentative, floorCell, Real.norm_eq_abs,
    abs_of_nonneg hlo'] using hhi'

/-- Two points in the same floor cell are at sup-distance `< 2ε`.
The harmless factor two is retained to make the triangle argument robust. -/
theorem norm_sub_lt_two_mul_of_floorCell_eq
    {ε : ℝ} (hε : 0 < ε) {x x' : R4}
    (hcell : floorCell ε x = floorCell ε x') :
    ‖x - x'‖ < 2 * ε := by
  let r := cellRepresentative ε (floorCell ε x)
  have hx : ‖x - r‖ < ε := norm_sub_cellRepresentative_lt hε x
  have hx' : ‖x' - r‖ < ε := by
    simpa [r, hcell] using norm_sub_cellRepresentative_lt hε x'
  calc
    ‖x - x'‖ = ‖(x - r) - (x' - r)‖ := by
      congr 1
      abel
    _ ≤ ‖x - r‖ + ‖x' - r‖ := norm_sub_le _ _
    _ < 2 * ε := by linarith

/-- The distance between cell representatives is exactly the mesh size
times the fixed lattice sup norm. -/
theorem norm_cellRepresentative_sub (ε : ℝ) (y y' : Z4) :
    ‖cellRepresentative ε y - cellRepresentative ε y'‖ =
      |ε| * znorm (y - y') := by
  have hv :
      cellRepresentative ε y - cellRepresentative ε y' =
        ε • (fun i => ((y - y') i : ℝ)) := by
    funext i
    simp only [cellRepresentative, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Int.cast_sub]
    ring
  rw [hv, norm_smul]
  rfl

/-- Cell/lattice distance comparison, upper direction. -/
theorem norm_sub_le_cell_lattice
    {ε : ℝ} (hε : 0 < ε) {x x' : R4} {y y' : Z4}
    (hxcell : floorCell ε x = y) (hx'cell : floorCell ε x' = y') :
    ‖x - x'‖ < ε * znorm (y - y') + 2 * ε := by
  let r := cellRepresentative ε y
  let r' := cellRepresentative ε y'
  have hx : ‖x - r‖ < ε := by
    simpa [r, hxcell] using norm_sub_cellRepresentative_lt hε x
  have hx' : ‖x' - r'‖ < ε := by
    simpa [r', hx'cell] using norm_sub_cellRepresentative_lt hε x'
  have hrr : ‖r - r'‖ = ε * znorm (y - y') := by
    simpa [r, r', abs_of_pos hε] using norm_cellRepresentative_sub ε y y'
  have h₁ : ‖x - x'‖ ≤ ‖x - r‖ + ‖r - x'‖ := dist_triangle x r x'
  have h₂ : ‖r - x'‖ ≤ ‖r - r'‖ + ‖r' - x'‖ := dist_triangle r r' x'
  have hr'x' : ‖r' - x'‖ = ‖x' - r'‖ := norm_sub_rev _ _
  rw [hrr, hr'x'] at h₂
  linarith

/-- Cell/lattice distance comparison, lower direction. -/
theorem cell_lattice_le_norm_sub
    {ε : ℝ} (hε : 0 < ε) {x x' : R4} {y y' : Z4}
    (hxcell : floorCell ε x = y) (hx'cell : floorCell ε x' = y') :
    ε * znorm (y - y') < ‖x - x'‖ + 2 * ε := by
  let r := cellRepresentative ε y
  let r' := cellRepresentative ε y'
  have hx : ‖x - r‖ < ε := by
    simpa [r, hxcell] using norm_sub_cellRepresentative_lt hε x
  have hx' : ‖x' - r'‖ < ε := by
    simpa [r', hx'cell] using norm_sub_cellRepresentative_lt hε x'
  have hrr : ‖r - r'‖ = ε * znorm (y - y') := by
    simpa [r, r', abs_of_pos hε] using norm_cellRepresentative_sub ε y y'
  have h₁ : ‖r - r'‖ ≤ ‖r - x‖ + ‖x - r'‖ := dist_triangle r x r'
  have h₂ : ‖x - r'‖ ≤ ‖x - x'‖ + ‖x' - r'‖ := dist_triangle x x' r'
  have hrx : ‖r - x‖ = ‖x - r‖ := norm_sub_rev _ _
  rw [hrr, hrx] at h₁
  linarith

/-- The torus cell index uses the canonical lift in `[-π,π)⁴`. -/
def torusFloorCell (ε : ℝ) (z : T4) : Z4 :=
  floorCell ε (torusLift z)

/-- The measurable torus cell carrying a fixed floor index. -/
def torusCell (ε : ℝ) (y : Z4) : Set T4 :=
  torusFloorCell ε ⁻¹' {y}

theorem measurable_torusFloorCell (ε : ℝ) :
    Measurable (torusFloorCell ε) := by
  apply measurable_pi_lambda
  intro i
  exact Int.measurable_floor.comp
    (((measurable_const.mul
      (((measurable_pi_apply i).comp measurable_torusLift)))))

theorem measurableSet_torusCell (ε : ℝ) (y : Z4) :
    MeasurableSet (torusCell ε y) :=
  (measurable_torusFloorCell ε) (measurableSet_singleton y)

@[simp] theorem mem_torusCell (ε : ℝ) (z : T4) (y : Z4) :
    z ∈ torusCell ε y ↔ torusFloorCell ε z = y :=
  Iff.rfl

theorem torusCell_pairwiseDisjoint (ε : ℝ) :
    Set.Pairwise Set.univ (fun y y' => Disjoint (torusCell ε y) (torusCell ε y')) := by
  intro y _ y' _ hne
  rw [Set.disjoint_left]
  intro z hz hz'
  exact hne (hz.symm.trans hz')

/-- Integer half-width of the finite grid met by the canonical fundamental
cube.  It is comparable to `ε⁻¹`; dyadic enlargement to the paper's `M`
is a later harmless monotonicity step. -/
def torusGridRadius (ε : ℝ) : ℤ :=
  ⌈Real.pi / ε⌉

/-- The finite box `ℤ⁴ ∩ [-⌈π/ε⌉,⌈π/ε⌉]⁴`. -/
def torusGrid (ε : ℝ) : Finset Z4 :=
  Fintype.piFinset fun _ : Fin dim =>
    Finset.Icc (-torusGridRadius ε) (torusGridRadius ε)

/-- Every canonical torus floor index lies in the finite grid box. -/
theorem torusFloorCell_mem_torusGrid
    {ε : ℝ} (hε : 0 < ε) (z : T4) :
    torusFloorCell ε z ∈ torusGrid ε := by
  unfold torusGrid
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  obtain ⟨hlift, huplift⟩ := torusLift_mem_Ico z i
  have hqlo : -(Real.pi / ε) ≤ torusLift z i / ε := by
    have h := (div_le_div_iff_of_pos_right hε).mpr hlift
    simpa only [neg_div] using h
  have hqhi : torusLift z i / ε < Real.pi / ε :=
    (div_lt_div_iff_of_pos_right hε).mpr huplift
  have hceil : Real.pi / ε ≤ (torusGridRadius ε : ℝ) := by
    exact Int.le_ceil _
  constructor
  · apply Int.le_floor.mpr
    change ((-torusGridRadius ε : ℤ) : ℝ) ≤
      ε⁻¹ * torusLift z i
    rw [Int.cast_neg, ← div_eq_inv_mul]
    exact (neg_le_neg hceil).trans hqlo
  · apply Int.floor_le_iff.mpr
    change ε⁻¹ * torusLift z i <
      ((torusGridRadius ε : ℤ) : ℝ) + 1
    rw [← div_eq_inv_mul]
    linarith

/-! ## Compact support of `η` and the periodized covariance -/

/-- A nonzero convolution value lies in the radius-`2R` support of
`η = ρ * ρ`.  This uses the cutoff support itself, not an abstract support
hypothesis on `η`. -/
theorem SmoothCutoff.norm_lt_two_radius_of_eta_ne_zero
    (ρ : SmoothCutoff) {x : R4} (hx : ρ.eta x ≠ 0) :
    ‖x‖ < 2 * ρ.radius := by
  have hex : ∃ y : R4, ρ y * ρ (x - y) ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    unfold SmoothCutoff.eta
    simp only [h, integral_zero]
  obtain ⟨y, hy⟩ := hex
  have hy₁ : ρ y ≠ 0 := (mul_ne_zero_iff.mp hy).1
  have hy₂ : ρ (x - y) ≠ 0 := (mul_ne_zero_iff.mp hy).2
  have hyr : ‖y‖ < ρ.radius := by
    have := ρ.support_subset hy₁
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hxyr : ‖x - y‖ < ρ.radius := by
    have := ρ.support_subset hy₂
    simpa [Metric.mem_ball, dist_zero_right] using this
  calc
    ‖x‖ = ‖y + (x - y)‖ := by
      congr 1
      abel
    _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    _ < 2 * ρ.radius := by linarith

/-- A lifted displacement, translated by a period vector. -/
def periodicDisplacement (z : T4) (k : Z4) : R4 :=
  fun i => torusLift z i + 2 * Real.pi * (k i : ℝ)

/-- Coordinatewise quotient map `ℝ⁴ → 𝕋⁴`. -/
def periodizeR4 (x : R4) : T4 :=
  fun i => (x i : AddCircle (2 * Real.pi))

/-- Adding an integer period does not change the represented torus
displacement. -/
theorem periodizeR4_periodicDisplacement (z : T4) (k : Z4) :
    periodizeR4 (periodicDisplacement z k) = z := by
  funext i
  simp only [periodizeR4, periodicDisplacement]
  change ((torusLift z i : AddCircle (2 * Real.pi)) +
    ((2 * Real.pi * (k i : ℝ) : ℝ) : AddCircle (2 * Real.pi))) = z i
  rw [show ((torusLift z i : ℝ) : AddCircle (2 * Real.pi)) = z i from
    AddCircle.coe_equivIco]
  simp only [add_eq_left, QuotientAddGroup.eq_zero_iff]
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨k i, ?_⟩
  simp only [zsmul_eq_mul]
  ring

/-- Nonvanishing of the periodized covariance produces an actual period
translate on which the Euclidean covariance is supported.  No summability
assumption is hidden here: if every summand vanished, the `tsum` would be
the `tsum` of the zero family. -/
theorem SmoothCutoff.exists_periodicDisplacement_of_etaEpsT4_ne_zero
    (ρ : SmoothCutoff) {ε : ℝ} {z : T4}
    (hε : ε ≠ 0) (hz : ρ.etaEpsT4 ε z ≠ 0) :
    ∃ k : Z4,
      ‖periodicDisplacement z k‖ < 2 * ρ.radius * |ε| := by
  have hex : ∃ k : Z4,
      ε⁻¹ ^ (dim : ℕ) *
        ρ.eta (fun i => ε⁻¹ *
          (torusLift z i + 2 * Real.pi * (k i : ℝ))) ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    unfold SmoothCutoff.etaEpsT4
    simp only [h, tsum_zero]
  obtain ⟨k, hk⟩ := hex
  have heta : ρ.eta (ε⁻¹ • periodicDisplacement z k) ≠ 0 := by
    have := (mul_ne_zero_iff.mp hk).2
    change ρ.eta (fun i =>
      ε⁻¹ * (torusLift z i + 2 * Real.pi * (k i : ℝ))) ≠ 0
    exact this
  have hs := ρ.norm_lt_two_radius_of_eta_ne_zero heta
  have habs : 0 < |ε| := abs_pos.mpr hε
  have hscaled :
      |ε|⁻¹ * ‖periodicDisplacement z k‖ < 2 * ρ.radius := by
    simpa [norm_smul, abs_inv] using hs
  refine ⟨k, ?_⟩
  calc
    ‖periodicDisplacement z k‖ =
        |ε| * (|ε|⁻¹ * ‖periodicDisplacement z k‖) := by
          field_simp
    _ < |ε| * (2 * ρ.radius) := mul_lt_mul_of_pos_left hscaled habs
    _ = 2 * ρ.radius * |ε| := by ring

/-- The exact paired-cell constraint extracted from the support of one
`η_ε` factor.  It records the cell chosen at the first endpoint and the
small periodic displacement of the paired endpoint; no assertion is made
that the canonical floor indices of both endpoints coincide (which is
false near cell and torus boundaries). -/
structure PairedCellConstraint
    (ρ : SmoothCutoff) (ε : ℝ) (z w : T4) (y : Z4) : Prop where
  first_cell : torusFloorCell ε z = y
  periodic_support :
    ∃ k : Z4, ‖periodicDisplacement (z - w) k‖ <
      2 * ρ.radius * |ε|

/-- A Euclidean representative of the paired endpoint obtained by subtracting
the supported displacement from the canonical representative of the first
endpoint. -/
def pairedEuclideanRepresentative (z w : T4) (k : Z4) : R4 :=
  torusLift z - periodicDisplacement (z - w) k

theorem periodizeR4_pairedEuclideanRepresentative
    (z w : T4) (k : Z4) :
    periodizeR4 (pairedEuclideanRepresentative z w k) = w := by
  funext i
  change (((torusLift z i -
    periodicDisplacement (z - w) k i : ℝ)) :
      AddCircle (2 * Real.pi)) = w i
  change ((torusLift z i : AddCircle (2 * Real.pi)) -
    (periodicDisplacement (z - w) k i : AddCircle (2 * Real.pi))) = w i
  rw [show ((torusLift z i : ℝ) : AddCircle (2 * Real.pi)) = z i from
    AddCircle.coe_equivIco]
  have hd := congrFun (periodizeR4_periodicDisplacement (z - w) k) i
  change (periodicDisplacement (z - w) k i :
    AddCircle (2 * Real.pi)) = (z - w) i at hd
  rw [hd]
  simp

/-- Paper §5.1's concrete paired-cell conclusion: if `z` lies in cell `y`
and the covariance support relates `z` to `w`, then `w` has a Euclidean
representative within `(1+2R)ε` of the same point `εy`. -/
theorem PairedCellConstraint.exists_representative_near_cell
    {ρ : SmoothCutoff} {ε : ℝ} (hε : 0 < ε)
    {z w : T4} {y : Z4} (h : PairedCellConstraint ρ ε z w y) :
    ∃ wrep : R4,
      periodizeR4 wrep = w ∧
      ‖wrep - cellRepresentative ε y‖ <
        (1 + 2 * ρ.radius) * ε := by
  obtain ⟨k, hk⟩ := h.periodic_support
  refine ⟨pairedEuclideanRepresentative z w k,
    periodizeR4_pairedEuclideanRepresentative z w k, ?_⟩
  have hzcell : ‖torusLift z - cellRepresentative ε y‖ < ε := by
    have := norm_sub_cellRepresentative_lt hε (torusLift z)
    rw [← h.first_cell]
    exact this
  have hεabs : |ε| = ε := abs_of_pos hε
  rw [hεabs] at hk
  calc
    ‖pairedEuclideanRepresentative z w k - cellRepresentative ε y‖ =
        ‖(torusLift z - cellRepresentative ε y) -
          periodicDisplacement (z - w) k‖ := by
            congr 1
            unfold pairedEuclideanRepresentative
            abel
    _ ≤ ‖torusLift z - cellRepresentative ε y‖ +
          ‖periodicDisplacement (z - w) k‖ := norm_sub_le _ _
    _ < (1 + 2 * ρ.radius) * ε := by nlinarith

theorem SmoothCutoff.pairedCellConstraint_of_etaEpsT4_ne_zero
    (ρ : SmoothCutoff) {ε : ℝ} (hε : ε ≠ 0) (z w : T4)
    (hη : ρ.etaEpsT4 ε (z - w) ≠ 0) :
    PairedCellConstraint ρ ε z w (torusFloorCell ε z) :=
  ⟨rfl, ρ.exists_periodicDisplacement_of_etaEpsT4_ne_zero hε hη⟩

/-! ## Pairing-compatible assignments -/

/-- The endpoint chosen to index a pair: the smaller of `i` and `κ i`.
Singles are fixed. -/
def pairingAnchor {m : ℕ} (κ : PartialPairing (Fin m)) (i : Fin m) : Fin m :=
  if i ≤ κ i then i else κ i

theorem pairingAnchor_apply {m : ℕ} (κ : PartialPairing (Fin m)) (i : Fin m) :
    pairingAnchor κ (κ i) = pairingAnchor κ i := by
  unfold pairingAnchor
  rw [κ.apply_apply]
  by_cases h : i ≤ κ i
  · by_cases heq : i = κ i
    · have hki : κ i = i := heq.symm
      rw [hki]
    · have hnot : ¬κ i ≤ i := fun hback => heq (le_antisymm h hback)
      rw [if_pos h, if_neg hnot]
  · have h' : κ i ≤ i := le_of_not_ge h
    rw [if_neg h, if_pos h']

/-- The lattice label used in (5.2): choose a floor cell only at the
smaller endpoint of every pair and copy that label to its mate. -/
def pairedCellAssignment {m : ℕ} (κ : PartialPairing (Fin m))
    (ε : ℝ) (x : Fin m → T4) : Fin m → Z4 :=
  fun i => torusFloorCell ε (x (pairingAnchor κ i))

/-- The copied labels obey `yᵢ = y_{κ(i)}` exactly. -/
theorem pairedCellAssignment_apply {m : ℕ}
    (κ : PartialPairing (Fin m)) (ε : ℝ) (x : Fin m → T4) (i : Fin m) :
    pairedCellAssignment κ ε x (κ i) = pairedCellAssignment κ ε x i := by
  simp only [pairedCellAssignment, pairingAnchor_apply]

/-- Predicate cutting out precisely the copied-label constraint in the
quantification following paper (5.5). -/
def RespectsPairing {m : ℕ} (κ : PartialPairing (Fin m))
    (y : Fin m → Z4) : Prop :=
  ∀ i, y (κ i) = y i

instance instDecidableRespectsPairing {m : ℕ}
    (κ : PartialPairing (Fin m)) (y : Fin m → Z4) :
    Decidable (RespectsPairing κ y) :=
  inferInstanceAs (Decidable (∀ i, y (κ i) = y i))

theorem pairedCellAssignment_respectsPairing {m : ℕ}
    (κ : PartialPairing (Fin m)) (ε : ℝ) (x : Fin m → T4) :
    RespectsPairing κ (pairedCellAssignment κ ε x) :=
  pairedCellAssignment_apply κ ε x

theorem measurable_pairedCellAssignment {m : ℕ}
    (κ : PartialPairing (Fin m)) (ε : ℝ) :
    Measurable (pairedCellAssignment κ ε) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_torusFloorCell ε).comp
    (measurable_pi_apply (pairingAnchor κ i))

/-- Every copied assignment lies in the finite product box. -/
theorem pairedCellAssignment_mem_piFinset {m : ℕ}
    (κ : PartialPairing (Fin m)) {ε : ℝ} (hε : 0 < ε)
    (x : Fin m → T4) :
    pairedCellAssignment κ ε x ∈
      Fintype.piFinset (fun _ : Fin m => torusGrid ε) := by
  rw [Fintype.mem_piFinset]
  intro i
  exact torusFloorCell_mem_torusGrid hε _

/-- Nonvanishing covariance at every (smaller) paired endpoint gives the
paper's support constraint at every selected cell.  The conclusion keeps
the actual torus variables and periodic translate explicit. -/
theorem pairedCellConstraints_of_covariance_ne_zero
    {m : ℕ} (ρ : SmoothCutoff) (κ : PartialPairing (Fin m))
    {ε : ℝ} (hε : ε ≠ 0) (x : Fin m → T4)
    (hη : ∀ i, i < κ i →
      ρ.etaEpsT4 ε (x i - x (κ i)) ≠ 0) :
    ∀ i, i < κ i →
      PairedCellConstraint ρ ε (x i) (x (κ i))
        (pairedCellAssignment κ ε x i) := by
  intro i hi
  have hanchor : pairingAnchor κ i = i := by
    simp [pairingAnchor, hi.le]
  simpa only [pairedCellAssignment, hanchor] using
    ρ.pairedCellConstraint_of_etaEpsT4_ne_zero hε
      (x i) (x (κ i)) (hη i hi)

/-! ## A finite measurable-cell compression lemma -/

/-- A finite measurable partition encoded by an index map.  `indices`
contains the range of `index`; the fibers are measurable.  The formulation
avoids quotienting by null sets and is convenient for product cells. -/
structure FiniteMeasurableCells
    (X ι : Type*) [MeasurableSpace X] [DecidableEq ι] where
  indices : Finset ι
  index : X → ι
  range_subset : ∀ x, index x ∈ indices
  measurable_fiber : ∀ i, MeasurableSet (index ⁻¹' {i})

namespace FiniteMeasurableCells

variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]

/-- Fibers belonging to different indices are disjoint. -/
theorem pairwiseDisjoint (P : FiniteMeasurableCells X ι) :
    Set.Pairwise (↑P.indices)
      (fun i j => Disjoint (P.index ⁻¹' {i}) (P.index ⁻¹' {j})) := by
  intro i _ j _ hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact hij (hxi.symm.trans hxj)

/-- The selected fibers cover the whole space. -/
theorem iUnion_fibers (P : FiniteMeasurableCells X ι) :
    ⋃ i ∈ P.indices, P.index ⁻¹' {i} = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  exact ⟨P.index x, P.range_subset x, rfl⟩

/-- **Finite-cell integral compression.**

Let `f ≥ 0` be integrable.  On the fiber indexed by `i`, suppose
`f ≤ B i`; suppose also that this fiber has real measure at most `V`.
Then the integral is bounded by `V` times the finite lattice sum of `B`.
An optional predicate `R` restricts the sum: `f` must vanish on fibers
outside `R`.  These are precisely the explicit analytic, support, and
measurability obligations needed when applying the lemma to (5.2).
-/
theorem integral_le_measure_mul_sum
    (P : FiniteMeasurableCells X ι) (μ : Measure X)
    [IsFiniteMeasure μ]
    (f : X → ℝ) (B : ι → ℝ) (R : ι → Prop) [DecidablePred R]
    (V : ℝ)
    (hf : Integrable f μ)
    (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hB_nonneg : ∀ i ∈ P.indices, 0 ≤ B i)
    (hmajor : ∀ i ∈ P.indices, ∀ x, P.index x = i → f x ≤ B i)
    (hsupport : ∀ i ∈ P.indices, ¬R i →
      ∀ᵐ x ∂μ.restrict (P.index ⁻¹' {i}), f x = 0)
    (hvol : ∀ i ∈ P.indices,
      (μ (P.index ⁻¹' {i})).toReal ≤ V) :
    ∫ x, f x ∂μ ≤ V * ∑ i ∈ P.indices.filter R, B i := by
  have hdecomp :
      ∫ x, f x ∂μ =
        ∑ i ∈ P.indices, ∫ x in P.index ⁻¹' {i}, f x ∂μ := by
    rw [← setIntegral_univ, ← P.iUnion_fibers]
    exact integral_biUnion_finset P.indices
      (fun i _ => P.measurable_fiber i)
      P.pairwiseDisjoint
      (fun _ _ => hf.integrableOn)
  rw [hdecomp]
  calc
    (∑ i ∈ P.indices, ∫ x in P.index ⁻¹' {i}, f x ∂μ)
        = ∑ i ∈ P.indices.filter R,
            ∫ x in P.index ⁻¹' {i}, f x ∂μ := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro i hi hiR
          rw [Finset.mem_filter] at hiR
          have hnot : ¬ R i := fun hRi => hiR ⟨hi, hRi⟩
          rw [integral_congr_ae (hsupport i hi hnot), integral_zero]
    _ ≤ ∑ i ∈ P.indices.filter R,
          (μ (P.index ⁻¹' {i})).toReal * B i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).1
        have hnonneg :
            0 ≤ᵐ[μ.restrict (P.index ⁻¹' {i})] f :=
          ae_mono (Measure.restrict_le_self) hf_nonneg
        have hmaj :
            ∀ᵐ x ∂μ.restrict (P.index ⁻¹' {i}), f x ≤ B i := by
          filter_upwards [ae_restrict_mem (P.measurable_fiber i)] with x hx
          exact hmajor i hi' x hx
        calc
          (∫ x in P.index ⁻¹' {i}, f x ∂μ)
              ≤ ∫ _x in P.index ⁻¹' {i}, B i ∂μ :=
                integral_mono_ae
                  hf.integrableOn
                  integrableOn_const
                  hmaj
          _ = (μ (P.index ⁻¹' {i})).toReal * B i := by
                rw [setIntegral_const]
                simp only [smul_eq_mul, mul_comm, measureReal_def]
    _ ≤ ∑ i ∈ P.indices.filter R, V * B i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∈ P.indices := (Finset.mem_filter.mp hi).1
        exact mul_le_mul_of_nonneg_right
          (hvol i hi')
          (hB_nonneg i hi')
    _ = V * ∑ i ∈ P.indices.filter R, B i := by
        rw [Finset.mul_sum]

/-- Variant of `integral_le_measure_mul_sum` with an effective support
inside every cell.  This is the form used in (5.2): the floor cell controls
the chosen endpoint, while compact support of `η_ε` cuts the paired endpoint
down to another `O(ε)` neighbourhood.  Consequently `hvol` measures the
intersection with `active i`, not the whole (too large) floor fiber. -/
theorem integral_le_activeMeasure_mul_sum
    (P : FiniteMeasurableCells X ι) (μ : Measure X)
    [IsFiniteMeasure μ]
    (f : X → ℝ) (B : ι → ℝ) (R : ι → Prop) [DecidablePred R]
    (active : ι → Set X) (V : ℝ)
    (hf : Integrable f μ)
    (hB_nonneg : ∀ i ∈ P.indices, 0 ≤ B i)
    (hactive : ∀ i ∈ P.indices, MeasurableSet (active i))
    (hmajor : ∀ i ∈ P.indices, ∀ x,
      P.index x = i → x ∈ active i → f x ≤ B i)
    (hvanish : ∀ i ∈ P.indices,
      ∀ᵐ x ∂μ,
        x ∈ (P.index ⁻¹' {i}) \ ((P.index ⁻¹' {i}) ∩ active i) →
          f x = 0)
    (hsupport : ∀ i ∈ P.indices, ¬R i →
      ∀ᵐ x ∂μ.restrict (P.index ⁻¹' {i}), f x = 0)
    (hvol : ∀ i ∈ P.indices,
      (μ ((P.index ⁻¹' {i}) ∩ active i)).toReal ≤ V) :
    ∫ x, f x ∂μ ≤ V * ∑ i ∈ P.indices.filter R, B i := by
  have hdecomp :
      ∫ x, f x ∂μ =
        ∑ i ∈ P.indices, ∫ x in P.index ⁻¹' {i}, f x ∂μ := by
    rw [← setIntegral_univ, ← P.iUnion_fibers]
    exact integral_biUnion_finset P.indices
      (fun i _ => P.measurable_fiber i)
      P.pairwiseDisjoint
      (fun _ _ => hf.integrableOn)
  rw [hdecomp]
  calc
    (∑ i ∈ P.indices, ∫ x in P.index ⁻¹' {i}, f x ∂μ)
        = ∑ i ∈ P.indices.filter R,
            ∫ x in P.index ⁻¹' {i}, f x ∂μ := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro i hi hiR
          rw [Finset.mem_filter] at hiR
          have hnot : ¬ R i := fun hRi => hiR ⟨hi, hRi⟩
          rw [integral_congr_ae (hsupport i hi hnot), integral_zero]
    _ = ∑ i ∈ P.indices.filter R,
          ∫ x in (P.index ⁻¹' {i}) ∩ active i, f x ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ∈ P.indices := (Finset.mem_filter.mp hi).1
        exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
          (P.measurable_fiber i).nullMeasurableSet
          inter_subset_left
          (hvanish i hi')
    _ ≤ ∑ i ∈ P.indices.filter R,
          (μ ((P.index ⁻¹' {i}) ∩ active i)).toReal * B i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∈ P.indices := (Finset.mem_filter.mp hi).1
        have hset : MeasurableSet ((P.index ⁻¹' {i}) ∩ active i) :=
          (P.measurable_fiber i).inter (hactive i hi')
        have hmaj :
            ∀ᵐ x ∂μ.restrict ((P.index ⁻¹' {i}) ∩ active i),
              f x ≤ B i := by
          filter_upwards [ae_restrict_mem hset] with x hx
          exact hmajor i hi' x hx.1 hx.2
        calc
          (∫ x in (P.index ⁻¹' {i}) ∩ active i, f x ∂μ)
              ≤ ∫ _x in (P.index ⁻¹' {i}) ∩ active i, B i ∂μ :=
                integral_mono_ae
                  hf.integrableOn
                  integrableOn_const
                  hmaj
          _ = (μ ((P.index ⁻¹' {i}) ∩ active i)).toReal * B i := by
                rw [setIntegral_const]
                simp only [smul_eq_mul, mul_comm, measureReal_def]
    _ ≤ ∑ i ∈ P.indices.filter R, V * B i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ∈ P.indices := (Finset.mem_filter.mp hi).1
        exact mul_le_mul_of_nonneg_right
          (hvol i hi')
          (hB_nonneg i hi')
    _ = V * ∑ i ∈ P.indices.filter R, B i := by
        rw [Finset.mul_sum]

/-- Cell-integral form of the compression lemma.  This is the most direct
consumer of paper (5.3): once the integral over each cell is bounded, the
finite disjoint decomposition simply sums those bounds. -/
theorem integral_le_sum_of_cellIntegrals
    (P : FiniteMeasurableCells X ι) (μ : Measure X)
    (f : X → ℝ) (B : ι → ℝ) (R : ι → Prop) [DecidablePred R]
    (hf : Integrable f μ)
    (hsupport : ∀ i ∈ P.indices, ¬R i →
      ∀ᵐ x ∂μ.restrict (P.index ⁻¹' {i}), f x = 0)
    (hcell : ∀ i ∈ P.indices, R i →
      ∫ x in P.index ⁻¹' {i}, f x ∂μ ≤ B i) :
    ∫ x, f x ∂μ ≤ ∑ i ∈ P.indices.filter R, B i := by
  have hdecomp :
      ∫ x, f x ∂μ =
        ∑ i ∈ P.indices, ∫ x in P.index ⁻¹' {i}, f x ∂μ := by
    rw [← setIntegral_univ, ← P.iUnion_fibers]
    exact integral_biUnion_finset P.indices
      (fun i _ => P.measurable_fiber i)
      P.pairwiseDisjoint
      (fun _ _ => hf.integrableOn)
  rw [hdecomp]
  calc
    (∑ i ∈ P.indices, ∫ x in P.index ⁻¹' {i}, f x ∂μ)
        = ∑ i ∈ P.indices.filter R,
            ∫ x in P.index ⁻¹' {i}, f x ∂μ := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro i hi hiR
          rw [Finset.mem_filter] at hiR
          have hnot : ¬ R i := fun hRi => hiR ⟨hi, hRi⟩
          rw [integral_congr_ae (hsupport i hi hnot), integral_zero]
    _ ≤ ∑ i ∈ P.indices.filter R, B i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcell i (Finset.mem_filter.mp hi).1
          (Finset.mem_filter.mp hi).2

end FiniteMeasurableCells

/-! The concrete finite cell family used by the pairing reduction. -/

/-- Finite measurable cells indexed by copied pair labels. -/
def pairedTorusGridCells {m : ℕ} (κ : PartialPairing (Fin m))
    (ε : ℝ) (hε : 0 < ε) :
    FiniteMeasurableCells (Fin m → T4) (Fin m → Z4) where
  indices := Fintype.piFinset fun _ : Fin m => torusGrid ε
  index := pairedCellAssignment κ ε
  range_subset := pairedCellAssignment_mem_piFinset κ hε
  measurable_fiber := fun y =>
    (measurable_pairedCellAssignment κ ε) (measurableSet_singleton y)

/-! ## The `(5.5)` lattice summand -/

/-- Japanese bracket squared in the project's fixed lattice norm:
`⟨x-y⟩² = 1 + |x-y|²`. -/
def latticeBracketSq (x y : Z4) : ℝ :=
  1 + znorm (x - y) ^ 2

/-- The exact nonnegative lattice weight displayed in (5.5):
`max_{i,j} ⟨yᵢ-yⱼ⟩² · ∏ⱼ ⟨yⱼ-yⱼ₊₁⟩⁻²`.
The input is indexed by `Fin (m+1)`, so the maximum is nonempty.  In the
paper one applies this with `m+1 = 2n ≥ 4`. -/
def reductionWeight (m : ℕ) (y : Fin (m + 1) → Z4) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (m + 1) =>
      Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m + 1) =>
        latticeBracketSq (y i) (y j))) *
    ∏ j : AdjacentIndex (m + 1),
      latticeEdgeWeight (y j.1) (y (adjacentSucc j)))

theorem latticeBracketSq_nonneg (x y : Z4) :
    0 ≤ latticeBracketSq x y := by
  unfold latticeBracketSq
  positivity

theorem reductionWeight_nonneg (m : ℕ) (y : Fin (m + 1) → Z4) :
    0 ≤ reductionWeight m y := by
  unfold reductionWeight
  apply mul_nonneg
  · have hinner :
        latticeBracketSq (y 0) (y 0) ≤
          Finset.univ.sup' Finset.univ_nonempty
            (fun j : Fin (m + 1) => latticeBracketSq (y 0) (y j)) :=
      Finset.le_sup' (f := fun j : Fin (m + 1) =>
        latticeBracketSq (y 0) (y j))
        (by simp)
    have houter :
        (Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m + 1) => latticeBracketSq (y 0) (y j))) ≤
          Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (m + 1) =>
            Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m + 1) =>
              latticeBracketSq (y i) (y j))) :=
      Finset.le_sup' (f := fun i : Fin (m + 1) =>
        Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m + 1) =>
          latticeBracketSq (y i) (y j))) (by simp)
    exact (latticeBracketSq_nonneg (y 0) (y 0)).trans
      (hinner.trans houter)
  · apply Finset.prod_nonneg
    intro j _
    unfold latticeEdgeWeight
    positivity

/-- **Direct cell-integral form of `(5.2) → (5.5)`.**

This is the paper-faithful consumer of (5.3).  The hypothesis `hcell` is
exactly the estimate after integrating all variables over one copied-pair
cell; summing the disjoint floor cells produces the finite (5.5) sum.  The
constraint `y_{κ(i)} = y_i` is not assumed for actual cells: it is proved by
`pairedCellAssignment_respectsPairing`, so all other summands have empty
fibers and disappear.
-/
theorem integral_le_reductionWeight_sum_of_cellIntegrals
    (m : ℕ) (κ : PartialPairing (Fin (m + 1)))
    {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Fin (m + 1) → T4))
    (f : (Fin (m + 1) → T4) → ℝ)
    (C : ℝ)
    (hf : Integrable f μ)
    (hcell : ∀ y ∈
      Fintype.piFinset (fun _ : Fin (m + 1) => torusGrid ε),
      RespectsPairing κ y →
        ∫ x in pairedCellAssignment κ ε ⁻¹' {y}, f x ∂μ ≤
          C * reductionWeight m y) :
    ∫ x, f x ∂μ ≤
      C *
        ∑ y ∈
          (Fintype.piFinset
            (fun _ : Fin (m + 1) => torusGrid ε)).filter
              (RespectsPairing κ),
          reductionWeight m y := by
  let P := pairedTorusGridCells κ ε hε
  have hsupport :
      ∀ y ∈ P.indices, ¬RespectsPairing κ y →
        ∀ᵐ x ∂μ.restrict (P.index ⁻¹' {y}), f x = 0 := by
    intro y hy hnot
    filter_upwards [ae_restrict_mem (P.measurable_fiber y)] with x hx
    have heq : pairedCellAssignment κ ε x = y := by
      simpa only [P, pairedTorusGridCells, Set.mem_preimage,
        Set.mem_singleton_iff] using hx
    exact False.elim (hnot (by
      rw [← heq]
      exact pairedCellAssignment_respectsPairing κ ε x))
  have hbound := P.integral_le_sum_of_cellIntegrals μ f
    (fun y => C * reductionWeight m y) (RespectsPairing κ)
    hf hsupport
    (by simpa only [P, pairedTorusGridCells] using hcell)
  calc
    (∫ x, f x ∂μ) ≤
        ∑ y ∈ P.indices.filter (RespectsPairing κ),
          C * reductionWeight m y := hbound
    _ = C *
        ∑ y ∈
          (Fintype.piFinset
            (fun _ : Fin (m + 1) => torusGrid ε)).filter
              (RespectsPairing κ),
          reductionWeight m y := by
      simp only [P, pairedTorusGridCells]
      rw [Finset.mul_sum]

/-- **Reusable `(5.2) → (5.5)` compression.**

For `2n = m+1` variables, assume the analytic work has provided:

* an effective support `active y` inside each copied-pair cell;
* a uniform active-cell measure bound `V`;
* the pointwise cell bound `f ≤ C · reductionWeight`.

Then the continuous integral is bounded by the exact finite lattice sum
from (5.5), restricted by `y_{κ(i)} = y_i`.  Measurability, integrability,
support-vanishing, and cell-volume hypotheses are all explicit.  In the
paper, compact support of `η_ε` supplies `active` (see
`pairedCellConstraints_of_covariance_ne_zero`) and (5.3)--(5.4) supply the
pointwise/volume ledger.
-/
theorem integral_le_reductionWeight_latticeSum
    (m : ℕ) (κ : PartialPairing (Fin (m + 1)))
    {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (Fin (m + 1) → T4)) [IsFiniteMeasure μ]
    (f : (Fin (m + 1) → T4) → ℝ)
    (active : (Fin (m + 1) → Z4) → Set (Fin (m + 1) → T4))
    (C V : ℝ)
    (hf : Integrable f μ)
    (hC : 0 ≤ C)
    (hactive : ∀ y ∈
      Fintype.piFinset (fun _ : Fin (m + 1) => torusGrid ε),
      MeasurableSet (active y))
    (hmajor : ∀ y ∈
      Fintype.piFinset (fun _ : Fin (m + 1) => torusGrid ε),
      ∀ x, pairedCellAssignment κ ε x = y → x ∈ active y →
        f x ≤ C * reductionWeight m y)
    (hvanish : ∀ y ∈
      Fintype.piFinset (fun _ : Fin (m + 1) => torusGrid ε),
      ∀ᵐ x ∂μ,
        x ∈ (pairedCellAssignment κ ε ⁻¹' {y}) \
            ((pairedCellAssignment κ ε ⁻¹' {y}) ∩ active y) →
          f x = 0)
    (hvol : ∀ y ∈
      Fintype.piFinset (fun _ : Fin (m + 1) => torusGrid ε),
      (μ ((pairedCellAssignment κ ε ⁻¹' {y}) ∩ active y)).toReal ≤ V) :
    ∫ x, f x ∂μ ≤
      (V * C) *
        ∑ y ∈
          (Fintype.piFinset
            (fun _ : Fin (m + 1) => torusGrid ε)).filter
              (RespectsPairing κ),
          reductionWeight m y := by
  let P := pairedTorusGridCells κ ε hε
  have hsupport :
      ∀ y ∈ P.indices, ¬RespectsPairing κ y →
        ∀ᵐ x ∂μ.restrict (P.index ⁻¹' {y}), f x = 0 := by
    intro y hy hnot
    filter_upwards [ae_restrict_mem (P.measurable_fiber y)] with x hx
    have heq : pairedCellAssignment κ ε x = y := by
      simpa only [P, pairedTorusGridCells, Set.mem_preimage,
        Set.mem_singleton_iff] using hx
    exact False.elim (hnot (by
      rw [← heq]
      exact pairedCellAssignment_respectsPairing κ ε x))
  have hbound := P.integral_le_activeMeasure_mul_sum μ f
    (fun y => C * reductionWeight m y) (RespectsPairing κ)
    active V hf
    (fun y _ => mul_nonneg hC (reductionWeight_nonneg m y))
    (by simpa only [P, pairedTorusGridCells] using hactive)
    (by simpa only [P, pairedTorusGridCells] using hmajor)
    (by simpa only [P, pairedTorusGridCells] using hvanish)
    hsupport
    (by simpa only [P, pairedTorusGridCells] using hvol)
  calc
    (∫ x, f x ∂μ) ≤
        V * ∑ y ∈ P.indices.filter (RespectsPairing κ),
          C * reductionWeight m y := hbound
    _ = (V * C) *
        ∑ y ∈
          (Fintype.piFinset
            (fun _ : Fin (m + 1) => torusGrid ε)).filter
              (RespectsPairing κ),
          reductionWeight m y := by
      simp only [P, pairedTorusGridCells]
      rw [← Finset.mul_sum]
      ring

end

end Anderson4D
