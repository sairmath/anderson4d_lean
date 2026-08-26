import Anderson4D.Continuum.CellSingular
import Anderson4D.Continuum.PeriodizedCovariance

/-!
# Periodic-boundary bridge for the continuum cell decomposition

The canonical floor index of a torus point jumps at the boundary of the
fundamental cube.  Consequently, covariance support never implies equality
of the two canonical floor indices.  This file instead works with the
Euclidean representative supplied by `PairedCellConstraint`: it floors that
representative, proves that the represented torus point lies in the resulting
lattice-centred neighbourhood, and proves a quantitative no-wrapping
criterion for the two lattice centres.

The criterion is deliberately geometric.  No singular-integral or lattice
sum estimate is included in its assumptions.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Set

/-! ## Exact no-wrap criterion for one lattice edge -/

/-- Coordinatewise half-period condition for the Euclidean displacement
between two lattice representatives. -/
def LatticeEdgeNoWrap (ε : ℝ) (y y' : Z4) : Prop :=
  ∀ i : Fin dim, |ε * ((y - y') i : ℝ)| ≤ Real.pi

/-- Under the half-period condition, quotienting the two Euclidean lattice
centres does not shorten their distance. -/
theorem latticeTorusCenter_dist_eq_of_edgeNoWrap
    {ε : ℝ} (hε : 0 < ε) {y y' : Z4}
    (h : LatticeEdgeNoWrap ε y y') :
    dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
      ε * znorm (y - y') := by
  calc
    dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
        ‖latticeTorusCenter ε y - latticeTorusCenter ε y'‖ :=
      dist_eq_norm _ _
    _ = ‖cellRepresentative ε y - cellRepresentative ε y'‖ := by
      simp only [Pi.norm_def]
      congr 1
      apply Finset.sup_congr rfl
      intro i _
      apply NNReal.eq
      simp only [coe_nnnorm]
      change ‖((ε * (y i : ℝ) - ε * (y' i : ℝ) : ℝ) :
          AddCircle (2 * Real.pi))‖ =
        ‖ε * (y i : ℝ) - ε * (y' i : ℝ)‖
      rw [Real.norm_eq_abs]
      rw [AddCircle.norm_coe_eq_abs_iff (p := 2 * Real.pi)
        (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
      have hi := h i
      simp only [abs_mul, abs_of_pos hε, Int.cast_sub, Pi.sub_apply,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        mul_div_cancel_left₀ Real.pi (by norm_num : (2 : ℝ) ≠ 0)] at hi ⊢
      simpa only [← mul_sub, abs_mul, abs_of_pos hε] using hi
    _ = |ε| * znorm (y - y') :=
      norm_cellRepresentative_sub ε y y'
    _ = ε * znorm (y - y') := by rw [abs_of_pos hε]

/-- A sup-norm bound is a convenient sufficient form of the coordinatewise
half-period condition. -/
theorem latticeEdgeNoWrap_of_scale_mul_znorm_le_pi
    {ε : ℝ} (hε : 0 ≤ ε) {y y' : Z4}
    (h : ε * znorm (y - y') ≤ Real.pi) :
    LatticeEdgeNoWrap ε y y' := by
  intro i
  rw [abs_mul, abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left
    (show |((y - y') i : ℝ)| ≤ znorm (y - y') by
      simpa only [znorm, Real.norm_eq_abs] using
        norm_le_pi_norm (fun j => (((y - y') j : ℤ) : ℝ)) i)
    hε |>.trans h

/-- The form consumed directly by `invSqKer_latticeCellEdge_le`. -/
theorem latticeTorusCenter_dist_eq_of_scale_mul_znorm_le_pi
    {ε : ℝ} (hε : 0 < ε) {y y' : Z4}
    (h : ε * znorm (y - y') ≤ Real.pi) :
    dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
      ε * znorm (y - y') :=
  latticeTorusCenter_dist_eq_of_edgeNoWrap hε
    (latticeEdgeNoWrap_of_scale_mul_znorm_le_pi hε.le h)

/-! ## Recursive adapters for the existing chain interfaces -/

/-- Every consecutive displacement in a lattice path is at most one
half-period after multiplication by the mesh. -/
def LatticeCellPathWithinHalfPeriod
    (ε : ℝ) (y : Z4) : List Z4 → Prop
  | [] => True
  | y' :: ys =>
      ε * znorm (y - y') ≤ Real.pi ∧
        LatticeCellPathWithinHalfPeriod ε y' ys

/-- The quantitative half-period predicate supplies exactly the geometric
hypothesis required by `integratedLatticeCellChain_le`. -/
theorem LatticeCellPathWithinHalfPeriod.toNoWrap
    {ε : ℝ} (hε : 0 < ε) {y : Z4} {ys : List Z4}
    (h : LatticeCellPathWithinHalfPeriod ε y ys) :
    LatticeCellPathNoWrap ε y ys := by
  induction ys generalizing y with
  | nil => trivial
  | cons y' ys ih =>
      exact ⟨latticeTorusCenter_dist_eq_of_scale_mul_znorm_le_pi hε h.1,
        ih h.2⟩

/-- Half-period version of the far-terminal path predicate.  Unlike
`LatticeTerminalPathFar`, all geometric premises are expressed directly in
the Euclidean lattice norm. -/
def LatticeTerminalPathWithinHalfPeriod
    (ε R : ℝ) (y e : Z4) : List Z4 → Prop
  | [] =>
      ε * znorm (y - e) ≤ Real.pi ∧
        4 * R ≤ znorm (y - e)
  | y' :: ys =>
      ε * znorm (y - y') ≤ Real.pi ∧
        LatticeTerminalPathWithinHalfPeriod ε R y' e ys

/-- Adapter from the quantitative terminal-path condition to the existing
far-terminal chain interface. -/
theorem LatticeTerminalPathWithinHalfPeriod.toTerminalPathFar
    {ε R : ℝ} (hε : 0 < ε) {y e : Z4} {ys : List Z4}
    (h : LatticeTerminalPathWithinHalfPeriod ε R y e ys) :
    LatticeTerminalPathFar ε R y e ys := by
  induction ys generalizing y with
  | nil =>
      exact ⟨latticeTorusCenter_dist_eq_of_scale_mul_znorm_le_pi hε h.1,
        h.2⟩
  | cons y' ys ih =>
      exact ⟨latticeTorusCenter_dist_eq_of_scale_mul_znorm_le_pi hε h.1,
        ih h.2⟩

/-! ## Euclidean representatives and lattice neighbourhoods -/

@[simp] theorem periodizeR4_sub (x x' : R4) :
    periodizeR4 (x - x') = periodizeR4 x - periodizeR4 x' := by
  funext i
  rfl

theorem periodizeR4_torusLift (z : T4) :
    periodizeR4 (torusLift z) = z := by
  funext i
  exact AddCircle.coe_equivIco

/-- The coordinatewise quotient map is distance non-increasing for the
fixed sup norms. -/
theorem dist_periodizeR4_le_norm_sub (x x' : R4) :
    dist (periodizeR4 x) (periodizeR4 x') ≤ ‖x - x'‖ := by
  rw [dist_eq_norm, ← periodizeR4_sub]
  exact SmoothCutoff.norm_periodizeR4_le _

/-- The first endpoint of a paired-cell constraint lies in the radius-one
lattice neighbourhood of the recorded cell. -/
theorem PairedCellConstraint.first_mem_latticeCellNeighborhood
    {ρ : SmoothCutoff} {ε : ℝ} (hε : 0 < ε)
    {z w : T4} {y : Z4} (h : PairedCellConstraint ρ ε z w y) :
    z ∈ latticeCellNeighborhood ε 1 y := by
  have hnear :
      ‖torusLift z - cellRepresentative ε y‖ < ε := by
    have hbase := norm_sub_cellRepresentative_lt hε (torusLift z)
    rw [show floorCell ε (torusLift z) = y from h.first_cell] at hbase
    exact hbase
  unfold latticeCellNeighborhood latticeTorusCenter
  rw [Metric.mem_ball]
  calc
    dist z (periodizeR4 (cellRepresentative ε y)) =
        dist (periodizeR4 (torusLift z))
          (periodizeR4 (cellRepresentative ε y)) := by
            rw [periodizeR4_torusLift]
    _ ≤ ‖torusLift z - cellRepresentative ε y‖ :=
      dist_periodizeR4_le_norm_sub _ _
    _ < 1 * ε := by simpa using hnear

/-- The supported paired endpoint lies in the enlarged neighbourhood of the
same recorded lattice cell.  This is the boundary-safe substitute for the
false assertion that both canonical floor indices are equal. -/
theorem PairedCellConstraint.second_mem_latticeCellNeighborhood
    {ρ : SmoothCutoff} {ε : ℝ} (hε : 0 < ε)
    {z w : T4} {y : Z4} (h : PairedCellConstraint ρ ε z w y) :
    w ∈ latticeCellNeighborhood ε (1 + 2 * ρ.radius) y := by
  obtain ⟨wrep, hwrep, hnear⟩ :=
    h.exists_representative_near_cell hε
  unfold latticeCellNeighborhood latticeTorusCenter
  rw [Metric.mem_ball]
  calc
    dist w (periodizeR4 (cellRepresentative ε y)) =
        dist (periodizeR4 wrep)
          (periodizeR4 (cellRepresentative ε y)) := by rw [hwrep]
    _ ≤ ‖wrep - cellRepresentative ε y‖ :=
      dist_periodizeR4_le_norm_sub _ _
    _ < (1 + 2 * ρ.radius) * ε := hnear

/-- Both paired endpoints lie in one common enlarged lattice
neighbourhood. -/
theorem PairedCellConstraint.endpoints_mem_latticeCellNeighborhood
    {ρ : SmoothCutoff} {ε : ℝ} (hε : 0 < ε)
    {z w : T4} {y : Z4} (h : PairedCellConstraint ρ ε z w y) :
    z ∈ latticeCellNeighborhood ε (1 + 2 * ρ.radius) y ∧
      w ∈ latticeCellNeighborhood ε (1 + 2 * ρ.radius) y := by
  constructor
  · have hz := h.first_mem_latticeCellNeighborhood hε
    unfold latticeCellNeighborhood at hz ⊢
    rw [Metric.mem_ball] at hz ⊢
    have hr : 0 < ρ.radius := ρ.radius_pos
    nlinarith
  · exact h.second_mem_latticeCellNeighborhood hε

/-! ## Flooring the boundary-safe representative -/

/-- Flooring the chosen Euclidean representative of the paired endpoint
produces a genuine lattice cell containing that endpoint, and its index is
within a cutoff-dependent bounded displacement of the first index. -/
theorem PairedCellConstraint.exists_floored_representative
    {ρ : SmoothCutoff} {ε : ℝ} (hε : 0 < ε)
    {z w : T4} {y : Z4} (h : PairedCellConstraint ρ ε z w y) :
    ∃ (y' : Z4) (wrep : R4),
      periodizeR4 wrep = w ∧
      floorCell ε wrep = y' ∧
      w ∈ latticeCellNeighborhood ε 1 y' ∧
      znorm (y - y') < 2 + 2 * ρ.radius := by
  obtain ⟨wrep, hwrep, hwnear⟩ :=
    h.exists_representative_near_cell hε
  let y' : Z4 := floorCell ε wrep
  have hcell :
      ‖wrep - cellRepresentative ε y'‖ < ε := by
    exact norm_sub_cellRepresentative_lt hε wrep
  have hcentres :
      ε * znorm (y - y') < ε * (2 + 2 * ρ.radius) := by
    calc
      ε * znorm (y - y') =
          ‖cellRepresentative ε y - cellRepresentative ε y'‖ := by
            rw [norm_cellRepresentative_sub, abs_of_pos hε]
      _ = ‖(cellRepresentative ε y - wrep) +
            (wrep - cellRepresentative ε y')‖ := by
          congr 1
          abel
      _ ≤ ‖cellRepresentative ε y - wrep‖ +
            ‖wrep - cellRepresentative ε y'‖ :=
          norm_add_le _ _
      _ < (1 + 2 * ρ.radius) * ε + ε := by
          exact add_lt_add (by simpa only [norm_sub_rev] using hwnear) hcell
      _ = ε * (2 + 2 * ρ.radius) := by ring
  have hindex : znorm (y - y') < 2 + 2 * ρ.radius := by
    nlinarith
  refine ⟨y', wrep, hwrep, rfl, ?_, hindex⟩
  unfold latticeCellNeighborhood latticeTorusCenter
  rw [Metric.mem_ball]
  calc
    dist w (periodizeR4 (cellRepresentative ε y')) =
        dist (periodizeR4 wrep)
          (periodizeR4 (cellRepresentative ε y')) := by rw [hwrep]
    _ ≤ ‖wrep - cellRepresentative ε y'‖ :=
      dist_periodizeR4_le_norm_sub _ _
    _ < 1 * ε := by simpa using hcell

/-- At scales below the explicit half-period threshold, the first cell and
the floored boundary-safe representative form an exact no-wrap edge.  The
conclusion is in the form consumed by
`invSqKer_latticeCellEdge_le`. -/
theorem PairedCellConstraint.exists_floored_representative_noWrap
    {ρ : SmoothCutoff} {ε : ℝ} (hε : 0 < ε)
    (hscale : ε * (2 + 2 * ρ.radius) ≤ Real.pi)
    {z w : T4} {y : Z4} (h : PairedCellConstraint ρ ε z w y) :
    ∃ y' : Z4,
      w ∈ latticeCellNeighborhood ε 1 y' ∧
      znorm (y - y') < 2 + 2 * ρ.radius ∧
      dist (latticeTorusCenter ε y) (latticeTorusCenter ε y') =
        ε * znorm (y - y') := by
  obtain ⟨y', _wrep, _hwrep, _hfloor, hwcell, hclose⟩ :=
    h.exists_floored_representative hε
  refine ⟨y', hwcell, hclose,
    latticeTorusCenter_dist_eq_of_scale_mul_znorm_le_pi hε ?_⟩
  exact (mul_le_mul_of_nonneg_left hclose.le hε.le).trans hscale

/-! ## Direct consumption by the singular-cell estimates -/

/-- One covariance-supported pair, floored through its boundary-safe
representative, supplies a legitimate invocation of
`invSqKer_latticeCellEdge_le`.  The theorem returns the chosen cell because
the canonical floor cell of `w` is intentionally not used. -/
theorem invSqKer_pairedFlooredCellEdge_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : SmoothCutoff) (ε : ℝ) (_hε : 0 < ε),
        ε * (2 + 2 * ρ.radius) ≤ Real.pi →
        ∀ (z w : T4) (y : Z4),
          PairedCellConstraint ρ ε z w y →
          ∃ y' : Z4,
            w ∈ latticeCellNeighborhood ε 1 y' ∧
            znorm (y - y') < 2 + 2 * ρ.radius ∧
            (∫ u in latticeCellNeighborhood ε 1 y',
                invSqKer (z - u) ∂paperMeasure) ≤
              C * (1 ^ 2 + 1 ^ 4) * ε ^ 2 *
                latticeEdgeWeight y y' := by
  obtain ⟨C, hC, hedge⟩ := invSqKer_latticeCellEdge_le
  refine ⟨C, hC, ?_⟩
  intro ρ ε hε hscale z w y hpair
  obtain ⟨y', hwcell, hclose, hcenter⟩ :=
    hpair.exists_floored_representative_noWrap hε hscale
  refine ⟨y', hwcell, hclose, ?_⟩
  exact hedge ε 1 hε (by norm_num) y y' z hcenter
    (hpair.first_mem_latticeCellNeighborhood hε)

/-- `integratedLatticeCellChain_le` with its no-wrap premise discharged by
the checkable half-period inequalities. -/
theorem integratedLatticeCellChain_le_of_withinHalfPeriod :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y : Z4) (ys : List Z4) (x : T4),
        LatticeCellPathWithinHalfPeriod ε y ys →
        x ∈ latticeCellNeighborhood ε R y →
        integratedCellChain (R * ε) x
            (ys.map (latticeTorusCenter ε)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ ys.length *
            ε ^ (2 * ys.length) * latticeCellPathWeight y ys := by
  obtain ⟨C, hC, hchain⟩ := integratedLatticeCellChain_le
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y ys x hhalf hx
  exact hchain ε R hε hR y ys x (hhalf.toNoWrap hε) hx

/-- Far-terminal analogue of
`integratedLatticeCellChain_le_of_withinHalfPeriod`. -/
theorem terminalLatticeCellChain_le_of_withinHalfPeriod :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ε R : ℝ) (_hε : 0 < ε) (_hR : 0 < R)
        (y e : Z4) (ys : List Z4) (x z : T4),
        x ∈ latticeCellNeighborhood ε R y →
        z ∈ latticeCellNeighborhood ε R e →
        LatticeTerminalPathWithinHalfPeriod ε R y e ys →
        terminalCellChain (R * ε) x z
            (ys.map (latticeTorusCenter ε)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ ys.length *
            ε ^ (2 * ys.length) *
            (terminalRadiusFactor R * (ε ^ 2)⁻¹) *
            latticeTerminalPathWeight y e ys := by
  obtain ⟨C, hC, hchain⟩ := terminalLatticeCellChain_le_of_far
  refine ⟨C, hC, ?_⟩
  intro ε R hε hR y e ys x z hx hz hhalf
  exact hchain ε R hε hR y e ys x z hx hz
    (hhalf.toTerminalPathFar hε)

/-! ## Exact index translations on a period-compatible mesh -/

/-- Translating a lattice index by `q` cells in each chosen coordinate. -/
def translateCellIndex (q : ℤ) (k y : Z4) : Z4 :=
  fun i => y i + q * k i

/-- Compatibility condition saying that exactly `q` mesh cells make one
torus period.  It is intended for a mesh `δ = 2π/q`; the covariance scale
may remain an arbitrary nearby positive real. -/
structure PeriodCompatibleMesh (δ : ℝ) (q : ℤ) : Prop where
  cellCount_pos : 0 < q
  period_eq : δ * (q : ℝ) = 2 * Real.pi

/-- Number of cells in the compatible mesh selected at covariance scale
`ε`. -/
def compatibleCellCount (ε : ℝ) : ℤ :=
  ⌈(2 * Real.pi) / ε⌉

/-- Mesh size `2π/q`, where `q = ⌈2π/ε⌉`.  Unlike using `ε` itself as
the mesh, this makes the discrete grid exactly periodic while staying
comparable to `ε`. -/
def compatibleMeshSize (ε : ℝ) : ℝ :=
  (2 * Real.pi) / (compatibleCellCount ε : ℝ)

theorem compatibleCellCount_pos
    {ε : ℝ} (hε : 0 < ε) :
    0 < compatibleCellCount ε := by
  apply Int.ceil_pos.mpr
  positivity

theorem compatibleMesh_isPeriodCompatible
    {ε : ℝ} (hε : 0 < ε) :
    PeriodCompatibleMesh (compatibleMeshSize ε)
      (compatibleCellCount ε) := by
  refine ⟨compatibleCellCount_pos hε, ?_⟩
  unfold compatibleMeshSize
  have hq : (compatibleCellCount ε : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (compatibleCellCount_pos hε))
  field_simp [hq]

theorem compatibleMeshSize_pos
    {ε : ℝ} (hε : 0 < ε) :
    0 < compatibleMeshSize ε := by
  unfold compatibleMeshSize
  have hq : 0 < (compatibleCellCount ε : ℝ) := by
    exact_mod_cast compatibleCellCount_pos hε
  positivity

/-- The compatible mesh is no coarser than the covariance scale. -/
theorem compatibleMeshSize_le
    {ε : ℝ} (hε : 0 < ε) :
    compatibleMeshSize ε ≤ ε := by
  have hq : 0 < (compatibleCellCount ε : ℝ) := by
    exact_mod_cast compatibleCellCount_pos hε
  have hceil :
      (2 * Real.pi) / ε ≤ (compatibleCellCount ε : ℝ) :=
    Int.le_ceil _
  have hperiod :
      2 * Real.pi ≤ ε * (compatibleCellCount ε : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hceil hε.le
    field_simp [ne_of_gt hε] at hmul
    simpa only [mul_comm] using hmul
  unfold compatibleMeshSize
  exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hperiod)

/-- For the theorem regime `ε ≤ 1`, the covariance scale is less than
twice the compatible mesh size.  Thus changing meshes only enlarges the
fixed cell-neighbourhood constant. -/
theorem lt_two_mul_compatibleMeshSize
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε < 2 * compatibleMeshSize ε := by
  have hq : 0 < (compatibleCellCount ε : ℝ) := by
    exact_mod_cast compatibleCellCount_pos hε
  have hceil :
      (compatibleCellCount ε : ℝ) <
        (2 * Real.pi) / ε + 1 :=
    Int.ceil_lt_add_one _
  have hmul := mul_lt_mul_of_pos_right hceil hε
  have hqε :
      (compatibleCellCount ε : ℝ) * ε < 2 * Real.pi + ε := by
    field_simp [ne_of_gt hε] at hmul
    nlinarith
  have hεpi : ε < 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hqεfour :
      (compatibleCellCount ε : ℝ) * ε < 4 * Real.pi := by
    nlinarith
  unfold compatibleMeshSize
  rw [show 2 * (2 * Real.pi / (compatibleCellCount ε : ℝ)) =
    (4 * Real.pi) / (compatibleCellCount ε : ℝ) by ring]
  apply (lt_div_iff₀ hq).mpr
  nlinarith

/-- Translating by a whole number of period-cell blocks does not change the
torus centre. -/
theorem latticeTorusCenter_translateCellIndex
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    (k y : Z4) :
    latticeTorusCenter δ (translateCellIndex q k y) =
      latticeTorusCenter δ y := by
  funext i
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨k i, ?_⟩
  simp only [cellRepresentative, translateCellIndex, Int.cast_add,
    Int.cast_mul, zsmul_eq_mul]
  rw [← hq.period_eq]
  ring

/-- The period-block translate of `y'` nearest to `y`, coordinatewise. -/
def nearestPeriodTranslate (q : ℤ) (y y' : Z4) : Z4 :=
  translateCellIndex q
    (fun i => round ((((y - y') i : ℤ) : ℝ) / (q : ℝ))) y'

/-- A nearest period-block translate is always inside the half-period
window around the reference index. -/
theorem nearestPeriodTranslate_edgeNoWrap
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    (y y' : Z4) :
    LatticeEdgeNoWrap δ y (nearestPeriodTranslate q y y') := by
  intro i
  let a : ℝ := (((y - y') i : ℤ) : ℝ)
  let k : ℤ := round (a / (q : ℝ))
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq.cellCount_pos
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqreal
  have hround : |a / (q : ℝ) - (k : ℝ)| ≤ (1 : ℝ) / 2 := by
    exact abs_sub_round (a / (q : ℝ))
  have hcoord :
      (((y - nearestPeriodTranslate q y y') i : ℤ) : ℝ) =
        a - (q : ℝ) * (k : ℝ) := by
    simp only [nearestPeriodTranslate, translateCellIndex, Pi.sub_apply,
      Int.cast_sub, Int.cast_add, Int.cast_mul, a, k]
    ring
  have halgebra :
      δ * (a - (q : ℝ) * (k : ℝ)) =
        (δ * (q : ℝ)) * (a / (q : ℝ) - (k : ℝ)) := by
    field_simp [hqne]
  rw [hcoord, halgebra, hq.period_eq, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  calc
    2 * Real.pi * |a / (q : ℝ) - (k : ℝ)|
        ≤ 2 * Real.pi * ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hround (by positivity)
    _ = Real.pi := by ring

/-- The nearest translate represents the same torus centre as the original
index. -/
theorem latticeTorusCenter_nearestPeriodTranslate
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    (y y' : Z4) :
    latticeTorusCenter δ (nearestPeriodTranslate q y y') =
      latticeTorusCenter δ y' :=
  latticeTorusCenter_translateCellIndex hq _ _

/-- Every edge on a compatible mesh admits a centre-preserving lattice
representative satisfying the exact distance identity required by the
cell estimates. -/
theorem exists_periodTranslate_dist_eq
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    (y y' : Z4) :
    ∃ y'' : Z4,
      latticeTorusCenter δ y'' = latticeTorusCenter δ y' ∧
      dist (latticeTorusCenter δ y) (latticeTorusCenter δ y'') =
        δ * znorm (y - y'') := by
  have hδ : 0 < δ := by
    have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq.cellCount_pos
    nlinarith [hq.period_eq, Real.pi_pos]
  refine ⟨nearestPeriodTranslate q y y',
    latticeTorusCenter_nearestPeriodTranslate hq y y', ?_⟩
  exact latticeTorusCenter_dist_eq_of_edgeNoWrap hδ
    (nearestPeriodTranslate_edgeNoWrap hq y y')

/-! ## Centre-preserving unwrapping of complete paths -/

/-- Recursively choose, for each original path vertex, the period-block
translate nearest to the previously chosen vertex. -/
def unwrapLatticePath (q : ℤ) (y : Z4) : List Z4 → List Z4
  | [] => []
  | y' :: ys =>
      let y'' := nearestPeriodTranslate q y y'
      y'' :: unwrapLatticePath q y'' ys

@[simp] theorem unwrapLatticePath_length
    (q : ℤ) (y : Z4) (ys : List Z4) :
    (unwrapLatticePath q y ys).length = ys.length := by
  induction ys generalizing y with
  | nil => rfl
  | cons y' ys ih =>
      simp only [unwrapLatticePath, List.length_cons]
      rw [ih]

/-- Unwrapping changes lattice labels but not the corresponding list of
torus centres. -/
theorem unwrapLatticePath_map_centers
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    (y : Z4) (ys : List Z4) :
    (unwrapLatticePath q y ys).map (latticeTorusCenter δ) =
      ys.map (latticeTorusCenter δ) := by
  induction ys generalizing y with
  | nil => rfl
  | cons y' ys ih =>
      simp only [unwrapLatticePath, List.map_cons]
      rw [latticeTorusCenter_nearestPeriodTranslate hq y y', ih]

/-- Every recursively unwrapped path satisfies the exact no-wrap predicate,
with no condition on the original canonical indices. -/
theorem unwrapLatticePath_noWrap
    {δ : ℝ} {q : ℤ} (hq : PeriodCompatibleMesh δ q)
    (y : Z4) (ys : List Z4) :
    LatticeCellPathNoWrap δ y (unwrapLatticePath q y ys) := by
  have hδ : 0 < δ := by
    have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq.cellCount_pos
    nlinarith [hq.period_eq, Real.pi_pos]
  induction ys generalizing y with
  | nil => trivial
  | cons y' ys ih =>
      exact ⟨latticeTorusCenter_dist_eq_of_edgeNoWrap hδ
          (nearestPeriodTranslate_edgeNoWrap hq y y'),
        ih (nearestPeriodTranslate q y y')⟩

/-- On a period-compatible mesh, the arbitrary torus-centre path is
therefore covered by `integratedLatticeCellChain_le`; only its lattice
weight is evaluated on the centre-preserving unwrapped labels. -/
theorem integratedLatticeCellChain_le_unwrapped :
    ∃ C : ℝ, 0 < C ∧
      ∀ (δ R : ℝ) (q : ℤ)
        (_hq : PeriodCompatibleMesh δ q) (_hR : 0 < R)
        (y : Z4) (ys : List Z4) (x : T4),
        x ∈ latticeCellNeighborhood δ R y →
        integratedCellChain (R * δ) x
            (ys.map (latticeTorusCenter δ)) ≤
          (C * (R ^ 2 + R ^ 4)) ^ ys.length *
            δ ^ (2 * ys.length) *
            latticeCellPathWeight y (unwrapLatticePath q y ys) := by
  obtain ⟨C, hC, hchain⟩ := integratedLatticeCellChain_le
  refine ⟨C, hC, ?_⟩
  intro δ R q hq hR y ys x hx
  have hδ : 0 < δ := by
    have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq.cellCount_pos
    nlinarith [hq.period_eq, Real.pi_pos]
  have hbound := hchain δ R hδ hR y
    (unwrapLatticePath q y ys) x (unwrapLatticePath_noWrap hq y ys) hx
  rw [unwrapLatticePath_map_centers hq y ys,
    unwrapLatticePath_length] at hbound
  exact hbound

/-! ## Covariance support on the compatible mesh -/

/-- Covariance support and an independently chosen positive mesh give a
boundary-safe representative of the paired endpoint.  Its distance to the
first mesh cell is `δ + 2Rε`, separating the mesh and covariance scales. -/
theorem SmoothCutoff.exists_representative_near_meshCell_of_etaEpsT4_ne_zero
    (ρ : SmoothCutoff) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (z w : T4) (y : Z4)
    (hzcell : torusFloorCell δ z = y)
    (hη : ρ.etaEpsT4 ε (z - w) ≠ 0) :
    ∃ wrep : R4,
      periodizeR4 wrep = w ∧
      ‖wrep - cellRepresentative δ y‖ <
        δ + 2 * ρ.radius * ε := by
  obtain ⟨k, hk⟩ :=
    ρ.exists_periodicDisplacement_of_etaEpsT4_ne_zero hε.ne' hη
  rw [abs_of_pos hε] at hk
  let wrep := pairedEuclideanRepresentative z w k
  refine ⟨wrep, periodizeR4_pairedEuclideanRepresentative z w k, ?_⟩
  have hznear :
      ‖torusLift z - cellRepresentative δ y‖ < δ := by
    have hbase := norm_sub_cellRepresentative_lt hδ (torusLift z)
    rw [show floorCell δ (torusLift z) = y from hzcell] at hbase
    exact hbase
  calc
    ‖wrep - cellRepresentative δ y‖ =
        ‖(torusLift z - cellRepresentative δ y) -
          periodicDisplacement (z - w) k‖ := by
            congr 1
            unfold wrep pairedEuclideanRepresentative
            abel
    _ ≤ ‖torusLift z - cellRepresentative δ y‖ +
          ‖periodicDisplacement (z - w) k‖ :=
      norm_sub_le _ _
    _ < δ + 2 * ρ.radius * ε := add_lt_add hznear hk

/-- At the compatible mesh `δ = 2π/⌈2π/ε⌉`, both endpoints of a nonzero
covariance factor lie in one common cell neighbourhood with the fixed
radius factor `1 + 4R`.  This is valid for every real `0 < ε ≤ 1`; no
commensurability assumption is placed on the covariance scale itself. -/
theorem SmoothCutoff.etaEpsT4_pair_mem_compatibleCellNeighborhood
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (z w : T4) (hη : ρ.etaEpsT4 ε (z - w) ≠ 0) :
    let δ := compatibleMeshSize ε
    let y := torusFloorCell δ z
    z ∈ latticeCellNeighborhood δ (1 + 4 * ρ.radius) y ∧
      w ∈ latticeCellNeighborhood δ (1 + 4 * ρ.radius) y := by
  dsimp only
  let δ := compatibleMeshSize ε
  let y := torusFloorCell δ z
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hεδ : ε < 2 * δ := lt_two_mul_compatibleMeshSize hε hε1
  obtain ⟨wrep, hwrep, hwnear⟩ :=
    ρ.exists_representative_near_meshCell_of_etaEpsT4_ne_zero
      hε hδ z w y rfl hη
  have hznear :
      ‖torusLift z - cellRepresentative δ y‖ < δ := by
    exact norm_sub_cellRepresentative_lt hδ (torusLift z)
  constructor
  · unfold latticeCellNeighborhood latticeTorusCenter
    rw [Metric.mem_ball]
    calc
      dist z (periodizeR4 (cellRepresentative δ y)) =
          dist (periodizeR4 (torusLift z))
            (periodizeR4 (cellRepresentative δ y)) := by
              rw [periodizeR4_torusLift]
      _ ≤ ‖torusLift z - cellRepresentative δ y‖ :=
        dist_periodizeR4_le_norm_sub _ _
      _ < (1 + 4 * ρ.radius) * δ := by
        nlinarith [ρ.radius_pos]
  · unfold latticeCellNeighborhood latticeTorusCenter
    rw [Metric.mem_ball]
    calc
      dist w (periodizeR4 (cellRepresentative δ y)) =
          dist (periodizeR4 wrep)
            (periodizeR4 (cellRepresentative δ y)) := by rw [hwrep]
      _ ≤ ‖wrep - cellRepresentative δ y‖ :=
        dist_periodizeR4_le_norm_sub _ _
      _ < (1 + 4 * ρ.radius) * δ := by
        have hr := ρ.radius_pos
        nlinarith

end

end Anderson4D
