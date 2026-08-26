import Anderson4D.Continuum.PrimitiveCopiedLabels

/-!
# Boundary-safe copied-cell reduction for the primitive integral

The canonical labels used in paper §5.1 live in one fundamental box.  Across
the cut of that box, ordinary differences of labels do not represent torus
distances.  This file therefore keeps the literal copied labels and records
the analytic cell estimate with the corresponding periodic edge weight.

No endpoint translation is discarded: the finite decomposition and the
lossless copied-label reindexing below retain an arbitrary decidable support
predicate on the complete reduction tuple.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

/-! ## The boundary-safe edge and chain weights -/

/-- The dimensionless inverse-square edge weight between two torus cell
centres.  It agrees with `latticeEdgeWeight` whenever the chosen lattice
representatives do not wrap. -/
def periodicCellEdgeWeight (δ : ℝ) (a b : Z4) : ℝ :=
  δ ^ 2 /
    (δ ^ 2 +
      dist (latticeTorusCenter δ a) (latticeTorusCenter δ b) ^ 2)

theorem periodicCellEdgeWeight_nonneg
    (δ : ℝ) (a b : Z4) :
    0 ≤ periodicCellEdgeWeight δ a b := by
  unfold periodicCellEdgeWeight
  positivity

theorem periodicCellEdgeWeight_comm
    (δ : ℝ) (a b : Z4) :
    periodicCellEdgeWeight δ a b =
      periodicCellEdgeWeight δ b a := by
  unfold periodicCellEdgeWeight
  rw [dist_comm]

/-- Product of periodic edge weights along a path with fixed endpoints. -/
def periodicTerminalPathWeight (δ : ℝ) (a e : Z4) :
    List Z4 → ℝ
  | [] => periodicCellEdgeWeight δ a e
  | b :: bs =>
      periodicCellEdgeWeight δ a b *
        periodicTerminalPathWeight δ b e bs

theorem periodicTerminalPathWeight_nonneg
    (δ : ℝ) (a e : Z4) (as : List Z4) :
    0 ≤ periodicTerminalPathWeight δ a e as := by
  induction as generalizing a with
  | nil =>
      exact periodicCellEdgeWeight_nonneg δ a e
  | cons b bs ih =>
      exact mul_nonneg
        (periodicCellEdgeWeight_nonneg δ a b) (ih b)

/-- On a no-wrap edge, the boundary-safe weight is exactly the ordinary
integer-lattice weight. -/
theorem periodicCellEdgeWeight_eq_latticeEdgeWeight_of_noWrap
    {δ : ℝ} (hδ : 0 < δ) {a b : Z4}
    (hcenter :
      dist (latticeTorusCenter δ a) (latticeTorusCenter δ b) =
        δ * znorm (a - b)) :
    periodicCellEdgeWeight δ a b = latticeEdgeWeight a b := by
  have hδne : δ ≠ 0 := ne_of_gt hδ
  unfold periodicCellEdgeWeight latticeEdgeWeight
  rw [hcenter]
  field_simp [hδne]

/-- Pathwise form of the preceding exact identity. -/
theorem periodicTerminalPathWeight_eq_latticeTerminalPathWeight_of_noWrap
    {δ : ℝ} (hδ : 0 < δ) (a e : Z4) (as : List Z4)
    (hnowrap : LatticeCellPathNoWrap δ a (as ++ [e])) :
    periodicTerminalPathWeight δ a e as =
      latticeTerminalPathWeight a e as := by
  induction as generalizing a with
  | nil =>
      rw [List.nil_append, LatticeCellPathNoWrap.eq_def] at hnowrap
      simpa only [periodicTerminalPathWeight,
        latticeTerminalPathWeight] using
        periodicCellEdgeWeight_eq_latticeEdgeWeight_of_noWrap
          hδ hnowrap.1
  | cons b bs ih =>
      rw [List.cons_append, LatticeCellPathNoWrap.eq_def] at hnowrap
      rw [periodicTerminalPathWeight, latticeTerminalPathWeight,
        periodicCellEdgeWeight_eq_latticeEdgeWeight_of_noWrap
          hδ hnowrap.1,
        ih b hnowrap.2]

/-- A periodic path weight only depends on the torus centres of all its
labels. -/
theorem periodicTerminalPathWeight_congr_centers
    (δ : ℝ) {a a' e e' : Z4} {as as' : List Z4}
    (ha :
      latticeTorusCenter δ a = latticeTorusCenter δ a')
    (he :
      latticeTorusCenter δ e = latticeTorusCenter δ e')
    (hs :
      as.map (latticeTorusCenter δ) =
        as'.map (latticeTorusCenter δ)) :
    periodicTerminalPathWeight δ a e as =
      periodicTerminalPathWeight δ a' e' as' := by
  induction as generalizing a a' as' with
  | nil =>
      have has' : as' = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using (congrArg List.length hs).symm
      subst as'
      simp only [periodicTerminalPathWeight]
      unfold periodicCellEdgeWeight
      rw [ha, he]
  | cons b bs ih =>
      cases as' with
      | nil =>
          simp at hs
      | cons b' bs' =>
          simp only [List.map_cons, List.cons.injEq] at hs
          rw [periodicTerminalPathWeight,
            periodicTerminalPathWeight]
          congr 1
          · unfold periodicCellEdgeWeight
            rw [ha, hs.1]
          · exact ih hs.1 hs.2

/-- The no-wrap weight produced internally by the analytic chain proof is
literally the periodic weight of the original canonical copied labels. -/
theorem primitiveUnwrappedTerminalWeight_eq_periodicCopied
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    latticeTerminalPathWeight
        (primitiveFirstCell n hn y)
        (primitiveUnwrappedLast ε n hn y)
        (primitiveUnwrappedInternal ε n hn y) =
      periodicTerminalPathWeight (compatibleMeshSize ε)
        (primitiveFirstCell n hn y)
        (primitiveLastCell n hn y)
        (primitiveInternalCellLabels n hn y) := by
  let δ := compatibleMeshSize ε
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hnowrap :=
    primitiveUnwrappedPath_noWrap hε n hn y
  rw [← periodicTerminalPathWeight_eq_latticeTerminalPathWeight_of_noWrap
    hδ _ _ _ hnowrap]
  apply periodicTerminalPathWeight_congr_centers
  · rfl
  · exact primitiveUnwrappedLast_center hε n hn y
  · exact primitiveUnwrappedInternal_map_centers hε n hn y

/-! ## The canonical periodic reduction statistic -/

/-- Boundary-safe version of the pointwise statistic in (5.5), on the
literal copied tuple rather than occurrence-wise path lifts. -/
def primitivePeriodicCopiedWeight
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : ℝ :=
  primitiveTupleDiameterBracketSq (by omega)
      (primitiveCopiedReductionTuple n hn y) *
    periodicTerminalPathWeight (compatibleMeshSize ε)
      (primitiveFirstCell n hn y)
      (primitiveLastCell n hn y)
      (primitiveInternalCellLabels n hn y)

/-- The same boundary-safe statistic as a function on the literal reduction
carrier. -/
def primitivePeriodicReductionWeight
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (u : Fin ((2 * n - 1) + 1) → Z4) : ℝ :=
  primitivePeriodicCopiedWeight ε n hn
    (primitiveCopiedSourceTuple n hn u)

@[simp]
theorem primitivePeriodicReductionWeight_reductionTuple
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    primitivePeriodicReductionWeight ε n hn
        (primitiveCopiedReductionTuple n hn y) =
      primitivePeriodicCopiedWeight ε n hn y := by
  simp [primitivePeriodicReductionWeight]

@[simp]
theorem primitiveCopiedReductionTuple_ofFn
    (n : ℕ) (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    List.ofFn (primitiveCopiedReductionTuple n hn y) =
      List.ofFn y := by
  apply List.ext_getElem
  · simp
    omega
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn]
    unfold primitiveCopiedReductionTuple
      primitiveReductionTupleOfCellTuple
    congr

/-- The arithmetic cast from the cell tuple to the reduction tuple does not
change its diameter maximum. -/
theorem primitiveCopiedCellDiameter_eq_reductionDiameter
    (n : ℕ) (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    primitiveTupleDiameterBracketSq (by omega) y =
      primitiveTupleDiameterBracketSq (by omega)
        (primitiveCopiedReductionTuple n hn y) := by
  let e : Fin ((2 * n - 1) + 1) ≃ Fin (2 * n) :=
    finCongr (Nat.sub_add_cancel (by omega : 1 ≤ 2 * n))
  have h :=
    primitiveTupleDiameterBracketSq_comp_equiv
      (by omega : 0 < (2 * n - 1) + 1)
      (by omega : 0 < 2 * n) e y
  have hu :
      (fun i => y (e i)) =
        primitiveCopiedReductionTuple n hn y := by
    funext i
    unfold primitiveCopiedReductionTuple
      primitiveReductionTupleOfCellTuple
    apply congrArg y
    apply Fin.ext
    rfl
  rw [hu] at h
  exact h.symm

theorem primitivePeriodicCopiedWeight_nonneg
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    0 ≤ primitivePeriodicCopiedWeight ε n hn y := by
  unfold primitivePeriodicCopiedWeight
  exact mul_nonneg
    (primitiveTupleDiameterBracketSq_nonneg (by omega) _)
    (periodicTerminalPathWeight_nonneg _ _ _ _)

theorem primitivePeriodicReductionWeight_nonneg
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (u : Fin ((2 * n - 1) + 1) → Z4) :
    0 ≤ primitivePeriodicReductionWeight ε n hn u :=
  primitivePeriodicCopiedWeight_nonneg ε n hn _

/-- In the absence of a boundary crossing, the periodic statistic is
exactly the ordinary copied-label `reductionWeight`. -/
theorem primitivePeriodicCopiedWeight_eq_reductionWeight_of_noWrap
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4)
    (hnowrap :
      LatticeCellPathNoWrap (compatibleMeshSize ε)
        (primitiveFirstCell n hn y)
        (primitiveInternalCellLabels n hn y ++
          [primitiveLastCell n hn y])) :
    primitivePeriodicCopiedWeight ε n hn y =
      reductionWeight (2 * n - 1)
        (primitiveCopiedReductionTuple n hn y) := by
  unfold primitivePeriodicCopiedWeight reductionWeight
  congr 1
  rw [periodicTerminalPathWeight_eq_latticeTerminalPathWeight_of_noWrap
    (compatibleMeshSize_pos hε) _ _ _ hnowrap]
  rw [adjacentProduct_eq_listChainProduct,
    primitiveCopiedReductionTuple_ofFn,
    ← primitiveOriginalCellList_eq_ofFn]
  exact (listChainProduct_lattice_eq_terminal
    (primitiveFirstCell n hn y)
    (primitiveLastCell n hn y)
    (primitiveInternalCellLabels n hn y)).symm

/-! ## Canonical copied-cell analytic bounds -/

/-- Pointwise majorization on an actual paired cell fiber, with the diameter
of the literal copied reduction tuple and no occurrence-wise lift in the statement. -/
theorem exists_primitiveInsertedIntegrand_copiedFiber_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))), κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4)
          (v : Fin (2 * n - 2) → T4),
          pairedCellAssignment κ (compatibleMeshSize ε)
              (primitiveAssemble n hn z w v) = y →
          primitiveCovarianceProduct ρ ε n κ
              (primitiveAssemble n hn z w v) ≠ 0 →
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let D := primitiveTupleDiameterBracketSq (by omega)
            (primitiveCopiedReductionTuple n hn y)
          ENNReal.ofReal
              |primitiveInsertedIntegrand ρ ε n hn G κ
                (primitiveAssemble n hn z w v)| ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * C) ^ n *
                  ((12 + 32 * R ^ 2) * δ ^ 2 * D)) *
              terminalSingularProduct z w (List.ofFn v) := by
  obtain ⟨C, hC, hub⟩ :=
    exists_abs_primitiveIntegrand_uniform_bound ρ
  refine ⟨C, hC, ?_⟩
  intro n hn G hG κ hfull ε hε hε1 z w y v hfiber hcov
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let x := primitiveAssemble n hn z w v
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let D := primitiveTupleDiameterBracketSq (by omega)
    (primitiveCopiedReductionTuple n hn y)
  let Q := (ε⁻¹ ^ (dim : ℕ) * C) ^ n
  let B := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let F := ε ^ 2 + torusTupleDiameterSq x
  let S := primitiveSingularChainProduct n hn x
  have hmem :=
    primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
      ρ κ hfull hε hε1 x hcov
  have hx : ∀ i, x i ∈ latticeCellNeighborhood δ R (y i) := by
    rw [hfiber] at hmem
    simpa only [x, δ, R] using hmem
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact add_nonneg (sq_nonneg ε) (torusTupleDiameterSq_nonneg x)
  have hF : F ≤ B := by
    have hraw :=
      primitiveInsertedFactor_le_cellMaximum
        (by omega : 0 < 2 * n) hε hε1 hR y x hx
    dsimp only [F, B, D, δ, R]
    rw [← primitiveCopiedCellDiameter_eq_reductionDiameter n hn y]
    exact hraw
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact pow_nonneg
      (mul_nonneg
        (pow_nonneg (inv_nonneg.mpr hε.le) _)
        hC.le) _
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) _
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (by positivity : 0 ≤ 12 + 32 * R ^ 2)
        (sq_nonneg δ))
      hD0
  have hS0 : 0 ≤ S :=
    primitiveSingularChainProduct_nonneg n hn x
  have hint :
      |primitiveIntegrand ρ ε n hn G κ x| ≤ Q * S := by
    simpa only [Q, S] using
      hub n hn G hG κ hfull hε hε1 x
  have hreal :
      |primitiveInsertedIntegrand ρ ε n hn G κ x| ≤
        (Q * B) * S := by
    calc
      |primitiveInsertedIntegrand ρ ε n hn G κ x| =
          F * |primitiveIntegrand ρ ε n hn G κ x| := by
        unfold primitiveInsertedIntegrand
        rw [abs_mul, abs_of_nonneg hF0]
      _ ≤ F * (Q * S) :=
        mul_le_mul_of_nonneg_left hint hF0
      _ ≤ B * (Q * S) :=
        mul_le_mul_of_nonneg_right hF
          (mul_nonneg hQ0 hS0)
      _ = (Q * B) * S := by ring
  calc
    ENNReal.ofReal
        |primitiveInsertedIntegrand ρ ε n hn G κ x| ≤
        ENNReal.ofReal ((Q * B) * S) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Q * B) *
          terminalSingularProduct z w (List.ofFn v) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hQ0 hB0)]
      change ENNReal.ofReal (Q * B) *
          ENNReal.ofReal
            (primitiveSingularChainProduct n hn
              (primitiveAssemble n hn z w v)) =
        ENNReal.ofReal (Q * B) *
          terminalSingularProduct z w (List.ofFn v)
      rw [primitiveSingularChainProduct_assemble_eq_terminal]

/-- Integrated form of the canonical copied-fiber bound.  Covariance
support enlarges the actual assignment fiber to the product of canonical
torus cells, after which Tonelli identifies the singular chain exactly. -/
theorem exists_primitiveInsertedIntegrand_copiedFiber_lintegral_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))), κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4),
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let D := primitiveTupleDiameterBracketSq (by omega)
            (primitiveCopiedReductionTuple n hn y)
          let c : Fin (2 * n - 2) → T4 := fun i =>
            latticeTorusCenter δ (y (primitiveInternalIdx n hn i))
          (∫⁻ v in
              (fun q =>
                pairedCellAssignment κ δ
                  (primitiveAssemble n hn z w q)) ⁻¹' {y},
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * C) ^ n *
                  ((12 + 32 * R ^ 2) * δ ^ 2 * D)) *
              terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
  obtain ⟨C, hC, hpointwise⟩ :=
    exists_primitiveInsertedIntegrand_copiedFiber_bound ρ
  refine ⟨C, hC, ?_⟩
  intro n hn G hG κ hfull ε hε hε1 z w y
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let D := primitiveTupleDiameterBracketSq (by omega)
    (primitiveCopiedReductionTuple n hn y)
  let c : Fin (2 * n - 2) → T4 := fun i =>
    latticeTorusCenter δ (y (primitiveInternalIdx n hn i))
  let fiber : Set (Fin (2 * n - 2) → T4) :=
    (fun q =>
      pairedCellAssignment κ δ
        (primitiveAssemble n hn z w q)) ⁻¹' {y}
  let box : Set (Fin (2 * n - 2) → T4) :=
    Set.univ.pi fun i => Metric.ball (c i) (R * δ)
  let lhs : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)|
  let K :=
    (ε⁻¹ ^ (dim : ℕ) * C) ^ n *
      ((12 + 32 * R ^ 2) * δ ^ 2 * D)
  let rhs : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal K * terminalSingularProduct z w (List.ofFn v)
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  have hfiberMeas : MeasurableSet fiber := by
    dsimp only [fiber, δ]
    exact
      (primitivePairedInternalCells n hn κ
        (compatibleMeshSize ε)
        (compatibleMeshSize_pos hε) z w).measurable_fiber y
  have hboxMeas : MeasurableSet box := by
    dsimp only [box]
    exact MeasurableSet.univ_pi fun _ =>
      measurableSet_ball
  have hterm : Measurable fun v : Fin (2 * n - 2) → T4 =>
      terminalSingularProduct z w (List.ofFn v) := by
    convert (measurable_terminalSingularProduct_ofFn
      (2 * n - 2) w).comp
        (measurable_const.prodMk measurable_id) using 1
    ext v
    rfl
  have hindicator :
      fiber.indicator lhs ≤ box.indicator rhs := by
    intro v
    by_cases hv : v ∈ fiber
    · rw [Set.indicator_of_mem hv]
      have hvfiber :
          pairedCellAssignment κ δ
              (primitiveAssemble n hn z w v) = y := by
        simpa only [fiber, Set.mem_preimage,
          Set.mem_singleton_iff] using hv
      by_cases hcov :
          primitiveCovarianceProduct ρ ε n κ
              (primitiveAssemble n hn z w v) = 0
      · have hz :
            primitiveInsertedIntegrand ρ ε n hn G κ
                (primitiveAssemble n hn z w v) = 0 := by
          unfold primitiveInsertedIntegrand primitiveIntegrand
          rw [hcov, mul_zero, mul_zero]
        simp only [lhs, hz, abs_zero, ENNReal.ofReal_zero, zero_le]
      · have hvbox : v ∈ box := by
          have hm :=
            primitiveInternal_mem_productCell_of_fiber_covariance_ne_zero
              ρ hε hε1 n hn κ hfull z w y v hvfiber hcov
          simpa only [box, c, R, δ] using hm
        rw [Set.indicator_of_mem hvbox]
        simpa only [lhs, rhs, K, R, δ, D] using
          hpointwise n hn G hG κ hfull hε hε1
            z w y v hvfiber hcov
    · simp only [Set.indicator, hv, ↓reduceIte, zero_le]
  calc
    (∫⁻ v in fiber, lhs v ∂μ) =
        ∫⁻ v, fiber.indicator lhs v ∂μ := by
      rw [lintegral_indicator hfiberMeas]
    _ ≤ ∫⁻ v, box.indicator rhs v ∂μ :=
      lintegral_mono hindicator
    _ = ∫⁻ v in box, rhs v ∂μ :=
      lintegral_indicator hboxMeas rhs
    _ = ENNReal.ofReal K *
          ∫⁻ v in box,
            terminalSingularProduct z w (List.ofFn v) ∂μ := by
      dsimp only [rhs]
      rw [lintegral_const_mul (ENNReal.ofReal K) hterm]
    _ = ENNReal.ofReal K *
          terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
      congr 1
      exact terminalSingularProduct_setLIntegral_productCell
        (R * δ) z w (2 * n - 2) c

/-- The canonical diameter maximum times the true terminal-chain integral
has the paper scale, with the boundary-safe periodic product of the same
copied labels. -/
theorem primitiveCopiedCellMaximumTerminalLIntegral_exhaustive_order :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) {ε : ℝ}
        (_hε : 0 < ε)
        (R : ℝ) (_hR : 0 < R)
        (y : Fin (2 * n) → Z4) (z w : T4),
        z ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
            (primitiveFirstCell n (by omega) y) →
        w ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
            (primitiveLastCell n (by omega) y) →
        let δ := compatibleMeshSize ε
        let D := primitiveTupleDiameterBracketSq (by omega)
          (primitiveCopiedReductionTuple n (by omega) y)
        let W := periodicTerminalPathWeight δ
          (primitiveFirstCell n (by omega) y)
          (primitiveLastCell n (by omega) y)
          (primitiveInternalCellLabels n (by omega) y)
        ENNReal.ofReal
              ((12 + 32 * R ^ 2) * δ ^ 2 * D) *
            terminalCellLIntegral (R * δ) z w
              ((primitiveInternalCellLabels n (by omega) y).map
                (latticeTorusCenter δ)) ≤
          ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
            ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                δ ^ (4 * n - 4) * W) := by
  obtain ⟨C, hC, hcell⟩ :=
    primitiveTerminalCellLIntegral_exhaustive_order
  refine ⟨C, hC, ?_⟩
  intro n hn ε hε R hR y z w hz hw
  let hn1 : 1 ≤ n := by omega
  let δ := compatibleMeshSize ε
  let D := primitiveTupleDiameterBracketSq (by omega)
    (primitiveCopiedReductionTuple n hn1 y)
  let W := periodicTerminalPathWeight δ
    (primitiveFirstCell n hn1 y)
    (primitiveLastCell n hn1 y)
    (primitiveInternalCellLabels n hn1 y)
  let F := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let A :=
    (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 6) * W
  let B :=
    (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 6) * W
  have hchain :=
    hcell n hn hε R hR y z w hz hw
  rw [primitiveUnwrappedTerminalWeight_eq_periodicCopied
    hε n hn1 y] at hchain
  change terminalCellLIntegral (R * δ) z w
      ((primitiveInternalCellLabels n hn1 y).map
        (latticeTorusCenter δ)) ≤
      ENNReal.ofReal A + ENNReal.ofReal B at hchain
  have hδ0 : 0 ≤ δ := (compatibleMeshSize_pos hε).le
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) _
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact periodicTerminalPathWeight_nonneg _ _ _ _
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg
      (mul_nonneg
        (by positivity : 0 ≤ 12 + 32 * R ^ 2)
        (sq_nonneg δ))
      hD0
  have hfarBase : 0 ≤ C * (R ^ 2 + R ^ 4) :=
    mul_nonneg hC.le
      (add_nonneg (sq_nonneg R) (by positivity))
  have hnearBase : 0 ≤ C * cellChainRadiusFactor R :=
    mul_nonneg hC.le (cellChainRadiusFactor_pos R).le
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hfarBase _)
          (terminalRadiusFactor_pos hR).le)
        (pow_nonneg hδ0 _))
      hW0
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hnearBase _) (pow_nonneg hδ0 _))
      hW0
  have hFA :
      F * A =
        (12 + 32 * R ^ 2) * D *
          (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) * W := by
    dsimp only [F, A]
    rw [← compatibleCell_inserted_power_ledger δ n hn]
    ring
  have hFB :
      F * B =
        (12 + 32 * R ^ 2) * D *
          (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) * W := by
    dsimp only [F, B]
    rw [← compatibleCell_inserted_power_ledger δ n hn]
    ring
  calc
    ENNReal.ofReal F *
        terminalCellLIntegral (R * δ) z w
          ((primitiveInternalCellLabels n hn1 y).map
            (latticeTorusCenter δ)) ≤
        ENNReal.ofReal F *
          (ENNReal.ofReal A + ENNReal.ofReal B) := by
      simpa only [mul_comm] using
        mul_le_mul_right hchain (ENNReal.ofReal F)
    _ = ENNReal.ofReal (F * A) +
          ENNReal.ofReal (F * B) := by
      rw [mul_add, ENNReal.ofReal_mul hF0,
        ENNReal.ofReal_mul hF0]
    _ = _ := by rw [hFA, hFB]

/-- Complete continuous estimate on one actual paired canonical-cell fiber.
The right-hand side contains only the literal copied labels and the periodic
edge product forced by the torus geometry. -/
theorem primitiveInsertedIntegrand_copiedFiber_exhaustive_order
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4),
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let D := primitiveTupleDiameterBracketSq (by omega)
            (primitiveCopiedReductionTuple n (by omega) y)
          let W := periodicTerminalPathWeight δ
            (primitiveFirstCell n (by omega) y)
            (primitiveLastCell n (by omega) y)
            (primitiveInternalCellLabels n (by omega) y)
          (∫⁻ v in
              (fun q =>
                pairedCellAssignment κ δ
                  (primitiveAssemble n (by omega) z w q)) ⁻¹' {y},
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
              (ENNReal.ofReal
                ((12 + 32 * R ^ 2) * D *
                  (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                  terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
               ENNReal.ofReal
                ((12 + 32 * R ^ 2) * D *
                  (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
                  δ ^ (4 * n - 4) * W)) := by
  obtain ⟨Ccov, hCcov, hfiberBound⟩ :=
    exists_primitiveInsertedIntegrand_copiedFiber_lintegral_bound ρ
  obtain ⟨Ccell, hCcell, hcellBound⟩ :=
    primitiveCopiedCellMaximumTerminalLIntegral_exhaustive_order
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w y
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let hn1 : 1 ≤ n := by omega
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let D := primitiveTupleDiameterBracketSq (by omega)
    (primitiveCopiedReductionTuple n hn1 y)
  let W := periodicTerminalPathWeight δ
    (primitiveFirstCell n hn1 y)
    (primitiveLastCell n hn1 y)
    (primitiveInternalCellLabels n hn1 y)
  let c : Fin (2 * n - 2) → T4 := fun i =>
    latticeTorusCenter δ (y (primitiveInternalIdx n hn1 i))
  let fiber : Set (Fin (2 * n - 2) → T4) :=
    (fun q =>
      pairedCellAssignment κ δ
        (primitiveAssemble n hn1 z w q)) ⁻¹' {y}
  let f : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn1 G κ
        (primitiveAssemble n hn1 z w v)|
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let F := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let A :=
    (12 + 32 * R ^ 2) * D *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4) * W
  let B :=
    (12 + 32 * R ^ 2) * D *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4) * W
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact pow_nonneg
      (mul_nonneg
        (pow_nonneg (inv_nonneg.mpr hε.le) _)
        hCcov.le) _
  have hc :
      List.ofFn c =
        (primitiveInternalCellLabels n hn1 y).map
          (latticeTorusCenter δ) := by
    unfold c primitiveInternalCellLabels
    exact List.ofFn_comp' _ _
  have hpre :
      (∫⁻ v in fiber, f v ∂μ) ≤
        ENNReal.ofReal (Q * F) *
          terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
    simpa only [fiber, f, μ, Q, F, R, δ, D] using
      hfiberBound n hn1 G hG κ hfull hε hε1 z w y
  change (∫⁻ v in fiber, f v ∂μ) ≤
    ENNReal.ofReal Q *
      (ENNReal.ofReal A + ENNReal.ofReal B)
  by_cases hsupported :
      ∃ v, v ∈ fiber ∧
        primitiveCovarianceProduct ρ ε n κ
          (primitiveAssemble n hn1 z w v) ≠ 0
  · obtain ⟨v₀, hv₀, hcov₀⟩ := hsupported
    have hvfiber :
        pairedCellAssignment κ δ
            (primitiveAssemble n hn1 z w v₀) = y := by
      simpa only [fiber, Set.mem_preimage,
        Set.mem_singleton_iff] using hv₀
    have hmem :=
      primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
        ρ κ hfull hε hε1
          (primitiveAssemble n hn1 z w v₀) hcov₀
    rw [hvfiber] at hmem
    have hz :
        z ∈ latticeCellNeighborhood δ R
          (primitiveFirstCell n hn1 y) := by
      simpa only [primitiveFirstCell, primitiveAssemble_zero,
        δ, R] using hmem (⟨0, by omega⟩ : Fin (2 * n))
    have hw :
        w ∈ latticeCellNeighborhood δ R
          (primitiveLastCell n hn1 y) := by
      simpa only [primitiveLastCell, primitiveAssemble_last,
        δ, R] using hmem (primitiveLast n hn1)
    have hcell :=
      hcellBound n hn hε R hR y z w hz hw
    change ENNReal.ofReal F *
        terminalCellLIntegral (R * δ) z w
          ((primitiveInternalCellLabels n hn1 y).map
            (latticeTorusCenter δ)) ≤
        ENNReal.ofReal A + ENNReal.ofReal B at hcell
    calc
      (∫⁻ v in fiber, f v ∂μ) ≤
          ENNReal.ofReal (Q * F) *
            terminalCellLIntegral (R * δ) z w (List.ofFn c) :=
        hpre
      _ = ENNReal.ofReal Q *
          (ENNReal.ofReal F *
            terminalCellLIntegral (R * δ) z w
              ((primitiveInternalCellLabels n hn1 y).map
                (latticeTorusCenter δ))) := by
        rw [ENNReal.ofReal_mul hQ0, hc]
        ring
      _ ≤ ENNReal.ofReal Q *
          (ENNReal.ofReal A + ENNReal.ofReal B) := by
        simpa only [mul_comm] using
          mul_le_mul_right hcell (ENNReal.ofReal Q)
  · have hfiberMeas : MeasurableSet fiber := by
      dsimp only [fiber, δ]
      exact
        (primitivePairedInternalCells n hn1 κ
          (compatibleMeshSize ε)
          (compatibleMeshSize_pos hε) z w).measurable_fiber y
    have hzero : (∫⁻ v in fiber, f v ∂μ) = 0 := by
      apply le_antisymm
      · calc
          (∫⁻ v in fiber, f v ∂μ) ≤
              ∫⁻ _v in fiber, 0 ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hfiberMeas] with v hv
            have hcov :
                primitiveCovarianceProduct ρ ε n κ
                    (primitiveAssemble n hn1 z w v) = 0 := by
              exact not_ne_iff.mp fun hne =>
                hsupported ⟨v, hv, hne⟩
            have hvalue :
                primitiveInsertedIntegrand ρ ε n hn1 G κ
                    (primitiveAssemble n hn1 z w v) = 0 := by
              unfold primitiveInsertedIntegrand primitiveIntegrand
              rw [hcov, mul_zero, mul_zero]
            simp only [f, hvalue, abs_zero, ENNReal.ofReal_zero]
            exact le_rfl
          _ = 0 := by simp
      · exact bot_le
    rw [hzero]
    exact bot_le

/-! ## Endpoint support and lossless filtered summation -/

/-- The endpoint constraint genuinely supplied by a nonzero endpoint-fixed
cell fiber. -/
def primitiveCanonicalEndpointSupported
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z w : T4) (y : Fin (2 * n) → Z4) : Prop :=
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  z ∈ latticeCellNeighborhood δ R (primitiveFirstCell n hn y) ∧
    w ∈ latticeCellNeighborhood δ R (primitiveLastCell n hn y)

/-- The same endpoint constraint transported to the exact reduction-tuple
carrier used by `sum_copiedLabels_filter_eq_boundedPairing_filter`. -/
def primitiveCopiedEndpointSupported
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z w : T4)
    (u : Fin ((2 * n - 1) + 1) → Z4) : Prop :=
  primitiveCanonicalEndpointSupported ρ ε n hn z w
    (primitiveCopiedSourceTuple n hn u)

noncomputable instance primitiveCopiedEndpointSupported_decidable
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z w : T4)
    (u : Fin ((2 * n - 1) + 1) → Z4) :
    Decidable (primitiveCopiedEndpointSupported ρ ε n hn z w u) :=
  Classical.propDecidable _

@[simp]
theorem primitiveCopiedEndpointSupported_reductionTuple
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (z w : T4) (y : Fin (2 * n) → Z4) :
    primitiveCopiedEndpointSupported ρ ε n hn z w
        (primitiveCopiedReductionTuple n hn y) ↔
      primitiveCanonicalEndpointSupported ρ ε n hn z w y := by
  simp [primitiveCopiedEndpointSupported]

/-- Actual contribution of one canonical paired-assignment fiber. -/
def primitiveCopiedFiberContribution
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n))) (z w : T4)
    (y : Fin (2 * n) → Z4) : ENNReal :=
  ∫⁻ v in
      (fun q =>
        pairedCellAssignment κ (compatibleMeshSize ε)
          (primitiveAssemble n hn z w q)) ⁻¹' {y},
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)|
    ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure

/-- Failure of the endpoint-support predicate forces the genuine canonical
fiber contribution to vanish. -/
theorem primitiveCopiedFiberContribution_eq_zero_of_not_endpointSupported
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (z w : T4) (y : Fin (2 * n) → Z4)
    (hunsupported :
      ¬primitiveCanonicalEndpointSupported ρ ε n hn z w y) :
    primitiveCopiedFiberContribution ρ ε n hn G κ z w y = 0 := by
  let δ := compatibleMeshSize ε
  let fiber : Set (Fin (2 * n - 2) → T4) :=
    (fun q =>
      pairedCellAssignment κ δ
        (primitiveAssemble n hn z w q)) ⁻¹' {y}
  let f : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)|
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  have hfiberMeas : MeasurableSet fiber := by
    dsimp only [fiber, δ]
    exact
      (primitivePairedInternalCells n hn κ
        (compatibleMeshSize ε)
        (compatibleMeshSize_pos hε) z w).measurable_fiber y
  change (∫⁻ v in fiber, f v ∂μ) = 0
  apply le_antisymm
  · calc
      (∫⁻ v in fiber, f v ∂μ) ≤
          ∫⁻ _v in fiber, 0 ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hfiberMeas] with v hv
        have hvfiber :
            pairedCellAssignment κ δ
                (primitiveAssemble n hn z w v) = y := by
          simpa only [fiber, Set.mem_preimage,
            Set.mem_singleton_iff] using hv
        have hcov :
            primitiveCovarianceProduct ρ ε n κ
                (primitiveAssemble n hn z w v) = 0 := by
          by_contra hne
          have hmem :=
            primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
              ρ κ hfull hε hε1
                (primitiveAssemble n hn z w v) hne
          rw [hvfiber] at hmem
          apply hunsupported
          constructor
          · simpa only [primitiveCanonicalEndpointSupported,
              primitiveFirstCell, primitiveAssemble_zero, δ] using
              hmem (⟨0, by omega⟩ : Fin (2 * n))
          · simpa only [primitiveCanonicalEndpointSupported,
              primitiveLastCell, primitiveAssemble_last, δ] using
              hmem (primitiveLast n hn)
        have hvalue :
            primitiveInsertedIntegrand ρ ε n hn G κ
                (primitiveAssemble n hn z w v) = 0 := by
          unfold primitiveInsertedIntegrand primitiveIntegrand
          rw [hcov, mul_zero, mul_zero]
        simp only [f, hvalue, abs_zero, ENNReal.ofReal_zero]
        exact le_rfl
      _ = 0 := by simp
  · exact bot_le

/-- `ENNReal` companion of the real-valued lossless reindexing theorem.
The proof is purely finite and retains any decidable tuple predicate. -/
theorem sum_copiedLabels_filter_eq_boundedPairing_filter_ennreal
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P]
    (f : (Fin ((2 * n - 1) + 1) → Z4) → ENNReal) :
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

/-- Exact endpoint-fixed Fubini decomposition, followed by exact copied-label
reindexing.  The predicate is arbitrary; the only semantic premise is that
fibers outside it vanish. -/
theorem primitiveInsertedIntegrand_lintegral_eq_boundedPairing_filter
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n))) (z w : T4)
    (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
    [DecidablePred P]
    (hvanish :
      ∀ y ∈ primitiveCanonicalCellCarrier ε n κ,
        ¬P (primitiveCopiedReductionTuple n hn y) →
          primitiveCopiedFiberContribution
            ρ ε n hn G κ z w y = 0) :
    (∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)|
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) =
      ∑ u ∈
          ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
              ((2 * n - 1) + 1)).filter
            (RespectsPairing
              (primitiveReductionPairing n hn κ))).filter P,
        primitiveCopiedFiberContribution ρ ε n hn G κ z w
          (primitiveCopiedSourceTuple n hn u) := by
  classical
  let grid :=
    Fintype.piFinset
      (fun _ : Fin (2 * n) =>
        torusGrid (compatibleMeshSize ε))
  let integrand : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)|
  have hpartition :=
    primitive_lintegral_eq_sum_pairedInternalCells
      n hn κ (compatibleMeshSize_pos hε) z w integrand
  change
    (∫⁻ v, integrand v
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) =
      ∑ y ∈ grid,
        primitiveCopiedFiberContribution ρ ε n hn G κ z w y
      at hpartition
  have hfiltered :
      (∑ y ∈ grid,
          primitiveCopiedFiberContribution ρ ε n hn G κ z w y) =
        ∑ y ∈
            (primitiveCanonicalCellCarrier ε n κ).filter
              (fun y =>
                P (primitiveCopiedReductionTuple n hn y)),
          primitiveCopiedFiberContribution ρ ε n hn G κ z w y := by
    unfold primitiveCanonicalCellCarrier
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hrespect : RespectsPairing κ y
    · by_cases hP : P (primitiveCopiedReductionTuple n hn y)
      · simp only [hrespect, hP, ↓reduceIte]
      · have hycarrier :
            y ∈ primitiveCanonicalCellCarrier ε n κ := by
          exact Finset.mem_filter.mpr ⟨hy, hrespect⟩
        rw [hvanish y hycarrier hP]
        simp only [hrespect, hP, ↓reduceIte]
    · have hempty :
          (fun q =>
            pairedCellAssignment κ (compatibleMeshSize ε)
              (primitiveAssemble n hn z w q)) ⁻¹' {y} = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨v, hv⟩
        have heq :
            pairedCellAssignment κ (compatibleMeshSize ε)
                (primitiveAssemble n hn z w v) = y := by
          simpa only [Set.mem_preimage,
            Set.mem_singleton_iff] using hv
        apply hrespect
        rw [← heq]
        exact pairedCellAssignment_respectsPairing κ
          (compatibleMeshSize ε)
          (primitiveAssemble n hn z w v)
      have hzero :
          primitiveCopiedFiberContribution
              ρ ε n hn G κ z w y = 0 := by
        unfold primitiveCopiedFiberContribution
        rw [hempty]
        simp
      rw [hzero]
      simp only [hrespect, ↓reduceIte]
  rw [hpartition, hfiltered]
  let f : (Fin ((2 * n - 1) + 1) → Z4) → ENNReal := fun u =>
    primitiveCopiedFiberContribution ρ ε n hn G κ z w
      (primitiveCopiedSourceTuple n hn u)
  have hreindex :=
    sum_copiedLabels_filter_eq_boundedPairing_filter_ennreal
      hε n hn κ P f
  simpa only [f, primitiveCopiedSourceTuple_reductionTuple] using
    hreindex

/-- Concrete specialization retaining precisely the endpoint support forced
by nonvanishing covariance. -/
theorem primitiveInsertedIntegrand_lintegral_eq_endpointSupportedCells
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (z w : T4) :
    (∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)|
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) =
      ∑ u ∈
          ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
              ((2 * n - 1) + 1)).filter
            (RespectsPairing
              (primitiveReductionPairing n hn κ))).filter
                (primitiveCopiedEndpointSupported
                  ρ ε n hn z w),
        primitiveCopiedFiberContribution ρ ε n hn G κ z w
          (primitiveCopiedSourceTuple n hn u) := by
  classical
  apply primitiveInsertedIntegrand_lintegral_eq_boundedPairing_filter
    ρ hε n hn G κ z w
      (primitiveCopiedEndpointSupported ρ ε n hn z w)
  intro y hy hunsupported
  apply
    primitiveCopiedFiberContribution_eq_zero_of_not_endpointSupported
      ρ hε hε1 n hn G κ hfull z w y
  exact fun hsupported =>
    hunsupported
      (primitiveCopiedEndpointSupported_reductionTuple
        ρ ε n hn z w y |>.2 hsupported)

/-! ## Complete periodic copied-label cell reduction -/

/-- The endpoint-fixed primitive integral is bounded by the finite,
losslessly reindexed periodic copied-label statistic.  `P` may be any
decidable endpoint-support refinement; no translation enlargement is made. -/
theorem primitiveInsertedIntegrand_lintegral_le_periodicCopiedSum_filter
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4)
          (P : (Fin ((2 * n - 1) + 1) → Z4) → Prop)
          [DecidablePred P],
          (∀ y ∈ primitiveCanonicalCellCarrier ε n κ,
            ¬P (primitiveCopiedReductionTuple n (by omega) y) →
              primitiveCopiedFiberContribution ρ ε n (by omega)
                G κ z w y = 0) →
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
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ∑ u ∈
                ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
                    ((2 * n - 1) + 1)).filter
                  (RespectsPairing
                    (primitiveReductionPairing n (by omega) κ))).filter P,
              ENNReal.ofReal
                  ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
                (ENNReal.ofReal
                    (farCoeff *
                      primitivePeriodicReductionWeight
                        ε n (by omega) u) +
                 ENNReal.ofReal
                    (nearCoeff *
                      primitivePeriodicReductionWeight
                        ε n (by omega) u)) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hfiber⟩ :=
    primitiveInsertedIntegrand_copiedFiber_exhaustive_order ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w P instP hvanish
  let hn1 : 1 ≤ n := by omega
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
  let carrier :=
    ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
        ((2 * n - 1) + 1)).filter
      (RespectsPairing
        (primitiveReductionPairing n hn1 κ))).filter P
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let cellBound :
      (Fin ((2 * n - 1) + 1) → Z4) → ENNReal := fun u =>
    ENNReal.ofReal Q *
      (ENNReal.ofReal
          (farCoeff *
            primitivePeriodicReductionWeight ε n hn1 u) +
       ENNReal.ofReal
          (nearCoeff *
            primitivePeriodicReductionWeight ε n hn1 u))
  have hdecomp :=
    primitiveInsertedIntegrand_lintegral_eq_boundedPairing_filter
      ρ hε n hn1 G κ z w P hvanish
  change
    (∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn1 G κ
            (primitiveAssemble n hn1 z w v)|
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) =
      ∑ u ∈ carrier,
        primitiveCopiedFiberContribution ρ ε n hn1 G κ z w
          (primitiveCopiedSourceTuple n hn1 u) at hdecomp
  change
    (∫⁻ v,
        ENNReal.ofReal
          |primitiveInsertedIntegrand ρ ε n hn1 G κ
            (primitiveAssemble n hn1 z w v)|
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
      ∑ u ∈ carrier, cellBound u
  rw [hdecomp]
  apply Finset.sum_le_sum
  intro u hu
  let y := primitiveCopiedSourceTuple n hn1 u
  let D := primitiveTupleDiameterBracketSq (by omega)
    (primitiveCopiedReductionTuple n hn1 y)
  let W := periodicTerminalPathWeight δ
    (primitiveFirstCell n hn1 y)
    (primitiveLastCell n hn1 y)
    (primitiveInternalCellLabels n hn1 y)
  have hcell :=
    hfiber n hn G hG κ hκ hε hε1 z w y
  have hperiodic :
      primitivePeriodicReductionWeight ε n hn1 u = D * W := by
    dsimp only [primitivePeriodicReductionWeight,
      primitivePeriodicCopiedWeight, D, W, y]
  have hfar :
      (12 + 32 * R ^ 2) * D *
          (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) * W =
        farCoeff *
          primitivePeriodicReductionWeight ε n hn1 u := by
    rw [hperiodic]
    dsimp only [farCoeff]
    ring
  have hnear :
      (12 + 32 * R ^ 2) * D *
          (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) * W =
        nearCoeff *
          primitivePeriodicReductionWeight ε n hn1 u := by
    rw [hperiodic]
    dsimp only [nearCoeff]
    ring
  simpa only [primitiveCopiedFiberContribution, cellBound,
    Q, R, δ, D, W, y, hfar, hnear] using hcell

/-- Specialization of the preceding theorem to the exact endpoint support
forced by covariance. -/
theorem primitiveInsertedIntegrand_lintegral_le_periodicEndpointSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
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
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ∑ u ∈
                ((rdec_boundedTuples (primitiveCopiedBoxRadius ε)
                    ((2 * n - 1) + 1)).filter
                  (RespectsPairing
                    (primitiveReductionPairing n (by omega) κ))).filter
                      (primitiveCopiedEndpointSupported
                        ρ ε n (by omega) z w),
              ENNReal.ofReal
                  ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
                (ENNReal.ofReal
                    (farCoeff *
                      primitivePeriodicReductionWeight
                        ε n (by omega) u) +
                 ENNReal.ofReal
                    (nearCoeff *
                      primitivePeriodicReductionWeight
                        ε n (by omega) u)) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hsum⟩ :=
    primitiveInsertedIntegrand_lintegral_le_periodicCopiedSum_filter ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w
  let hn1 : 1 ≤ n := by omega
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  apply hsum n hn G hG κ hκ hε hε1 z w
    (primitiveCopiedEndpointSupported ρ ε n hn1 z w)
  intro y hy hunsupported
  apply
    primitiveCopiedFiberContribution_eq_zero_of_not_endpointSupported
      ρ hε hε1 n hn1 G κ hfull z w y
  exact fun hsupported =>
    hunsupported
      (primitiveCopiedEndpointSupported_reductionTuple
        ρ ε n hn1 z w y |>.2 hsupported)

/-! ## Exact remaining boundary interface -/

/-- The sole pointwise interface that would turn the periodic cell statistic
back into the existing Euclidean copied-label statistic.  It is deliberately
defined, not assumed by any theorem above.  A constant uniform in the mesh
cannot satisfy this predicate on the canonical torus box. -/
def PeriodicCellEdgeComparison (δ C : ℝ) : Prop :=
  ∀ a b : Z4,
    periodicCellEdgeWeight δ a b ≤
      C * latticeEdgeWeight a b

/-- On a genuinely no-wrap edge the required comparison holds with constant
one, in fact as an equality. -/
theorem periodicCellEdgeComparison_of_noWrap
    {δ : ℝ} (hδ : 0 < δ) {a b : Z4}
    (hcenter :
      dist (latticeTorusCenter δ a) (latticeTorusCenter δ b) =
        δ * znorm (a - b)) :
    periodicCellEdgeWeight δ a b ≤ latticeEdgeWeight a b := by
  rw [periodicCellEdgeWeight_eq_latticeEdgeWeight_of_noWrap
    hδ hcenter]

/-- A whole-period translate has periodic edge weight exactly one.  Its
ordinary lattice weight still sees the (possibly arbitrarily large) integer
translate; this is the precise cut obstruction to canonical (5.3). -/
theorem periodicCellEdgeWeight_translateCellIndex_eq_one
    {δ : ℝ} (hδ : 0 < δ) {q : ℤ}
    (hq : PeriodCompatibleMesh δ q) (k y : Z4) :
    periodicCellEdgeWeight δ
        (translateCellIndex q k y) y = 1 := by
  have hc :=
    latticeTorusCenter_translateCellIndex hq k y
  unfold periodicCellEdgeWeight
  rw [hc, dist_self]
  norm_num [ne_of_gt hδ]

end

end Anderson4D
