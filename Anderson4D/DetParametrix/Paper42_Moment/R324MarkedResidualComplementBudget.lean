import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualPhysicalModeIntegration

/-!
# Finiteness of the marked-residual physical complement

The marked-mode bridge leaves every covariance except the selected open
edge in physical space.  This file proves that the resulting complement
has finite `L¹` mass on every genuine selected cell.

The proof does not expand those covariances.  Instead, it expands only the
finite Green-difference product.  Each resulting summand is an increasing
Green tree on the internal vertices, hence is integrable by
`integrable_increasingTreeGreenProduct`; the remaining physical
covariances are bounded at every fixed positive mollifier scale.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## The internal Green tree carried by one expanded branch -/

/-- The full chain edge corresponding to an internal edge. -/
def r324InteriorFullEdge (n : ℕ) (i : Fin (n + 1)) :
    Fin ((n + 2) + 1) :=
  ⟨i.val + 1, by omega⟩

/-- The internal parent of a shortcut edge. -/
def r324InteriorShortcutParent
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (i : Fin (n + 1))
    (hi :
      r324InteriorFullEdge n i ∈ extractedRightEdges κ) :
    Fin (i.val + 1) := by
  let p :=
    extractedPairOfRightEdge κ
      (r324InteriorFullEdge n i) hi
  refine ⟨p.1.val, ?_⟩
  have hp :=
    extract_spec κ p
      (extractedPairOfRightEdge_mem κ
        (r324InteriorFullEdge n i) hi)
  have hedge :=
    congrArg Fin.val
      (extractedRightEdge_extractedPairOfRightEdge κ
        (r324InteriorFullEdge n i) hi)
  have hpval : p.1.val ≤ p.2.val := hp
  have hedgeval : p.2.val + 1 = i.val + 1 := by
    change
      p.2.val + 1 =
        (r324InteriorFullEdge n i).val at hedge
    change p.2.val + 1 = i.val + 1 at hedge
    exact hedge
  omega

/-- Parent map of one branch of the internal Green-difference product. -/
def r324InteriorExpandedTreeParent
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (original : Finset (Fin (n + 1))) :
    IncreasingTreeParent (n + 1) :=
  fun i =>
    if i ∈ original then ordinaryEdgeParent i
    else if hi :
        r324InteriorFullEdge n i ∈ extractedRightEdges κ then
      r324InteriorShortcutParent κ i hi
    else ordinaryEdgeParent i

/-- Original full-chain factor at an internal edge. -/
def r324InteriorOriginalGreenEdge
    {n : ℕ} (v : Fin (n + 2) → T4)
    (i : Fin (n + 1)) : ℂ :=
  originalGreenEdge (assemble 0 0 v)
    (r324InteriorFullEdge n i)

/-- Shortcut factor at an internal edge, zero if no shortcut exists. -/
def r324InteriorShortcutGreenEdge
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (v : Fin (n + 2) → T4)
    (i : Fin (n + 1)) : ℂ :=
  extractedShortcutGreenEdge κ (assemble 0 0 v)
    (r324InteriorFullEdge n i)

/-- One branch in the internal product-of-sums expansion. -/
def r324InteriorExpandedGreenBranch
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (original : Finset (Fin (n + 1)))
    (v : Fin (n + 2) → T4) : ℂ :=
  (∏ i ∈ original, r324InteriorOriginalGreenEdge v i) *
    ∏ i ∈ originalᶜ,
      r324InteriorShortcutGreenEdge κ v i

private theorem r324InteriorFullEdge_castSucc
    {n : ℕ} (i : Fin (n + 1)) :
    (r324InteriorFullEdge n i).castSucc =
      varIdx i.castSucc := by
  apply Fin.ext
  rfl

private theorem r324InteriorFullEdge_succ
    {n : ℕ} (i : Fin (n + 1)) :
    (r324InteriorFullEdge n i).succ = varIdx i.succ := by
  apply Fin.ext
  rfl

private theorem r324InteriorExpandedTreeParentVertex_original
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (original : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ original) :
    increasingTreeParentVertex
        (r324InteriorExpandedTreeParent κ original) i =
      i.castSucc := by
  apply Fin.ext
  simp [increasingTreeParentVertex,
    r324InteriorExpandedTreeParent, hi, ordinaryEdgeParent]

private theorem r324InteriorShortcutParent_fullVertex
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (i : Fin (n + 1))
    (hi :
      r324InteriorFullEdge n i ∈ extractedRightEdges κ) :
    Fin.castLE (by omega)
        (extractedShortcutParent κ
          (r324InteriorFullEdge n i) hi) =
      varIdx
        (Fin.castLE (by omega)
          (r324InteriorShortcutParent κ i hi) :
          Fin (n + 2)) := by
  apply Fin.ext
  change
    (extractedShortcutParent κ
      (r324InteriorFullEdge n i) hi).val =
      (r324InteriorShortcutParent κ i hi).val + 1
  unfold extractedShortcutParent
    r324InteriorShortcutParent
  rfl

private theorem r324InteriorExpandedTreeParentVertex_shortcut
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (original : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∉ original)
    (hextract :
      r324InteriorFullEdge n i ∈ extractedRightEdges κ) :
    increasingTreeParentVertex
        (r324InteriorExpandedTreeParent κ original) i =
      Fin.castLE (by omega)
        (r324InteriorShortcutParent κ i hextract) := by
  apply Fin.ext
  simp [increasingTreeParentVertex,
    r324InteriorExpandedTreeParent, hi, hextract]

/-- A nonzero internal branch is exactly an increasing Green tree. -/
theorem r324InteriorExpandedGreenBranch_eq_tree
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (original : Finset (Fin (n + 1)))
    (hshortcut :
      ∀ i : Fin (n + 1), i ∉ original →
        r324InteriorFullEdge n i ∈ extractedRightEdges κ) :
    r324InteriorExpandedGreenBranch κ original =
      increasingTreeGreenProduct
        (r324InteriorExpandedTreeParent κ original) := by
  funext v
  have hfactor :
      ∀ i : Fin (n + 1),
        (greenFn
          (v (increasingTreeParentVertex
              (r324InteriorExpandedTreeParent κ original) i) -
            v i.succ) : ℂ) =
          if i ∈ original then
            r324InteriorOriginalGreenEdge v i
          else r324InteriorShortcutGreenEdge κ v i := by
    intro i
    by_cases hi : i ∈ original
    · rw [if_pos hi,
        r324InteriorExpandedTreeParentVertex_original
          κ original i hi]
      unfold r324InteriorOriginalGreenEdge originalGreenEdge
      rw [r324InteriorFullEdge_castSucc,
        r324InteriorFullEdge_succ,
        assemble_varIdx, assemble_varIdx]
    · have hextract := hshortcut i hi
      rw [if_neg hi,
        r324InteriorExpandedTreeParentVertex_shortcut
          κ original i hi hextract]
      unfold r324InteriorShortcutGreenEdge
        extractedShortcutGreenEdge
      rw [dif_pos hextract,
        r324InteriorShortcutParent_fullVertex,
        r324InteriorFullEdge_succ,
        assemble_varIdx, assemble_varIdx]
  unfold r324InteriorExpandedGreenBranch
    increasingTreeGreenProduct
  rw [show
      (∏ i : Fin (n + 1),
          (greenFn
            (v (increasingTreeParentVertex
                (r324InteriorExpandedTreeParent κ original) i) -
              v i.succ) : ℂ)) =
        ∏ i : Fin (n + 1),
          if i ∈ original then
            r324InteriorOriginalGreenEdge v i
          else r324InteriorShortcutGreenEdge κ v i by
    apply Finset.prod_congr rfl
    intro i _hi
    exact hfactor i]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  have hcompl :
      {i ∈ (Finset.univ : Finset (Fin (n + 1))) |
          ¬i ∈ original} =
        originalᶜ := by
    ext i
    simp
  rw [hcompl]

/-- Every internal branch is integrable. -/
theorem integrable_r324InteriorExpandedGreenBranch
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (original : Finset (Fin (n + 1))) :
    Integrable (r324InteriorExpandedGreenBranch κ original)
      (Measure.pi fun _ : Fin (n + 2) => paperMeasure) := by
  by_cases hshortcut :
      ∀ i : Fin (n + 1), i ∉ original →
        r324InteriorFullEdge n i ∈ extractedRightEdges κ
  · rw [r324InteriorExpandedGreenBranch_eq_tree
      κ original hshortcut]
    exact integrable_increasingTreeGreenProduct
      (r324InteriorExpandedTreeParent κ original)
  · push Not at hshortcut
    obtain ⟨i, hi, hnotExtracted⟩ := hshortcut
    have hiCompl : i ∈ originalᶜ := by
      simpa using hi
    have hzero :
        ∀ v : Fin (n + 2) → T4,
          (∏ j ∈ originalᶜ,
            r324InteriorShortcutGreenEdge κ v j) = 0 := by
      intro v
      apply Finset.prod_eq_zero hiCompl
      simp [r324InteriorShortcutGreenEdge,
        extractedShortcutGreenEdge, hnotExtracted]
    have hfun :
        r324InteriorExpandedGreenBranch κ original =
          fun _ : Fin (n + 2) → T4 => 0 := by
      funext v
      unfold r324InteriorExpandedGreenBranch
      rw [hzero v, mul_zero]
    rw [hfun]
    exact integrable_zero _ _ _

/-! ## Integrability of the endpoint-independent Green profile -/

/-- The product-of-sums majorant for the internal Green differences. -/
def r324InteriorExpandedGreenMajorant
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (v : Fin (n + 2) → T4) : ℂ :=
  ∏ i : Fin (n + 1),
    (r324InteriorOriginalGreenEdge v i +
      r324InteriorShortcutGreenEdge κ v i)

theorem r324InteriorExpandedGreenMajorant_eq_sum_branches
    {n : ℕ} (κ : PartialPairing (Fin (n + 2))) :
    r324InteriorExpandedGreenMajorant κ =
      fun v => ∑ original : Finset (Fin (n + 1)),
        r324InteriorExpandedGreenBranch κ original v := by
  funext v
  unfold r324InteriorExpandedGreenMajorant
    r324InteriorExpandedGreenBranch
  exact Fintype.prod_add
    (fun i : Fin (n + 1) =>
      r324InteriorOriginalGreenEdge v i)
    (fun i : Fin (n + 1) =>
      r324InteriorShortcutGreenEdge κ v i)

theorem integrable_r324InteriorExpandedGreenMajorant
    {n : ℕ} (κ : PartialPairing (Fin (n + 2))) :
    Integrable (r324InteriorExpandedGreenMajorant κ)
      (Measure.pi fun _ : Fin (n + 2) => paperMeasure) := by
  rw [r324InteriorExpandedGreenMajorant_eq_sum_branches]
  exact integrable_finsetSum Finset.univ fun original _ =>
    integrable_r324InteriorExpandedGreenBranch κ original

/-- The erased external-edge product is the standard internal-edge
product. -/
theorem r324RenormalizedInteriorCore_eq_internalDifferenceProduct
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (v : Fin (n + 2) → T4) :
    r324RenormalizedInteriorCore κ v =
      ∏ i : Fin (n + 1),
        (r324InteriorOriginalGreenEdge v i -
          r324InteriorShortcutGreenEdge κ v i) := by
  unfold r324RenormalizedInteriorCore
    r324InteriorOriginalGreenEdge
    r324InteriorShortcutGreenEdge
  symm
  refine Finset.prod_bij
    (fun i _hi => r324InteriorFullEdge n i) ?_ ?_ ?_ ?_
  · intro i _hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    · intro hlast
      have hval := congrArg Fin.val hlast
      simp only [r324InteriorFullEdge, Fin.val_last] at hval
      omega
    · intro hzero
      have hval := congrArg Fin.val hzero
      simp only [r324InteriorFullEdge, Fin.val_zero] at hval
      omega
  · intro i _hi j _hj hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simp only [r324InteriorFullEdge] at hval
    omega
  · intro edge hedge
    have hlast :
        edge ≠ Fin.last (n + 2) :=
      (Finset.mem_erase.mp hedge).1
    have hzero :
        edge ≠ 0 :=
      (Finset.mem_erase.mp
        (Finset.mem_erase.mp hedge).2).1
    have hedgePos : 1 ≤ edge.val := by
      have := edge.isLt
      by_contra h
      have hz : edge.val = 0 := by omega
      exact hzero (Fin.ext hz)
    have hedgeUpper : edge.val ≤ n + 1 := by
      have hedgeLt := edge.isLt
      have hneLast : edge.val ≠ n + 2 := by
        intro heq
        exact hlast (Fin.ext (by simpa using heq))
      omega
    let i : Fin (n + 1) :=
      ⟨edge.val - 1, by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change i.val + 1 = edge.val
    dsimp only [i]
    omega
  · intro i _hi
    rfl

theorem norm_r324RenormalizedInteriorCore_le_internalMajorant
    {n : ℕ} (κ : PartialPairing (Fin (n + 2)))
    (v : Fin (n + 2) → T4) :
    ‖r324RenormalizedInteriorCore κ v‖ ≤
      ‖r324InteriorExpandedGreenMajorant κ v‖ := by
  rw [r324RenormalizedInteriorCore_eq_internalDifferenceProduct]
  unfold r324InteriorExpandedGreenMajorant
  rw [norm_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro i _hi
    exact norm_nonneg _
  intro i _hi
  by_cases hi :
      r324InteriorFullEdge n i ∈ extractedRightEdges κ
  · let a :=
      greenFn
        ((assemble 0 0 v)
            (r324InteriorFullEdge n i).castSucc -
          (assemble 0 0 v)
            (r324InteriorFullEdge n i).succ)
    let b :=
      greenFn
        ((assemble 0 0 v)
            (Fin.castLE (by omega)
              (extractedShortcutParent κ
                (r324InteriorFullEdge n i) hi)) -
          (assemble 0 0 v)
            (r324InteriorFullEdge n i).succ)
    have haeq :
        r324InteriorOriginalGreenEdge v i = (a : ℂ) := by
      rfl
    have hbeq :
        r324InteriorShortcutGreenEdge κ v i = (b : ℂ) := by
      unfold r324InteriorShortcutGreenEdge
        extractedShortcutGreenEdge
      rw [dif_pos hi]
    rw [haeq, hbeq]
    have ha : 0 ≤ a := greenFn_nonneg _
    have hb : 0 ≤ b := greenFn_nonneg _
    calc
      ‖(a : ℂ) - (b : ℂ)‖ ≤
          ‖(a : ℂ)‖ + ‖(b : ℂ)‖ :=
        norm_sub_le _ _
      _ = a + b := by
        simp [abs_of_nonneg ha, abs_of_nonneg hb]
      _ = ‖(a : ℂ) + (b : ℂ)‖ := by
        have hcast :
            (a : ℂ) + (b : ℂ) =
              ((a + b : ℝ) : ℂ) := by
          norm_num
        rw [hcast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg ha hb)]
  · simp [r324InteriorShortcutGreenEdge,
      extractedShortcutGreenEdge, hi]

/-- Every endpoint-independent renormalized interior profile is jointly
integrable. -/
theorem integrable_r324RenormalizedInteriorCore
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Integrable (r324RenormalizedInteriorCore κ)
      (Measure.pi fun _ : Fin m => paperMeasure) := by
  rcases m with _ | _ | n
  · have hfun :
        r324RenormalizedInteriorCore κ =
          fun _ : Fin 0 → T4 => (1 : ℂ) := by
      funext v
      simp [r324RenormalizedInteriorCore]
    rw [hfun]
    exact integrable_const 1
  · have hfun :
        r324RenormalizedInteriorCore κ =
          fun _ : Fin 1 → T4 => (1 : ℂ) := by
      funext v
      unfold r324RenormalizedInteriorCore
      have hempty :
          (((Finset.univ : Finset (Fin 2)).erase 0).erase
            (Fin.last 1)) = ∅ := by
        ext i
        fin_cases i <;> simp
      rw [hempty]
      simp
    rw [hfun]
    exact integrable_const 1
  · have hmajor :=
      integrable_r324InteriorExpandedGreenMajorant κ
    exact hmajor.mono
      ((measurable_r324RenormalizedInteriorCore κ)
        |>.aestronglyMeasurable)
      (.of_forall fun v =>
        norm_r324RenormalizedInteriorCore_le_internalMajorant
          κ v)

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The two independent endpoint-free Green profiles have integrable norm
on the doubled internal space. -/
theorem integrable_r324SelectedInteriorSkeletonNormDensity
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Integrable
      (r324SelectedInteriorSkeletonNormDensity κp κm)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let μm := Measure.pi fun _ : Fin m => paperMeasure
  let μ2m := Measure.pi fun _ : Fin (2 * m) => paperMeasure
  let fp : (Fin m → T4) → ℂ :=
    r324RenormalizedInteriorCore κp
  let fm : (Fin m → T4) → ℂ :=
    r324RenormalizedInteriorCore κm
  have hp : Integrable fp μm := by
    simpa only [fp, μm] using
      integrable_r324RenormalizedInteriorCore κp
  have hm : Integrable fm μm := by
    simpa only [fm, μm] using
      integrable_r324RenormalizedInteriorCore κm
  have hprod :
      Integrable
        (fun p : (Fin m → T4) × (Fin m → T4) =>
          fp p.1 * fm p.2)
        (μm.prod μm) :=
    hp.mul_prod hm
  let e := r324DoublePiMeasurableEquiv m
  have he :
      MeasurePreserving e μ2m (μm.prod μm) := by
    simpa only [e, μm, μ2m] using
      measurePreserving_r324DoublePiMeasurableEquiv m
  have hiff :=
    he.integrable_comp_emb e.measurableEmbedding
      (g := fun p : (Fin m → T4) × (Fin m → T4) =>
        fp p.1 * fm p.2)
  have hpull :
      Integrable
        ((fun p : (Fin m → T4) × (Fin m → T4) =>
          fp p.1 * fm p.2) ∘ e)
        μ2m :=
    hiff.mpr hprod
  have hnorm := hpull.norm
  convert hnorm using 1
  funext v
  simp only [Function.comp_apply, e,
    r324DoublePiMeasurableEquiv_apply, fp, fm,
    norm_mul]
  rfl

/-! ## Boundedness of the unexpanded physical covariances -/

/-- At each fixed positive mollifier scale, the complete collection of
unexpanded covariances left after deleting the selected edge is uniformly
bounded in the spatial variables. -/
theorem
    exists_r324MarkedResidualPhysicalCovarianceFactor_bound
    {m : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ v : Fin (2 * m) → T4,
        ρ.r324MarkedResidualBlockUnselectedCovarianceMass
              ε κp κm π selected v *
            ‖ρ.r324UnmarkedResidualBlockProduct
              ε κp κm π selected v‖ ≤
          B := by
  obtain ⟨Cη, hCη, heta⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let A : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  let markedSet : Finset (Fin (2 * m)) :=
    ((r324MarkedResidualBlock κp κm π selected).filter
      (fun i => i < momentCombinedPairing κp κm π i)).erase
      (r324ResidualMarkedLowerEndpoint selected)
  let unmarkedBlocks : Finset (Finset (Fin (2 * m))) :=
    (nonemptyMomentResidualCollapseBlocks κp κm π).toFinset.erase
      (r324MarkedResidualBlock κp κm π selected)
  let blockLowerSet : Finset (Fin (2 * m)) → Finset (Fin (2 * m)) :=
    fun block =>
      block.filter
        (fun i => i < momentCombinedPairing κp κm π i)
  let markedBound : ℝ :=
    ∏ _i ∈ markedSet, (1 + A)
  let unmarkedBound : ℝ :=
    ∏ block ∈ unmarkedBlocks,
      ∏ _i ∈ blockLowerSet block, (1 + A)
  let B := markedBound * unmarkedBound
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbase : 0 ≤ 1 + A := by linarith
  have hetaReal :
      ∀ z : T4, ρ.etaEpsT4 ε z ≤ 1 + A := by
    intro z
    calc
      ρ.etaEpsT4 ε z ≤ A := by
        simpa only [A] using heta hε hε1 z
      _ ≤ 1 + A := by linarith
  have hmarkedBound : 0 ≤ markedBound := by
    dsimp only [markedBound]
    exact Finset.prod_nonneg fun _ _ => hbase
  have hunmarkedBound : 0 ≤ unmarkedBound := by
    dsimp only [unmarkedBound]
    exact Finset.prod_nonneg fun _ _ =>
      Finset.prod_nonneg fun _ _ => hbase
  refine ⟨B, mul_nonneg hmarkedBound hunmarkedBound, ?_⟩
  intro v
  have hmarked :
      ρ.r324MarkedResidualBlockUnselectedCovarianceMass
          ε κp κm π selected v ≤ markedBound := by
    unfold r324MarkedResidualBlockUnselectedCovarianceMass
    change
      (∏ i ∈ markedSet,
        ‖(ρ.etaEpsT4 ε
          (v i -
            v (momentCombinedPairing κp κm π i)) : ℂ)‖) ≤
        markedBound
    dsimp only [markedBound]
    apply Finset.prod_le_prod
    · intro i _hi
      exact norm_nonneg _
    intro i _hi
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        (ρ.etaEpsT4_nonneg ε
          (v i -
            v (momentCombinedPairing κp κm π i)))]
    exact hetaReal _
  have hunmarked :
      ‖ρ.r324UnmarkedResidualBlockProduct
          ε κp κm π selected v‖ ≤ unmarkedBound := by
    unfold r324UnmarkedResidualBlockProduct
    change
      ‖∏ block ∈ unmarkedBlocks,
          (pairingCovarianceProductOn ρ ε
            (momentCombinedPairing κp κm π) block v : ℂ)‖ ≤
        unmarkedBound
    rw [norm_prod]
    dsimp only [unmarkedBound]
    apply Finset.prod_le_prod
    · intro block _hblock
      exact norm_nonneg _
    intro block _hblock
    unfold pairingCovarianceProductOn
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun i _ =>
        ρ.etaEpsT4_nonneg ε
          (v i -
            v (momentCombinedPairing κp κm π i)))]
    change
      (∏ i ∈ blockLowerSet block,
          ρ.etaEpsT4 ε
            (v i -
              v (momentCombinedPairing κp κm π i))) ≤
        ∏ _i ∈ blockLowerSet block, (1 + A)
    apply Finset.prod_le_prod
    · intro i _hi
      exact ρ.etaEpsT4_nonneg ε _
    intro i _hi
    exact hetaReal _
  change
    ρ.r324MarkedResidualBlockUnselectedCovarianceMass
          ε κp κm π selected v *
        ‖ρ.r324UnmarkedResidualBlockProduct
          ε κp κm π selected v‖ ≤
      markedBound * unmarkedBound
  exact mul_le_mul hmarked hunmarked
    (norm_nonneg _)
    hmarkedBound

/-! ## Genuine selected-cell complement finiteness -/

/-- The physical complement is globally integrable at each fixed positive
mollifier scale.  No covariance has been Fourier-expanded in this proof. -/
theorem integrable_r324MarkedResidualPhysicalComplementMass
    {m : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp) :
    Integrable
      (ρ.r324MarkedResidualPhysicalComplementMass
        ε κp κm π selected)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  obtain ⟨B, _hB, hbound⟩ :=
    ρ.exists_r324MarkedResidualPhysicalCovarianceFactor_bound
      hε hε1 κp κm π selected
  have hskeleton :=
    integrable_r324SelectedInteriorSkeletonNormDensity κp κm
  let covarianceFactor :
      (Fin (2 * m) → T4) → ℝ :=
    fun v =>
      ρ.r324MarkedResidualBlockUnselectedCovarianceMass
          ε κp κm π selected v *
        ‖ρ.r324UnmarkedResidualBlockProduct
          ε κp κm π selected v‖
  have hcovarianceMeasurable :
      Measurable covarianceFactor := by
    dsimp only [covarianceFactor]
    exact
      (ρ.measurable_r324MarkedResidualBlockUnselectedCovarianceMass
        ε κp κm π selected).mul
      (ρ.measurable_r324UnmarkedResidualBlockProduct
        ε κp κm π selected).norm
  have hcovarianceNonneg :
      ∀ v, 0 ≤ covarianceFactor v := by
    intro v
    dsimp only [covarianceFactor]
    exact mul_nonneg
      (ρ.r324MarkedResidualBlockUnselectedCovarianceMass_nonneg
        ε κp κm π selected v)
      (norm_nonneg _)
  have hcovarianceNormBound :
      ∀ v, ‖covarianceFactor v‖ ≤ B := by
    intro v
    rw [Real.norm_eq_abs,
      abs_of_nonneg (hcovarianceNonneg v)]
    exact hbound v
  have hproduct :=
    hskeleton.mul_bdd
      hcovarianceMeasurable.aestronglyMeasurable
      (.of_forall hcovarianceNormBound)
  convert hproduct using 1
  funext v
  unfold r324MarkedResidualPhysicalComplementMass
    covarianceFactor
  ring

/-- The extended physical-complement mass on every genuine selected cell
is finite.  This discharges the qualitative hypothesis of the marked-mode
Tonelli bridge. -/
theorem r324MarkedResidualPhysicalComplementCellLIntegral_lt_top
    {m : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (cell : Fin (2 * m) → Z4) :
    ρ.r324MarkedResidualPhysicalComplementCellLIntegral
        ε κp κm π selected hε cell < ∞ := by
  unfold r324MarkedResidualPhysicalComplementCellLIntegral
  exact
    (ρ.integrable_r324MarkedResidualPhysicalComplementMass
      hε hε1 κp κm π selected)
      |>.integrableOn
      |>.setLIntegral_lt_top

/-- Consequently, the complete marked Fourier-mode family is absolutely
summable after integration on every genuine selected cell. -/
theorem
    tsum_r324MarkedResidualPhysicalInteriorModeCellLIntegral_lt_top_unconditional
    {m : ℕ} {ε L : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (selected : R324ResidualCovarianceSlot κp)
    (cell : Fin (2 * m) → Z4) :
    (∑' k : Z4,
      ρ.r324MarkedResidualPhysicalInteriorModeCellLIntegral
        ε L κp κm π selected hε cell k) < ∞ := by
  exact
    ρ.tsum_r324MarkedResidualPhysicalInteriorModeCellLIntegral_lt_top
      κp κm π selected hε cell
      (ρ.r324MarkedResidualPhysicalComplementCellLIntegral_lt_top
        hε hε1 κp κm π selected cell)

end SmoothCutoff

end

end Anderson4D
