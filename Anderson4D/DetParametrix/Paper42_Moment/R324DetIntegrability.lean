import Anderson4D.DetParametrix.Paper42_Moment.R324TreeIntegrability
import Anderson4D.Continuum.CovariancePoissonDeterministic

/-!
# Joint integrability of the R-324 deterministic contractions

This file expands the renormalized Green differences in the two copies of
(4.18).  Choosing either the original edge or its shortcut at every
extracted right endpoint produces an increasing Green tree, so the analytic
result of `R324TreeIntegrability.lean` applies term by term.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Extracted right edges and their shortcut parents -/

/-- Membership in `extractedRightEdges` carries an actual extracted
interval with that right edge. -/
theorem exists_extractedPairOfRightEdge
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) (hi : i ∈ extractedRightEdges κ) :
    ∃ p, p ∈ extract κ ∧ extractedRightEdge p = i := by
  simpa only [extractedRightEdges, List.mem_toFinset,
    List.mem_map] using hi

/-- The unique extracted interval whose replaced right edge is `i`. -/
noncomputable def extractedPairOfRightEdge
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) (hi : i ∈ extractedRightEdges κ) :
    Fin m × Fin m :=
  Classical.choose (exists_extractedPairOfRightEdge κ i hi)

theorem extractedPairOfRightEdge_mem
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) (hi : i ∈ extractedRightEdges κ) :
    extractedPairOfRightEdge κ i hi ∈ extract κ :=
  (Classical.choose_spec
    (exists_extractedPairOfRightEdge κ i hi)).1

theorem extractedRightEdge_extractedPairOfRightEdge
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) (hi : i ∈ extractedRightEdges κ) :
    extractedRightEdge (extractedPairOfRightEdge κ i hi) = i :=
  (Classical.choose_spec
    (exists_extractedPairOfRightEdge κ i hi)).2

/-- The predecessor of an ordinary chain edge, in dependent parent form. -/
def ordinaryEdgeParent {m : ℕ} (i : Fin (m + 1)) :
    Fin (i.val + 1) :=
  ⟨i.val, by omega⟩

/-- The earlier endpoint of the shortcut replacing an extracted right
edge. -/
def extractedShortcutParent
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) (hi : i ∈ extractedRightEdges κ) :
    Fin (i.val + 1) := by
  let p := extractedPairOfRightEdge κ i hi
  refine ⟨p.1.val + 1, ?_⟩
  have hpFin := extract_spec κ p
    (extractedPairOfRightEdge_mem κ i hi)
  have hp : p.1.val ≤ p.2.val := hpFin
  have hedgeFin :=
    congrArg Fin.val
      (extractedRightEdge_extractedPairOfRightEdge κ i hi)
  have hedge : p.2.val + 1 = i.val := by
    simpa only [extractedRightEdge_val] using hedgeFin
  omega

/-- Parent map of one fully expanded renormalized Green summand.  Membership
in `original` means that the original chain edge is chosen; otherwise the
shortcut is chosen when it exists. -/
def expandedGreenTreeParent
    {m : ℕ} (κ : PartialPairing (Fin m))
    (original : Finset (Fin (m + 1))) :
    IncreasingTreeParent (m + 1) :=
  fun i =>
    if i ∈ original then ordinaryEdgeParent i
    else if hi : i ∈ extractedRightEdges κ then
      extractedShortcutParent κ i hi
    else ordinaryEdgeParent i

/-- Original Green edge with right endpoint `i+1`. -/
def originalGreenEdge {m : ℕ}
    (x : Fin (m + 2) → T4) (i : Fin (m + 1)) : ℂ :=
  (greenFn (x i.castSucc - x i.succ) : ℂ)

@[simp]
theorem extractedRightEdge_castSucc
    {m : ℕ} (p : Fin m × Fin m) :
    (extractedRightEdge p).castSucc = varIdx p.2 := by
  apply Fin.ext
  rfl

@[simp]
theorem extractedRightEdge_succ
    {m : ℕ} (p : Fin m × Fin m) :
    (extractedRightEdge p).succ =
      (⟨p.2.val + 2, by have := p.2.isLt; omega⟩ :
        Fin (m + 2)) := by
  apply Fin.ext
  rfl

/-- Shortcut Green edge at an extracted right endpoint, and zero at an
unextracted endpoint.  The zero makes the product-of-sums expansion uniform
over all edges. -/
def extractedShortcutGreenEdge
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) (i : Fin (m + 1)) : ℂ :=
  if hi : i ∈ extractedRightEdges κ then
    (greenFn
      (x (Fin.castLE (by omega)
          (extractedShortcutParent κ i hi)) -
        x i.succ) : ℂ)
  else 0

/-- One term in the powerset expansion of the product of edge sums. -/
def expandedGreenBranch
    {m : ℕ} (κ : PartialPairing (Fin m))
    (original : Finset (Fin (m + 1)))
    (x : Fin (m + 2) → T4) : ℂ :=
  (∏ i ∈ original, originalGreenEdge x i) *
    ∏ i ∈ originalᶜ, extractedShortcutGreenEdge κ x i

private theorem expandedGreenTreeParentVertex_original
    {m : ℕ} (κ : PartialPairing (Fin m))
    (original : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) (hi : i ∈ original) :
    increasingTreeParentVertex
        (expandedGreenTreeParent κ original) i =
      i.castSucc := by
  apply Fin.ext
  simp [increasingTreeParentVertex,
    expandedGreenTreeParent, hi, ordinaryEdgeParent]

private theorem expandedGreenTreeParentVertex_shortcut
    {m : ℕ} (κ : PartialPairing (Fin m))
    (original : Finset (Fin (m + 1)))
    (i : Fin (m + 1)) (hi : i ∉ original)
    (hextract : i ∈ extractedRightEdges κ) :
    increasingTreeParentVertex
        (expandedGreenTreeParent κ original) i =
      Fin.castLE (by omega)
        (extractedShortcutParent κ i hextract) := by
  apply Fin.ext
  simp [increasingTreeParentVertex,
    expandedGreenTreeParent, hi, hextract]

/-- If every chosen shortcut really is extracted, the corresponding branch
is exactly the increasing-tree Green product. -/
theorem expandedGreenBranch_eq_tree
    {m : ℕ} (κ : PartialPairing (Fin m))
    (original : Finset (Fin (m + 1)))
    (hshortcut :
      ∀ i : Fin (m + 1), i ∉ original →
        i ∈ extractedRightEdges κ) :
    expandedGreenBranch κ original =
      increasingTreeGreenProduct
        (expandedGreenTreeParent κ original) := by
  funext x
  have hfactor :
      ∀ i : Fin (m + 1),
        (greenFn
          (x (increasingTreeParentVertex
              (expandedGreenTreeParent κ original) i) -
            x i.succ) : ℂ) =
          if i ∈ original then originalGreenEdge x i
          else extractedShortcutGreenEdge κ x i := by
    intro i
    by_cases hi : i ∈ original
    · rw [if_pos hi,
        expandedGreenTreeParentVertex_original κ original i hi]
      rfl
    · have hextract := hshortcut i hi
      rw [if_neg hi,
        expandedGreenTreeParentVertex_shortcut
          κ original i hi hextract]
      simp only [extractedShortcutGreenEdge, dif_pos hextract]
  unfold expandedGreenBranch increasingTreeGreenProduct
  rw [show
      (∏ i : Fin (m + 1),
          (greenFn
            (x (increasingTreeParentVertex
                (expandedGreenTreeParent κ original) i) -
              x i.succ) : ℂ)) =
        ∏ i : Fin (m + 1),
          if i ∈ original then originalGreenEdge x i
          else extractedShortcutGreenEdge κ x i by
    apply Finset.prod_congr rfl
    intro i _hi
    exact hfactor i]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  have hcompl :
      {i ∈ (Finset.univ : Finset (Fin (m + 1))) |
          ¬i ∈ original} =
        originalᶜ := by
    ext i
    simp
  rw [hcompl]

/-- Every branch in the uniform powerset expansion is jointly integrable.
Branches selecting a nonexistent shortcut vanish; all other branches are
increasing Green trees. -/
theorem integrable_expandedGreenBranch
    {m : ℕ} (κ : PartialPairing (Fin m))
    (original : Finset (Fin (m + 1))) :
    Integrable (expandedGreenBranch κ original)
      (Measure.pi fun _ : Fin (m + 2) => paperMeasure) := by
  by_cases hshortcut :
      ∀ i : Fin (m + 1), i ∉ original →
        i ∈ extractedRightEdges κ
  · rw [expandedGreenBranch_eq_tree κ original hshortcut]
    exact integrable_increasingTreeGreenProduct
      (expandedGreenTreeParent κ original)
  · push Not at hshortcut
    obtain ⟨i, hi, hnotExtracted⟩ := hshortcut
    have hiCompl : i ∈ originalᶜ := by
      simpa using hi
    have hzero :
        ∀ x : Fin (m + 2) → T4,
          (∏ j ∈ originalᶜ,
            extractedShortcutGreenEdge κ x j) = 0 := by
      intro x
      apply Finset.prod_eq_zero hiCompl
      simp [extractedShortcutGreenEdge, hnotExtracted]
    have hfun :
        expandedGreenBranch κ original =
          fun _ : Fin (m + 2) → T4 => 0 := by
      funext x
      unfold expandedGreenBranch
      rw [hzero x, mul_zero]
    rw [hfun]
    exact integrable_zero _ _ _

/-- Nonnegative complex majorant obtained by replacing every extracted
difference by the sum of its two Green terms. -/
def expandedGreenMajorant
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) : ℂ :=
  ∏ i : Fin (m + 1),
    (originalGreenEdge x i +
      extractedShortcutGreenEdge κ x i)

/-- The edgewise majorant is a finite sum of the integrable expanded-tree
branches. -/
theorem expandedGreenMajorant_eq_sum_branches
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    expandedGreenMajorant κ =
      fun x => ∑ original : Finset (Fin (m + 1)),
        expandedGreenBranch κ original x := by
  funext x
  unfold expandedGreenMajorant expandedGreenBranch
  exact Fintype.prod_add
    (fun i : Fin (m + 1) => originalGreenEdge x i)
    (fun i : Fin (m + 1) =>
      extractedShortcutGreenEdge κ x i)

/-- Joint integrability of the complete Green edge majorant. -/
theorem integrable_expandedGreenMajorant
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Integrable (expandedGreenMajorant κ)
      (Measure.pi fun _ : Fin (m + 2) => paperMeasure) := by
  rw [expandedGreenMajorant_eq_sum_branches]
  exact integrable_finsetSum Finset.univ fun original _ =>
    integrable_expandedGreenBranch κ original

/-! ## Comparison with the renormalized Green skeleton -/

/-- The Green-only part of `detIntegrand`, before the bounded covariance
product is attached. -/
def renormalizedGreenSkeleton
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) : ℂ :=
  (∏ i : Fin (m + 1),
      if i ∈ extractedRightEdges κ then 1
      else originalGreenEdge x i) *
    ((extract κ).map fun p =>
      originalGreenEdge x (extractedRightEdge p) -
        (greenFn
          (x (varIdx p.1) -
            x (extractedRightEdge p).succ) : ℂ)).prod

/-- Distinct extracted right endpoints make the extraction list itself
duplicate-free. -/
theorem extract_nodup
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (extract κ).Nodup :=
  List.Nodup.of_map Prod.snd (extract_map_snd_nodup κ)

/-- Two extracted intervals with the same replaced right edge coincide. -/
theorem extractedRightEdge_injective_on_extract
    {m : ℕ} (κ : PartialPairing (Fin m))
    {p q : Fin m × Fin m}
    (hp : p ∈ extract κ) (hq : q ∈ extract κ)
    (hedge : extractedRightEdge p = extractedRightEdge q) :
    p = q := by
  have hsnd : p.2 = q.2 := by
    apply Fin.ext
    have hval := congrArg Fin.val hedge
    simp only [extractedRightEdge_val] at hval
    omega
  exact List.inj_on_of_nodup_map
    (extract_map_snd_nodup κ) hp hq hsnd

/-- Every extracted interval contributes its right edge to the replacement
finset. -/
theorem extractedRightEdge_mem_extractedRightEdges
    {m : ℕ} (κ : PartialPairing (Fin m))
    (p : Fin m × Fin m) (hp : p ∈ extract κ) :
    extractedRightEdge p ∈ extractedRightEdges κ := by
  unfold extractedRightEdges
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

/-- The chosen inverse of an extracted right edge returns the original
interval. -/
theorem extractedPairOfRightEdge_eq
    {m : ℕ} (κ : PartialPairing (Fin m))
    (p : Fin m × Fin m) (hp : p ∈ extract κ) :
    extractedPairOfRightEdge κ (extractedRightEdge p)
        (extractedRightEdge_mem_extractedRightEdges κ p hp) =
      p := by
  let hedge :=
    extractedRightEdge_mem_extractedRightEdges κ p hp
  apply extractedRightEdge_injective_on_extract κ
  · exact extractedPairOfRightEdge_mem κ
      (extractedRightEdge p) hedge
  · exact hp
  · exact extractedRightEdge_extractedPairOfRightEdge κ
      (extractedRightEdge p) hedge

/-- Reindex a product over the extracted right-edge finset by the original
extraction list. -/
theorem prod_extractedRightEdges_eq_extract_prod
    {m : ℕ} {M : Type*} [CommMonoid M]
    (κ : PartialPairing (Fin m))
    (f : Fin (m + 1) → M) :
    (∏ i ∈ extractedRightEdges κ, f i) =
      ((extract κ).map fun p =>
        f (extractedRightEdge p)).prod := by
  have hinj :
      ∀ p ∈ extract κ, ∀ q ∈ extract κ,
        extractedRightEdge p = extractedRightEdge q →
          p = q := by
    intro p hp q hq h
    exact extractedRightEdge_injective_on_extract κ hp hq h
  have hnodup :
      ((extract κ).map extractedRightEdge).Nodup :=
    (extract_nodup κ).map_on hinj
  unfold extractedRightEdges
  rw [List.prod_toFinset f hnodup]
  simp only [List.map_map, Function.comp_def]

@[simp]
theorem extractedShortcutGreenEdge_extractedRightEdge
    {m : ℕ} (κ : PartialPairing (Fin m))
    (p : Fin m × Fin m) (hp : p ∈ extract κ)
    (x : Fin (m + 2) → T4) :
    extractedShortcutGreenEdge κ x (extractedRightEdge p) =
      (greenFn
        (x (varIdx p.1) -
          x (extractedRightEdge p).succ) : ℂ) := by
  let hedge :=
    extractedRightEdge_mem_extractedRightEdges κ p hp
  unfold extractedShortcutGreenEdge
  rw [dif_pos hedge]
  congr 2
  congr 1
  apply congrArg x
  apply Fin.ext
  simp only [Fin.castLE, extractedShortcutParent]
  rw [extractedPairOfRightEdge_eq κ p hp]
  rfl

/-- The uniform edge product with subtraction.  Unextracted shortcut terms
are zero, while extracted ones reproduce the renormalized differences. -/
def expandedGreenDifferenceProduct
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) : ℂ :=
  ∏ i : Fin (m + 1),
    (originalGreenEdge x i -
      extractedShortcutGreenEdge κ x i)

private theorem prod_if_extracted_else_original
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) :
    (∏ i : Fin (m + 1),
        if i ∈ extractedRightEdges κ then 1
        else originalGreenEdge x i) =
      ∏ i ∈ (Finset.univ : Finset (Fin (m + 1))) \
          extractedRightEdges κ,
        originalGreenEdge x i := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1
  ext i
  simp

/-- The Green skeleton in the closed renormalized integrand is exactly the
uniform edge-difference product. -/
theorem renormalizedGreenSkeleton_eq_differenceProduct
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    renormalizedGreenSkeleton κ =
      expandedGreenDifferenceProduct κ := by
  funext x
  let E := extractedRightEdges κ
  let U : Finset (Fin (m + 1)) := Finset.univ
  let F : Fin (m + 1) → ℂ := fun i =>
    originalGreenEdge x i -
      extractedShortcutGreenEdge κ x i
  have hEU : E ⊆ U := Finset.subset_univ E
  have hunextracted :
      (∏ i ∈ U \ E, F i) =
        ∏ i ∈ U \ E, originalGreenEdge x i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiE : i ∉ extractedRightEdges κ := by
      exact (Finset.mem_sdiff.mp hi).2
    unfold F
    simp [extractedShortcutGreenEdge, hiE]
  have hextracted :
      (∏ i ∈ E, F i) =
        ((extract κ).map fun p =>
          originalGreenEdge x (extractedRightEdge p) -
            (greenFn
              (x (varIdx p.1) -
                x (extractedRightEdge p).succ) : ℂ)).prod := by
    change
      (∏ i ∈ extractedRightEdges κ,
          (fun i =>
            originalGreenEdge x i -
              extractedShortcutGreenEdge κ x i) i) = _
    rw [prod_extractedRightEdges_eq_extract_prod κ]
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [extractedShortcutGreenEdge_extractedRightEdge κ p hp x]
  have hpartition :
      (∏ i ∈ U, F i) =
        (∏ i ∈ U \ E, F i) * ∏ i ∈ E, F i :=
    (Finset.prod_sdiff hEU).symm
  unfold renormalizedGreenSkeleton
  rw [prod_if_extracted_else_original, ← hunextracted,
    ← hextracted, ← hpartition]
  rfl

theorem measurable_originalGreenEdge
    {m : ℕ} (i : Fin (m + 1)) :
    Measurable
      (fun x : Fin (m + 2) → T4 =>
        originalGreenEdge x i) := by
  unfold originalGreenEdge
  exact
    (measurable_greenFn.comp
      ((measurable_pi_apply i.castSucc).sub
        (measurable_pi_apply i.succ))).complex_ofReal

theorem measurable_extractedShortcutGreenEdge
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) :
    Measurable
      (fun x : Fin (m + 2) → T4 =>
        extractedShortcutGreenEdge κ x i) := by
  by_cases hi : i ∈ extractedRightEdges κ
  · simp only [extractedShortcutGreenEdge, dif_pos hi]
    exact
      (measurable_greenFn.comp
        ((measurable_pi_apply
          (Fin.castLE (by omega)
            (extractedShortcutParent κ i hi))).sub
          (measurable_pi_apply i.succ))).complex_ofReal
  · simp [extractedShortcutGreenEdge, hi]

theorem measurable_expandedGreenDifferenceProduct
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Measurable (expandedGreenDifferenceProduct κ) := by
  unfold expandedGreenDifferenceProduct
  apply Finset.measurable_prod
  intro i _hi
  exact (measurable_originalGreenEdge i).sub
    (measurable_extractedShortcutGreenEdge κ i)

/-- Edgewise triangle inequality between the signed renormalized expansion
and its nonnegative product-of-sums majorant. -/
theorem norm_expandedGreenDifferenceProduct_le
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) :
    ‖expandedGreenDifferenceProduct κ x‖ ≤
      ‖expandedGreenMajorant κ x‖ := by
  unfold expandedGreenDifferenceProduct expandedGreenMajorant
  rw [norm_prod, norm_prod]
  apply Finset.prod_le_prod
  · intro i _hi
    exact norm_nonneg _
  intro i _hi
  by_cases hi : i ∈ extractedRightEdges κ
  · let a := greenFn (x i.castSucc - x i.succ)
    let b := greenFn
      (x (Fin.castLE (by omega)
          (extractedShortcutParent κ i hi)) -
        x i.succ)
    have haeq :
        originalGreenEdge x i = (a : ℂ) := by
      rfl
    have hbeq :
        extractedShortcutGreenEdge κ x i = (b : ℂ) := by
      unfold extractedShortcutGreenEdge
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
  · simp [extractedShortcutGreenEdge, hi]

/-- Joint integrability of the signed renormalized Green skeleton. -/
theorem integrable_renormalizedGreenSkeleton
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Integrable (renormalizedGreenSkeleton κ)
      (Measure.pi fun _ : Fin (m + 2) => paperMeasure) := by
  have hmajor := integrable_expandedGreenMajorant κ
  rw [renormalizedGreenSkeleton_eq_differenceProduct]
  exact hmajor.mono
    (measurable_expandedGreenDifferenceProduct κ).aestronglyMeasurable
    (.of_forall fun x =>
      norm_expandedGreenDifferenceProduct_le κ x)

/-! ## Bounded covariance factor and the full deterministic integrand -/

/-- Covariance part of one deterministic closed integrand, coerced to the
same complex scalar field as the Green skeleton. -/
def detCovarianceFactor
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) : ℂ :=
  ((∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε
        (x (varIdx i) - x (varIdx (κ i)))) : ℝ)

theorem measurable_detCovarianceFactor
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) :
    Measurable (detCovarianceFactor ρ ε κ) := by
  unfold detCovarianceFactor
  apply Measurable.complex_ofReal
  apply Finset.measurable_prod
  intro i _hi
  exact (ρ.measurable_etaEpsT4 ε).comp
    ((measurable_pi_apply (varIdx i)).sub
      (measurable_pi_apply (varIdx (κ i))))

/-- At a positive small scale the covariance product is uniformly bounded
on the compact physical product space. -/
theorem exists_norm_detCovarianceFactor_le
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : Fin (m + 2) → T4,
        ‖detCovarianceFactor ρ ε κ x‖ ≤ B := by
  obtain ⟨Cη, hCη, heta⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let A : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  let B : ℝ := (1 + A) ^ m
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbase : 1 ≤ 1 + A := by linarith
  refine ⟨B, pow_nonneg (by linarith) _, ?_⟩
  intro x
  unfold detCovarianceFactor
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg fun i _ =>
      ρ.etaEpsT4_nonneg ε
        (x (varIdx i) - x (varIdx (κ i))))]
  calc
    (∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        ρ.etaEpsT4 ε
          (x (varIdx i) - x (varIdx (κ i)))) ≤
        ∏ _i ∈ κ.pairSupport.filter (fun i => i < κ i),
          (1 + A) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact ρ.etaEpsT4_nonneg ε
          (x (varIdx i) - x (varIdx (κ i)))
      · intro i _hi
        calc
          ρ.etaEpsT4 ε
              (x (varIdx i) - x (varIdx (κ i))) ≤ A := by
            simpa only [A] using
              heta hε hε1
                (x (varIdx i) - x (varIdx (κ i)))
          _ ≤ 1 + A := by linarith
    _ = (1 + A) ^
        (κ.pairSupport.filter (fun i => i < κ i)).card := by
      simp
    _ ≤ (1 + A) ^ m := by
      apply pow_le_pow_right₀ hbase
      calc
        (κ.pairSupport.filter (fun i => i < κ i)).card ≤
            (Finset.univ : Finset (Fin m)).card :=
          Finset.card_le_univ _
        _ = m := by simp
    _ = B := rfl

/-- Exact factorization of the frozen deterministic integrand into its
signed Green skeleton and bounded covariance product. -/
theorem detIntegrand_eq_renormalizedGreenSkeleton_mul_covariance
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) :
    (detIntegrand ρ ε m κ x : ℂ) =
      renormalizedGreenSkeleton κ x *
        detCovarianceFactor ρ ε κ x := by
  have hchain :
      ((∏ e : Fin (m + 1),
          if e ∈ extractedRightEdges κ then 1
          else greenFn (x e.castSucc - x e.succ) : ℝ) : ℂ) =
        ∏ e : Fin (m + 1),
          if e ∈ extractedRightEdges κ then 1
          else originalGreenEdge x e := by
    change
      Complex.ofRealHom
          (∏ e : Fin (m + 1),
            if e ∈ extractedRightEdges κ then 1
            else greenFn (x e.castSucc - x e.succ)) =
        _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro e _he
    by_cases h : e ∈ extractedRightEdges κ
    · simp [h]
    · simp [h, originalGreenEdge]
  have hdiff :
      ((((extract κ).map (fun p =>
          greenFn
              (x (varIdx p.2) -
                x (⟨p.2.val + 2,
                  by have := p.2.isLt; omega⟩ :
                    Fin (m + 2))) -
            greenFn
              (x (varIdx p.1) -
                x (⟨p.2.val + 2,
                  by have := p.2.isLt; omega⟩ :
                    Fin (m + 2))))).prod : ℝ) : ℂ) =
        ((extract κ).map (fun p =>
          originalGreenEdge x (extractedRightEdge p) -
            (greenFn
              (x (varIdx p.1) -
                x (extractedRightEdge p).succ) : ℂ))).prod := by
    change
      Complex.ofRealHom
          (((extract κ).map (fun p =>
            greenFn
                (x (varIdx p.2) -
                  x (⟨p.2.val + 2,
                    by have := p.2.isLt; omega⟩ :
                      Fin (m + 2))) -
              greenFn
                (x (varIdx p.1) -
                  x (⟨p.2.val + 2,
                    by have := p.2.isLt; omega⟩ :
                      Fin (m + 2))))).prod) =
        _
    rw [map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _hp
    simp [originalGreenEdge]
  rw [← detIntegrandWith_green_eq_detIntegrand
    ρ ε m κ x]
  unfold detIntegrandWith renormalizedGreenSkeleton
  unfold chainEdgeWith diffFactorWith
  unfold detCovarianceFactor
  rw [Complex.ofReal_mul, Complex.ofReal_mul,
    hchain, hdiff]

/-- Joint integrability of every deterministic closed-form parametrix
integrand in all of its `m+2` spatial vertices. -/
theorem integrable_detIntegrand_joint
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Integrable
      (fun x : Fin (m + 2) → T4 =>
        (detIntegrand ρ ε m κ x : ℂ))
      (Measure.pi fun _ => paperMeasure) := by
  obtain ⟨B, _hB, hcovBound⟩ :=
    exists_norm_detCovarianceFactor_le ρ hε hε1 κ
  have hprod :=
    (integrable_renormalizedGreenSkeleton κ).mul_bdd
      (measurable_detCovarianceFactor ρ ε κ).aestronglyMeasurable
      (.of_forall hcovBound)
  convert hprod using 1
  funext x
  exact
    detIntegrand_eq_renormalizedGreenSkeleton_mul_covariance
      ρ ε κ x

/-! ## Flat and doubled physical coordinates -/

/-- Split the first and last coordinates of a complete parametrix tuple.
Its inverse is exactly `assemble`. -/
def r324FlatAssembleMeasurableEquiv (m : ℕ) :
    (Fin (m + 2) → T4) ≃ᵐ
      T4 × (T4 × (Fin m → T4)) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 2) => T4) 0).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (m + 1) => T4) (Fin.last m)))

@[simp]
theorem r324FlatAssembleMeasurableEquiv_symm_apply
    (m : ℕ) (x y : T4) (v : Fin m → T4) :
    (r324FlatAssembleMeasurableEquiv m).symm (x, y, v) =
      assemble x y v := by
  simp only [r324FlatAssembleMeasurableEquiv,
    MeasurableEquiv.trans_symm,
    MeasurableEquiv.trans_apply]
  have hprod :
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 1) => T4) (Fin.last m))).symm
          (x, y, v) =
        (x, (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 1) => T4) (Fin.last m)).symm
            (y, v)) := by
    rfl
  rw [hprod]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [assemble]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [assemble]
    · simp [assemble, show k.val ≠ m by omega]

/-- The complete-tuple/flat-coordinate split preserves the paper's Haar
product measures. -/
theorem measurePreserving_r324FlatAssembleMeasurableEquiv
    (m : ℕ) :
    MeasurePreserving
      (r324FlatAssembleMeasurableEquiv m)
      (Measure.pi fun _ : Fin (m + 2) => paperMeasure)
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin m => paperMeasure))) := by
  have hhead :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 2) => T4) 0)
        (Measure.pi fun _ : Fin (m + 2) => paperMeasure)
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (m + 1) => paperMeasure)) := by
    simpa using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 2) => paperMeasure) 0)
  have hlast :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (m + 1) => T4) (Fin.last m))
        (Measure.pi fun _ : Fin (m + 1) => paperMeasure)
        (paperMeasure.prod
          (Measure.pi fun _ : Fin m => paperMeasure)) := by
    simpa only [Fin.succAbove_last] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => paperMeasure) (Fin.last m))
  exact ((MeasurePreserving.id paperMeasure).prod hlast).comp hhead

/-- Joint integrability in the paper's flat `(x,y,v)` coordinates. -/
theorem integrable_detIntegrand_flat
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    Integrable
      (fun p : T4 × (T4 × (Fin m → T4)) =>
        (detIntegrand ρ ε m κ
          (assemble p.1 p.2.1 p.2.2) : ℂ))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin m => paperMeasure))) := by
  let e := r324FlatAssembleMeasurableEquiv m
  let μ := Measure.pi fun _ : Fin (m + 2) => paperMeasure
  let ν :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin m => paperMeasure))
  have hp : MeasurePreserving e μ ν :=
    measurePreserving_r324FlatAssembleMeasurableEquiv m
  have hsource :=
    integrable_detIntegrand_joint ρ hε hε1 κ
  have htarget :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          (detIntegrand ρ ε m κ (e.symm p) : ℂ))
        ν := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p : T4 × (T4 × (Fin m → T4)) =>
          (detIntegrand ρ ε m κ (e.symm p) : ℂ))
    apply hiff.mp
    convert hsource using 1
    funext x
    simp only [Function.comp_apply, e,
      MeasurableEquiv.symm_apply_apply]
  convert htarget using 1
  funext p
  rcases p with ⟨x, y, v⟩
  exact congrArg (fun q => (detIntegrand ρ ε m κ q : ℂ))
    (r324FlatAssembleMeasurableEquiv_symm_apply m x y v).symm

/-- Move the middle coordinate of a triple to the front.  This small
equivalence is used twice to regroup the doubled physical variables without
asserting any pointwise Fubini statement. -/
def r324MoveMiddleMeasurableEquiv
    (A B C : Type*) [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] :
    A × (B × C) ≃ᵐ B × (A × C) :=
  (MeasurableEquiv.prodAssoc (α := A) (β := B) (γ := C)).symm.trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
      (MeasurableEquiv.refl C)).trans
      (MeasurableEquiv.prodAssoc (α := B) (β := A) (γ := C)))

theorem measurePreserving_r324MoveMiddleMeasurableEquiv
    {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (τ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving
      (r324MoveMiddleMeasurableEquiv A B C)
      (μ.prod (ν.prod τ))
      (ν.prod (μ.prod τ)) := by
  exact
    (measurePreserving_prodAssoc ν μ τ).comp
      (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
        (MeasurePreserving.id τ)).comp
          (measurePreserving_prodAssoc μ ν τ).symm)

/-- Split a doubled tuple according to its left and right moment labels. -/
def r324DoublePiMeasurableEquiv (m : ℕ) :
    (Fin (2 * m) → T4) ≃ᵐ
      (Fin m → T4) × (Fin m → T4) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (2 * m) => T4)
      (momentDoubleFinEquiv m)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m => T4))

@[simp]
theorem r324DoublePiMeasurableEquiv_apply
    (m : ℕ) (v : Fin (2 * m) → T4) :
    r324DoublePiMeasurableEquiv m v =
      (fun i => v (leftMomentIndex i),
        fun j => v (rightMomentIndex j)) := by
  apply Prod.ext
  · funext i
    rfl
  · funext j
    rfl

theorem measurePreserving_r324DoublePiMeasurableEquiv
    (m : ℕ) :
    MeasurePreserving
      (r324DoublePiMeasurableEquiv m)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure)
      ((Measure.pi fun _ : Fin m => paperMeasure).prod
        (Measure.pi fun _ : Fin m => paperMeasure)) := by
  have hcongr :=
    (measurePreserving_piCongrLeft
      (fun _ : Fin (2 * m) => paperMeasure)
      (momentDoubleFinEquiv m)).symm
  have hsum :=
    measurePreserving_sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m => paperMeasure)
  exact hsum.comp hcongr

/-- Regroup `(x,y,z,w,v⁺⊔v⁻)` into the two independent flat parametrix
tuples `(x,y,v⁺)` and `(z,w,v⁻)`. -/
def r324PhysicalSplitMeasurableEquiv (m : ℕ) :
    R324PhysicalPoint m ≃ᵐ
      (T4 × (T4 × (Fin m → T4))) ×
        (T4 × (T4 × (Fin m → T4))) :=
  (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (r324DoublePiMeasurableEquiv m))))).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (r324MoveMiddleMeasurableEquiv
            T4 (Fin m → T4) (Fin m → T4))))).trans
      ((MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (r324MoveMiddleMeasurableEquiv
            T4 (Fin m → T4)
              (T4 × (Fin m → T4))))).trans
        ((MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodAssoc
            (α := T4) (β := Fin m → T4)
              (γ := T4 × (T4 × (Fin m → T4)))).symm).trans
          (MeasurableEquiv.prodAssoc
            (α := T4)
            (β := T4 × (Fin m → T4))
            (γ := T4 × (T4 × (Fin m → T4))).symm))))

@[simp]
theorem r324PhysicalSplitMeasurableEquiv_apply
    (m : ℕ) (p : R324PhysicalPoint m) :
    r324PhysicalSplitMeasurableEquiv m p =
      ((p.1, p.2.1,
          fun i => p.2.2.2.2 (leftMomentIndex i)),
        (p.2.2.1, p.2.2.2.1,
          fun i => p.2.2.2.2 (rightMomentIndex i))) := by
  unfold r324PhysicalSplitMeasurableEquiv
  simp only [MeasurableEquiv.trans_apply]
  have hsplit :
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (MeasurableEquiv.prodCongr
              (MeasurableEquiv.refl T4)
              (r324DoublePiMeasurableEquiv m))))) p =
        (p.1, p.2.1, p.2.2.1, p.2.2.2.1,
          r324DoublePiMeasurableEquiv m p.2.2.2.2) := by
    rfl
  rw [hsplit, r324DoublePiMeasurableEquiv_apply]
  rfl

/-- The physical regrouping preserves the genuine five-group product
measure. -/
theorem measurePreserving_r324PhysicalSplitMeasurableEquiv
    (m : ℕ) :
    MeasurePreserving
      (r324PhysicalSplitMeasurableEquiv m)
      (r324PhysicalMeasure m)
      ((paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure))).prod
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure)))) := by
  let μm := Measure.pi fun _ : Fin m => paperMeasure
  let μ2m := Measure.pi fun _ : Fin (2 * m) => paperMeasure
  have h0 :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (MeasurableEquiv.prodCongr
              (MeasurableEquiv.refl T4)
              (MeasurableEquiv.prodCongr
                (MeasurableEquiv.refl T4)
                (r324DoublePiMeasurableEquiv m)))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod μ2m))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod (μm.prod μm))))) :=
    (MeasurePreserving.id paperMeasure).prod
      ((MeasurePreserving.id paperMeasure).prod
        ((MeasurePreserving.id paperMeasure).prod
          ((MeasurePreserving.id paperMeasure).prod
            (measurePreserving_r324DoublePiMeasurableEquiv m))))
  have h1 :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (MeasurableEquiv.prodCongr
              (MeasurableEquiv.refl T4)
              (r324MoveMiddleMeasurableEquiv
                T4 (Fin m → T4) (Fin m → T4)))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod (μm.prod μm)))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (μm.prod (paperMeasure.prod μm))))) :=
    (MeasurePreserving.id paperMeasure).prod
      ((MeasurePreserving.id paperMeasure).prod
        ((MeasurePreserving.id paperMeasure).prod
          (measurePreserving_r324MoveMiddleMeasurableEquiv
            paperMeasure μm μm)))
  have h2 :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (r324MoveMiddleMeasurableEquiv
              T4 (Fin m → T4) (T4 × (Fin m → T4)))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (μm.prod (paperMeasure.prod μm)))))
        (paperMeasure.prod
          (paperMeasure.prod
            (μm.prod
              (paperMeasure.prod
                (paperMeasure.prod μm))))) :=
    (MeasurePreserving.id paperMeasure).prod
      ((MeasurePreserving.id paperMeasure).prod
        (measurePreserving_r324MoveMiddleMeasurableEquiv
          paperMeasure μm (paperMeasure.prod μm)))
  have h3 :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodAssoc
            (α := T4) (β := Fin m → T4)
              (γ := T4 × (T4 × (Fin m → T4)))).symm)
        (paperMeasure.prod
          (paperMeasure.prod
            (μm.prod
              (paperMeasure.prod
                (paperMeasure.prod μm)))))
        (paperMeasure.prod
          ((paperMeasure.prod μm).prod
            (paperMeasure.prod
              (paperMeasure.prod μm)))) :=
    (MeasurePreserving.id paperMeasure).prod
      (measurePreserving_prodAssoc
        paperMeasure μm
          (paperMeasure.prod (paperMeasure.prod μm))).symm
  have h4 :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc
          (α := T4)
          (β := T4 × (Fin m → T4))
          (γ := T4 × (T4 × (Fin m → T4))).symm)
        (paperMeasure.prod
          ((paperMeasure.prod μm).prod
            (paperMeasure.prod
              (paperMeasure.prod μm))))
        ((paperMeasure.prod (paperMeasure.prod μm)).prod
          (paperMeasure.prod
            (paperMeasure.prod μm))) :=
    (measurePreserving_prodAssoc paperMeasure
      (paperMeasure.prod μm)
      (paperMeasure.prod (paperMeasure.prod μm))).symm
  simpa only [r324PhysicalSplitMeasurableEquiv,
    MeasurableEquiv.coe_trans, Function.comp_assoc,
    r324PhysicalMeasure, r324PhysicalRestMeasure, μm, μ2m] using
      h4.comp (h3.comp (h2.comp (h1.comp h0)))

/-- Joint integrability of the bare doubled deterministic profile before
the four Fourier characters and the cross-covariance factors are attached. -/
theorem integrable_r324Flatten_detIntegrand_product
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    Integrable
      (r324Flatten
        (fun x y z w v =>
          ((detIntegrand ρ ε m κp
              (assemble x y fun i => v (leftMomentIndex i)) *
            detIntegrand ρ ε m κm
              (assemble z w fun i => v (rightMomentIndex i)) : ℝ) : ℂ)))
      (r324PhysicalMeasure m) := by
  let Flat := T4 × (T4 × (Fin m → T4))
  let μflat :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin m => paperMeasure))
  let fp : Flat → ℂ := fun p =>
    (detIntegrand ρ ε m κp
      (assemble p.1 p.2.1 p.2.2) : ℂ)
  let fm : Flat → ℂ := fun p =>
    (detIntegrand ρ ε m κm
      (assemble p.1 p.2.1 p.2.2) : ℂ)
  have hp : Integrable fp μflat := by
    simpa only [fp, μflat] using
      integrable_detIntegrand_flat ρ hε hε1 κp
  have hm : Integrable fm μflat := by
    simpa only [fm, μflat] using
      integrable_detIntegrand_flat ρ hε hε1 κm
  have hprod :
      Integrable
        (fun p : Flat × Flat => fp p.1 * fm p.2)
        (μflat.prod μflat) :=
    hp.mul_prod hm
  let e := r324PhysicalSplitMeasurableEquiv m
  have he :
      MeasurePreserving e
        (r324PhysicalMeasure m) (μflat.prod μflat) := by
    simpa only [e, μflat] using
      measurePreserving_r324PhysicalSplitMeasurableEquiv m
  have hiff :=
    he.integrable_comp_emb e.measurableEmbedding
      (g := fun p : Flat × Flat => fp p.1 * fm p.2)
  have hpull :
      Integrable
        ((fun p : Flat × Flat => fp p.1 * fm p.2) ∘ e)
        (r324PhysicalMeasure m) :=
    hiff.mpr hprod
  convert hpull using 1
  funext p
  simp only [Function.comp_apply, e,
    r324PhysicalSplitMeasurableEquiv_apply, fp, fm,
    r324Flatten]
  push_cast
  rfl

/-! ## The full deterministic moment contraction -/

/-- The cross-copy covariance product is measurable in the doubled internal
tuple. -/
theorem measurable_momentCrossCovarianceProduct
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Measurable
      (momentCrossCovarianceProduct ρ ε m κp κm π) := by
  unfold momentCrossCovarianceProduct
  apply Finset.measurable_prod
  intro i _hi
  exact (ρ.measurable_etaEpsT4 ε).comp
    ((measurable_pi_apply (leftMomentIndex i.val)).sub
      (measurable_pi_apply
        (rightMomentIndex (π i).val)))

/-- At positive scale, every cross-copy covariance product is uniformly
bounded.  The bound may depend on the frozen pairing data and scale, which is
all that joint integrability requires. -/
theorem exists_norm_momentCrossCovarianceProduct_le
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ v : Fin (2 * m) → T4,
        ‖(momentCrossCovarianceProduct
          ρ ε m κp κm π v : ℂ)‖ ≤ B := by
  obtain ⟨Cη, hCη, heta⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let A : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  let B : ℝ := (1 + A) ^ m
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbase : 1 ≤ 1 + A := by linarith
  refine ⟨B, pow_nonneg (by linarith) _, ?_⟩
  intro v
  unfold momentCrossCovarianceProduct
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg fun i _ =>
      ρ.etaEpsT4_nonneg ε
        (v (leftMomentIndex i.val) -
          v (rightMomentIndex (π i).val)))]
  calc
    (∏ i : ↥κp.singles,
        ρ.etaEpsT4 ε
          (v (leftMomentIndex i.val) -
            v (rightMomentIndex (π i).val))) ≤
        ∏ _i : ↥κp.singles, (1 + A) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact ρ.etaEpsT4_nonneg ε
          (v (leftMomentIndex i.val) -
            v (rightMomentIndex (π i).val))
      · intro i _hi
        calc
          ρ.etaEpsT4 ε
              (v (leftMomentIndex i.val) -
                v (rightMomentIndex (π i).val)) ≤ A := by
            simpa only [A] using
              heta hε hε1
                (v (leftMomentIndex i.val) -
                  v (rightMomentIndex (π i).val))
          _ ≤ 1 + A := by linarith
    _ = (1 + A) ^ κp.singles.card := by
      simp
    _ ≤ (1 + A) ^ m := by
      apply pow_le_pow_right₀ hbase
      calc
        κp.singles.card ≤
            (Finset.univ : Finset (Fin m)).card :=
          Finset.card_le_univ κp.singles
        _ = m := by simp
    _ = B := rfl

/-- Every contraction term in the deterministic form of (3.24)/(4.18) is
jointly integrable on its genuine product space. -/
theorem integrable_r324Flatten_deterministicMomentIntegrand
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Integrable
      (r324Flatten
        (deterministicMomentIntegrand
          ρ ε m α β κp κm π))
      (r324PhysicalMeasure m) := by
  have hbare :=
    integrable_r324Flatten_detIntegrand_product
      ρ hε hε1 κp κm
  obtain ⟨B, _hB, hcrossBound⟩ :=
    exists_norm_momentCrossCovarianceProduct_le
      ρ hε hε1 κp κm π
  let weight : R324PhysicalPoint m → ℂ := fun p =>
    charT4 α p.1 *
      charT4 β p.2.1 *
      charT4 (-α) p.2.2.1 *
      charT4 (-β) p.2.2.2.1 *
      (momentCrossCovarianceProduct
        ρ ε m κp κm π p.2.2.2.2 : ℂ)
  have hx : Measurable fun p : R324PhysicalPoint m => p.1 :=
    measurable_fst
  have hy : Measurable fun p : R324PhysicalPoint m => p.2.1 :=
    measurable_fst.comp measurable_snd
  have hz : Measurable fun p : R324PhysicalPoint m => p.2.2.1 :=
    measurable_fst.comp
      (measurable_snd.comp measurable_snd)
  have hw : Measurable fun p : R324PhysicalPoint m => p.2.2.2.1 :=
    measurable_fst.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
  have hv :
      Measurable fun p : R324PhysicalPoint m => p.2.2.2.2 :=
    measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp measurable_snd))
  have hweightMeas : Measurable weight := by
    exact
      (((((continuous_charT4 α).measurable.comp hx).mul
        ((continuous_charT4 β).measurable.comp hy)).mul
        ((continuous_charT4 (-α)).measurable.comp hz)).mul
        ((continuous_charT4 (-β)).measurable.comp hw)).mul
        (Complex.measurable_ofReal.comp
          ((measurable_momentCrossCovarianceProduct
            ρ ε κp κm π).comp hv))
  have hweightBound :
      ∀ p : R324PhysicalPoint m, ‖weight p‖ ≤ B := by
    intro p
    unfold weight
    simpa only [norm_mul, norm_charT4, one_mul] using
      hcrossBound p.2.2.2.2
  have hproduct :=
    hbare.mul_bdd hweightMeas.aestronglyMeasurable
      (.of_forall hweightBound)
  convert hproduct using 1
  funext p
  unfold r324Flatten deterministicMomentIntegrand weight
  push_cast
  ring

/-- Uniformly package the preceding theorem as the physical-fiber
integrability ledger consumed by deterministic R-324 reduction. -/
theorem r324MomentIntegrable_all
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) :
    ∀ e : MomentContraction m,
      R324MomentIntegrable ρ ε m α β e := by
  rintro ⟨κp, κm, π⟩
  exact
    integrable_r324Flatten_deterministicMomentIntegrand
      ρ hε hε1 α β κp κm π

end

end Anderson4D
