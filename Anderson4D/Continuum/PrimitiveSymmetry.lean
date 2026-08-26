import Anderson4D.Continuum.PrimitiveBaseSymmetry
import Anderson4D.DetParametrix.Core.ReductionSymmetry

/-!
# Hyperoctahedral symmetry of primitive kernels at every order

This file proves the symmetry half of Proposition 4.1 without assuming
symmetry of the resulting primitive kernel.  Coordinate permutations and
single-coordinate sign flips are transported simultaneously through every
internal integration variable.  The product paper measure is preserved,
while assembly, chain differences, covariance differences, and the diameter
insertion are equivariant.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Coordinate permutations on the torus and product measures -/

/-- Permute the four torus coordinates. -/
def permuteT4 (σ : Equiv.Perm (Fin dim)) (x : T4) : T4 :=
  x ∘ σ

/-- Coordinate permutation as a measurable equivalence of the torus. -/
def permuteT4MeasurableEquiv (σ : Equiv.Perm (Fin dim)) : T4 ≃ᵐ T4 :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin dim => AddCircle (2 * Real.pi)) σ.symm

@[simp]
theorem permuteT4MeasurableEquiv_apply
    (σ : Equiv.Perm (Fin dim)) (x : T4) :
    permuteT4MeasurableEquiv σ x = permuteT4 σ x := by
  funext i
  simp [permuteT4MeasurableEquiv, permuteT4,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- Coordinate permutation preserves the paper-normalized torus measure. -/
theorem measurePreserving_permuteT4 (σ : Equiv.Perm (Fin dim)) :
    MeasurePreserving (permuteT4MeasurableEquiv σ)
      paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  exact volume_measurePreserving_piCongrLeft
    (fun _ : Fin dim => AddCircle (2 * Real.pi)) σ.symm

/-- Function-valued form of coordinate-permutation measure preservation. -/
theorem measurePreserving_permuteT4_fun (σ : Equiv.Perm (Fin dim)) :
    MeasurePreserving (permuteT4 σ) paperMeasure paperMeasure := by
  have hfun :
      (⇑(permuteT4MeasurableEquiv σ) : T4 → T4) = permuteT4 σ := by
    funext x
    exact permuteT4MeasurableEquiv_apply σ x
  rw [← hfun]
  exact measurePreserving_permuteT4 σ

/-- Apply a coordinate permutation in every member of a finite tuple. -/
def permuteT4Tuple {ι : Type*} (σ : Equiv.Perm (Fin dim))
    (x : ι → T4) : ι → T4 :=
  fun a => permuteT4 σ (x a)

/-- Apply one coordinate flip in every member of a finite tuple. -/
def coordinateFlipT4Tuple {ι : Type*} (i : Fin dim)
    (x : ι → T4) : ι → T4 :=
  fun a => coordinateFlipT4 i (x a)

/-- Coordinatewise permutation bundled as a measurable equivalence of
finite tuples. -/
def permuteT4TupleMeasurableEquiv {ι : Type*}
    (σ : Equiv.Perm (Fin dim)) : (ι → T4) ≃ᵐ (ι → T4) :=
  MeasurableEquiv.piCongrRight fun _ : ι => permuteT4MeasurableEquiv σ

@[simp]
theorem permuteT4TupleMeasurableEquiv_apply
    {ι : Type*} (σ : Equiv.Perm (Fin dim)) (x : ι → T4) :
    permuteT4TupleMeasurableEquiv σ x = permuteT4Tuple σ x :=
  by
    funext a
    exact permuteT4MeasurableEquiv_apply σ (x a)

/-- Coordinatewise flip bundled as a measurable equivalence of finite
tuples. -/
def coordinateFlipT4TupleMeasurableEquiv {ι : Type*}
    (i : Fin dim) : (ι → T4) ≃ᵐ (ι → T4) :=
  MeasurableEquiv.piCongrRight fun _ : ι => coordinateFlipMeasurableEquiv i

@[simp]
theorem coordinateFlipT4TupleMeasurableEquiv_apply
    {ι : Type*} (i : Fin dim) (x : ι → T4) :
    coordinateFlipT4TupleMeasurableEquiv i x =
      coordinateFlipT4Tuple i x :=
  rfl

/-- Coordinatewise permutation preserves every finite product of the paper
measure. -/
theorem measurePreserving_permuteT4Tuple
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm (Fin dim)) :
    MeasurePreserving (permuteT4TupleMeasurableEquiv (ι := ι) σ)
      (Measure.pi fun _ : ι => paperMeasure)
      (Measure.pi fun _ : ι => paperMeasure) := by
  change MeasurePreserving
    (fun x : ι → T4 => fun a => permuteT4MeasurableEquiv σ (x a))
    (Measure.pi fun _ : ι => paperMeasure)
    (Measure.pi fun _ : ι => paperMeasure)
  exact measurePreserving_pi
    (fun _ : ι => paperMeasure) (fun _ : ι => paperMeasure)
    fun _ => measurePreserving_permuteT4 σ

/-- Coordinatewise flip preserves every finite product of the paper measure. -/
theorem measurePreserving_coordinateFlipT4Tuple
    {ι : Type*} [Fintype ι] (i : Fin dim) :
    MeasurePreserving (coordinateFlipT4TupleMeasurableEquiv (ι := ι) i)
      (Measure.pi fun _ : ι => paperMeasure)
      (Measure.pi fun _ : ι => paperMeasure) := by
  change MeasurePreserving
    (fun x : ι → T4 => fun a => coordinateFlipMeasurableEquiv i (x a))
    (Measure.pi fun _ : ι => paperMeasure)
    (Measure.pi fun _ : ι => paperMeasure)
  exact measurePreserving_pi
    (fun _ : ι => paperMeasure) (fun _ : ι => paperMeasure)
    fun _ => measurePreserving_coordinateFlipT4 i

/-- Integral change of variables for a simultaneous tuple permutation. -/
theorem integral_comp_permuteT4Tuple
    {ι : Type*} [Fintype ι] (σ : Equiv.Perm (Fin dim))
    (F : (ι → T4) → ℝ) :
    (∫ v, F (permuteT4Tuple σ v)
        ∂(Measure.pi fun _ : ι => paperMeasure)) =
      ∫ v, F v ∂(Measure.pi fun _ : ι => paperMeasure) := by
  simpa only [permuteT4TupleMeasurableEquiv_apply] using
    (measurePreserving_permuteT4Tuple (ι := ι) σ).integral_comp' F

/-- Integral change of variables for a simultaneous tuple flip. -/
theorem integral_comp_coordinateFlipT4Tuple
    {ι : Type*} [Fintype ι] (i : Fin dim)
    (F : (ι → T4) → ℝ) :
    (∫ v, F (coordinateFlipT4Tuple i v)
        ∂(Measure.pi fun _ : ι => paperMeasure)) =
      ∫ v, F v ∂(Measure.pi fun _ : ι => paperMeasure) :=
  (measurePreserving_coordinateFlipT4Tuple (ι := ι) i).integral_comp' F

/-! ## Equivariance of group operations and endpoint assembly -/

theorem permuteT4_sub (σ : Equiv.Perm (Fin dim)) (x y : T4) :
    permuteT4 σ (x - y) = permuteT4 σ x - permuteT4 σ y :=
  rfl

theorem coordinateFlipT4_sub (i : Fin dim) (x y : T4) :
    coordinateFlipT4 i (x - y) =
      coordinateFlipT4 i x - coordinateFlipT4 i y := by
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp only [coordinateFlipT4, Function.update_self, Pi.sub_apply]
    abel
  · simp [coordinateFlipT4, Function.update_of_ne hji]

@[simp]
theorem permuteT4_zero (σ : Equiv.Perm (Fin dim)) :
    permuteT4 σ (0 : T4) = 0 :=
  rfl

@[simp]
theorem coordinateFlipT4_zero (i : Fin dim) :
    coordinateFlipT4 i (0 : T4) = 0 := by
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp [coordinateFlipT4]
  · simp [coordinateFlipT4, Function.update_of_ne hji]

/-- Endpoint assembly commutes with a simultaneous coordinate permutation. -/
theorem assemble_permute {m : ℕ} (σ : Equiv.Perm (Fin dim))
    (z w : T4) (v : Fin m → T4) (j : Fin (m + 2)) :
    assemble (permuteT4 σ z) (permuteT4 σ w)
        (permuteT4Tuple σ v) j =
      permuteT4 σ (assemble z w v j) := by
  unfold assemble
  by_cases hzero : j.val = 0
  · simp only [hzero, ↓reduceDIte]
  · by_cases hlast : j.val = m + 1
    · have hm : m + 1 ≠ 0 := by omega
      simp only [hlast, hm, ↓reduceDIte]
    · simp only [hzero, hlast, ↓reduceDIte, permuteT4Tuple]

/-- Endpoint assembly commutes with a simultaneous coordinate flip. -/
theorem assemble_coordinateFlip {m : ℕ} (i : Fin dim)
    (z w : T4) (v : Fin m → T4) (j : Fin (m + 2)) :
    assemble (coordinateFlipT4 i z) (coordinateFlipT4 i w)
        (coordinateFlipT4Tuple i v) j =
      coordinateFlipT4 i (assemble z w v j) := by
  unfold assemble
  by_cases hzero : j.val = 0
  · simp only [hzero, ↓reduceDIte]
  · by_cases hlast : j.val = m + 1
    · have hm : m + 1 ≠ 0 := by omega
      simp only [hlast, hm, ↓reduceDIte]
    · simp only [hzero, hlast, ↓reduceDIte, coordinateFlipT4Tuple]

theorem primitiveAssemble_permute
    (n : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin dim))
    (z w : T4) (v : Fin (2 * n - 2) → T4)
    (j : Fin (2 * n)) :
    primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w)
        (permuteT4Tuple σ v) j =
      permuteT4 σ (primitiveAssemble n hn z w v j) := by
  unfold primitiveAssemble
  exact assemble_permute σ z w v _

theorem primitiveAssemble_coordinateFlip
    (n : ℕ) (hn : 1 ≤ n) (i : Fin dim)
    (z w : T4) (v : Fin (2 * n - 2) → T4)
    (j : Fin (2 * n)) :
    primitiveAssemble n hn (coordinateFlipT4 i z) (coordinateFlipT4 i w)
        (coordinateFlipT4Tuple i v) j =
      coordinateFlipT4 i (primitiveAssemble n hn z w v j) := by
  unfold primitiveAssemble
  exact assemble_coordinateFlip i z w v _

/-! ## Equivariance of products and diameter insertion -/

theorem primitiveChainProduct_permute
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (σ : Equiv.Perm (Fin dim)) (x : Fin (2 * n) → T4) :
    primitiveChainProduct n hn G (permuteT4Tuple σ x) =
      primitiveChainProduct n hn G x := by
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j hj
  change
    G j
        (permuteT4 σ (x (primitiveEdgeLeft n hn j)) -
          permuteT4 σ (x (primitiveEdgeRight n hn j))) =
      G j
        (x (primitiveEdgeLeft n hn j) -
          x (primitiveEdgeRight n hn j))
  rw [← permuteT4_sub]
  exact (hG j).perm_invariant σ _

theorem primitiveChainProduct_coordinateFlip
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (i : Fin dim) (x : Fin (2 * n) → T4) :
    primitiveChainProduct n hn G (coordinateFlipT4Tuple i x) =
      primitiveChainProduct n hn G x := by
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j hj
  change
    G j
        (coordinateFlipT4 i (x (primitiveEdgeLeft n hn j)) -
          coordinateFlipT4 i (x (primitiveEdgeRight n hn j))) =
      G j
        (x (primitiveEdgeLeft n hn j) -
          x (primitiveEdgeRight n hn j))
  rw [← coordinateFlipT4_sub]
  exact (hG j).even_coord i _

theorem primitiveCovarianceProduct_permute
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (κ : PartialPairing (Fin (2 * n)))
    (σ : Equiv.Perm (Fin dim)) (x : Fin (2 * n) → T4) :
    primitiveCovarianceProduct ρ ε n κ (permuteT4Tuple σ x) =
      primitiveCovarianceProduct ρ ε n κ x := by
  unfold primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro j hj
  change
    ρ.etaEpsT4 ε
        (permuteT4 σ (x j) - permuteT4 σ (x (κ j))) =
      ρ.etaEpsT4 ε (x j - x (κ j))
  rw [← permuteT4_sub]
  exact (ρ.etaEpsT4_memE ε).perm_invariant σ _

theorem primitiveCovarianceProduct_coordinateFlip
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (κ : PartialPairing (Fin (2 * n)))
    (i : Fin dim) (x : Fin (2 * n) → T4) :
    primitiveCovarianceProduct ρ ε n κ (coordinateFlipT4Tuple i x) =
      primitiveCovarianceProduct ρ ε n κ x := by
  unfold primitiveCovarianceProduct
  apply Finset.prod_congr rfl
  intro j hj
  change
    ρ.etaEpsT4 ε
        (coordinateFlipT4 i (x j) -
          coordinateFlipT4 i (x (κ j))) =
      ρ.etaEpsT4 ε (x j - x (κ j))
  rw [← coordinateFlipT4_sub]
  exact (ρ.etaEpsT4_memE ε).even_coord i _

theorem primitiveIntegrand_permute
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (σ : Equiv.Perm (Fin dim)) (x : Fin (2 * n) → T4) :
    primitiveIntegrand ρ ε n hn G κ (permuteT4Tuple σ x) =
      primitiveIntegrand ρ ε n hn G κ x := by
  unfold primitiveIntegrand
  rw [primitiveChainProduct_permute n hn G hG,
    primitiveCovarianceProduct_permute]

theorem primitiveIntegrand_coordinateFlip
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (i : Fin dim) (x : Fin (2 * n) → T4) :
    primitiveIntegrand ρ ε n hn G κ (coordinateFlipT4Tuple i x) =
      primitiveIntegrand ρ ε n hn G κ x := by
  unfold primitiveIntegrand
  rw [primitiveChainProduct_coordinateFlip n hn G hG,
    primitiveCovarianceProduct_coordinateFlip]

theorem torusTupleDiameterSq_permute
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : Equiv.Perm (Fin dim)) (x : ι → T4) :
    torusTupleDiameterSq (permuteT4Tuple σ x) =
      torusTupleDiameterSq x := by
  unfold torusTupleDiameterSq
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro a ha
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro b hb
  change
    torusDistSq (permuteT4 σ (x a) - permuteT4 σ (x b)) =
      torusDistSq (x a - x b)
  rw [← permuteT4_sub]
  exact torusDistSq_memE.perm_invariant σ _

theorem torusTupleDiameterSq_coordinateFlip
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (i : Fin dim) (x : ι → T4) :
    torusTupleDiameterSq (coordinateFlipT4Tuple i x) =
      torusTupleDiameterSq x := by
  unfold torusTupleDiameterSq
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro a ha
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro b hb
  change
    torusDistSq
        (coordinateFlipT4 i (x a) - coordinateFlipT4 i (x b)) =
      torusDistSq (x a - x b)
  rw [← coordinateFlipT4_sub]
  exact torusDistSq_memE.even_coord i _

theorem primitiveInsertedIntegrand_permute
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (σ : Equiv.Perm (Fin dim)) (x : Fin (2 * n) → T4) :
    primitiveInsertedIntegrand ρ ε n hn G κ
        (permuteT4Tuple σ x) =
      primitiveInsertedIntegrand ρ ε n hn G κ x := by
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  unfold primitiveInsertedIntegrand
  rw [torusTupleDiameterSq_permute,
    primitiveIntegrand_permute ρ ε n hn G hG]

theorem primitiveInsertedIntegrand_coordinateFlip
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (i : Fin dim) (x : Fin (2 * n) → T4) :
    primitiveInsertedIntegrand ρ ε n hn G κ
        (coordinateFlipT4Tuple i x) =
      primitiveInsertedIntegrand ρ ε n hn G κ x := by
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  unfold primitiveInsertedIntegrand
  rw [torusTupleDiameterSq_coordinateFlip,
    primitiveIntegrand_coordinateFlip ρ ε n hn G hG]

/-! ## Change of variables in the primitive kernels -/

theorem primitiveIntegrandIntegral_permute
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (σ : Equiv.Perm (Fin dim)) (z w : T4) :
    (∫ v : Fin (2 * n - 2) → T4,
        primitiveIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w) v)
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ v : Fin (2 * n - 2) → T4,
        primitiveIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn z w v)
        ∂(Measure.pi fun _ => paperMeasure) := by
  let F : (Fin (2 * n - 2) → T4) → ℝ :=
    fun v =>
      primitiveIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w) v)
  calc
    (∫ v : Fin (2 * n - 2) → T4, F v
        ∂(Measure.pi fun _ => paperMeasure)) =
        ∫ v : Fin (2 * n - 2) → T4,
          F (permuteT4Tuple σ v)
          ∂(Measure.pi fun _ => paperMeasure) :=
      (integral_comp_permuteT4Tuple σ F).symm
    _ = ∫ v : Fin (2 * n - 2) → T4,
          primitiveIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
          ∂(Measure.pi fun _ => paperMeasure) := by
      apply integral_congr_ae
      filter_upwards with v
      change
        primitiveIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w)
              (permuteT4Tuple σ v)) =
          primitiveIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
      rw [show primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w)
            (permuteT4Tuple σ v) =
          permuteT4Tuple σ (primitiveAssemble n hn z w v) by
        funext j
        exact primitiveAssemble_permute n hn σ z w v j]
      exact primitiveIntegrand_permute ρ ε n hn G hG κ σ _

theorem primitiveIntegrandIntegral_coordinateFlip
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (i : Fin dim) (z w : T4) :
    (∫ v : Fin (2 * n - 2) → T4,
        primitiveIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn (coordinateFlipT4 i z)
            (coordinateFlipT4 i w) v)
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ v : Fin (2 * n - 2) → T4,
        primitiveIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn z w v)
        ∂(Measure.pi fun _ => paperMeasure) := by
  let F : (Fin (2 * n - 2) → T4) → ℝ :=
    fun v =>
      primitiveIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn (coordinateFlipT4 i z)
          (coordinateFlipT4 i w) v)
  calc
    (∫ v : Fin (2 * n - 2) → T4, F v
        ∂(Measure.pi fun _ => paperMeasure)) =
        ∫ v : Fin (2 * n - 2) → T4,
          F (coordinateFlipT4Tuple i v)
          ∂(Measure.pi fun _ => paperMeasure) :=
      (integral_comp_coordinateFlipT4Tuple i F).symm
    _ = ∫ v : Fin (2 * n - 2) → T4,
          primitiveIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
          ∂(Measure.pi fun _ => paperMeasure) := by
      apply integral_congr_ae
      filter_upwards with v
      change
        primitiveIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn (coordinateFlipT4 i z)
              (coordinateFlipT4 i w) (coordinateFlipT4Tuple i v)) =
          primitiveIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
      rw [show primitiveAssemble n hn (coordinateFlipT4 i z)
            (coordinateFlipT4 i w) (coordinateFlipT4Tuple i v) =
          coordinateFlipT4Tuple i (primitiveAssemble n hn z w v) by
        funext j
        exact primitiveAssemble_coordinateFlip n hn i z w v j]
      exact primitiveIntegrand_coordinateFlip ρ ε n hn G hG κ i _

theorem primitiveInsertedIntegrandIntegral_permute
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (σ : Equiv.Perm (Fin dim)) (z w : T4) :
    (∫ v : Fin (2 * n - 2) → T4,
        primitiveInsertedIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w) v)
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ v : Fin (2 * n - 2) → T4,
        primitiveInsertedIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn z w v)
        ∂(Measure.pi fun _ => paperMeasure) := by
  let F : (Fin (2 * n - 2) → T4) → ℝ :=
    fun v =>
      primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w) v)
  calc
    (∫ v : Fin (2 * n - 2) → T4, F v
        ∂(Measure.pi fun _ => paperMeasure)) =
        ∫ v : Fin (2 * n - 2) → T4,
          F (permuteT4Tuple σ v)
          ∂(Measure.pi fun _ => paperMeasure) :=
      (integral_comp_permuteT4Tuple σ F).symm
    _ = ∫ v : Fin (2 * n - 2) → T4,
          primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
          ∂(Measure.pi fun _ => paperMeasure) := by
      apply integral_congr_ae
      filter_upwards with v
      change
        primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w)
              (permuteT4Tuple σ v)) =
          primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
      rw [show primitiveAssemble n hn (permuteT4 σ z) (permuteT4 σ w)
            (permuteT4Tuple σ v) =
          permuteT4Tuple σ (primitiveAssemble n hn z w v) by
        funext j
        exact primitiveAssemble_permute n hn σ z w v j]
      exact primitiveInsertedIntegrand_permute ρ ε n hn G hG κ σ _

theorem primitiveInsertedIntegrandIntegral_coordinateFlip
    (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (κ : PartialPairing (Fin (2 * n)))
    (i : Fin dim) (z w : T4) :
    (∫ v : Fin (2 * n - 2) → T4,
        primitiveInsertedIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn (coordinateFlipT4 i z)
            (coordinateFlipT4 i w) v)
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ v : Fin (2 * n - 2) → T4,
        primitiveInsertedIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn z w v)
        ∂(Measure.pi fun _ => paperMeasure) := by
  let F : (Fin (2 * n - 2) → T4) → ℝ :=
    fun v =>
      primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn (coordinateFlipT4 i z)
          (coordinateFlipT4 i w) v)
  calc
    (∫ v : Fin (2 * n - 2) → T4, F v
        ∂(Measure.pi fun _ => paperMeasure)) =
        ∫ v : Fin (2 * n - 2) → T4,
          F (coordinateFlipT4Tuple i v)
          ∂(Measure.pi fun _ => paperMeasure) :=
      (integral_comp_coordinateFlipT4Tuple i F).symm
    _ = ∫ v : Fin (2 * n - 2) → T4,
          primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
          ∂(Measure.pi fun _ => paperMeasure) := by
      apply integral_congr_ae
      filter_upwards with v
      change
        primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn (coordinateFlipT4 i z)
              (coordinateFlipT4 i w) (coordinateFlipT4Tuple i v)) =
          primitiveInsertedIntegrand ρ ε n hn G κ
            (primitiveAssemble n hn z w v)
      rw [show primitiveAssemble n hn (coordinateFlipT4 i z)
            (coordinateFlipT4 i w) (coordinateFlipT4Tuple i v) =
          coordinateFlipT4Tuple i (primitiveAssemble n hn z w v) by
        funext j
        exact primitiveAssemble_coordinateFlip n hn i z w v j]
      exact
        primitiveInsertedIntegrand_coordinateFlip ρ ε n hn G hG κ i _

theorem primitiveKernel_permute
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (σ : Equiv.Perm (Fin dim)) (z w : T4) :
    primitiveKernel ρ lam ε n hn G
        (permuteT4 σ z) (permuteT4 σ w) =
      primitiveKernel ρ lam ε n hn G z w := by
  unfold primitiveKernel
  apply congrArg (fun t : ℝ => lamEps lam ε ^ (2 * n) * t)
  apply Finset.sum_congr rfl
  intro κ hκ
  exact primitiveIntegrandIntegral_permute ρ ε n hn G hG κ σ z w

theorem primitiveKernel_coordinateFlip
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (i : Fin dim) (z w : T4) :
    primitiveKernel ρ lam ε n hn G
        (coordinateFlipT4 i z) (coordinateFlipT4 i w) =
      primitiveKernel ρ lam ε n hn G z w := by
  unfold primitiveKernel
  apply congrArg (fun t : ℝ => lamEps lam ε ^ (2 * n) * t)
  apply Finset.sum_congr rfl
  intro κ hκ
  exact primitiveIntegrandIntegral_coordinateFlip ρ ε n hn G hG κ i z w

theorem primitiveKernelInserted_permute
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (σ : Equiv.Perm (Fin dim)) (z w : T4) :
    primitiveKernelInserted ρ lam ε n hn G
        (permuteT4 σ z) (permuteT4 σ w) =
      primitiveKernelInserted ρ lam ε n hn G z w := by
  unfold primitiveKernelInserted
  apply congrArg (fun t : ℝ => lamEps lam ε ^ (2 * n) * t)
  apply Finset.sum_congr rfl
  intro κ hκ
  exact
    primitiveInsertedIntegrandIntegral_permute ρ ε n hn G hG κ σ z w

theorem primitiveKernelInserted_coordinateFlip
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j))
    (i : Fin dim) (z w : T4) :
    primitiveKernelInserted ρ lam ε n hn G
        (coordinateFlipT4 i z) (coordinateFlipT4 i w) =
      primitiveKernelInserted ρ lam ε n hn G z w := by
  unfold primitiveKernelInserted
  apply congrArg (fun t : ℝ => lamEps lam ε ^ (2 * n) * t)
  apply Finset.sum_congr rfl
  intro κ hκ
  exact primitiveInsertedIntegrandIntegral_coordinateFlip
    ρ ε n hn G hG κ i z w

/-! ## One-variable kernels belong to the paper's class `𝓔` -/

theorem primitiveKernelDiff_memE
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j)) :
    MemEClassT4 (primitiveKernelDiff ρ lam ε n hn G) where
  perm_invariant := by
    intro σ z
    unfold primitiveKernelDiff
    rw [← permuteT4_zero σ]
    exact primitiveKernel_permute ρ lam ε n hn G hG σ z 0
  even_coord := by
    intro i z
    unfold primitiveKernelDiff
    change
      primitiveKernel ρ lam ε n hn G (coordinateFlipT4 i z) 0 =
        primitiveKernel ρ lam ε n hn G z 0
    simpa only [coordinateFlipT4_zero] using
      primitiveKernel_coordinateFlip ρ lam ε n hn G hG i z 0

theorem primitiveKernelInsertedDiff_memE
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j, MemEClassT4 (G j)) :
    MemEClassT4 (primitiveKernelInsertedDiff ρ lam ε n hn G) where
  perm_invariant := by
    intro σ z
    unfold primitiveKernelInsertedDiff
    rw [← permuteT4_zero σ]
    exact primitiveKernelInserted_permute ρ lam ε n hn G hG σ z 0
  even_coord := by
    intro i z
    unfold primitiveKernelInsertedDiff
    change
      primitiveKernelInserted ρ lam ε n hn G (coordinateFlipT4 i z) 0 =
        primitiveKernelInserted ρ lam ε n hn G z 0
    simpa only [coordinateFlipT4_zero] using
      primitiveKernelInserted_coordinateFlip ρ lam ε n hn G hG i z 0

end

end Anderson4D
