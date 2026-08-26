import Anderson4D.Continuum.PeriodizedCovariance

/-!
# Hyperoctahedral symmetry of the cutoff covariance

This file transports the cutoff's `B₄` symmetry through Euclidean
convolution and lattice periodization.  These structural facts supply the
symmetry half of the primitive-kernel estimates independently of their
analytic bounds.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Measure-preserving Euclidean coordinate actions -/

/-- Permute Euclidean coordinates. -/
def permuteR4 (σ : Equiv.Perm (Fin dim)) (x : R4) : R4 :=
  x ∘ σ

/-- Coordinate permutation as a measurable equivalence. -/
def permuteR4MeasurableEquiv (σ : Equiv.Perm (Fin dim)) : R4 ≃ᵐ R4 :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin dim => ℝ) σ.symm

@[simp]
theorem permuteR4MeasurableEquiv_apply
    (σ : Equiv.Perm (Fin dim)) (x : R4) :
    permuteR4MeasurableEquiv σ x = permuteR4 σ x := by
  funext i
  simp [permuteR4MeasurableEquiv, permuteR4,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- Coordinate permutation preserves Lebesgue measure on `ℝ⁴`. -/
theorem measurePreserving_permuteR4 (σ : Equiv.Perm (Fin dim)) :
    MeasurePreserving (permuteR4MeasurableEquiv σ) :=
  volume_measurePreserving_piCongrLeft
    (fun _ : Fin dim => ℝ) σ.symm

/-- Flip one Euclidean coordinate. -/
def coordinateFlipR4 (i : Fin dim) (x : R4) : R4 :=
  Function.update x i (-(x i))

/-- A Euclidean coordinate flip as a measurable involution. -/
def coordinateFlipR4MeasurableEquiv (i : Fin dim) : R4 ≃ᵐ R4 where
  toEquiv := Function.Involutive.toPerm (coordinateFlipR4 i) fun x => by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp [coordinateFlipR4]
    · simp [coordinateFlipR4, Function.update_of_ne hji]
  measurable_toFun := by
    change Measurable (coordinateFlipR4 i)
    unfold coordinateFlipR4
    fun_prop
  measurable_invFun := by
    change Measurable (coordinateFlipR4 i)
    unfold coordinateFlipR4
    fun_prop

@[simp]
theorem coordinateFlipR4MeasurableEquiv_apply
    (i : Fin dim) (x : R4) :
    coordinateFlipR4MeasurableEquiv i x = coordinateFlipR4 i x :=
  rfl

/-- A single-coordinate sign flip preserves Lebesgue measure on `ℝ⁴`. -/
theorem measurePreserving_coordinateFlipR4 (i : Fin dim) :
    MeasurePreserving (coordinateFlipR4MeasurableEquiv i) := by
  have hpi : MeasurePreserving
      (fun x : R4 => fun j => if j = i then -(x j) else x j) := by
    refine measurePreserving_pi
      (fun _ : Fin dim => (volume : Measure ℝ))
      (fun _ : Fin dim => (volume : Measure ℝ))
      (f := fun j x => if j = i then -x else x) fun j => ?_
    by_cases hji : j = i
    · subst j
      simp only [if_pos]
      exact Measure.measurePreserving_neg _
    · simp only [if_neg hji]
      exact MeasurePreserving.id _
  change MeasurePreserving (coordinateFlipR4 i)
  convert hpi using 1
  funext x j
  by_cases hji : j = i
  · subst j
    simp [coordinateFlipR4]
  · rw [coordinateFlipR4, Function.update_of_ne hji]
    simp [hji]

/-! ## Euclidean covariance symmetry -/

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

private theorem permuteR4_sub
    (σ : Equiv.Perm (Fin dim)) (x y : R4) :
    permuteR4 σ x - permuteR4 σ y = permuteR4 σ (x - y) := by
  rfl

private theorem coordinateFlipR4_sub
    (i : Fin dim) (x y : R4) :
    coordinateFlipR4 i x - coordinateFlipR4 i y =
      coordinateFlipR4 i (x - y) := by
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp [coordinateFlipR4]
    ring
  · simp [coordinateFlipR4, Function.update_of_ne hji]

/-- Euclidean covariance is invariant under coordinate permutations. -/
theorem eta_perm_invariant
    (σ : Equiv.Perm (Fin dim)) (x : R4) :
    ρ.eta (x ∘ σ) = ρ.eta x := by
  unfold eta
  let g : R4 → ℝ := fun y => ρ y * ρ ((x ∘ σ) - y)
  calc
    (∫ y : R4, ρ y * ρ ((x ∘ σ) - y)) =
        ∫ y : R4, g (permuteR4MeasurableEquiv σ y) :=
      ((measurePreserving_permuteR4 σ).integral_comp' g).symm
    _ = ∫ y : R4, ρ y * ρ (x - y) := by
      apply integral_congr_ae
      filter_upwards with y
      have hfirst := ρ.memE.perm_invariant σ y
      have hsecond := ρ.memE.perm_invariant σ (x - y)
      rw [permuteR4MeasurableEquiv_apply]
      change
        ρ (y ∘ σ) * ρ ((x ∘ σ) - (y ∘ σ))
          = ρ y * ρ (x - y)
      have hsub : (x ∘ σ) - (y ∘ σ) = (x - y) ∘ σ := rfl
      rw [hsub, hfirst, hsecond]

/-- Euclidean covariance is invariant under a sign flip in one slot. -/
theorem eta_even_coord (i : Fin dim) (x : R4) :
    ρ.eta (Function.update x i (-(x i))) = ρ.eta x := by
  unfold eta
  let g : R4 → ℝ := fun y => ρ y * ρ (coordinateFlipR4 i x - y)
  calc
    (∫ y : R4,
        ρ y * ρ (Function.update x i (-(x i)) - y)) =
        ∫ y : R4, g (coordinateFlipR4MeasurableEquiv i y) := by
      change (∫ y : R4, g y) =
        ∫ y : R4, g (coordinateFlipR4MeasurableEquiv i y)
      exact ((measurePreserving_coordinateFlipR4 i).integral_comp' g).symm
    _ = ∫ y : R4, ρ y * ρ (x - y) := by
      apply integral_congr_ae
      filter_upwards with y
      have hfirst := ρ.memE.even_coord i y
      have hsecond := ρ.memE.even_coord i (x - y)
      change ρ (coordinateFlipR4 i y) = ρ y at hfirst
      change ρ (coordinateFlipR4 i (x - y)) = ρ (x - y) at hsecond
      rw [coordinateFlipR4MeasurableEquiv_apply]
      change
        ρ (coordinateFlipR4 i y) *
          ρ (coordinateFlipR4 i x - coordinateFlipR4 i y) =
        ρ y * ρ (x - y)
      rw [coordinateFlipR4_sub, hfirst, hsecond]

/-- The Euclidean covariance belongs to the same `B₄` symmetry class as
the cutoff. -/
theorem eta_memE : MemEClassR4 ρ.eta where
  perm_invariant := ρ.eta_perm_invariant
  even_coord := ρ.eta_even_coord

/-! ## Permutation symmetry after lattice periodization -/

/-- Coordinate permutation of the integer period lattice. -/
def permuteZ4Equiv (σ : Equiv.Perm (Fin dim)) : Z4 ≃ Z4 :=
  Equiv.piCongrLeft (fun _ : Fin dim => ℤ) σ.symm

@[simp]
theorem permuteZ4Equiv_apply
    (σ : Equiv.Perm (Fin dim)) (k : Z4) :
    permuteZ4Equiv σ k = k ∘ σ := by
  funext i
  have h :=
    Equiv.piCongrLeft_apply_apply
      (fun _ : Fin dim => ℤ) σ.symm k (σ i)
  simpa [permuteZ4Equiv] using h

/-- Simultaneously permuting a torus displacement and its period vector
leaves one covariance-periodization term unchanged. -/
theorem etaPeriodTerm_perm
    (ε : ℝ) (σ : Equiv.Perm (Fin dim)) (z : T4) (k : Z4) :
    ρ.etaPeriodTerm ε (z ∘ σ) (permuteZ4Equiv σ k) =
      ρ.etaPeriodTerm ε z k := by
  unfold etaPeriodTerm
  rw [permuteZ4Equiv_apply]
  congr 1
  have heta := ρ.eta_perm_invariant σ
    (fun i => ε⁻¹ *
      (torusLift z i + 2 * Real.pi * (k i : ℝ)))
  apply heta

/-- The periodized torus covariance is invariant under coordinate
permutations. -/
theorem etaEpsT4_perm_invariant
    (ε : ℝ) (σ : Equiv.Perm (Fin dim)) (z : T4) :
    ρ.etaEpsT4 ε (z ∘ σ) = ρ.etaEpsT4 ε z := by
  rw [etaEpsT4_eq_tsum_etaPeriodTerm,
    etaEpsT4_eq_tsum_etaPeriodTerm]
  calc
    (∑' k : Z4, ρ.etaPeriodTerm ε (z ∘ σ) k) =
        ∑' k : Z4,
          ρ.etaPeriodTerm ε (z ∘ σ) (permuteZ4Equiv σ k) :=
      ((permuteZ4Equiv σ).tsum_eq
        (fun k => ρ.etaPeriodTerm ε (z ∘ σ) k)).symm
    _ = ∑' k : Z4, ρ.etaPeriodTerm ε z k := by
      apply tsum_congr
      intro k
      exact ρ.etaPeriodTerm_perm ε σ z k

/-! ## Representative independence and coordinate-flip symmetry -/

/-- Euclidean period vector attached to an integer lattice point. -/
def covariancePeriodVector (a : Z4) : R4 :=
  fun j => 2 * Real.pi * (a j : ℝ)

/-- A periodization term based at an arbitrary Euclidean representative. -/
def etaPeriodTermR4 (ε : ℝ) (x : R4) (k : Z4) : ℝ :=
  ε⁻¹ ^ (dim : ℕ) *
    ρ.eta (fun j => ε⁻¹ * (x j + covariancePeriodVector k j))

/-- Periodization at an arbitrary Euclidean representative. -/
def etaPeriodizationR4 (ε : ℝ) (x : R4) : ℝ :=
  ∑' k : Z4, ρ.etaPeriodTermR4 ε x k

theorem etaEpsT4_eq_etaPeriodizationR4 (ε : ℝ) (z : T4) :
    ρ.etaEpsT4 ε z = ρ.etaPeriodizationR4 ε (torusLift z) :=
  rfl

/-- Translating the representative and the period index in opposite
descriptions gives the same summand. -/
theorem etaPeriodTermR4_add_period
    (ε : ℝ) (x : R4) (a k : Z4) :
    ρ.etaPeriodTermR4 ε (x + covariancePeriodVector a) k =
      ρ.etaPeriodTermR4 ε x (k + a) := by
  unfold etaPeriodTermR4 covariancePeriodVector
  congr 2
  funext j
  simp only [Pi.add_apply, Int.cast_add]
  ring

/-- Lattice periodization is independent of the Euclidean representative. -/
theorem etaPeriodizationR4_add_period
    (ε : ℝ) (x : R4) (a : Z4) :
    ρ.etaPeriodizationR4 ε (x + covariancePeriodVector a) =
      ρ.etaPeriodizationR4 ε x := by
  unfold etaPeriodizationR4
  calc
    (∑' k : Z4,
        ρ.etaPeriodTermR4 ε (x + covariancePeriodVector a) k) =
        ∑' k : Z4, ρ.etaPeriodTermR4 ε x (k + a) := by
      apply tsum_congr
      intro k
      exact ρ.etaPeriodTermR4_add_period ε x a k
    _ = ∑' k : Z4, ρ.etaPeriodTermR4 ε x k :=
      (Equiv.addRight a).tsum_eq
        (fun k : Z4 => ρ.etaPeriodTermR4 ε x k)

/-- Flip one coordinate of the integer lattice. -/
def coordinateFlipZ4 (i : Fin dim) (k : Z4) : Z4 :=
  Function.update k i (-(k i))

/-- The lattice coordinate flip as an involutive equivalence. -/
def coordinateFlipZ4Equiv (i : Fin dim) : Z4 ≃ Z4 :=
  Function.Involutive.toPerm (coordinateFlipZ4 i) fun k => by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp [coordinateFlipZ4]
    · simp [coordinateFlipZ4, Function.update_of_ne hji]

@[simp]
theorem coordinateFlipZ4Equiv_apply (i : Fin dim) (k : Z4) :
    coordinateFlipZ4Equiv i k = coordinateFlipZ4 i k :=
  rfl

/-- Flipping a representative and the matching lattice coordinate leaves
one periodization term unchanged. -/
theorem etaPeriodTermR4_coordinateFlip
    (ε : ℝ) (i : Fin dim) (x : R4) (k : Z4) :
    ρ.etaPeriodTermR4 ε (coordinateFlipR4 i x)
        (coordinateFlipZ4Equiv i k) =
      ρ.etaPeriodTermR4 ε x k := by
  unfold etaPeriodTermR4
  apply congrArg (fun t : ℝ => ε⁻¹ ^ (dim : ℕ) * t)
  have hvec :
      (fun j => ε⁻¹ *
        (coordinateFlipR4 i x j +
          covariancePeriodVector (coordinateFlipZ4Equiv i k) j)) =
        Function.update
          (fun j => ε⁻¹ * (x j + covariancePeriodVector k j))
          i (-(ε⁻¹ * (x i + covariancePeriodVector k i))) := by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp [coordinateFlipR4, coordinateFlipZ4Equiv,
        coordinateFlipZ4, covariancePeriodVector]
      ring
    · simp [coordinateFlipR4, coordinateFlipZ4Equiv,
        coordinateFlipZ4, covariancePeriodVector,
        Function.update_of_ne hji]
  rw [hvec]
  have heta := ρ.eta_even_coord i
    (fun j => ε⁻¹ * (x j + covariancePeriodVector k j))
  exact heta

/-- Arbitrary-representative periodization is even in every coordinate. -/
theorem etaPeriodizationR4_coordinateFlip
    (ε : ℝ) (i : Fin dim) (x : R4) :
    ρ.etaPeriodizationR4 ε (coordinateFlipR4 i x) =
      ρ.etaPeriodizationR4 ε x := by
  unfold etaPeriodizationR4
  calc
    (∑' k : Z4,
        ρ.etaPeriodTermR4 ε (coordinateFlipR4 i x) k) =
        ∑' k : Z4,
          ρ.etaPeriodTermR4 ε (coordinateFlipR4 i x)
            (coordinateFlipZ4Equiv i k) :=
      ((coordinateFlipZ4Equiv i).tsum_eq
        (fun k => ρ.etaPeriodTermR4 ε (coordinateFlipR4 i x) k)).symm
    _ = ∑' k : Z4, ρ.etaPeriodTermR4 ε x k := by
      apply tsum_congr
      intro k
      exact ρ.etaPeriodTermR4_coordinateFlip ε i x k

/-- The canonical lift of a flipped torus coordinate differs from the
flipped canonical lift by an integer period vector. -/
theorem exists_periodVector_torusLift_coordinateFlip
    (i : Fin dim) (z : T4) :
    ∃ a : Z4,
      torusLift (Function.update z i (-(z i))) =
        coordinateFlipR4 i (torusLift z) + covariancePeriodVector a := by
  have hcoe :
      ((torusLift (Function.update z i (-(z i))) i : ℝ) :
          AddCircle (2 * Real.pi)) =
        ((-(torusLift z i) : ℝ) : AddCircle (2 * Real.pi)) := by
    calc
      ((torusLift (Function.update z i (-(z i))) i : ℝ) :
          AddCircle (2 * Real.pi)) =
          (Function.update z i (-(z i))) i :=
        AddCircle.coe_equivIco
      _ = -(z i) := by simp
      _ = ((-(torusLift z i) : ℝ) :
          AddCircle (2 * Real.pi)) := by
        rw [AddCircle.coe_neg]
        have hlift :
            ((torusLift z i : ℝ) : AddCircle (2 * Real.pi)) = z i :=
          AddCircle.coe_equivIco
        exact (congrArg Neg.neg hlift).symm
  have hmem :
      torusLift (Function.update z i (-(z i))) i -
          (-(torusLift z i)) ∈
        AddSubgroup.zmultiples (2 * Real.pi) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hcoe
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  let a : Z4 := Function.update 0 i n
  refine ⟨a, ?_⟩
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp only [Pi.add_apply, coordinateFlipR4,
      covariancePeriodVector, a]
    simp only [Function.update_self]
    simp only [zsmul_eq_mul] at hn
    linarith
  · simp [torusLift, coordinateFlipR4, covariancePeriodVector, a,
      Function.update_of_ne hji]

/-- The torus covariance is invariant under a sign flip in one
coordinate. -/
theorem etaEpsT4_even_coord (ε : ℝ) (i : Fin dim) (z : T4) :
    ρ.etaEpsT4 ε (Function.update z i (-(z i))) =
      ρ.etaEpsT4 ε z := by
  obtain ⟨a, ha⟩ := exists_periodVector_torusLift_coordinateFlip i z
  rw [etaEpsT4_eq_etaPeriodizationR4,
    etaEpsT4_eq_etaPeriodizationR4, ha,
    etaPeriodizationR4_add_period,
    etaPeriodizationR4_coordinateFlip]

/-- The periodized covariance belongs to the torus symmetry class. -/
theorem etaEpsT4_memE (ε : ℝ) : MemEClassT4 (ρ.etaEpsT4 ε) where
  perm_invariant := ρ.etaEpsT4_perm_invariant ε
  even_coord := ρ.etaEpsT4_even_coord ε

end SmoothCutoff

end

end Anderson4D
