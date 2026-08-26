import Anderson4D.Continuum.CovarianceSymmetry
import Anderson4D.Continuum.PrimitiveBase
import Anderson4D.Continuum.PrimitiveBaseUniform

/-!
# Symmetry of the first primitive kernel

The analytic base bounds and the symmetry conclusion of Proposition 4.1
are deliberately separated.  Here the latter follows from closure of the
hyperoctahedral class under products and the periodized covariance symmetry.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The torus symmetry class is closed under pointwise multiplication. -/
theorem MemEClassT4.mul {f g : T4 → ℝ}
    (hf : MemEClassT4 f) (hg : MemEClassT4 g) :
    MemEClassT4 fun z => f z * g z where
  perm_invariant := by
    intro σ z
    rw [hf.perm_invariant σ z, hg.perm_invariant σ z]
  even_coord := by
    intro i z
    rw [hf.even_coord i z, hg.even_coord i z]

/-- Multiplication by a scalar preserves the torus symmetry class. -/
theorem MemEClassT4.const_mul {f : T4 → ℝ}
    (hf : MemEClassT4 f) (c : ℝ) :
    MemEClassT4 fun z => c * f z where
  perm_invariant := by
    intro σ z
    rw [hf.perm_invariant σ z]
  even_coord := by
    intro i z
    rw [hf.even_coord i z]

/-- The canonical squared torus distance is hyperoctahedrally invariant. -/
theorem torusDistSq_memE : MemEClassT4 torusDistSq where
  perm_invariant := by
    intro σ z
    rw [torusDistSq_eq_sum_norm_sq, torusDistSq_eq_sum_norm_sq,
      ← Equiv.sum_comp σ (fun i => ‖z i‖ ^ 2)]
    rfl
  even_coord := by
    intro i z
    rw [torusDistSq_eq_sum_norm_sq, torusDistSq_eq_sum_norm_sq]
    apply Finset.sum_congr rfl
    intro j _
    rcases eq_or_ne j i with rfl | hji
    · simp
    · rw [Function.update_of_ne hji]

/-- The diameter factor in the inserted base kernel is symmetric. -/
theorem add_torusDistSq_memE (ε : ℝ) :
    MemEClassT4 fun z => ε ^ 2 + torusDistSq z where
  perm_invariant := by
    intro σ z
    rw [torusDistSq_memE.perm_invariant σ z]
  even_coord := by
    intro i z
    rw [torusDistSq_memE.even_coord i z]

/-- The ordinary first primitive kernel belongs to `𝓔`. -/
theorem primitiveKernelDiff_one_memE
    (ρ : SmoothCutoff) (lam ε : ℝ) (G : Fin 1 → T4 → ℝ)
    (hG : MemEClassT4 (G 0)) :
    MemEClassT4 (primitiveKernelDiff ρ lam ε 1 (by omega) G) := by
  have hprod := hG.mul (ρ.etaEpsT4_memE ε)
  have hscaled := hprod.const_mul (lamEps lam ε ^ 2)
  have heq :
      primitiveKernelDiff ρ lam ε 1 (by omega) G =
        fun z => lamEps lam ε ^ 2 *
          (G 0 z * ρ.etaEpsT4 ε z) := by
    funext z
    rw [primitiveKernelDiff, primitiveKernel_one, sub_zero]
  rw [heq]
  exact hscaled

/-- The diameter-inserted first primitive kernel belongs to `𝓔`. -/
theorem primitiveKernelInsertedDiff_one_memE
    (ρ : SmoothCutoff) (lam ε : ℝ) (G : Fin 1 → T4 → ℝ)
    (hG : MemEClassT4 (G 0)) :
    MemEClassT4
      (primitiveKernelInsertedDiff ρ lam ε 1 (by omega) G) := by
  have hinner := hG.mul (ρ.etaEpsT4_memE ε)
  have hwithDiameter := (add_torusDistSq_memE ε).mul hinner
  have hscaled := hwithDiameter.const_mul (lamEps lam ε ^ 2)
  have heq :
      primitiveKernelInsertedDiff ρ lam ε 1 (by omega) G =
        fun z => lamEps lam ε ^ 2 *
          ((ε ^ 2 + torusDistSq z) *
            (G 0 z * ρ.etaEpsT4 ε z)) := by
    funext z
    rw [primitiveKernelInsertedDiff, primitiveKernelInserted_one, sub_zero]
  rw [heq]
  exact hscaled

/-- Fully uniform Proposition 4.1 predicate at the base order, including
both symmetry conclusions and both analytic estimates. -/
theorem exists_uniform_prop41BoundPredicate_one (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
        ∀ (lam ε orderConstant : ℝ) (G : Fin 1 → T4 → ℝ),
          Prop41BoundPredicate ρ lam ε 1 (by omega) G
            orderConstant supportConstant C := by
  obtain ⟨supportConstant, C, hsupport, hC, hbounds⟩ :=
    exists_uniform_primitiveKernelBounds_one ρ
  refine ⟨supportConstant, C, hsupport, hC, ?_⟩
  intro lam ε orderConstant G hreg hadm
  refine ⟨primitiveKernelDiff_one_memE ρ lam ε G (hadm.1 0),
    primitiveKernelInsertedDiff_one_memE ρ lam ε G (hadm.1 0), ?_⟩
  exact hbounds lam ε orderConstant G hreg hadm

end

end Anderson4D
