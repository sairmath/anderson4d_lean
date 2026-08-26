import Anderson4D.Continuum.PrimitiveEstimate

/-!
# The first primitive-pairing order

Paper §5 begins the proof of Proposition 4.1 by separating `n = 1`.
At that order there are no internal variables and exactly one primitive
full pairing.  This file proves the resulting closed formulas for both
the ordinary and diameter-inserted kernels.  Thus the base case is reduced
honestly to the cutoff covariance bounds, with no lattice-tree machinery.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The unique full pairing of two indices. -/
def pairingFinTwo : PartialPairing (Fin 2) :=
  ⟨Fin.rev, Fin.rev_involutive⟩

theorem primitiveFullPairings_one_eq :
    primitiveFullPairings 1 = {pairingFinTwo} := by
  decide

@[simp] theorem pairingFinTwo_zero :
    pairingFinTwo (0 : Fin 2) = 1 := by
  decide

@[simp] theorem pairingFinTwo_one :
    pairingFinTwo (1 : Fin 2) = 0 := by
  decide

theorem pairingFinTwo_lowerSupport :
    pairingFinTwo.pairSupport.filter
      (fun i => i < pairingFinTwo i) = {0} := by
  decide

private theorem primitiveIntegrand_one
    (ρ : SmoothCutoff) (ε : ℝ) (G : Fin 1 → T4 → ℝ)
    (x : Fin 2 → T4) :
    primitiveIntegrand ρ ε 1 (by omega) G pairingFinTwo x =
      G 0 (x 0 - x 1) * ρ.etaEpsT4 ε (x 0 - x 1) := by
  rw [primitiveIntegrand, primitiveChainProduct,
    primitiveCovarianceProduct, pairingFinTwo_lowerSupport]
  simp [primitiveEdgeLeft, primitiveEdgeRight]

private theorem primitiveInsertedIntegrand_one
    (ρ : SmoothCutoff) (ε : ℝ) (G : Fin 1 → T4 → ℝ)
    (x : Fin 2 → T4) :
    primitiveInsertedIntegrand ρ ε 1 (by omega) G pairingFinTwo x =
      (ε ^ 2 + torusDistSq (x 0 - x 1)) *
        (G 0 (x 0 - x 1) * ρ.etaEpsT4 ε (x 0 - x 1)) := by
  letI : Nonempty (Fin 2) := inferInstance
  rw [primitiveInsertedIntegrand, primitiveIntegrand_one]
  congr 2
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    apply Finset.sup'_le
    intro j hj
    have hzero : torusDistSq (0 : T4) = 0 :=
      (torusDistSq_eq_zero_iff 0).mpr rfl
    fin_cases i <;> fin_cases j
    · change torusDistSq (x (0 : Fin 2) - x (0 : Fin 2)) ≤
        torusDistSq (x 0 - x 1)
      rw [sub_self, hzero]
      exact torusDistSq_nonneg (x 0 - x 1)
    · exact le_rfl
    · change torusDistSq (x (1 : Fin 2) - x (0 : Fin 2)) ≤
        torusDistSq (x 0 - x 1)
      rw [show x 1 - x 0 = -(x 0 - x 1) by abel, torusDistSq_neg]
    · change torusDistSq (x (1 : Fin 2) - x (1 : Fin 2)) ≤
        torusDistSq (x 0 - x 1)
      rw [sub_self, hzero]
      exact torusDistSq_nonneg (x 0 - x 1)
  · exact torusDistSq_sub_le_torusTupleDiameterSq x 0 1

/-- Closed `n = 1` formula quoted at the start of paper §5. -/
theorem primitiveKernel_one
    (ρ : SmoothCutoff) (lam ε : ℝ) (G : Fin 1 → T4 → ℝ)
    (z w : T4) :
    primitiveKernel ρ lam ε 1 (by omega) G z w =
      lamEps lam ε ^ 2 *
        (G 0 (z - w) * ρ.etaEpsT4 ε (z - w)) := by
  rw [primitiveKernel, primitiveFullPairings_one_eq]
  simp only [Finset.sum_singleton]
  have hconst : ∀ v : Fin 0 → T4,
      primitiveIntegrand ρ ε 1 (by omega) G pairingFinTwo
          (primitiveAssemble 1 (by omega) z w v) =
        G 0 (z - w) * ρ.etaEpsT4 ε (z - w) := by
    intro v
    rw [primitiveIntegrand_one]
    have hx0 :
        primitiveAssemble 1 (by omega) z w v (0 : Fin 2) = z := by
      simpa using primitiveAssemble_zero 1 (by omega) z w v
    have hx1 :
        primitiveAssemble 1 (by omega) z w v (1 : Fin 2) = w := by
      simpa [primitiveLast] using
        primitiveAssemble_last 1 (by omega) z w v
    rw [hx0, hx1]
  rw [integral_congr_ae (Filter.Eventually.of_forall hconst),
    integral_const]
  simp [measureReal_def]

/-- Closed `n = 1` formula with the (4.4) diameter insertion. -/
theorem primitiveKernelInserted_one
    (ρ : SmoothCutoff) (lam ε : ℝ) (G : Fin 1 → T4 → ℝ)
    (z w : T4) :
    primitiveKernelInserted ρ lam ε 1 (by omega) G z w =
      lamEps lam ε ^ 2 *
        ((ε ^ 2 + torusDistSq (z - w)) *
          (G 0 (z - w) * ρ.etaEpsT4 ε (z - w))) := by
  rw [primitiveKernelInserted, primitiveFullPairings_one_eq]
  simp only [Finset.sum_singleton]
  have hconst : ∀ v : Fin 0 → T4,
      primitiveInsertedIntegrand ρ ε 1 (by omega) G pairingFinTwo
          (primitiveAssemble 1 (by omega) z w v) =
        (ε ^ 2 + torusDistSq (z - w)) *
          (G 0 (z - w) * ρ.etaEpsT4 ε (z - w)) := by
    intro v
    rw [primitiveInsertedIntegrand_one]
    have hx0 :
        primitiveAssemble 1 (by omega) z w v (0 : Fin 2) = z := by
      simpa using primitiveAssemble_zero 1 (by omega) z w v
    have hx1 :
        primitiveAssemble 1 (by omega) z w v (1 : Fin 2) = w := by
      simpa [primitiveLast] using
        primitiveAssemble_last 1 (by omega) z w v
    rw [hx0, hx1]
  rw [integral_congr_ae (Filter.Eventually.of_forall hconst),
    integral_const]
  simp [measureReal_def]

end

end Anderson4D
