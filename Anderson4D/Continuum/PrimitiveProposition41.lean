import Anderson4D.Continuum.PrimitiveBaseSymmetry
import Anderson4D.Continuum.PrimitiveHigherBound
import Anderson4D.PermSum.Main

/-!
# Proposition 4.1

Paper: P-4.1 — Prop 4.1 — the primitive pairing estimate, proved

This file combines the exact first-order computation with the
endpoint-preserving R-51 argument at orders `n ≥ 2`, and packages the
result in the frozen `Proposition41` specification.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-! ## Monotonicity in the named majorant constant -/

theorem primitiveKernelMajorant_mono_constant
    {C₁ C₂ lam ε supportConstant : ℝ} {n : ℕ} {z : T4}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hlam : 0 ≤ lam) :
    primitiveKernelMajorant C₁ lam ε supportConstant n z ≤
      primitiveKernelMajorant C₂ lam ε supportConstant n z := by
  have hbase₁ : 0 ≤ C₁ * lam :=
    mul_nonneg hC₁ hlam
  have hbase :
      C₁ * lam ≤ C₂ * lam :=
    mul_le_mul_of_nonneg_right hC hlam
  have hpow :
      (C₁ * lam) ^ (2 * n) ≤
        (C₂ * lam) ^ (2 * n) :=
    pow_le_pow_left₀ hbase₁ hbase _
  unfold primitiveKernelMajorant
  apply mul_le_mul_of_nonneg_right hpow
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (div_nonneg (by positivity) (abs_nonneg _))
        (invSqKer_nonneg z))
      (primitiveSupportIndicator_nonneg
        supportConstant ε z)
  · exact mul_nonneg
      (div_nonneg zero_le_one (sq_nonneg _))
      (pow_nonneg
        (inv_nonneg.mpr
          (add_nonneg (torusDistSq_nonneg z)
            (sq_nonneg ε))) 3)

theorem primitiveInsertedMajorant_mono_constant
    {C₁ C₂ lam ε supportConstant : ℝ} {n : ℕ} {z : T4}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hlam : 0 ≤ lam) :
    primitiveInsertedMajorant C₁ lam ε supportConstant n z ≤
      primitiveInsertedMajorant C₂ lam ε supportConstant n z := by
  have hbase₁ : 0 ≤ C₁ * lam :=
    mul_nonneg hC₁ hlam
  have hbase :
      C₁ * lam ≤ C₂ * lam :=
    mul_le_mul_of_nonneg_right hC hlam
  have hpow :
      (C₁ * lam) ^ (2 * n) ≤
        (C₂ * lam) ^ (2 * n) :=
    pow_le_pow_left₀ hbase₁ hbase _
  unfold primitiveInsertedMajorant
  apply mul_le_mul_of_nonneg_right hpow
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg
        (div_nonneg (by positivity) (abs_nonneg _))
        (invSqKer_nonneg z))
      (primitiveSupportIndicator_nonneg
        supportConstant ε z)
  · exact mul_nonneg
      (div_nonneg zero_le_one (sq_nonneg _))
      (pow_nonneg
        (inv_nonneg.mpr
          (add_nonneg (torusDistSq_nonneg z)
            (sq_nonneg ε))) 2)

theorem PrimitiveKernelBounds.mono_constant
    (ρ : SmoothCutoff) {lam ε : ℝ} {n : ℕ} (hn : 1 ≤ n)
    {G : Fin (2 * n - 1) → T4 → ℝ}
    {supportConstant C₁ C₂ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hlam : 0 ≤ lam)
    (hbound :
      PrimitiveKernelBounds
        ρ lam ε n hn G supportConstant C₁) :
    PrimitiveKernelBounds
      ρ lam ε n hn G supportConstant C₂ := by
  intro z
  obtain ⟨hordinary, hinserted⟩ := hbound z
  exact
    ⟨hordinary.trans
        (primitiveKernelMajorant_mono_constant
          hC₁ hC hlam),
      hinserted.trans
        (primitiveInsertedMajorant_mono_constant
          hC₁ hC hlam)⟩

/-! ## Final assembly -/

/-- Proposition 4.1 with its order constant exposed as exactly `1`.

The generic `Proposition41` specification existentially hides that
constant, which is appropriate for the standalone paper statement but
insufficient when connecting it to the concrete truncation
`A = ⌊|log ε|⌋`.  This strengthened public form records the compatibility
needed by the R-322/R-324 reductions. -/
theorem proposition41_order_one (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
        ∀ (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
          (G : Fin (2 * n - 1) → T4 → ℝ),
          Prop41BoundPredicate ρ lam ε n hn G
            1 supportConstant C := by
  obtain ⟨Cperm, hperm⟩ := permSum_estimate
  obtain ⟨C₂, hC₂, hhigher⟩ :=
    exists_uniform_primitiveKernelBounds_ge_two hperm ρ
  obtain ⟨supportConstant, C₁, hsupport, hC₁, hbase⟩ :=
    exists_uniform_prop41BoundPredicate_one ρ
  let C : ℝ := C₁ + C₂
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hC₁C : C₁ ≤ C := by
    dsimp only [C]
    linarith
  have hC₂C : C₂ ≤ C := by
    dsimp only [C]
    linarith
  refine
    ⟨supportConstant, C, hsupport, hC, ?_⟩
  intro lam ε n hn G hreg hG
  rcases hreg with
    ⟨hnReg, hε, hε1, hlam, horder,
      hsupportReg, _hCReg, hnOrder⟩
  by_cases hnOne : n = 1
  · subst n
    have hreg₁ :
        PrimitiveEstimateRegime 1 lam ε 1
          supportConstant C₁ :=
      ⟨hnReg, hε, hε1, hlam, horder,
        hsupportReg, hC₁, hnOrder⟩
    obtain ⟨hmem, hmemInserted, hbounds⟩ :=
      hbase lam ε 1 G hreg₁ hG
    exact
      ⟨hmem, hmemInserted,
        PrimitiveKernelBounds.mono_constant
          ρ (by omega) hC₁.le hC₁C hlam.le hbounds⟩
  · have hn₂ : 2 ≤ n := by omega
    have hreg₂ :
        PrimitiveEstimateRegime n lam ε 1
          supportConstant C₂ :=
      ⟨hnReg, hε, hε1, hlam, horder,
        hsupportReg, hC₂, hnOrder⟩
    have hbounds :=
      hhigher lam ε n hn₂ G supportConstant hreg₂ hG
    exact
      ⟨primitiveKernelDiff_memE
          ρ lam ε n hn G hG.1,
        primitiveKernelInsertedDiff_memE
          ρ lam ε n hn G hG.1,
        PrimitiveKernelBounds.mono_constant
          ρ hn hC₂.le hC₂C hlam.le hbounds⟩

/-- Proposition 4.1 specialized to every order used by the concrete
renormalized parametrix.

This theorem is the direct paper-facing bridge: its order hypothesis is
literally `n ≤ truncOrder ε`, with no hidden comparison constant left for a
downstream reduction to recover. -/
theorem proposition41_at_truncation (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
        ∀ (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
          (G : Fin (2 * n - 1) → T4 → ℝ),
          0 < lam → 0 < ε → ε ≤ 1 →
          n ≤ truncOrder ε →
          IsAdmissiblePrimitiveInput n G →
            MemEClassT4
                (primitiveKernelDiff ρ lam ε n hn G) ∧
              MemEClassT4
                (primitiveKernelInsertedDiff ρ lam ε n hn G) ∧
              PrimitiveKernelBounds
                ρ lam ε n hn G supportConstant C := by
  obtain ⟨supportConstant, C, hsupport, hC, hbound⟩ :=
    proposition41_order_one ρ
  refine
    ⟨supportConstant, C, hsupport, hC, ?_⟩
  intro lam ε n hn G hlam hε hε1 hntrunc hG
  exact
    hbound lam ε n hn G
      (primitiveEstimateRegime_of_le_truncOrder
        hn hε hε1 hlam hsupport hC hntrunc)
      hG

/-- **Proposition 4.1.**  Primitive pairing kernels belong to the
hyperoctahedrally invariant class `𝓔` and obey (4.3)--(4.4), uniformly
over the perturbative order range. -/
theorem proposition41 (ρ : SmoothCutoff) :
    Proposition41 ρ := by
  obtain ⟨supportConstant, C, hsupport, hC, hbound⟩ :=
    proposition41_order_one ρ
  exact
    ⟨1, supportConstant, C, zero_lt_one,
      hsupport, hC, hbound⟩

end

end Anderson4D
