import Anderson4D.Continuum.PrimitiveEndpointScaling
import Anderson4D.Continuum.PrimitiveSymmetry

/-!
# Higher-order primitive kernel bounds

This file reconnects the real-valued R-51 scaling ledger to the
`ENNReal` Tonelli bounds for the Bochner integrals.  It closes both
pointwise estimates in Proposition 4.1 for every order `n ≥ 2`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The higher-order part of Proposition 4.1, uniformly in the
admissible input family.  The order constant is the fixed value `1`, so
the result covers the paper's full truncation
`n ≤ ⌊|log ε|⌋`; the support constant is irrelevant here because the
proof uses only the global term of each majorant. -/
theorem exists_uniform_primitiveKernelBounds_ge_two
    {C : ℝ} (hC : PermSumEstimate C)
    (ρ : SmoothCutoff) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (lam ε : ℝ) (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ)
        (supportConstant : ℝ),
        PrimitiveEstimateRegime n lam ε 1
            supportConstant C₂ →
          IsAdmissiblePrimitiveInput n G →
            PrimitiveKernelBounds
              ρ lam ε n (by omega) G supportConstant C₂ := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hsum⟩ :=
    sum_primitiveInsertedIntegrand_lintegral_le_r51GlobalDecayBound
      hC ρ
  let R : ℝ := 1 + 4 * ρ.radius
  let C₂ : ℝ := primitiveR51TotalBase C Ccov Ccell R
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hCnonneg : 0 ≤ C := hC.1.le
  have hC₂ : 0 < C₂ := by
    dsimp only [C₂]
    exact primitiveR51TotalBase_pos
      hCnonneg hCcov hCcell hR
  refine ⟨C₂, hC₂, ?_⟩
  intro lam ε n hn G supportConstant hreg hG
  rcases hreg with
    ⟨hn1, hε, hε1, hlam, _horderPos,
      _hsupportPos, _hC₂reg, hnOrder⟩
  have hlogLarge : 2 ≤ |Real.log ε| := by
    have hnReal : (2 : ℝ) ≤ n := by
      exact_mod_cast hn
    norm_num at hnOrder
    exact hnReal.trans hnOrder
  let q : ℕ := (compatibleCellCount ε).toNat
  have hqε : (q : ℤ) = compatibleCellCount ε := by
    dsimp only [q]
    exact Int.toNat_of_nonneg
      (compatibleCellCount_pos hε).le
  have hqpos : 0 < q := by
    by_contra hq
    have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq
    have hqNonpos :
        compatibleCellCount ε ≤ 0 := by
      apply Int.toNat_eq_zero.mp
      simpa only [q] using hqzero
    exact (not_le_of_gt (compatibleCellCount_pos hε)) hqNonpos
  letI : NeZero q := NeZero.of_pos hqpos
  have hnL :
      n ≤ 1 *
        (Nat.log 2 (4 * (2 * q)) + 1) := by
    simpa only [one_mul, primitiveDyadicPeriodLog] using
      order_le_primitiveDyadicPeriodLog
        hε hε1 hn1 (by simpa using hnOrder) hqε
  let δ : ℝ := compatibleMeshSize ε
  let farCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff : ℝ :=
    (12 + 32 * R ^ 2) *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let Q : ℝ := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hQ : 0 ≤ Q := by
    dsimp only [Q, dim]
    positivity
  have hfar : 0 ≤ farCoeff := by
    dsimp only [farCoeff]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (pow_nonneg
            (mul_nonneg hCcell.le (by positivity)) _))
        (terminalRadiusFactor_pos hR).le)
      (pow_nonneg hδ.le _)
  have hnear : 0 ≤ nearCoeff := by
    dsimp only [nearCoeff]
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (pow_nonneg
          (mul_nonneg hCcell.le
            (cellChainRadiusFactor_pos R).le) _))
      (pow_nonneg hδ.le _)
  have hcoeff :
      0 ≤ Q * (farCoeff + nearCoeff) :=
    mul_nonneg hQ (add_nonneg hfar hnear)
  have hcoupling :
      0 ≤ lamEps lam ε ^ (2 * n) :=
    (even_two_mul n).pow_nonneg _
  intro z
  have hsumBound :
      (∑ κ ∈ primitiveFullPairings n,
          ∫⁻ v,
            ENNReal.ofReal
              |primitiveInsertedIntegrand
                ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z 0 v)|
            ∂Measure.pi
              fun _ : Fin (2 * n - 2) => paperMeasure) ≤
        ENNReal.ofReal Q *
          (ENNReal.ofReal farCoeff +
            ENNReal.ofReal nearCoeff) *
          ENNReal.ofReal
            (primitiveR51GlobalDecayBound
              C n q 1 δ R z 0) := by
    simpa only [R, δ, farCoeff, nearCoeff, Q] using
      hsum n hn G hG hε hε1 hqε 1 hnL z 0
  let raw : ℝ :=
    lamEps lam ε ^ (2 * n) *
      (Q * (farCoeff + nearCoeff) *
        primitiveR51GlobalDecayBound
          C n q 1 δ R z 0)
  let targetInserted : ℝ :=
    (C₂ * lam) ^ (2 * n) *
      (1 / |Real.log ε| ^ 2) *
      (torusDistSq z + ε ^ 2)⁻¹ ^ 2
  have hraw :
      raw ≤ targetInserted := by
    simpa only [raw, targetInserted, C₂, R, δ,
      farCoeff, nearCoeff, Q, sub_zero] using
      primitiveR51ScaledAnalyticDecay_le
        hCnonneg hCcov hCcell hlam hε hε1 hR
          hlogLarge hqε n hn z 0
  have htargetInserted : 0 ≤ targetInserted := by
    dsimp only [targetInserted]
    positivity
  have hcollapse :
      ENNReal.ofReal raw =
        ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
          (ENNReal.ofReal Q *
            (ENNReal.ofReal farCoeff +
              ENNReal.ofReal nearCoeff) *
            ENNReal.ofReal
              (primitiveR51GlobalDecayBound
                C n q 1 δ R z 0)) := by
    dsimp only [raw]
    rw [ENNReal.ofReal_mul hcoupling,
      ENNReal.ofReal_mul hcoeff,
      ENNReal.ofReal_mul hQ,
      ENNReal.ofReal_add hfar hnear]
  have hinsertedE :
      ENNReal.ofReal
          |primitiveKernelInserted
            ρ lam ε n (by omega) G z 0| ≤
        ENNReal.ofReal targetInserted := by
    calc
      ENNReal.ofReal
          |primitiveKernelInserted
            ρ lam ε n (by omega) G z 0| ≤
        ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
          ∑ κ ∈ primitiveFullPairings n,
            ∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand
                  ρ ε n (by omega) G κ
                    (primitiveAssemble n (by omega) z 0 v)|
              ∂Measure.pi
                fun _ : Fin (2 * n - 2) => paperMeasure :=
        ofReal_abs_primitiveKernelInserted_le_lintegralSum
          ρ lam ε n (by omega) G z 0
      _ ≤ ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
          (ENNReal.ofReal Q *
            (ENNReal.ofReal farCoeff +
              ENNReal.ofReal nearCoeff) *
            ENNReal.ofReal
              (primitiveR51GlobalDecayBound
                C n q 1 δ R z 0)) :=
        mul_le_mul_right hsumBound _
      _ = ENNReal.ofReal raw := hcollapse.symm
      _ ≤ ENNReal.ofReal targetInserted :=
        ENNReal.ofReal_le_ofReal hraw
  have hinserted :
      |primitiveKernelInserted
          ρ lam ε n (by omega) G z 0| ≤
        targetInserted :=
    (ENNReal.ofReal_le_ofReal_iff
      htargetInserted).mp hinsertedE
  let D : ℝ := torusDistSq z + ε ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [torusDistSq_nonneg z, sq_pos_of_pos hε]
  have hordinaryE :
      ENNReal.ofReal D *
          ENNReal.ofReal
            |primitiveKernel
              ρ lam ε n (by omega) G z 0| ≤
        ENNReal.ofReal targetInserted := by
    calc
      ENNReal.ofReal D *
          ENNReal.ofReal
            |primitiveKernel
              ρ lam ε n (by omega) G z 0| ≤
        ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
          ∑ κ ∈ primitiveFullPairings n,
            ∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand
                  ρ ε n (by omega) G κ
                    (primitiveAssemble n (by omega) z 0 v)|
              ∂Measure.pi
                fun _ : Fin (2 * n - 2) => paperMeasure := by
        simpa only [D, sub_zero, add_comm] using
          endpointFactor_mul_ofReal_abs_primitiveKernel_le_insertedSum
            ρ lam ε n (by omega) G z 0
      _ ≤ ENNReal.ofReal (lamEps lam ε ^ (2 * n)) *
          (ENNReal.ofReal Q *
            (ENNReal.ofReal farCoeff +
              ENNReal.ofReal nearCoeff) *
            ENNReal.ofReal
              (primitiveR51GlobalDecayBound
                C n q 1 δ R z 0)) :=
        mul_le_mul_right hsumBound _
      _ = ENNReal.ofReal raw := hcollapse.symm
      _ ≤ ENNReal.ofReal targetInserted :=
        ENNReal.ofReal_le_ofReal hraw
  have hordinaryMul :
      D *
          |primitiveKernel
            ρ lam ε n (by omega) G z 0| ≤
        targetInserted := by
    apply (ENNReal.ofReal_le_ofReal_iff
      htargetInserted).mp
    rw [ENNReal.ofReal_mul hD.le]
    exact hordinaryE
  have hordinary :
      |primitiveKernel
          ρ lam ε n (by omega) G z 0| ≤
        (C₂ * lam) ^ (2 * n) *
          (1 / |Real.log ε| ^ 2) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 3 := by
    calc
      |primitiveKernel
          ρ lam ε n (by omega) G z 0| =
        D⁻¹ *
          (D *
            |primitiveKernel
              ρ lam ε n (by omega) G z 0|) := by
        field_simp [hD.ne']
      _ ≤ D⁻¹ * targetInserted :=
        mul_le_mul_of_nonneg_left hordinaryMul
          (inv_nonneg.mpr hD.le)
      _ = (C₂ * lam) ^ (2 * n) *
          (1 / |Real.log ε| ^ 2) *
          (torusDistSq z + ε ^ 2)⁻¹ ^ 3 := by
        dsimp only [D, targetInserted]
        ring
  constructor
  · unfold primitiveKernelDiff
    refine hordinary.trans ?_
    unfold primitiveKernelMajorant
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left
    · exact le_add_of_nonneg_left
        (mul_nonneg
          (mul_nonneg
            (div_nonneg (by positivity) (abs_nonneg _))
            (invSqKer_nonneg z))
          (primitiveSupportIndicator_nonneg
            supportConstant ε z))
    · exact (even_two_mul n).pow_nonneg (C₂ * lam)
  · unfold primitiveKernelInsertedDiff
    dsimp only [targetInserted] at hinserted
    refine hinserted.trans ?_
    unfold primitiveInsertedMajorant
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left
    · exact le_add_of_nonneg_left
        (mul_nonneg
          (mul_nonneg
            (div_nonneg (by positivity) (abs_nonneg _))
            (invSqKer_nonneg z))
          (primitiveSupportIndicator_nonneg
            supportConstant ε z))
    · exact (even_two_mul n).pow_nonneg (C₂ * lam)

end

end Anderson4D
