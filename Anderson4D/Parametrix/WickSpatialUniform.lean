import Anderson4D.Parametrix.MollifiedWickSecondMoment
import Anderson4D.Continuum.PeriodizedCovariance

/-!
# Uniform spatial bounds for the parametrix Wick factors

The pointwise Wick law is not by itself enough to exchange the noise and
physical integrations in the second-moment calculation.  This file records
the missing uniform ingredient.  At fixed mollification scale the covariance
is bounded uniformly on the torus, hence the second moment of every fixed
finite Wick factor is bounded uniformly in all of its spatial labels.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NoiseModel

variable (M : NoiseModel)

/-- Exact cross-contraction formula for two `wickAt` factors with arbitrary
spatial tuples. -/
theorem integral_wickAt_mul_eq_crossSingles
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (xtp xtm : Fin (m + 2) → T4) :
    (∫ ω,
        wickAt M ρ ε κp xtp ω *
          wickAt M ρ ε κm xtm ω
        ∂(volume : Measure M.Ω)) =
      crossSinglesEquivCovarianceSum κp κm
        (fun i j =>
          ρ.etaEpsT4 ε
            (xtp (varIdx i.val) - xtm (varIdx j.val))) := by
  simp_rw [wickAt_eq_wickPolynomial]
  rw [M.integral_wickPolynomial_xiEps_mul ρ hε]
  exact crossWickList_wickAtSingleLabels_eq_crossSingles
    κp κm xtp xtm
      (fun x y : T4 => ρ.etaEpsT4 ε (x - y))

/-- Products of two `wickAt` factors are integrable for every fixed pair of
spatial tuples. -/
theorem integrable_wickAt_mul
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) {m : ℕ}
    (κp κm : PartialPairing (Fin m))
    (xtp xtm : Fin (m + 2) → T4) :
    Integrable
      (fun ω =>
        wickAt M ρ ε κp xtp ω *
          wickAt M ρ ε κm xtm ω)
      (volume : Measure M.Ω) := by
  simp_rw [wickAt_eq_wickPolynomial]
  exact M.integrable_wickPolynomial_xiEps_mul ρ hε
    (wickAtSingleLabels κp xtp)
    (wickAtSingleLabels κm xtm)

/-- A uniform covariance bound controls the diagonal cross-contraction sum
of one Wick factor, independently of its spatial labels. -/
theorem crossSingles_self_le_of_covariance_bound
    (ρ : SmoothCutoff) (ε B : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m))
    (hB : ∀ z : T4, ρ.etaEpsT4 ε z ≤ B)
    (xt : Fin (m + 2) → T4) :
    crossSinglesEquivCovarianceSum κ κ
        (fun i j =>
          ρ.etaEpsT4 ε
            (xt (varIdx i.val) - xt (varIdx j.val))) ≤
      ∑ _π : κ.singles ≃ κ.singles,
        ∏ _i : κ.singles, B := by
  unfold crossSinglesEquivCovarianceSum
  apply Finset.sum_le_sum
  intro π _hπ
  unfold crossSinglesEquivCovarianceProduct
  apply Finset.prod_le_prod
  · intro i _hi
    exact SmoothCutoff.etaEpsT4_nonneg ρ ε _
  · intro i _hi
    exact hB _

/-- The second moment of a fixed Wick factor admits a finite uniform bound
over every choice of its spatial labels. -/
theorem exists_uniform_integral_sq_wickAt_bound
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ xt : Fin (m + 2) → T4,
        (∫ ω, wickAt M ρ ε κ xt ω ^ 2
            ∂(volume : Measure M.Ω)) ≤ C := by
  obtain ⟨Cη, hCη, hη⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let B : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  let C : ℝ :=
    ∑ _π : κ.singles ≃ κ.singles,
      ∏ _i : κ.singles, B
  have hC0 : 0 ≤ C := by
    unfold C
    have hB0 : 0 ≤ B := by
      exact mul_nonneg
        (pow_nonneg (inv_nonneg.mpr hε.le) _) hCη.le
    positivity
  refine ⟨C, hC0, ?_⟩
  intro xt
  calc
    (∫ ω, wickAt M ρ ε κ xt ω ^ 2
        ∂(volume : Measure M.Ω)) =
      crossSinglesEquivCovarianceSum κ κ
        (fun i j =>
          ρ.etaEpsT4 ε
            (xt (varIdx i.val) - xt (varIdx j.val))) := by
      simpa only [pow_two] using
        M.integral_wickAt_mul_eq_crossSingles
          ρ hε κ κ xt xt
    _ ≤ C := by
      exact crossSingles_self_le_of_covariance_bound
        ρ ε B κ (fun z => hη hε hε1 z) xt

/-- The absolute first moment of a product of two Wick factors is uniformly
bounded in both spatial tuples.  This is the domination used in the
noise-by-space Tonelli argument. -/
theorem exists_uniform_integral_norm_wickAt_mul_bound
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κp κm : PartialPairing (Fin m)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (xtp xtm : Fin (m + 2) → T4),
        (∫ ω,
            ‖wickAt M ρ ε κp xtp ω *
              wickAt M ρ ε κm xtm ω‖
            ∂(volume : Measure M.Ω)) ≤ C := by
  obtain ⟨Cp, hCp0, hCp⟩ :=
    M.exists_uniform_integral_sq_wickAt_bound
      ρ hε hε1 κp
  obtain ⟨Cm, hCm0, hCm⟩ :=
    M.exists_uniform_integral_sq_wickAt_bound
      ρ hε hε1 κm
  refine ⟨(Cp + Cm) / 2, div_nonneg (add_nonneg hCp0 hCm0)
    (by norm_num), ?_⟩
  intro xtp xtm
  let fp : M.Ω → ℝ :=
    fun ω => wickAt M ρ ε κp xtp ω
  let fm : M.Ω → ℝ :=
    fun ω => wickAt M ρ ε κm xtm ω
  have hpInt : Integrable (fun ω => fp ω ^ 2)
      (volume : Measure M.Ω) := by
    simpa only [fp, pow_two] using
      M.integrable_wickAt_mul ρ hε κp κp xtp xtp
  have hmInt : Integrable (fun ω => fm ω ^ 2)
      (volume : Measure M.Ω) := by
    simpa only [fm, pow_two] using
      M.integrable_wickAt_mul ρ hε κm κm xtm xtm
  have hprodInt : Integrable (fun ω => fp ω * fm ω)
      (volume : Measure M.Ω) :=
    M.integrable_wickAt_mul ρ hε κp κm xtp xtm
  have hmajorInt :
      Integrable (fun ω => (fp ω ^ 2 + fm ω ^ 2) / 2)
        (volume : Measure M.Ω) :=
    (hpInt.add hmInt).div_const 2
  calc
    (∫ ω,
        ‖wickAt M ρ ε κp xtp ω *
          wickAt M ρ ε κm xtm ω‖
        ∂(volume : Measure M.Ω)) =
      ∫ ω, ‖fp ω * fm ω‖
        ∂(volume : Measure M.Ω) := by rfl
    _ ≤ ∫ ω, (fp ω ^ 2 + fm ω ^ 2) / 2
        ∂(volume : Measure M.Ω) := by
      apply integral_mono hprodInt.norm hmajorInt
      intro ω
      change |fp ω * fm ω| ≤
        (fp ω ^ 2 + fm ω ^ 2) / 2
      rw [abs_mul]
      nlinarith [sq_nonneg (|fp ω| - |fm ω|),
        sq_abs (fp ω), sq_abs (fm ω)]
    _ = ((∫ ω, fp ω ^ 2 ∂(volume : Measure M.Ω)) +
          ∫ ω, fm ω ^ 2 ∂(volume : Measure M.Ω)) / 2 := by
      rw [integral_div, integral_add hpInt hmInt]
    _ ≤ (Cp + Cm) / 2 := by
      exact div_le_div_of_nonneg_right
        (add_le_add (hCp xtp) (hCm xtm)) (by norm_num)

/-- On every continuous noise sample, `wickAt` is bounded uniformly over
all of its spatial labels. -/
theorem exists_uniform_norm_wickAt_bound_of_continuous
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (κ : PartialPairing (Fin m)) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ xt : Fin (m + 2) → T4,
        |wickAt M ρ ε κ xt ω| ≤ B := by
  let ξ : C(T4, ℝ) :=
    ⟨M.xiEps ρ ε ω, hξ⟩
  let X : ℝ := ‖ξ‖
  have hX0 : 0 ≤ X := norm_nonneg _
  have hX : ∀ z : T4,
      |M.xiEps ρ ε ω z| ≤ X := by
    intro z
    change |ξ z| ≤ X
    simpa only [X, Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm ξ z
  -- Repeat the finite estimate with the fixed simultaneous bound.
  obtain ⟨Cη, hCη, heta⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  let A : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη
  let K : ℝ := (1 + A) ^ m * (1 + X) ^ m
  let B : ℝ :=
    ∑ _κ' : PartialPairing {i // i ∈ κ.singles}, K
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hA1 : 1 ≤ 1 + A := by linarith
  have hX1 : 1 ≤ 1 + X := by linarith
  have hK0 : 0 ≤ K := by
    exact mul_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith) _)
  refine ⟨B, Finset.sum_nonneg fun _ _ => hK0, ?_⟩
  intro xt
  unfold wickAt
  calc
    |∑ κ' : PartialPairing {i // i ∈ κ.singles},
        (-1 : ℝ) ^ κ'.pairs.card *
          (∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
            ρ.etaEpsT4 ε
              (xt (varIdx i.val) -
                xt (varIdx (κ' i).val))) *
          ∏ i ∈ κ'.singles,
            M.xiEps ρ ε ω (xt (varIdx i.val))| ≤
      ∑ κ' : PartialPairing {i // i ∈ κ.singles},
        |(-1 : ℝ) ^ κ'.pairs.card *
          (∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
            ρ.etaEpsT4 ε
              (xt (varIdx i.val) -
                xt (varIdx (κ' i).val))) *
          ∏ i ∈ κ'.singles,
            M.xiEps ρ ε ω (xt (varIdx i.val))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _κ' :
        PartialPairing {i // i ∈ κ.singles}, K := by
      apply Finset.sum_le_sum
      intro κ' _hκ'
      have hcov :
          |∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
              ρ.etaEpsT4 ε
                (xt (varIdx i.val) -
                  xt (varIdx (κ' i).val))| ≤
            (1 + A) ^ m := by
        rw [abs_of_nonneg
          (Finset.prod_nonneg fun i _ =>
            ρ.etaEpsT4_nonneg ε _)]
        calc
          (∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
              ρ.etaEpsT4 ε
                (xt (varIdx i.val) -
                  xt (varIdx (κ' i).val))) ≤
              ∏ _i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
                (1 + A) := by
            apply Finset.prod_le_prod
            · intro i _hi
              exact ρ.etaEpsT4_nonneg ε _
            · intro i _hi
              have hi := heta hε hε1
                (xt (varIdx i.val) -
                  xt (varIdx (κ' i).val))
              change
                ρ.etaEpsT4 ε
                    (xt (varIdx i.val) -
                      xt (varIdx (κ' i).val)) ≤ A at hi
              exact hi.trans (by linarith)
          _ = (1 + A) ^
              (κ'.pairSupport.filter
                (fun i => i < κ' i)).card := by simp
          _ ≤ (1 + A) ^ m := by
            apply pow_le_pow_right₀ hA1
            calc
              (κ'.pairSupport.filter
                  (fun i => i < κ' i)).card ≤
                  Fintype.card {i // i ∈ κ.singles} :=
                Finset.card_le_univ _
              _ = κ.singles.card :=
                Fintype.card_coe κ.singles
              _ ≤ Fintype.card (Fin m) :=
                Finset.card_le_univ _
              _ = m := Fintype.card_fin m
      have hnoiseProd :
          |∏ i ∈ κ'.singles,
              M.xiEps ρ ε ω (xt (varIdx i.val))| ≤
            (1 + X) ^ m := by
        rw [Finset.abs_prod]
        calc
          (∏ i ∈ κ'.singles,
              |M.xiEps ρ ε ω (xt (varIdx i.val))|) ≤
              ∏ _i ∈ κ'.singles, (1 + X) := by
            apply Finset.prod_le_prod
            · intro i _hi
              exact abs_nonneg _
            · intro i _hi
              exact (hX _).trans (by linarith)
          _ = (1 + X) ^ κ'.singles.card := by simp
          _ ≤ (1 + X) ^ m := by
            apply pow_le_pow_right₀ hX1
            calc
              κ'.singles.card ≤
                  Fintype.card {i // i ∈ κ.singles} :=
                Finset.card_le_univ _
              _ = κ.singles.card :=
                Fintype.card_coe κ.singles
              _ ≤ Fintype.card (Fin m) :=
                Finset.card_le_univ _
              _ = m := Fintype.card_fin m
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      exact
        (mul_le_mul hcov hnoiseProd
          (abs_nonneg _) (pow_nonneg (by linarith) _))
    _ = B := rfl

end NoiseModel

end

end Anderson4D
