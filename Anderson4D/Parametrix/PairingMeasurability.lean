import Anderson4D.Parametrix.Measurability
import Anderson4D.Parametrix.MomentBounds
import Anderson4D.Probability.CovariancePoisson

/-!
# Measurability for individual parametrix pairing coefficients

This file supplies the measurable half of the spatial Fubini interface used
in the second-moment reduction.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The deterministic closed-form parametrix integrand is measurable in
all of its assembled spatial coordinates. -/
theorem measurable_detIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) :
    Measurable fun xt : Fin (m + 2) → T4 =>
      detIntegrand ρ ε m κ xt := by
  have hdiff (p : Fin m × Fin m) :
      Measurable fun xt : Fin (m + 2) → T4 =>
        diffFactor xt p := by
    unfold diffFactor
    exact
      (measurable_greenFn.comp
        (((measurable_pi_apply (varIdx p.2)).sub
          (measurable_pi_apply
            (⟨p.2.val + 2, by have := p.2.isLt; omega⟩ :
              Fin (m + 2)))))).sub
      (measurable_greenFn.comp
        (((measurable_pi_apply (varIdx p.1)).sub
          (measurable_pi_apply
            (⟨p.2.val + 2, by have := p.2.isLt; omega⟩ :
              Fin (m + 2))))))
  have hchain :
      Measurable fun xt : Fin (m + 2) → T4 =>
        ∏ e : Fin (m + 1),
          if e.val ∈ ((extract κ).map fun p => p.2.val + 1) then 1
          else greenFn (xt e.castSucc - xt e.succ) := by
    apply Finset.measurable_prod
    intro e _he
    by_cases hskip :
        e.val ∈ ((extract κ).map fun p => p.2.val + 1)
    · simp only [hskip, if_true]
      exact measurable_const
    · simp only [hskip, if_false]
      exact measurable_greenFn.comp
        ((measurable_pi_apply e.castSucc).sub
          (measurable_pi_apply e.succ))
  have hdifference :
      Measurable fun xt : Fin (m + 2) → T4 =>
        ((extract κ).map (diffFactor xt)).prod := by
    let ps := extract κ
    change Measurable fun xt : Fin (m + 2) → T4 =>
      (ps.map (diffFactor xt)).prod
    induction ps with
    | nil =>
        simp
    | cons p ps ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (hdiff p).mul ih
  have hcovariance :
      Measurable fun xt : Fin (m + 2) → T4 =>
        ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
          ρ.etaEpsT4 ε
            (xt (varIdx i) - xt (varIdx (κ i))) := by
    apply Finset.measurable_prod
    intro i _hi
    exact (ρ.measurable_etaEpsT4 ε).comp
      ((measurable_pi_apply (varIdx i)).sub
        (measurable_pi_apply (varIdx (κ i))))
  unfold detIntegrand
  exact (hchain.mul hdifference).mul hcovariance

namespace NoiseModel

variable (M : NoiseModel)

/-- `wickAt` is jointly measurable in the sample and its complete spatial
tuple. -/
theorem measurable_wickAt_joint
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) :
    Measurable fun p : M.Ω × (Fin (m + 2) → T4) =>
      wickAt M ρ ε κ p.2 p.1 := by
  unfold wickAt
  apply Finset.measurable_sum
  intro κ' _hκ'
  have hpairs :
      Measurable fun p : M.Ω × (Fin (m + 2) → T4) =>
        ∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
          ρ.etaEpsT4 ε
            (p.2 (varIdx i.val) -
              p.2 (varIdx (κ' i).val)) := by
    apply Finset.measurable_prod
    intro i _hi
    exact (ρ.measurable_etaEpsT4 ε).comp
      (((measurable_pi_apply (varIdx i.val)).comp measurable_snd).sub
        ((measurable_pi_apply (varIdx (κ' i).val)).comp measurable_snd))
  have hsingles :
      Measurable fun p : M.Ω × (Fin (m + 2) → T4) =>
        ∏ i ∈ κ'.singles,
          M.xiEps ρ ε p.1 (p.2 (varIdx i.val)) := by
    apply Finset.measurable_prod
    intro i _hi
    have hω :
        Measurable fun p : M.Ω × (Fin (m + 2) → T4) => p.1 :=
      measurable_fst
    have hz :
        Measurable fun p : M.Ω × (Fin (m + 2) → T4) =>
          p.2 (varIdx i.val) :=
      (measurable_pi_apply (varIdx i.val)).comp measurable_snd
    exact (M.measurable_xiEps_joint ρ ε).comp (hω.prodMk hz)
  exact (measurable_const.mul hpairs).mul hsingles

/-- The random renormalized integrand is jointly measurable in the sample
and its assembled spatial tuple. -/
theorem measurable_randIntegrand_joint
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) :
    Measurable fun p : M.Ω × (Fin (m + 2) → T4) =>
      randIntegrand M ρ ε κ p.2 p.1 := by
  unfold randIntegrand
  exact
    ((measurable_detIntegrand ρ ε κ).comp measurable_snd).mul
      (M.measurable_wickAt_joint ρ ε κ)

/-- A single random pairing kernel is jointly measurable in the sample
and its two external points. -/
theorem measurable_randRI_joint
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m)) :
    Measurable fun p : (M.Ω × T4) × T4 =>
      randRI M ρ lam ε m κ p.1.2 p.2 p.1.1 := by
  let V := Fin m → T4
  have hω :
      Measurable fun p : (((M.Ω × T4) × T4) × V) =>
        p.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hx :
      Measurable fun p : (((M.Ω × T4) × T4) × V) =>
        p.1.1.2 :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hy :
      Measurable fun p : (((M.Ω × T4) × T4) × V) =>
        p.1.2 :=
    measurable_snd.comp measurable_fst
  have hassemble :
      Measurable fun p : (((M.Ω × T4) × T4) × V) =>
        assemble p.1.1.2 p.1.2 p.2 :=
    (measurable_assemble_prod m).comp
      (hx.prodMk (hy.prodMk measurable_snd))
  have hraw :
      StronglyMeasurable fun p : (((M.Ω × T4) × T4) × V) =>
        randIntegrand M ρ ε κ
          (assemble p.1.1.2 p.1.2 p.2) p.1.1.1 :=
    ((M.measurable_randIntegrand_joint ρ ε κ).comp
      (hω.prodMk hassemble)).stronglyMeasurable
  have hint :
      StronglyMeasurable fun p : (M.Ω × T4) × T4 =>
        ∫ v : V,
          randIntegrand M ρ ε κ
            (assemble p.1.2 p.2 v) p.1.1
          ∂(Measure.pi fun _ => paperMeasure) :=
    hraw.integral_prod_right
  unfold randRI
  exact (measurable_const.mul hint.measurable)

/-- Every individual pairing contribution to a Fourier coefficient is
measurable in the noise sample. -/
theorem measurable_pmPairingCoeff
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) :
    Measurable (pmPairingCoeff M ρ lam ε m α β κ) := by
  have hω :
      Measurable fun p : (M.Ω × T4) × T4 => p.1.1 :=
    measurable_fst.comp measurable_fst
  have hx :
      Measurable fun p : (M.Ω × T4) × T4 => p.1.2 :=
    measurable_snd.comp measurable_fst
  have hy :
      Measurable fun p : (M.Ω × T4) × T4 => p.2 :=
    measurable_snd
  have hraw :
      StronglyMeasurable fun p : (M.Ω × T4) × T4 =>
        charT4 α p.1.2 * charT4 β p.2 *
          (randRI M ρ lam ε m κ p.1.2 p.2 p.1.1 : ℂ) := by
    exact
      ((((continuous_charT4 α).measurable.comp hx).mul
        ((continuous_charT4 β).measurable.comp hy)).mul
        (Complex.measurable_ofReal.comp
          ((M.measurable_randRI_joint ρ lam ε m κ).comp
            ((hω.prodMk hx).prodMk hy)))).stronglyMeasurable
  have hintY :
      StronglyMeasurable fun p : M.Ω × T4 =>
        ∫ y,
          charT4 α p.2 * charT4 β y *
            (randRI M ρ lam ε m κ p.2 y p.1 : ℂ)
          ∂paperMeasure :=
    hraw.integral_prod_right
  have hintX :
      StronglyMeasurable fun ω : M.Ω =>
        ∫ x, ∫ y,
          charT4 α x * charT4 β y *
            (randRI M ρ lam ε m κ x y ω : ℂ)
          ∂paperMeasure ∂paperMeasure :=
    hintY.integral_prod_right
  exact hintX.measurable

/-- The measurable field of `PmCoeffMomentFubiniOutput` is unconditional:
it follows directly from the explicit Fourier-series construction. -/
theorem aestronglyMeasurable_pmPairingCoeff
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) :
    AEStronglyMeasurable
      (pmPairingCoeff M ρ lam ε m α β κ)
      (volume : Measure M.Ω) :=
  (M.measurable_pmPairingCoeff ρ lam ε m α β κ).aestronglyMeasurable

end NoiseModel

end

end Anderson4D
