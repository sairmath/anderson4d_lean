import Anderson4D.Parametrix.GlobalIntegrability
import Anderson4D.Parametrix.IdentityRightKernelSymmetry

/-!
# Integrability of graded parametrix words

On every sample for which the mollified noise is continuous, the vertex
factor of a graded resolvent word is bounded.  Global Green-chain
integrability therefore makes the complete word integrable jointly in
both endpoints and all internal variables.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

theorem measurable_renormWordWeight
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (d : ℕ) :
    Measurable
      (fun z : T4 =>
        renormWordWeight M ρ lam ε d z ω) := by
  by_cases hd : d = 1
  · simp only [renormWordWeight, hd, if_true]
    exact measurable_const.mul
      ((M.measurable_xiEps_joint ρ ε).comp
        (measurable_const.prodMk measurable_id))
  · simp only [renormWordWeight, hd, if_false]
    by_cases heven : Even d
    · simp only [heven, if_true]
      exact measurable_const
    · simp only [heven, if_false]
      exact measurable_const

theorem continuous_renormWordWeight
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (d : ℕ) :
    Continuous
      (fun z : T4 =>
        renormWordWeight M ρ lam ε d z ω) := by
  by_cases hd : d = 1
  · simp only [renormWordWeight, hd, if_true]
    exact continuous_const.mul hξ
  · simp only [renormWordWeight, hd, if_false]
    by_cases heven : Even d
    · simp only [heven, if_true]
      exact continuous_const
    · simp only [heven, if_false]
      exact continuous_const

/-- The finite vertex multiplier of one graded word, packaged as a
continuous map so its uniform bound is canonical. -/
def renormWordMultiplierContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (word : List ℕ) :
    C((Fin word.length → T4), ℂ) where
  toFun v :=
    ∏ i : Fin word.length,
      (renormWordWeight M ρ lam ε
        (word.get i) (v i) ω : ℂ)
  continuous_toFun := by
    apply continuous_finsetProd
    intro i _hi
    exact Complex.continuous_ofReal.comp
      ((continuous_renormWordWeight
        M ρ lam ε ω hξ (word.get i)).comp
          (continuous_apply i))

@[simp]
theorem renormWordMultiplierContinuousMap_apply
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (word : List ℕ)
    (v : Fin word.length → T4) :
    renormWordMultiplierContinuousMap
        M ρ lam ε ω hξ word v =
      ∏ i : Fin word.length,
        (renormWordWeight M ρ lam ε
          (word.get i) (v i) ω : ℂ) :=
  rfl

/-- Joint integrability of a complete graded word in flat coordinates.
This is the global, coefficient-level analytic input for Proposition 3.4. -/
theorem integrable_renormWordIntegrandOnTuple_global
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (word : List ℕ) :
    Integrable
      (fun p :
          T4 × (T4 × (Fin word.length → T4)) =>
        (renormWordIntegrandOnTuple
          M ρ lam ε word
          (assemble p.1 p.2.1 p.2.2) ω : ℂ))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin word.length =>
            paperMeasure))) := by
  let multiplier :
      (T4 × (T4 × (Fin word.length → T4))) → ℂ :=
    fun p =>
      ∏ i : Fin word.length,
        (renormWordWeight M ρ lam ε
          (word.get i) (p.2.2 i) ω : ℂ)
  have hmultiplier :
      AEStronglyMeasurable multiplier
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin word.length =>
              paperMeasure))) := by
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_prod
    intro i _hi
    exact Complex.measurable_ofReal.comp
      ((measurable_renormWordWeight
        M ρ lam ε ω (word.get i)).comp
          ((measurable_pi_apply i).comp
            (measurable_snd.comp measurable_snd)))
  let multiplierMap :=
    renormWordMultiplierContinuousMap
      M ρ lam ε ω hξ word
  have hbound :
      ∀ᵐ p ∂(paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin word.length =>
              paperMeasure))),
        ‖multiplier p‖ ≤ ‖multiplierMap‖ :=
    Filter.Eventually.of_forall fun p => by
      exact
        ContinuousMap.norm_coe_le_norm
          multiplierMap p.2.2
  have hmajor :=
    integrable_bounded_mul_flatGreenChain_joint
      word.length multiplier hmultiplier
      ‖multiplierMap‖ hbound
  convert hmajor using 1
  funext p
  unfold renormWordIntegrandOnTuple multiplier
  push_cast
  simp only [assemble_varIdx]
  ring

/-- Consequently, the fixed-endpoint word ledger holds for almost every
pair of external points.  This is the section statement used by
coefficient-level Fubini; no false assertion is made on the diagonal. -/
theorem ae_ae_renormWordIntegrable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (word : List ℕ) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      RenormWordIntegrable
        M ρ lam ε word x y ω := by
  have hglobal :=
    integrable_renormWordIntegrandOnTuple_global
      M ρ lam ε ω hξ word
  filter_upwards [hglobal.prod_right_ae] with x hx
  filter_upwards [hx.prod_right_ae] with y hy
  unfold RenormWordIntegrable
  have hyRe := hy.re
  convert hyRe using 1
  funext v
  exact Complex.ofReal_re _

/-- The graded Proposition 3.4 recurrence therefore holds almost
everywhere in the two external variables on every continuous noise
sample. -/
theorem ae_ae_gradedParametrix_succ_eq_noise_sub_counterterms
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      gradedParametrix M ρ lam ε (n + 1) x y ω =
        gradedParametrixNoiseSource
            M ρ lam ε n x y ω -
          gradedOrderCountertermSum
            M ρ lam ε n x y ω := by
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ k : Fin (n + 1),
          ∀ c : Composition (n - k.val),
            ∀ᵐ y ∂paperMeasure,
              RenormWordIntegrable M ρ lam ε
                ((k.val + 1) :: c.blocks) x y ω := by
    exact Filter.eventually_all.2 fun k =>
      Filter.eventually_all.2 fun c =>
        ae_ae_renormWordIntegrable
          M ρ lam ε ω hξ
            ((k.val + 1) :: c.blocks)
  filter_upwards [hallX] with x hx
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ k : Fin (n + 1),
          ∀ c : Composition (n - k.val),
            RenormWordIntegrable M ρ lam ε
              ((k.val + 1) :: c.blocks) x y ω := by
    exact Filter.eventually_all.2 fun k =>
      Filter.eventually_all.2 fun c =>
        hx k c
  filter_upwards [hallY] with y hy
  exact
    gradedParametrix_succ_eq_noise_sub_counterterms
      M ρ lam ε n x y ω hy

end PartialPairing

end

end Anderson4D
