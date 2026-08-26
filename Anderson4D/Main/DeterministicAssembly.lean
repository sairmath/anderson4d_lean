import Anderson4D.Main.GoodEventConstruction
import Anderson4D.Main.CouplingThreshold

/-!
# Final assembly from deterministic estimates

This module removes the abstract `MainGoodEventInput` interface.  Given the
moving deterministic P-3.5b estimate and the R-322 counterterm estimate, the
measurable event is constructed internally and the characteristic-function
argument is completed at one common coupling threshold.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- Complete quantifier assembly from the second-moment estimate and the
two deterministic inputs to the one-sided operator good event. -/
theorem mainConditional_of_secondMoment_and_deterministic_bounds
    {M : NoiseModel} {ρ : SmoothCutoff}
    {K secondPower outerConstant goodPower Crenorm : ℝ}
    (hK : 0 ≤ K)
    (hsecondPower : 0 < secondPower)
    (houter : 0 ≤ outerConstant)
    (hgoodPower : 0 < goodPower)
    (hCrenorm : 0 < Crenorm)
    (hsecond :
      MainSecondMomentInput M ρ K secondPower)
    (hdet :
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
            ‖deterministicMomentPairingSum
                ρ lam ε m α β‖ ≤
              deterministicMomentRHS
                outerConstant goodPower lam ε m α β)
    (hcounter :
      ∀ lam : ℝ, 0 < lam →
        ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ∀ q ∈ Finset.Icc 1 (truncOrder ε),
            |renormC2q ρ lam ε q| ≤
              ε⁻¹ ^ (2 : ℕ) / |Real.log ε| *
                (Crenorm * lam) ^ (2 * q)) :
    MainConditional M ρ := by
  intro hfamily
  refine
    ⟨hfamily.mainCouplingThreshold
        secondPower goodPower Crenorm,
      hfamily.mainCouplingThreshold_pos
        hsecondPower hgoodPower hCrenorm, ?_⟩
  intro lam hlam s modes c
  have hspec :=
    hfamily.mainCouplingThreshold_spec
      hsecondPower hgoodPower hCrenorm hlam
  have hlamBase : lam ∈ Ioo 0 hfamily.couplingThreshold :=
    hspec.1
  have hsecondRatioNonneg :
      0 ≤ secondPower * lam :=
    mul_nonneg hsecondPower.le hlam.1.le
  let hP36 : Prop36 M ρ lam :=
    hfamily.prop36 hlam.1
  obtain ⟨data⟩ :=
    MainGoodEvent.nonempty_fixedModeGoodEventData_of_deterministic_bounds
      houter hgoodPower.le hCrenorm.le
      hlam.1 hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2
      (hdet lam hlam.1) (hcounter lam hlam.1)
      s modes c
  have hIoi :=
    hP36.tendsto_fullResolventChar_of_second_moment_and_goodEvent
      hlam.1
      (hfamily.boundConstant_mul_lt_one hlamBase)
      (hfamily.sq_lt_two_mul_pi_sq hlamBase)
      modes c K (secondPower * lam)
      hK hsecondRatioNonneg hspec.2.1
      (hsecond lam hlam.1 s modes)
      data.good data.good_measurable data.error
      data.error_nonneg data.error_tendsto
      data.bad_probability_tendsto data.close_on_good
  have hIoo :=
    tendsto_fullResolventChar_on_Ioo_of_Ioi
      ρ lam modes c hIoi
  have hsamplewise :
      Tendsto
        (fun ε => ∫ ω,
          Complex.exp
            (Complex.I *
              (fredholmFiniteModeReal
                M ρ lam ε s modes c ω : ℂ)))
        (nhdsWithin 0 (Ioo (0 : ℝ) 1))
        (𝓝 (((Real.exp
          (-(limitVar lam modes c) / 2) : ℝ) : ℂ))) := by
    refine hIoo.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact
      integral_exp_I_measurableFredholm_eq_fredholm
        M ρ lam hε.1 s modes c
  exact hsamplewise

end

end Anderson4D
