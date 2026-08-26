import Anderson4D.Main.Theorem
import Anderson4D.Main.GoodEventCharacteristic

/-!
# Final conditional-theorem assembly

This file records the exact interfaces still supplied by the
coefficient second-moment estimate and the operator good-event argument,
then performs all remaining quantifier, coupling-threshold, filter, and
characteristic-function bookkeeping for Theorem 1.1.

Neither interface assumes convergence in law or a characteristic-function
limit.  `MainSecondMomentInput` is precisely the squared geometric form of
paper (3.24), while `FixedModeGoodEventData` is the direct fixed-mode
replacement output of paper §3.4 Steps 1--2.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- Uniform squared geometric coefficient control in the form consumed by
the moving-truncation theorem.  The constants are selected before the
coupling and the finite family of Fourier modes. -/
def MainSecondMomentInput
    (M : NoiseModel) (ρ : SmoothCutoff)
    (K powerConstant : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    ∀ (s : ℕ) (modes : Fin s → Z4 × Z4),
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ∀ j : Fin s, ∀ n : ℕ, 1 ≤ n → n ≤ truncOrder ε →
          MemLp
            (pmCoeff M ρ lam ε n
              (modes j).1 (modes j).2)
            2 (volume : Measure M.Ω) ∧
          ∫ ω,
              ‖pmCoeff M ρ lam ε n
                (modes j).1 (modes j).2 ω‖ ^ 2 ≤
            (‖(lamEps lam ε : ℂ)‖ * K *
              (powerConstant * lam) ^ (n - 1)) ^ 2

/-- Fixed-mode output of the operator comparison on its measurable good
event.  It is intentionally quantitative and contains no limiting-law
statement. -/
structure FixedModeGoodEventData
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4)
    (c : Fin s → ℂ) where
  good : ℝ → Set M.Ω
  error : ℝ → ℝ
  good_measurable : ∀ ε, MeasurableSet (good ε)
  error_nonneg :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      0 ≤ error ε
  error_tendsto :
    Tendsto error
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (𝓝 0)
  bad_probability_tendsto :
    Tendsto
      (fun ε =>
        (volume : Measure M.Ω).real (good ε)ᶜ)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (𝓝 0)
  close_on_good :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
      ∀ ω ∈ good ε,
        ‖fullParametrixReal M ρ lam ε s modes c ω -
          fullResolventReal M ρ lam ε s modes c ω‖ ≤
        error ε

/-- Uniform availability of the fixed-mode good-event comparison. -/
def MainGoodEventInput
    (M : NoiseModel) (ρ : SmoothCutoff) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    ∀ (s : ℕ) (modes : Fin s → Z4 × Z4)
      (c : Fin s → ℂ),
      Nonempty (FixedModeGoodEventData M ρ lam s modes c)

/-- Complete quantifier assembly for the conditional main theorem.

Given the genuine upstream outputs of (3.24) and the operator good-event
comparison, the external Proposition 3.6 family implies the frozen main
statement.  The coupling threshold is the minimum of the independent
external and internal geometric thresholds. -/
theorem mainConditional_of_secondMoment_and_goodEvent
    {M : NoiseModel} {ρ : SmoothCutoff}
    {K powerConstant : ℝ}
    (hK : 0 ≤ K) (hpower : 0 < powerConstant)
    (hsecond :
      MainSecondMomentInput M ρ K powerConstant)
    (hgood : MainGoodEventInput M ρ) :
    MainConditional M ρ := by
  intro hfamily
  refine
    ⟨hfamily.couplingThresholdWith powerConstant,
      hfamily.couplingThresholdWith_pos hpower, ?_⟩
  intro lam hlam s modes c
  have hlamBase :
      lam ∈ Set.Ioo 0 hfamily.couplingThreshold :=
    hfamily.mem_couplingThreshold_of_mem_couplingThresholdWith
      hlam
  have hratioNonneg :
      0 ≤ powerConstant * lam :=
    mul_nonneg hpower.le hlam.1.le
  have hratioLt :
      powerConstant * lam < 1 :=
    hfamily.powerConstant_mul_lt_one hpower hlam
  let hP36 : Prop36 M ρ lam :=
    hfamily.prop36 hlam.1
  obtain ⟨data⟩ :=
    hgood lam hlam.1 s modes c
  have hIoi :=
    hP36.tendsto_fullResolventChar_of_second_moment_and_goodEvent
      hlam.1
      (hfamily.boundConstant_mul_lt_one hlamBase)
      (hfamily.sq_lt_two_mul_pi_sq hlamBase)
      modes c K (powerConstant * lam)
      hK hratioNonneg hratioLt
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
        (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
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
