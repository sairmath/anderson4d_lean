import Anderson4D.Parametrix.OperatorBounds

/-!
# Second-moment good events for bounded random resolvents

This file supplies the probability-theoretic shell of the paper's
Chebyshev/Neumann argument.  The analytic random-kernel estimate only has
to bound `E ‖K‖²`; Markov's inequality then gives a high-probability
half-ball on which the inverse and its deterministic norm bounds exist.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

variable {Ω H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The event that a random bounded operator exceeds a norm threshold. -/
def operatorBadEvent (K : Ω → H →L[ℂ] H) (r : ℝ) : Set Ω :=
  {ω | r ≤ ‖K ω‖}

/-- Markov's inequality applied to the squared operator norm. -/
theorem sq_mul_measureReal_operatorBadEvent_le
    [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → H →L[ℂ] H) (r : ℝ)
    (hr : 0 ≤ r)
    (hint : Integrable (fun ω => ‖K ω‖ ^ 2) μ) :
    r ^ 2 * μ.real (operatorBadEvent K r) ≤
      ∫ ω, ‖K ω‖ ^ 2 ∂μ := by
  have hmark :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := fun ω => ‖K ω‖ ^ 2)
      (ae_of_all μ fun ω => sq_nonneg ‖K ω‖)
      hint (r ^ 2)
  have hevent :
      {ω | r ^ 2 ≤ ‖K ω‖ ^ 2} = operatorBadEvent K r := by
    ext ω
    simp only [Set.mem_setOf_eq, operatorBadEvent]
    constructor
    · intro h
      nlinarith [norm_nonneg (K ω)]
    · intro h
      nlinarith [norm_nonneg (K ω)]
  rwa [hevent] at hmark

/-- At threshold `1/2`, a second-moment bound `δ` gives bad-event
probability at most `4δ`. -/
theorem measureReal_operatorBadEvent_half_le
    [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → H →L[ℂ] H) (δ : ℝ)
    (hint : Integrable (fun ω => ‖K ω‖ ^ 2) μ)
    (hsecond : (∫ ω, ‖K ω‖ ^ 2 ∂μ) ≤ δ) :
    μ.real (operatorBadEvent K (1 / 2)) ≤ 4 * δ := by
  have hmark :=
    sq_mul_measureReal_operatorBadEvent_le μ K (1 / 2)
      (by norm_num) hint
  have hnonneg : 0 ≤ μ.real (operatorBadEvent K (1 / 2)) :=
    measureReal_nonneg
  nlinarith

/-- The norm-small event used to construct the random inverse. -/
def resolventGoodEvent
    (G : H →L[ℂ] H) (M : Ω → H →L[ℂ] H) : Set Ω :=
  {ω | ‖Kop G (M ω)‖ < 1 / 2}

theorem compl_resolventGoodEvent
    (G : H →L[ℂ] H) (M : Ω → H →L[ℂ] H) :
    (resolventGoodEvent G M)ᶜ =
      operatorBadEvent (fun ω => Kop G (M ω)) (1 / 2) := by
  ext ω
  simp [resolventGoodEvent, operatorBadEvent, not_lt]

/-- Every sample in the good event has an inverse. -/
theorem lopInvertible_on_resolventGoodEvent
    [CompleteSpace H]
    (G : H →L[ℂ] H) (M : Ω → H →L[ℂ] H)
    {ω : Ω} (hω : ω ∈ resolventGoodEvent G M) :
    LopInvertible G (M ω) := by
  apply lopInvertible_of_norm_Kop_lt_one
  exact hω.trans (by norm_num)

/-- The recentered inverse obeys the uniform half-ball estimate on the
good event. -/
theorem norm_inverseGreen_sub_G_on_resolventGoodEvent
    [CompleteSpace H] [Nontrivial H]
    (G : H →L[ℂ] H) (M : Ω → H →L[ℂ] H)
    {ω : Ω} (hω : ω ∈ resolventGoodEvent G M) :
    ‖inverseGreen G (M ω)
        (lopInvertible_of_norm_Kop_lt_one G (M ω)
          (hω.trans (by norm_num))) - G‖ ≤
      2 * (‖G‖ * ‖M ω‖ * ‖G‖) := by
  exact norm_inverseGreen_sub_G_le_two G (M ω) hω.le

/-- A second-moment estimate for the random `K` controls the complement
of the resolvent good event. -/
theorem measureReal_compl_resolventGoodEvent_le
    [MeasurableSpace Ω]
    (μ : Measure Ω) (G : H →L[ℂ] H) (M : Ω → H →L[ℂ] H) (δ : ℝ)
    (hint : Integrable (fun ω => ‖Kop G (M ω)‖ ^ 2) μ)
    (hsecond : (∫ ω, ‖Kop G (M ω)‖ ^ 2 ∂μ) ≤ δ) :
    μ.real (resolventGoodEvent G M)ᶜ ≤ 4 * δ := by
  rw [compl_resolventGoodEvent]
  exact measureReal_operatorBadEvent_half_le μ
    (fun ω => Kop G (M ω)) δ hint hsecond

end

end Anderson4D
