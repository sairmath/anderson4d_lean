import Anderson4D.Continuum.CovariancePeriodizationDerivativeClosure
import Anderson4D.Continuum.PeriodicFourierIBPIteration

/-!
# Periodicity supplies the endpoint jets for Fourier integration by parts

The iterated derivative of a translated function is the corresponding
translate of its iterated derivative.  Hence a literal `2π`-periodicity
identity supplies every endpoint-jet equality required by the repeated
integration-by-parts theorem.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- A literal `2π`-periodicity identity supplies all endpoint jets on
`[-π, π]`. -/
theorem negPiPiPeriodicJets_of_two_pi_periodic
    {f : ℝ → ℂ}
    (hperiod : ∀ t : ℝ,
      f (t + 2 * Real.pi) = f t)
    (r : ℕ) :
    NegPiPiPeriodicJets f r := by
  intro j hj
  have hfun :
      (fun t : ℝ => f (t + 2 * Real.pi)) = f :=
    funext hperiod
  have hderiv :=
    congrArg
      (fun g : ℝ → ℂ =>
        iteratedDeriv j g (-Real.pi)) hfun
  rw [iteratedDeriv_comp_add_const] at hderiv
  convert hderiv using 1
  ring_nf

namespace SmoothCutoff

/-- The coordinate-line covariance periodization has all endpoint jets
needed for eight periodic integrations by parts. -/
theorem negPiPiPeriodicJets_etaPeriodizationR4_coordLine
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4)
    (i : Fin dim) (r : ℕ) :
    NegPiPiPeriodicJets
      (fun t =>
        (ρ.etaPeriodizationR4 ε
          (Function.update x i t) : ℂ)) r := by
  apply negPiPiPeriodicJets_of_two_pi_periodic
  intro t
  exact congrArg Complex.ofReal
    (ρ.etaPeriodizationR4_update_add_two_pi
      ε x i t)

end SmoothCutoff

end

end Anderson4D
