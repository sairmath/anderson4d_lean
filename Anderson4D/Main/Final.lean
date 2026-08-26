import Anderson4D.DetParametrix.Paper42_Moment.R324PaperWholeSeriesHighProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperFullFullZeroShiftProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointProducer
import Anderson4D.Main.LawCorollary

/-!
# The conditional main theorem

This file supplies the closed paper-order estimates from Section 4.2 and
assembles the conditional theorem. The Gabriel--Rosati input remains an
explicit premise inside `MainConditional`; no unconditional theorem is
declared.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter Set

/-- **P-3.5b-det / paper (3.24), closed.**  The deterministic pairing sum
obeys the paper's second-moment bound, including all three Fourier decay
factors, with constants depending only on the cutoff. -/
theorem deterministic_second_moment_bound (rho : SmoothCutoff) :
    exists outerC powerC : Real, 0 < outerC /\ 0 < powerC /\
      forall lam : Real, 0 < lam ->
        ∀ᶠ epsilon : Real in nhdsWithin 0 (Set.Ioi 0),
          forall m, 1 <= m -> m <= truncOrder epsilon ->
            forall alpha beta : Z4,
              norm (deterministicMomentPairingSum
                rho lam epsilon m alpha beta) <=
                paperDeterministicMomentRHS
                  outerC powerC lam epsilon m alpha beta :=
  r324PaperScale_hdet_of_exists_paperEndpointCases_and_highWholeSeries rho
    (R324WithinHalfResidualPrefix.exists_r324PaperResidualEndpointWeightedMajorantBound rho)
    (fun hsupport =>
      exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound
        rho hsupport)
    (rho.exists_r324PaperHighWholeSeriesWeightedMajorantBound)

/-- **Conditional Deng--Shen Theorem 1.1.**  For every noise model and
cutoff, the uniform Gabriel--Rosati input implies the finite-family
Fourier-mode characteristic-function statement `MainStatement`. -/
theorem main_conditional (M : NoiseModel) (rho : SmoothCutoff) :
    MainConditional M rho :=
  mainConditional_of_exists_paperEndpointCases_and_highWholeSeries
    (R324WithinHalfResidualPrefix.exists_r324PaperResidualEndpointWeightedMajorantBound rho)
    (fun hsupport =>
      exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound
        rho hsupport)
    (rho.exists_r324PaperHighWholeSeriesWeightedMajorantBound)

/-- Conditional Deng--Shen Theorem 1.1 in the advertised finite-family
convergence-in-distribution form.  Proposition 3.6 remains the sole explicit
external hypothesis. -/
theorem main_conditional_law (M : NoiseModel) (rho : SmoothCutoff) :
    Prop36Family M rho -> MainLawStatement M rho :=
  mainConditionalLaw_of_mainConditional M rho (main_conditional M rho)

end

end Anderson4D
