import Anderson4D.Continuum.GreenFunction

/-!
# Fourier coefficients of the four-point Green kernel

This file fixes the deterministic coefficient used in Proposition 3.6 and
the limiting Gaussian law.  It belongs to the continuum layer: no random
parametrix or external probabilistic input is needed to state it.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- **Mode coefficients of the four-point kernel `H`** (paper (3.25)):
the pairing of `fourPointH` with characters in all four external variables,
against `paperMeasure` in each.  The iterated Bochner integrals use mathlib's
standard junk value outside the integrable regime; downstream continuum
lemmas prove the required integrability and compute the coefficient. -/
def fourPointHCoeff (α₁ β₁ α₂ β₂ : Z4) : ℂ :=
  ∫ x₁, ∫ y₁, ∫ x₂, ∫ y₂,
    charT4 α₁ x₁ * charT4 β₁ y₁ * charT4 α₂ x₂ * charT4 β₂ y₂ *
      (fourPointH x₁ y₁ x₂ y₂ : ℂ)
    ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure

end

end Anderson4D
