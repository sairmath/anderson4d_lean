import Anderson4D.Continuum.Basic

/-!
# The torus Green's function via the heat-kernel representation

Paper: I-green — Green's function via the Bessel/heat-kernel time integral

For blueprint node I-green, `G = (1-Δ)⁻¹`'s kernel is
**defined** by the Bessel-potential time integral of the periodized
Gaussian — a plain Fourier `tsum` is ill-defined
(`⟨k⟩⁻² ∉ ℓ¹ ∪ ℓ²` over `ℤ⁴`, and `G ∉ L²(𝕋⁴)`). The Fourier
coefficient identity `Ĝ(k) = ⟨k⟩⁻²` is proved separately and is not the definition.

All definitions are junk-totalized (DESIGN §5.7): `tsum`/`∫` default to
`0` off summability, and the analytic estimates carry the hypotheses that
exclude the junk branches.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Canonical componentwise lift `𝕋⁴ → ℝ⁴` with values in `[-π, π)`. -/
def torusLift (z : T4) : R4 := fun i =>
  ((AddCircle.equivIco (2 * Real.pi) (-Real.pi)) (z i) : ℝ)

/-- Squared Euclidean distance from the lifted point to the lattice point
`2π k` (the summand geometry of the periodized Gaussian). -/
def latticeDistSq (z : T4) (k : Z4) : ℝ :=
  ∑ i, (torusLift z i + 2 * Real.pi * (k i : ℝ)) ^ 2

/-- Periodized Gaussian heat kernel on the torus:
`Θ(t,z) = ∑_{k ∈ ℤ⁴} (4πt)⁻² e^{-|z̃ + 2πk|²/(4t)}` where `z̃` is the
canonical lift. Rapidly convergent for every `t > 0`; positive; in `𝓔`
These properties are proved in `GreenBounds`. -/
def heatKernelT4 (t : ℝ) (z : T4) : ℝ :=
  ∑' k : Z4, (4 * Real.pi * t) ^ (-2 : ℤ) * Real.exp (-latticeDistSq z k / (4 * t))

/-- The Green's function of `1 - Δ` on `𝕋⁴`: the Bessel-potential time
integral `G(z) = ∫_0^∞ e^{-t} Θ(t,z) dt` (paper (1.2)'s free Green's
function; blueprint node I-green). -/
def greenFn (z : T4) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * heatKernelT4 t z

/-- The two-variable Green's kernel `G(x,y) = G(x - y)`. -/
def greenKernel (x y : T4) : ℝ := greenFn (x - y)

/-- The paper's four-point kernel
`H(x₁,y₁,x₂,y₂) = ∫ G(x₁-z)G(y₁-z)G(x₂-z)G(y₂-z) dz` ((3.25); the
covariance kernel of the limit field, blueprint node D-limit). Integral
against `paperMeasure` per the normalization ledger. -/
def fourPointH (x₁ y₁ x₂ y₂ : T4) : ℝ :=
  ∫ z, greenFn (x₁ - z) * greenFn (y₁ - z) * greenFn (x₂ - z) *
    greenFn (y₂ - z) ∂paperMeasure

end

end Anderson4D
