import Mathlib

/-!
# The torus model, symmetry class, and cutoff (paper §1.1, Def. 2.1)

Paper: I-torus — the torus model and the normalization ledger

Stable torus and cutoff definitions fixed by the normalization design; see
`docs/DESIGN.md` §5.1 and the blueprint's Conventions section. Blueprint
nodes: D-E, parts of I-torus.

Normalization ledger (fixed here once):
* the torus is `T4 := Fin 4 → AddCircle (2π)`; the paper's reference
  measure is `paperMeasure = (2π)⁴ •` the product of probability Haar
  measures (mass `(2π)⁴` — Lebesgue on `[-π,π]⁴`);
* characters are `charT4 k x = ∏ i, e^{i k i · x i}`;
* the `ℝ⁴` Fourier transform used for the mollifier multiplier is
  `fourierR4 f ξ = ∫ x, e^{-i⟨x,ξ⟩} f x`; this convention makes
  periodization match the multiplier `fourierR4 ρ (ε • k)` by Poisson
  summation;
* the cutoff `ρ` lives on `ℝ⁴` with an explicit support radius; no
  radius-one rescaling is assumed at fixed `ε`.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate

/-- Spatial dimension. -/
abbrev dim : ℕ := 4

/-- The frequency lattice `ℤ⁴`. -/
abbrev Z4 := Fin dim → ℤ

/-- Euclidean-side space `ℝ⁴` (with the sup Pi norm; all constants are
norm-choice-dependent and named, DESIGN §5.4). -/
abbrev R4 := Fin dim → ℝ

/-- The spatial torus `𝕋⁴ = (ℝ/2πℤ)⁴`. -/
abbrev T4 := Fin dim → AddCircle (2 * Real.pi)

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Product character `e_k(x) = ∏ i, e^{i k_i x_i}` (paper's `e^{ik·x}`). -/
def charT4 (k : Z4) (x : T4) : ℂ := ∏ i, fourier (k i) (x i)

@[simp] lemma charT4_zero (x : T4) : charT4 0 x = 1 := by simp [charT4]

/-- The product of probability Haar measures on `T4` (mathlib-normalized
side of the measure dictionary). -/
def haarT4 : Measure T4 := Measure.pi fun _ => AddCircle.haarAddCircle

instance : IsProbabilityMeasure haarT4 := by
  unfold haarT4; infer_instance

/-- The paper's reference measure on `𝕋⁴`: total mass `(2π)⁴`
(Lebesgue on `[-π,π]⁴`). -/
def paperMeasure : Measure T4 :=
  (ENNReal.ofReal ((2 * Real.pi) ^ (dim : ℕ))) • haarT4

/-- The `ℝ⁴` Fourier transform convention used for mollifier multipliers:
`(fourierR4 f) ξ = ∫ x, e^{-i⟨x,ξ⟩} f x dx` with the plain bilinear
pairing `⟨x,ξ⟩ = ∑ i, x i * ξ i` and Lebesgue measure. -/
def fourierR4 (f : R4 → ℝ) (ξ : R4) : ℂ :=
  ∫ x : R4, Complex.exp (-Complex.I * (∑ i, x i * ξ i)) * (f x : ℂ)

/-- The hyperoctahedral symmetry class `𝓔` for functions on `ℝ⁴`
(paper Def. 2.1, single-slot `B₄` reading): invariance under coordinate
permutations and per-coordinate sign flips. -/
structure MemEClassR4 (f : R4 → ℝ) : Prop where
  perm_invariant : ∀ (σ : Equiv.Perm (Fin dim)) (x : R4), f (x ∘ σ) = f x
  even_coord : ∀ (i : Fin dim) (x : R4), f (Function.update x i (-(x i))) = f x

/-- The symmetry class `𝓔` on the torus (same `B₄` action, descended). -/
structure MemEClassT4 (f : T4 → ℝ) : Prop where
  perm_invariant : ∀ (σ : Equiv.Perm (Fin dim)) (x : T4), f (x ∘ σ) = f x
  even_coord : ∀ (i : Fin dim) (x : T4), f (Function.update x i (-(x i))) = f x

/-- Negate exactly the torus coordinates belonging to `s`. -/
def flipT4Coords (s : Finset (Fin dim)) (x : T4) : T4 :=
  fun i => if i ∈ s then -(x i) else x i

theorem flipT4Coords_insert
    (s : Finset (Fin dim)) (i : Fin dim) (hi : i ∉ s)
    (x : T4) :
    flipT4Coords (insert i s) x =
      Function.update (flipT4Coords s x) i
        (-(flipT4Coords s x i)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipT4Coords, hi]
  · simp [flipT4Coords, hji]

/-- Membership in `𝓔` gives invariance under any simultaneous collection
of coordinate sign flips. -/
theorem MemEClassT4.flipT4Coords_invariant
    {f : T4 → ℝ} (hf : MemEClassT4 f)
    (s : Finset (Fin dim)) (x : T4) :
    f (flipT4Coords s x) = f x := by
  induction s using Finset.induction with
  | empty =>
      have harg : flipT4Coords ∅ x = x := by
        funext i
        simp [flipT4Coords]
      rw [harg]
  | @insert i s hi ih =>
      rw [flipT4Coords_insert s i hi]
      exact (hf.even_coord i (flipT4Coords s x)).trans ih

/-- Slotwise evenness implies invariance under simultaneous negation of
all four coordinates. -/
theorem MemEClassT4.neg_invariant
    {f : T4 → ℝ} (hf : MemEClassT4 f) (x : T4) :
    f (-x) = f x := by
  have h := hf.flipT4Coords_invariant Finset.univ x
  have harg : flipT4Coords Finset.univ x = -x := by
    funext i
    simp [flipT4Coords]
  rw [harg] at h
  exact h

/-- The mollifier class of the paper's §1.1 (blueprint Conventions item 3):
smooth, nonnegative, compactly supported with an **explicit** support
radius, in the class `𝓔`, integral one. Smoothness is recorded per finite
order (robust against smoothness-exponent API differences). -/
structure SmoothCutoff where
  toFun : R4 → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  smooth : ∀ n : ℕ, ContDiff ℝ n toFun
  nonneg : ∀ x, 0 ≤ toFun x
  support_subset : Function.support toFun ⊆ Metric.ball 0 radius
  memE : MemEClassR4 toFun
  integral_one : ∫ x, toFun x = 1

instance : CoeFun SmoothCutoff (fun _ => R4 → ℝ) := ⟨SmoothCutoff.toFun⟩

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- Parabolic rescaling `ρ_ε = ε⁻⁴ ρ(·/ε)` on `ℝ⁴` (paper §1.1). -/
def rescale (ε : ℝ) (x : R4) : ℝ := ε⁻¹ ^ (dim : ℕ) * ρ (ε⁻¹ • x)

/-- The paper's `η = ρ * ρ` (convolution on `ℝ⁴`), entering the noise
covariance `E[ξ_ε(x)ξ_ε(y)] = η_ε(x-y)` (paper (2.3)). -/
def eta (x : R4) : ℝ := ∫ y : R4, ρ y * ρ (x - y)

/-- The Fourier multiplier symbol of the mollifier at scale `ε`:
`ρ̂(εk)`, matching periodized convolution by Poisson summation. -/
def symbol (ε : ℝ) (k : Z4) : ℂ := fourierR4 ρ (fun i => ε * (k i : ℝ))

end SmoothCutoff

/-- The coupling constant `λ_ε = λ / √|log ε|` (paper (1.1)); junk for
`ε ∉ (0,1)` per DESIGN §5.7 (the theorem hypotheses exclude it). -/
def lamEps (lam ε : ℝ) : ℝ := lam / Real.sqrt |Real.log ε|

/-- The truncation order `A = ⌊|log ε|⌋` (paper (3.11)). -/
def truncOrder (ε : ℝ) : ℕ := ⌊|Real.log ε|⌋₊

end

end Anderson4D
