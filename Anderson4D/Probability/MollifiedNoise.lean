import Anderson4D.Continuum.CutoffFourier
import Anderson4D.Continuum.TorusFourier
import Anderson4D.Probability.NoiseProducts

/-!
# Finite Fourier approximations of the mollified noise

Before passing to the infinite random Fourier series, all covariance and
moment manipulations are finite.  This file records those exact identities
with the project's cutoff and character normalizations.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory ComplexConjugate
open scoped ENNReal BigOperators

namespace NoiseModel

variable (M : NoiseModel)

/-- A finite mode set closed under the reality involution `k ↦ -k`. -/
def NegClosedModes (s : Finset Z4) : Prop :=
  ∀ k ∈ s, -k ∈ s

/-- Negation permutes a finite negation-closed mode set. -/
def negClosedModesEquiv (s : Finset Z4) (hs : NegClosedModes s) :
    ↥s ≃ ↥s where
  toFun k := ⟨-k.1, hs k.1 k.2⟩
  invFun k := ⟨-k.1, hs k.1 k.2⟩
  left_inv k := by ext; simp
  right_inv k := by ext; simp

theorem sum_neg_eq_sum_of_negClosedModes
    (s : Finset Z4) (hs : NegClosedModes s) (f : Z4 → ℂ) :
    (∑ k ∈ s, f (-k)) = ∑ k ∈ s, f k := by
  apply Finset.sum_equiv (Equiv.neg Z4)
  · intro k
    constructor
    · exact hs k
    · intro hk
      simpa using hs (-k) hk
  · intro k hk
    rfl

/-- Deterministic coefficient multiplying the white-noise mode `g k` at
the spatial point `x`. -/
def mollifiedModeCoeff
    (ρ : SmoothCutoff) (ε : ℝ) (x : T4) (k : Z4) : ℂ :=
  (whiteNoiseFourierScale : ℂ) * ρ.symbol ε k * charT4 k x

/-- Finite complex Fourier approximation to the mollified noise. -/
def xiEpsFiniteC
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4)
    (ω : M.Ω) (x : T4) : ℂ :=
  M.finiteNoiseCombination s (mollifiedModeCoeff ρ ε x) ω

theorem measurable_xiEpsFiniteC
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4) (x : T4) :
    Measurable (fun ω => M.xiEpsFiniteC ρ ε s ω x) := by
  unfold xiEpsFiniteC finiteNoiseCombination mollifiedModeCoeff
  apply Finset.measurable_sum
  intro k hk
  exact measurable_const.mul (M.measurable_g k)

/-- Every finite Fourier approximation has all finite moments. -/
theorem memLp_xiEpsFiniteC
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4) (x : T4)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => M.xiEpsFiniteC ρ ε s ω x) p
      (volume : Measure M.Ω) := by
  unfold xiEpsFiniteC finiteNoiseCombination
  apply memLp_finsetSum
  intro k hk
  exact (M.memLp_g k p hp).const_mul (mollifiedModeCoeff ρ ε x k)

/-- A negation-closed truncation is pointwise real. -/
theorem conj_xiEpsFiniteC_eq
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4)
    (hs : NegClosedModes s) (ω : M.Ω) (x : T4) :
    conj (M.xiEpsFiniteC ρ ε s ω x) =
      M.xiEpsFiniteC ρ ε s ω x := by
  unfold xiEpsFiniteC finiteNoiseCombination
  rw [map_sum]
  calc
    (∑ k ∈ s, conj (mollifiedModeCoeff ρ ε x k * M.g k ω)) =
        ∑ k ∈ s,
          mollifiedModeCoeff ρ ε x (-k) * M.g (-k) ω := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        conj (mollifiedModeCoeff ρ ε x k * M.g k ω) =
            conj (mollifiedModeCoeff ρ ε x k) * conj (M.g k ω) := by
          rw [map_mul]
        _ = mollifiedModeCoeff ρ ε x (-k) * M.g (-k) ω := by
          rw [← M.reality]
          congr 1
          unfold mollifiedModeCoeff
          rw [map_mul, map_mul, ← ρ.symbol_neg, ← charT4_neg]
          rw [Complex.conj_ofReal]
    _ = ∑ k ∈ s, mollifiedModeCoeff ρ ε x k * M.g k ω := by
      exact sum_neg_eq_sum_of_negClosedModes s hs
        (fun k => mollifiedModeCoeff ρ ε x k * M.g k ω)

/-- The imaginary part of a negation-closed truncation vanishes. -/
theorem xiEpsFiniteC_im_eq_zero
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4)
    (hs : NegClosedModes s) (ω : M.Ω) (x : T4) :
    (M.xiEpsFiniteC ρ ε s ω x).im = 0 := by
  have h := congrArg Complex.im
    (M.conj_xiEpsFiniteC_eq ρ ε s hs ω x)
  simp only [Complex.conj_im] at h
  linarith

/-- The exact finite covariance, with no symmetry assumption on either
mode set. -/
theorem integral_xiEpsFiniteC_mul
    (ρ : SmoothCutoff) (ε : ℝ) (s t : Finset Z4) (x y : T4) :
    ∫ ω, M.xiEpsFiniteC ρ ε s ω x *
        M.xiEpsFiniteC ρ ε t ω y =
      ∑ k ∈ s, ∑ l ∈ t,
        mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y l *
            (if k = -l then 1 else 0) := by
  exact M.integral_finiteNoiseCombination_mul s t
    (mollifiedModeCoeff ρ ε x) (mollifiedModeCoeff ρ ε y)

/-- On a negation-closed truncation, the two-field covariance collapses
from a double Kronecker sum to one sum over paired modes. -/
theorem integral_xiEpsFiniteC_mul_of_negClosedModes
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4)
    (hs : NegClosedModes s) (x y : T4) :
    ∫ ω, M.xiEpsFiniteC ρ ε s ω x *
        M.xiEpsFiniteC ρ ε s ω y =
      ∑ k ∈ s,
        mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y (-k) := by
  rw [M.integral_xiEpsFiniteC_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hmem : -k ∈ s := hs k hk
  calc
    (∑ l ∈ s,
        mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y l *
            (if k = -l then 1 else 0)) =
        ∑ l ∈ s,
          if l = -k then
            mollifiedModeCoeff ρ ε x k *
              mollifiedModeCoeff ρ ε y l
          else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      have hiff : k = -l ↔ l = -k := by
        constructor
        · intro h
          have hn := congrArg Neg.neg h
          simpa using hn.symm
        · intro h
          have hn := congrArg Neg.neg h
          simpa using hn.symm
      rw [if_congr hiff rfl rfl]
      split_ifs <;> simp
    _ = mollifiedModeCoeff ρ ε x k *
          mollifiedModeCoeff ρ ε y (-k) := by
      simp [hmem]

/-- The exact finite covariance against a conjugated field. -/
theorem integral_xiEpsFiniteC_mul_conj
    (ρ : SmoothCutoff) (ε : ℝ) (s t : Finset Z4) (x y : T4) :
    ∫ ω, M.xiEpsFiniteC ρ ε s ω x *
        conj (M.xiEpsFiniteC ρ ε t ω y) =
      ∑ k ∈ s, ∑ l ∈ t,
        mollifiedModeCoeff ρ ε x k *
          conj (mollifiedModeCoeff ρ ε y l) *
            (if k = l then 1 else 0) := by
  exact M.integral_finiteNoiseCombination_mul_conj s t
    (mollifiedModeCoeff ρ ε x) (mollifiedModeCoeff ρ ε y)

/-- Real part of the finite Fourier approximation, matching the codomain
of the totalized infinite field `xiEps`. -/
def xiEpsFinite
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4)
    (ω : M.Ω) (x : T4) : ℝ :=
  (M.xiEpsFiniteC ρ ε s ω x).re

theorem measurable_xiEpsFinite
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4) (x : T4) :
    Measurable (fun ω => M.xiEpsFinite ρ ε s ω x) := by
  unfold xiEpsFinite
  have h := M.measurable_xiEpsFiniteC ρ ε s x
  fun_prop

theorem memLp_xiEpsFinite
    (ρ : SmoothCutoff) (ε : ℝ) (s : Finset Z4) (x : T4)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => M.xiEpsFinite ρ ε s ω x) p
      (volume : Measure M.Ω) := by
  exact
    (M.memLp_xiEpsFiniteC ρ ε s x p hp).continuousLinearMap_comp
      Complex.reCLM

end NoiseModel

end

end Anderson4D
