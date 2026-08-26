import Anderson4D.DetParametrix.Paper42_Moment.R324DifferenceRetainingCore

/-!
# The general-order Green-chain Parseval collapse

The direct physical→lattice collapse lemmas are specialized to
`m ≤ 2` (`integral_integral_greenFn_etaPair_eq_tsum`,
`integral_prod_greenFn_mul_tsum_crossModes`): the internal coordinates
are peeled by hand, one named lemma per coordinate.  This file replaces
that with a *recursion on the chain length*.

The object is the half chain of a pure-cross entity after the cross
covariances have been Fourier-expanded: each internal vertex `uⱼ`
carries one character `e_{kⱼ}` (the mode of the covariance leg attached
there) and each internal edge carries one Green kernel.  Integrating the
innermost coordinate is exactly the proved one-variable evaluation
`integral_charT4_mul_greenFn_shift`,

`∫ e_b(u) · G(z-u) du = e_b(z) · ⟨b⟩⁻²`,

so the character *migrates* to the next vertex and multiplies the
character already there.  Hence after `n` steps the surviving character
is `e_{Sₙ}` with `Sₙ = k₀+…+k_{n-1}` the partial sum, and the harvested
propagators are exactly the brackets of the partial sums:

`r324Col_chain_eq : r324ColChain k n z = ⟨S₁⟩⁻²⋯⟨Sₙ⟩⁻² · e_{Sₙ}(z)`.

Closing the chain against the free external endpoint turns the last
character into the momentum-conservation Kronecker delta
(`r324Col_chain_closed`), which is the vertex constraint the `m ≤ 2`
files produced by hand.

Nothing here is `m`-specific: `n` is arbitrary and the proof is a
one-step induction.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Partial sums and their propagators -/

/-- The `n`-th partial sum `Sₙ = k₀ + … + k_{n-1}` of a momentum
sequence.  These are the keys that survive at each vertex of a Green
chain. -/
def r324ColPartial (k : ℕ → Z4) (n : ℕ) : Z4 :=
  ∑ j ∈ Finset.range n, k j

@[simp] theorem r324ColPartial_zero (k : ℕ → Z4) :
    r324ColPartial k 0 = 0 := by
  simp [r324ColPartial]

theorem r324ColPartial_succ (k : ℕ → Z4) (n : ℕ) :
    r324ColPartial k (n + 1) = r324ColPartial k n + k n := by
  simp [r324ColPartial, Finset.sum_range_succ]

/-- The Japanese bracket `⟨b⟩⁻² = (1+|b|²)⁻¹` of the paper's Green
propagator: the exact Fourier multiplier of `greenFn`. -/
def r324ColBrk (b : Z4) : ℝ := (1 + paperModeNormSq b)⁻¹

theorem r324ColBrk_nonneg (b : Z4) : 0 ≤ r324ColBrk b := by
  unfold r324ColBrk paperModeNormSq
  positivity

theorem r324ColBrk_le_one (b : Z4) : r324ColBrk b ≤ 1 := by
  unfold r324ColBrk
  have h : (0 : ℝ) ≤ paperModeNormSq b := by
    unfold paperModeNormSq; positivity
  rw [inv_le_one_iff₀]
  right; linarith

/-- The propagator harvested by a chain of `n` internal edges: one
bracket per partial sum. -/
def r324ColProp (k : ℕ → Z4) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, r324ColBrk (r324ColPartial k (j + 1))

@[simp] theorem r324ColProp_zero (k : ℕ → Z4) :
    r324ColProp k 0 = 1 := by
  simp [r324ColProp]

theorem r324ColProp_succ (k : ℕ → Z4) (n : ℕ) :
    r324ColProp k (n + 1) =
      r324ColProp k n * r324ColBrk (r324ColPartial k (n + 1)) := by
  simp [r324ColProp, Finset.prod_range_succ]

theorem r324ColProp_nonneg (k : ℕ → Z4) (n : ℕ) :
    0 ≤ r324ColProp k n :=
  Finset.prod_nonneg fun _ _ => r324ColBrk_nonneg _

/-! ## The chain -/

/-- **The Green half chain against its vertex characters**, defined by
recursion on the number of internal coordinates.  `r324ColChain k n z`
is the `n`-fold iterated integral

`∫…∫ e_{k₀}(u₀) G(u₁-u₀) e_{k₁}(u₁) G(u₂-u₁) ⋯ e_{k_{n-1}}(u_{n-1})
   G(z-u_{n-1}) du₀⋯du_{n-1}`,

i.e. the chain running from the innermost vertex out to the free
terminal point `z`. -/
def r324ColChain (k : ℕ → Z4) : ℕ → T4 → ℂ
  | 0, _ => 1
  | (n + 1), z =>
      ∫ u : T4,
        r324ColChain k n u * charT4 (k n) u *
          ((greenFn (z - u) : ℝ) : ℂ) ∂paperMeasure

@[simp] theorem r324ColChain_zero (k : ℕ → Z4) (z : T4) :
    r324ColChain k 0 z = 1 := rfl

theorem r324ColChain_succ (k : ℕ → Z4) (n : ℕ) (z : T4) :
    r324ColChain k (n + 1) z =
      ∫ u : T4,
        r324ColChain k n u * charT4 (k n) u *
          ((greenFn (z - u) : ℝ) : ℂ) ∂paperMeasure := rfl

theorem r324Col_charT4_zero (z : T4) : charT4 (0 : Z4) z = 1 := by
  simp [charT4]

/-! ## The collapse -/

/-- **The general-order chain collapse.**  A Green chain of arbitrary
length integrated against one character per internal vertex collapses to
the product of the brackets of its *partial sums*, times the single
surviving character carrying the total momentum.

This is the statement that the proved `m ≤ 2` collapses hardcode.
The proof is a one-step induction on the chain length: the innermost
integral is `integral_charT4_mul_greenFn_shift`, which harvests one
bracket and migrates the character one vertex outwards, where
`charT4_add` merges it with the character already sitting there. -/
theorem r324Col_chain_eq (k : ℕ → Z4) :
    ∀ (n : ℕ) (z : T4),
      r324ColChain k n z =
        ((r324ColProp k n : ℝ) : ℂ) * charT4 (r324ColPartial k n) z := by
  intro n
  induction n with
  | zero =>
      intro z
      rw [r324ColChain_zero, r324ColProp_zero, r324ColPartial_zero,
        r324Col_charT4_zero]
      norm_num
  | succ n ih =>
      intro z
      rw [r324ColChain_succ]
      have hpt : ∀ u : T4,
          r324ColChain k n u * charT4 (k n) u *
              ((greenFn (z - u) : ℝ) : ℂ) =
            ((r324ColProp k n : ℝ) : ℂ) *
              (charT4 (r324ColPartial k (n + 1)) u *
                ((greenFn (z - u) : ℝ) : ℂ)) := by
        intro u
        rw [ih u, r324ColPartial_succ, charT4_add]
        ring
      simp only [hpt]
      rw [integral_const_mul]
      rw [integral_charT4_mul_greenFn_shift]
      rw [r324ColProp_succ, r324ColBrk]
      push_cast
      ring

/-! ## Closing the chain: momentum conservation at the free endpoint -/

theorem r324Col_integrable_charT4 (b : Z4) :
    Integrable (charT4 b) paperMeasure :=
  (continuous_charT4 b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The chain integrand is integrable in its terminal coordinate. -/
theorem r324Col_integrable_chain (k : ℕ → Z4) (n : ℕ) :
    Integrable (fun z : T4 => r324ColChain k n z) paperMeasure := by
  have hEq : (fun z : T4 => r324ColChain k n z) =
      fun z : T4 =>
        ((r324ColProp k n : ℝ) : ℂ) * charT4 (r324ColPartial k n) z := by
    funext z
    exact r324Col_chain_eq k n z
  rw [hEq]
  exact (r324Col_integrable_charT4 _).const_mul _

/-- **The closed chain: the vertex Kronecker delta.**  Integrating the
free terminal endpoint of a collapsed chain enforces total momentum
conservation `Sₙ = 0` and leaves the propagator product.  At `Sₙ = 0`
the last bracket is `1`, so the surviving weight is
`⟨S₁⟩⁻²⋯⟨S_{n-1}⟩⁻²`: one propagator per *internal* edge, exactly the
paper's count. -/
theorem r324Col_chain_closed (k : ℕ → Z4) (n : ℕ) :
    (∫ z : T4, r324ColChain k n z ∂paperMeasure) =
      if r324ColPartial k n = 0 then
        ((r324ColProp k n * (2 * Real.pi) ^ dim : ℝ) : ℂ)
      else 0 := by
  have hEq : (∫ z : T4, r324ColChain k n z ∂paperMeasure) =
      ∫ z : T4,
        ((r324ColProp k n : ℝ) : ℂ) * charT4 (r324ColPartial k n) z
          ∂paperMeasure :=
    integral_congr_ae
      (Filter.Eventually.of_forall fun z => r324Col_chain_eq k n z)
  rw [hEq, integral_const_mul, integral_charT4_paper]
  by_cases h : r324ColPartial k n = 0
  · rw [if_pos h, if_pos h]
    push_cast
    ring
  · rw [if_neg h, if_neg h, mul_zero]

end

end Anderson4D
