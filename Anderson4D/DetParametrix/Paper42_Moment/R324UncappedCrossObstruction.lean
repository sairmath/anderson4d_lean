import Anderson4D.DetParametrix.Paper42_Moment.R324PermCrossMinorant

/-!
# Factorial obstruction to an uncapped injective cross bound

The uncapped `crossIntegral` hypothesis for the uniform-branch
closure `exists_momentRefinedIntegratedReductionOutputAt_of_crossIntegral_and_mixed`
demands, for a single `K = K(ρ)` and **every** order `m ≥ 3` and every
admissible scale,

`∫ (pure-cross fibre density) ≤ K^m |log ε|^{m-1}`.

This file proves that no such order-uniform estimate exists.  Retaining pairing
injectivity does not make the uniform branch valid: injectivity fixes the
fibre cardinality at exactly `m!`, and each of the `m!` bijection
entities carries at least one full covariance mass above the Green
floor,

`∫ ≥ g₀^{2m+2} · m! · (2π)^{4(m+4)}`   (`r324PermCross_integral_crossDensity_ge`),

an `ε`-uniform bound.  At the admissible scale `ε = e⁻¹` (where
`|log ε| = 1`) the demanded budget degenerates to `K^m`, and
`m! c^m > K^m` for large `m`.

The obstruction is the factorial fibre count itself, which the paper controls
because its expansion is truncated at `A = ⌊|log ε|⌋` orders
(`truncOrder`) and its §5 permutation-sum machinery is allowed
`(m!)^{1/2}`-type growth (cf. `permSumRHS`).  Any sound uniform-branch
interface must either cap the order against `|log ε|` or budget an
explicit factorial factor; `R324PermCrossOrderCappedCrossBound` records the
order-capped form.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Every permutation entity is a pure-cross entity. -/
theorem r324PermCross_permEntities_allCross (m : ℕ) :
    ∀ e ∈ r324LedgerThreePermEntities m,
      R324LedgerThreeAllCrossEntity e := by
  intro e he
  obtain ⟨π, -, rfl⟩ := Finset.mem_image.mp he
  exact ⟨rfl, rfl⟩

/-- Factorial growth defeats every geometric budget: given `c > 0` and
`0 < C₀`, for every `K ≥ 0` there are arbitrarily large `m` with
`K ^ m < C₀ * (m.factorial * c ^ m)`. -/
theorem r324PermCross_exists_factorial_beats_pow
    {c C₀ : ℝ} (hc : 0 < c) (hC₀ : 0 < C₀) (K : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧
      K ^ m < C₀ * ((m.factorial : ℝ) * c ^ m) := by
  have htend :
      Filter.Tendsto
        (fun n : ℕ => (K / c) ^ n / (n.factorial : ℝ))
        Filter.atTop (nhds 0) :=
    (Real.summable_pow_div_factorial (K / c)).tendsto_atTop_zero
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (K / c) ^ n / (n.factorial : ℝ) < C₀ :=
    htend.eventually_lt_const hC₀
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max M N, le_max_right M N, ?_⟩
  set m : ℕ := max M N
  have hm : (K / c) ^ m / (m.factorial : ℝ) < C₀ :=
    hM m (le_max_left M N)
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hKc : K ^ m = (K / c) ^ m * c ^ m := by
    rw [div_pow, div_mul_cancel₀]
    positivity
  rw [hKc]
  have hlt : (K / c) ^ m < C₀ * (m.factorial : ℝ) := by
    rw [div_lt_iff₀ hfac] at hm
    linarith
  have hcm : (0 : ℝ) < c ^ m := by positivity
  calc (K / c) ^ m * c ^ m <
      (C₀ * (m.factorial : ℝ)) * c ^ m :=
      mul_lt_mul_of_pos_right hlt hcm
    _ = C₀ * ((m.factorial : ℝ) * c ^ m) := by ring

/-- **No constant funds the uncapped injectivity-retaining cross bound.**  The
`crossIntegral` hypothesis of the auxiliary closure
`exists_momentRefinedIntegratedReductionOutputAt_of_crossIntegral_and_mixed`
has no witness: at the admissible scale `ε = e⁻¹` the full
permutation fibre carries `m!` unit covariance masses above the Green
floor, defeating `K^m |log ε|^{m-1}` at large `m`. -/
theorem r324PermCross_crossIntegral_no_constant (ρ : SmoothCutoff) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧
      ∀ {ε : ℝ} (m : ℕ),
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
          ∀ F : Finset (MomentContraction m),
            (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) →
              (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
                  ∂(r324PhysicalMeasure m)) ≤
                K ^ m * |Real.log ε| ^ (m - 1) := by
  rintro ⟨K, hK, hbound⟩
  set g0 : ℝ := r324PermCrossGreenFloorConst with hg0def
  have hg0 := r324PermCrossGreenFloorConst_pos
  set V : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hVdef
  have hV0 : 0 < V := by rw [hVdef]; positivity
  -- the geometric-vs-factorial threshold
  obtain ⟨m, hm3, hbeats⟩ :=
    r324PermCross_exists_factorial_beats_pow
      (c := g0 ^ 2 * V) (C₀ := g0 ^ 2 * V ^ 4)
      (by positivity) (by positivity) K 3
  -- the admissible scale `ε = e⁻¹`
  set ε : ℝ := Real.exp (-1) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := by
    rw [hεdef, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hlog : |Real.log ε| = 1 := by
    rw [hεdef, Real.log_exp]
    norm_num
  have hlog1 : 1 ≤ |Real.log ε| := le_of_eq hlog.symm
  -- the proved budget at the full permutation fibre
  have hup := hbound m hε hε1 hlog1 hm3
    (r324LedgerThreePermEntities m)
    (r324PermCross_permEntities_allCross m)
  rw [hlog, one_pow, mul_one] at hup
  -- the factorial minorant
  have hlow := r324PermCross_integral_crossDensity_ge ρ hε hε1
    (m := m) (le_trans (by norm_num) hm3)
  rw [← hg0def, ← hVdef] at hlow
  -- numeric contradiction
  have hchain : g0 ^ 2 * V ^ 4 *
      ((m.factorial : ℝ) * (g0 ^ 2 * V) ^ m) ≤
      g0 ^ (2 * m + 2) * ((m.factorial : ℝ) * V ^ (m + 4)) := by
    have h1 : g0 ^ (2 * m + 2) = g0 ^ 2 * (g0 ^ 2) ^ m := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    have h2 : V ^ (m + 4) = V ^ m * V ^ 4 := by
      rw [← pow_add]
    rw [h1, h2, mul_pow]
    ring_nf
    exact le_refl _
  have hcontr : K ^ m <
      g0 ^ (2 * m + 2) * ((m.factorial : ℝ) * V ^ (m + 4)) :=
    lt_of_lt_of_le hbeats hchain
  exact absurd (le_trans hlow hup) (not_le.mpr hcontr)

/-- **The `ε`-uniform factorial floor of the pure-cross fibre**, in the
interface variables: at every admissible scale the summed pure-cross
density of the full bijection fibre integrates to at least
`m! · c(ρ)^m` with `c` independent of `ε` — so *any* sound cross-case
budget must grow at least factorially in the order.  (Re-export of
`r324PermCross_integral_crossDensity_ge` with the fibre-side
hypotheses of the interface.) -/
theorem r324PermCross_crossDensity_factorial_floor (ρ : SmoothCutoff) :
    ∃ c C₀ : ℝ, 0 < c ∧ 0 < C₀ ∧
      ∀ {ε : ℝ} (m : ℕ), 0 < ε → ε ≤ 1 → 1 ≤ m →
        ∃ F : Finset (MomentContraction m),
          (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) ∧
            C₀ * ((m.factorial : ℝ) * c ^ m) ≤
              ∫ p, r324LedgerThreeCrossDensity ρ ε m F p
                ∂(r324PhysicalMeasure m) := by
  set g0 : ℝ := r324PermCrossGreenFloorConst with hg0def
  have hg0 := r324PermCrossGreenFloorConst_pos
  set V : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hVdef
  have hV0 : 0 < V := by rw [hVdef]; positivity
  refine ⟨g0 ^ 2 * V, g0 ^ 2 * V ^ 4, by positivity, by positivity,
    ?_⟩
  intro ε m hε hε1 hm
  refine ⟨r324LedgerThreePermEntities m,
    r324PermCross_permEntities_allCross m, ?_⟩
  refine le_trans (le_of_eq ?_)
    (r324PermCross_integral_crossDensity_ge ρ hε hε1 (m := m) hm)
  rw [← hg0def, ← hVdef]
  have h1 : g0 ^ (2 * m + 2) = g0 ^ 2 * (g0 ^ 2) ^ m := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have h2 : V ^ (m + 4) = V ^ m * V ^ 4 := by
    rw [← pow_add]
  rw [h1, h2, mul_pow]
  ring

/-- **Order-capped cross bound**: the pure-cross fibre bound with
the order capped against the logarithmic budget, exactly matching the
paper's truncation `A = ⌊|log ε|⌋` (`truncOrder`).  The factorial floor
`r324PermCross_crossDensity_factorial_floor` shows some cap (or an
explicit factorial allowance) is *necessary*; this Prop records the
form used by the truncated parametrix estimate. -/
def R324PermCrossOrderCappedCrossBound
    (ρ : SmoothCutoff) (K : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m →
      m ≤ truncOrder ε →
        ∀ F : Finset (MomentContraction m),
          (∀ e ∈ F, R324LedgerThreeAllCrossEntity e) →
            (∫ p, r324LedgerThreeCrossDensity ρ ε m F p
                ∂(r324PhysicalMeasure m)) ≤
              K ^ m * (m.factorial : ℝ) *
                |Real.log ε| ^ (m - 1)

end

end Anderson4D
