import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Convergence from high-probability good events

This file packages the probability-theoretic replacement step used in
§3.4, Step 2 of Deng--Shen.  If two random variables are uniformly close
on events whose complements have probability tending to zero, then their
difference tends to zero in probability.  Consequently one may replace
one by the other in a convergence-in-distribution statement.

The statements are filter-indexed, so they apply directly to
`ε → 0⁺` rather than only to sequences.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory
open scoped Topology

variable {ι Ω E Ω' : Type*}

/-- Uniform closeness on high-probability events implies convergence in
probability of the difference to zero.  No measurability hypothesis on
the good events is needed: monotonicity of outer measure suffices. -/
theorem tendstoInMeasure_sub_of_goodEvent
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    [SeminormedAddCommGroup E]
    {l : Filter ι} (X Y : ι → Ω → E)
    (good : ι → Set Ω) (error : ι → ℝ)
    (herror : Tendsto error l (𝓝 0))
    (hbad : Tendsto (fun i ↦ μ.real (good i)ᶜ) l (𝓝 0))
    (hclose :
      ∀ᶠ i in l, ∀ ω ∈ good i, ‖Y i ω - X i ω‖ ≤ error i) :
    TendstoInMeasure μ (Y - X) l 0 := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbad
      (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [herror.eventually_lt_const hε, hclose] with i hi hclose_i
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω
  show ω ∈ (good i)ᶜ
  intro hω_good
  exact (not_le_of_gt hi) (hω.trans (hclose_i ω hω_good))

/-- **Good-event replacement for convergence in distribution.**
If `X` converges in distribution and `Y-X` is uniformly small on events
whose complements vanish in probability, then `Y` has the same limit
law. -/
theorem TendstoInDistribution.goodEvent_replace
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [MeasurableSpace Ω'] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    [SeminormedAddCommGroup E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {l : Filter ι} [l.IsCountablyGenerated]
    (X Y : ι → Ω → E) (Z : Ω' → E)
    (hX : TendstoInDistribution X l Z (fun _ ↦ μ) μ')
    (hY : ∀ i, AEMeasurable (Y i) μ)
    (good : ι → Set Ω) (error : ι → ℝ)
    (herror : Tendsto error l (𝓝 0))
    (hbad : Tendsto (fun i ↦ μ.real (good i)ᶜ) l (𝓝 0))
    (hclose :
      ∀ᶠ i in l, ∀ ω ∈ good i, ‖Y i ω - X i ω‖ ≤ error i) :
    TendstoInDistribution Y l Z (fun _ ↦ μ) μ' := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub Y Z hX
    (tendstoInMeasure_sub_of_goodEvent μ X Y good error
      herror hbad hclose)
    hY

end

end Anderson4D
