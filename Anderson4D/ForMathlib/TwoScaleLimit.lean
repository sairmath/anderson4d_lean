import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Two-scale limits

This file packages the `ε → 0` first, truncation order `B → ∞` second
argument used in paper (3.39).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open Filter
open scoped Topology

/-- A family converges if it is uniformly approximated, at every fixed
truncation order, by families with known limits; the approximation error
and those limits then converge as the truncation order tends to infinity.

No countability or nontriviality assumption on the primary filter is
needed. -/
theorem tendsto_of_two_scale_approximation
    {ι E : Type*} [PseudoMetricSpace E]
    {l : Filter ι}
    (f : ι → E) (g : ℕ → ι → E) (zB : ℕ → E) (z : E)
    (error : ℕ → ℝ)
    (hg : ∀ B, Tendsto (g B) l (𝓝 (zB B)))
    (hz : Tendsto zB atTop (𝓝 z))
    (herror : Tendsto error atTop (𝓝 0))
    (hclose : ∀ B, ∀ᶠ i in l,
      dist (f i) (g B i) ≤ error B) :
    Tendsto f l (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨Bz, hBz⟩ :=
    (Metric.tendsto_atTop.mp hz) (ε / 3) hε3
  obtain ⟨Be, hBe⟩ :=
    (Metric.tendsto_atTop.mp herror) (ε / 3) hε3
  let B := max Bz Be
  have hzB : dist (zB B) z < ε / 3 :=
    hBz B (le_max_left _ _)
  have heB : dist (error B) 0 < ε / 3 :=
    hBe B (le_max_right _ _)
  have heB' : error B < ε / 3 := by
    have habs : |error B| < ε / 3 := by
      simpa only [Real.dist_eq, sub_zero] using heB
    exact (abs_lt.mp habs).2
  have hgB :=
    (Metric.tendsto_nhds.mp (hg B)) (ε / 3) hε3
  filter_upwards [hclose B, hgB] with i hfg hgi
  calc
    dist (f i) z ≤
        dist (f i) (g B i) +
          dist (g B i) (zB B) + dist (zB B) z := by
      exact (dist_triangle4 (f i) (g B i) (zB B) z)
    _ < ε := by linarith

end Anderson4D
