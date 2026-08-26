import Anderson4D.DetParametrix.Paper42_Moment.R324SelectedCellDecomposition
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFourierTermClosure

/-!
# Internal-cell Fubini bridge for R-324

The open-edge discretization constrains only the doubled internal
variables.  This file moves such a measurable constraint through the
genuine five-variable product measure and puts the internal integral
outside the four endpoint integrals.

This order is essential for the decaying branch of (3.24): the four
endpoint Fourier integrals must be performed before a norm is taken.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The internal coordinate of the genuine R-324 physical product. -/
def r324InternalCoordinate {m : ℕ} :
    R324PhysicalPoint m → (Fin (2 * m) → T4) :=
  fun p => p.2.2.2.2

theorem measurable_r324InternalCoordinate {m : ℕ} :
    Measurable (r324InternalCoordinate (m := m)) :=
  measurable_snd.comp
    (measurable_snd.comp
      (measurable_snd.comp measurable_snd))

/-- A measurable restriction on only the internal variables may be
moved outside all four endpoint integrations. -/
theorem r324_setIntegral_internal_eq_internal_first
    {m : ℕ}
    (f : T4 → T4 → T4 → T4 →
      (Fin (2 * m) → T4) → ℂ)
    (S : Set (Fin (2 * m) → T4))
    (hS : MeasurableSet S)
    (hf : Integrable (r324Flatten f)
      (r324PhysicalMeasure m)) :
    (∫ p in r324InternalCoordinate ⁻¹' S,
        r324Flatten f p
        ∂(r324PhysicalMeasure m)) =
      ∫ v in S, ∫ x, ∫ y, ∫ z, ∫ w,
        f x y z w v
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let g : T4 → T4 → T4 → T4 →
      (Fin (2 * m) → T4) → ℂ :=
    fun x y z w v =>
      S.indicator (fun u => f x y z w u) v
  have hflat :
      r324Flatten g =
        (r324InternalCoordinate ⁻¹' S).indicator
          (r324Flatten f) := by
    funext p
    by_cases hp : r324InternalCoordinate p ∈ S
    · change
        S.indicator
            (fun u => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 u)
            (r324InternalCoordinate p) =
          (r324InternalCoordinate ⁻¹' S).indicator
            (r324Flatten f) p
      rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem]
      · rfl
      · exact hp
    · change
        S.indicator
            (fun u => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 u)
            (r324InternalCoordinate p) =
          (r324InternalCoordinate ⁻¹' S).indicator
            (r324Flatten f) p
      simp only [Set.indicator]
      rw [if_neg hp, if_neg]
      exact hp
  have hg :
      Integrable (r324Flatten g)
        (r324PhysicalMeasure m) := by
    rw [hflat]
    exact
      hf.indicator
        (hS.preimage measurable_r324InternalCoordinate)
  have horder :=
    r324_integral_product_eq_internal_first g hg
  rw [hflat] at horder
  rw [← integral_indicator
    (hS.preimage measurable_r324InternalCoordinate)]
  rw [horder]
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hv : v ∈ S
  · simp [g, Set.indicator, hv]
  · simp [Set.indicator, g, hv]

end

end Anderson4D
