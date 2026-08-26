import Anderson4D.Continuum.CovariancePeriodTermDerivatives

/-!
# Finite-window derivatives of the covariance periodization

Finite lattice windows may be differentiated without any summability
argument.  This file proves the exact formula and its termwise auxiliary
majorant, then gives local-finiteness interfaces which transfer those facts
to `etaPeriodizationR4`.  The geometric construction of a suitable window
is intentionally left to the support-localization layer.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter
open scoped Topology

namespace SmoothCutoff

/-- A finite lattice window of the coordinate-line periodization. -/
def etaPeriodizationCoordLineWindow
    (ρ : SmoothCutoff) (Q : Finset Z4) (ε : ℝ)
    (x : R4) (i : Fin dim) (t : ℝ) : ℝ :=
  ∑ k ∈ Q, ρ.etaPeriodTermCoordLine ε x k i t

/-- The coordinate-line window is the corresponding finite sum of the
existing arbitrary-representative periodization terms. -/
theorem etaPeriodizationCoordLineWindow_eq
    (ρ : SmoothCutoff) (Q : Finset Z4) (ε : ℝ)
    (x : R4) (i : Fin dim) (t : ℝ) :
    ρ.etaPeriodizationCoordLineWindow Q ε x i t =
      ∑ k ∈ Q,
        ρ.etaPeriodTermR4 ε (Function.update x i t) k := by
  apply Finset.sum_congr rfl
  intro k hk
  exact ρ.etaPeriodTermCoordLine_eq ε x k i t

/-- Every finite coordinate-line window is `C⁸`. -/
theorem contDiff_etaPeriodizationCoordLineWindow_eight
    (ρ : SmoothCutoff) (Q : Finset Z4) (ε : ℝ)
    (x : R4) (i : Fin dim) :
    ContDiff ℝ 8
      (ρ.etaPeriodizationCoordLineWindow Q ε x i) := by
  unfold etaPeriodizationCoordLineWindow
  apply ContDiff.sum
  intro k hk
  exact ρ.contDiff_etaPeriodTermCoordLine_eight ε x k i

/-- Iterated differentiation commutes with a finite lattice window. -/
theorem iteratedDeriv_etaPeriodizationCoordLineWindow_eq_sum
    (ρ : SmoothCutoff) (Q : Finset Z4) (ε : ℝ)
    (x : R4) (i : Fin dim) (t : ℝ)
    {r : ℕ} (hr : r ≤ 8) :
    iteratedDeriv r
        (ρ.etaPeriodizationCoordLineWindow Q ε x i) t =
      ∑ k ∈ Q,
        iteratedDeriv r
          (ρ.etaPeriodTermCoordLine ε x k i) t := by
  unfold etaPeriodizationCoordLineWindow
  exact iteratedDeriv_fun_sum fun k hk =>
    ((ρ.contDiff_etaPeriodTermCoordLine_eight ε x k i).of_le
      (by exact_mod_cast hr)).contDiffAt

/-- Exact finite-sum formula for the repeated coordinate derivative. -/
theorem iteratedDeriv_etaPeriodizationCoordLineWindow
    (ρ : SmoothCutoff) (Q : Finset Z4)
    {ε : ℝ} (hε : 0 < ε) (x : R4)
    (i : Fin dim) (t : ℝ) {r : ℕ} (hr : r ≤ 8) :
    iteratedDeriv r
        (ρ.etaPeriodizationCoordLineWindow Q ε x i) t =
      ∑ k ∈ Q,
        ε⁻¹ ^ (dim : ℕ) * ε⁻¹ ^ r *
          ρ.etaCoordDerivative r i
            (fun j =>
              ε⁻¹ *
                (Function.update x i t j +
                  covariancePeriodVector k j)) := by
  rw [ρ.iteratedDeriv_etaPeriodizationCoordLineWindow_eq_sum
    Q ε x i t hr]
  apply Finset.sum_congr rfl
  intro k hk
  exact ρ.iteratedDeriv_etaPeriodTermCoordLine hε r x k i t

/-- The finite-window derivative is bounded by the matching auxiliary
finite sum, with no lattice-cardinality factor. -/
theorem abs_iteratedDeriv_etaPeriodizationCoordLineWindow_le
    (ρ : SmoothCutoff) (Q : Finset Z4)
    {ε : ℝ} (hε : 0 < ε) (x : R4)
    (i : Fin dim) (t : ℝ) {r : ℕ} (hr : r ≤ 8) :
    |iteratedDeriv r
        (ρ.etaPeriodizationCoordLineWindow Q ε x i) t| ≤
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ∑ k ∈ Q,
          ρ.auxiliaryCutoff.etaPeriodTermR4 ε
            (Function.update x i t) k := by
  rw [ρ.iteratedDeriv_etaPeriodizationCoordLineWindow_eq_sum
    Q ε x i t hr]
  calc
    |∑ k ∈ Q,
        iteratedDeriv r
          (ρ.etaPeriodTermCoordLine ε x k i) t| ≤
      ∑ k ∈ Q,
        |iteratedDeriv r
          (ρ.etaPeriodTermCoordLine ε x k i) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
      ∑ k ∈ Q,
        (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
          ρ.auxiliaryCutoff.etaPeriodTermR4 ε
            (Function.update x i t) k := by
      apply Finset.sum_le_sum
      intro k hk
      exact ρ.abs_iteratedDeriv_etaPeriodTermCoordLine_le
        hε hr x k i t
    _ =
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ∑ k ∈ Q,
          ρ.auxiliaryCutoff.etaPeriodTermR4 ε
            (Function.update x i t) k := by
      rw [Finset.mul_sum]

/-- An arbitrary-representative periodization equals a finite window once
all terms outside that window vanish. -/
theorem etaPeriodizationR4_eq_sum_of_outside_eq_zero
    (ρ : SmoothCutoff) (Q : Finset Z4)
    (ε : ℝ) (y : R4)
    (hout : ∀ k : Z4, k ∉ Q →
      ρ.etaPeriodTermR4 ε y k = 0) :
    ρ.etaPeriodizationR4 ε y =
      ∑ k ∈ Q, ρ.etaPeriodTermR4 ε y k := by
  unfold etaPeriodizationR4
  exact tsum_eq_sum hout

/-- A neighborhood-wise vanishing condition gives the local finite
representation needed for differentiation. -/
theorem eventuallyEq_etaPeriodizationCoordLineWindow
    (ρ : SmoothCutoff) (Q : Finset Z4)
    (ε : ℝ) (x : R4) (i : Fin dim) (t : ℝ)
    (hout : ∀ᶠ s in 𝓝 t, ∀ k : Z4, k ∉ Q →
      ρ.etaPeriodTermCoordLine ε x k i s = 0) :
    (fun s =>
      ρ.etaPeriodizationR4 ε (Function.update x i s)) =ᶠ[𝓝 t]
        ρ.etaPeriodizationCoordLineWindow Q ε x i := by
  filter_upwards [hout] with s hs
  calc
    ρ.etaPeriodizationR4 ε (Function.update x i s) =
        ∑ k ∈ Q,
          ρ.etaPeriodTermR4 ε
            (Function.update x i s) k := by
      apply ρ.etaPeriodizationR4_eq_sum_of_outside_eq_zero
      intro k hk
      simpa only [ρ.etaPeriodTermCoordLine_eq ε x k i s] using
        hs k hk
    _ = ρ.etaPeriodizationCoordLineWindow Q ε x i s :=
      (ρ.etaPeriodizationCoordLineWindow_eq Q ε x i s).symm

/-- Local finite representations at every point imply global `C⁸`
regularity of the arbitrary-representative coordinate line. -/
theorem contDiff_etaPeriodizationR4_coordLine_eight_of_local_windows
    (ρ : SmoothCutoff) (ε : ℝ) (x : R4) (i : Fin dim)
    (hlocal : ∀ t : ℝ, ∃ Q : Finset Z4,
      ∀ᶠ s in 𝓝 t, ∀ k : Z4, k ∉ Q →
        ρ.etaPeriodTermCoordLine ε x k i s = 0) :
    ContDiff ℝ 8 fun t =>
      ρ.etaPeriodizationR4 ε (Function.update x i t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  obtain ⟨Q, hQ⟩ := hlocal t
  have heq :=
    ρ.eventuallyEq_etaPeriodizationCoordLineWindow
      Q ε x i t hQ
  exact
    (ρ.contDiff_etaPeriodizationCoordLineWindow_eight
      Q ε x i).contDiffAt.congr_of_eventuallyEq heq

/-- Exact derivative of the true periodization under a local finite-window
condition. -/
theorem iteratedDeriv_etaPeriodizationR4_coordLine_eq_sum
    (ρ : SmoothCutoff) (Q : Finset Z4)
    (ε : ℝ) (x : R4)
    (i : Fin dim) (t : ℝ) {r : ℕ} (hr : r ≤ 8)
    (hout : ∀ᶠ s in 𝓝 t, ∀ k : Z4, k ∉ Q →
      ρ.etaPeriodTermCoordLine ε x k i s = 0) :
    iteratedDeriv r
        (fun s =>
          ρ.etaPeriodizationR4 ε
            (Function.update x i s)) t =
      ∑ k ∈ Q,
        iteratedDeriv r
          (ρ.etaPeriodTermCoordLine ε x k i) t := by
  have heq :=
    ρ.eventuallyEq_etaPeriodizationCoordLineWindow
      Q ε x i t hout
  calc
    iteratedDeriv r
        (fun s =>
          ρ.etaPeriodizationR4 ε
            (Function.update x i s)) t =
      iteratedDeriv r
        (ρ.etaPeriodizationCoordLineWindow Q ε x i) t :=
      Filter.EventuallyEq.iteratedDeriv_eq r heq
    _ = ∑ k ∈ Q,
        iteratedDeriv r
          (ρ.etaPeriodTermCoordLine ε x k i) t :=
      ρ.iteratedDeriv_etaPeriodizationCoordLineWindow_eq_sum
        Q ε x i t hr

/-- The true periodization inherits the auxiliary majorant whenever the
same window is locally valid for the original terms and pointwise valid
for the auxiliary terms. -/
theorem abs_iteratedDeriv_etaPeriodizationR4_coordLine_le
    (ρ : SmoothCutoff) (Q : Finset Z4)
    {ε : ℝ} (hε : 0 < ε) (x : R4)
    (i : Fin dim) (t : ℝ) {r : ℕ} (hr : r ≤ 8)
    (hout : ∀ᶠ s in 𝓝 t, ∀ k : Z4, k ∉ Q →
      ρ.etaPeriodTermCoordLine ε x k i s = 0)
    (houtAux : ∀ k : Z4, k ∉ Q →
      ρ.auxiliaryCutoff.etaPeriodTermR4 ε
        (Function.update x i t) k = 0) :
    |iteratedDeriv r
        (fun s =>
          ρ.etaPeriodizationR4 ε
            (Function.update x i s)) t| ≤
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ρ.auxiliaryCutoff.etaPeriodizationR4 ε
          (Function.update x i t) := by
  have heq :=
    ρ.eventuallyEq_etaPeriodizationCoordLineWindow
      Q ε x i t hout
  have haux :=
    ρ.auxiliaryCutoff.etaPeriodizationR4_eq_sum_of_outside_eq_zero
      Q ε (Function.update x i t) houtAux
  calc
    |iteratedDeriv r
        (fun s =>
          ρ.etaPeriodizationR4 ε
            (Function.update x i s)) t| =
      |iteratedDeriv r
        (ρ.etaPeriodizationCoordLineWindow Q ε x i) t| := by
      exact congrArg (fun u : ℝ => |u|)
        (Filter.EventuallyEq.iteratedDeriv_eq r heq)
    _ ≤
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ∑ k ∈ Q,
          ρ.auxiliaryCutoff.etaPeriodTermR4 ε
            (Function.update x i t) k :=
      ρ.abs_iteratedDeriv_etaPeriodizationCoordLineWindow_le
        Q hε x i t hr
    _ =
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ρ.auxiliaryCutoff.etaPeriodizationR4 ε
          (Function.update x i t) := by
      rw [haux]

end SmoothCutoff

end

end Anderson4D
