import Anderson4D.Continuum.CovariancePeriodizationFiniteDerivatives

/-!
# Global derivative bounds for the covariance periodization

Compact support gives a common finite lattice window near every point.
Combining that geometry with the finite-window derivative formulas removes
the local-window hypotheses from the coordinate `C⁸` and derivative
majorant statements.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open Filter
open scoped Topology

namespace SmoothCutoff

/-- A lattice radius large enough to contain every nonzero periodization
term in the unit neighborhood of `x₀`. -/
def etaPeriodLocalRadiusR4
    (ρ : SmoothCutoff) (ε : ℝ) (x₀ : R4) : ℤ :=
  ⌈(2 * ρ.radius * ε + ‖x₀‖ + 1) / (2 * Real.pi)⌉

/-- The corresponding finite lattice window. -/
def etaPeriodLocalBoxR4
    (ρ : SmoothCutoff) (ε : ℝ) (x₀ : R4) : Finset Z4 :=
  Fintype.piFinset fun _ : Fin dim =>
    Finset.Icc (-ρ.etaPeriodLocalRadiusR4 ε x₀)
      (ρ.etaPeriodLocalRadiusR4 ε x₀)

/-- Every nonzero periodization term in the unit neighborhood belongs to
the explicit local box. -/
theorem mem_etaPeriodLocalBoxR4_of_ne_zero
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x₀ x : R4) (hx : dist x x₀ < 1) {k : Z4}
    (hk : ρ.etaPeriodTermR4 ε x k ≠ 0) :
    k ∈ ρ.etaPeriodLocalBoxR4 ε x₀ := by
  have heta :
      ρ.eta (fun j =>
        ε⁻¹ * (x j + covariancePeriodVector k j)) ≠ 0 :=
    (mul_ne_zero_iff.mp hk).2
  have hsupport :=
    ρ.norm_lt_two_radius_of_eta_ne_zero heta
  change ‖ε⁻¹ • (x + covariancePeriodVector k)‖ <
    2 * ρ.radius at hsupport
  have hterm :
      ‖x + covariancePeriodVector k‖ <
        2 * ρ.radius * ε := by
    have hscaled :
        ε⁻¹ * ‖x + covariancePeriodVector k‖ <
          2 * ρ.radius := by
      calc
        ε⁻¹ * ‖x + covariancePeriodVector k‖ =
            ‖ε⁻¹ • (x + covariancePeriodVector k)‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hε)]
        _ < 2 * ρ.radius := hsupport
    calc
      ‖x + covariancePeriodVector k‖ =
          ε * (ε⁻¹ * ‖x + covariancePeriodVector k‖) := by
        field_simp
      _ < ε * (2 * ρ.radius) :=
        mul_lt_mul_of_pos_left hscaled hε
      _ = 2 * ρ.radius * ε := by ring
  have hxnorm : ‖x‖ < ‖x₀‖ + 1 := by
    calc
      ‖x‖ = ‖(x - x₀) + x₀‖ := by
        congr 1
        abel
      _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
      _ < 1 + ‖x₀‖ := by
        simpa [dist_eq_norm] using
          add_lt_add_right hx ‖x₀‖
      _ = ‖x₀‖ + 1 := by ring
  unfold etaPeriodLocalBoxR4
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hcoord :
      |x i + 2 * Real.pi * (k i : ℝ)| <
        2 * ρ.radius * ε := by
    calc
      |x i + 2 * Real.pi * (k i : ℝ)| =
          ‖(x + covariancePeriodVector k) i‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖x + covariancePeriodVector k‖ :=
        norm_le_pi_norm _ _
      _ < 2 * ρ.radius * ε := hterm
  have hxcoord : |x i| < ‖x₀‖ + 1 := by
    calc
      |x i| = ‖x i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖x‖ := norm_le_pi_norm _ _
      _ < ‖x₀‖ + 1 := hxnorm
  have hperiod :
      |2 * Real.pi * (k i : ℝ)| <
        2 * ρ.radius * ε + ‖x₀‖ + 1 := by
    calc
      |2 * Real.pi * (k i : ℝ)| =
          |(x i + 2 * Real.pi * (k i : ℝ)) - x i| := by
        congr 1
        ring
      _ ≤ |x i + 2 * Real.pi * (k i : ℝ)| + |x i| :=
        abs_sub _ _
      _ < 2 * ρ.radius * ε + (‖x₀‖ + 1) :=
        add_lt_add hcoord hxcoord
      _ = 2 * ρ.radius * ε + ‖x₀‖ + 1 := by ring
  have hkabs :
      |(k i : ℝ)| <
        (2 * ρ.radius * ε + ‖x₀‖ + 1) /
          (2 * Real.pi) := by
    rw [abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      at hperiod
    exact (lt_div_iff₀
      (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      (by simpa [mul_comm] using hperiod)
  have hceil :
      (2 * ρ.radius * ε + ‖x₀‖ + 1) /
          (2 * Real.pi) ≤
        (ρ.etaPeriodLocalRadiusR4 ε x₀ : ℝ) :=
    Int.le_ceil _
  have hkupper :
      (k i : ℝ) ≤
        (ρ.etaPeriodLocalRadiusR4 ε x₀ : ℝ) :=
    (le_abs_self _).trans (hkabs.le.trans hceil)
  have hklower :
      (-(ρ.etaPeriodLocalRadiusR4 ε x₀ : ℤ) : ℝ) ≤
        (k i : ℝ) := by
    have hneg :
        -(ρ.etaPeriodLocalRadiusR4 ε x₀ : ℝ) ≤
          -|(k i : ℝ)| :=
      neg_le_neg (hkabs.le.trans hceil)
    exact hneg.trans (neg_abs_le _)
  constructor
  · exact_mod_cast hklower
  · exact_mod_cast hkupper

/-- A common window for the original cutoff and the auxiliary cutoff used
in the derivative majorant. -/
def etaPeriodJointLocalBoxR4
    (ρ : SmoothCutoff) (ε : ℝ) (x₀ : R4) : Finset Z4 :=
  ρ.etaPeriodLocalBoxR4 ε x₀ ∪
    ρ.auxiliaryCutoff.etaPeriodLocalBoxR4 ε x₀

/-- Compact support supplies exactly the two window conditions required
by `abs_iteratedDeriv_etaPeriodizationR4_coordLine_le`. -/
theorem exists_etaPeriodizationR4_coordLine_jointLocalWindow
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : R4) (i : Fin dim) (t : ℝ) :
    ∃ Q : Finset Z4,
      (∀ᶠ s in 𝓝 t, ∀ k : Z4, k ∉ Q →
        ρ.etaPeriodTermCoordLine ε x k i s = 0) ∧
      (∀ k : Z4, k ∉ Q →
        ρ.auxiliaryCutoff.etaPeriodTermR4 ε
          (Function.update x i t) k = 0) := by
  let x₀ : R4 := Function.update x i t
  let Q := ρ.etaPeriodJointLocalBoxR4 ε x₀
  refine ⟨Q, ?_, ?_⟩
  · have hnear :
        ∀ᶠ s in 𝓝 t,
          Function.update x i s ∈ Metric.ball x₀ 1 := by
      exact
        (continuous_const.update i continuous_id).continuousAt
          (Metric.ball_mem_nhds x₀ zero_lt_one)
    filter_upwards [hnear] with s hs
    intro k hk
    by_contra hne
    apply hk
    unfold Q etaPeriodJointLocalBoxR4
    apply Finset.mem_union_left
    apply ρ.mem_etaPeriodLocalBoxR4_of_ne_zero
      hε x₀ (Function.update x i s)
      (by simpa [Metric.mem_ball] using hs)
    simpa only [
      ρ.etaPeriodTermCoordLine_eq ε x k i s] using hne
  · intro k hk
    by_contra hne
    apply hk
    unfold Q etaPeriodJointLocalBoxR4
    apply Finset.mem_union_right
    apply
      ρ.auxiliaryCutoff.mem_etaPeriodLocalBoxR4_of_ne_zero
        hε x₀ x₀
    · simp
    · exact hne

/-- Every coordinate line of the true periodization is `C⁸`, with the
finite lattice window constructed from compact support. -/
theorem contDiff_etaPeriodizationR4_coordLine_eight
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : R4) (i : Fin dim) :
    ContDiff ℝ 8 fun t =>
      ρ.etaPeriodizationR4 ε (Function.update x i t) := by
  apply
    ρ.contDiff_etaPeriodizationR4_coordLine_eight_of_local_windows
  intro t
  obtain ⟨Q, hout, _haux⟩ :=
    ρ.exists_etaPeriodizationR4_coordLine_jointLocalWindow
      hε x i t
  exact ⟨Q, hout⟩

/-- Global coordinate-derivative majorant for the true periodization.
There is no lattice-cardinality loss. -/
theorem abs_iteratedDeriv_etaPeriodizationR4_coordLine_le_global
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (x : R4) (i : Fin dim) (t : ℝ)
    {r : ℕ} (hr : r ≤ 8) :
    |iteratedDeriv r
        (fun s =>
          ρ.etaPeriodizationR4 ε
            (Function.update x i s)) t| ≤
      (ρ.etaDerivativeMajorantConstant * ε⁻¹ ^ r) *
        ρ.auxiliaryCutoff.etaPeriodizationR4 ε
          (Function.update x i t) := by
  obtain ⟨Q, hout, haux⟩ :=
    ρ.exists_etaPeriodizationR4_coordLine_jointLocalWindow
      hε x i t
  exact
    ρ.abs_iteratedDeriv_etaPeriodizationR4_coordLine_le
      Q hε x i t hr hout haux

end SmoothCutoff

end

end Anderson4D
