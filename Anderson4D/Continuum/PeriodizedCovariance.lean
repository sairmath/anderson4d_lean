import Anderson4D.Continuum.Covariance
import Anderson4D.Continuum.Discretization

/-!
# Bounds for the periodized cutoff covariance

The torus covariance is written in `DetParametrix.Kernels` as a lattice
periodization of the compactly supported Euclidean covariance.  This file
proves that, for `0 < ε ≤ 1`, only a fixed finite box of period vectors can
contribute.  It then turns the Euclidean uniform bound into the paper-scale
`O(ε⁻⁴)` torus bound without any summability hypothesis.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- A fixed integer half-width containing every period vector which can
meet the support of `η_ε`, uniformly for `0 < ε ≤ 1`. -/
def covariancePeriodRadius : ℤ :=
  ⌈(2 * ρ.radius + Real.pi) / (2 * Real.pi)⌉

/-- The corresponding finite box in `ℤ⁴`. -/
def covariancePeriodBox : Finset Z4 :=
  Fintype.piFinset fun _ : Fin dim =>
    Finset.Icc (-ρ.covariancePeriodRadius) ρ.covariancePeriodRadius

/-- One summand in the lattice periodization defining `etaEpsT4`. -/
def etaPeriodTerm (ε : ℝ) (z : T4) (k : Z4) : ℝ :=
  ε⁻¹ ^ (dim : ℕ) *
    ρ.eta (fun i => ε⁻¹ *
      (torusLift z i + 2 * Real.pi * (k i : ℝ)))

theorem etaEpsT4_eq_tsum_etaPeriodTerm (ε : ℝ) (z : T4) :
    ρ.etaEpsT4 ε z = ∑' k : Z4, ρ.etaPeriodTerm ε z k :=
  rfl

/-- Passing from a Euclidean representative to the product quotient does
not increase the fixed sup norm. -/
theorem norm_periodizeR4_le (x : R4) :
    ‖periodizeR4 x‖ ≤ ‖x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro i
  calc
    ‖periodizeR4 x i‖ ≤ ‖x i‖ :=
      QuotientAddGroup.norm_mk_le_norm
    _ ≤ ‖x‖ := norm_le_pi_norm _ _

/-- Every period representative of a torus point dominates its quotient
norm. -/
theorem norm_le_periodicDisplacement (z : T4) (k : Z4) :
    ‖z‖ ≤ ‖periodicDisplacement z k‖ := by
  calc
    ‖z‖ = ‖periodizeR4 (periodicDisplacement z k)‖ := by
      rw [periodizeR4_periodicDisplacement]
    _ ≤ ‖periodicDisplacement z k‖ :=
      norm_periodizeR4_le _

/-- A nonzero periodization term belongs to the fixed period box. -/
theorem etaPeriodTerm_ne_zero_mem_covariancePeriodBox
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : T4) {k : Z4}
    (hk : ρ.etaPeriodTerm ε z k ≠ 0) :
    k ∈ ρ.covariancePeriodBox := by
  have heta :
      ρ.eta (fun i => ε⁻¹ *
        (torusLift z i + 2 * Real.pi * (k i : ℝ))) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hk).2
  have hsupport := ρ.norm_lt_two_radius_of_eta_ne_zero heta
  change ‖ε⁻¹ • periodicDisplacement z k‖ < 2 * ρ.radius at hsupport
  have hdisp : ‖periodicDisplacement z k‖ < 2 * ρ.radius * ε := by
    have hscaled :
        ε⁻¹ * ‖periodicDisplacement z k‖ < 2 * ρ.radius := by
      simpa [norm_smul, abs_of_pos hε, abs_inv] using hsupport
    calc
      ‖periodicDisplacement z k‖ =
          ε * (ε⁻¹ * ‖periodicDisplacement z k‖) := by
            field_simp
      _ < ε * (2 * ρ.radius) :=
        mul_lt_mul_of_pos_left hscaled hε
      _ = 2 * ρ.radius * ε := by ring
  unfold covariancePeriodBox
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hcoord :
      |torusLift z i + 2 * Real.pi * (k i : ℝ)|
        < 2 * ρ.radius * ε := by
    calc
      |torusLift z i + 2 * Real.pi * (k i : ℝ)| =
          ‖periodicDisplacement z k i‖ := by
            rw [Real.norm_eq_abs]
            rfl
      _ ≤ ‖periodicDisplacement z k‖ :=
        norm_le_pi_norm _ _
      _ < 2 * ρ.radius * ε := hdisp
  have hlift : |torusLift z i| ≤ Real.pi := by
    obtain ⟨hlo, hhi⟩ := torusLift_mem_Ico z i
    rw [abs_le]
    exact ⟨hlo, hhi.le⟩
  have hperiod :
      |2 * Real.pi * (k i : ℝ)|
        < 2 * ρ.radius * ε + Real.pi := by
    calc
      |2 * Real.pi * (k i : ℝ)| =
          |(torusLift z i + 2 * Real.pi * (k i : ℝ)) -
            torusLift z i| := by congr 1; ring
      _ ≤ |torusLift z i + 2 * Real.pi * (k i : ℝ)| +
          |torusLift z i| := abs_sub _ _
      _ < 2 * ρ.radius * ε + Real.pi :=
        add_lt_add_of_lt_of_le hcoord hlift
  have hperiod' :
      |2 * Real.pi * (k i : ℝ)|
        < 2 * ρ.radius + Real.pi := by
    have hr : 0 < 2 * ρ.radius := by nlinarith [ρ.radius_pos]
    have := mul_le_mul_of_nonneg_left hε1 hr.le
    linarith
  have hkabs :
      |(k i : ℝ)| <
        (2 * ρ.radius + Real.pi) / (2 * Real.pi) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hperiod'
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
      (by simpa [mul_comm] using hperiod')
  have hceil :
      (2 * ρ.radius + Real.pi) / (2 * Real.pi) ≤
        (ρ.covariancePeriodRadius : ℝ) := by
    exact Int.le_ceil _
  have hkupperReal : (k i : ℝ) ≤ (ρ.covariancePeriodRadius : ℝ) :=
    (le_abs_self _).trans (hkabs.le.trans hceil)
  have hklowerReal : (-(ρ.covariancePeriodRadius : ℤ) : ℝ) ≤ (k i : ℝ) := by
    have hneg : -(ρ.covariancePeriodRadius : ℝ) ≤ -|(k i : ℝ)| :=
      neg_le_neg (hkabs.le.trans hceil)
    exact hneg.trans (neg_abs_le _)
  constructor
  · exact_mod_cast hklowerReal
  · exact_mod_cast hkupperReal

/-- The lattice periodization is an actual finite sum on the fixed box. -/
theorem etaEpsT4_eq_sum_covariancePeriodBox
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : T4) :
    ρ.etaEpsT4 ε z =
      ∑ k ∈ ρ.covariancePeriodBox, ρ.etaPeriodTerm ε z k := by
  rw [etaEpsT4_eq_tsum_etaPeriodTerm]
  exact tsum_eq_sum fun k hk => by
    by_contra hne
    exact hk (ρ.etaPeriodTerm_ne_zero_mem_covariancePeriodBox hε hε1 z hne)

/-- Every periodization term is nonnegative at positive scale. -/
theorem etaPeriodTerm_nonneg {ε : ℝ} (hε : 0 < ε) (z : T4) (k : Z4) :
    0 ≤ ρ.etaPeriodTerm ε z k := by
  unfold etaPeriodTerm
  exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hε.le) _) (ρ.eta_nonneg _)

/-- Positivity of the torus covariance.  The fourth rescaling power is
nonnegative even outside the theorem's positive-scale regime. -/
theorem etaEpsT4_nonneg (ε : ℝ) (z : T4) :
    0 ≤ ρ.etaEpsT4 ε z := by
  rw [etaEpsT4_eq_tsum_etaPeriodTerm]
  exact tsum_nonneg fun k => by
    unfold etaPeriodTerm
    exact mul_nonneg ((even_two_mul 2).pow_nonneg ε⁻¹) (ρ.eta_nonneg _)

/-- Nonvanishing of the periodized covariance forces the torus
displacement into an explicit `O(ε)` neighbourhood of zero. -/
theorem norm_lt_two_radius_mul_of_etaEpsT4_ne_zero
    {ε : ℝ} (hε : 0 < ε) {z : T4}
    (hz : ρ.etaEpsT4 ε z ≠ 0) :
    ‖z‖ < 2 * ρ.radius * ε := by
  obtain ⟨k, hk⟩ :=
    ρ.exists_periodicDisplacement_of_etaEpsT4_ne_zero hε.ne' hz
  rw [abs_of_pos hε] at hk
  exact (norm_le_periodicDisplacement z k).trans_lt hk

/-- Squared support indicator in exactly the form used by Proposition 4.1.
The factor `4` combines the product quotient norm and
`torusDistSq ≤ 4‖z‖²`. -/
theorem torusDistSq_le_support_of_etaEpsT4_ne_zero
    {ε : ℝ} (hε : 0 < ε) {z : T4}
    (hz : ρ.etaEpsT4 ε z ≠ 0) :
    torusDistSq z ≤ (4 * ρ.radius * ε) ^ 2 := by
  have hnorm := ρ.norm_lt_two_radius_mul_of_etaEpsT4_ne_zero hε hz
  have hsquare :
      ‖z‖ ^ 2 ≤ (2 * ρ.radius * ε) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hnorm.le 2
  calc
    torusDistSq z ≤ 4 * ‖z‖ ^ 2 :=
      torusDistSq_le_four_mul_sq_norm z
    _ ≤ 4 * (2 * ρ.radius * ε) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ = (4 * ρ.radius * ε) ^ 2 := by ring

/-- A Euclidean bound `η ≤ C` yields the paper-scale torus bound, with
the finite period-box cardinality kept explicit. -/
theorem etaEpsT4_le_card_mul_of_eta_bound
    {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : ∀ x : R4, ρ.eta x ≤ C) (z : T4) :
    ρ.etaEpsT4 ε z ≤
      (ρ.covariancePeriodBox.card : ℝ) *
        (ε⁻¹ ^ (dim : ℕ) * C) := by
  rw [ρ.etaEpsT4_eq_sum_covariancePeriodBox hε hε1]
  calc
    (∑ k ∈ ρ.covariancePeriodBox, ρ.etaPeriodTerm ε z k)
        ≤ ∑ _k ∈ ρ.covariancePeriodBox,
            ε⁻¹ ^ (dim : ℕ) * C := by
          exact Finset.sum_le_sum fun k _ => by
            unfold etaPeriodTerm
            exact mul_le_mul_of_nonneg_left (hC _)
              (pow_nonneg (inv_nonneg.mpr hε.le) _)
    _ = (ρ.covariancePeriodBox.card : ℝ) *
          (ε⁻¹ ^ (dim : ℕ) * C) := by simp [mul_comm]

/-- Named positive constants give a uniform `O(ε⁻⁴)` bound for the torus
covariance. -/
theorem exists_pos_etaEpsT4_uniform_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : T4,
        ρ.etaEpsT4 ε z ≤ ε⁻¹ ^ (dim : ℕ) * C := by
  obtain ⟨Cη, hCηpos, hCη⟩ := ρ.exists_pos_eta_uniform_bound
  let C : ℝ := (ρ.covariancePeriodBox.card : ℝ) * Cη
  have hboxne : ρ.covariancePeriodBox.Nonempty := by
    refine ⟨0, ?_⟩
    unfold covariancePeriodBox
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hradius : 0 ≤ ρ.covariancePeriodRadius := by
      apply Int.ceil_nonneg
      exact div_nonneg
        (by nlinarith [ρ.radius_pos, Real.pi_pos]) (by positivity)
    exact ⟨neg_nonpos.mpr hradius, hradius⟩
  have hCpos : 0 < C := by
    exact mul_pos (by exact_mod_cast hboxne.card_pos) hCηpos
  refine ⟨C, hCpos, ?_⟩
  intro ε hε hε1 z
  calc
    ρ.etaEpsT4 ε z ≤
        (ρ.covariancePeriodBox.card : ℝ) *
          (ε⁻¹ ^ (dim : ℕ) * Cη) :=
      ρ.etaEpsT4_le_card_mul_of_eta_bound hε hε1 hCη z
    _ = ε⁻¹ ^ (dim : ℕ) * C := by
      unfold C
      ring

end SmoothCutoff

end

end Anderson4D
