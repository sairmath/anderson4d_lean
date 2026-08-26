import Anderson4D.Continuum.CovarianceDilationPositivity

/-!
# Euclidean cutoff-covariance derivative majorant

This file constructs the cutoff-dependent positive majorant for repeated
coordinate derivatives of `η`.  It is deliberately Euclidean: periodization
and integration by parts belong to later modules.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Set
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- The unit vector in Euclidean coordinate `i`. -/
def etaCoordDirection (i : Fin dim) : R4 :=
  Pi.single i 1

/-- The same coordinate direction in every derivative slot. -/
def repeatedEtaCoordDirections (r : ℕ) (i : Fin dim) :
    Fin r → R4 :=
  fun _ => etaCoordDirection i

/-- The `r`-fold derivative of `η` in coordinate `i`, evaluated through
mathlib's actual iterated Fréchet derivative. -/
noncomputable def etaCoordDerivative
    (r : ℕ) (i : Fin dim) (x : R4) : ℝ :=
  iteratedFDeriv ℝ r ρ.eta x
    (repeatedEtaCoordDirections r i)

/-- Repeated coordinate derivatives of `η` are continuous. -/
theorem continuous_etaCoordDerivative (r : ℕ) (i : Fin dim) :
    Continuous (ρ.etaCoordDerivative r i) := by
  unfold etaCoordDerivative
  exact
    (ρ.contDiff_eta r).continuous_iteratedFDeriv'.eval
      continuous_const

/-- The support of the full iterated Fréchet derivative is contained in
the original covariance's topological support. -/
theorem support_iteratedFDeriv_eta_subset_tsupport (r : ℕ) :
    Function.support
        (fun x : R4 => iteratedFDeriv ℝ r ρ.eta x) ⊆
      tsupport ρ.eta :=
  support_iteratedFDeriv_subset r

/-- Consequently the full iterated derivative vanishes outside
`tsupport η`. -/
theorem iteratedFDeriv_eta_eq_zero_of_not_mem_tsupport
    (r : ℕ) {x : R4} (hx : x ∉ tsupport ρ.eta) :
    iteratedFDeriv ℝ r ρ.eta x = 0 := by
  by_contra hne
  exact hx (ρ.support_iteratedFDeriv_eta_subset_tsupport r hne)

/-- The repeated coordinate derivative also vanishes outside
`tsupport η`. -/
theorem etaCoordDerivative_eq_zero_of_not_mem_tsupport
    (r : ℕ) (i : Fin dim) {x : R4}
    (hx : x ∉ tsupport ρ.eta) :
    ρ.etaCoordDerivative r i x = 0 := by
  unfold etaCoordDerivative
  rw [ρ.iteratedFDeriv_eta_eq_zero_of_not_mem_tsupport r hx]
  simp

/-- Explicit support inclusion for the scalar coordinate derivative. -/
theorem support_etaCoordDerivative_subset_tsupport
    (r : ℕ) (i : Fin dim) :
    Function.support (ρ.etaCoordDerivative r i) ⊆
      tsupport ρ.eta := by
  intro x hx
  by_contra hmem
  exact hx
    (ρ.etaCoordDerivative_eq_zero_of_not_mem_tsupport
      r i hmem)

/-- Evaluation on repeated unit coordinate vectors is bounded by the
operator norm of the full iterated derivative. -/
theorem abs_etaCoordDerivative_le_norm_iteratedFDeriv
    (r : ℕ) (i : Fin dim) (x : R4) :
    |ρ.etaCoordDerivative r i x| ≤
      ‖iteratedFDeriv ℝ r ρ.eta x‖ := by
  rw [← Real.norm_eq_abs]
  unfold etaCoordDerivative
  calc
    ‖iteratedFDeriv ℝ r ρ.eta x
        (repeatedEtaCoordDirections r i)‖ ≤
        ‖iteratedFDeriv ℝ r ρ.eta x‖ *
          ∏ j : Fin r,
            ‖repeatedEtaCoordDirections r i j‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ r ρ.eta x‖ := by
      simp [repeatedEtaCoordDirections, etaCoordDirection,
        Pi.norm_single]

/-- Every fixed derivative order has a positive global operator-norm
bound depending only on the named cutoff. -/
theorem exists_pos_etaIteratedFDeriv_bound (r : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ x : R4, ‖iteratedFDeriv ℝ r ρ.eta x‖ ≤ B := by
  obtain ⟨B, hB⟩ :=
    (ρ.contDiff_eta r).continuous_iteratedFDeriv'
      |>.bounded_above_of_compact_support
        (ρ.hasCompactSupport_eta.iteratedFDeriv r)
  refine ⟨max B 1,
    lt_of_lt_of_le zero_lt_one (le_max_right B 1),
    fun x => (hB x).trans (le_max_left B 1)⟩

/-- The auxiliary covariance has a strictly positive lower bound on the
compact support of the original covariance. -/
theorem exists_pos_auxiliaryEta_lowerBound_on_tsupport :
    ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ tsupport ρ.eta, c ≤ ρ.auxiliaryCutoff.eta x := by
  exact ρ.hasCompactSupport_eta.exists_forall_le'
    ρ.auxiliaryCutoff.continuous_eta.continuousOn
    (fun x hx => ρ.auxiliaryCutoff_eta_pos_on_tsupport hx)

/-! ## Uniform constants through order eight -/

/-- A single positive operator-norm bound for derivative orders `0,...,8`.
It depends on `ρ`, as it must. -/
theorem exists_pos_etaIteratedFDeriv_bound_upto_eight :
    ∃ B : ℝ, 0 < B ∧
      ∀ r : ℕ, r ≤ 8 →
        ∀ x : R4, ‖iteratedFDeriv ℝ r ρ.eta x‖ ≤ B := by
  have hall :
      ∀ r : ℕ, ∃ B : ℝ, 0 < B ∧
        ∀ x : R4, ‖iteratedFDeriv ℝ r ρ.eta x‖ ≤ B :=
    fun r => ρ.exists_pos_etaIteratedFDeriv_bound r
  choose bound hbound_pos hbound using hall
  let B : ℝ := ∑ r ∈ Finset.range 9, bound r
  have hnonneg :
      ∀ r ∈ Finset.range 9, 0 ≤ bound r :=
    fun r _ => (hbound_pos r).le
  have hzero_mem : 0 ∈ Finset.range 9 := by simp
  have hBpos : 0 < B := by
    exact (hbound_pos 0).trans_le
      (Finset.single_le_sum hnonneg hzero_mem)
  refine ⟨B, hBpos, fun r hr x => ?_⟩
  have hr_mem : r ∈ Finset.range 9 := by
    simp
    omega
  exact (hbound r x).trans
    (Finset.single_le_sum hnonneg hr_mem)

/-- The named numerator constant, selected after fixing `ρ`. -/
noncomputable def etaIteratedFDerivBound : ℝ :=
  Classical.choose ρ.exists_pos_etaIteratedFDeriv_bound_upto_eight

theorem etaIteratedFDerivBound_pos :
    0 < ρ.etaIteratedFDerivBound :=
  (Classical.choose_spec
    ρ.exists_pos_etaIteratedFDeriv_bound_upto_eight).1

theorem norm_iteratedFDeriv_eta_le_etaIteratedFDerivBound
    {r : ℕ} (hr : r ≤ 8) (x : R4) :
    ‖iteratedFDeriv ℝ r ρ.eta x‖ ≤
      ρ.etaIteratedFDerivBound :=
  (Classical.choose_spec
    ρ.exists_pos_etaIteratedFDeriv_bound_upto_eight).2 r hr x

/-- The named positive lower bound for the auxiliary covariance on
`tsupport η`. -/
noncomputable def auxiliaryEtaLowerBound : ℝ :=
  Classical.choose ρ.exists_pos_auxiliaryEta_lowerBound_on_tsupport

theorem auxiliaryEtaLowerBound_pos :
    0 < ρ.auxiliaryEtaLowerBound :=
  (Classical.choose_spec
    ρ.exists_pos_auxiliaryEta_lowerBound_on_tsupport).1

theorem auxiliaryEtaLowerBound_le
    {x : R4} (hx : x ∈ tsupport ρ.eta) :
    ρ.auxiliaryEtaLowerBound ≤ ρ.auxiliaryCutoff.eta x :=
  (Classical.choose_spec
    ρ.exists_pos_auxiliaryEta_lowerBound_on_tsupport).2 x hx

/-- The cutoff-dependent constant in the Euclidean derivative majorant. -/
noncomputable def etaDerivativeMajorantConstant : ℝ :=
  ρ.etaIteratedFDerivBound / ρ.auxiliaryEtaLowerBound

theorem etaDerivativeMajorantConstant_pos :
    0 < ρ.etaDerivativeMajorantConstant := by
  unfold etaDerivativeMajorantConstant
  exact div_pos ρ.etaIteratedFDerivBound_pos
    ρ.auxiliaryEtaLowerBound_pos

/-- Every repeated coordinate derivative through order eight is dominated
globally by the covariance of the named auxiliary cutoff. -/
theorem abs_etaCoordDerivative_le_majorant
    {r : ℕ} (hr : r ≤ 8) (i : Fin dim) (x : R4) :
    |ρ.etaCoordDerivative r i x| ≤
      ρ.etaDerivativeMajorantConstant *
        ρ.auxiliaryCutoff.eta x := by
  by_cases hx : x ∈ tsupport ρ.eta
  · have hderiv :
        |ρ.etaCoordDerivative r i x| ≤
          ρ.etaIteratedFDerivBound :=
      (ρ.abs_etaCoordDerivative_le_norm_iteratedFDeriv r i x).trans
        (ρ.norm_iteratedFDeriv_eta_le_etaIteratedFDerivBound hr x)
    have hlower := ρ.auxiliaryEtaLowerBound_le hx
    calc
      |ρ.etaCoordDerivative r i x| ≤
          ρ.etaIteratedFDerivBound := hderiv
      _ =
          ρ.etaDerivativeMajorantConstant *
            ρ.auxiliaryEtaLowerBound := by
        unfold etaDerivativeMajorantConstant
        field_simp [ρ.auxiliaryEtaLowerBound_pos.ne']
      _ ≤
          ρ.etaDerivativeMajorantConstant *
            ρ.auxiliaryCutoff.eta x :=
        mul_le_mul_of_nonneg_left hlower
          ρ.etaDerivativeMajorantConstant_pos.le
  · rw [ρ.etaCoordDerivative_eq_zero_of_not_mem_tsupport r i hx,
      abs_zero]
    exact mul_nonneg ρ.etaDerivativeMajorantConstant_pos.le
      (ρ.auxiliaryCutoff.eta_nonneg x)

end SmoothCutoff

end

end Anderson4D
