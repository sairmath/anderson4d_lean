import Anderson4D.Continuum.Basic

/-!
# Logarithmic asymptotics at the positive side of zero

Small filter lemmas for the critical coupling
`λ_ε = λ / sqrt |log ε|`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open Filter Set
open scoped Topology

/-- The absolute logarithm diverges along `ε ↓ 0`. -/
theorem tendsto_abs_log_nhdsGT_zero_atTop :
    Tendsto (fun ε : ℝ => |Real.log ε|)
      (nhdsWithin 0 (Ioi 0)) atTop :=
  tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

/-- The paper's integer truncation order tends to infinity as
`ε ↓ 0`. -/
theorem tendsto_truncOrder_nhdsGT_zero_atTop :
    Tendsto truncOrder
      (nhdsWithin 0 (Ioi 0)) atTop := by
  exact tendsto_nat_floor_atTop.comp
    tendsto_abs_log_nhdsGT_zero_atTop

/-- Every fixed perturbative order is eventually below the moving paper
cutoff `A = ⌊|log ε|⌋`. -/
theorem eventually_le_truncOrder (B : ℕ) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      B ≤ truncOrder ε :=
  tendsto_truncOrder_nhdsGT_zero_atTop.eventually
    (eventually_ge_atTop B)

/-- One inverse logarithm vanishes along `ε ↓ 0`. -/
theorem tendsto_inv_abs_log_nhdsGT_zero :
    Tendsto (fun ε : ℝ => 1 / |Real.log ε|)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  refine tendsto_abs_log_nhdsGT_zero_atTop.inv_tendsto_atTop.congr' ?_
  filter_upwards with ε
  simp only [Pi.inv_apply, one_div]

/-- A fixed constant divided by the absolute logarithm also vanishes. -/
theorem tendsto_const_div_abs_log_nhdsGT_zero (C : ℝ) :
    Tendsto (fun ε : ℝ => C / |Real.log ε|)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  simpa only [div_eq_mul_inv, one_mul, mul_zero] using
    Tendsto.const_mul C tendsto_inv_abs_log_nhdsGT_zero

/-- The absolute logarithm is eventually strictly positive. -/
theorem eventually_abs_log_pos :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      0 < |Real.log ε| :=
  tendsto_abs_log_nhdsGT_zero_atTop.eventually
    (eventually_gt_atTop 0)

/-- Every fixed positive upper cutoff is eventually respected as
`ε ↓ 0`. -/
theorem eventually_smallScale_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε ≤ δ := by
  show Iic δ ∈ nhdsWithin 0 (Ioi 0)
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  exact
    ⟨Iio δ, Iio_mem_nhds hδ,
      (inter_subset_left.trans Iio_subset_Iic_self)⟩

/-- The logarithmic lower bound used in the deterministic estimates is
automatic at sufficiently small positive scale. -/
theorem eventually_one_le_abs_log :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      1 ≤ |Real.log ε| :=
  tendsto_abs_log_nhdsGT_zero_atTop.eventually
    (eventually_ge_atTop 1)

/-- A positive critical coupling is eventually positive. -/
theorem eventually_lamEps_pos
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      0 < lamEps lam ε := by
  filter_upwards [eventually_abs_log_pos] with ε hlog
  unfold lamEps
  exact div_pos hlam (Real.sqrt_pos.2 hlog)

/-- In particular the critical coupling is eventually nonzero. -/
theorem eventually_lamEps_ne_zero
    {lam : ℝ} (hlam : 0 < lam) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
      lamEps lam ε ≠ 0 :=
  (eventually_lamEps_pos hlam).mono fun _ h => ne_of_gt h

/-- Restricting from the positive punctured side to `(0,1)` preserves
every eventual statement. -/
theorem eventually_nhdsGT_zero_to_Ioo
    {P : ℝ → Prop}
    (hP : ∀ᶠ ε in nhdsWithin 0 (Ioi 0), P ε) :
    ∀ᶠ ε in nhdsWithin 0 (Ioo 0 1), P ε := by
  apply hP.filter_mono
  exact nhdsWithin_mono 0 (fun _ h => h.1)

end Anderson4D
