import Anderson4D.Continuum.GreenBounds
import Anderson4D.Continuum.FourPointFourier

/-!
# R324PermCross: a uniform positive floor for the Green's function

Off the single junk point `z = 0`, the heat-integral Green's function
of `1 - Δ` on `𝕋⁴` is bounded *below* by the explicit positive constant
`g₀ = e⁻² (8π)⁻² e^{-π²}`: the defining time integral is genuinely
convergent there, and already the `t ∈ (1,2]` window of the `k = 0`
Gaussian summand carries this much mass.

This floor is the geometric input of the R324PermCross nonexistence theorem: every
physical pure-cross pairing integral is bounded below by a fixed
exponential `c^m`, so the `m!`-member bijection fibre defeats any
`K^m |log ε|^{m-1}` budget at a fixed admissible scale.

Main results:

* `r324PermCross_integrableOn_greenIntegrand` — for `z ≠ 0` the
  integrand `t ↦ e^{-t} Θ(t,z)` is integrable on `(0,∞)`;
* `r324PermCross_greenFn_floor` — `g₀ ≤ greenFn z` for every `z ≠ 0`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory Set Real
open scoped BigOperators

/-! ## Geometry of the canonical lift -/

/-- The canonical lift has squared length at most `4π²`. -/
theorem r324PermCross_torusDistSq_le (z : T4) :
    torusDistSq z ≤ 4 * Real.pi ^ 2 := by
  have h : ∀ i : Fin dim, torusLift z i ^ 2 ≤ Real.pi ^ 2 := by
    intro i
    have hIco := torusLift_mem_Ico z i
    have h1 : -Real.pi ≤ torusLift z i := hIco.1
    have h2 : torusLift z i < Real.pi := hIco.2
    nlinarith
  calc torusDistSq z = ∑ i, torusLift z i ^ 2 := rfl
    _ ≤ ∑ _i : Fin dim, Real.pi ^ 2 :=
        Finset.sum_le_sum fun i _ => h i
    _ = 4 * Real.pi ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ]
        norm_num [dim]

/-- Vanishing lifted distance forces the origin: `torusDistSq` only
vanishes at `z = 0`. -/
theorem r324PermCross_eq_zero_of_torusDistSq {z : T4}
    (h : torusDistSq z = 0) : z = 0 := by
  have hlift : ∀ i, torusLift z i = 0 := by
    intro i
    have hsum : ∑ j, torusLift z j ^ 2 = 0 := h
    have hz :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (torusLift z j))).mp hsum i
        (Finset.mem_univ i)
    exact pow_eq_zero_iff two_ne_zero |>.mp hz
  funext i
  have hzi : z i =
      ((torusLift z i : ℝ) : AddCircle (2 * Real.pi)) :=
    (AddCircle.coe_equivIco (a := -Real.pi) (y := z i)).symm
  rw [Pi.zero_apply, hzi, hlift i]
  norm_cast

/-- Positive lifted distance off the origin. -/
theorem r324PermCross_torusDistSq_pos {z : T4} (hz : z ≠ 0) :
    0 < torusDistSq z :=
  lt_of_le_of_ne (torusDistSq_nonneg z)
    (fun h0 => hz (r324PermCross_eq_zero_of_torusDistSq h0.symm))

/-- Componentwise lattice bound: for `|a| ≤ π` and `m ∈ ℤ`,
`(a + 2πm)² ≥ a²/2 + (π²/2) m²`. -/
theorem r324PermCross_coord_sq {a : ℝ} (ha : |a| ≤ Real.pi) (m : ℤ) :
    a ^ 2 / 2 + Real.pi ^ 2 / 2 * (m : ℝ) ^ 2 ≤
      (a + 2 * Real.pi * (m : ℝ)) ^ 2 := by
  have hpi := Real.pi_pos
  have ha2 : a ^ 2 ≤ Real.pi ^ 2 := by
    have := abs_le.mp ha
    nlinarith
  rcases eq_or_ne m 0 with rfl | hm
  · push_cast
    nlinarith [sq_nonneg a]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hm
    have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      nlinarith [sq_abs (m : ℝ)]
    have htri : 2 * Real.pi * |(m : ℝ)| - |a| ≤
        |a + 2 * Real.pi * (m : ℝ)| := by
      have h2 : |2 * Real.pi * (m : ℝ)| - |a| ≤
          |a + 2 * Real.pi * (m : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (2 * Real.pi * (m : ℝ)) (-a)
        have habs : |2 * Real.pi * (m : ℝ) - -a| =
            |a + 2 * Real.pi * (m : ℝ)| := by
          rw [sub_neg_eq_add, add_comm]
        rw [habs, abs_neg] at this
        linarith
      have h3 : |2 * Real.pi * (m : ℝ)| = 2 * Real.pi * |(m : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      linarith [h2, h3.symm.le]
    have hlow : Real.pi * |(m : ℝ)| ≤ |a + 2 * Real.pi * (m : ℝ)| := by
      have : Real.pi * |(m : ℝ)| ≤ 2 * Real.pi * |(m : ℝ)| - |a| := by
        nlinarith [ha, h1]
      linarith
    have hsq : Real.pi ^ 2 * (m : ℝ) ^ 2 ≤
        (a + 2 * Real.pi * (m : ℝ)) ^ 2 := by
      have h5 := mul_self_le_mul_self
        (by positivity : (0 : ℝ) ≤ Real.pi * |(m : ℝ)|) hlow
      have h6 : |a + 2 * Real.pi * (m : ℝ)| * |a + 2 * Real.pi * (m : ℝ)| =
          (a + 2 * Real.pi * (m : ℝ)) ^ 2 := by
        rw [← sq_abs]; ring
      have h7 : Real.pi * |(m : ℝ)| * (Real.pi * |(m : ℝ)|) =
          Real.pi ^ 2 * (m : ℝ) ^ 2 := by
        rw [← sq_abs (m : ℝ)]; ring
      rw [h6, h7] at h5
      exact h5
    nlinarith [hsq, ha2, hm2, sq_nonneg (m : ℝ)]

/-- The lattice-point distance dominates half the lifted distance plus a
Gaussian lattice weight. -/
theorem r324PermCross_latticeDistSq_ge (z : T4) (k : Z4) :
    torusDistSq z / 2 +
        Real.pi ^ 2 / 2 * ∑ i, ((k i : ℝ)) ^ 2 ≤
      latticeDistSq z k := by
  rw [latticeDistSq, torusDistSq, Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  refine r324PermCross_coord_sq ?_ (k i)
  have hIco := torusLift_mem_Ico z i
  rw [abs_le]
  exact ⟨hIco.1, hIco.2.le⟩

/-! ## Gaussian lattice sums -/

/-- Summability of the one-dimensional Gaussian lattice sum. -/
theorem r324PermCross_summable_exp_int {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2) := by
  have hgeo : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith))
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hgeo.of_nonneg_of_le (fun n => (Real.exp_pos _).le) fun n => ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast Nat.le_self_pow two_ne_zero n
    push_cast
    nlinarith
  · refine hgeo.of_nonneg_of_le (fun n => (Real.exp_pos _).le) fun n => ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [hc, sq_nonneg ((n : ℝ)), Nat.cast_nonneg (α := ℝ) n]

/-- One-dimensional Gaussian tail: `∑_{m ∈ ℤ} e^{-c m²} ≤ 2 (1 - e^{-c})⁻¹`. -/
theorem r324PermCross_tsum_exp_int_le {c : ℝ} (hc : 0 < c) :
    (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ≤
      2 * (1 - Real.exp (-c))⁻¹ := by
  set r : ℝ := Real.exp (-c) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hrdef, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeo : Summable fun n : ℕ => r ^ n :=
    summable_geometric_of_lt_one hr0.le hr1
  have hle : ∀ n : ℕ, Real.exp (-c * ((n : ℤ) : ℝ) ^ 2) ≤ r ^ n := by
    intro n
    rw [hrdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast Nat.le_self_pow two_ne_zero n
    push_cast
    nlinarith
  have hleneg : ∀ n : ℕ,
      Real.exp (-c * ((-((n : ℤ)) - 1 : ℤ) : ℝ) ^ 2) ≤ r ^ n := by
    intro n
    rw [hrdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [hc, sq_nonneg ((n : ℝ)), Nat.cast_nonneg (α := ℝ) n]
  have hs1 : Summable fun n : ℕ => Real.exp (-c * ((n : ℤ) : ℝ) ^ 2) :=
    hgeo.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hle
  have hs2 : Summable fun n : ℕ =>
      Real.exp (-c * ((-((n : ℤ)) - 1 : ℤ) : ℝ) ^ 2) :=
    hgeo.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hleneg
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2)) hs1 (by
      refine hs2.congr fun n => ?_
      congr 2
      push_cast
      ring)
  have hgeosum : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
    tsum_geometric_of_lt_one hr0.le hr1
  have hb1 : (∑' n : ℕ, Real.exp (-c * ((n : ℤ) : ℝ) ^ 2)) ≤ (1 - r)⁻¹ := by
    rw [← hgeosum]
    exact hs1.tsum_le_tsum hle hgeo
  have hs2' : Summable fun n : ℕ =>
      Real.exp (-c * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) := by
    refine hs2.congr fun n => ?_
    congr 2
    push_cast
    ring
  have hb2 : (∑' n : ℕ,
      Real.exp (-c * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) ≤ (1 - r)⁻¹ := by
    rw [← hgeosum]
    refine hs2'.tsum_le_tsum (fun n => ?_) hgeo
    have := hleneg n
    have harg : ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 =
        ((-((n : ℤ)) - 1 : ℤ) : ℝ) ^ 2 := by
      push_cast
      ring
    rw [harg]
    exact this
  calc (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) =
      (∑' n : ℕ, Real.exp (-c * ((n : ℤ) : ℝ) ^ 2)) +
        ∑' n : ℕ, Real.exp (-c * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2) :=
      hsplit
    _ ≤ (1 - r)⁻¹ + (1 - r)⁻¹ := add_le_add hb1 hb2
    _ = 2 * (1 - r)⁻¹ := by ring

/-- Nonnegative product-form lattice sums over `Fin n → ℤ` factor into
powers of the one-dimensional sum. -/
theorem r324PermCross_summable_tsum_pi_prod {g : ℤ → ℝ}
    (h0 : ∀ m, 0 ≤ g m) (hg : Summable g) :
    ∀ n : ℕ,
      (Summable fun k : Fin n → ℤ => ∏ i, g (k i)) ∧
        (∑' k : Fin n → ℤ, ∏ i, g (k i)) = (∑' m, g m) ^ n := by
  intro n
  induction n with
  | zero =>
      constructor
      · exact Summable.of_finite
      · rw [pow_zero]
        have hval : ∀ k : Fin 0 → ℤ, (∏ i, g (k i)) = 1 := by
          intro k
          simp
        calc (∑' k : Fin 0 → ℤ, ∏ i, g (k i)) =
            ∑' _k : Fin 0 → ℤ, (1 : ℝ) := by
              exact tsum_congr hval
          _ = 1 := by
              rw [tsum_eq_single (fun i => i.elim0)
                (fun k' hk' => absurd (Subsingleton.elim _ _) hk')]
  | succ n ih =>
      have hg0 : (0 : ℤ → ℝ) ≤ g := fun m => h0 m
      have hp0 : (0 : (Fin n → ℤ) → ℝ) ≤ fun k => ∏ i, g (k i) :=
        fun k => Finset.prod_nonneg fun i _ => h0 _
      have hstep :
          Summable fun p : ℤ × (Fin n → ℤ) =>
            g p.1 * ∏ i, g (p.2 i) :=
        Summable.mul_of_nonneg hg ih.1 hg0 hp0
      have hequiv :
          Summable fun k : Fin (n + 1) → ℤ => ∏ i, g (k i) := by
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
        refine hstep.congr fun p => ?_
        simp [Fin.consEquiv, Fin.prod_univ_succ]
      refine ⟨hequiv, ?_⟩
      have h1 : (∑' k : Fin (n + 1) → ℤ, ∏ i, g (k i)) =
          ∑' p : ℤ × (Fin n → ℤ), g p.1 * ∏ i, g (p.2 i) := by
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).tsum_eq
          (fun k : Fin (n + 1) → ℤ => ∏ i, g (k i))]
        refine tsum_congr fun p => ?_
        simp [Fin.consEquiv, Fin.prod_univ_succ]
      have h2 : (∑' p : ℤ × (Fin n → ℤ), g p.1 * ∏ i, g (p.2 i)) =
          ∑' a : ℤ, ∑' b : Fin n → ℤ, g a * ∏ i, g (b i) :=
        hstep.tsum_prod' fun a => ih.1.mul_left (g a)
      have h3 : (∑' a : ℤ, ∑' b : Fin n → ℤ, g a * ∏ i, g (b i)) =
          ∑' a : ℤ, g a * ∑' b : Fin n → ℤ, ∏ i, g (b i) := by
        refine tsum_congr fun a => ?_
        exact tsum_mul_left
      rw [h1, h2, h3, tsum_mul_right, ih.2, pow_succ]
      ring

/-- The `ℤ⁴` Gaussian lattice sum is the fourth power of the
one-dimensional one. -/
theorem r324PermCross_tsum_gaussZ4 {c : ℝ} (hc : 0 < c) :
    (Summable fun k : Z4 =>
        Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2)) ∧
      (∑' k : Z4, Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2)) =
        (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ^ (dim : ℕ) := by
  have hprod := r324PermCross_summable_tsum_pi_prod
    (g := fun m : ℤ => Real.exp (-c * (m : ℝ) ^ 2))
    (fun m => (Real.exp_pos _).le)
    (r324PermCross_summable_exp_int hc) dim
  have hfun : ∀ k : Z4,
      Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2) =
        ∏ i, Real.exp (-c * ((k i : ℝ)) ^ 2) := by
    intro k
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  constructor
  · exact hprod.1.congr fun k => (hfun k).symm
  · calc (∑' k : Z4, Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2)) =
        ∑' k : Z4, ∏ i, Real.exp (-c * ((k i : ℝ)) ^ 2) :=
          tsum_congr hfun
      _ = (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ^ (dim : ℕ) :=
          hprod.2

/-! ## The two heat-kernel majorants -/

/-- The heat normalization as an honest inverse square. -/
theorem r324PermCross_heat_coeff (t : ℝ) :
    (4 * Real.pi * t) ^ (-2 : ℤ) =
      (16 * Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg,
    zpow_natCast, ← mul_inv]
  congr 1
  ring

/-- Nonnegativity of the heat normalization. -/
theorem r324PermCross_heat_coeff_nonneg (t : ℝ) :
    0 ≤ (4 * Real.pi * t) ^ (-2 : ℤ) := by
  rw [r324PermCross_heat_coeff]
  positivity

/-- The `ℤ⁴` Gaussian constant of the small-time majorant. -/
def r324PermCrossGaussConst : ℝ :=
  ∑' k : Z4, Real.exp (-(Real.pi ^ 2 / 8) * ∑ i, ((k i : ℝ)) ^ 2)

theorem r324PermCrossGaussConst_nonneg :
    0 ≤ r324PermCrossGaussConst :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

/-- Small-time bound: for `0 < t ≤ 1`,
`e^{-t} Θ(t,z) ≤ (16π²)⁻¹ C_Z · t⁻² e^{-(d/8)/t}`. -/
theorem r324PermCross_heat_small {z : T4} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.exp (-t) * heatKernelT4 t z ≤
      (16 * Real.pi ^ 2)⁻¹ * r324PermCrossGaussConst *
        ((t ^ 2)⁻¹ * Real.exp (-(torusDistSq z / 8 / t))) := by
  have hπ8 : (0 : ℝ) < Real.pi ^ 2 / 8 := by positivity
  have hgauss := r324PermCross_tsum_gaussZ4 hπ8
  set S : Z4 → ℝ := fun k => ∑ i, ((k i : ℝ)) ^ 2 with hSdef
  set d : ℝ := torusDistSq z with hddef
  have hd0 : 0 ≤ d := torusDistSq_nonneg z
  set A : ℝ := (4 * Real.pi * t) ^ (-2 : ℤ) *
    Real.exp (-(d / 8 / t)) with hAdef
  have hA0 : 0 ≤ A :=
    mul_nonneg (r324PermCross_heat_coeff_nonneg t) (Real.exp_pos _).le
  have hterm : ∀ k : Z4,
      (4 * Real.pi * t) ^ (-2 : ℤ) *
          Real.exp (-latticeDistSq z k / (4 * t)) ≤
        A * Real.exp (-(Real.pi ^ 2 / 8) * S k) := by
    intro k
    have hprod : A * Real.exp (-(Real.pi ^ 2 / 8) * S k) =
        (4 * Real.pi * t) ^ (-2 : ℤ) *
          Real.exp (-(d / 8 / t) + -(Real.pi ^ 2 / 8) * S k) := by
      rw [hAdef, Real.exp_add]
      ring
    rw [hprod]
    refine mul_le_mul_of_nonneg_left ?_
      (r324PermCross_heat_coeff_nonneg t)
    apply Real.exp_le_exp.mpr
    have hD := r324PermCross_latticeDistSq_ge z k
    have hS0 : (0 : ℝ) ≤ S k :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hSt : S k ≤ S k / t := by
      rw [le_div_iff₀ ht]
      nlinarith
    have hkey : d / 8 / t + Real.pi ^ 2 / 8 * S k ≤
        latticeDistSq z k / (4 * t) := by
      have h1 : (d / 2 + Real.pi ^ 2 / 2 * S k) / (4 * t) ≤
          latticeDistSq z k / (4 * t) := by
        gcongr
      have h2 : (d / 2 + Real.pi ^ 2 / 2 * S k) / (4 * t) =
          d / 8 / t + Real.pi ^ 2 / 8 * (S k / t) := by
        field_simp
        ring
      have h3 : Real.pi ^ 2 / 8 * S k ≤
          Real.pi ^ 2 / 8 * (S k / t) := by
        have hc : (0 : ℝ) ≤ Real.pi ^ 2 / 8 := by positivity
        exact mul_le_mul_of_nonneg_left hSt hc
      rw [h2] at h1
      linarith
    have hgoal : -latticeDistSq z k / (4 * t) =
        -(latticeDistSq z k / (4 * t)) := by ring
    rw [hgoal]
    linarith
  have hΘ : heatKernelT4 t z ≤ A * r324PermCrossGaussConst := by
    have hsumL := summable_heatKernel_terms ht z
    have hsumR : Summable fun k : Z4 =>
        A * Real.exp (-(Real.pi ^ 2 / 8) * S k) :=
      (hgauss.1).mul_left A
    calc heatKernelT4 t z =
        ∑' k : Z4, (4 * Real.pi * t) ^ (-2 : ℤ) *
          Real.exp (-latticeDistSq z k / (4 * t)) := rfl
      _ ≤ ∑' k : Z4, A * Real.exp (-(Real.pi ^ 2 / 8) * S k) :=
          hsumL.tsum_le_tsum hterm hsumR
      _ = A * r324PermCrossGaussConst := tsum_mul_left
  have hexp1 : Real.exp (-t) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hΘ0 : 0 ≤ heatKernelT4 t z := heatKernelT4_nonneg t z
  calc Real.exp (-t) * heatKernelT4 t z ≤ heatKernelT4 t z :=
      mul_le_of_le_one_left hΘ0 hexp1
    _ ≤ A * r324PermCrossGaussConst := hΘ
    _ = (16 * Real.pi ^ 2)⁻¹ * r324PermCrossGaussConst *
        ((t ^ 2)⁻¹ * Real.exp (-(d / 8 / t))) := by
        rw [hAdef, r324PermCross_heat_coeff]
        ring

/-- The constant of the large-time majorant. -/
def r324PermCrossLargeConst : ℝ :=
  (16 * Real.pi ^ 2)⁻¹ *
    (16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) * 16

/-- Large-time bound: for `1 ≤ t`, `e^{-t} Θ(t,z) ≤ C_L e^{-t/2}`. -/
theorem r324PermCross_heat_large (z : T4) {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) * heatKernelT4 t z ≤
      r324PermCrossLargeConst * Real.exp (-(t / 2)) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  set c : ℝ := Real.pi ^ 2 / (8 * t) with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hgauss := r324PermCross_tsum_gaussZ4 hc0
  have hterm : ∀ k : Z4,
      (4 * Real.pi * t) ^ (-2 : ℤ) *
          Real.exp (-latticeDistSq z k / (4 * t)) ≤
        (4 * Real.pi * t) ^ (-2 : ℤ) *
          Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2) := by
    intro k
    refine mul_le_mul_of_nonneg_left ?_
      (r324PermCross_heat_coeff_nonneg t)
    apply Real.exp_le_exp.mpr
    have hD := r324PermCross_latticeDistSq_ge z k
    have hd0 : 0 ≤ torusDistSq z := torusDistSq_nonneg z
    have hkey : c * ∑ i, ((k i : ℝ)) ^ 2 ≤
        latticeDistSq z k / (4 * t) := by
      have h1 : (Real.pi ^ 2 / 2 * ∑ i, ((k i : ℝ)) ^ 2) / (4 * t) ≤
          latticeDistSq z k / (4 * t) := by
        gcongr
        linarith
      have h2 : (Real.pi ^ 2 / 2 * ∑ i, ((k i : ℝ)) ^ 2) / (4 * t) =
          c * ∑ i, ((k i : ℝ)) ^ 2 := by
        rw [hcdef]
        field_simp
        ring
      linarith
    have hgoal : -latticeDistSq z k / (4 * t) =
        -(latticeDistSq z k / (4 * t)) := by ring
    rw [hgoal]
    linarith
  have hone : (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ≤
      16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2 * t := by
    have h1 := r324PermCross_tsum_exp_int_le hc0
    have hlow : c * Real.exp (-c) ≤ 1 - Real.exp (-c) := by
      have h2 := Real.add_one_le_exp c
      have h3 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
      have h4 : (c + 1) * Real.exp (-c) ≤ Real.exp c * Real.exp (-c) :=
        mul_le_mul_of_nonneg_right h2 h3.le
      rw [← Real.exp_add] at h4
      simp only [add_neg_cancel, Real.exp_zero] at h4
      nlinarith
    have hpos : (0 : ℝ) < c * Real.exp (-c) := by positivity
    have hinv : (1 - Real.exp (-c))⁻¹ ≤ (c * Real.exp (-c))⁻¹ :=
      inv_anti₀ hpos hlow
    have hval : (c * Real.exp (-c))⁻¹ =
        8 * t / Real.pi ^ 2 * Real.exp c := by
      rw [mul_inv, Real.exp_neg, inv_inv, hcdef, inv_div]
    have hec : Real.exp c ≤ Real.exp (Real.pi ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr
      rw [hcdef]
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 8)]
      nlinarith [sq_nonneg Real.pi, Real.pi_pos]
    have h5 : (c * Real.exp (-c))⁻¹ ≤
        8 * t / Real.pi ^ 2 * Real.exp (Real.pi ^ 2 / 8) := by
      rw [hval]
      exact mul_le_mul_of_nonneg_left hec (by positivity)
    calc (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ≤
        2 * (1 - Real.exp (-c))⁻¹ := h1
      _ ≤ 2 * (c * Real.exp (-c))⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ 2 * (8 * t / Real.pi ^ 2 * Real.exp (Real.pi ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_left h5 (by norm_num)
      _ = 16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2 * t := by
          ring
  have hΘ : heatKernelT4 t z ≤
      (16 * Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ *
        ((16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) *
          t ^ (dim : ℕ)) := by
    have hsumL := summable_heatKernel_terms ht0 z
    have hsumR : Summable fun k : Z4 =>
        (4 * Real.pi * t) ^ (-2 : ℤ) *
          Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2) :=
      (hgauss.1).mul_left _
    have hstep1 : heatKernelT4 t z ≤
        (4 * Real.pi * t) ^ (-2 : ℤ) *
          (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ^ (dim : ℕ) := by
      calc heatKernelT4 t z =
          ∑' k : Z4, (4 * Real.pi * t) ^ (-2 : ℤ) *
            Real.exp (-latticeDistSq z k / (4 * t)) := rfl
        _ ≤ ∑' k : Z4, (4 * Real.pi * t) ^ (-2 : ℤ) *
            Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2) :=
            hsumL.tsum_le_tsum hterm hsumR
        _ = (4 * Real.pi * t) ^ (-2 : ℤ) *
            ∑' k : Z4, Real.exp (-c * ∑ i, ((k i : ℝ)) ^ 2) :=
            tsum_mul_left
        _ = (4 * Real.pi * t) ^ (-2 : ℤ) *
            (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ^ (dim : ℕ) := by
            rw [hgauss.2]
    have hpow : (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ^ (dim : ℕ) ≤
        (16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) *
          t ^ (dim : ℕ) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀
        (tsum_nonneg fun m => (Real.exp_pos _).le) hone _
    calc heatKernelT4 t z ≤
        (4 * Real.pi * t) ^ (-2 : ℤ) *
          (∑' m : ℤ, Real.exp (-c * (m : ℝ) ^ 2)) ^ (dim : ℕ) := hstep1
      _ ≤ (4 * Real.pi * t) ^ (-2 : ℤ) *
          ((16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) *
            t ^ (dim : ℕ)) :=
          mul_le_mul_of_nonneg_left hpow
            (r324PermCross_heat_coeff_nonneg t)
      _ = (16 * Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ *
          ((16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) *
            t ^ (dim : ℕ)) := by
          rw [r324PermCross_heat_coeff]
  have hsq : t ^ 2 ≤ 16 * Real.exp (t / 2) := by
    have h1 := Real.add_one_le_exp (t / 4)
    have h2 : (0 : ℝ) ≤ t / 4 + 1 := by linarith
    have h3 : (t / 4 + 1) ^ 2 ≤ Real.exp (t / 4) ^ 2 := by
      exact pow_le_pow_left₀ h2 h1 2
    have h4 : Real.exp (t / 4) ^ 2 = Real.exp (t / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [sq_nonneg t, ht0.le]
  have hfinal : (t ^ 2)⁻¹ * t ^ (dim : ℕ) * Real.exp (-t) ≤
      16 * Real.exp (-(t / 2)) := by
    have hteq : (t ^ 2)⁻¹ * t ^ (dim : ℕ) = t ^ 2 := by
      have h4 : t ^ (dim : ℕ) = t ^ 2 * t ^ 2 := by
        norm_num [dim]
        ring
      rw [h4, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [hteq]
    have h5 : t ^ 2 * Real.exp (-t) ≤
        16 * Real.exp (t / 2) * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    calc t ^ 2 * Real.exp (-t) ≤
        16 * Real.exp (t / 2) * Real.exp (-t) := h5
      _ = 16 * Real.exp (-(t / 2)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hΘ0 : 0 ≤ heatKernelT4 t z := heatKernelT4_nonneg t z
  calc Real.exp (-t) * heatKernelT4 t z ≤
      Real.exp (-t) *
        ((16 * Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ *
          ((16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) *
            t ^ (dim : ℕ))) :=
      mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le
    _ = (16 * Real.pi ^ 2)⁻¹ *
        (16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) *
          ((t ^ 2)⁻¹ * t ^ (dim : ℕ) * Real.exp (-t)) := by ring
    _ ≤ (16 * Real.pi ^ 2)⁻¹ *
        (16 * Real.exp (Real.pi ^ 2 / 8) / Real.pi ^ 2) ^ (dim : ℕ) *
          (16 * Real.exp (-(t / 2))) := by
        refine mul_le_mul_of_nonneg_left hfinal ?_
        positivity
    _ = r324PermCrossLargeConst * Real.exp (-(t / 2)) := by
        rw [r324PermCrossLargeConst]
        ring

/-! ## Integrability and the floor -/

/-- Off the origin, the Green time integrand is integrable on `(0,∞)`. -/
theorem r324PermCross_integrableOn_greenIntegrand {z : T4} (hz : z ≠ 0) :
    IntegrableOn (fun t => Real.exp (-t) * heatKernelT4 t z)
      (Ioi (0 : ℝ)) := by
  have hmeas : Measurable fun t : ℝ =>
      Real.exp (-t) * heatKernelT4 t z :=
    (Real.measurable_exp.comp measurable_neg).mul
      (measurable_heatKernelT4_prod.comp
        (measurable_id.prodMk measurable_const))
  have hnn : ∀ t : ℝ, 0 ≤ Real.exp (-t) * heatKernelT4 t z :=
    fun t => mul_nonneg (Real.exp_pos _).le (heatKernelT4_nonneg _ _)
  have hd : (0 : ℝ) < torusDistSq z / 8 := by
    have := r324PermCross_torusDistSq_pos hz
    positivity
  have hsmall : IntegrableOn
      (fun t => Real.exp (-t) * heatKernelT4 t z) (Ioc (0 : ℝ) 1) := by
    have hmaj : IntegrableOn
        (fun t => (16 * Real.pi ^ 2)⁻¹ * r324PermCrossGaussConst *
          ((t ^ 2)⁻¹ * Real.exp (-(torusDistSq z / 8 / t))))
        (Ioc (0 : ℝ) 1) :=
      (((integrableOn_inv_sq_exp hd).mono_set
        Ioc_subset_Ioi_self).const_mul _)
    refine hmaj.mono' hmeas.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
    exact r324PermCross_heat_small ht.1 ht.2
  have hlarge : IntegrableOn
      (fun t => Real.exp (-t) * heatKernelT4 t z) (Ioi (1 : ℝ)) := by
    have hbase : IntegrableOn
        (fun t : ℝ => Real.exp (-(2⁻¹ : ℝ) * t)) (Ioi (1 : ℝ)) :=
      exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 2⁻¹)
    have hmaj : IntegrableOn
        (fun t : ℝ => r324PermCrossLargeConst *
          Real.exp (-(2⁻¹ : ℝ) * t)) (Ioi (1 : ℝ)) :=
      hbase.const_mul _
    refine hmaj.mono' hmeas.aestronglyMeasurable.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]
    have h1 := r324PermCross_heat_large z (le_of_lt ht)
    have h2 : Real.exp (-(t / 2)) = Real.exp (-(2⁻¹ : ℝ) * t) := by
      congr 1
      ring
    rw [h2] at h1
    exact h1
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion]
  exact hsmall.union hlarge

/-- The explicit uniform floor constant `e⁻² (64π²)⁻¹ e^{-π²}`. -/
def r324PermCrossGreenFloorConst : ℝ :=
  Real.exp (-2) * ((64 * Real.pi ^ 2)⁻¹ * Real.exp (-Real.pi ^ 2))

theorem r324PermCrossGreenFloorConst_pos :
    0 < r324PermCrossGreenFloorConst := by
  rw [r324PermCrossGreenFloorConst]
  positivity

/-- **The Green's function floor**: off the origin,
`greenFn z ≥ e⁻² (64π²)⁻¹ e^{-π²} > 0`. -/
theorem r324PermCross_greenFn_floor {z : T4} (hz : z ≠ 0) :
    r324PermCrossGreenFloorConst ≤ greenFn z := by
  have hint := r324PermCross_integrableOn_greenIntegrand hz
  have hnn : ∀ t : ℝ, 0 ≤ Real.exp (-t) * heatKernelT4 t z :=
    fun t => mul_nonneg (Real.exp_pos _).le (heatKernelT4_nonneg _ _)
  have hpt : ∀ t ∈ Ioc (1 : ℝ) 2,
      r324PermCrossGreenFloorConst ≤
        Real.exp (-t) * heatKernelT4 t z := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1.le
    have hzero : latticeDistSq z 0 = torusDistSq z := by
      unfold latticeDistSq torusDistSq
      refine Finset.sum_congr rfl fun i _ => ?_
      norm_num
    have hΘ : (4 * Real.pi * t) ^ (-2 : ℤ) *
        Real.exp (-latticeDistSq z 0 / (4 * t)) ≤ heatKernelT4 t z :=
      (summable_heatKernel_terms ht0 z).le_tsum 0 fun k _ =>
        mul_nonneg (r324PermCross_heat_coeff_nonneg t)
          (Real.exp_pos _).le
    have hcoeff : (64 * Real.pi ^ 2)⁻¹ ≤
        (4 * Real.pi * t) ^ (-2 : ℤ) := by
      rw [r324PermCross_heat_coeff]
      have ht2 : t ^ 2 ≤ 4 := by nlinarith [ht.1.le, ht.2]
      have h1 : (t ^ 2)⁻¹ ≥ (4 : ℝ)⁻¹ :=
        inv_anti₀ (by positivity) ht2
      calc (64 * Real.pi ^ 2)⁻¹ =
          (16 * Real.pi ^ 2)⁻¹ * (4 : ℝ)⁻¹ := by
            rw [← mul_inv]
            congr 1
            ring
        _ ≤ (16 * Real.pi ^ 2)⁻¹ * (t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hexpd : Real.exp (-Real.pi ^ 2) ≤
        Real.exp (-latticeDistSq z 0 / (4 * t)) := by
      apply Real.exp_le_exp.mpr
      rw [hzero]
      have hd4 : torusDistSq z ≤ 4 * Real.pi ^ 2 :=
        r324PermCross_torusDistSq_le z
      have hd0 : 0 ≤ torusDistSq z := torusDistSq_nonneg z
      rw [neg_div, neg_le_neg_iff]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
      nlinarith [ht.1.le, sq_nonneg Real.pi]
    have hterm : (64 * Real.pi ^ 2)⁻¹ * Real.exp (-Real.pi ^ 2) ≤
        (4 * Real.pi * t) ^ (-2 : ℤ) *
          Real.exp (-latticeDistSq z 0 / (4 * t)) :=
      mul_le_mul hcoeff hexpd (Real.exp_pos _).le
        (r324PermCross_heat_coeff_nonneg t)
    have hexpt : Real.exp (-2) ≤ Real.exp (-t) :=
      Real.exp_le_exp.mpr (by linarith [ht.2])
    calc r324PermCrossGreenFloorConst =
        Real.exp (-2) *
          ((64 * Real.pi ^ 2)⁻¹ * Real.exp (-Real.pi ^ 2)) := rfl
      _ ≤ Real.exp (-t) *
          ((4 * Real.pi * t) ^ (-2 : ℤ) *
            Real.exp (-latticeDistSq z 0 / (4 * t))) :=
          mul_le_mul hexpt hterm
            (mul_nonneg (by positivity) (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ ≤ Real.exp (-t) * heatKernelT4 t z :=
          mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le
  have hsub : Ioc (1 : ℝ) 2 ⊆ Ioi (0 : ℝ) := fun t ht =>
    lt_of_lt_of_le one_pos ht.1.le
  have hstep1 : (∫ t in Ioc (1 : ℝ) 2,
      Real.exp (-t) * heatKernelT4 t z) ≤ greenFn z := by
    unfold greenFn
    refine setIntegral_mono_set hint ?_ hsub.eventuallyLE
    exact Filter.Eventually.of_forall fun t => hnn t
  have hstep2 : r324PermCrossGreenFloorConst ≤
      ∫ t in Ioc (1 : ℝ) 2, Real.exp (-t) * heatKernelT4 t z := by
    have hμ : (volume : Measure ℝ) (Ioc (1 : ℝ) 2) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have hμreal : (volume : Measure ℝ).real (Ioc (1 : ℝ) 2) = 1 := by
      rw [measureReal_def, Real.volume_Ioc]
      norm_num
    have h := setIntegral_ge_of_const_le_real measurableSet_Ioc hμ hpt
      (hint.mono_set hsub)
    rw [hμreal, mul_one] at h
    exact h
  exact le_trans hstep2 hstep1

end

end Anderson4D
