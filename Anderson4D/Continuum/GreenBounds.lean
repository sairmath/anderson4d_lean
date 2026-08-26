import Anderson4D.Continuum.SingularConv

/-!
# Heat-kernel and Green's function estimates (blueprint node I-green)

Basic estimates for the periodized heat kernel `heatKernelT4` and the
Green's function `greenFn`:

* summability of the periodization (`summable_heatKernel_terms`),
  positivity (`heatKernelT4_pos`) and symmetry (`heatKernelT4_memE`);
* the paper's bound (4.1) for `k = 0`: `greenFn z ≤ C / torusDistSq z`
  (`greenFn_le`), via the split `|z̃ + 2πk|² ≥ |z̃|²/2 + π²|k|²/2` and the
  exact identity `∫_0^∞ t⁻² e^{-a/t} dt = a⁻¹`;
* `greenFn_memE` and `greenFn_nonneg`.
-/

namespace Anderson4D

noncomputable section

open Real MeasureTheory Set

-- `torusDistSq` and its basic lemmas come from `Continuum/SingularConv.lean`.

lemma latticeDistSq_nonneg (z : T4) (k : Z4) : 0 ≤ latticeDistSq z k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

-- `torusLift_mem_Ico` comes from `Continuum/SingularConv.lean`.

private lemma abs_torusLift_le (z : T4) (i : Fin dim) : |torusLift z i| ≤ π := by
  have h := torusLift_mem_Ico z i
  rw [abs_le]
  exact ⟨h.1, h.2.le⟩

/-- Single-coordinate lower bound: for `|a| ≤ π` and `m ∈ ℤ`,
`(a + 2πm)² ≥ a²/2 + (π²/2) m²`. -/
private lemma coord_sq_bound {a : ℝ} (ha : |a| ≤ π) (m : ℤ) :
    a ^ 2 / 2 + π ^ 2 / 2 * (m : ℝ) ^ 2 ≤ (a + 2 * π * (m : ℝ)) ^ 2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · push_cast
    nlinarith [sq_nonneg a]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hm
    have hpi := Real.pi_pos
    -- `2π|m| ≤ |a + 2πm| + |a|`, hence `π|m| ≤ |a + 2πm|`
    have h3 : |2 * π * (m : ℝ)| ≤ |a + 2 * π * (m : ℝ)| + |a| := by
      calc |2 * π * (m : ℝ)| = |a + 2 * π * (m : ℝ) + -a| := by congr 1; ring
        _ ≤ |a + 2 * π * (m : ℝ)| + |-a| := abs_add_le _ _
        _ = |a + 2 * π * (m : ℝ)| + |a| := by rw [abs_neg]
    have h4 : |2 * π * (m : ℝ)| = 2 * π * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have h2 : π * |(m : ℝ)| ≤ |a + 2 * π * (m : ℝ)| := by
      rw [h4] at h3
      nlinarith [ha, h1]
    have hA2 : π ^ 2 * (m : ℝ) ^ 2 ≤ (a + 2 * π * (m : ℝ)) ^ 2 := by
      have h5 := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ π * |(m : ℝ)|) h2
      have h6 : |a + 2 * π * (m : ℝ)| * |a + 2 * π * (m : ℝ)|
          = (a + 2 * π * (m : ℝ)) ^ 2 := by rw [← sq_abs]; ring
      have h7 : π * |(m : ℝ)| * (π * |(m : ℝ)|) = π ^ 2 * (m : ℝ) ^ 2 := by
        rw [← sq_abs (m : ℝ)]; ring
      rw [h6, h7] at h5
      exact h5
    have ha2 : a ^ 2 ≤ π ^ 2 := sq_le_sq' (abs_le.mp ha).1 (abs_le.mp ha).2
    have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [h1, sq_abs (m : ℝ)]
    have hpm : π ^ 2 ≤ π ^ 2 * (m : ℝ) ^ 2 := by nlinarith [hm1, sq_nonneg π]
    linarith

/-- The key geometric bound: `|z̃ + 2πk|² ≥ |z̃|²/2 + (π²/2)|k|²`. -/
private lemma latticeDistSq_ge (z : T4) (k : Z4) :
    torusDistSq z / 2 + π ^ 2 / 2 * ∑ i, ((k i : ℝ)) ^ 2 ≤ latticeDistSq z k := by
  rw [latticeDistSq, torusDistSq, Finset.sum_div, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => coord_sq_bound (abs_torusLift_le z i) (k i)

private lemma latticeDistSq_ge_sum (z : T4) (k : Z4) :
    π ^ 2 / 2 * ∑ i, ((k i : ℝ)) ^ 2 ≤ latticeDistSq z k := by
  have h := latticeDistSq_ge z k
  have h2 := torusDistSq_nonneg z
  linarith

/-! ### Summability of the periodization -/

private lemma summable_exp_neg_mul_int_sq {c : ℝ} (hc : 0 < c) :
    Summable fun m : ℤ => exp (-c * (m : ℝ) ^ 2) := by
  have hgeo : Summable fun n : ℕ => exp (-c) ^ n :=
    summable_geometric_of_lt_one (exp_pos _).le
      (by rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith))
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hgeo.of_nonneg_of_le (fun n => (exp_pos _).le) fun n => ?_
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
    push_cast
    nlinarith [h1, hc]
  · refine hgeo.of_nonneg_of_le (fun n => (exp_pos _).le) fun n => ?_
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    push_cast
    nlinarith [hc, sq_nonneg ((n : ℝ)), Nat.cast_nonneg (α := ℝ) n]

/-- Summability over `ℤⁿ` of nonnegative product-form terms, by iterating
the binary product criterion through `Fin.consEquiv`. -/
private lemma summable_pi_prod {g : ℤ → ℝ} (h0 : ∀ m, 0 ≤ g m)
    (hg : Summable g) : ∀ n : ℕ, Summable fun k : Fin n → ℤ => ∏ i, g (k i) := by
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    have hg0 : (0 : ℤ → ℝ) ≤ g := fun m => h0 m
    have hp0 : (0 : (Fin n → ℤ) → ℝ) ≤ fun k => ∏ i, g (k i) :=
      fun k => Finset.prod_nonneg fun i _ => h0 _
    have hstep : Summable fun p : ℤ × (Fin n → ℤ) => g p.1 * ∏ i, g (p.2 i) :=
      @Summable.mul_of_nonneg ℤ (Fin n → ℤ) g (fun k => ∏ i, g (k i)) hg ih hg0 hp0
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    refine hstep.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

private lemma heat_coeff_nonneg (t : ℝ) : 0 ≤ (4 * π * t) ^ (-2 : ℤ) := by
  rw [zpow_neg, inv_nonneg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num,
    zpow_natCast]
  exact sq_nonneg _

lemma summable_heatKernel_terms {t : ℝ} (ht : 0 < t) (z : T4) :
    Summable fun k : Z4 =>
      (4 * π * t) ^ (-2 : ℤ) * exp (-latticeDistSq z k / (4 * t)) := by
  have ht' : t ≠ 0 := ht.ne'
  have hc0 : 0 < π ^ 2 / (8 * t) := by positivity
  have hprod := summable_pi_prod
    (g := fun m => exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2))
    (fun m => (exp_pos _).le) (summable_exp_neg_mul_int_sq hc0) dim
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hprod.mul_left ((4 * π * t) ^ (-2 : ℤ)))
  refine mul_le_mul_of_nonneg_left ?_ (heat_coeff_nonneg t)
  rw [← Real.exp_sum]
  apply exp_le_exp.mpr
  rw [← Finset.mul_sum, neg_div, neg_mul, neg_le_neg_iff,
    le_div_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
  have h1 : π ^ 2 / (8 * t) * (∑ i, ((k i : ℝ)) ^ 2) * (4 * t)
      = π ^ 2 / 2 * ∑ i, ((k i : ℝ)) ^ 2 := by
    field_simp
    ring
  rw [h1]
  exact latticeDistSq_ge_sum z k

/-! ### Positivity -/

lemma heatKernelT4_nonneg (t : ℝ) (z : T4) : 0 ≤ heatKernelT4 t z :=
  tsum_nonneg fun _ => mul_nonneg (heat_coeff_nonneg t) (exp_pos _).le

theorem heatKernelT4_pos {t : ℝ} (ht : 0 < t) (z : T4) :
    0 < heatKernelT4 t z := by
  unfold heatKernelT4
  exact (summable_heatKernel_terms ht z).tsum_pos
    (fun _ => mul_nonneg (heat_coeff_nonneg t) (exp_pos _).le) 0 (by positivity)

/-! ### Symmetry: the heat kernel lies in the class `𝓔` -/

private lemma torusLift_comp (x : T4) (σ : Equiv.Perm (Fin dim)) (i : Fin dim) :
    torusLift (x ∘ σ) i = torusLift x (σ i) := rfl

private lemma latticeDistSq_comp_perm (x : T4) (σ : Equiv.Perm (Fin dim))
    (k : Z4) : latticeDistSq (x ∘ σ) k = latticeDistSq x (k ∘ σ.symm) := by
  unfold latticeDistSq
  rw [← Equiv.sum_comp σ fun j => (torusLift x j + 2 * π * ((k ∘ σ.symm) j : ℝ)) ^ 2]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [torusLift_comp]

/-- Precomposition with `σ⁻¹` as a self-equivalence of `ℤ⁴`. -/
private def permZ4 (σ : Equiv.Perm (Fin dim)) : Z4 ≃ Z4 where
  toFun k := k ∘ σ.symm
  invFun k := k ∘ σ
  left_inv k := by funext j; simp [Function.comp]
  right_inv k := by funext j; simp [Function.comp]

private lemma heatKernelT4_perm (t : ℝ) (σ : Equiv.Perm (Fin dim)) (x : T4) :
    heatKernelT4 t (x ∘ σ) = heatKernelT4 t x := by
  unfold heatKernelT4
  simp only [latticeDistSq_comp_perm]
  exact (permZ4 σ).tsum_eq fun k =>
    (4 * π * t) ^ (-2 : ℤ) * exp (-latticeDistSq x k / (4 * t))

private lemma coe_torusLift (x : T4) (i : Fin dim) :
    ((torusLift x i : ℝ) : AddCircle (2 * π)) = x i :=
  AddCircle.coe_equivIco

/-- If the lift of `x i` is the boundary point `-π`, negating that
coordinate fixes the point of the torus. -/
private lemma update_neg_of_boundary {x : T4} {i : Fin dim}
    (h : torusLift x i = -π) : Function.update x i (-(x i)) = x := by
  have hfix : -(x i) = x i := by
    rw [← coe_torusLift x i, h, ← AddCircle.coe_neg]
    have h2 : -(-π) = -π + 2 * π := by ring
    rw [h2, AddCircle.coe_add_period]
  rw [hfix, Function.update_eq_self]

/-- Away from the boundary, the canonical lift of `-w` is minus the lift. -/
private lemma equivIco_neg {w : AddCircle (2 * π)}
    (h : ((AddCircle.equivIco (2 * π) (-π)) w : ℝ) ≠ -π) :
    ((AddCircle.equivIco (2 * π) (-π)) (-w) : ℝ)
      = -((AddCircle.equivIco (2 * π) (-π)) w : ℝ) := by
  set a := ((AddCircle.equivIco (2 * π) (-π)) w : ℝ)
  have hmem : a ∈ Ico (-π) (-π + 2 * π) := ((AddCircle.equivIco (2 * π) (-π)) w).2
  have hw : ((a : ℝ) : AddCircle (2 * π)) = w := AddCircle.coe_equivIco
  have h1 : -w = ((-a : ℝ) : AddCircle (2 * π)) := by rw [AddCircle.coe_neg, hw]
  rw [h1]
  have hlt : -π < a := lt_of_le_of_ne hmem.1 (Ne.symm h)
  have h2 : -a ∈ Ico (-π) (-π + 2 * π) := by
    constructor
    · have := hmem.2; linarith
    · linarith
  exact AddCircle.equivIco_coe_of_mem h2

private lemma torusLift_update_self {x : T4} {i : Fin dim}
    (h : torusLift x i ≠ -π) :
    torusLift (Function.update x i (-(x i))) i = -(torusLift x i) := by
  have hkey := equivIco_neg (w := x i) h
  show ((AddCircle.equivIco (2 * π) (-π)) (Function.update x i (-(x i)) i) : ℝ)
      = -(torusLift x i)
  rw [Function.update_self]
  exact hkey

private lemma torusLift_update_ne {x : T4} {i j : Fin dim} (hj : j ≠ i)
    (v : AddCircle (2 * π)) :
    torusLift (Function.update x i v) j = torusLift x j := by
  show ((AddCircle.equivIco (2 * π) (-π)) (Function.update x i v j) : ℝ) = _
  rw [Function.update_of_ne hj]
  rfl

/-- Negation of the `i`-th coordinate as a self-equivalence of `ℤ⁴`. -/
private def negAt (i : Fin dim) : Z4 ≃ Z4 :=
  Function.Involutive.toPerm (fun k => Function.update k i (-(k i))) fun k => by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [Function.update_of_ne hj]

private lemma heatKernelT4_flip (t : ℝ) (i : Fin dim) (x : T4) :
    heatKernelT4 t (Function.update x i (-(x i))) = heatKernelT4 t x := by
  rcases eq_or_ne (torusLift x i) (-π) with h | h
  · rw [update_neg_of_boundary h]
  · have key : ∀ k : Z4, latticeDistSq (Function.update x i (-(x i))) k
        = latticeDistSq x (Function.update k i (-(k i))) := by
      intro k
      unfold latticeDistSq
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases eq_or_ne j i with rfl | hj
      · rw [torusLift_update_self h, Function.update_self]
        push_cast
        ring
      · rw [torusLift_update_ne hj, Function.update_of_ne hj]
    unfold heatKernelT4
    simp only [key]
    exact (negAt i).tsum_eq fun k =>
      (4 * π * t) ^ (-2 : ℤ) * exp (-latticeDistSq x k / (4 * t))

/-- The heat kernel lies in the hyperoctahedral symmetry class `𝓔`
(paper Def. 2.1) for every `t`. -/
theorem heatKernelT4_memE (t : ℝ) : MemEClassT4 (heatKernelT4 t) :=
  ⟨fun σ x => heatKernelT4_perm t σ x, fun i x => heatKernelT4_flip t i x⟩

/-! ### The Gaussian-sum bound `∑_{m∈ℤ} e^{-cm²} ≤ 2(1 + c⁻¹)` -/

private lemma gauss_sum_le {c : ℝ} (hc : 0 < c) :
    ∑' m : ℤ, exp (-c * (m : ℝ) ^ 2) ≤ 2 * (1 + c⁻¹) := by
  set f : ℤ → ℝ := fun m => exp (-c * (m : ℝ) ^ 2) with hf
  have hr0 : (0 : ℝ) ≤ exp (-c) := (exp_pos _).le
  have hr1 : exp (-c) < 1 := by
    rw [← exp_zero]; exact exp_lt_exp.mpr (by linarith)
  have hgeo : Summable fun n : ℕ => exp (-c) ^ n :=
    summable_geometric_of_lt_one hr0 hr1
  have key : ∀ (n : ℕ) (m : ℤ), (n : ℝ) ≤ (m : ℝ) ^ 2 → f m ≤ exp (-c) ^ n := by
    intro n m hnm
    simp only [hf]
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    nlinarith [hc, hnm]
  have hb1 : ∀ n : ℕ, f ((n : ℤ)) ≤ exp (-c) ^ n := by
    intro n
    apply key n
    push_cast
    exact_mod_cast Nat.le_self_pow two_ne_zero n
  have hb2 : ∀ n : ℕ, f (-((n : ℤ) + 1)) ≤ exp (-c) ^ n := by
    intro n
    apply key n
    push_cast
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg ((n : ℝ)), hn0]
  have hpos : ∀ m : ℤ, 0 ≤ f m := fun m => (exp_pos _).le
  have hs1 : Summable fun n : ℕ => f ((n : ℤ)) :=
    hgeo.of_nonneg_of_le (fun n => hpos _) hb1
  have hs2 : Summable fun n : ℕ => f (-((n : ℤ) + 1)) :=
    hgeo.of_nonneg_of_le (fun n => hpos _) hb2
  have hgs : ∑' n : ℕ, exp (-c) ^ n = (1 - exp (-c))⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hT1 : ∑' n : ℕ, f ((n : ℤ)) ≤ (1 - exp (-c))⁻¹ := by
    rw [← hgs]; exact hs1.tsum_le_tsum hb1 hgeo
  have hT2 : ∑' n : ℕ, f (-((n : ℤ) + 1)) ≤ (1 - exp (-c))⁻¹ := by
    rw [← hgs]; exact hs2.tsum_le_tsum hb2 hgeo
  have hinv : (1 - exp (-c))⁻¹ ≤ 1 + c⁻¹ := by
    have hrc : exp (-c) * (1 + c) ≤ 1 := by
      have h1 : c + 1 ≤ exp c := add_one_le_exp c
      have h2 : exp (-c) * exp c = 1 := by rw [← exp_add]; simp
      nlinarith [(exp_pos (-c)).le, h1, h2]
    have h3 : c / (1 + c) ≤ 1 - exp (-c) := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + c)]
      nlinarith [hrc]
    calc (1 - exp (-c))⁻¹ ≤ (c / (1 + c))⁻¹ := inv_anti₀ (by positivity) h3
      _ = (1 + c) / c := by rw [inv_div]
      _ = 1 + c⁻¹ := by
        rw [add_div, div_self hc.ne', one_div]
        ring
  calc ∑' m : ℤ, f m
      = (∑' n : ℕ, f ((n : ℤ))) + ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
        tsum_of_nat_of_neg_add_one hs1 hs2
    _ ≤ 2 * (1 + c⁻¹) := by linarith [hT1, hT2, hinv]

/-- Factorization of the lattice sum: `∑_{k∈ℤⁿ} ∏ᵢ g(kᵢ) = (∑_{m∈ℤ} g m)ⁿ`. -/
private lemma tsum_pi_prod {g : ℤ → ℝ} (h0 : ∀ m, 0 ≤ g m) (hg : Summable g) :
    ∀ n : ℕ, ∑' k : Fin n → ℤ, ∏ i, g (k i) = (∑' m, g m) ^ n := by
  intro n
  induction n with
  | zero =>
    rw [tsum_eq_single (fun i : Fin 0 => (0 : ℤ))
      (fun b' hb' => absurd (funext fun i => i.elim0) hb'), pow_zero]
    simp
  | succ n ih =>
    have hsum_n := summable_pi_prod h0 hg n
    have hg0 : (0 : ℤ → ℝ) ≤ g := fun m => h0 m
    have hp0 : (0 : (Fin n → ℤ) → ℝ) ≤ fun k => ∏ i, g (k i) :=
      fun k => Finset.prod_nonneg fun i _ => h0 _
    have hstep : Summable fun p : ℤ × (Fin n → ℤ) => g p.1 * ∏ i, g (p.2 i) :=
      @Summable.mul_of_nonneg ℤ (Fin n → ℤ) g (fun k => ∏ i, g (k i)) hg hsum_n hg0 hp0
    calc ∑' k : Fin (n + 1) → ℤ, ∏ i, g (k i)
        = ∑' p : ℤ × (Fin n → ℤ), g p.1 * ∏ i, g (p.2 i) := by
          rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).tsum_eq
            (fun k : Fin (n + 1) → ℤ => ∏ i, g (k i))]
          exact tsum_congr fun p => by simp [Fin.consEquiv, Fin.prod_univ_succ]
      _ = ∑' m : ℤ, ∑' k : Fin n → ℤ, g m * ∏ i, g (k i) :=
          hstep.tsum_prod' fun m => hsum_n.mul_left (g m)
      _ = ∑' m : ℤ, g m * (∑' m' : ℤ, g m') ^ n :=
          tsum_congr fun m => by rw [tsum_mul_left, ih]
      _ = (∑' m : ℤ, g m) * (∑' m' : ℤ, g m') ^ n := tsum_mul_right
      _ = (∑' m : ℤ, g m) ^ (n + 1) := by ring

/-! ### Pointwise heat-kernel bound -/

private lemma heat_coeff_eq (t : ℝ) :
    (4 * π * t) ^ (-2 : ℤ) = (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ := by
  rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
    ← mul_inv]
  congr 1
  ring

private lemma exp_neg_mul_quartic_le {t : ℝ} (ht : 0 ≤ t) :
    exp (-t) * (1 + t) ^ 4 ≤ 256 := by
  have h1 : 1 + t ≤ 4 * exp (t / 4) := by
    have h2 := add_one_le_exp (t / 4)
    linarith
  have h2 : (1 + t) ^ 4 ≤ (4 * exp (t / 4)) ^ 4 :=
    pow_le_pow_left₀ (by linarith) h1 4
  have h3 : (4 * exp (t / 4)) ^ 4 = 256 * exp t := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have h4 : ((4 : ℕ) : ℝ) * (t / 4) = t := by push_cast; ring
    rw [h4]
    norm_num
  calc exp (-t) * (1 + t) ^ 4 ≤ exp (-t) * (256 * exp t) :=
        mul_le_mul_of_nonneg_left (h2.trans_eq h3) (exp_pos _).le
    _ = 256 := by
        have h5 : exp (-t) * exp t = 1 := by rw [← exp_add]; simp
        rw [show exp (-t) * (256 * exp t) = 256 * (exp (-t) * exp t) from by ring,
          h5, mul_one]

/-- Heat-kernel bound after splitting `|z̃+2πk|² ≥ |z̃|²/2 + (π²/2)|k|²`:
the periodization is controlled by a Gaussian factor in `z` times the
fourth power of a one-dimensional Gaussian sum. -/
private lemma heatKernel_le {t : ℝ} (ht : 0 < t) (z : T4) :
    heatKernelT4 t z ≤ (4 * π * t) ^ (-2 : ℤ) * (exp (-(torusDistSq z / 8 / t))
      * (∑' m : ℤ, exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2)) ^ dim) := by
  have ht' : t ≠ 0 := ht.ne'
  have hc0 : 0 < π ^ 2 / (8 * t) := by positivity
  have hgsum := summable_exp_neg_mul_int_sq hc0
  have hprod := summable_pi_prod
    (g := fun m => exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2))
    (fun m => (exp_pos _).le) hgsum dim
  have hterm : ∀ k : Z4, (4 * π * t) ^ (-2 : ℤ) * exp (-latticeDistSq z k / (4 * t))
      ≤ (4 * π * t) ^ (-2 : ℤ) * (exp (-(torusDistSq z / 8 / t))
        * ∏ i, exp (-(π ^ 2 / (8 * t)) * ((k i : ℝ)) ^ 2)) := by
    intro k
    refine mul_le_mul_of_nonneg_left ?_ (heat_coeff_nonneg t)
    rw [← Real.exp_sum, ← exp_add]
    apply exp_le_exp.mpr
    rw [← Finset.mul_sum]
    have h48 : -(torusDistSq z / 8 / t) + -(π ^ 2 / (8 * t)) * ∑ i, ((k i : ℝ)) ^ 2
        = -((torusDistSq z / 2 + π ^ 2 / 2 * ∑ i, ((k i : ℝ)) ^ 2) / (4 * t)) := by
      field_simp
      ring
    rw [h48, neg_div, neg_le_neg_iff]
    gcongr
    exact latticeDistSq_ge z k
  calc heatKernelT4 t z
      ≤ ∑' k : Z4, (4 * π * t) ^ (-2 : ℤ) * (exp (-(torusDistSq z / 8 / t))
          * ∏ i, exp (-(π ^ 2 / (8 * t)) * ((k i : ℝ)) ^ 2)) :=
        (summable_heatKernel_terms ht z).tsum_le_tsum hterm
          ((hprod.mul_left (exp (-(torusDistSq z / 8 / t)))).mul_left
            ((4 * π * t) ^ (-2 : ℤ)))
    _ = (4 * π * t) ^ (-2 : ℤ) * (exp (-(torusDistSq z / 8 / t))
          * ∑' k : Z4, ∏ i, exp (-(π ^ 2 / (8 * t)) * ((k i : ℝ)) ^ 2)) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ = (4 * π * t) ^ (-2 : ℤ) * (exp (-(torusDistSq z / 8 / t))
          * (∑' m : ℤ, exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2)) ^ dim) := by
        rw [tsum_pi_prod (fun m => (exp_pos _).le) hgsum dim]

/-- The integrand bound feeding (4.1): for `t > 0`,
`e⁻ᵗ Θ(t,z) ≤ (256/π²) t⁻² e^{-|z̃|²/(8t)}`. -/
lemma pointwise_bound {t : ℝ} (ht : 0 < t) (z : T4) :
    exp (-t) * heatKernelT4 t z
      ≤ 256 / π ^ 2 * ((t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t))) := by
  have hΘ := heatKernel_le ht z
  have hT0 : (0 : ℝ) ≤ ∑' m : ℤ, exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2) :=
    tsum_nonneg fun m => (exp_pos _).le
  have hTle : (∑' m : ℤ, exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2)) ≤ 2 * (1 + t) := by
    have h1 := gauss_sum_le (by positivity : (0 : ℝ) < π ^ 2 / (8 * t))
    have hc : (π ^ 2 / (8 * t))⁻¹ ≤ t := by
      rw [inv_div, div_le_iff₀ (by positivity : (0 : ℝ) < π ^ 2)]
      nlinarith [Real.pi_gt_three, ht, sq_nonneg (π - 3)]
    linarith [h1, hc]
  have hT4 : (∑' m : ℤ, exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2)) ^ dim
      ≤ 16 * (1 + t) ^ 4 := by
    calc (∑' m : ℤ, exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2)) ^ dim
        ≤ (2 * (1 + t)) ^ 4 := pow_le_pow_left₀ hT0 hTle 4
      _ = 16 * (1 + t) ^ 4 := by ring
  calc exp (-t) * heatKernelT4 t z
      ≤ exp (-t) * ((4 * π * t) ^ (-2 : ℤ) * (exp (-(torusDistSq z / 8 / t))
          * (∑' m : ℤ, exp (-(π ^ 2 / (8 * t)) * (m : ℝ) ^ 2)) ^ dim)) :=
        mul_le_mul_of_nonneg_left hΘ (exp_pos _).le
    _ ≤ exp (-t) * ((4 * π * t) ^ (-2 : ℤ) * (exp (-(torusDistSq z / 8 / t))
          * (16 * (1 + t) ^ 4))) := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ (heat_coeff_nonneg t)
        exact mul_le_mul_of_nonneg_left hT4 (exp_pos _).le
    _ = (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t))
          * (16 * (exp (-t) * (1 + t) ^ 4)) := by
        rw [heat_coeff_eq]
        ring
    _ ≤ (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t))
          * (16 * 256) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h6 := exp_neg_mul_quartic_le ht.le
        linarith
    _ = 256 / π ^ 2 * ((t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t))) := by
        have hpi : ((16 * π ^ 2)⁻¹ * (16 * 256) : ℝ) = 256 / π ^ 2 := by
          rw [mul_inv, div_eq_mul_inv]
          ring
        calc (16 * π ^ 2)⁻¹ * (t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t)) * (16 * 256)
            = (16 * π ^ 2)⁻¹ * (16 * 256)
              * ((t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t))) := by ring
          _ = 256 / π ^ 2 * ((t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t))) := by
              rw [hpi]

/-! ### The exact time integral `∫_0^∞ t⁻² e^{-a/t} dt = a⁻¹` -/

theorem integral_inv_sq_exp {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (t ^ 2)⁻¹ * exp (-(a / t)) = a⁻¹ := by
  calc ∫ t in Ioi (0 : ℝ), (t ^ 2)⁻¹ * exp (-(a / t))
      = ∫ x in Ioi (0 : ℝ),
          (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • exp (-(a * x ^ (-1 : ℝ))) := by
        refine (setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_).symm
        have hx0 : (0 : ℝ) < x := hx
        rw [smul_eq_mul, abs_neg, abs_one, one_mul,
          show ((-1 : ℝ) - 1) = -2 by norm_num,
          Real.rpow_neg hx0.le, Real.rpow_neg_one,
          show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          ← div_eq_mul_inv]
    _ = ∫ y in Ioi (0 : ℝ), exp (-(a * y)) :=
        integral_comp_rpow_Ioi (fun y => exp (-(a * y))) (by norm_num)
    _ = a⁻¹ := by
        have h3 := integral_comp_mul_left_Ioi (fun y => exp (-y)) 0 ha
        simp only [mul_zero] at h3
        rw [h3, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]

theorem integrableOn_inv_sq_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => (t ^ 2)⁻¹ * exp (-(a / t))) (Ioi (0 : ℝ)) := by
  have base : IntegrableOn (fun y => exp (-(a * y))) (Ioi (0 : ℝ)) := by
    have h := exp_neg_integrableOn_Ioi 0 ha
    simp only [neg_mul] at h
    exact h
  have h2 := (integrableOn_Ioi_comp_rpow_iff (fun y => exp (-(a * y)))
    (p := (-1 : ℝ)) (by norm_num)).mpr base
  refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := hx
  simp only [smul_eq_mul]
  rw [abs_neg, abs_one, one_mul, show ((-1 : ℝ) - 1) = -2 by norm_num,
    Real.rpow_neg hx0.le, Real.rpow_neg_one,
    show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv]

/-! ### Green's function: positivity, symmetry, and the (4.1) bound -/

theorem greenFn_nonneg (z : T4) : 0 ≤ greenFn z :=
  integral_nonneg fun _ => mul_nonneg (exp_pos _).le (heatKernelT4_nonneg _ _)

/-- The Green's function lies in the symmetry class `𝓔` (blueprint node
I-green; inherited from `heatKernelT4_memE` under the time integral). -/
theorem greenFn_memE : MemEClassT4 greenFn := by
  constructor
  · intro σ x
    unfold greenFn
    have h : (fun t => exp (-t) * heatKernelT4 t (x ∘ σ))
        = fun t => exp (-t) * heatKernelT4 t x := by
      funext t
      rw [(heatKernelT4_memE t).perm_invariant σ x]
    rw [h]
  · intro i x
    unfold greenFn
    have h : (fun t => exp (-t) * heatKernelT4 t (Function.update x i (-(x i))))
        = fun t => exp (-t) * heatKernelT4 t x := by
      funext t
      rw [(heatKernelT4_memE t).even_coord i x]
    rw [h]

/-- Paper estimate (4.1) for the free Green's function (`k = 0` case):
`G(z) ≤ C |z̃|⁻²` with an explicit constant, where `|z̃|² = torusDistSq z`
is the squared canonical lift. -/
theorem greenFn_le : ∃ C : ℝ, 0 < C ∧ ∀ z : T4, torusDistSq z ≠ 0 →
    greenFn z ≤ C / torusDistSq z := by
  refine ⟨2048 / π ^ 2, by positivity, fun z hz => ?_⟩
  have hd : 0 < torusDistSq z :=
    lt_of_le_of_ne (torusDistSq_nonneg z) (Ne.symm hz)
  have ha : 0 < torusDistSq z / 8 := by positivity
  have hint : IntegrableOn (fun t => (t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t)))
      (Ioi (0 : ℝ)) := integrableOn_inv_sq_exp ha
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  calc greenFn z
      ≤ ∫ t in Ioi (0 : ℝ),
          256 / π ^ 2 * ((t ^ 2)⁻¹ * exp (-(torusDistSq z / 8 / t))) := by
        unfold greenFn
        refine integral_mono_of_nonneg ?_ (Integrable.const_mul hint _) ?_
        · exact Filter.Eventually.of_forall fun t =>
            mul_nonneg (exp_pos _).le (heatKernelT4_nonneg _ _)
        · refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
          exact Filter.Eventually.of_forall fun t ht => pointwise_bound ht z
    _ = 256 / π ^ 2 * (torusDistSq z / 8)⁻¹ := by
        rw [integral_const_mul, integral_inv_sq_exp ha]
    _ = 2048 / π ^ 2 / torusDistSq z := by
        rw [inv_div]
        field_simp
        ring

end

end Anderson4D
