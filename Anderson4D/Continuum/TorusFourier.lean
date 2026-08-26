import Anderson4D.Continuum.Basic

/-!
# Fourier bookkeeping on the four-dimensional torus

This file fixes the normalization conventions on the formal torus carrier.
It provides character algebra, orthogonality for both
the probability Haar measure and the paper's Lebesgue-normalized measure,
the coefficient convention used in paper equation (3.23), and the complete
product-torus `L²` Fourier/Plancherel interface.
-/

namespace Anderson4D

noncomputable section

open scoped ENNReal

open Set Algebra Submodule MeasureTheory ComplexConjugate

/-! ## Character algebra -/

@[simp] theorem charT4_add (k l : Z4) (x : T4) :
    charT4 (k + l) x = charT4 k x * charT4 l x := by
  simp only [charT4, Pi.add_apply, fourier_add, Finset.prod_mul_distrib]

@[simp] theorem charT4_neg (k : Z4) (x : T4) :
    charT4 (-k) x = conj (charT4 k x) := by
  simp only [charT4, Pi.neg_apply, fourier_neg, map_prod]

@[simp] theorem conj_charT4 (k : Z4) (x : T4) :
    conj (charT4 k x) = charT4 (-k) x := by
  rw [charT4_neg]

@[simp] theorem conj_charT4_neg (k : Z4) (x : T4) :
    conj (charT4 (-k) x) = charT4 k x := by
  rw [conj_charT4, neg_neg]

theorem norm_charT4 (k : Z4) (x : T4) : ‖charT4 k x‖ = 1 := by
  simp [charT4]

theorem abs_charT4 (k : Z4) (x : T4) : ‖charT4 k x‖₊ = 1 := by
  apply NNReal.eq
  simpa using norm_charT4 k x

theorem continuous_charT4 (k : Z4) : Continuous (charT4 k) := by
  unfold charT4
  fun_prop

theorem integrable_charT4_mul_conj (k l : Z4) :
    Integrable (fun x : T4 => charT4 k x * conj (charT4 l x)) haarT4 := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_charT4 k).mul (continuous_charT4 l).star
  · exact HasCompactSupport.of_compactSpace _

/-! ## Orthogonality -/

/-- The mean of a one-dimensional Fourier character under probability Haar
measure. -/
lemma integral_fourier (k : ℤ) :
    ∫ x : AddCircle (2 * Real.pi), fourier k x ∂AddCircle.haarAddCircle =
      if k = 0 then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [if_neg hk]
    exact integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk Real.two_pi_pos)

/-- One-dimensional Fourier orthogonality under probability Haar measure. -/
theorem fourier_orthogonality (n m : ℤ) :
    ∫ x : AddCircle (2 * Real.pi),
        fourier n x * conj (fourier m x) ∂AddCircle.haarAddCircle =
      if n = m then 1 else 0 := by
  have h : ∀ x : AddCircle (2 * Real.pi),
      fourier n x * conj (fourier m x) = fourier (n + -m) x := fun x => by
    rw [fourier_add, fourier_neg]
  simp_rw [h, integral_fourier, add_neg_eq_zero]

private lemma prod_ite_apply_eq (k l : Z4) :
    (∏ i, if k i = l i then (1 : ℂ) else 0) =
      if k = l then 1 else 0 := by
  rcases eq_or_ne k l with rfl | h
  · simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Product-character orthogonality under the probability Haar measure. -/
theorem charT4_orthogonality (k l : Z4) :
    ∫ x : T4, charT4 k x * conj (charT4 l x) ∂haarT4 =
      if k = l then 1 else 0 := by
  have h : ∀ x : T4, charT4 k x * conj (charT4 l x) =
      ∏ i, (fourier (k i) (x i) * conj (fourier (l i) (x i))) := fun x => by
    simp only [charT4, map_prod, ← Finset.prod_mul_distrib]
  calc
    ∫ x : T4, charT4 k x * conj (charT4 l x) ∂haarT4 =
        ∫ x : T4, ∏ i, (fourier (k i) (x i) *
          conj (fourier (l i) (x i)))
          ∂(Measure.pi fun _ => AddCircle.haarAddCircle) := by
            simp_rw [h]
            rfl
    _ = ∏ i, ∫ t, fourier (k i) t * conj (fourier (l i) t)
          ∂AddCircle.haarAddCircle :=
      MeasureTheory.integral_fintype_prod_eq_prod
        fun i t => fourier (k i) t * conj (fourier (l i) t)
    _ = ∏ i, if k i = l i then (1 : ℂ) else 0 := by
      simp_rw [fourier_orthogonality]
    _ = if k = l then 1 else 0 := prod_ite_apply_eq k l

/-- Product-character orthogonality under the paper's measure.  This is the
explicit `(2π)⁴` normalization ledger entry. -/
theorem charT4_orthogonality_paper (k l : Z4) :
    ∫ x : T4, charT4 k x * conj (charT4 l x) ∂paperMeasure =
      if k = l then (((2 * Real.pi) ^ dim : ℝ) : ℂ) else 0 := by
  have h2π : (ENNReal.ofReal ((2 * Real.pi) ^ dim)).toReal =
      (2 * Real.pi) ^ dim := ENNReal.toReal_ofReal (by positivity)
  simp only [paperMeasure, integral_smul_measure, charT4_orthogonality, h2π]
  rcases eq_or_ne k l with rfl | hkl
  · simp [Complex.real_smul]
  · simp [hkl]

/-! ## Coefficient conventions -/

/-- Standard probability-Haar Fourier coefficient.  The conjugated character
gives the usual negative-exponential convention. -/
def torusFourierCoeff (f : T4 → ℂ) (k : Z4) : ℂ :=
  ∫ x, conj (charT4 k x) * f x ∂haarT4

/-- The paper's one-variable positive-exponential coefficient, without a
normalizing `(2π)⁻⁴` factor. -/
def paperFourierCoeff (f : T4 → ℂ) (k : Z4) : ℂ :=
  ∫ x, charT4 k x * f x ∂paperMeasure

/-- Paper equation (3.23), for an arbitrary complex kernel. -/
def paperKernelCoeff (K : T4 → T4 → ℂ) (α β : Z4) : ℂ :=
  ∫ x, ∫ y, charT4 α x * charT4 β y * K x y
    ∂paperMeasure ∂paperMeasure

/-- Probability-Haar counterpart of `paperKernelCoeff`, useful for
normalization arguments. -/
def normalizedKernelCoeff (K : T4 → T4 → ℂ) (α β : Z4) : ℂ :=
  ∫ x, ∫ y, charT4 α x * charT4 β y * K x y
    ∂haarT4 ∂haarT4

/-- Fourier coefficients of the character basis at probability-Haar
normalization. -/
theorem torusFourierCoeff_char (k l : Z4) :
    torusFourierCoeff (charT4 l) k = if k = l then 1 else 0 := by
  unfold torusFourierCoeff
  calc
    (∫ x, conj (charT4 k x) * charT4 l x ∂haarT4) =
        ∫ x, charT4 l x * conj (charT4 k x) ∂haarT4 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => mul_comm _ _
    _ = if l = k then 1 else 0 := charT4_orthogonality l k
    _ = if k = l then 1 else 0 := by
      rcases eq_or_ne k l with rfl | h
      · simp
      · simp [h, Ne.symm h]

/-- Under the paper's positive-exponential convention, the coefficient of
`e_l` is supported at frequency `-l` and has mass `(2π)⁴`. -/
theorem paperFourierCoeff_char (k l : Z4) :
    paperFourierCoeff (charT4 l) k =
      if l = -k then (((2 * Real.pi) ^ dim : ℝ) : ℂ) else 0 := by
  unfold paperFourierCoeff
  calc
    (∫ x, charT4 k x * charT4 l x ∂paperMeasure) =
        ∫ x, charT4 l x * conj (charT4 (-k) x) ∂paperMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change charT4 k x * charT4 l x =
          charT4 l x * conj (charT4 (-k) x)
        rw [conj_charT4_neg]
        exact mul_comm _ _
    _ = if l = -k then (((2 * Real.pi) ^ dim : ℝ) : ℂ) else 0 :=
      charT4_orthogonality_paper l (-k)

/-- Complete one-variable normalization/sign dictionary: the paper's
unnormalized positive-exponential coefficient is `(2π)⁴` times the
probability-Haar coefficient at the opposite frequency. -/
theorem paperFourierCoeff_eq_volume_mul_torusFourierCoeff_neg
    (f : T4 → ℂ) (k : Z4) :
    paperFourierCoeff f k =
      (((2 * Real.pi) ^ dim : ℝ) : ℂ) * torusFourierCoeff f (-k) := by
  have h2π : (ENNReal.ofReal ((2 * Real.pi) ^ dim)).toReal =
      (2 * Real.pi) ^ dim := ENNReal.toReal_ofReal (by positivity)
  simp only [paperFourierCoeff, paperMeasure, integral_smul_measure, h2π,
    Complex.real_smul]
  congr 1
  unfold torusFourierCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change charT4 k x * f x = conj (charT4 (-k) x) * f x
    rw [conj_charT4_neg]

/-! ## Finite Fourier polynomials -/

/-- A finite Fourier polynomial on `𝕋⁴`. -/
def torusTrigPoly (s : Finset Z4) (a : Z4 → ℂ) (x : T4) : ℂ :=
  ∑ k ∈ s, a k * charT4 k x

/-- Fourier coefficient extraction for a finite trigonometric polynomial. -/
theorem torusFourierCoeff_trigPoly
    (s : Finset Z4) (a : Z4 → ℂ) (k : Z4) :
    torusFourierCoeff (torusTrigPoly s a) k =
      if k ∈ s then a k else 0 := by
  classical
  have hpoint : ∀ x : T4,
      conj (charT4 k x) * torusTrigPoly s a x =
        ∑ l ∈ s, a l * (charT4 l x * conj (charT4 k x)) := by
    intro x
    simp only [torusTrigPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  unfold torusFourierCoeff
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [integral_const_mul, charT4_orthogonality]
    simp
  · intro l hl
    exact (integrable_charT4_mul_conj l k).const_mul _

/-- Finite-dimensional Parseval identity.  This is the algebraic core of
the product-torus Plancherel interface and already suffices for every
finite Fourier truncation. -/
theorem torusTrigPoly_parseval (s : Finset Z4) (a : Z4 → ℂ) :
    (∫ x, torusTrigPoly s a x * conj (torusTrigPoly s a x) ∂haarT4) =
      ∑ k ∈ s, a k * conj (a k) := by
  classical
  have hpoint : ∀ x : T4,
      torusTrigPoly s a x * conj (torusTrigPoly s a x) =
        ∑ k ∈ s, ∑ l ∈ s,
          (a k * conj (a l)) *
            (charT4 k x * conj (charT4 l x)) := by
    intro x
    simp only [torusTrigPoly, map_sum, map_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [MeasureTheory.integral_finsetSum]
    · simp_rw [integral_const_mul, charT4_orthogonality]
      simp [hk]
    · intro l hl
      exact (integrable_charT4_mul_conj k l).const_mul _
  · intro k hk
    exact integrable_finsetSum s fun l _ =>
      (integrable_charT4_mul_conj k l).const_mul _

/-! ## Product-torus `L²` Fourier theory -/

/-- A Fourier character regarded as a continuous function. -/
def charT4Continuous (k : Z4) : C(T4, ℂ) where
  toFun := charT4 k
  continuous_toFun := continuous_charT4 k

@[simp] theorem charT4Continuous_apply (k : Z4) (x : T4) :
    charT4Continuous k x = charT4 k x := rfl

@[simp] theorem charT4Continuous_zero : charT4Continuous 0 = 1 := by
  ext x
  simp

@[simp] theorem charT4Continuous_add (k l : Z4) :
    charT4Continuous (k + l) = charT4Continuous k * charT4Continuous l := by
  ext x
  exact charT4_add k l x

@[simp] theorem star_charT4Continuous (k : Z4) :
    star (charT4Continuous k) = charT4Continuous (-k) := by
  ext x
  change conj (charT4 k x) = charT4 (-k) x
  exact conj_charT4 k x

/-- The star subalgebra generated by the Fourier characters. -/
def torusFourierSubalgebra : StarSubalgebra ℂ C(T4, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range charT4Continuous)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range charT4Continuous) ≤
      star (Algebra.adjoin ℂ (Set.range charT4Continuous))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩
    refine Algebra.subset_adjoin ⟨-k, ?_⟩
    simpa only [starRingEnd_apply] using (star_charT4Continuous k).symm

/-- The algebra generated by the Fourier characters is already their
complex linear span. -/
theorem torusFourierSubalgebra_coe :
    torusFourierSubalgebra.toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range charT4Continuous) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine .trans
    (fun x => Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_)
    Submodule.subset_span
  · exact charT4Continuous_zero
  · rintro _ _ _ _ ⟨k, rfl⟩ ⟨l, rfl⟩
    exact ⟨k + l, charT4Continuous_add k l⟩

/-- A character supported in a single coordinate reads that coordinate
through the standard circle embedding. -/
theorem charT4Continuous_single (x : T4) (i : Fin dim) :
    charT4Continuous (Pi.single i 1) x = fourier 1 (x i) := by
  simp_rw [charT4Continuous_apply, charT4]
  have hprod := Finset.prod_mul_prod_compl {i}
    (fun j => fourier ((Pi.single i (1 : ℤ) : Z4) j) (x j))
  rw [Finset.prod_singleton, Finset.prod_congr rfl (fun j hj => ?_)] at hprod
  · rw [← hprod, Finset.prod_const_one, mul_one, Pi.single_eq_same]
  · rw [Finset.mem_compl, Finset.mem_singleton] at hj
    simp only [Pi.single_eq_of_ne hj, fourier_zero]

/-- Fourier characters separate points of `T4`. -/
theorem torusFourierSubalgebra_separatesPoints :
    torusFourierSubalgebra.SeparatesPoints := by
  classical
  intro x y hxy
  rw [ne_eq, funext_iff, not_forall] at hxy
  obtain ⟨i, hi⟩ := hxy
  refine ⟨_, ⟨charT4Continuous (Pi.single i 1),
    Algebra.subset_adjoin ⟨Pi.single i 1, rfl⟩, rfl⟩, ?_⟩
  dsimp only
  rw [charT4Continuous_single, charT4Continuous_single, fourier_one,
    fourier_one, ne_eq, Subtype.coe_inj]
  contrapose hi
  exact AddCircle.injective_toCircle (ne_of_gt (by positivity)) hi

/-- The character-generated star subalgebra is uniformly dense in the
continuous functions on `T4`. -/
theorem torusFourierSubalgebra_closure_eq_top :
    torusFourierSubalgebra.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    torusFourierSubalgebra_separatesPoints

/-- The complex linear span of the Fourier characters is uniformly dense in
the continuous functions on `T4`. -/
theorem span_charT4Continuous_closure_eq_top :
    (Submodule.span ℂ (Set.range charT4Continuous)).topologicalClosure = ⊤ := by
  rw [← torusFourierSubalgebra_coe]
  exact congr_arg
    (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    torusFourierSubalgebra_closure_eq_top

/-- A Fourier character as an element of `Lᵖ(T4, haarT4)`. -/
abbrev charT4Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : Z4) :
    Lp ℂ p haarT4 :=
  ContinuousMap.toLp (E := ℂ) p haarT4 ℂ (charT4Continuous k)

/-- The `Lᵖ` representative of a character agrees almost everywhere with
the pointwise character. -/
theorem coeFn_charT4Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : Z4) :
    charT4Lp p k =ᵐ[haarT4] charT4 k :=
  ContinuousMap.coeFn_toLp haarT4 (charT4Continuous k)

/-- For finite `p`, the Fourier characters have dense span in
`Lᵖ(T4, haarT4)`. -/
theorem span_charT4Lp_closure_eq_top {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) :
    (Submodule.span ℂ (Set.range (@charT4Lp p _))).topologicalClosure = ⊤ := by
  simpa only [Submodule.map_span, ContinuousLinearMap.coe_coe, ← Set.range_comp,
    Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ haarT4 ℂ hp).topologicalClosure_map_submodule
      span_charT4Continuous_closure_eq_top

/-- The Fourier characters form an orthonormal family in `L²(T4, haarT4)`. -/
theorem orthonormal_charT4 : Orthonormal ℂ (charT4Lp (p := 2)) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [MeasureTheory.ContinuousMap.inner_toLp haarT4
    (charT4Continuous k) (charT4Continuous l)]
  simpa only [charT4Continuous_apply, eq_comm] using charT4_orthogonality l k

/-- The product Fourier characters as a Hilbert basis of `L²(T4, haarT4)`. -/
def torusFourierBasis : HilbertBasis Z4 ℂ (Lp ℂ 2 haarT4) :=
  HilbertBasis.mk orthonormal_charT4
    (span_charT4Lp_closure_eq_top (by simp)).ge

@[simp] theorem coe_torusFourierBasis :
    ⇑torusFourierBasis = charT4Lp 2 :=
  HilbertBasis.coe_mk _ _

/-- The abstract Hilbert-basis coordinate is the integral Fourier
coefficient fixed above. -/
theorem torusFourierBasis_repr (f : Lp ℂ 2 haarT4) (k : Z4) :
    torusFourierBasis.repr f k = torusFourierCoeff f k := by
  trans ∫ x, conj (charT4Lp 2 k x) * f x ∂haarT4
  · rw [torusFourierBasis.repr_apply_apply f k, MeasureTheory.L2.inner_def,
      coe_torusFourierBasis]
    simp only [RCLike.inner_apply, mul_comm]
  · unfold torusFourierCoeff
    apply integral_congr_ae
    filter_upwards [coeFn_charT4Lp 2 k] with x hx
    rw [hx]

/-- Each Fourier coefficient is bounded by the `L²` norm. -/
theorem norm_torusFourierCoeff_le (f : Lp ℂ 2 haarT4) (k : Z4) :
    ‖torusFourierCoeff f k‖ ≤ ‖f‖ := by
  rw [← torusFourierBasis_repr]
  calc
    ‖torusFourierBasis.repr f k‖ ≤ ‖torusFourierBasis.repr f‖ :=
      lp.norm_apply_le_norm (by norm_num) _ _
    _ = ‖f‖ := torusFourierBasis.repr.norm_map f

/-- Every `L²` function is the `L²` sum of its product-torus Fourier
series.  This `HasSum` statement, rather than a raw `tsum`, records the
required convergence. -/
theorem hasSum_torusFourier_series_L2 (f : Lp ℂ 2 haarT4) :
    HasSum (fun k => torusFourierCoeff f k • charT4Lp 2 k) f := by
  simpa [← coe_torusFourierBasis, torusFourierBasis_repr] using
    torusFourierBasis.hasSum_repr f

/-- Parseval's identity for inner products on the product torus. -/
theorem hasSum_conj_mul_torusFourierCoeff
    (f g : Lp ℂ 2 haarT4) :
    HasSum
      (fun k => conj (torusFourierCoeff f k) * torusFourierCoeff g k)
      (∫ x, conj (f x) * g x ∂haarT4) := by
  simp_rw [mul_comm (conj _)]
  refine HasSum.congr_fun
    (torusFourierBasis.hasSum_inner_mul_inner f g) (fun k => ?_)
  simp only [← torusFourierBasis_repr, HilbertBasis.repr_apply_apply,
    inner_conj_symm, mul_comm (inner ℂ f _)]

/-- Parseval's identity for squared norms on the product torus. -/
theorem hasSum_sq_torusFourierCoeff (f : Lp ℂ 2 haarT4) :
    HasSum (fun k => ‖torusFourierCoeff f k‖ ^ 2)
      (∫ x, ‖f x‖ ^ 2 ∂haarT4) := by
  simpa only [← RCLike.inner_apply', inner_self_eq_norm_sq, ← integral_re
    (MeasureTheory.L2.integrable_inner f f)] using
    RCLike.hasSum_re ℂ (hasSum_conj_mul_torusFourierCoeff f f)

/-- `tsum` form of Plancherel, derived from the convergent `HasSum`
statement. -/
theorem tsum_sq_torusFourierCoeff (f : Lp ℂ 2 haarT4) :
    ∑' k, ‖torusFourierCoeff f k‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂haarT4 :=
  (hasSum_sq_torusFourierCoeff f).tsum_eq

/-- Fourier coefficients determine an `L²` function. -/
theorem torusFourierCoeff_l2_ext {f g : Lp ℂ 2 haarT4}
    (h : ∀ k, torusFourierCoeff f k = torusFourierCoeff g k) :
    f = g := by
  apply torusFourierBasis.repr.injective
  ext k
  simpa only [torusFourierBasis_repr] using h k

/-- Passing an `L²` function to the quotient does not change its Fourier
coefficients. -/
theorem torusFourierCoeff_toLp (f : T4 → ℂ)
    (hf : MemLp f 2 haarT4) (k : Z4) :
    torusFourierCoeff (hf.toLp f) k = torusFourierCoeff f k := by
  unfold torusFourierCoeff
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

/-! ## Bounded and finite multiplier interfaces -/

/-- The `ℓ²(Z4)` coefficient space used by the Fourier basis. -/
abbrev TorusL2Sequence := lp (fun _ : Z4 => ℂ) 2

/-- Coordinatewise multiplication by a uniformly bounded symbol on
`ℓ²(Z4)`. -/
def torusDiagonalCLM (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C) :
    TorusL2Sequence →L[ℂ] TorusL2Sequence :=
  lp.mapCLM 2
    (fun k => symbol k • ContinuousLinearMap.id ℂ ℂ) hC (by
      intro k
      simpa [norm_smul, ContinuousLinearMap.norm_id] using hsymbol k)

@[simp] theorem torusDiagonalCLM_apply
    (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C)
    (a : TorusL2Sequence) (k : Z4) :
    torusDiagonalCLM symbol C hC hsymbol a k = symbol k * a k := by
  rfl

/-- Operator-norm control for the diagonal action on coefficients. -/
theorem torusDiagonalCLM_norm_le
    (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C) :
    ‖torusDiagonalCLM symbol C hC hsymbol‖ ≤ C :=
  lp.norm_mapCLM_le 2 _ hC _

/-- The bounded `L²` Fourier multiplier obtained by conjugating the
coefficient-space diagonal map by the product-torus Fourier basis. -/
def torusL2MultiplierCLM
    (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C) :
    Lp ℂ 2 haarT4 →L[ℂ] Lp ℂ 2 haarT4 :=
  torusFourierBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((torusDiagonalCLM symbol C hC hsymbol).comp
      torusFourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The bounded multiplier has exactly the prescribed Fourier
coefficients. -/
@[simp] theorem torusFourierCoeff_l2MultiplierCLM
    (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C)
    (f : Lp ℂ 2 haarT4) (k : Z4) :
    torusFourierCoeff (torusL2MultiplierCLM symbol C hC hsymbol f) k =
      symbol k * torusFourierCoeff f k := by
  rw [← torusFourierBasis_repr, ← torusFourierBasis_repr]
  change torusFourierBasis.repr
      (torusFourierBasis.repr.symm
        (torusDiagonalCLM symbol C hC hsymbol
          (torusFourierBasis.repr f))) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Pointwise norm bound for the bounded Fourier multiplier. -/
theorem torusL2MultiplierCLM_apply_norm_le
    (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C)
    (f : Lp ℂ 2 haarT4) :
    ‖torusL2MultiplierCLM symbol C hC hsymbol f‖ ≤ C * ‖f‖ := by
  change ‖torusFourierBasis.repr.symm
      (torusDiagonalCLM symbol C hC hsymbol
        (torusFourierBasis.repr f))‖ ≤ _
  rw [torusFourierBasis.repr.symm.norm_map,
    ← torusFourierBasis.repr.norm_map f]
  exact (torusDiagonalCLM symbol C hC hsymbol).le_of_opNorm_le
    (torusDiagonalCLM_norm_le symbol C hC hsymbol)
    (torusFourierBasis.repr f)

/-- Operator-norm bound for the bounded Fourier multiplier. -/
theorem torusL2MultiplierCLM_norm_le
    (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C) :
    ‖torusL2MultiplierCLM symbol C hC hsymbol‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact torusL2MultiplierCLM_apply_norm_le symbol C hC hsymbol

/-- Synthesis of finitely many Fourier modes in `L²`. -/
def torusFiniteSynthesis (s : Finset Z4) (a : Z4 → ℂ) :
    Lp ℂ 2 haarT4 :=
  ∑ k ∈ s, a k • charT4Lp 2 k

/-- Coefficient extraction for finite `L²` synthesis. -/
theorem torusFourierCoeff_finiteSynthesis
    (s : Finset Z4) (a : Z4 → ℂ) (k : Z4) :
    torusFourierCoeff (torusFiniteSynthesis s a) k =
      if k ∈ s then a k else 0 := by
  classical
  rw [← torusFourierBasis_repr]
  simp only [torusFiniteSynthesis, map_sum, map_smul]
  rw [← coe_torusFourierBasis]
  simp only [torusFourierBasis.repr_self]
  simp only [lp.coeFn_sum, lp.coeFn_smul, lp.coeFn_single,
    Finset.sum_apply, Pi.smul_apply]
  simp [Pi.single_apply]

/-- Multiplication by a symbol on a finite set of Fourier modes. -/
def torusFiniteMultiplier (symbol : Z4 → ℂ)
    (s : Finset Z4) (a : Z4 → ℂ) : Lp ℂ 2 haarT4 :=
  torusFiniteSynthesis s fun k => symbol k * a k

/-- The defining coefficient formula for the finite Fourier multiplier. -/
theorem torusFourierCoeff_finiteMultiplier
    (symbol : Z4 → ℂ) (s : Finset Z4) (a : Z4 → ℂ) (k : Z4) :
    torusFourierCoeff (torusFiniteMultiplier symbol s a) k =
      if k ∈ s then symbol k * a k else 0 := by
  exact torusFourierCoeff_finiteSynthesis s (fun l => symbol l * a l) k

/-- A graph-style Fourier multiplier specification.  It applies equally to
bounded and unbounded symbols and therefore does not assert nonexistent
global domains. -/
def IsTorusL2Multiplier (symbol : Z4 → ℂ)
    (f g : Lp ℂ 2 haarT4) : Prop :=
  ∀ k, torusFourierCoeff g k = symbol k * torusFourierCoeff f k

/-- The constructed bounded multiplier satisfies the domain-independent
multiplier specification. -/
theorem isTorusL2Multiplier_l2MultiplierCLM
    (symbol : Z4 → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ k, ‖symbol k‖ ≤ C)
    (f : Lp ℂ 2 haarT4) :
    IsTorusL2Multiplier symbol f
      (torusL2MultiplierCLM symbol C hC hsymbol f) :=
  torusFourierCoeff_l2MultiplierCLM symbol C hC hsymbol f

/-- A multiplier output, when it exists, is unique in `L²`. -/
theorem IsTorusL2Multiplier.unique {symbol : Z4 → ℂ}
    {f g h : Lp ℂ 2 haarT4}
    (hg : IsTorusL2Multiplier symbol f g)
    (hh : IsTorusL2Multiplier symbol f h) :
    g = h :=
  torusFourierCoeff_l2_ext fun k => (hg k).trans (hh k).symm

/-- The identity symbol acts as the identity. -/
theorem isTorusL2Multiplier_one (f : Lp ℂ 2 haarT4) :
    IsTorusL2Multiplier (fun _ => 1) f f := by
  intro k
  simp

/-- Multiplier specifications compose by pointwise multiplication of their
symbols. -/
theorem IsTorusL2Multiplier.comp {symbol₁ symbol₂ : Z4 → ℂ}
    {f g h : Lp ℂ 2 haarT4}
    (h₁ : IsTorusL2Multiplier symbol₁ f g)
    (h₂ : IsTorusL2Multiplier symbol₂ g h) :
    IsTorusL2Multiplier (fun k => symbol₂ k * symbol₁ k) f h := by
  intro k
  rw [h₂ k, h₁ k]
  ring

/-- Finite synthesis realizes the multiplier specification without any
summability assumption. -/
theorem isTorusL2Multiplier_finite
    (symbol : Z4 → ℂ) (s : Finset Z4) (a : Z4 → ℂ) :
    IsTorusL2Multiplier symbol
      (torusFiniteSynthesis s a)
      (torusFiniteMultiplier symbol s a) := by
  intro k
  rw [torusFourierCoeff_finiteMultiplier,
    torusFourierCoeff_finiteSynthesis]
  split_ifs
  · rfl
  · simp

/-- General two-variable normalization ledger: each integration against
the paper measure contributes one factor `(2π)⁴`. -/
theorem paperKernelCoeff_eq_volume_sq_smul_normalized
    (K : T4 → T4 → ℂ) (α β : Z4) :
    paperKernelCoeff K α β =
      ((2 * Real.pi) ^ dim : ℝ) ^ 2 •
        normalizedKernelCoeff K α β := by
  have h2π : (ENNReal.ofReal ((2 * Real.pi) ^ dim)).toReal =
      (2 * Real.pi) ^ dim := ENNReal.toReal_ofReal (by positivity)
  simp only [paperKernelCoeff, normalizedKernelCoeff, paperMeasure,
    integral_smul_measure, integral_smul, h2π]
  rw [smul_smul, ← pow_two]

/-- Positive-exponential normalized kernel coefficients are iterated
standard coefficients at the opposite frequencies. -/
theorem normalizedKernelCoeff_eq_iterated_torusFourierCoeff
    (K : T4 → T4 → ℂ) (α β : Z4) :
    normalizedKernelCoeff K α β =
      torusFourierCoeff (fun x => torusFourierCoeff (K x) (-β)) (-α) := by
  unfold normalizedKernelCoeff torusFourierCoeff
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∫ y, charT4 α x * charT4 β y * K x y ∂haarT4) =
      conj (charT4 (-α) x) *
        ∫ y, conj (charT4 (-β) y) * K x y ∂haarT4
    rw [conj_charT4_neg]
    calc
      _ = ∫ y, charT4 α x * (charT4 β y * K x y) ∂haarT4 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by ring
      _ = charT4 α x * ∫ y, charT4 β y * K x y ∂haarT4 :=
        integral_const_mul _ _
      _ = charT4 α x *
          ∫ y, conj (charT4 (-β) y) * K x y ∂haarT4 := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change charT4 β y * K x y =
            conj (charT4 (-β) y) * K x y
          rw [conj_charT4_neg]

/-- A rank-one normalized kernel coefficient factors into two
one-variable integrals.  No Fubini theorem is needed. -/
theorem normalizedKernelCoeff_rankOne (f g : T4 → ℂ) (α β : Z4) :
    normalizedKernelCoeff (fun x y => f x * g y) α β =
      (∫ x, charT4 α x * f x ∂haarT4) *
        ∫ y, charT4 β y * g y ∂haarT4 := by
  have h : ∀ x : T4,
      (∫ y, charT4 α x * charT4 β y * (f x * g y) ∂haarT4) =
        (charT4 α x * f x) *
          ∫ y, charT4 β y * g y ∂haarT4 := by
    intro x
    rw [← integral_const_mul]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun y => by ring)
  unfold normalizedKernelCoeff
  simp_rw [h]
  exact integral_mul_const _ _

/-- A rank-one paper-normalized kernel coefficient factors into the two
unnormalized one-variable coefficients. -/
theorem paperKernelCoeff_rankOne (f g : T4 → ℂ) (α β : Z4) :
    paperKernelCoeff (fun x y => f x * g y) α β =
      paperFourierCoeff f α * paperFourierCoeff g β := by
  have h : ∀ x : T4,
      (∫ y, charT4 α x * charT4 β y * (f x * g y)
          ∂paperMeasure) =
        (charT4 α x * f x) *
          ∫ y, charT4 β y * g y ∂paperMeasure := by
    intro x
    rw [← integral_const_mul]
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun y => by ring)
  unfold paperKernelCoeff paperFourierCoeff
  simp_rw [h]
  exact integral_mul_const _ _

/-- The paper and normalized rank-one coefficients differ by two copies of
the measure factor `(2π)⁴`. -/
theorem paperKernelCoeff_rankOne_eq_normalized
    (f g : T4 → ℂ) (α β : Z4) :
    paperKernelCoeff (fun x y => f x * g y) α β =
      ((2 * Real.pi) ^ dim : ℝ) ^ 2 •
        normalizedKernelCoeff (fun x y => f x * g y) α β := by
  exact paperKernelCoeff_eq_volume_sq_smul_normalized _ α β

/-! ## Operator-sign ledger -/

/-- The rank-one operator pairing with `e_{-α}` in the conjugate-linear
slot, written at probability-Haar normalization. -/
def rankOneOperatorPairing (f g : T4 → ℂ) (α β : Z4) : ℂ :=
  (∫ x, conj (charT4 (-α) x) * f x ∂haarT4) *
    ∫ y, charT4 β y * g y ∂haarT4

/-- Sign check for equation (3.23): `e_{-α}` in the operator's
conjugate-linear slot produces the paper's positive `e_α` convention. -/
theorem rankOneOperatorPairing_eq_normalizedKernelCoeff
    (f g : T4 → ℂ) (α β : Z4) :
    rankOneOperatorPairing f g α β =
      normalizedKernelCoeff (fun x y => f x * g y) α β := by
  unfold rankOneOperatorPairing
  rw [normalizedKernelCoeff_rankOne]
  simp_rw [conj_charT4_neg]

end

end Anderson4D
