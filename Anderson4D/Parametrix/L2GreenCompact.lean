import Anderson4D.Parametrix.L2Fredholm
import Anderson4D.Parametrix.L2Realization
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Compactness of the torus Green multiplier

The multiplier `(1 + |k|²)⁻¹` is the operator-norm limit of its finite
Fourier-cube truncations.  This supplies the compactness input required
by the one-sided Fredholm parametrix argument.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Topology

/-! ## Finite Fourier cubes -/

/-- The integer-frequency cube `[-N,N]⁴`. -/
def z4Cube (N : ℕ) : Finset Z4 :=
  Fintype.piFinset fun _ : Fin dim =>
    Finset.Icc (-(N : ℤ)) (N : ℤ)

@[simp] theorem mem_z4Cube (N : ℕ) (k : Z4) :
    k ∈ z4Cube N ↔
      ∀ i : Fin dim, -(N : ℤ) ≤ k i ∧ k i ≤ (N : ℤ) := by
  simp [z4Cube]

theorem exists_coord_abs_gt_of_not_mem_z4Cube
    (N : ℕ) (k : Z4) (hk : k ∉ z4Cube N) :
    ∃ i : Fin dim, (N : ℤ) < |k i| := by
  by_contra h
  push Not at h
  apply hk
  rw [mem_z4Cube]
  intro i
  exact abs_le.mp (h i)

/-- Green symbol cut off to the finite frequency cube. -/
def greenL2TruncatedSymbol (N : ℕ) (k : Z4) : ℂ :=
  if k ∈ z4Cube N then greenL2Symbol k else 0

theorem greenL2TruncatedSymbol_norm_le_one (N : ℕ) (k : Z4) :
    ‖greenL2TruncatedSymbol N k‖ ≤ 1 := by
  classical
  simp only [greenL2TruncatedSymbol]
  split_ifs
  · exact greenL2Symbol_norm_le_one k
  · simp

/-- The finite Fourier-cube truncation of `greenL2Op`. -/
def greenL2TruncatedOp (N : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  torusL2MultiplierCLM (greenL2TruncatedSymbol N) 1 zero_le_one
    (greenL2TruncatedSymbol_norm_le_one N)

@[simp] theorem torusFourierCoeff_greenL2TruncatedOp
    (N : ℕ) (f : TorusL2) (k : Z4) :
    torusFourierCoeff (greenL2TruncatedOp N f) k =
      greenL2TruncatedSymbol N k * torusFourierCoeff f k :=
  torusFourierCoeff_l2MultiplierCLM
    (greenL2TruncatedSymbol N) 1 zero_le_one
    (greenL2TruncatedSymbol_norm_le_one N) f k

/-! ## Finite-rank compactness -/

theorem isCompactOperator_torus_rankOne (k : Z4) :
    IsCompactOperator
      (InnerProductSpace.rankOne ℂ
        (torusFourierBasis k) (torusFourierBasis k)) := by
  rw [InnerProductSpace.rankOne_def']
  exact
    (isCompactOperator_of_locallyCompactSpace_dom
      (innerSL ℂ (torusFourierBasis k))).clm_comp
        (ContinuousLinearMap.toSpanSingleton ℂ (torusFourierBasis k))

@[simp] theorem torusFourierCoeff_rankOne_basis
    (k l : Z4) (f : TorusL2) :
    torusFourierCoeff
        (InnerProductSpace.rankOne ℂ
          (torusFourierBasis k) (torusFourierBasis k) f) l =
      if l = k then torusFourierCoeff f k else 0 := by
  rw [← torusFourierBasis_repr]
  rw [HilbertBasis.repr_apply_apply]
  have hk :
      ⟪torusFourierBasis k, f⟫_ℂ =
        torusFourierCoeff f k := by
    rw [← torusFourierBasis_repr,
      HilbertBasis.repr_apply_apply]
  simp only [InnerProductSpace.rankOne_apply, inner_smul_right,
    hk, orthonormal_iff_ite.mp torusFourierBasis.orthonormal]
  split_ifs with h
  · subst l
    simp
  · simp

theorem greenL2TruncatedOp_eq_rankOne_sum (N : ℕ) :
    greenL2TruncatedOp N =
      ∑ k ∈ z4Cube N,
        greenL2Symbol k •
          InnerProductSpace.rankOne ℂ
            (torusFourierBasis k) (torusFourierBasis k) := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply torusFourierCoeff_l2_ext
  intro l
  rw [torusFourierCoeff_greenL2TruncatedOp]
  have hcoeff (g : TorusL2) :
      torusFourierCoeff g l =
        innerSL ℂ (torusFourierBasis l) g := by
    rw [← torusFourierBasis_repr,
      HilbertBasis.repr_apply_apply]
    rfl
  conv_rhs => rw [hcoeff]
  simp only [sum_apply, smul_apply, map_sum, map_smul,
    InnerProductSpace.rankOne_apply, innerSL_apply_apply,
    smul_eq_mul]
  simp_rw [orthonormal_iff_ite.mp torusFourierBasis.orthonormal]
  have hk (k : Z4) :
      ⟪torusFourierBasis k, f⟫_ℂ =
        torusFourierCoeff f k := by
    rw [← torusFourierBasis_repr,
      HilbertBasis.repr_apply_apply]
  simp_rw [hk]
  simp [greenL2TruncatedSymbol]

theorem isCompactOperator_finset_sum_torus
    {ι : Type*} (s : Finset ι)
    (F : ι → TorusL2 →L[ℂ] TorusL2)
    (hF : ∀ i ∈ s, IsCompactOperator (F i)) :
    IsCompactOperator
      ((∑ i ∈ s, F i) : TorusL2 →L[ℂ] TorusL2) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change IsCompactOperator
        (fun _ : TorusL2 => (0 : TorusL2))
      exact isCompactOperator_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem isCompactOperator_greenL2TruncatedOp (N : ℕ) :
    IsCompactOperator (greenL2TruncatedOp N) := by
  rw [greenL2TruncatedOp_eq_rankOne_sum]
  classical
  refine isCompactOperator_finset_sum_torus
    (z4Cube N)
    (fun k =>
      greenL2Symbol k •
        InnerProductSpace.rankOne ℂ
          (torusFourierBasis k) (torusFourierBasis k)) ?_
  intro k hk
  exact (isCompactOperator_torus_rankOne k).smul
    (greenL2Symbol k)

/-! ## Uniform tail control -/

/-- Uniform bound for frequencies outside `z4Cube N`. -/
def greenL2TailBound (N : ℕ) : ℝ :=
  (1 + (N : ℝ) ^ 2)⁻¹

theorem greenL2TailBound_nonneg (N : ℕ) :
    0 ≤ greenL2TailBound N := by
  unfold greenL2TailBound
  positivity

/-- Symbol of the Fourier tail discarded by the finite truncation. -/
def greenL2TailSymbol (N : ℕ) (k : Z4) : ℂ :=
  if k ∈ z4Cube N then 0 else greenL2Symbol k

theorem greenL2TailSymbol_norm_le
    (N : ℕ) (k : Z4) :
    ‖greenL2TailSymbol N k‖ ≤ greenL2TailBound N := by
  classical
  by_cases hk : k ∈ z4Cube N
  · simp [greenL2TailSymbol, hk, greenL2TailBound_nonneg]
  · rw [greenL2TailSymbol, if_neg hk]
    obtain ⟨i, hi⟩ :=
      exists_coord_abs_gt_of_not_mem_z4Cube N k hk
    have hiR : (N : ℝ) < |(k i : ℝ)| := by
      exact_mod_cast hi
    have hsquare :
        (N : ℝ) ^ 2 ≤ (k i : ℝ) ^ 2 := by
      nlinarith [abs_nonneg (k i : ℝ), sq_abs (k i : ℝ)]
    have hterm :
        (k i : ℝ) ^ 2 ≤ ∑ j, (k j : ℝ) ^ 2 :=
      Finset.single_le_sum
        (fun j _ => sq_nonneg (k j : ℝ))
        (Finset.mem_univ i)
    have hden :
        1 + (N : ℝ) ^ 2 ≤
          1 + ∑ j, (k j : ℝ) ^ 2 := by
      linarith
    have hbasepos : 0 < 1 + (N : ℝ) ^ 2 := by
      positivity
    have hdenpos :
        0 < 1 + ∑ j, (k j : ℝ) ^ 2 := by
      have : 0 ≤ ∑ j, (k j : ℝ) ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg (k j : ℝ)
      linarith
    simp only [greenL2Symbol, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (inv_nonneg.mpr hdenpos.le)]
    unfold greenL2TailBound
    exact (inv_le_inv₀ hdenpos hbasepos).2 hden

theorem tendsto_greenL2TailBound :
    Filter.Tendsto greenL2TailBound Filter.atTop (𝓝 0) := by
  have hinv :
      Filter.Tendsto (fun N : ℕ => ((N : ℝ))⁻¹)
        Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  apply squeeze_zero'
    (Filter.Eventually.of_forall
      (fun N => greenL2TailBound_nonneg N)) _ hinv
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hNreal
  have hden :
      (N : ℝ) ≤ 1 + (N : ℝ) ^ 2 := by
    nlinarith
  unfold greenL2TailBound
  exact
    (inv_le_inv₀ (by positivity : 0 < 1 + (N : ℝ) ^ 2)
      hNpos).2 hden

/-- The discarded Fourier tail as a bounded operator. -/
def greenL2TailOp (N : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  torusL2MultiplierCLM (greenL2TailSymbol N)
    (greenL2TailBound N) (greenL2TailBound_nonneg N)
    (greenL2TailSymbol_norm_le N)

@[simp] theorem torusFourierCoeff_greenL2TailOp
    (N : ℕ) (f : TorusL2) (k : Z4) :
    torusFourierCoeff (greenL2TailOp N f) k =
      greenL2TailSymbol N k * torusFourierCoeff f k :=
  torusFourierCoeff_l2MultiplierCLM
    (greenL2TailSymbol N) (greenL2TailBound N)
    (greenL2TailBound_nonneg N)
    (greenL2TailSymbol_norm_le N) f k

theorem torusFourierCoeff_sub
    (f g : TorusL2) (k : Z4) :
    torusFourierCoeff ((f - g : TorusL2)) k =
      torusFourierCoeff f k - torusFourierCoeff g k := by
  have hcoeff (u : TorusL2) :
      torusFourierCoeff u k =
        innerSL ℂ (torusFourierBasis k) u := by
    rw [← torusFourierBasis_repr,
      HilbertBasis.repr_apply_apply]
    rfl
  calc
    torusFourierCoeff ((f - g : TorusL2)) k =
        innerSL ℂ (torusFourierBasis k) (f - g) :=
      hcoeff (f - g)
    _ =
        innerSL ℂ (torusFourierBasis k) f -
          innerSL ℂ (torusFourierBasis k) g :=
      map_sub _ f g
    _ =
        torusFourierCoeff f k -
          torusFourierCoeff g k := by
      rw [← hcoeff f, ← hcoeff g]

theorem greenL2Op_sub_truncated_eq_tail (N : ℕ) :
    greenL2Op - greenL2TruncatedOp N =
      greenL2TailOp N := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply torusFourierCoeff_l2_ext
  intro k
  calc
    torusFourierCoeff
        ((greenL2Op - greenL2TruncatedOp N) f) k =
        torusFourierCoeff
            ((greenL2Op f -
              greenL2TruncatedOp N f : TorusL2)) k := by
      rw [sub_apply]
    _ =
        torusFourierCoeff (greenL2Op f) k -
          torusFourierCoeff (greenL2TruncatedOp N f) k :=
      torusFourierCoeff_sub _ _ k
    _ =
        greenL2Symbol k * torusFourierCoeff f k -
          greenL2TruncatedSymbol N k *
            torusFourierCoeff f k := by
      rw [torusFourierCoeff_greenL2Op,
        torusFourierCoeff_greenL2TruncatedOp]
    _ =
        greenL2TailSymbol N k *
          torusFourierCoeff f k := by
      by_cases hk : k ∈ z4Cube N
      · simp [greenL2TruncatedSymbol, greenL2TailSymbol, hk]
      · simp [greenL2TruncatedSymbol, greenL2TailSymbol, hk]
    _ = torusFourierCoeff (greenL2TailOp N f) k :=
      (torusFourierCoeff_greenL2TailOp N f k).symm

theorem norm_greenL2Op_sub_truncated_le (N : ℕ) :
    ‖greenL2Op - greenL2TruncatedOp N‖ ≤
      greenL2TailBound N := by
  rw [greenL2Op_sub_truncated_eq_tail]
  exact torusL2MultiplierCLM_norm_le
    (greenL2TailSymbol N) (greenL2TailBound N)
    (greenL2TailBound_nonneg N)
    (greenL2TailSymbol_norm_le N)

theorem tendsto_greenL2TruncatedOp :
    Filter.Tendsto greenL2TruncatedOp Filter.atTop
      (𝓝 greenL2Op) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
    (fun N => norm_nonneg (greenL2TruncatedOp N - greenL2Op))
    (fun N => by
      simpa only [norm_sub_rev] using
        norm_greenL2Op_sub_truncated_le N)
    tendsto_greenL2TailBound

/-- The torus Green operator is compact. -/
theorem isCompactOperator_greenL2Op :
    IsCompactOperator greenL2Op :=
  isCompactOperator_of_tendsto tendsto_greenL2TruncatedOp
    (Filter.Eventually.of_forall
      isCompactOperator_greenL2TruncatedOp)

/-- Composing the compact Green operator with an arbitrary bounded
multiplication operator preserves compactness. -/
theorem isCompactOperator_Kop_greenL2Op
    (M : TorusL2 →L[ℂ] TorusL2) :
    IsCompactOperator (Kop greenL2Op M) := by
  exact isCompactOperator_greenL2Op.comp_clm M

end

end Anderson4D
