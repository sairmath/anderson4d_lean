import Anderson4D.Main.FixedTruncationGaussian

/-!
# Removing the fixed perturbative truncation

This file carries out the `B → ∞` part of paper (3.38)--(3.39).  The
finite square `m₁,m₂ ≤ B` is separated into a coefficient rectangle
and a mode-dependent four-point form.  Proposition 3.6's global
antidiagonal identity evaluates the triangular part, while its uniform
geometric coefficient bound controls the two corner tails.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ComplexConjugate NNReal

/-- The square coefficient sum `𝔛_B` used immediately before (3.36). -/
def prop36RectangleSum (X : ℕ → ℕ → ℝ) (B : ℕ) : ℝ :=
  ∑ m₁ : Fin B, ∑ m₂ : Fin B, X (m₁ + 1) (m₂ + 1)

/-- A mode together with the Boolean choice in the real-part
expansion. -/
abbrev FixedModeSign (s : ℕ) := Fin s × Bool

def fixedModeSignPair {s : ℕ}
    (modes : Fin s → Z4 × Z4) (u : FixedModeSign s) :
    Z4 × Z4 :=
  if u.2 then (-(modes u.1).1, -(modes u.1).2) else modes u.1

def fixedModeSignCoeff {s : ℕ}
    (c : Fin s → ℂ) (u : FixedModeSign s) : ℂ :=
  if u.2 then conj (c u.1) / 2 else c u.1 / 2

/-- The mode-dependent four-point form left after the perturbative
orders have been summed out. -/
def fixedModePairVariance {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) : ℂ :=
  ∑ u : FixedModeSign s, ∑ v : FixedModeSign s,
    fixedModeSignCoeff c u * fixedModeSignCoeff c v *
      fourPointHCoeff
        (fixedModeSignPair modes u).1
        (fixedModeSignPair modes u).2
        (fixedModeSignPair modes v).1
        (fixedModeSignPair modes v).2

/-- Reindex an atom by its perturbative order first and its signed mode
second. -/
def FixedTruncationAtom.equivOrderMode (s B : ℕ) :
    FixedTruncationAtom s B ≃ Fin B × FixedModeSign s where
  toFun a := (a.orderIndex, a.mode, a.conjugated)
  invFun p :=
    { orderIndex := p.1, mode := p.2.1, conjugated := p.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem FixedTruncationAtom.equivOrderMode_symm_apply
    {s B : ℕ} (p : Fin B × FixedModeSign s) :
    (FixedTruncationAtom.equivOrderMode s B).symm p =
      { orderIndex := p.1, mode := p.2.1,
        conjugated := p.2.2 } :=
  rfl

/-- Simultaneously regroup two atoms into an order pair and a signed
mode pair. -/
def FixedTruncationAtom.pairEquivOrderMode (s B : ℕ) :
    (FixedTruncationAtom s B × FixedTruncationAtom s B) ≃
      (Fin B × Fin B) × (FixedModeSign s × FixedModeSign s) where
  toFun p :=
    ((p.1.orderIndex, p.2.orderIndex),
      ((p.1.mode, p.1.conjugated), (p.2.mode, p.2.conjugated)))
  invFun p :=
    ({ orderIndex := p.1.1, mode := p.2.1.1,
       conjugated := p.2.1.2 },
     { orderIndex := p.1.2, mode := p.2.2.1,
       conjugated := p.2.2.2 })
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem FixedTruncationAtom.pairEquivOrderMode_symm_apply
    {s B : ℕ}
    (p : (Fin B × Fin B) ×
      (FixedModeSign s × FixedModeSign s)) :
    (FixedTruncationAtom.pairEquivOrderMode s B).symm p =
      ({ orderIndex := p.1.1, mode := p.2.1.1,
         conjugated := p.2.1.2 },
       { orderIndex := p.1.2, mode := p.2.2.1,
         conjugated := p.2.2.2 }) :=
  rfl

/-- Exact separation of the perturbative rectangle from the signed
mode covariance. -/
theorem fixedTruncationPairVariance_eq_rectangle_mul
    (X : ℕ → ℕ → ℝ) (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    fixedTruncationPairVariance X B modes c =
      (prop36RectangleSum X B : ℂ) *
        fixedModePairVariance modes c := by
  unfold fixedTruncationPairVariance
  rw [← Fintype.sum_prod_type']
  rw [← (FixedTruncationAtom.pairEquivOrderMode s B).symm.sum_comp
    (fun p : FixedTruncationAtom s B × FixedTruncationAtom s B =>
      p.1.coeff c * p.2.coeff c *
        fixedTruncationAtomPairLimit X modes p.1 p.2)]
  simp only [Fintype.sum_prod_type,
    FixedTruncationAtom.pairEquivOrderMode_symm_apply,
    FixedTruncationAtom.coeff, FixedTruncationAtom.modePair,
    FixedTruncationAtom.order, fixedTruncationAtomPairLimit]
  unfold prop36RectangleSum fixedModePairVariance
    fixedModeSignCoeff fixedModeSignPair
  push_cast
  rw [Fintype.sum_mul_sum]
  simp only [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro m₁
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro b
  rw [Fintype.sum_mul_sum]
  apply Fintype.sum_congr
  intro m₂
  apply Fintype.sum_congr
  intro k
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro d
  ring

/-- Simultaneously negating all four external modes leaves the real
four-point coefficient unchanged. -/
theorem fourPointHCoeff_neg_all
    (α₁ β₁ α₂ β₂ : Z4) :
    fourPointHCoeff (-α₁) (-β₁) (-α₂) (-β₂) =
      fourPointHCoeff α₁ β₁ α₂ β₂ := by
  calc
    fourPointHCoeff (-α₁) (-β₁) (-α₂) (-β₂) =
        fourPointHCoeff (-α₂) (-β₂) (-α₁) (-β₁) :=
      fourPointHCoeff_swap_pairs _ _ _ _
    _ = fourPointHCoeff α₁ β₁ α₂ β₂ := by
      simpa only [neg_neg] using
        (fourPointHCoeff_cross_swap α₁ β₁ (-α₂) (-β₂)).symm

/-- Moving a simultaneous sign change from the first mode pair to the
second preserves the coefficient. -/
theorem fourPointHCoeff_neg_left_eq_neg_right
    (α₁ β₁ α₂ β₂ : Z4) :
    fourPointHCoeff (-α₁) (-β₁) α₂ β₂ =
      fourPointHCoeff α₁ β₁ (-α₂) (-β₂) := by
  calc
    fourPointHCoeff (-α₁) (-β₁) α₂ β₂ =
        fourPointHCoeff α₂ β₂ (-α₁) (-β₁) :=
      fourPointHCoeff_swap_pairs _ _ _ _
    _ = fourPointHCoeff α₁ β₁ (-α₂) (-β₂) :=
      (fourPointHCoeff_cross_swap α₁ β₁ α₂ β₂).symm

theorem conj_fourPointHCoeff
    (α₁ β₁ α₂ β₂ : Z4) :
    conj (fourPointHCoeff α₁ β₁ α₂ β₂) =
      fourPointHCoeff α₁ β₁ α₂ β₂ := by
  apply Complex.ext
  · simp only [Complex.conj_re]
  · simp only [Complex.conj_im, fourPointHCoeff_im_eq_zero, neg_zero]

theorem sum_div_two_mul_div_two
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (b : κ → ℂ) (H : ι → κ → ℂ) :
    (∑ i, ∑ j, (a i / 2) * (b j / 2) * H i j) =
      (∑ i, ∑ j, a i * b j * H i j) * (1 / 4) := by
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro i
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro j
  ring

/-- The four-point quadratic form before multiplication by the
geometric limiting prefactor. -/
def unscaledLimitVariance {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) : ℝ :=
  ((∑ i, ∑ j, c i * c j *
      fourPointHCoeff
        (modes i).1 (modes i).2
        (modes j).1 (modes j).2).re +
    (∑ i, ∑ j, c i * conj (c j) *
      fourPointHCoeff
        (modes i).1 (modes i).2
        (-(modes j).1) (-(modes j).2)).re) / 2

theorem limitVar_eq_prefactor_mul_unscaled
    (lam : ℝ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    limitVar lam modes c =
      limitPrefactor lam * unscaledLimitVariance modes c := by
  unfold limitVar unscaledLimitVariance
  ring

/-- The Boolean signed-mode expansion is exactly the real unscaled
four-point variance. -/
theorem fixedModePairVariance_eq_unscaled
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    fixedModePairVariance modes c =
      (unscaledLimitVariance modes c : ℂ) := by
  let P : ℂ :=
    ∑ i, ∑ j, c i * c j *
      fourPointHCoeff
        (modes i).1 (modes i).2
        (modes j).1 (modes j).2
  let Q : ℂ :=
    ∑ i, ∑ j, c i * conj (c j) *
      fourPointHCoeff
        (modes i).1 (modes i).2
        (-(modes j).1) (-(modes j).2)
  have hP :
      (∑ i, ∑ j, conj (c i) * conj (c j) *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (modes j).1 (modes j).2) = conj P := by
    simp only [P, map_sum, map_mul, conj_fourPointHCoeff]
  have hQ :
      (∑ i, ∑ j, conj (c i) * c j *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (-(modes j).1) (-(modes j).2)) = conj Q := by
    simp only [Q, map_sum, map_mul,
      starRingEnd_self_apply, conj_fourPointHCoeff]
  have hPscaled :
      (∑ i, ∑ j, (conj (c i) / 2) * (conj (c j) / 2) *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (modes j).1 (modes j).2) = conj P * (1 / 4) := by
    rw [sum_div_two_mul_div_two, hP]
  have hQscaled :
      (∑ i, ∑ j, (conj (c i) / 2) * (c j / 2) *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (-(modes j).1) (-(modes j).2)) = conj Q * (1 / 4) := by
    rw [sum_div_two_mul_div_two, hQ]
  have hQdirectScaled :
      (∑ i, ∑ j, (c i / 2) * (conj (c j) / 2) *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (-(modes j).1) (-(modes j).2)) = Q * (1 / 4) := by
    rw [sum_div_two_mul_div_two]
  have hPdirectScaled :
      (∑ i, ∑ j, (c i / 2) * (c j / 2) *
        fourPointHCoeff
          (modes i).1 (modes i).2
          (modes j).1 (modes j).2) = P * (1 / 4) := by
    rw [sum_div_two_mul_div_two]
  unfold fixedModePairVariance fixedModeSignCoeff fixedModeSignPair
    unscaledLimitVariance
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true]
  simp_rw [fourPointHCoeff_neg_all,
    fourPointHCoeff_neg_left_eq_neg_right]
  simp_rw [Finset.sum_add_distrib]
  rw [hPscaled, hQscaled, hQdirectScaled, hPdirectScaled]
  have hPQ :
      conj P * (1 / 4) + conj Q * (1 / 4) +
            (Q * (1 / 4) + P * (1 / 4)) =
        (((P.re + Q.re) / 2 : ℝ) : ℂ) := by
    push_cast
    rw [Complex.re_eq_add_conj, Complex.re_eq_add_conj]
    ring
  simpa only [P, Q] using hPQ

/-! ## The coefficient rectangle and its corner tail -/

def prop36RectanglePairs (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 (B + 1)).product (Finset.Ico 1 (B + 1))

def prop36TrianglePairs (B : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 (2 * B + 1)).product
      (Finset.Ico 1 (2 * B + 1))).filter
    (fun p => p.1 + p.2 ≤ 2 * B)

def prop36CornerPairs (B : ℕ) : Finset (ℕ × ℕ) :=
  prop36TrianglePairs B \ prop36RectanglePairs B

theorem prop36RectanglePairs_subset_triangle (B : ℕ) :
    prop36RectanglePairs B ⊆ prop36TrianglePairs B := by
  intro p hp
  change p ∈
    (Finset.Ico 1 (B + 1)).product (Finset.Ico 1 (B + 1)) at hp
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  obtain ⟨hp₁lo, hp₁hi⟩ := Finset.mem_Ico.mp hp₁
  obtain ⟨hp₂lo, hp₂hi⟩ := Finset.mem_Ico.mp hp₂
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Ico.mpr <;> omega
  · omega

theorem prop36RectangleSum_eq_sum_pairs
    (X : ℕ → ℕ → ℝ) (B : ℕ) :
    prop36RectangleSum X B =
      ∑ p ∈ prop36RectanglePairs B, X p.1 p.2 := by
  unfold prop36RectangleSum prop36RectanglePairs
  calc
    (∑ m₁ : Fin B, ∑ m₂ : Fin B,
        X (m₁ + 1) (m₂ + 1)) =
        ∑ m₁ ∈ Finset.range B, ∑ m₂ ∈ Finset.range B,
          X (m₁ + 1) (m₂ + 1) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m₁ hm₁
      have hm₁B := Finset.mem_range.mp hm₁
      rw [dif_pos hm₁B, Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m₂ hm₂
      have hm₂B := Finset.mem_range.mp hm₂
      rw [dif_pos hm₂B]
    _ = ∑ m₁ ∈ Finset.Ico 1 (B + 1),
          ∑ m₂ ∈ Finset.Ico 1 (B + 1), X m₁ m₂ := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp_rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.add_comm 1]
    _ = ∑ p ∈
          (Finset.Ico 1 (B + 1)).product
            (Finset.Ico 1 (B + 1)), X p.1 p.2 :=
      (Finset.sum_product
        (Finset.Ico 1 (B + 1))
        (Finset.Ico 1 (B + 1))
        (fun p => X p.1 p.2)).symm

/-- The finite sum of all positive antidiagonals through total order
`2B`. -/
def prop36TriangleAntidiagonalSum
    (X : ℕ → ℕ → ℝ) (B : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (2 * B + 1), positiveAntidiagonalSum X m

theorem positiveAntidiagonalSum_one
    (X : ℕ → ℕ → ℝ) :
    positiveAntidiagonalSum X 1 = 0 := by
  unfold positiveAntidiagonalSum
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpdiag, hppos⟩ := Finset.mem_filter.mp hp
  have hsum :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hpdiag
  omega

theorem positiveAntidiagonalSum_zero
    (X : ℕ → ℕ → ℝ) :
    positiveAntidiagonalSum X 0 = 0 := by
  unfold positiveAntidiagonalSum
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpdiag, hppos⟩ := Finset.mem_filter.mp hp
  have hsum :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hpdiag
  omega

/-- Global (3.28) evaluates every finite positive triangle as the
corresponding even geometric partial sum. -/
theorem Prop36FullData.triangleAntidiagonalSum_eq_partialSum
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    (B : ℕ) :
    prop36TriangleAntidiagonalSum data.coeff B =
      prop36EvenPartialSum lam B := by
  induction B with
  | zero =>
      simp [prop36TriangleAntidiagonalSum,
        prop36EvenPartialSum, positiveAntidiagonalSum_zero]
  | succ B ih =>
      have hodd :
          positiveAntidiagonalSum data.coeff (2 * B + 1) = 0 := by
        by_cases hB : B = 0
        · subst B
          simpa using positiveAntidiagonalSum_one data.coeff
        · rw [data.sum_identity (2 * B + 1) (by omega)]
          rw [if_neg]
          intro heven
          obtain ⟨k, hk⟩ := heven
          omega
      have heven :
          positiveAntidiagonalSum data.coeff (2 * B + 2) =
            prop36MomentBase lam ^ (2 * B) := by
        rw [data.sum_identity (2 * B + 2) (by omega),
          if_pos (by
            use B + 1
            omega)]
        congr
      unfold prop36TriangleAntidiagonalSum
      rw [show 2 * (B + 1) + 1 = (2 * B + 1) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      change
        prop36TriangleAntidiagonalSum data.coeff B +
              positiveAntidiagonalSum data.coeff (2 * B + 1) +
            positiveAntidiagonalSum data.coeff (2 * B + 2) =
          prop36EvenPartialSum lam (B + 1)
      rw [ih, hodd, heven, add_zero]
      unfold prop36EvenPartialSum
      rw [Finset.sum_range_succ]

/-- Summing the positive antidiagonal fibers of the triangle is the
same as summing the triangle directly. -/
theorem sum_prop36TrianglePairs_eq_antidiagonal
    (X : ℕ → ℕ → ℝ) (B : ℕ) :
    (∑ p ∈ prop36TrianglePairs B, X p.1 p.2) =
      prop36TriangleAntidiagonalSum X B := by
  let S := prop36TrianglePairs B
  let T := Finset.range (2 * B + 1)
  have hmap : ∀ p ∈ S, p.1 + p.2 ∈ T := by
    intro p hp
    change p ∈ prop36TrianglePairs B at hp
    obtain ⟨_hpbox, hpsum⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_range.mpr (by omega)
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := S) (t := T) (g := fun p : ℕ × ℕ => p.1 + p.2)
      hmap (fun p => X p.1 p.2)
  rw [← hfiber]
  unfold prop36TriangleAntidiagonalSum
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.ext
  intro p
  have hm' : m < 2 * B + 1 := Finset.mem_range.mp hm
  constructor
  · intro hp
    obtain ⟨hpS, hpsum⟩ := Finset.mem_filter.mp hp
    change p ∈ prop36TrianglePairs B at hpS
    obtain ⟨hpbox, _hptri⟩ := Finset.mem_filter.mp hpS
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpbox
    obtain ⟨hp₁lo, _hp₁hi⟩ := Finset.mem_Ico.mp hp₁
    obtain ⟨hp₂lo, _hp₂hi⟩ := Finset.mem_Ico.mp hp₂
    apply Finset.mem_filter.mpr
    exact ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr hpsum,
      hp₁lo, hp₂lo⟩
  · intro hp
    obtain ⟨hpdiag, hp₁lo, hp₂lo⟩ := Finset.mem_filter.mp hp
    have hpsum :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp hpdiag
    apply Finset.mem_filter.mpr
    constructor
    · change p ∈ prop36TrianglePairs B
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_Ico.mpr <;> omega
      · omega
    · exact hpsum

/-- The coefficient rectangle plus its two corners is exactly the
geometric partial sum dictated by (3.28). -/
theorem Prop36FullData.rectangle_add_corner_eq_partialSum
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    (B : ℕ) :
    prop36RectangleSum data.coeff B +
        (∑ p ∈ prop36CornerPairs B, data.coeff p.1 p.2) =
      prop36EvenPartialSum lam B := by
  have hsubset := prop36RectanglePairs_subset_triangle B
  have hsplit :=
    Finset.sum_sdiff
      (f := fun p : ℕ × ℕ => data.coeff p.1 p.2) hsubset
  calc
    prop36RectangleSum data.coeff B +
        (∑ p ∈ prop36CornerPairs B, data.coeff p.1 p.2) =
        (∑ p ∈ prop36RectanglePairs B, data.coeff p.1 p.2) +
          ∑ p ∈ prop36TrianglePairs B \ prop36RectanglePairs B,
            data.coeff p.1 p.2 := by
      rw [prop36RectangleSum_eq_sum_pairs]
      rfl
    _ = ∑ p ∈ prop36TrianglePairs B, data.coeff p.1 p.2 := by
      rw [add_comm]
      exact hsplit
    _ = prop36TriangleAntidiagonalSum data.coeff B :=
      sum_prop36TrianglePairs_eq_antidiagonal data.coeff B
    _ = prop36EvenPartialSum lam B :=
      data.triangleAntidiagonalSum_eq_partialSum B

theorem prop36CornerPairs_card_le (B : ℕ) :
    (prop36CornerPairs B).card ≤ (2 * B) ^ 2 := by
  let box :=
    (Finset.Ico 1 (2 * B + 1)).product
      (Finset.Ico 1 (2 * B + 1))
  have hsubset : prop36CornerPairs B ⊆ box := by
    intro p hp
    have htri := (Finset.mem_sdiff.mp hp).1
    exact (Finset.mem_filter.mp htri).1
  calc
    (prop36CornerPairs B).card ≤ box.card :=
      Finset.card_le_card hsubset
    _ = (2 * B) ^ 2 := by
      simp [box, pow_two]

/-- A convenient polynomial-times-geometric envelope for both corner
tails. -/
def prop36CornerBound (C q : ℝ) (B : ℕ) : ℝ :=
  4 * C * (B : ℝ) ^ 2 * q ^ B

theorem Prop36FullData.abs_coeff_le_cornerBound
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    {B : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ prop36CornerPairs B)
    (hq0 : 0 ≤ data.constant * lam)
    (hq1 : data.constant * lam ≤ 1) :
    |data.coeff p.1 p.2| ≤
      data.constant * (data.constant * lam) ^ B := by
  obtain ⟨htri, hpnot⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hpbox, _hpsum⟩ := Finset.mem_filter.mp htri
  obtain ⟨hp₁box, hp₂box⟩ := Finset.mem_product.mp hpbox
  obtain ⟨hp₁pos, _hp₁hi⟩ := Finset.mem_Ico.mp hp₁box
  obtain ⟨hp₂pos, _hp₂hi⟩ := Finset.mem_Ico.mp hp₂box
  have hlarge : B < p.1 ∨ B < p.2 := by
    by_contra h
    push Not at h
    apply hpnot
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Ico.mpr <;> omega
  have hexp : B ≤ p.1 + p.2 - 2 := by omega
  calc
    |data.coeff p.1 p.2| ≤
        data.constant *
          (data.constant * lam) ^ (p.1 + p.2 - 2) :=
      data.coeff_bound p.1 p.2 hp₁pos hp₂pos
    _ ≤ data.constant * (data.constant * lam) ^ B := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_of_le_one hq0 hq1 hexp
      · exact data.constant_pos.le

theorem Prop36FullData.abs_cornerSum_le
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    (B : ℕ)
    (hq0 : 0 ≤ data.constant * lam)
    (hq1 : data.constant * lam ≤ 1) :
    |∑ p ∈ prop36CornerPairs B, data.coeff p.1 p.2| ≤
      prop36CornerBound data.constant
        (data.constant * lam) B := by
  have hterm :
      ∀ p ∈ prop36CornerPairs B,
        |data.coeff p.1 p.2| ≤
          data.constant * (data.constant * lam) ^ B :=
    fun p hp => data.abs_coeff_le_cornerBound hp hq0 hq1
  calc
    |∑ p ∈ prop36CornerPairs B, data.coeff p.1 p.2| ≤
        ∑ p ∈ prop36CornerPairs B, |data.coeff p.1 p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (prop36CornerPairs B).card •
          (data.constant * (data.constant * lam) ^ B) :=
      Finset.sum_le_card_nsmul _ _ _ hterm
    _ ≤ ((2 * B) ^ 2 : ℕ) •
          (data.constant * (data.constant * lam) ^ B) := by
      exact nsmul_le_nsmul_left
        (mul_nonneg data.constant_pos.le (pow_nonneg hq0 B))
        (prop36CornerPairs_card_le B)
    _ = prop36CornerBound data.constant
          (data.constant * lam) B := by
      unfold prop36CornerBound
      norm_num [nsmul_eq_mul]
      ring

theorem tendsto_prop36CornerBound
    {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (prop36CornerBound C q) atTop (𝓝 0) := by
  change Tendsto
    (fun B : ℕ => 4 * C * (B : ℝ) ^ 2 * q ^ B)
    atTop (𝓝 0)
  have ht :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 hq0 hq1
  have ht' := ht.const_mul (4 * C)
  convert ht' using 1
  · funext B
    ring
  · ring

theorem Prop36.abs_rectangle_sub_partialSum_le
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (B : ℕ) :
    |prop36RectangleSum (hP36.fullData B 2).coeff B -
        prop36EvenPartialSum lam B| ≤
      prop36CornerBound hP36.boundConstant
        (hP36.boundConstant * lam) B := by
  let data := hP36.fullData B 2
  have hq0 : 0 ≤ data.constant * lam := by
    exact mul_nonneg data.constant_pos.le hlam.le
  have hq1 : data.constant * lam ≤ 1 := by
    simpa only [data, Prop36.fullData] using hsmall.le
  have hsum := data.rectangle_add_corner_eq_partialSum B
  have hdiff :
      prop36RectangleSum data.coeff B -
          prop36EvenPartialSum lam B =
        -(∑ p ∈ prop36CornerPairs B, data.coeff p.1 p.2) := by
    linarith
  rw [show hP36.fullData B 2 = data by rfl, hdiff, abs_neg]
  simpa only [data, Prop36.fullData] using
    data.abs_cornerSum_le B hq0 hq1

/-- The square coefficient sums `𝔛_B` converge to the explicit
geometric prefactor. -/
theorem Prop36.tendsto_rectangleSum
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2) :
    Tendsto
      (fun B =>
        prop36RectangleSum (hP36.fullData B 2).coeff B)
      atTop (𝓝 (limitPrefactor lam)) := by
  let q := hP36.boundConstant * lam
  have hq0 : 0 ≤ q :=
    mul_nonneg hP36.boundConstant_pos.le hlam.le
  have hdist :
      Tendsto
        (fun B =>
          dist (prop36EvenPartialSum lam B)
            (prop36RectangleSum
              (hP36.fullData B 2).coeff B))
        atTop (𝓝 0) := by
    refine squeeze_zero'
      (Filter.Eventually.of_forall fun B => dist_nonneg)
      (Filter.Eventually.of_forall fun B =>
        show
          dist (prop36EvenPartialSum lam B)
              (prop36RectangleSum
                (hP36.fullData B 2).coeff B) ≤
            prop36CornerBound hP36.boundConstant q B
          from ?_)
      (tendsto_prop36CornerBound
        (C := hP36.boundConstant) hq0 hsmall)
    rw [Real.dist_eq, abs_sub_comm]
    simpa only [q] using
      hP36.abs_rectangle_sub_partialSum_le
        hlam hsmall B
  exact (tendsto_prop36EvenPartialSum hsub).congr_dist hdist

/-- The finite Gaussian variance is the coefficient rectangle times
the mode-dependent unscaled variance. -/
theorem Prop36.ofReal_fixedTruncationGaussianVariance_eq
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    ((fixedTruncationGaussianVariance
        hP36 hlam B modes c : ℝ≥0) : ℝ) =
      prop36RectangleSum (hP36.fullData B 2).coeff B *
        unscaledLimitVariance modes c := by
  rw [ofReal_fixedTruncationGaussianVariance,
    fixedTruncationPairVariance_eq_rectangle_mul,
    fixedModePairVariance_eq_unscaled]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- After the perturbative cutoff is removed, the canonical finite
Gaussian variances converge to `limitVar`. -/
theorem Prop36.tendsto_fixedTruncationGaussianVariance_real
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Tendsto
      (fun B =>
        ((fixedTruncationGaussianVariance
          hP36 hlam B modes c : ℝ≥0) : ℝ))
      atTop (𝓝 (limitVar lam modes c)) := by
  have ht :=
    (hP36.tendsto_rectangleSum hlam hsmall hsub).mul_const
      (unscaledLimitVariance modes c)
  rw [limitVar_eq_prefactor_mul_unscaled]
  exact ht.congr'
    (Filter.Eventually.of_forall fun B =>
      (hP36.ofReal_fixedTruncationGaussianVariance_eq
        hlam B modes c).symm)

/-- The limiting nonnegative scalar variance. -/
def limitGaussianVarianceNNReal
    (lam : ℝ) {s : ℕ} (modes : Fin s → Z4 × Z4)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    (c : Fin s → ℂ) : ℝ≥0 :=
  ⟨limitVar lam modes c, limitVar_nonneg lam modes hsub c⟩

theorem Prop36.tendsto_fixedTruncationGaussianVariance
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Tendsto
      (fun B =>
        fixedTruncationGaussianVariance hP36 hlam B modes c)
      atTop
      (𝓝 (limitGaussianVarianceNNReal lam modes hsub c)) := by
  apply NNReal.tendsto_coe.mp
  change Tendsto
    (fun B =>
      ((fixedTruncationGaussianVariance
        hP36 hlam B modes c : ℝ≥0) : ℝ))
    atTop (𝓝 (limitVar lam modes c))
  exact hP36.tendsto_fixedTruncationGaussianVariance_real
    hlam hsmall hsub modes c

/-- The characteristic functions of the canonical fixed-truncation
Gaussians converge to the characteristic function prescribed by the
explicit limiting variance. -/
theorem Prop36.tendsto_fixedGaussianCharFun_atTop
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Tendsto
      (fun B =>
        charFun
          (gaussianReal 0
            (fixedTruncationGaussianVariance
              hP36 hlam B modes c)) 1)
      atTop
      (𝓝 (Complex.exp (-((limitVar lam modes c : ℂ) / 2)))) := by
  have htR :=
    hP36.tendsto_fixedTruncationGaussianVariance_real
      hlam hsmall hsub modes c
  have htC :
      Tendsto
        (fun B =>
          (((fixedTruncationGaussianVariance
            hP36 hlam B modes c : ℝ≥0) : ℝ) : ℂ))
        atTop
        (𝓝 (limitVar lam modes c : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp htR
  have htScaled :
      Tendsto
        (fun B =>
          -((((fixedTruncationGaussianVariance
            hP36 hlam B modes c : ℝ≥0) : ℝ) : ℂ) / 2))
        atTop
        (𝓝 (-((limitVar lam modes c : ℂ) / 2))) := by
    convert htC.neg.div_const 2 using 1 <;> ring
  have htExp :=
    (Complex.continuous_exp.tendsto
      (-((limitVar lam modes c : ℂ) / 2))).comp
      htScaled
  refine htExp.congr' (Filter.Eventually.of_forall fun B => ?_)
  simp only [Function.comp_apply]
  rw [charFun_gaussianReal]
  push_cast
  congr 1
  ring

end

end Anderson4D
