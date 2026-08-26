import Anderson4D.Continuum.PrimitiveFinalAssembly

/-!
# Endpoint-preserving primitive lattice assembly

The endpoint values in paper (5.5) are fixed.  They must therefore remain
visible until Proposition 5.6 supplies the factor
`⟨x₀-x₁⟩⁻⁴`.  This file provides the endpoint-preserving summation layer
which is deliberately absent from `primitiveAcrossLatticeSum`.

The first theorem below closes one complete paired-incidence fibre.  Unlike
`primitive_lattice_estimate`, its denominator remains inside the genuine
tuple sum; no constancy of the incidence denominator across supports or
multiplicity profiles is assumed.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- The `(5.5)` reduction weight on its natural even tuple carrier. -/
def primitiveDirectReductionWeight
    {n : ℕ} (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) : ℝ :=
  primitiveTupleDiameterBracketSq (by omega) y *
    ∏ j : AdjacentIndex (2 * n),
      latticeEdgeWeight (y j.1) (y (adjacentSucc j))

theorem primitiveDirectReductionWeight_nonneg
    {n : ℕ} (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    0 ≤ primitiveDirectReductionWeight hn y := by
  unfold primitiveDirectReductionWeight
  exact mul_nonneg
    (primitiveTupleDiameterBracketSq_nonneg (by omega) y)
    (Finset.prod_nonneg fun j _ => latticeEdgeWeight_nonneg _ _)

/-- First and last slots of the paper's even tuple. -/
def primitiveEndpointLeft (n : ℕ) (hn : 1 ≤ n) : Fin (2 * n) :=
  ⟨0, by omega⟩

def primitiveEndpointRight (n : ℕ) (hn : 1 ≤ n) : Fin (2 * n) :=
  ⟨2 * n - 1, by omega⟩

/-- Tuples in a finite family with prescribed endpoint lattice labels. -/
def primitiveTuplesAtEndpoints
    {n : ℕ} (hn : 1 ≤ n)
    (Y : Finset (Fin (2 * n) → Z4)) (x₀ x₁ : Z4) :
    Finset (Fin (2 * n) → Z4) :=
  Y.filter fun y =>
    y (primitiveEndpointLeft n hn) = x₀ ∧
      y (primitiveEndpointRight n hn) = x₁

@[simp]
theorem mem_primitiveTuplesAtEndpoints
    {n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)} {x₀ x₁ : Z4}
    {y : Fin (2 * n) → Z4} :
    y ∈ primitiveTuplesAtEndpoints hn Y x₀ x₁ ↔
      y ∈ Y ∧ y (primitiveEndpointLeft n hn) = x₀ ∧
        y (primitiveEndpointRight n hn) = x₁ := by
  simp [primitiveTuplesAtEndpoints]

/-- The actual fixed-datum endpoint contribution after finite incidence
reindexing.  Both the primitive-pairing multiplicity and the symmetry
denominator are evaluated on each tuple. -/
def primitiveFixedDataEndpointContribution
    {n : ℕ} (M : ℕ) (hn : 1 ≤ n) (t : PlaneTree)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) : ℝ :=
  ∑ y ∈ primitiveTuplesAtEndpoints hn Y x₀ x₁,
    ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
      primitiveDirectReductionWeight hn y /
        pairedTreeSymDenom t M (2 * n) y

theorem primitiveFixedDataEndpointContribution_nonneg
    {n M : ℕ} (hn : 1 ≤ n) (t : PlaneTree)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    0 ≤ primitiveFixedDataEndpointContribution M hn t Y A x₀ x₁ := by
  unfold primitiveFixedDataEndpointContribution
  apply Finset.sum_nonneg
  intro y hy
  exact div_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (primitiveDirectReductionWeight_nonneg hn y))
    (Nat.cast_nonneg _)

@[simp]
theorem primitiveDirectReductionWeight_eq_tupleWord
    {n : ℕ} (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    primitiveDirectReductionWeight hn y =
      primitiveTupleDiameterBracketSq (by omega) y *
        supportChainWeight (tupleWord y) := by
  rfl

/-- A realized tuple with the displayed endpoints has support in the
two-anchor carrier used by Proposition 5.6. -/
theorem tupleSupport_mem_realizedSetsContainingPair
    {n M : ℕ} (hn : 1 ≤ n) {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    {y : Fin (2 * n) → Z4}
    (hy : PairedDataRealizes d y)
    {x₀ x₁ : Z4}
    (hy₀ : y (primitiveEndpointLeft n hn) = x₀)
    (hy₁ : y (primitiveEndpointRight n hn) = x₁) :
    tupleSupport y ∈
      realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁ := by
  rw [mem_realizedSetsContainingPair]
  refine
    ⟨tupleSupport_mem_realizedSets_of_pairedDataRealizes d hy, ?_, ?_⟩
  · exact mem_tupleSupport.mpr
      ⟨primitiveEndpointLeft n hn, hy₀⟩
  · exact mem_tupleSupport.mpr
      ⟨primitiveEndpointRight n hn, hy₁⟩

/-- Pointwise denominator estimate with the full realized-support
cardinality kept on the left.  The primitive-pairing cardinality may be
zero; in the nonzero case one compatible pairing supplies positivity of the
incidence denominator. -/
theorem realizedSupportCard_mul_primitiveTupleTerm_le
    {n M : ℕ} (hn : 2 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (d : PairedValidRealizationData t M (2 * n))
    (A : Finset (Fin (2 * n)))
    (y : Fin (2 * n) → Z4)
    (hyreal : PairedDataRealizes d y)
    (x₀ x₁ : Z4) :
    ((realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁).card : ℝ) *
        (((primitiveCompatibleAcrossPairings A y).card : ℝ) *
          primitiveDirectReductionWeight (by omega) y /
            pairedTreeSymDenom t M (2 * n) y) ≤
      (volumeEstimateFinalConstant ^ t.leafCount *
          branchScaleProduct (pairedMarking d) *
          latticeBracketInvFourth x₀ x₁) *
        (((primitiveCompatibleAcrossPairings A y).card : ℝ) *
          primitiveDirectReductionWeight (by omega) y) := by
  classical
  by_cases hκne :
      (primitiveCompatibleAcrossPairings A y).Nonempty
  · obtain ⟨κ, hκ⟩ := hκne
    have hκdata :=
      mem_primitiveCompatibleAcrossPairings.mp hκ
    have hratio :=
      realizedSetsPair_div_pairedDenom_le_volume
        ht d.1.1 d.2.1.1 (pairedMultiplicities d)
        y hyreal A κ hκdata.1 x₀ x₁
    have hweight :
        0 ≤ ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
          primitiveDirectReductionWeight (by omega) y :=
      mul_nonneg (Nat.cast_nonneg _)
        (primitiveDirectReductionWeight_nonneg (by omega) y)
    calc
      ((realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁).card : ℝ) *
          (((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            primitiveDirectReductionWeight (by omega) y /
              pairedTreeSymDenom t M (2 * n) y) =
        (((realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁).card : ℝ) /
            pairedTreeSymDenom t M (2 * n) y) *
          (((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            primitiveDirectReductionWeight (by omega) y) := by ring
      _ ≤
        (volumeEstimateFinalConstant ^ t.leafCount *
            branchScaleProduct (pairedMarking d) *
            latticeBracketInvFourth x₀ x₁) *
          (((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            primitiveDirectReductionWeight (by omega) y) :=
        mul_le_mul_of_nonneg_right hratio hweight
  · rw [Finset.not_nonempty_iff_eq_empty.mp hκne]
    simp

theorem primitiveCompatibleAcrossPairings_toTuple
    {m : ℕ} {Z : Finset Z4}
    (A : Finset (Fin m)) (w : SupportWord m Z) :
    primitiveCompatibleAcrossPairings A w.toTuple =
      primitiveCompatibleAcrossPairings A w := by
  ext κ
  simp only [mem_primitiveCompatibleAcrossPairings]
  rw [← supportWord_respectsWord_iff_toTuple]

/-- Every induced word in a fixed paired fibre inherits the root-cluster
diameter bound from its underlying realized tuple. -/
theorem primitive_inducedWord_diameter_le_rootScale
    {n M : ℕ} (hn : 1 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    {Z : Finset Z4} {w : SupportWord (2 * n) Z}
    (hw : w ∈ inducedWordsAtSupport Y Z) :
    primitiveTupleDiameterBracketSq (by omega) w.toTuple ≤
      (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2 := by
  obtain ⟨y, hy, hwy⟩ := Finset.mem_image.mp hw
  have hyY : y.1 ∈ Y :=
    (mem_tuplesAtSupport.mp y.2).1
  have htuple : w.toTuple = y.1 := by
    rw [← hwy, tupleWordAt_toTuple]
  rw [htuple]
  exact primitiveTupleDiameterBracketSq_le_rootScale
    ht (by omega) (hYreal y.1 hyY)

/-- Numerator of the fixed-datum endpoint contribution, before the
incidence denominator. -/
def primitiveFixedDataEndpointNumerator
    {n : ℕ} (hn : 1 ≤ n)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) : ℝ :=
  ∑ y ∈ primitiveTuplesAtEndpoints hn Y x₀ x₁,
    ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
      primitiveDirectReductionWeight hn y

theorem primitiveFixedDataEndpointNumerator_nonneg
    {n : ℕ} (hn : 1 ≤ n)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    0 ≤ primitiveFixedDataEndpointNumerator hn Y A x₀ x₁ := by
  unfold primitiveFixedDataEndpointNumerator
  apply Finset.sum_nonneg
  intro y hy
  exact mul_nonneg (Nat.cast_nonneg _)
    (primitiveDirectReductionWeight_nonneg hn y)

/-- One realized support contributes at most the root-diameter factor times
the complete Proposition 5.7 scale expression. -/
theorem sum_inducedWords_primitiveDirectReductionWeight_le
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (Z : Finset Z4) (A : Finset (Fin (2 * n)))
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y) :
    (∑ w ∈ inducedWordsAtSupport Y Z,
        ((primitiveCompatibleAcrossPairings A w.toTuple).card : ℝ) *
          primitiveDirectReductionWeight (by omega) w.toTuple) ≤
      ((1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2) *
        primitiveScaleRHS (4 * C) n t (pairedMarking d) := by
  let D₀ : ℝ :=
    (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
      (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2
  have hD₀ : 0 ≤ D₀ := by
    dsimp only [D₀]
    positivity
  calc
    (∑ w ∈ inducedWordsAtSupport Y Z,
        ((primitiveCompatibleAcrossPairings A w.toTuple).card : ℝ) *
          primitiveDirectReductionWeight (by omega) w.toTuple) =
      ∑ w ∈ inducedWordsAtSupport Y Z,
        (((primitiveCompatibleAcrossPairings A w).card : ℝ) *
          supportChainWeight w) *
            primitiveTupleDiameterBracketSq (by omega) w.toTuple := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [primitiveCompatibleAcrossPairings_toTuple]
      rw [primitiveDirectReductionWeight_eq_tupleWord]
      change _ * (_ * supportChainWeight w) = _
      ring
    _ ≤ ∑ w ∈ inducedWordsAtSupport Y Z,
        (((primitiveCompatibleAcrossPairings A w).card : ℝ) *
          supportChainWeight w) * D₀ := by
      apply Finset.sum_le_sum
      intro w hw
      apply mul_le_mul_of_nonneg_left
        (primitive_inducedWord_diameter_le_rootScale
          (by omega) ht d Y hYreal hw)
      exact mul_nonneg (Nat.cast_nonneg _)
        (supportChainWeight_nonneg w)
    _ = D₀ *
        (∑ w ∈ inducedWordsAtSupport Y Z,
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
            supportChainWeight w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = D₀ *
        (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
          ∑ w ∈ inducedWordsAtProfile Y Z p,
            ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
              supportChainWeight w) := by
      rw [← sum_inducedWords_eq_sum_profiles Y Z
        (fun w =>
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
            supportChainWeight w)]
    _ ≤ D₀ * primitiveScaleRHS (4 * C) n t (pairedMarking d) := by
      apply mul_le_mul_of_nonneg_left _ hD₀
      exact
        sum_profiles_primitivePairings_chainWeight_le_primitiveScaleRHS
          hC d Y Z A hn ht hroot hYreal

/-- Summing one fixed datum over all endpoint-valid supports costs exactly
the cardinality of the two-anchor realized-set carrier.  This is the factor
which Proposition 5.6 cancels against the incidence denominator. -/
theorem primitiveFixedDataEndpointNumerator_le
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4)
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y) :
    primitiveFixedDataEndpointNumerator (by omega) Y A x₀ x₁ ≤
      ((realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁).card : ℝ) *
        (((1 + 2 * (t.leafCount : ℝ)) ^ 2 *
            (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2) *
          primitiveScaleRHS (4 * C) n t (pairedMarking d)) := by
  let YE :=
    primitiveTuplesAtEndpoints (by omega : 1 ≤ n) Y x₀ x₁
  let S :=
    realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁
  let F : (Fin (2 * n) → Z4) → ℝ := fun y =>
    ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
      primitiveDirectReductionWeight (by omega) y
  have hYEreal : ∀ y ∈ YE, PairedDataRealizes d y := by
    intro y hy
    exact hYreal y (mem_primitiveTuplesAtEndpoints.mp hy).1
  have hsupport : ∀ y ∈ YE, tupleSupport y ∈ S := by
    intro y hy
    have hydata := mem_primitiveTuplesAtEndpoints.mp hy
    exact tupleSupport_mem_realizedSetsContainingPair
      (by omega) d (hYreal y hydata.1) hydata.2.1 hydata.2.2
  change (∑ y ∈ YE, F y) ≤ _
  calc
    (∑ y ∈ YE, F y) =
        ∑ Z ∈ S, ∑ y ∈ tuplesAtSupport YE Z, F y :=
      sum_eq_sum_tuplesAtSupport YE S hsupport F
    _ = ∑ Z ∈ S,
        ∑ w ∈ inducedWordsAtSupport YE Z, F w.toTuple := by
      apply Finset.sum_congr rfl
      intro Z hZ
      exact (sum_inducedWordsAtSupport YE Z F).symm
    _ ≤ ∑ _Z ∈ S,
        ((1 + 2 * (t.leafCount : ℝ)) ^ 2 *
            (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2) *
          primitiveScaleRHS (4 * C) n t (pairedMarking d) := by
      apply Finset.sum_le_sum
      intro Z hZ
      exact
        sum_inducedWords_primitiveDirectReductionWeight_le
          hC d YE Z A hn ht hroot hYEreal
    _ =
      ((S.card : ℕ) : ℝ) *
        (((1 + 2 * (t.leafCount : ℝ)) ^ 2 *
            (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2) *
          primitiveScaleRHS (4 * C) n t (pairedMarking d)) := by
      simp
    _ = _ := by rfl

/-- **Complete fixed-datum endpoint assembly.**

This is the denominator-correct version of the one-datum lattice estimate.
The actual tuple-dependent incidence denominator remains under the sum.  The
cardinality of the two-anchor support carrier is introduced pointwise,
cancelled by Proposition 5.6, and then cancelled again after summing the
same carrier. -/
theorem primitiveFixedDataEndpointContribution_le
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4)
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y) :
    primitiveFixedDataEndpointContribution
        M (by omega) t Y A x₀ x₁ ≤
      volumeEstimateFinalConstant ^ t.leafCount *
        (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        latticeBracketInvFourth x₀ x₁ *
          primitiveRatioRHS (4 * C) n t (pairedMarking d) := by
  classical
  let YE :=
    primitiveTuplesAtEndpoints (by omega : 1 ≤ n) Y x₀ x₁
  let S :=
    realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁
  let V : ℝ :=
    volumeEstimateFinalConstant ^ t.leafCount *
      branchScaleProduct (pairedMarking d) *
      latticeBracketInvFourth x₀ x₁
  let DQ : ℝ :=
    ((1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2) *
      primitiveScaleRHS (4 * C) n t (pairedMarking d)
  let R : ℝ :=
    volumeEstimateFinalConstant ^ t.leafCount *
      (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
      latticeBracketInvFourth x₀ x₁ *
        primitiveRatioRHS (4 * C) n t (pairedMarking d)
  have hV : 0 ≤ V := by
    dsimp only [V]
    exact mul_nonneg
      (mul_nonneg (by
        unfold volumeEstimateFinalConstant
        positivity)
        (branchScaleProduct_nonneg (pairedMarking d)))
      (latticeBracketInvFourth_nonneg x₀ x₁)
  have hDQ : 0 ≤ DQ := by
    dsimp only [DQ]
    exact mul_nonneg (by positivity)
      (primitiveScaleRHS_nonneg
        (mul_nonneg (by norm_num) hC.1.le)
        n t (pairedMarking d))
  have hnum :
      primitiveFixedDataEndpointNumerator
          (by omega) Y A x₀ x₁ ≤
        ((S.card : ℕ) : ℝ) * DQ := by
    simpa only [S, DQ] using
      primitiveFixedDataEndpointNumerator_le
        hC d Y A x₀ x₁ hn ht hroot hYreal
  have hratioIdentity :
      V * DQ = R := by
    have hcancel :=
      branchVolume_rootDiameter_mul_primitiveScaleRHS
        (4 * C) n t (pairedMarking d)
    calc
      V * DQ =
        volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁ *
            ((branchScaleProduct (pairedMarking d) *
                (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2) *
              primitiveScaleRHS (4 * C) n t (pairedMarking d)) := by
          dsimp only [V, DQ]
          ring
      _ =
        volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁ *
            primitiveRatioRHS (4 * C) n t (pairedMarking d) := by
          rw [hcancel]
      _ = R := by rfl
  by_cases hSempty : S = ∅
  · have hYEempty : YE = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      obtain ⟨y, hy⟩ := hne
      have hydata := mem_primitiveTuplesAtEndpoints.mp hy
      have hmem :
          tupleSupport y ∈ S :=
        tupleSupport_mem_realizedSetsContainingPair
          (by omega) d (hYreal y hydata.1)
          hydata.2.1 hydata.2.2
      rw [hSempty] at hmem
      simp at hmem
    change
      (∑ y ∈ YE,
        ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
          primitiveDirectReductionWeight (by omega) y /
            pairedTreeSymDenom t M (2 * n) y) ≤ R
    rw [hYEempty]
    simp only [Finset.sum_empty]
    dsimp only [R]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by
          unfold volumeEstimateFinalConstant
          positivity) (by positivity))
        (latticeBracketInvFourth_nonneg x₀ x₁))
      (primitiveRatioRHS_nonneg
        (mul_nonneg (by norm_num) hC.1.le)
        n t (pairedMarking d))
  · have hScardNat : 0 < S.card :=
      Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hSempty)
    have hScard : (0 : ℝ) < ((S.card : ℕ) : ℝ) := by
      exact_mod_cast hScardNat
    have hscaled :
        ((S.card : ℕ) : ℝ) *
            primitiveFixedDataEndpointContribution
              M (by omega) t Y A x₀ x₁ ≤
          ((S.card : ℕ) : ℝ) * R := by
      calc
        ((S.card : ℕ) : ℝ) *
            primitiveFixedDataEndpointContribution
              M (by omega) t Y A x₀ x₁ =
          ∑ y ∈ YE,
            ((S.card : ℕ) : ℝ) *
              (((primitiveCompatibleAcrossPairings A y).card : ℝ) *
                primitiveDirectReductionWeight (by omega) y /
                  pairedTreeSymDenom t M (2 * n) y) := by
            unfold primitiveFixedDataEndpointContribution
            dsimp only [YE]
            rw [Finset.mul_sum]
        _ ≤ ∑ y ∈ YE,
            V *
              (((primitiveCompatibleAcrossPairings A y).card : ℝ) *
                primitiveDirectReductionWeight (by omega) y) := by
          apply Finset.sum_le_sum
          intro y hy
          exact
            realizedSupportCard_mul_primitiveTupleTerm_le
              hn ht d A y
                (hYreal y
                  (mem_primitiveTuplesAtEndpoints.mp hy).1)
              x₀ x₁
        _ = V *
            primitiveFixedDataEndpointNumerator
              (by omega) Y A x₀ x₁ := by
          unfold primitiveFixedDataEndpointNumerator
          dsimp only [YE]
          rw [Finset.mul_sum]
        _ ≤ V * (((S.card : ℕ) : ℝ) * DQ) :=
          mul_le_mul_of_nonneg_left hnum hV
        _ = ((S.card : ℕ) : ℝ) * (V * DQ) := by ring
        _ = ((S.card : ℕ) : ℝ) * R := by rw [hratioIdentity]
    exact le_of_mul_le_mul_left hscaled hScard

/-! ## Reindexing active paired data -/

/-- Halving the positive even leaf multiplicities of paired data gives a
positive assignment of total mass `n`.  This is the exact `2^n` carrier
for the paper's choice of `(m_l)`. -/
def pairedLeafHalfAssignment
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n)) :
    PositiveAssignment (HeppLeaf t) n := by
  let f : HeppLeaf t → Fin (n + 1) := fun l =>
    ⟨(d.1.2 l).1 / 2, by
      have hle :
          (d.1.2 l).1 ≤ 2 * n :=
        LeafMultiplicityData.value_le_of_hasTotal
          d.1.2 d.2.1.2.2 l
      omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro l
    have htwo : 2 ≤ (d.1.2 l).1 := d.2.1.2.1 l
    exact Nat.div_pos (by omega) (by omega)
  · have heven :
        ∀ l : HeppLeaf t, 2 * ((d.1.2 l).1 / 2) =
          (d.1.2 l).1 := by
      intro l
      obtain ⟨k, hk⟩ := d.2.2 l
      omega
    have htotal := d.2.1.2.2
    change ∑ l : HeppLeaf t, (d.1.2 l).1 / 2 = n
    have hdouble :
        2 * (∑ l : HeppLeaf t, (d.1.2 l).1 / 2) =
          2 * n := by
      calc
        2 * (∑ l : HeppLeaf t, (d.1.2 l).1 / 2) =
            ∑ l : HeppLeaf t, 2 * ((d.1.2 l).1 / 2) := by
              rw [Finset.mul_sum]
        _ = ∑ l : HeppLeaf t, (d.1.2 l).1 := by
          apply Finset.sum_congr rfl
          intro l hl
          exact heven l
        _ = 2 * n := htotal
    omega

theorem pairedLeafHalfAssignment_injective_on_fiber
    {n M : ℕ} {t : PlaneTree}
    {d d' : PairedValidRealizationData t M (2 * n)}
    (hbranch : d.1.1 = d'.1.1)
    (hhalf :
      pairedLeafHalfAssignment d =
        pairedLeafHalfAssignment d') :
    d = d' := by
  apply Subtype.ext
  apply Prod.ext hbranch
  apply LeafMultiplicityData.ext
  intro l
  have hv :=
    congrArg
      (fun p : PositiveAssignment (HeppLeaf t) n =>
        (p.1 l).1) hhalf
  have heven := d.2.2 l
  have heven' := d'.2.2 l
  change (d.1.2 l).1 / 2 = (d'.1.2 l).1 / 2 at hv
  obtain ⟨k, hk⟩ := heven
  obtain ⟨k', hk'⟩ := heven'
  omega

/-- Paired incidence data which actually contribute to a prescribed
endpoint family.  The nonempty primitive-pairing fibre excludes all
zero-contribution denominator data before the logarithmic reindexing. -/
abbrev PrimitiveActiveEndpointData
    (t : PlaneTree) (M n : ℕ) (hn : 1 ≤ n)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :=
  {d : PairedValidRealizationData t M (2 * n) //
    ∃ y ∈ primitiveTuplesAtEndpoints hn Y x₀ x₁,
      PairedDataRealizes d y ∧
        (primitiveCompatibleAcrossPairings A y).Nonempty}

noncomputable instance instFintypePrimitiveActiveEndpointData
    (t : PlaneTree) (M n : ℕ) (hn : 1 ≤ n)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    Fintype
      (PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :=
  Fintype.ofFinite _

noncomputable def primitiveActiveEndpointWitness
    {t : PlaneTree} {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :
    Fin (2 * n) → Z4 :=
  Classical.choose d.2

theorem primitiveActiveEndpointWitness_mem
    {t : PlaneTree} {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :
    primitiveActiveEndpointWitness d ∈
      primitiveTuplesAtEndpoints hn Y x₀ x₁ :=
  (Classical.choose_spec d.2).1

theorem primitiveActiveEndpointWitness_realizes
    {t : PlaneTree} {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :
    PairedDataRealizes d.1 (primitiveActiveEndpointWitness d) :=
  (Classical.choose_spec d.2).2.1

theorem primitiveActiveEndpointWitness_pairing_nonempty
    {t : PlaneTree} {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :
    (primitiveCompatibleAcrossPairings A
      (primitiveActiveEndpointWitness d)).Nonempty :=
  (Classical.choose_spec d.2).2.2

theorem primitiveActiveEndpointScaleBound
    {t : PlaneTree} {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :
    ∀ v ∈ BranchNodes t,
      (scaleN (pairedMarking d.1) v : ℝ) ≤ 4 * (M : ℝ) := by
  obtain ⟨z, w, hadm, hw, hy⟩ :=
    primitiveActiveEndpointWitness_realizes d
  intro v hv
  exact scaleN_le_four_mul_of_isAdmissible hadm hv

/-- The active datum's marking restricted to the genuine logarithmic scale
window. -/
def primitiveActiveEndpointBranchData
    {t : PlaneTree} (ht : t.isValid = true)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :
    ValidBranchExponentData t (Nat.log 2 (4 * M)) :=
  ⟨logBranchDataOfScaleBound
      (pairedMarking d.1) (primitiveActiveEndpointScaleBound d),
    logBranchDataOfScaleBound_isValid ht
      (pairedMarking d.1) (primitiveActiveEndpointScaleBound d)⟩

/-- Active paired data inject into the product of the logarithmic marking
carrier and the positive half-multiplicity carrier. -/
def primitiveActiveEndpointCode
    {t : PlaneTree} (ht : t.isValid = true)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁) :
    ValidBranchExponentData t (Nat.log 2 (4 * M)) ×
      PositiveAssignment (HeppLeaf t) n :=
  (primitiveActiveEndpointBranchData ht d,
    pairedLeafHalfAssignment d.1)

theorem primitiveActiveEndpointCode_injective
    {t : PlaneTree} (ht : t.isValid = true)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4} :
    Function.Injective
      (primitiveActiveEndpointCode
        (M := M) (n := n) (hn := hn)
        (Y := Y) (A := A) (x₀ := x₀) (x₁ := x₁) ht) := by
  intro d d' hcode
  have hbranchLog :
      (primitiveActiveEndpointBranchData ht d).1 =
        (primitiveActiveEndpointBranchData ht d').1 :=
    congrArg (fun p => p.1.1) hcode
  have hbranch : d.1.1.1 = d'.1.1.1 := by
    apply BranchExponentData.ext
    intro v
    have hv :=
      congrArg (fun N : BranchExponentData t (Nat.log 2 (4 * M)) =>
        (N v).1) hbranchLog
    simpa [primitiveActiveEndpointBranchData,
      pairedMarking, RealizationData.toHeppMarking,
      BranchExponentData.toHeppMarking] using hv
  have hhalf :
      pairedLeafHalfAssignment d.1 =
        pairedLeafHalfAssignment d'.1 :=
    congrArg Prod.snd hcode
  apply Subtype.ext
  exact pairedLeafHalfAssignment_injective_on_fiber hbranch hhalf

theorem primitiveRatioRHS_activeBranchData
    {t : PlaneTree} (ht : t.isValid = true)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PrimitiveActiveEndpointData t M n hn Y A x₀ x₁)
    (C : ℝ) :
    primitiveRatioRHS C n t (pairedMarking d.1) =
      primitiveRatioRHS C n t
        ((primitiveActiveEndpointBranchData ht d).1.toHeppMarking
          (primitiveActiveEndpointBranchData ht d).2) := by
  unfold primitiveRatioRHS
  apply congrArg (fun s : ℝ => C ^ n * s)
  apply Finset.sum_congr rfl
  intro W hW
  apply congrArg
    (fun p : ℝ => ((n - W.card).factorial : ℝ) * p)
  apply Finset.prod_congr rfl
  intro v hv
  exact
    (parentScaleRatio_logBranchDataOfScaleBound
      ht (pairedMarking d.1)
        (primitiveActiveEndpointScaleBound d)
        ⟨v, (Finset.mem_sdiff.mp hv).1⟩).symm

/-- Summing active paired data separates into a logarithmic marking sum and
at most `2^n` positive half-multiplicity assignments. -/
theorem sum_activeEndpointData_primitiveRatioRHS_le
    {C : ℝ} (hC : 0 ≤ C)
    {t : PlaneTree} (ht : t.isValid = true)
    {M n : ℕ} {hn : 1 ≤ n}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4} :
    (∑ d : PrimitiveActiveEndpointData
        t M n hn Y A x₀ x₁,
        primitiveRatioRHS C n t (pairedMarking d.1)) ≤
      ((2 ^ n : ℕ) : ℝ) *
        primitiveMarkingRatioSum C n M t := by
  classical
  let code :
      PrimitiveActiveEndpointData t M n hn Y A x₀ x₁ →
        ValidBranchExponentData t (Nat.log 2 (4 * M)) ×
          PositiveAssignment (HeppLeaf t) n :=
    primitiveActiveEndpointCode ht
  let F :
      ValidBranchExponentData t (Nat.log 2 (4 * M)) ×
          PositiveAssignment (HeppLeaf t) n → ℝ :=
    fun p =>
      primitiveRatioRHS C n t
        (p.1.1.toHeppMarking p.1.2)
  have hcode : Function.Injective code :=
    primitiveActiveEndpointCode_injective ht
  have hF : ∀ p, 0 ≤ F p := by
    intro p
    exact primitiveRatioRHS_nonneg hC n t
      (p.1.1.toHeppMarking p.1.2)
  have hmark :
      0 ≤ primitiveMarkingRatioSum C n M t := by
    unfold primitiveMarkingRatioSum
    exact Finset.sum_nonneg fun N _ =>
      primitiveRatioRHS_nonneg hC n t
        (N.1.toHeppMarking N.2)
  calc
    (∑ d : PrimitiveActiveEndpointData
        t M n hn Y A x₀ x₁,
        primitiveRatioRHS C n t (pairedMarking d.1)) =
      ∑ d : PrimitiveActiveEndpointData
          t M n hn Y A x₀ x₁, F (code d) := by
        apply Fintype.sum_congr
        intro d
        exact primitiveRatioRHS_activeBranchData ht d C
    _ = ∑ p ∈
        (Finset.univ :
          Finset (PrimitiveActiveEndpointData
            t M n hn Y A x₀ x₁)).image code,
        F p := by
      symm
      exact Finset.sum_image hcode.injOn
    _ ≤ ∑ p :
        ValidBranchExponentData t (Nat.log 2 (4 * M)) ×
          PositiveAssignment (HeppLeaf t) n, F p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _)
      intro p hp hnot
      exact hF p
    _ =
      (Fintype.card (PositiveAssignment (HeppLeaf t) n) : ℝ) *
        primitiveMarkingRatioSum C n M t := by
      rw [Fintype.sum_prod_type]
      unfold F primitiveMarkingRatioSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      calc
        (∑ h : PositiveAssignment (HeppLeaf t) n,
            primitiveRatioRHS C n t
              ((N, h).1.1.toHeppMarking (N, h).1.2)) =
            ∑ _h : PositiveAssignment (HeppLeaf t) n,
              primitiveRatioRHS C n t
                (N.1.toHeppMarking N.2) := by
          apply Fintype.sum_congr
          intro h
          congr
        _ = (Fintype.card
              (PositiveAssignment (HeppLeaf t) n) : ℝ) *
              primitiveRatioRHS C n t
                (N.1.toHeppMarking N.2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((2 ^ n : ℕ) : ℝ) *
        primitiveMarkingRatioSum C n M t := by
      apply mul_le_mul_of_nonneg_right _ hmark
      exact_mod_cast
        PositiveAssignment.card_le_two_pow
          (ι := HeppLeaf t) n

/-! ## Summing the paired-incidence carrier -/

/-- The endpoint contribution attached to every paired realization datum.
The tuple family is restricted to the actual incidence fiber before the
fixed-datum estimate is applied. -/
def primitiveEndpointTreeIncidenceSum
    (M n : ℕ) (hn : 1 ≤ n) (t : PlaneTree)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) : ℝ :=
  ∑ d : PairedValidRealizationData t M (2 * n),
    primitiveFixedDataEndpointContribution M hn t
      (Y.filter fun y => PairedDataRealizes d y) A x₀ x₁

/-- A datum outside the active endpoint subtype contributes zero.  This is
the precise justification for discarding the enormous ambient realization
data carrier before the logarithmic marking sum. -/
theorem primitiveFixedDataEndpointContribution_eq_zero_of_inactive
    {M n : ℕ} {hn : 1 ≤ n} {t : PlaneTree}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (d : PairedValidRealizationData t M (2 * n))
    (hinactive :
      ¬∃ y ∈ primitiveTuplesAtEndpoints hn Y x₀ x₁,
        PairedDataRealizes d y ∧
          (primitiveCompatibleAcrossPairings A y).Nonempty) :
    primitiveFixedDataEndpointContribution M hn t
        (Y.filter fun y => PairedDataRealizes d y) A x₀ x₁ = 0 := by
  classical
  unfold primitiveFixedDataEndpointContribution
  apply Finset.sum_eq_zero
  intro y hy
  have hydata := mem_primitiveTuplesAtEndpoints.mp hy
  have hyfilter := Finset.mem_filter.mp hydata.1
  have hpairs :
      primitiveCompatibleAcrossPairings A y = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hpairs
    exact hinactive
      ⟨y,
        mem_primitiveTuplesAtEndpoints.mpr
          ⟨hyfilter.1, hydata.2.1, hydata.2.2⟩,
        hyfilter.2, hpairs⟩
  rw [hpairs]
  simp

/-- Exact removal of the zero paired-incidence data. -/
theorem primitiveEndpointTreeIncidenceSum_eq_active
    {M n : ℕ} {hn : 1 ≤ n} {t : PlaneTree}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4} :
    primitiveEndpointTreeIncidenceSum M n hn t Y A x₀ x₁ =
      ∑ d : PrimitiveActiveEndpointData
          t M n hn Y A x₀ x₁,
        primitiveFixedDataEndpointContribution M hn t
          (Y.filter fun y => PairedDataRealizes d.1 y)
          A x₀ x₁ := by
  classical
  let P : PairedValidRealizationData t M (2 * n) → Prop :=
    fun d =>
      ∃ y ∈ primitiveTuplesAtEndpoints hn Y x₀ x₁,
        PairedDataRealizes d y ∧
          (primitiveCompatibleAcrossPairings A y).Nonempty
  let F : PairedValidRealizationData t M (2 * n) → ℝ :=
    fun d =>
      primitiveFixedDataEndpointContribution M hn t
        (Y.filter fun y => PairedDataRealizes d y) A x₀ x₁
  calc
    primitiveEndpointTreeIncidenceSum M n hn t Y A x₀ x₁ =
        ∑ d : PairedValidRealizationData t M (2 * n), F d := by
      rfl
    _ = ∑ d ∈
        (Finset.univ :
          Finset (PairedValidRealizationData t M (2 * n))).filter P,
        F d := by
      symm
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hP : P d
      · rw [if_pos hP]
      · rw [if_neg hP]
        dsimp only [F]
        symm
        exact
          primitiveFixedDataEndpointContribution_eq_zero_of_inactive
            d (by simpa only [P] using hP)
    _ = ∑ d : {d : PairedValidRealizationData t M (2 * n) // P d},
        F d.1 := by
      apply Finset.sum_subtype
      intro d
      simp [P]
    _ = ∑ d : PrimitiveActiveEndpointData
          t M n hn Y A x₀ x₁,
        primitiveFixedDataEndpointContribution M hn t
          (Y.filter fun y => PairedDataRealizes d.1 y)
          A x₀ x₁ := by
      rfl

/-- Summation of the denominator-correct fixed-datum estimate over all
active incidence data.  This is the common branch before the extremal and
non-extremal marking arguments diverge. -/
theorem primitiveEndpointTreeIncidenceSum_le_activeRatio
    {C : ℝ} (hC : PermSumEstimate C)
    {M n : ℕ} (hn : 2 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointTreeIncidenceSum
        M n (by omega) t Y A x₀ x₁ ≤
      (volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁) *
        (((2 ^ n : ℕ) : ℝ) *
          primitiveMarkingRatioSum (4 * C) n M t) := by
  classical
  let K₀ : ℝ :=
    volumeEstimateFinalConstant ^ t.leafCount *
      (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
      latticeBracketInvFourth x₀ x₁
  have hK₀ : 0 ≤ K₀ := by
    dsimp only [K₀]
    exact mul_nonneg
      (mul_nonneg
        (by
          unfold volumeEstimateFinalConstant
          positivity)
        (by positivity))
      (latticeBracketInvFourth_nonneg x₀ x₁)
  rw [primitiveEndpointTreeIncidenceSum_eq_active]
  calc
    (∑ d : PrimitiveActiveEndpointData
        t M n (by omega) Y A x₀ x₁,
        primitiveFixedDataEndpointContribution M (by omega) t
          (Y.filter fun y => PairedDataRealizes d.1 y)
          A x₀ x₁) ≤
      ∑ d : PrimitiveActiveEndpointData
          t M n (by omega) Y A x₀ x₁,
        K₀ * primitiveRatioRHS
          (4 * C) n t (pairedMarking d.1) := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [K₀] using
        primitiveFixedDataEndpointContribution_le
          hC d.1
          (Y.filter fun y => PairedDataRealizes d.1 y)
          A x₀ x₁ hn ht hroot
          (fun y hy => (Finset.mem_filter.mp hy).2)
    _ = K₀ *
        (∑ d : PrimitiveActiveEndpointData
          t M n (by omega) Y A x₀ x₁,
          primitiveRatioRHS
            (4 * C) n t (pairedMarking d.1)) := by
      rw [Finset.mul_sum]
    _ ≤ K₀ *
        (((2 ^ n : ℕ) : ℝ) *
          primitiveMarkingRatioSum (4 * C) n M t) := by
      apply mul_le_mul_of_nonneg_left _ hK₀
      exact
        sum_activeEndpointData_primitiveRatioRHS_le
          (mul_nonneg (by norm_num) hC.1.le) ht
    _ = _ := by rfl

/-- Non-extremal branch of the paper's `(5.16)--(5.17)` summation.  The
strict branch-cardinality inequality leaves enough room for the unrestricted
logarithmic marking carrier. -/
theorem primitiveEndpointTreeIncidenceSum_le_of_card_lt_aux
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (htotal : totalMultiplicity mu = 2 * n)
    (hcard : (nonrootBranches t).card < n - 2)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointTreeIncidenceSum
        M n (by omega) t Y A x₀ x₁ ≤
      (volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁) *
        (((2 ^ n : ℕ) : ℝ) *
          ((32 * (4 * C) * (K + 1)) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2)))) := by
  calc
    primitiveEndpointTreeIncidenceSum
        M n (by omega) t Y A x₀ x₁ ≤
      (volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁) *
        (((2 ^ n : ℕ) : ℝ) *
          primitiveMarkingRatioSum (4 * C) n M t) :=
      primitiveEndpointTreeIncidenceSum_le_activeRatio
        hC hn ht hroot Y A x₀ x₁
    _ ≤
      (volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁) *
        (((2 ^ n : ℕ) : ℝ) *
          ((32 * (4 * C) * (K + 1)) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2)))) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
        · exact
            primitiveMarkingRatioSum_le_final_of_card_lt
              (mul_nonneg (by norm_num) hC.1.le)
              ht hroot mu hn htotal hcard hnL
        · positivity
      · exact mul_nonneg
          (mul_nonneg
            (by
              unfold volumeEstimateFinalConstant
              positivity)
            (by positivity))
          (latticeBracketInvFourth_nonneg x₀ x₁)

/-! ## Endpoint-preserving tree cover of the lattice sum -/

/-- The primitive `(5.5)` statistic after summing all compatible primitive
across pairings, while retaining the two fixed endpoint labels. -/
def primitiveEndpointLatticeStatistic
    {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4)
    (y : Fin (2 * n) → Z4) : ℝ :=
  if y (primitiveEndpointLeft n hn) = x₀ ∧
      y (primitiveEndpointRight n hn) = x₁ then
    ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
      primitiveDirectReductionWeight hn y
  else 0

theorem primitiveEndpointLatticeStatistic_nonneg
    {n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4)
    (y : Fin (2 * n) → Z4) :
    0 ≤ primitiveEndpointLatticeStatistic hn A x₀ x₁ y := by
  unfold primitiveEndpointLatticeStatistic
  split
  · exact mul_nonneg (Nat.cast_nonneg _)
      (primitiveDirectReductionWeight_nonneg hn y)
  · exact le_rfl

/-- The finite endpoint-preserving version of the lattice sum `(5.5)`. -/
def primitiveEndpointLatticeSum
    (M n : ℕ) (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) : ℝ :=
  latticeChainSum M (2 * n)
    (primitiveEndpointLatticeStatistic hn A x₀ x₁)

private theorem endpoint_two_le_valueFiber_of_respectsAcross
    {m : ℕ} (A : Finset (Fin m)) (y : Fin m → Z4)
    (κ : AcrossPairing A) (hκ : RespectsWord A y κ)
    (j : Fin m) :
    2 ≤ (Finset.univ.filter fun k => y k = y j).card := by
  classical
  by_cases hj : j ∈ A
  · let jA : ↥A := ⟨j, hj⟩
    let k : Fin m := (κ jA).1
    have hkAc : k ∈ Aᶜ := (κ jA).2
    have hk : k ∉ A := Finset.mem_compl.mp hkAc
    have hjk : j ≠ k := fun h => hk (h ▸ hj)
    have hyk : y k = y j := (hκ jA).symm
    apply Finset.one_lt_card.mpr
    exact ⟨j, by simp, k, by simp [hyk], hjk⟩
  · have hjAc : j ∈ Aᶜ := Finset.mem_compl.mpr hj
    let jAc : ↥(Aᶜ) := ⟨j, hjAc⟩
    let kA : ↥A := κ.symm jAc
    let k : Fin m := kA.1
    have hk : k ∈ A := kA.2
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    have hyk : y k = y j := by
      simpa [k, kA, jAc] using hκ kA
    apply Finset.one_lt_card.mpr
    exact ⟨j, by simp, k, by simp [hyk], hjk⟩

/-- A nonzero primitive endpoint statistic lies in the repeated-value locus
required by the weak Hepp-tree cover. -/
theorem primitiveEndpointLatticeStatistic_eq_zero_of_not_repeated
    {M n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4)
    (y : Fin (2 * n) → Z4)
    (hybox : y ∈ rdec_boundedTuples M (2 * n))
    (hynot : y ∉ rdec_repeatedTuples M (2 * n)) :
    primitiveEndpointLatticeStatistic hn A x₀ x₁ y = 0 := by
  classical
  unfold primitiveEndpointLatticeStatistic
  split_ifs with hendpoints
  · by_cases hpairs :
      (primitiveCompatibleAcrossPairings A y).Nonempty
    · obtain ⟨κ, hκ⟩ := hpairs
      obtain ⟨hrespect, _hprimitive⟩ :=
        mem_primitiveCompatibleAcrossPairings.mp hκ
      exact False.elim
        (hynot (rdec_mem_repeatedTuples.mpr
          ⟨hybox,
            endpoint_two_le_valueFiber_of_respectsAcross
              A y κ hrespect⟩))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hpairs]
      simp
  · rfl

/-- If a valid tree realizes a word carrying an across pairing, its
restricted realization data can be promoted to the even paired carrier.
This is the arithmetic-carrier version of the fixed-slice construction in
`PrimitiveAssembly`. -/
theorem exists_pairedData_realizes_of_treeRealized_of_respectsAcross
    {t : PlaneTree} (ht : t.isValid = true)
    {M m : ℕ} {A : Finset (Fin m)}
    {κ : AcrossPairing A} {y : Fin m → Z4}
    (hytree : y ∈ rdec_treeRealized t M m)
    (hκ : RespectsWord A y κ) :
    ∃ d : PairedValidRealizationData t M m,
      PairedDataRealizes d y := by
  obtain ⟨_hybounded, Nm, mu, hreal⟩ :=
    rdec_mem_treeRealized.mp hytree
  obtain ⟨z, w, hadm, hw, hyz⟩ := hreal
  have hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ) :=
    fun _v hv => scaleN_le_four_mul_of_isAdmissible hadm hv
  have htotal :
      ∑ l : HeppLeaf t, mu.m l.1 = m :=
    multiplicities_total_of_realizesTuple
      ⟨z, w, hadm, hw, hyz⟩
  have hwκ : RespectsWord A w κ := by
    intro j
    apply hadm.inj
    rw [← hyz j.1, ← hyz (κ j).1]
    exact hκ j
  have heven :
      ∀ l : HeppLeaf t, Even (mu.m l.1) :=
    even_mult_of_compatibleAcrossPairing
      A (fun l : HeppLeaf t => mu.m l.1) hw κ hwκ
  let d₀ : RealizationData t M m :=
    realizationDataOfBundles Nm mu hscale htotal
  have hd₀ : d₀.IsPairedValid :=
    realizationDataOfBundles_isPairedValid_of_treeValid
      ht Nm mu hscale htotal heven
  let d : PairedValidRealizationData t M m := ⟨d₀, hd₀⟩
  refine ⟨d, ?_⟩
  have hNm :
      HeppMarking.EqOnBranch
        (d₀.toHeppMarking hd₀.1) Nm := by
    intro v hv
    change (branchDataOfScaleBound Nm hscale).raw v = Nm.Nexp v
    rw [BranchExponentData.raw_apply_of_mem _ hv]
    exact branchDataOfScaleBound_apply Nm hscale ⟨v, hv⟩
  have hmu :
      Multiplicities.EqOnLeaves
        (d₀.toMultiplicities hd₀.1) mu := by
    intro v hv
    change (leafDataOfTotal mu htotal).raw v = mu.m v
    rw [LeafMultiplicityData.raw_apply_of_mem _ hv]
    exact LeafMultiplicityData.ofMultiplicities_apply mu _ ⟨v, hv⟩
  exact (realizesTuple_congr_restricted hNm hmu).mpr
    ⟨z, w, hadm, hw, hyz⟩

/-- The genuinely contributing endpoint tuples in one valid-tree slice. -/
def primitiveEndpointTreeTupleFamily
    (M n : ℕ) (hn : 1 ≤ n) (t : PlaneTree)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    Finset (Fin (2 * n) → Z4) :=
  (rdec_treeRealized t M (2 * n)).filter fun y =>
    y (primitiveEndpointLeft n hn) = x₀ ∧
      y (primitiveEndpointRight n hn) = x₁ ∧
        (primitiveCompatibleAcrossPairings A y).Nonempty

@[simp]
theorem mem_primitiveEndpointTreeTupleFamily
    {M n : ℕ} {hn : 1 ≤ n} {t : PlaneTree}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    {y : Fin (2 * n) → Z4} :
    y ∈ primitiveEndpointTreeTupleFamily M n hn t A x₀ x₁ ↔
      y ∈ rdec_treeRealized t M (2 * n) ∧
        y (primitiveEndpointLeft n hn) = x₀ ∧
        y (primitiveEndpointRight n hn) = x₁ ∧
          (primitiveCompatibleAcrossPairings A y).Nonempty := by
  simp [primitiveEndpointTreeTupleFamily]

/-- On a valid tree, the endpoint statistic is exactly the
denominator-correct paired-incidence sum over the active tuple family. -/
theorem sum_treeRealized_primitiveEndpointLatticeStatistic_eq_incidence
    {M n : ℕ} (hn : 1 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    (∑ y ∈ rdec_treeRealized t M (2 * n),
        primitiveEndpointLatticeStatistic hn A x₀ x₁ y) =
      primitiveEndpointTreeIncidenceSum M n hn t
        (primitiveEndpointTreeTupleFamily
          M n hn t A x₀ x₁)
        A x₀ x₁ := by
  classical
  let Y :=
    primitiveEndpointTreeTupleFamily M n hn t A x₀ x₁
  let F : (Fin (2 * n) → Z4) → ℝ := fun y =>
    ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
      primitiveDirectReductionWeight hn y
  have hleft :
      (∑ y ∈ rdec_treeRealized t M (2 * n),
          primitiveEndpointLatticeStatistic hn A x₀ x₁ y) =
        ∑ y ∈ Y, F y := by
    unfold primitiveEndpointLatticeStatistic
    simp only [Y, primitiveEndpointTreeTupleFamily]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hend :
        y (primitiveEndpointLeft n hn) = x₀ ∧
          y (primitiveEndpointRight n hn) = x₁
    · rw [if_pos hend]
      by_cases hpairs :
          (primitiveCompatibleAcrossPairings A y).Nonempty
      · rw [if_pos ⟨hend.1, hend.2, hpairs⟩]
      · have hempty :=
          Finset.not_nonempty_iff_eq_empty.mp hpairs
        rw [if_neg (fun h => hpairs h.2.2)]
        rw [hempty]
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    · rw [if_neg hend]
      rw [if_neg (fun h => hend ⟨h.1, h.2.1⟩)]
  have hcover :
      ∀ y ∈ Y,
        ∃ d : PairedValidRealizationData t M (2 * n),
          PairedDataRealizes d y := by
    intro y hy
    have hydata :=
      mem_primitiveEndpointTreeTupleFamily.mp hy
    obtain ⟨κ, hκ⟩ := hydata.2.2.2
    exact
      exists_pairedData_realizes_of_treeRealized_of_respectsAcross
        ht hydata.1
          (mem_primitiveCompatibleAcrossPairings.mp hκ).1
  have hincidence :=
    sum_eq_sum_paired_tree_incidence_div
      t M (2 * n) Y F hcover
  rw [hleft, hincidence]
  unfold primitiveEndpointTreeIncidenceSum
    primitiveFixedDataEndpointContribution
    pairedValidRealizationDataFinset
  apply Fintype.sum_congr
  intro d
  have hfilter :
      primitiveTuplesAtEndpoints hn
          (Y.filter fun y => PairedDataRealizes d y) x₀ x₁ =
        Y.filter fun y => PairedDataRealizes d y := by
    ext y
    simp only [mem_primitiveTuplesAtEndpoints,
      Finset.mem_filter]
    constructor
    · intro hy
      exact hy.1
    · intro hy
      have hyY :=
        mem_primitiveEndpointTreeTupleFamily.mp hy.1
      exact ⟨hy, hyY.2.1, hyY.2.2.1⟩
  rw [hfilter]

/-- Endpoint-preserving master bridge from the finite lattice sum to valid
trees and their exact even-multiplicity incidence denominators. -/
theorem primitiveEndpointLatticeSum_le_treeIncidence
    (M n : ℕ) (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointLatticeSum M n hn A x₀ x₁ ≤
      ∑ t ∈ rdec_treeEnum (2 * n),
        primitiveEndpointTreeIncidenceSum M n hn t
          (primitiveEndpointTreeTupleFamily
            M n hn t A x₀ x₁)
          A x₀ x₁ := by
  unfold primitiveEndpointLatticeSum
  calc
    latticeChainSum M (2 * n)
        (primitiveEndpointLatticeStatistic hn A x₀ x₁) ≤
      ∑ t ∈ rdec_treeEnum (2 * n),
        ∑ y ∈ rdec_treeRealized t M (2 * n),
          primitiveEndpointLatticeStatistic hn A x₀ x₁ y := by
      apply latticeChainSum_le_treeSum M (2 * n) (by omega)
      · exact
          primitiveEndpointLatticeStatistic_nonneg hn A x₀ x₁
      · exact
          primitiveEndpointLatticeStatistic_eq_zero_of_not_repeated
            hn A x₀ x₁
    _ = ∑ t ∈ rdec_treeEnum (2 * n),
        primitiveEndpointTreeIncidenceSum M n hn t
          (primitiveEndpointTreeTupleFamily
            M n hn t A x₀ x₁)
          A x₀ x₁ := by
      apply Finset.sum_congr rfl
      intro t ht
      exact
        sum_treeRealized_primitiveEndpointLatticeStatistic_eq_incidence
          hn (rdec_mem_treeEnum.mp ht).1 A x₀ x₁

/-! ## The bare-leaf slice -/

theorem realizesTuple_leaf_apply_eq
    {M m : ℕ} {Nm : HeppMarking leaf}
    {mu : Multiplicities leaf} {y : Fin m → Z4}
    (hy : RealizesTuple leaf Nm mu M y)
    (i j : Fin m) :
    y i = y j := by
  obtain ⟨z, w, hadm, hw, hyz⟩ := hy
  rw [hyz i, hyz j]
  congr 1
  apply Subtype.ext
  exact
    (vpos_leaf_eq (w i).1).trans
      (vpos_leaf_eq (w j).1).symm

theorem primitiveDirectReductionWeight_eq_one_of_constant
    {n : ℕ} (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) (x : Z4)
    (hy : ∀ i, y i = x) :
    primitiveDirectReductionWeight hn y = 1 := by
  have hfun : y = fun _ => x := by
    funext i
    exact hy i
  subst y
  unfold primitiveDirectReductionWeight
    primitiveTupleDiameterBracketSq
  simp [latticeBracketSq, znorm]

theorem primitiveCompatibleAcrossPairings_card_le_factorial
    {n : ℕ} (A : Finset (Fin (2 * n)))
    (y : Fin (2 * n) → Z4) :
    (primitiveCompatibleAcrossPairings A y).card ≤ n.factorial := by
  classical
  by_cases hpairs :
      (primitiveCompatibleAcrossPairings A y).Nonempty
  · obtain ⟨κ, hκ⟩ := hpairs
    have hAcard :
        A.card = n := by
      have heq :
          Fintype.card ↥A =
            Fintype.card ↥(Aᶜ : Finset (Fin (2 * n))) :=
        Fintype.card_congr κ
      simp only [Fintype.card_coe] at heq
      rw [Finset.card_compl] at heq
      simp only [Fintype.card_fin] at heq
      omega
    calc
      (primitiveCompatibleAcrossPairings A y).card ≤
          Fintype.card (AcrossPairing A) :=
        Finset.card_le_univ _
      _ = A.card.factorial :=
        by
          simpa only [Fintype.card_coe] using
            Fintype.card_equiv κ
      _ = n.factorial := by rw [hAcard]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hpairs]
    simp

/-- The bare leaf contributes at most one constant endpoint tuple, and its
primitive across-pairing multiplicity is at most `n!`. -/
theorem primitiveEndpointTreeIncidenceSum_leaf_le_factorial
    {M n : ℕ} (hn : 1 ≤ n)
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointTreeIncidenceSum M n hn leaf
        (primitiveEndpointTreeTupleFamily
          M n hn leaf A x₀ x₁)
        A x₀ x₁ ≤
      (n.factorial : ℝ) := by
  classical
  let Y :=
    primitiveEndpointTreeTupleFamily M n hn leaf A x₀ x₁
  have hYcard : Y.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy y' hy'
    have hydata :=
      mem_primitiveEndpointTreeTupleFamily.mp hy
    have hydata' :=
      mem_primitiveEndpointTreeTupleFamily.mp hy'
    obtain ⟨_hybox, Nm, mu, hyreal⟩ :=
      rdec_mem_treeRealized.mp hydata.1
    obtain ⟨_hybox', Nm', mu', hyreal'⟩ :=
      rdec_mem_treeRealized.mp hydata'.1
    funext i
    calc
      y i = y (primitiveEndpointLeft n hn) :=
        realizesTuple_leaf_apply_eq hyreal _ _
      _ = x₀ := hydata.2.1
      _ = y' (primitiveEndpointLeft n hn) :=
        hydata'.2.1.symm
      _ = y' i :=
        realizesTuple_leaf_apply_eq hyreal' _ _
  have hterm :
      ∀ y ∈ Y,
        ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            primitiveDirectReductionWeight hn y ≤
          (n.factorial : ℝ) := by
    intro y hy
    have hydata :=
      mem_primitiveEndpointTreeTupleFamily.mp hy
    obtain ⟨_hybox, Nm, mu, hyreal⟩ :=
      rdec_mem_treeRealized.mp hydata.1
    have hweight :
        primitiveDirectReductionWeight hn y = 1 := by
      apply primitiveDirectReductionWeight_eq_one_of_constant
        hn y (y (primitiveEndpointLeft n hn))
      intro i
      exact realizesTuple_leaf_apply_eq hyreal _ _
    rw [hweight, mul_one]
    exact_mod_cast
      primitiveCompatibleAcrossPairings_card_le_factorial A y
  have hsum :
      (∑ y ∈ Y,
          ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            primitiveDirectReductionWeight hn y) ≤
        (n.factorial : ℝ) := by
    calc
      (∑ y ∈ Y,
          ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            primitiveDirectReductionWeight hn y) ≤
          ∑ _y ∈ Y, (n.factorial : ℝ) :=
        Finset.sum_le_sum hterm
      _ = (Y.card : ℝ) * (n.factorial : ℝ) := by simp
      _ ≤ 1 * (n.factorial : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hYcard
        · positivity
      _ = (n.factorial : ℝ) := one_mul _
  rw [←
    sum_treeRealized_primitiveEndpointLatticeStatistic_eq_incidence
      hn (show leaf.isValid = true by rfl) A x₀ x₁]
  have hleft :
      (∑ y ∈ rdec_treeRealized leaf M (2 * n),
          primitiveEndpointLatticeStatistic hn A x₀ x₁ y) =
        ∑ y ∈ Y,
          ((primitiveCompatibleAcrossPairings A y).card : ℝ) *
            primitiveDirectReductionWeight hn y := by
    unfold primitiveEndpointLatticeStatistic
    simp only [Y, primitiveEndpointTreeTupleFamily]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hend :
        y (primitiveEndpointLeft n hn) = x₀ ∧
          y (primitiveEndpointRight n hn) = x₁
    · rw [if_pos hend]
      by_cases hpairs :
          (primitiveCompatibleAcrossPairings A y).Nonempty
      · rw [if_pos ⟨hend.1, hend.2, hpairs⟩]
      · have hempty :=
          Finset.not_nonempty_iff_eq_empty.mp hpairs
        rw [if_neg (fun h => hpairs h.2.2), hempty]
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    · rw [if_neg hend]
      rw [if_neg (fun h => hend ⟨h.1, h.2.1⟩)]
  rw [hleft]
  exact hsum

theorem primitiveEndpointTreeIncidenceSum_leaf_le_factorialLog
    {M n K : ℕ} (hn : 2 ≤ n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointTreeIncidenceSum M n (by omega) leaf
        (primitiveEndpointTreeTupleFamily
          M n (by omega) leaf A x₀ x₁)
        A x₀ x₁ ≤
      (8 * (K + 1) : ℝ) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) *
          latticeBracketInvFourth x₀ x₁ := by
  by_cases hend : x₀ = x₁
  · subst x₁
    rw [latticeBracketInvFourth_self, mul_one]
    have hfac :=
      factorial_log_balance n 0
        (Nat.log 2 (4 * M) + 1) K hn (by omega) hnL
    have hL :
        (1 : ℝ) ≤
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            min (0 + 1) (n - 2)) := by
      apply one_le_pow₀
      exact_mod_cast
        Nat.one_le_iff_ne_zero.mpr (by omega)
    exact
      (primitiveEndpointTreeIncidenceSum_leaf_le_factorial
        (by omega) A x₀ x₀).trans
        ((calc
          (n.factorial : ℝ) =
              (n.factorial : ℝ) * 1 := by ring
          _ ≤ (n.factorial : ℝ) *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                min (0 + 1) (n - 2)) :=
            mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
          _ ≤ (8 * (K + 1) : ℝ) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (n - 2)) := by
            simpa only [Nat.sub_zero] using hfac))
  · have hzero :
        primitiveEndpointTreeIncidenceSum M n (by omega) leaf
            (primitiveEndpointTreeTupleFamily
              M n (by omega) leaf A x₀ x₁)
            A x₀ x₁ = 0 := by
      rw [←
        sum_treeRealized_primitiveEndpointLatticeStatistic_eq_incidence
          (by omega) (show leaf.isValid = true by rfl) A x₀ x₁]
      apply Finset.sum_eq_zero
      intro y hy
      unfold primitiveEndpointLatticeStatistic
      rw [if_neg]
      intro hyend
      obtain ⟨_hybox, Nm, mu, hyreal⟩ :=
        rdec_mem_treeRealized.mp hy
      apply hend
      calc
        x₀ = y (primitiveEndpointLeft n (by omega)) :=
          hyend.1.symm
        _ = y (primitiveEndpointRight n (by omega)) :=
          realizesTuple_leaf_apply_eq hyreal _ _
        _ = x₁ := hyend.2
    rw [hzero]
    exact mul_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (latticeBracketInvFourth_nonneg x₀ x₁)

theorem validTree_root_branch_or_eq_leaf
    {t : PlaneTree} (ht : t.isValid = true) :
    rootV t ∈ BranchNodes t ∨ t = leaf := by
  obtain ⟨cs⟩ := t
  by_cases hbranch : 2 ≤ cs.length
  · left
    rw [mem_BranchNodes_iff]
    exact hbranch
  · right
    have hvalid :
        (cs.length != 1) = true := by
      have ht' :
          (cs.length != 1) = true ∧
            isValidList cs = true := by
        simpa only [isValid, Bool.and_eq_true] using ht
      exact ht'.1
    have hne : cs.length ≠ 1 := by
      simpa only [bne_iff_ne] using hvalid
    have hzero : cs.length = 0 := by omega
    have hnil : cs = [] := List.eq_nil_of_length_eq_zero hzero
    subst cs
    rfl

/-- Non-extremal bound without requiring a multiplicity witness from the
caller.  If the active carrier is nonempty, any one active datum supplies
the total-multiplicity witness; otherwise the incidence sum is exactly
zero. -/
theorem primitiveEndpointTreeIncidenceSum_le_of_card_lt
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hcard : (nonrootBranches t).card < n - 2)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointTreeIncidenceSum
        M n (by omega) t Y A x₀ x₁ ≤
      (volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁) *
        (((2 ^ n : ℕ) : ℝ) *
          ((32 * (4 * C) * (K + 1)) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2)))) := by
  classical
  let Active :=
    PrimitiveActiveEndpointData
      t M n (by omega : 1 ≤ n) Y A x₀ x₁
  by_cases hactive : Nonempty Active
  · let d : Active := Classical.choice hactive
    exact
      primitiveEndpointTreeIncidenceSum_le_of_card_lt_aux
        hC hn ht hroot (pairedMultiplicities d.1)
        (RealizationData.toMultiplicities_total
          d.1.1 d.1.2.1)
        hcard hnL Y A x₀ x₁
  · rw [primitiveEndpointTreeIncidenceSum_eq_active]
    have hsumzero :
        (∑ d : PrimitiveActiveEndpointData
            t M n (by omega) Y A x₀ x₁,
          primitiveFixedDataEndpointContribution M (by omega) t
            (Y.filter fun y => PairedDataRealizes d.1 y)
            A x₀ x₁) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact False.elim (hactive ⟨d⟩)
    rw [hsumzero]
    have hvol : 0 ≤ volumeEstimateFinalConstant := by
      unfold volumeEstimateFinalConstant
      positivity
    have hbase :
        0 ≤ (32 * (4 * C) * (K + 1) : ℝ) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg (by norm_num) hC.1.le))
        (add_nonneg (Nat.cast_nonneg K) zero_le_one)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hvol t.leafCount) (sq_nonneg _))
        (latticeBracketInvFourth_nonneg x₀ x₁))
      (mul_nonneg (by positivity)
        (mul_nonneg (pow_nonneg hbase n) (by positivity)))

end

end Anderson4D
