import Anderson4D.PermSum.CollapseEligible
import Anderson4D.PermSum.WeightFilters

/-!
# No-collapse base case for Proposition 5.9

When (5.40) has no eligible branch, the whole tree satisfies (5.38).
Proposition 5.10 is then applied with no skipped edge.  This file records the
pointwise and sum-level bridges for that reduction, together with a dyadic
scale which always dominates a prescribed natural scale.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

/-- With no skipped indices, `NoAdjacentEqual` implies the single-scale
adjacency predicate. -/
theorem noAdjacentOutside_empty_of_noAdjacentEqual
    {α : Type*} [DecidableEq α] {m : ℕ}
    {w : Fin m → α} (hw : NoAdjacentEqual w) :
    NoAdjacentOutside (∅ : Finset (AdjacentIndex m)) w := by
  intro j _
  exact hw j.1 j.2

/-- Omitting no edges leaves the chain product unchanged. -/
@[simp] theorem heppChainWeightExcept_empty
    {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) :
    heppChainWeightExcept z ∅ w = heppChainWeight z w := by
  simp [heppChainWeightExcept, heppChainWeight]

/-- Pointwise bridge from the P-5.9 summand to P-5.10 with `O = ∅`. -/
theorem primitiveSeparatedChainWeight_le_singleScale_empty
    {t : PlaneTree} {m : ℕ}
    (z : HeppLeaf t → Fin 4 → ℤ) (w : Fin m → HeppLeaf t) :
    primitiveSeparatedChainWeight z w ≤
      singleScaleChainWeight z ∅ w := by
  by_cases hw :
      NoProperLeafBlock w ∧ NoAdjacentEqual w
  · have hout :
        NoAdjacentOutside (∅ : Finset (AdjacentIndex m)) w :=
      noAdjacentOutside_empty_of_noAdjacentEqual hw.2
    simp [primitiveSeparatedChainWeight, singleScaleChainWeight,
      hw, hout]
  · rw [primitiveSeparatedChainWeight, if_neg hw]
    exact singleScaleChainWeight_nonneg z ∅ w

/-- The pointwise base bridge summed in the exact `paperSum` normalization. -/
theorem paperSum_primitiveSeparated_le_singleScale_empty
    {t : PlaneTree} {m : ℕ}
    (mu : Multiplicities t) (z : HeppLeaf t → Fin 4 → ℤ) :
    paperSum (M := m) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) ≤
      paperSum (M := m) (leafMultiplicity mu)
        (singleScaleChainWeight z ∅) := by
  unfold paperSum wordSum
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun w _ =>
      primitiveSeparatedChainWeight_le_singleScale_empty z w
  · exact Finset.prod_nonneg fun _ _ => by positivity

/-- Every natural scale is dominated by a natural dyadic scale. -/
theorem exists_dyadicNat_ge (q : ℕ) :
    ∃ R : ℕ, IsDyadicNat R ∧ q ≤ R := by
  exact ⟨2 ^ q, ⟨q, rfl⟩, q.lt_two_pow_self.le⟩

/-- At zero skipped edges, the P-5.10 right side is independent of the
auxiliary dyadic scale `R`. -/
theorem singleScaleRHS_zero_skips
    (C0 : ℝ) (m R : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    singleScaleRHS C0 m 0 R t Nm mu compound =
      C0 ^ ((m : ℝ) / 2) *
        sqrtFactorial m *
        (∏ l ∈ simpleLeaves t compound,
          sqrtFactorial (mu.m l)) *
        (∏ l ∈ compoundLeaves t compound,
          factorialThreeQuarters (mu.m l)) *
        (∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))) *
        (∏ v ∈ nonrootBranches t,
          (parentScaleRatio Nm v) ^ 3) := by
  simp [singleScaleRHS]

/-- The zero-skipped single-scale right side is bounded by the P-5.9 right
side.  It is exactly the `W = ∅` summand, apart from the smaller
`C0^(m/2)` coefficient and the absent `D` factor. -/
theorem singleScaleRHS_zero_le_inductiveRHS
    (C0 D : ℝ) (hC0 : 1000 < C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (m R : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    singleScaleRHS C0 m 0 R t Nm mu compound ≤
      inductiveRHS C0 D m t Nm mu compound := by
  let tail : ℝ :=
    sqrtFactorial m *
      (∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l)) *
      (∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l)) *
      (∏ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ^
          ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))) *
      (∏ v ∈ nonrootBranches t,
        (parentScaleRatio Nm v) ^ 3)
  have htail : 0 ≤ tail := by
    dsimp only [tail, sqrtFactorial, factorialThreeQuarters,
      parentScaleRatio]
    positivity
  have hC0one : 1 ≤ C0 := by linarith
  have hDone : 1 ≤ D := by
    rw [hD]
    exact Real.one_le_exp (by positivity)
  have hcoef :
      C0 ^ ((m : ℝ) / 2) ≤ C0 ^ m * D ^ (BranchNodes t).card := by
    calc
      C0 ^ ((m : ℝ) / 2) ≤ C0 ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hC0one (by
          have hm : 0 ≤ (m : ℝ) := by positivity
          linarith)
      _ = C0 ^ m := Real.rpow_natCast C0 m
      _ ≤ C0 ^ m * D ^ (BranchNodes t).card := by
        exact le_mul_of_one_le_right (pow_nonneg (by linarith) m)
          (one_le_pow₀ hDone)
  have hcoefnonneg :
      0 ≤ C0 ^ m * D ^ (BranchNodes t).card := by
    positivity
  let summand : Finset (VPos t) → ℝ := fun W =>
    sqrtFactorial (m - 2 * W.card) *
      (∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l)) *
      (∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l)) *
      (∏ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ^
          ((-2 : ℤ) * ((gamma2 mu compound v : ℤ) - 1))) *
      (∏ v ∈ nonrootBranches t, (parentScaleRatio Nm v) ^ 2) *
      ∏ v ∈ (nonrootBranches t) \ W, parentScaleRatio Nm v
  have hsummand_nonneg (W : Finset (VPos t)) :
      0 ≤ summand W := by
    dsimp only [summand, sqrtFactorial, factorialThreeQuarters,
      parentScaleRatio]
    positivity
  have hsummand_empty : summand ∅ = tail := by
    dsimp only [summand, tail]
    simp only [Finset.card_empty, mul_zero, Nat.sub_zero,
      Finset.sdiff_empty]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
  have hsum :
      tail ≤
        ∑ W ∈ (nonrootBranches t).powerset, summand W := by
    rw [← hsummand_empty]
    exact Finset.single_le_sum
      (fun W _ => hsummand_nonneg W)
      (by simp)
  rw [singleScaleRHS_zero_skips]
  unfold inductiveRHS
  calc
    _ = C0 ^ ((m : ℝ) / 2) * tail := by
      dsimp only [tail]
      ring
    _ ≤
        (C0 ^ m * D ^ (BranchNodes t).card) * tail :=
      mul_le_mul_of_nonneg_right hcoef htail
    _ ≤
        (C0 ^ m * D ^ (BranchNodes t).card) *
          ∑ W ∈ (nonrootBranches t).powerset, summand W :=
      mul_le_mul_of_nonneg_left hsum hcoefnonneg
    _ = _ := rfl

/-- Complete no-eligible-branch case of Proposition 5.9, parameterized by
Proposition 5.10 with the same constant `C0`. -/
theorem noEligible_case_of_singleScale
    {C0 D : ℝ} (hsingle : SingleScaleEstimate C0)
    (hD : D = Real.exp (C0 ^ (10 : ℕ)))
    (m : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
    (mu : Multiplicities t) (compound : Finset (VPos t))
    (z : HeppLeaf t → Fin 4 → ℤ)
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hcompound : compound ⊆ Leaves t)
    (htotal : totalMultiplicity mu = m)
    (hsep : IsSeparatedEmbedding Nm z)
    (hempty : eligibleBranches Nm mu = ∅) :
    paperSum (M := m) (leafMultiplicity mu)
        (primitiveSeparatedChainWeight z) ≤
      inductiveRHS C0 D m t Nm mu compound := by
  rcases hsingle with ⟨hC0, hsingle⟩
  obtain ⟨R, hRdyadic, hR⟩ :=
    exists_dyadicNat_ge (accumulatedScale Nm mu (rootV t))
  calc
    paperSum (M := m) (leafMultiplicity mu)
          (primitiveSeparatedChainWeight z) ≤
        paperSum (M := m) (leafMultiplicity mu)
          (singleScaleChainWeight z ∅) :=
      paperSum_primitiveSeparated_le_singleScale_empty mu z
    _ ≤ singleScaleRHS C0 m 0 R t Nm mu compound :=
      hsingle m 0 R t Nm mu compound z ∅
        ht hroot hcompound htotal hsep
        (noEligible_implies_singleScale Nm mu hempty)
        hRdyadic hR (by simp)
    _ ≤ inductiveRHS C0 D m t Nm mu compound :=
      singleScaleRHS_zero_le_inductiveRHS
        C0 D hC0 hD m R t Nm mu compound

end Anderson4D
