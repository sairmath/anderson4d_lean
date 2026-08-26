import Anderson4D.Continuum.PrimitiveFiberReindex
import Anderson4D.Continuum.PrimitiveMarkingReindex

/-!
# Final primitive-pairing ledger

This file contains the last algebraic and finite-sum steps in paper
(5.5)--(5.17).  In particular, the primitive pairing is kept *inside* the
word sum until the `(m_l / 2)! / m_l!` gain from (5.10) has been used.
Summing a fixed-pairing estimate here would lose precisely the factorial
gain which makes the argument close.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## The leaf-factorial cancellation after (5.15) -/

private theorem factorial_sq_le_factorial_two_mul (k : ℕ) :
    k.factorial ^ 2 ≤ (2 * k).factorial := by
  have hdvd :
      k.factorial * k.factorial ∣ (k + k).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add k k
  have hpos : 0 < (k + k).factorial := Nat.factorial_pos _
  have hle : k.factorial * k.factorial ≤ (k + k).factorial :=
    Nat.le_of_dvd hpos hdvd
  simpa [pow_two, two_mul] using hle

/-- For an even multiplicity, the half-factorial supplied by the pairing
count cancels the square-root factorial in Proposition 5.7. -/
theorem halfFactorial_div_factorial_mul_sqrtFactorial_le_one
    (m : ℕ) (hm : Even m) :
    (((m / 2).factorial : ℝ) / (m.factorial : ℝ)) *
        sqrtFactorial m ≤ 1 := by
  obtain ⟨k, rfl⟩ := hm
  have hfac :
      (((k.factorial : ℕ) : ℝ) ^ 2) ≤
        (((2 * k).factorial : ℕ) : ℝ) := by
    exact_mod_cast factorial_sq_le_factorial_two_mul k
  have hsqrt :
      (k.factorial : ℝ) ≤
        Real.sqrt (((2 * k).factorial : ℕ) : ℝ) := by
    exact Real.le_sqrt_of_sq_le hfac
  unfold sqrtFactorial
  have hden : (0 : ℝ) < ((2 * k).factorial : ℕ) := by positivity
  have hhalf : (k + k) / 2 = k := by omega
  have hdouble : k + k = 2 * k := by omega
  rw [hhalf, hdouble]
  calc
    ((k.factorial : ℝ) / (((2 * k).factorial : ℕ) : ℝ)) *
          Real.sqrt (((2 * k).factorial : ℕ) : ℝ) =
        (k.factorial : ℝ) /
          Real.sqrt (((2 * k).factorial : ℕ) : ℝ) := by
      have hsqrtpos :
          0 < Real.sqrt (((2 * k).factorial : ℕ) : ℝ) :=
        Real.sqrt_pos.2 hden
      field_simp [hden.ne', hsqrtpos.ne',
        Real.sq_sqrt hden.le]
      exact Real.sq_sqrt hden.le
    _ ≤ 1 := (div_le_one
      (Real.sqrt_pos.2 hden)).2 hsqrt

/-- Product form of the preceding cancellation, exactly the leaf ledger
remaining after multiplying (5.10) and (5.15). -/
theorem pairedFactorialLedger_le_one
    {t : PlaneTree} (mu : Multiplicities t)
    (heven : ∀ l : HeppLeaf t, Even (leafMultiplicity mu l)) :
    (∏ l : HeppLeaf t,
        (((leafMultiplicity mu l / 2).factorial : ℝ) /
          ((leafMultiplicity mu l).factorial : ℝ))) *
      (∏ l : HeppLeaf t,
        sqrtFactorial (leafMultiplicity mu l)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_one
  · intro l hl
    exact mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (by unfold sqrtFactorial; positivity)
  · intro l hl
    exact
      halfFactorial_div_factorial_mul_sqrtFactorial_le_one
        (leafMultiplicity mu l) (heven l)

/-! ## Primitive pairings survive the support/leaf reindexing -/

theorem primitiveCompatibleAcrossPairings_reindexSupportWord
    {t : PlaneTree} {m : ℕ} {Z : Finset Z4}
    (e : HeppLeaf t ≃ {x // x ∈ Z})
    (A : Finset (Fin m)) (w : SupportWord m Z) :
    primitiveCompatibleAcrossPairings A (reindexSupportWord e w) =
      primitiveCompatibleAcrossPairings A w := by
  ext κ
  simp only [mem_primitiveCompatibleAcrossPairings]
  constructor
  · rintro ⟨hrespects, hprimitive⟩
    refine ⟨?_, hprimitive⟩
    intro j
    apply e.symm.injective
    exact hrespects j
  · rintro ⟨hrespects, hprimitive⟩
    exact ⟨reindexSupportWord_respectsWord e A κ w hrespects,
      hprimitive⟩

/-- Fixed-profile form of (5.8)--(5.10), with *all* primitive pairings
summed before Proposition 5.7 is applied.  This is the pairing-preserving
counterpart of the fixed-`κ` fiber theorem. -/
theorem sum_profile_primitivePairings_chainWeight_le
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m)
    (Y : Finset (Fin m → Z4))
    {Z : Finset Z4}
    (p : PositiveAssignment {x // x ∈ Z} m)
    (A : Finset (Fin m))
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (hne : (inducedWordsAtProfile Y Z p).Nonempty) :
    ∃ z : HeppLeaf t → Z4,
      IsAdmissible (pairedMarking d) M z ∧
      leafEmbeddingImage z = Z ∧
      (∑ w ∈ inducedWordsAtProfile Y Z p,
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
            supportChainWeight w) ≤
        primitivePairedWordSum
          (leafMultiplicity (pairedMultiplicities d)) A
          (heppChainWeight z) := by
  classical
  obtain ⟨w₀, hw₀⟩ := hne
  have hw₀support :
      w₀ ∈ inducedWordsAtSupport Y Z :=
    (Finset.mem_filter.mp hw₀).1
  have hw₀profile : w₀.HasProfile p :=
    (Finset.mem_filter.mp hw₀).2
  obtain ⟨z, u₀, hadm, hu₀, himage, hw₀u⟩ :=
    SupportWord.isInducedBy_of_mem_inducedWordsAtSupport
      d Y hYreal hw₀support
  let e : HeppLeaf t ≃ {x // x ∈ Z} :=
    leafEquivSupport z hadm.inj himage
  have hsubset :
      (inducedWordsAtProfile Y Z p).image
          (reindexSupportWord e) ⊆
        validWords
          (leafMultiplicity (pairedMultiplicities d)) := by
    intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    exact reindexSupportWord_mem_validWords_of_sameProfile
      d p w₀ w hw₀profile (Finset.mem_filter.mp hw).2
      hadm hu₀ himage hw₀u
  refine ⟨z, hadm, himage, ?_⟩
  calc
    (∑ w ∈ inducedWordsAtProfile Y Z p,
        ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
          supportChainWeight w) =
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          ((primitiveCompatibleAcrossPairings A
            (reindexSupportWord e w)).card : ℝ) *
            heppChainWeight z (reindexSupportWord e w) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [primitiveCompatibleAcrossPairings_reindexSupportWord]
      congr 1
      exact supportChainWeight_eq_heppChainWeight_reindex
        e w z (fun l =>
          leafEquivSupport_apply_val z hadm.inj himage l)
    _ = ∑ u ∈
          (inducedWordsAtProfile Y Z p).image
            (reindexSupportWord e),
          ((primitiveCompatibleAcrossPairings A u).card : ℝ) *
            heppChainWeight z u := by
      rw [Finset.sum_image
        (reindexSupportWord_injective e).injOn]
    _ ≤ ∑ u ∈
          validWords
            (leafMultiplicity (pairedMultiplicities d)),
          ((primitiveCompatibleAcrossPairings A u).card : ℝ) *
            heppChainWeight z u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro u hu hnot
      exact mul_nonneg (Nat.cast_nonneg _)
        (heppChainWeight_nonneg z u)
    _ = primitivePairedWordSum
          (leafMultiplicity (pairedMultiplicities d)) A
          (heppChainWeight z) := rfl

/-! ## Applying Proposition 5.7 without losing (5.10) -/

/-- The exact half-factorial quotient supplied by the primitive pairing
count for the multiplicities carried by `d`. -/
def pairedFactorialQuotient
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) : ℝ :=
  ∏ l : HeppLeaf t,
    (((leafMultiplicity (pairedMultiplicities d) l / 2).factorial : ℝ) /
      ((leafMultiplicity (pairedMultiplicities d) l).factorial : ℝ))

theorem pairedFactorialQuotient_nonneg
    {t : PlaneTree} {M m : ℕ}
    (d : PairedValidRealizationData t M m) :
    0 ≤ pairedFactorialQuotient d := by
  unfold pairedFactorialQuotient
  positivity

/-- One fixed multiplicity profile, including all compatible primitive
pairings, is bounded by Proposition 5.7 with the exact (5.10) quotient. -/
theorem sum_profile_primitivePairings_chainWeight_le_permSumRHS
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    {Z : Finset Z4}
    (p : PositiveAssignment {x // x ∈ Z} (2 * n))
    (A : Finset (Fin (2 * n)))
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y) :
    (∑ w ∈ inducedWordsAtProfile Y Z p,
        ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
          supportChainWeight w) ≤
      pairedFactorialQuotient d *
        permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) := by
  classical
  by_cases hne : (inducedWordsAtProfile Y Z p).Nonempty
  · obtain ⟨z, hadm, himage, hprofile⟩ :=
      sum_profile_primitivePairings_chainWeight_le
        d Y p A hYreal hne
    exact hprofile.trans
      (primitivePairedChainSum_le_permSumRHS
        hC n M t (pairedMarking d) (pairedMultiplicities d)
        z A hn ht hroot
        (RealizationData.toMultiplicities_total d.1 d.2.1)
        (fun l => RealizationData.toMultiplicities_even
          d.1 d.2.1 d.2.2 l)
        hadm)
  · have hempty :
        inducedWordsAtProfile Y Z p = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    exact mul_nonneg (pairedFactorialQuotient_nonneg d)
      (permSumRHS_nonneg hC.1.le n t
        (pairedMarking d) (pairedMultiplicities d))

/-- Summing the genuine profile carrier costs at most `2^(2n)`, while the
primitive-pairing factorial quotient remains intact. -/
theorem sum_profiles_primitivePairings_chainWeight_le
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (Z : Finset Z4) (A : Finset (Fin (2 * n)))
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y) :
    (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
            supportChainWeight w) ≤
      ((2 ^ (2 * n) : ℕ) : ℝ) *
        (pairedFactorialQuotient d *
          permSumRHS C n t (pairedMarking d)
            (pairedMultiplicities d)) := by
  have htarget :
      0 ≤ pairedFactorialQuotient d *
        permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) :=
    mul_nonneg (pairedFactorialQuotient_nonneg d)
      (permSumRHS_nonneg hC.1.le n t
        (pairedMarking d) (pairedMultiplicities d))
  have hcard :
      ((Fintype.card
        (PositiveAssignment {x // x ∈ Z} (2 * n)) : ℕ) : ℝ) ≤
        ((2 ^ (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast
      card_positiveAssignments_support_le_two_pow (2 * n) Z
  calc
    (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
            supportChainWeight w) ≤
        ∑ _p : PositiveAssignment {x // x ∈ Z} (2 * n),
          pairedFactorialQuotient d *
            permSumRHS C n t (pairedMarking d)
              (pairedMultiplicities d) := by
      apply Finset.sum_le_sum
      intro p hp
      exact
        sum_profile_primitivePairings_chainWeight_le_permSumRHS
          hC d Y p A hn ht hroot hYreal
    _ = ((Fintype.card
          (PositiveAssignment {x // x ∈ Z} (2 * n)) : ℕ) : ℝ) *
          (pairedFactorialQuotient d *
            permSumRHS C n t (pairedMarking d)
              (pairedMultiplicities d)) := by simp
    _ ≤ ((2 ^ (2 * n) : ℕ) : ℝ) *
          (pairedFactorialQuotient d *
            permSumRHS C n t (pairedMarking d)
              (pairedMultiplicities d)) :=
      mul_le_mul_of_nonneg_right hcard htarget

/-! ## Removing the remaining leaf factorials -/

/-- The scale tail which remains from (5.15) after the leaf factorials,
the volume monomial, and the root-diameter factor have been cancelled. -/
def primitiveScaleRHS
    (C : ℝ) (n : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) : ℝ :=
  C ^ n *
    ∑ W ∈ (nonrootBranches t).powerset,
      ((n - W.card).factorial : ℝ) *
        permSumScaleTail Nm W

theorem primitive_permSumScaleTail_nonneg
    {t : PlaneTree} (Nm : HeppMarking t)
    (W : Finset (VPos t)) :
    0 ≤ permSumScaleTail Nm W := by
  unfold permSumScaleTail
  have hbranch :
      0 ≤ ∏ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ^
          ((-4 : ℤ) *
            (((childrenOf v).card : ℤ) - 1)) := by
    exact Finset.prod_nonneg fun v _ =>
      zpow_nonneg (Nat.cast_nonneg _) _
  have hroot :
      0 ≤ (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ) :=
    zpow_nonneg (Nat.cast_nonneg _) _
  have hratio :
      0 ≤ ∏ v ∈ nonrootBranches t \ W,
        parentScaleRatio Nm v := by
    exact Finset.prod_nonneg fun v _ => by
      unfold parentScaleRatio
      positivity
  positivity

theorem primitiveScaleRHS_nonneg
    {C : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (t : PlaneTree) (Nm : HeppMarking t) :
    0 ≤ primitiveScaleRHS C n t Nm := by
  unfold primitiveScaleRHS
  apply mul_nonneg (pow_nonneg hC n)
  apply Finset.sum_nonneg
  intro W hW
  exact mul_nonneg (Nat.cast_nonneg _)
    (primitive_permSumScaleTail_nonneg Nm W)

/-- The pairing quotient cancels every square-root leaf factorial in
Proposition 5.7. -/
theorem pairedFactorialQuotient_mul_permSumRHS_le_primitiveScaleRHS
    {C : ℝ} (hC : 0 ≤ C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n)) :
    pairedFactorialQuotient d *
        permSumRHS C n t (pairedMarking d)
          (pairedMultiplicities d) ≤
      primitiveScaleRHS C n t (pairedMarking d) := by
  have hledger :
      pairedFactorialQuotient d *
        (∏ l : HeppLeaf t,
          sqrtFactorial
            (leafMultiplicity (pairedMultiplicities d) l)) ≤ 1 := by
    exact pairedFactorialLedger_le_one
      (pairedMultiplicities d)
      (fun l => RealizationData.toMultiplicities_even
        d.1 d.2.1 d.2.2 l)
  rw [permSumRHS_eq_factored]
  unfold primitiveScaleRHS
  calc
    pairedFactorialQuotient d *
        (C ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n (pairedMarking d)
              (pairedMultiplicities d) W) =
      C ^ n *
        (pairedFactorialQuotient d *
          ∑ W ∈ (nonrootBranches t).powerset,
            permSumSummand n (pairedMarking d)
              (pairedMultiplicities d) W) := by ring
    _ ≤ C ^ n *
        (∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            permSumScaleTail (pairedMarking d) W) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC n)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro W hW
      unfold permSumSummand
      have htail :
          0 ≤ ((n - W.card).factorial : ℝ) *
            permSumScaleTail (pairedMarking d) W :=
        mul_nonneg (Nat.cast_nonneg _)
          (primitive_permSumScaleTail_nonneg
            (pairedMarking d) W)
      calc
        pairedFactorialQuotient d *
            (((n - W.card).factorial : ℝ) *
              (∏ l : HeppLeaf t,
                sqrtFactorial
                  (leafMultiplicity (pairedMultiplicities d) l)) *
              permSumScaleTail (pairedMarking d) W) =
          (pairedFactorialQuotient d *
            (∏ l : HeppLeaf t,
              sqrtFactorial
                (leafMultiplicity (pairedMultiplicities d) l))) *
            (((n - W.card).factorial : ℝ) *
              permSumScaleTail (pairedMarking d) W) := by ring
        _ ≤ 1 *
            (((n - W.card).factorial : ℝ) *
              permSumScaleTail (pairedMarking d) W) :=
          mul_le_mul_of_nonneg_right hledger htail
        _ = ((n - W.card).factorial : ℝ) *
              permSumScaleTail (pairedMarking d) W := one_mul _

/-- The two profile-count powers from (5.8)--(5.9) are absorbed into
`C ↦ 4C`, after which no leaf-factorial term remains. -/
theorem sum_profiles_primitivePairings_chainWeight_le_primitiveScaleRHS
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (Z : Finset Z4) (A : Finset (Fin (2 * n)))
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y) :
    (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
            supportChainWeight w) ≤
      primitiveScaleRHS (4 * C) n t (pairedMarking d) := by
  calc
    (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
        ∑ w ∈ inducedWordsAtProfile Y Z p,
          ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
            supportChainWeight w) ≤
      ((2 ^ (2 * n) : ℕ) : ℝ) *
        (pairedFactorialQuotient d *
          permSumRHS C n t (pairedMarking d)
            (pairedMultiplicities d)) :=
      sum_profiles_primitivePairings_chainWeight_le
        hC d Y Z A hn ht hroot hYreal
    _ = pairedFactorialQuotient d *
          permSumRHS (4 * C) n t (pairedMarking d)
            (pairedMultiplicities d) := by
      calc
        ((2 ^ (2 * n) : ℕ) : ℝ) *
            (pairedFactorialQuotient d *
              permSumRHS C n t (pairedMarking d)
                (pairedMultiplicities d)) =
          pairedFactorialQuotient d *
            (((2 ^ (2 * n) : ℕ) : ℝ) *
              permSumRHS C n t (pairedMarking d)
                (pairedMultiplicities d)) := by ring
        _ = pairedFactorialQuotient d *
            permSumRHS (4 * C) n t (pairedMarking d)
              (pairedMultiplicities d) := by
          rw [two_pow_two_mul_permSumRHS]
    _ ≤ primitiveScaleRHS (4 * C) n t (pairedMarking d) :=
      pairedFactorialQuotient_mul_permSumRHS_le_primitiveScaleRHS
        (mul_nonneg (by norm_num) hC.1.le) d

/-! ## Exact volume/diameter scale cancellation in (5.16) -/

/-- The right side of (5.16), before the summation over increasing
markings. -/
def primitiveRatioRHS
    (C : ℝ) (n : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) : ℝ :=
  C ^ n *
    ∑ W ∈ (nonrootBranches t).powerset,
      ((n - W.card).factorial : ℝ) *
        ∏ v ∈ nonrootBranches t \ W,
          parentScaleRatio Nm v

theorem primitiveRatioRHS_nonneg
    {C : ℝ} (hC : 0 ≤ C)
    (n : ℕ) (t : PlaneTree) (Nm : HeppMarking t) :
    0 ≤ primitiveRatioRHS C n t Nm := by
  unfold primitiveRatioRHS
  apply mul_nonneg (pow_nonneg hC n)
  apply Finset.sum_nonneg
  intro W hW
  apply mul_nonneg (Nat.cast_nonneg _)
  exact Finset.prod_nonneg fun v _ => by
    unfold parentScaleRatio
    positivity

private theorem branchScaleProduct_mul_inverse_eq_one
    {t : PlaneTree} (Nm : HeppMarking t) :
    branchScaleProduct Nm *
        (∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-4 : ℤ) *
              (((childrenOf v).card : ℤ) - 1))) = 1 := by
  unfold branchScaleProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro v hv
  have hscale : (scaleN Nm v : ℝ) ≠ 0 := by
    exact_mod_cast (scaleN_pos Nm v).ne'
  rw [← zpow_natCast, ← zpow_add₀ hscale]
  convert zpow_zero (scaleN Nm v : ℝ) using 2
  rw [card_childrenOf]
  have hchild : 1 ≤ childCount t v.1 := by
    have : 2 ≤ childCount t v.1 := by
      simpa [BranchNodes] using hv
    omega
  push_cast [Nat.cast_sub hchild]
  ring

private theorem rootScale_sq_mul_inverse_eq_one
    {t : PlaneTree} (Nm : HeppMarking t) :
    (scaleN Nm (rootV t) : ℝ) ^ 2 *
        (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ) = 1 := by
  have hscale : (scaleN Nm (rootV t) : ℝ) ≠ 0 := by
    exact_mod_cast (scaleN_pos Nm (rootV t)).ne'
  rw [← zpow_natCast, ← zpow_add₀ hscale]
  convert zpow_zero (scaleN Nm (rootV t) : ℝ) using 2
  norm_num

/-- The P-5.6 volume monomial cancels the inverse branch monomial in
P-5.7, while the root-scale square paying for the diameter cancels
`N_r⁻²`.  Only the parent ratios indexed by `B \\ (W ∪ {r})` remain. -/
theorem branchVolume_rootDiameter_mul_primitiveScaleRHS
    (C : ℝ) (n : ℕ) (t : PlaneTree)
    (Nm : HeppMarking t) :
    (branchScaleProduct Nm *
        (scaleN Nm (rootV t) : ℝ) ^ 2) *
        primitiveScaleRHS C n t Nm =
      primitiveRatioRHS C n t Nm := by
  unfold primitiveScaleRHS primitiveRatioRHS
  calc
    (branchScaleProduct Nm *
        (scaleN Nm (rootV t) : ℝ) ^ 2) *
        (C ^ n *
          ∑ W ∈ (nonrootBranches t).powerset,
            ((n - W.card).factorial : ℝ) *
              permSumScaleTail Nm W) =
      C ^ n *
        ((branchScaleProduct Nm *
          (scaleN Nm (rootV t) : ℝ) ^ 2) *
          ∑ W ∈ (nonrootBranches t).powerset,
            ((n - W.card).factorial : ℝ) *
              permSumScaleTail Nm W) := by ring
    _ = C ^ n *
        (∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            ∏ v ∈ nonrootBranches t \ W,
              parentScaleRatio Nm v) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W hW
      unfold permSumScaleTail
      have hbranch :=
        branchScaleProduct_mul_inverse_eq_one Nm
      have hroot :=
        rootScale_sq_mul_inverse_eq_one Nm
      let Binv : ℝ :=
        ∏ v ∈ BranchNodes t,
          (scaleN Nm v : ℝ) ^
            ((-4 : ℤ) *
              (((childrenOf v).card : ℤ) - 1))
      let Rinv : ℝ :=
        (scaleN Nm (rootV t) : ℝ) ^ (-2 : ℤ)
      let ratios : ℝ :=
        ∏ v ∈ nonrootBranches t \ W,
          parentScaleRatio Nm v
      change
        (branchScaleProduct Nm *
            (scaleN Nm (rootV t) : ℝ) ^ 2) *
          (((n - W.card).factorial : ℝ) *
            (Binv * Rinv * ratios)) =
        ((n - W.card).factorial : ℝ) * ratios
      calc
        (branchScaleProduct Nm *
              (scaleN Nm (rootV t) : ℝ) ^ 2) *
            (((n - W.card).factorial : ℝ) *
              (Binv * Rinv * ratios)) =
          ((n - W.card).factorial : ℝ) *
            ((branchScaleProduct Nm *
              Binv) *
              ((scaleN Nm (rootV t) : ℝ) ^ 2 *
                Rinv) *
              ratios) := by ring
        _ = ((n - W.card).factorial : ℝ) *
              ratios := by
          dsimp only [Binv, Rinv]
          rw [hbranch, hroot]
          ring

/-! ## Summing the genuine increasing markings -/

/-- The actual finite marking sum remaining after (5.16), on the sharp
logarithmic exponent carrier. -/
def primitiveMarkingRatioSum
    (C : ℝ) (n M : ℕ) (t : PlaneTree) : ℝ :=
  ∑ N :
      ValidBranchExponentData t (Nat.log 2 (4 * M)),
    primitiveRatioRHS C n t
      (N.1.toHeppMarking N.2)

/-- The exact independent-gap majorant obtained from the injective marking
code.  No endpoint refinement has yet been used in this expression. -/
def primitiveGenericDyadicRHS
    (C : ℝ) (n M : ℕ) (t : PlaneTree) : ℝ :=
  C ^ n *
    ∑ W ∈ (nonrootBranches t).powerset,
      ((n - W.card).factorial : ℝ) *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (W.card + 1) *
          2 ^ ((nonrootBranches t).card - W.card))

/-- Genuine valid markings inject into the independent root/free/gap
coordinates.  This is the complete non-endpoint part of (5.17). -/
theorem primitiveMarkingRatioSum_le_genericDyadic
    {C : ℝ} (hC : 0 ≤ C)
    {n M : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t) :
    primitiveMarkingRatioSum C n M t ≤
      primitiveGenericDyadicRHS C n M t := by
  unfold primitiveMarkingRatioSum primitiveRatioRHS
    primitiveGenericDyadicRHS
  calc
    (∑ N :
        ValidBranchExponentData t (Nat.log 2 (4 * M)),
      C ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            ∏ v ∈ nonrootBranches t \ W,
              parentScaleRatio
                (N.1.toHeppMarking N.2) v) =
      C ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            (∑ N :
              ValidBranchExponentData t
                (Nat.log 2 (4 * M)),
              ∏ v ∈ nonrootBranches t \ W,
                parentScaleRatio
                  (N.1.toHeppMarking N.2) v) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro W hW
      rw [Finset.mul_sum]
    _ ≤ C ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (W.card + 1) *
              2 ^ ((nonrootBranches t).card - W.card)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC n)
      apply Finset.sum_le_sum
      intro W hW
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact
        sum_logBranchExponentData_parentScaleRatio_le
          ht hroot M W (Finset.mem_powerset.mp hW)

/-- Away from the unique extremal case
`|B \\ {r}| = n-2`, the generic marking code already gives the refined
exponent `min(|W|+1,n-2)` used after (5.17). -/
theorem primitiveGenericDyadicRHS_le_factorialLog_of_card_lt
    {C : ℝ} (hC : 0 ≤ C)
    {n M K : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (hn : 2 ≤ n)
    (htotal : totalMultiplicity mu = 2 * n)
    (hcard : (nonrootBranches t).card < n - 2)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1)) :
    primitiveGenericDyadicRHS C n M t ≤
      C ^ n *
        2 ^ (nonrootBranches t).card *
        ((16 * (K + 1) : ℝ) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (n - 2))) := by
  let L : ℕ := Nat.log 2 (4 * M) + 1
  have hbalance :
      (∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            (L : ℝ) ^ min (W.card + 1) (n - 2)) ≤
        (16 * (K + 1) : ℝ) ^ n *
          (L : ℝ) ^ (n - 2) :=
    tree_sum_factorial_log_balance
      ht hroot mu n L K hn htotal hnL
  unfold primitiveGenericDyadicRHS
  change
    C ^ n *
      (∑ W ∈ (nonrootBranches t).powerset,
        ((n - W.card).factorial : ℝ) *
          ((L : ℝ) ^ (W.card + 1) *
            2 ^ ((nonrootBranches t).card - W.card))) ≤ _
  calc
    C ^ n *
        (∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            ((L : ℝ) ^ (W.card + 1) *
              2 ^ ((nonrootBranches t).card - W.card))) ≤
      C ^ n *
        (2 ^ (nonrootBranches t).card *
          ∑ W ∈ (nonrootBranches t).powerset,
            ((n - W.card).factorial : ℝ) *
              (L : ℝ) ^ min (W.card + 1) (n - 2)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC n)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro W hW
      have hWcard :
          W.card ≤ (nonrootBranches t).card :=
        Finset.card_le_card (Finset.mem_powerset.mp hW)
      have hmin :
          min (W.card + 1) (n - 2) = W.card + 1 := by
        apply min_eq_left
        omega
      rw [hmin]
      have hpow :
          (2 : ℝ) ^
              ((nonrootBranches t).card - W.card) ≤
            2 ^ (nonrootBranches t).card := by
        exact pow_le_pow_right₀ (by norm_num)
          (Nat.sub_le _ _)
      have hbase :
          0 ≤ ((n - W.card).factorial : ℝ) *
            (L : ℝ) ^ (W.card + 1) := by positivity
      calc
        ((n - W.card).factorial : ℝ) *
            ((L : ℝ) ^ (W.card + 1) *
              2 ^ ((nonrootBranches t).card - W.card)) =
          (((n - W.card).factorial : ℝ) *
            (L : ℝ) ^ (W.card + 1)) *
              2 ^ ((nonrootBranches t).card - W.card) := by ring
        _ ≤ (((n - W.card).factorial : ℝ) *
              (L : ℝ) ^ (W.card + 1)) *
                2 ^ (nonrootBranches t).card :=
          mul_le_mul_of_nonneg_left hpow hbase
        _ = 2 ^ (nonrootBranches t).card *
              (((n - W.card).factorial : ℝ) *
                (L : ℝ) ^ (W.card + 1)) := by ring
    _ ≤ C ^ n *
        2 ^ (nonrootBranches t).card *
        ((16 * (K + 1) : ℝ) ^ n *
          (L : ℝ) ^ (n - 2)) := by
      calc
        C ^ n *
            (2 ^ (nonrootBranches t).card *
              ∑ W ∈ (nonrootBranches t).powerset,
                ((n - W.card).factorial : ℝ) *
                  (L : ℝ) ^
                    min (W.card + 1) (n - 2)) ≤
          C ^ n *
            (2 ^ (nonrootBranches t).card *
              ((16 * (K + 1) : ℝ) ^ n *
                (L : ℝ) ^ (n - 2))) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC n)
          exact mul_le_mul_of_nonneg_left hbalance (by positivity)
        _ = _ := by ring

/-! ## The one constrained coordinate in the endpoint refinement -/

/-- Valid branch data whose exponent at `anchor` lies in a prescribed
finite set.  The endpoint geometry will supply a set of cardinality
`O(log n)` (and hence `O(C^n)`) in the unique extremal case of (5.17). -/
abbrev ConstrainedValidBranchExponentData
    (t : PlaneTree) (bound : ℕ)
    (anchor : {v // v ∈ BranchNodes t})
    (allowed : Finset (Fin (bound + 1))) :=
  {N : ValidBranchExponentData t bound //
    N.1 anchor ∈ allowed}

/-- Delete the anchored branch coordinate. -/
abbrev BranchAwayFrom
    (t : PlaneTree) (anchor : {v // v ∈ BranchNodes t}) :=
  {v : {v // v ∈ BranchNodes t} // v ≠ anchor}

/-- An anchored marking is encoded by its allowed anchor exponent and all
remaining branch exponents. -/
def constrainedBranchExponentCode
    {t : PlaneTree} {bound : ℕ}
    {anchor : {v // v ∈ BranchNodes t}}
    {allowed : Finset (Fin (bound + 1))}
    (N : ConstrainedValidBranchExponentData
      t bound anchor allowed) :
    {e // e ∈ allowed} ×
      (BranchAwayFrom t anchor → Fin (bound + 1)) :=
  (⟨N.1.1 anchor, N.2⟩,
    fun v => N.1.1 v.1)

theorem constrainedBranchExponentCode_injective
    {t : PlaneTree} {bound : ℕ}
    {anchor : {v // v ∈ BranchNodes t}}
    {allowed : Finset (Fin (bound + 1))} :
    Function.Injective
      (@constrainedBranchExponentCode
        t bound anchor allowed) := by
  intro N N' hcode
  apply Subtype.ext
  apply Subtype.ext
  apply BranchExponentData.ext
  intro v
  by_cases hv : v = anchor
  · subst v
    change (N.1.1 anchor).1 = (N'.1.1 anchor).1
    have hfirst := congrArg Prod.fst hcode
    exact congrArg
      (fun e : {e // e ∈ allowed} => e.1.1) hfirst
  · have htail :=
      congrArg
        (fun c :
          {e // e ∈ allowed} ×
            (BranchAwayFrom t anchor → Fin (bound + 1)) =>
          c.2 ⟨v, hv⟩)
        hcode
    change (N.1.1 v).1 = (N'.1.1 v).1
    simpa [constrainedBranchExponentCode] using
      congrArg Fin.val htail

/-- Fixing one branch exponent removes one full logarithmic coordinate.
This is the finite counting lemma needed in the top `W = B \\ {r}` case. -/
theorem card_constrainedValidBranchExponentData_le
    {t : PlaneTree} (bound : ℕ)
    (anchor : {v // v ∈ BranchNodes t})
    (allowed : Finset (Fin (bound + 1))) :
    Fintype.card
        (ConstrainedValidBranchExponentData
          t bound anchor allowed) ≤
      allowed.card *
        (bound + 1) ^ ((BranchNodes t).card - 1) := by
  calc
    Fintype.card
        (ConstrainedValidBranchExponentData
          t bound anchor allowed) ≤
      Fintype.card
        ({e // e ∈ allowed} ×
          (BranchAwayFrom t anchor → Fin (bound + 1))) :=
      Fintype.card_le_of_injective
        constrainedBranchExponentCode
        constrainedBranchExponentCode_injective
    _ = allowed.card *
        (bound + 1) ^ ((BranchNodes t).card - 1) := by
      have haway :
          Fintype.card (BranchAwayFrom t anchor) =
            (BranchNodes t).card - 1 := by
        unfold BranchAwayFrom
        calc
          Fintype.card {v : {v // v ∈ BranchNodes t} //
              v ≠ anchor} =
              Fintype.card {v // v ∈ BranchNodes t} - 1 :=
            Set.card_ne_eq anchor
          _ = (BranchNodes t).card - 1 := by
            rw [Fintype.card_coe]
      simp [haway]

/-! ## Geometry of the fixed endpoint coordinate -/

/-- Exponents compatible with the two-sided admissibility comparison for a
fixed pair of endpoint values. -/
def endpointExponentFinset
    {t : PlaneTree} (bound : ℕ)
    (x₀ x₁ : Z4) : Finset (Fin (bound + 1)) :=
  Finset.univ.filter fun e =>
    ((2 ^ e.1 : ℕ) : ℝ) / 2 ≤ znorm (x₀ - x₁) ∧
      znorm (x₀ - x₁) ≤
        2 * (t.leafCount : ℝ) * ((2 ^ e.1 : ℕ) : ℝ)

private theorem card_finset_fin_le_of_pairwise_sub_le
    {B D : ℕ} (s : Finset (Fin B))
    (hdiam :
      ∀ a ∈ s, ∀ b ∈ s, a.1 ≤ b.1 →
        b.1 - a.1 ≤ D) :
    s.card ≤ D + 1 := by
  by_cases hs : s.Nonempty
  · obtain ⟨a₀, ha₀, hmin⟩ :=
      Finset.exists_min_image s (fun e : Fin B => e.1) hs
    have hmaps :
        Set.MapsTo (fun e : Fin B => e.1) (s : Set (Fin B))
          (Finset.Ico a₀.1 (a₀.1 + (D + 1)) : Set ℕ) := by
      intro a ha
      rw [Finset.coe_Ico]
      have hlow : a₀.1 ≤ a.1 := hmin a ha
      have hgap : a.1 - a₀.1 ≤ D :=
        hdiam a₀ ha₀ a ha hlow
      have hrecover :
          a.1 - a₀.1 + a₀.1 = a.1 :=
        Nat.sub_add_cancel hlow
      refine ⟨hlow, ?_⟩
      calc
        a.1 = (a.1 - a₀.1) + a₀.1 := hrecover.symm
        _ < (D + 1) + a₀.1 :=
          Nat.add_lt_add_right (Nat.lt_succ_of_le hgap) _
        _ = a₀.1 + (D + 1) := Nat.add_comm _ _
    calc
      s.card ≤
          (Finset.Ico a₀.1 (a₀.1 + (D + 1))).card :=
        Finset.card_le_card_of_injOn
          (fun e : Fin B => e.1) hmaps Fin.val_injective.injOn
      _ = D + 1 := by simp
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    simp [hs]

/-- The endpoint window contains at most linearly many dyadic exponents.
The paper only needs an exponential-in-`leafCount` bound; this elementary
linear estimate is deliberately stronger and avoids any analytic logarithm
comparison. -/
theorem card_endpointExponentFinset_le
    {t : PlaneTree} (bound : ℕ) (x₀ x₁ : Z4) :
    (endpointExponentFinset (t := t) bound x₀ x₁).card ≤
      4 * t.leafCount + 1 := by
  apply card_finset_fin_le_of_pairwise_sub_le
  intro a ha b hb hab
  rw [endpointExponentFinset, Finset.mem_filter] at ha hb
  have hpowReal :
      (((2 ^ b.1 : ℕ) : ℝ)) ≤
        4 * (t.leafCount : ℝ) *
          (((2 ^ a.1 : ℕ) : ℝ)) := by
    calc
      (((2 ^ b.1 : ℕ) : ℝ)) ≤
          2 * znorm (x₀ - x₁) := by
        linarith [hb.2.1]
      _ ≤ 2 *
          (2 * (t.leafCount : ℝ) *
            (((2 ^ a.1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left ha.2.2 (by norm_num)
      _ = 4 * (t.leafCount : ℝ) *
          (((2 ^ a.1 : ℕ) : ℝ)) := by ring
  have hpowNat :
      2 ^ b.1 ≤
        (4 * t.leafCount) * 2 ^ a.1 := by
    exact_mod_cast hpowReal
  have hfactor :
      2 ^ (b.1 - a.1) * 2 ^ a.1 ≤
        (4 * t.leafCount) * 2 ^ a.1 := by
    rw [← pow_add, Nat.sub_add_cancel hab]
    exact hpowNat
  have hpowGap :
      2 ^ (b.1 - a.1) ≤ 4 * t.leafCount :=
    Nat.le_of_mul_le_mul_right hfactor (by positivity)
  exact Nat.lt_two_pow_self.le.trans hpowGap

/-- A genuine admissible embedding with fixed distinct endpoint leaves
forces the LCA exponent into `endpointExponentFinset`.  The lower inequality
is Definition 5.4(a); the upper one is the cluster-diameter bound used in
the proof of Proposition 5.6. -/
theorem branchExponent_mem_endpointExponentFinset
    {t : PlaneTree} (ht : t.isValid = true)
    {bound M : ℕ}
    (N : ValidBranchExponentData t bound)
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (z : HeppLeaf t → Z4)
    (hadm : IsAdmissible
      (N.1.toHeppMarking N.2) M z) :
    N.1 anchor ∈
      endpointExponentFinset (t := t) bound (z f₀) (z f₁) := by
  rw [endpointExponentFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · have hsep := hadm.sep f₀ f₁ hf
    rw [← hanchor] at hsep
    simpa [scaleN, BranchExponentData.toHeppMarking,
      BranchExponentData.raw_apply_of_mem N.1 anchor.2] using hsep
  · have hf₀ :
        f₀ ∈ leavesUnder anchor.1 := by
      rw [mem_leavesUnder, hanchor]
      exact lcaPath_prefix_left f₀.1.1 f₁.1.1
    have hf₁ :
        f₁ ∈ leavesUnder anchor.1 := by
      rw [mem_leavesUnder, hanchor]
      exact lcaPath_prefix_right f₀.1.1 f₁.1.1
    have hdiam :
        znorm (z f₀ - z f₁) ≤
          tildeScale (N.1.toHeppMarking N.2) anchor.1 :=
      clusterDiameter_le_tildeScale hadm anchor.1 hf₀ hf₁
    have htilde :
        tildeScale (N.1.toHeppMarking N.2) anchor.1 ≤
          2 * (t.leafCount : ℝ) *
            (scaleN (N.1.toHeppMarking N.2) anchor.1 : ℝ) :=
      tildeScale_le_two_mul_leafCount_mul_scaleN
        ht (N.1.toHeppMarking N.2) anchor.1
    have := hdiam.trans htilde
    simpa [scaleN, BranchExponentData.toHeppMarking,
      BranchExponentData.raw_apply_of_mem N.1 anchor.2] using this

/-- Valid logarithmic branch data admitting an embedding with the two
chosen leaves fixed at `x₀,x₁`. -/
abbrev EndpointValidBranchExponentData
    (t : PlaneTree) (bound M : ℕ)
    (f₀ f₁ : HeppLeaf t) (x₀ x₁ : Z4) :=
  {N : ValidBranchExponentData t bound //
    ∃ z : HeppLeaf t → Z4,
      IsAdmissible (N.1.toHeppMarking N.2) M z ∧
        z f₀ = x₀ ∧ z f₁ = x₁}

noncomputable instance instFintypeEndpointValidBranchExponentData
    (t : PlaneTree) (bound M : ℕ)
    (f₀ f₁ : HeppLeaf t) (x₀ x₁ : Z4) :
    Fintype
      (EndpointValidBranchExponentData
        t bound M f₀ f₁ x₀ x₁) :=
  Fintype.ofFinite _

/-- Forget the endpoint witness while retaining the constrained LCA
coordinate. -/
def endpointDataToConstrained
    {t : PlaneTree} (ht : t.isValid = true)
    {bound M : ℕ}
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (x₀ x₁ : Z4)
    (N : EndpointValidBranchExponentData
      t bound M f₀ f₁ x₀ x₁) :
    ConstrainedValidBranchExponentData t bound anchor
      (endpointExponentFinset (t := t) bound x₀ x₁) := by
  refine ⟨N.1, ?_⟩
  obtain ⟨z, hadm, hz₀, hz₁⟩ := N.2
  have hmem :=
    branchExponent_mem_endpointExponentFinset
      ht N.1 anchor f₀ f₁ hf hanchor z hadm
  simpa [hz₀, hz₁] using hmem

theorem endpointDataToConstrained_injective
    {t : PlaneTree} (ht : t.isValid = true)
    {bound M : ℕ}
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (x₀ x₁ : Z4) :
    Function.Injective
      (endpointDataToConstrained (bound := bound) (M := M)
        ht anchor f₀ f₁ hf hanchor x₀ x₁) := by
  intro N N' h
  apply Subtype.ext
  change N.1 = N'.1
  have hv :=
    congrArg
      (fun q :
        ConstrainedValidBranchExponentData t bound anchor
          (endpointExponentFinset (t := t) bound x₀ x₁) =>
        q.1)
      h
  simpa [endpointDataToConstrained] using hv

/-- The fixed endpoints remove one logarithmic marking coordinate.  The
only residual cost is the number of dyadic exponents in the geometric
window; the next numerical step absorbs that cardinality exponentially. -/
theorem card_endpointValidBranchExponentData_le
    {t : PlaneTree} (ht : t.isValid = true)
    {bound M : ℕ}
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (x₀ x₁ : Z4) :
    Fintype.card
        (EndpointValidBranchExponentData
          t bound M f₀ f₁ x₀ x₁) ≤
      (endpointExponentFinset (t := t) bound x₀ x₁).card *
        (bound + 1) ^ ((BranchNodes t).card - 1) := by
  calc
    Fintype.card
        (EndpointValidBranchExponentData
          t bound M f₀ f₁ x₀ x₁) ≤
      Fintype.card
        (ConstrainedValidBranchExponentData t bound anchor
          (endpointExponentFinset (t := t) bound x₀ x₁)) :=
      Fintype.card_le_of_injective
        (endpointDataToConstrained (bound := bound) (M := M)
          ht anchor f₀ f₁ hf hanchor x₀ x₁)
        (endpointDataToConstrained_injective
          (bound := bound) (M := M) ht anchor
          f₀ f₁ hf hanchor x₀ x₁)
    _ ≤ (endpointExponentFinset (t := t) bound x₀ x₁).card *
        (bound + 1) ^ ((BranchNodes t).card - 1) :=
      card_constrainedValidBranchExponentData_le
        bound anchor
          (endpointExponentFinset (t := t) bound x₀ x₁)

private theorem sum_endpointValidBranchExponentData_le_sum_valid
    {t : PlaneTree} {bound M : ℕ}
    (f₀ f₁ : HeppLeaf t) (x₀ x₁ : Z4)
    (F : ValidBranchExponentData t bound → ℝ)
    (hF : ∀ N, 0 ≤ F N) :
    (∑ N :
        EndpointValidBranchExponentData
          t bound M f₀ f₁ x₀ x₁,
        F N.1) ≤
      ∑ N : ValidBranchExponentData t bound, F N := by
  classical
  let P : ValidBranchExponentData t bound → Prop :=
    fun N =>
      ∃ z : HeppLeaf t → Z4,
        IsAdmissible (N.1.toHeppMarking N.2) M z ∧
          z f₀ = x₀ ∧ z f₁ = x₁
  let s : Finset (ValidBranchExponentData t bound) :=
    Finset.univ.filter P
  calc
    (∑ N :
        EndpointValidBranchExponentData
          t bound M f₀ f₁ x₀ x₁,
        F N.1) =
        ∑ N ∈ s, F N := by
      symm
      apply Finset.sum_subtype
      intro N
      simp [s, P]
    _ ≤ ∑ N ∈ Finset.univ, F N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ s)
      intro N hN hsN
      exact hF N
    _ = ∑ N : ValidBranchExponentData t bound, F N := by
      simp

/-- Fixed endpoints give the paper's refined exponent
`min(|W|+1,n-2)` for every powerset term.  The unique top term uses the
constrained LCA coordinate; all proper subsets inject into the unrestricted
marking carrier. -/
theorem sum_endpointValidBranchExponentData_parentScaleRatio_le
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    {n M : ℕ}
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (x₀ x₁ : Z4)
    (W : Finset (VPos t))
    (hW : W ⊆ nonrootBranches t) :
    (∑ N :
        EndpointValidBranchExponentData t
          (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁,
        ∏ v ∈ nonrootBranches t \ W,
          parentScaleRatio
            (N.1.1.toHeppMarking N.1.2) v) ≤
      ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          min (W.card + 1) (n - 2) *
        2 ^ ((nonrootBranches t).card - W.card)) := by
  let L : ℕ := Nat.log 2 (4 * M) + 1
  by_cases htop : W = nonrootBranches t
  · subst W
    have hbranchNodes :
        (BranchNodes t).card - 1 =
          (nonrootBranches t).card := by
      have hcard :
          (nonrootBranches t).card + 1 =
            (BranchNodes t).card := by
        simpa [nonrootBranches] using
          Finset.card_erase_add_one hroot
      omega
    have hendpoint :=
      card_endpointValidBranchExponentData_le
        ht (bound := Nat.log 2 (4 * M)) (M := M)
        anchor f₀ f₁ hf hanchor x₀ x₁
    have hallowed :=
      card_endpointExponentFinset_le
        (t := t) (Nat.log 2 (4 * M)) x₀ x₁
    have hcard :
        Fintype.card
            (EndpointValidBranchExponentData t
              (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁) ≤
          (4 * t.leafCount + 1) * L ^ (n - 2) := by
      calc
        Fintype.card
            (EndpointValidBranchExponentData t
              (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁) ≤
            (endpointExponentFinset (t := t)
              (Nat.log 2 (4 * M)) x₀ x₁).card *
              L ^ ((BranchNodes t).card - 1) := by
          simpa [L] using hendpoint
        _ ≤ (4 * t.leafCount + 1) *
              L ^ ((BranchNodes t).card - 1) :=
          Nat.mul_le_mul_right _ hallowed
        _ = (4 * t.leafCount + 1) * L ^ (n - 2) := by
          rw [hbranchNodes, hbranchCard]
    have hmin :
        min ((nonrootBranches t).card + 1) (n - 2) =
          n - 2 := by
      rw [hbranchCard]
      omega
    simp only [Finset.sdiff_self, Finset.prod_empty]
    calc
      (∑ _N :
          EndpointValidBranchExponentData t
            (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁, 1) =
          (Fintype.card
            (EndpointValidBranchExponentData t
              (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁) : ℝ) := by
        simp
      _ ≤ (((4 * t.leafCount + 1) * L ^ (n - 2) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ = ((4 * t.leafCount + 1 : ℕ) : ℝ) *
          ((L : ℝ) ^ min ((nonrootBranches t).card + 1) (n - 2) *
            2 ^ ((nonrootBranches t).card -
              (nonrootBranches t).card)) := by
        rw [hmin]
        push_cast
        simp
  · have hWcard :
        W.card < (nonrootBranches t).card := by
      have hle :=
        Finset.card_le_card hW
      have hne :
          W.card ≠ (nonrootBranches t).card := by
        intro heq
        apply htop
        apply Finset.eq_of_subset_of_card_le hW
        omega
      omega
    have hmin :
        min (W.card + 1) (n - 2) = W.card + 1 := by
      apply min_eq_left
      rw [← hbranchCard]
      omega
    have hsub :=
      sum_endpointValidBranchExponentData_le_sum_valid
        (bound := Nat.log 2 (4 * M)) (M := M)
        f₀ f₁ x₀ x₁
        (fun N =>
          ∏ v ∈ nonrootBranches t \ W,
            parentScaleRatio
              (N.1.toHeppMarking N.2) v)
        (fun N => Finset.prod_nonneg fun v _ => by
          unfold parentScaleRatio
          positivity)
    have hgeneric :=
      sum_logBranchExponentData_parentScaleRatio_le
        ht hroot M W hW
    have hfactor :
        (1 : ℝ) ≤ ((4 * t.leafCount + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    have htail :
        0 ≤ ((L : ℝ) ^ (W.card + 1) *
          2 ^ ((nonrootBranches t).card - W.card)) := by
      positivity
    calc
      (∑ N :
          EndpointValidBranchExponentData t
            (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁,
          ∏ v ∈ nonrootBranches t \ W,
            parentScaleRatio
              (N.1.1.toHeppMarking N.1.2) v) ≤
          ∑ N :
            ValidBranchExponentData t (Nat.log 2 (4 * M)),
            ∏ v ∈ nonrootBranches t \ W,
              parentScaleRatio
                (N.1.toHeppMarking N.2) v := hsub
      _ ≤ (L : ℝ) ^ (W.card + 1) *
          2 ^ ((nonrootBranches t).card - W.card) := by
        simpa [L] using hgeneric
      _ = 1 * ((L : ℝ) ^ (W.card + 1) *
          2 ^ ((nonrootBranches t).card - W.card)) := by ring
      _ ≤ ((4 * t.leafCount + 1 : ℕ) : ℝ) *
          ((L : ℝ) ^ (W.card + 1) *
            2 ^ ((nonrootBranches t).card - W.card)) :=
        mul_le_mul_of_nonneg_right hfactor htail
      _ = ((4 * t.leafCount + 1 : ℕ) : ℝ) *
          ((L : ℝ) ^ min (W.card + 1) (n - 2) *
            2 ^ ((nonrootBranches t).card - W.card)) := by
        rw [hmin]

/-! ## Endpoint-refined summation of (5.16)--(5.17) -/

/-- The (5.16) marking sum restricted to markings which genuinely realize
the two fixed endpoint values at two fixed distinct leaves. -/
def primitiveEndpointMarkingRatioSum
    (C : ℝ) (n M : ℕ) (t : PlaneTree)
    (f₀ f₁ : HeppLeaf t) (x₀ x₁ : Z4) : ℝ :=
  ∑ N :
      EndpointValidBranchExponentData t
        (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁,
    primitiveRatioRHS C n t
      (N.1.1.toHeppMarking N.1.2)

/-- In the extremal tree, the complete endpoint-valid marking sum has the
refined exponent `min(|W|+1,n-2)` term by term. -/
theorem primitiveEndpointMarkingRatioSum_le_refinedDyadic
    {C : ℝ} (hC : 0 ≤ C)
    {n M : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (x₀ x₁ : Z4) :
    primitiveEndpointMarkingRatioSum
        C n M t f₀ f₁ x₀ x₁ ≤
      C ^ n * ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            ((((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                min (W.card + 1) (n - 2)) *
              2 ^ ((nonrootBranches t).card - W.card)) := by
  unfold primitiveEndpointMarkingRatioSum primitiveRatioRHS
  calc
    (∑ N :
        EndpointValidBranchExponentData t
          (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁,
      C ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            ∏ v ∈ nonrootBranches t \ W,
              parentScaleRatio
                (N.1.1.toHeppMarking N.1.2) v) =
      C ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            (∑ N :
              EndpointValidBranchExponentData t
                (Nat.log 2 (4 * M)) M f₀ f₁ x₀ x₁,
              ∏ v ∈ nonrootBranches t \ W,
                parentScaleRatio
                  (N.1.1.toHeppMarking N.1.2) v) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro W hW
      rw [Finset.mul_sum]
    _ ≤ C ^ n *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            (((4 * t.leafCount + 1 : ℕ) : ℝ) *
              ((((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                min (W.card + 1) (n - 2)) *
              2 ^ ((nonrootBranches t).card - W.card))) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC n)
      apply Finset.sum_le_sum
      intro W hW
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact
        sum_endpointValidBranchExponentData_parentScaleRatio_le
          ht hroot hbranchCard anchor f₀ f₁ hf hanchor x₀ x₁
          W (Finset.mem_powerset.mp hW)
    _ = C ^ n *
        (((4 * t.leafCount + 1 : ℕ) : ℝ) *
          ∑ W ∈ (nonrootBranches t).powerset,
            ((n - W.card).factorial : ℝ) *
              ((((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  min (W.card + 1) (n - 2)) *
                2 ^ ((nonrootBranches t).card - W.card))) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W hW
      ring
    _ = C ^ n * ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            ((((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                min (W.card + 1) (n - 2)) *
              2 ^ ((nonrootBranches t).card - W.card)) := by
      ring

/-- Pulling the residual geometric-series factors out of the refined
powerset sum costs at most `2^|B\{r}|`. -/
theorem primitiveEndpointMarkingRatioSum_le_factorialLog
    {C : ℝ} (hC : 0 ≤ C)
    {n M K : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (hn : 2 ≤ n)
    (htotal : totalMultiplicity mu = 2 * n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (x₀ x₁ : Z4) :
    primitiveEndpointMarkingRatioSum
        C n M t f₀ f₁ x₀ x₁ ≤
      C ^ n * ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        2 ^ (nonrootBranches t).card *
          ((16 * (K + 1) : ℝ) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2))) := by
  let L : ℕ := Nat.log 2 (4 * M) + 1
  have hbalance :=
    tree_sum_factorial_log_balance
      ht hroot mu n L K hn htotal hnL
  calc
    primitiveEndpointMarkingRatioSum
        C n M t f₀ f₁ x₀ x₁ ≤
      C ^ n * ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        ∑ W ∈ (nonrootBranches t).powerset,
          ((n - W.card).factorial : ℝ) *
            ((L : ℝ) ^ min (W.card + 1) (n - 2) *
              2 ^ ((nonrootBranches t).card - W.card)) := by
      simpa [L] using
        primitiveEndpointMarkingRatioSum_le_refinedDyadic
          hC ht hroot hbranchCard anchor f₀ f₁ hf hanchor x₀ x₁
    _ ≤ C ^ n * ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        (2 ^ (nonrootBranches t).card *
          ∑ W ∈ (nonrootBranches t).powerset,
            ((n - W.card).factorial : ℝ) *
              (L : ℝ) ^ min (W.card + 1) (n - 2)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (pow_nonneg hC n) (Nat.cast_nonneg _))
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro W hW
      have hpow :
          (2 : ℝ) ^ ((nonrootBranches t).card - W.card) ≤
            2 ^ (nonrootBranches t).card :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      have hbase :
          0 ≤ ((n - W.card).factorial : ℝ) *
            (L : ℝ) ^ min (W.card + 1) (n - 2) := by
        positivity
      calc
        ((n - W.card).factorial : ℝ) *
            ((L : ℝ) ^ min (W.card + 1) (n - 2) *
              2 ^ ((nonrootBranches t).card - W.card)) =
          (((n - W.card).factorial : ℝ) *
            (L : ℝ) ^ min (W.card + 1) (n - 2)) *
              2 ^ ((nonrootBranches t).card - W.card) := by ring
        _ ≤ (((n - W.card).factorial : ℝ) *
            (L : ℝ) ^ min (W.card + 1) (n - 2)) *
              2 ^ (nonrootBranches t).card :=
          mul_le_mul_of_nonneg_left hpow hbase
        _ = 2 ^ (nonrootBranches t).card *
            (((n - W.card).factorial : ℝ) *
              (L : ℝ) ^ min (W.card + 1) (n - 2)) := by ring
    _ ≤ C ^ n * ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        (2 ^ (nonrootBranches t).card *
          ((16 * (K + 1) : ℝ) ^ n *
            (L : ℝ) ^ (n - 2))) := by
      gcongr
    _ = _ := by
      simp only [L]
      ring

private theorem four_mul_add_one_le_eight_pow
    (r : ℕ) (hr : 1 ≤ r) :
    4 * r + 1 ≤ 8 ^ r := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        norm_num
      · have ihr : 4 * r + 1 ≤ 8 ^ r :=
          ih (Nat.one_le_iff_ne_zero.mpr hr0)
        have hp : 1 ≤ 8 ^ r :=
          one_le_pow₀ (by norm_num)
        rw [pow_succ]
        omega

private theorem leafCount_le_order_of_totalMultiplicity
    {t : PlaneTree} (mu : Multiplicities t)
    {n : ℕ} (htotal : totalMultiplicity mu = 2 * n) :
    t.leafCount ≤ n := by
  have hleaf :
      2 * t.leafCount ≤ totalMultiplicity mu := by
    rw [totalMultiplicity]
    calc
      2 * t.leafCount =
          ∑ _l : HeppLeaf t, 2 := by
        simp [card_Leaves_eq_leafCount, Nat.mul_comm]
      _ ≤ ∑ l : HeppLeaf t, leafMultiplicity mu l :=
        Finset.sum_le_sum fun l _ => mu.two_le l.1 l.2
  omega

/-- Non-extremal form of the complete numerical marking assembly: the
unrestricted marking carrier already has at most `n-2` logarithmic
coordinates, and every residual finite factor is absorbed into the displayed
exponential base. -/
theorem primitiveMarkingRatioSum_le_final_of_card_lt
    {C : ℝ} (hC : 0 ≤ C)
    {n M K : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (hn : 2 ≤ n)
    (htotal : totalMultiplicity mu = 2 * n)
    (hcard : (nonrootBranches t).card < n - 2)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1)) :
    primitiveMarkingRatioSum C n M t ≤
      (32 * C * (K + 1)) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (n - 2)) := by
  have hgeneric :=
    primitiveMarkingRatioSum_le_genericDyadic
      (n := n) (M := M) hC ht hroot
  have hfactorial :=
    primitiveGenericDyadicRHS_le_factorialLog_of_card_lt
      (n := n) (M := M) (K := K)
      hC ht hroot mu hn htotal hcard hnL
  have hbranchLe :
      (nonrootBranches t).card ≤ n := by
    omega
  have hpow :
      (2 : ℝ) ^ (nonrootBranches t).card ≤ 2 ^ n :=
    pow_le_pow_right₀ (by norm_num) hbranchLe
  have htail :
      0 ≤ (16 * (K + 1) : ℝ) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (n - 2)) := by
    positivity
  calc
    primitiveMarkingRatioSum C n M t ≤
        primitiveGenericDyadicRHS C n M t :=
      hgeneric
    _ ≤ C ^ n * 2 ^ (nonrootBranches t).card *
        ((16 * (K + 1) : ℝ) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (n - 2))) := hfactorial
    _ ≤ C ^ n * 2 ^ n *
        ((16 * (K + 1) : ℝ) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (n - 2))) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow htail)
          (pow_nonneg hC n)
    _ = (32 * C * (K + 1)) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (n - 2)) := by
      rw [show (32 * C * (K + 1) : ℝ) =
        C * 2 * (16 * (K + 1)) by ring]
      simp only [mul_pow]
      ring

/-- Extremal endpoint form of the complete numerical marking assembly.
The one LCA scale constrained by the fixed endpoint values replaces the
otherwise extra logarithm; all polynomial and geometric losses are absorbed
into the explicit base `256*C*(K+1)`. -/
theorem primitiveEndpointMarkingRatioSum_le_final_of_card_eq
    {C : ℝ} (hC : 0 ≤ C)
    {n M K : ℕ} {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (hn : 2 ≤ n)
    (htotal : totalMultiplicity mu = 2 * n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (hbranchCard : (nonrootBranches t).card = n - 2)
    (anchor : {v // v ∈ BranchNodes t})
    (f₀ f₁ : HeppLeaf t) (hf : f₀ ≠ f₁)
    (hanchor : anchor.1 = lcaV f₀.1 f₁.1)
    (x₀ x₁ : Z4) :
    primitiveEndpointMarkingRatioSum
        C n M t f₀ f₁ x₀ x₁ ≤
      (256 * C * (K + 1)) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (n - 2)) := by
  have hraw :=
    primitiveEndpointMarkingRatioSum_le_factorialLog
      hC ht hroot mu hn htotal hnL hbranchCard
      anchor f₀ f₁ hf hanchor x₀ x₁
  have hleaf : t.leafCount ≤ n :=
    leafCount_le_order_of_totalMultiplicity mu htotal
  have hleafFactorNat :
      4 * t.leafCount + 1 ≤ 8 ^ n := by
    exact
      (four_mul_add_one_le_eight_pow
        t.leafCount (one_le_leafCount t)).trans
        (Nat.pow_le_pow_right (by norm_num) hleaf)
  have hleafFactor :
      (((4 * t.leafCount + 1 : ℕ) : ℝ)) ≤
        (8 : ℝ) ^ n := by
    exact_mod_cast hleafFactorNat
  have hbranchLe :
      (nonrootBranches t).card ≤ n := by
    omega
  have htwo :
      (2 : ℝ) ^ (nonrootBranches t).card ≤ 2 ^ n :=
    pow_le_pow_right₀ (by norm_num) hbranchLe
  have hCpow : 0 ≤ C ^ n := pow_nonneg hC n
  have htail :
      0 ≤ (16 * (K + 1) : ℝ) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (n - 2)) := by
    positivity
  calc
    primitiveEndpointMarkingRatioSum
        C n M t f₀ f₁ x₀ x₁ ≤
      C ^ n * ((4 * t.leafCount + 1 : ℕ) : ℝ) *
        2 ^ (nonrootBranches t).card *
          ((16 * (K + 1) : ℝ) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2))) := hraw
    _ ≤ C ^ n * 8 ^ n * 2 ^ n *
        ((16 * (K + 1) : ℝ) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
            (n - 2))) := by
      gcongr
    _ = (256 * C * (K + 1)) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
          (n - 2)) := by
      rw [show (256 * C * (K + 1) : ℝ) =
        C * 8 * 2 * (16 * (K + 1)) by ring]
      simp only [mul_pow]
      ring

/-! ## One-datum P-5.6/P-5.7 lattice assembly -/

/-- The maximum lattice bracket on a nonempty tuple.  Unlike the earlier
`latticeTupleDiameterBracketSq`, this form is indexed by `Fin m` directly,
which is the carrier used by the paired-incidence layer. -/
def primitiveTupleDiameterBracketSq
    {m : ℕ} (hm : 0 < m) (y : Fin m → Z4) : ℝ :=
  Finset.univ.sup'
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    (fun i : Fin m =>
      Finset.univ.sup'
        ⟨⟨0, hm⟩, Finset.mem_univ _⟩
        (fun j : Fin m => latticeBracketSq (y i) (y j)))

theorem primitiveTupleDiameterBracketSq_nonneg
    {m : ℕ} (hm : 0 < m) (y : Fin m → Z4) :
    0 ≤ primitiveTupleDiameterBracketSq hm y := by
  let i₀ : Fin m := ⟨0, hm⟩
  have hinner :
      latticeBracketSq (y i₀) (y i₀) ≤
        Finset.univ.sup'
          ⟨i₀, Finset.mem_univ _⟩
          (fun j : Fin m => latticeBracketSq (y i₀) (y j)) :=
    Finset.le_sup'
      (f := fun j : Fin m => latticeBracketSq (y i₀) (y j))
      (by simp)
  have houter :
      (Finset.univ.sup'
        ⟨i₀, Finset.mem_univ _⟩
        (fun j : Fin m => latticeBracketSq (y i₀) (y j))) ≤
      Finset.univ.sup'
        ⟨i₀, Finset.mem_univ _⟩
        (fun i : Fin m =>
          Finset.univ.sup'
            ⟨i₀, Finset.mem_univ _⟩
            (fun j : Fin m => latticeBracketSq (y i) (y j))) :=
    Finset.le_sup'
      (f := fun i : Fin m =>
        Finset.univ.sup'
          ⟨i₀, Finset.mem_univ _⟩
          (fun j : Fin m => latticeBracketSq (y i) (y j)))
      (by simp)
  exact (latticeBracketSq_nonneg (y i₀) (y i₀)).trans
    (hinner.trans houter)

/-- Root-cluster control of the actual maximum bracket on the paired tuple
carrier. -/
theorem primitiveTupleDiameterBracketSq_le_rootScale
    {t : PlaneTree} (ht : t.isValid = true)
    {m M : ℕ} (hm : 0 < m)
    {Nm : HeppMarking t} {mu : Multiplicities t}
    {y : Fin m → Z4}
    (hreal : RealizesTuple t Nm mu M y) :
    primitiveTupleDiameterBracketSq hm y ≤
      (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        (scaleN Nm (rootV t) : ℝ) ^ 2 := by
  obtain ⟨z, w, hadm, _hw, hy⟩ := hreal
  unfold primitiveTupleDiameterBracketSq
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  have hwi : w i ∈ leavesUnder (rootV t) := by
    rw [mem_leavesUnder]
    exact List.nil_prefix
  have hwj : w j ∈ leavesUnder (rootV t) := by
    rw [mem_leavesUnder]
    exact List.nil_prefix
  have hdist :
      znorm (z (w i) - z (w j)) ≤
        2 * (t.leafCount : ℝ) *
          (scaleN Nm (rootV t) : ℝ) :=
    (clusterDiameter_le_tildeScale hadm (rootV t) hwi hwj).trans
      (tildeScale_le_two_mul_leafCount_mul_scaleN
        ht Nm (rootV t))
  have hscale :
      (1 : ℝ) ≤ scaleN Nm (rootV t) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (scaleN_pos Nm (rootV t)))
  rw [hy i, hy j]
  unfold latticeBracketSq
  have hsq :
      znorm (z (w i) - z (w j)) ^ 2 ≤
        (2 * (t.leafCount : ℝ) *
          (scaleN Nm (rootV t) : ℝ)) ^ 2 := by
    have hdist0 : 0 ≤ znorm (z (w i) - z (w j)) :=
      norm_nonneg _
    have hupper0 :
        0 ≤ 2 * (t.leafCount : ℝ) *
          (scaleN Nm (rootV t) : ℝ) := by
      positivity
    nlinarith
  calc
    1 + znorm (z (w i) - z (w j)) ^ 2 ≤
        (scaleN Nm (rootV t) : ℝ) ^ 2 +
          (2 * (t.leafCount : ℝ) *
            (scaleN Nm (rootV t) : ℝ)) ^ 2 := by
      have hsquare :
          (1 : ℝ) ≤ (scaleN Nm (rootV t) : ℝ) ^ 2 := by
        nlinarith
      gcongr
    _ = (1 + (2 * (t.leafCount : ℝ)) ^ 2) *
        (scaleN Nm (rootV t) : ℝ) ^ 2 := by ring
    _ ≤ (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        (scaleN Nm (rootV t) : ℝ) ^ 2 := by
      have hr : 0 ≤ (t.leafCount : ℝ) := by positivity
      gcongr
      nlinarith

/-- **Fixed-data lattice assembly for R-4.1pf.**

For one paired incidence datum, the actual maximum bracket and the complete
primitive pairing/profile chain sum are bounded by P-5.6 and P-5.7.  The
branch-volume and root-scale monomials cancel exactly, leaving the (5.16)
parent-ratio expression. -/
theorem primitive_lattice_estimate
    {C : ℝ} (hC : PermSumEstimate C)
    {n M : ℕ} {t : PlaneTree}
    (d : PairedValidRealizationData t M (2 * n))
    (Y : Finset (Fin (2 * n) → Z4))
    (Z : Finset Z4) (A : Finset (Fin (2 * n)))
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (hYreal : ∀ y ∈ Y, PairedDataRealizes d y)
    (y : Fin (2 * n) → Z4)
    (hyreal : PairedDataRealizes d y)
    (κ : AcrossPairing A) (hκ : RespectsWord A y κ)
    (x₀ x₁ : Z4) :
    (((realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁).card : ℝ) /
        pairedTreeSymDenom t M (2 * n) y) *
      primitiveTupleDiameterBracketSq (by omega) y *
        (∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
          ∑ w ∈ inducedWordsAtProfile Y Z p,
            ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
              supportChainWeight w) ≤
      volumeEstimateFinalConstant ^ t.leafCount *
        (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        latticeBracketInvFourth x₀ x₁ *
          primitiveRatioRHS (4 * C) n t (pairedMarking d) := by
  let a : ℝ :=
    ((realizedSetsContainingPair d.1.1 d.2.1.1 x₀ x₁).card : ℝ) /
      pairedTreeSymDenom t M (2 * n) y
  let D : ℝ := primitiveTupleDiameterBracketSq (by omega) y
  let S : ℝ :=
    ∑ p : PositiveAssignment {x // x ∈ Z} (2 * n),
      ∑ w ∈ inducedWordsAtProfile Y Z p,
        ((primitiveCompatibleAcrossPairings A w).card : ℝ) *
          supportChainWeight w
  let V : ℝ :=
    volumeEstimateFinalConstant ^ t.leafCount *
      branchScaleProduct (pairedMarking d) *
        latticeBracketInvFourth x₀ x₁
  let D₀ : ℝ :=
    (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
      (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2
  let Q : ℝ :=
    primitiveScaleRHS (4 * C) n t (pairedMarking d)
  have ha : a ≤ V := by
    exact
      realizedSetsPair_div_pairedDenom_le_volume
        ht d.1.1 d.2.1.1 (pairedMultiplicities d)
        y hyreal A κ hκ x₀ x₁
  have hD : D ≤ D₀ := by
    exact primitiveTupleDiameterBracketSq_le_rootScale
      ht (by omega) hyreal
  have hS : S ≤ Q := by
    exact
      sum_profiles_primitivePairings_chainWeight_le_primitiveScaleRHS
        hC d Y Z A hn ht hroot hYreal
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) y
  have hV0 : 0 ≤ V := by
    dsimp only [V]
    exact mul_nonneg
      (mul_nonneg (by
        unfold volumeEstimateFinalConstant
        positivity)
        (branchScaleProduct_nonneg (pairedMarking d)))
      (latticeBracketInvFourth_nonneg x₀ x₁)
  have hD₀0 : 0 ≤ D₀ := by
    dsimp only [D₀]
    positivity
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact primitiveScaleRHS_nonneg
      (mul_nonneg (by norm_num) hC.1.le)
      n t (pairedMarking d)
  have haD : a * D ≤ V * D₀ :=
    mul_le_mul ha hD hD0 hV0
  calc
    a * D * S ≤ a * D * Q :=
      mul_le_mul_of_nonneg_left hS (mul_nonneg ha0 hD0)
    _ ≤ V * D₀ * Q :=
      mul_le_mul_of_nonneg_right haD hQ0
    _ = volumeEstimateFinalConstant ^ t.leafCount *
        (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        latticeBracketInvFourth x₀ x₁ *
          ((branchScaleProduct (pairedMarking d) *
              (scaleN (pairedMarking d) (rootV t) : ℝ) ^ 2) *
            primitiveScaleRHS (4 * C) n t (pairedMarking d)) := by
      dsimp only [V, D₀, Q]
      ring
    _ = volumeEstimateFinalConstant ^ t.leafCount *
        (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        latticeBracketInvFourth x₀ x₁ *
          primitiveRatioRHS (4 * C) n t (pairedMarking d) := by
      rw [branchVolume_rootDiameter_mul_primitiveScaleRHS]

end

end Anderson4D
