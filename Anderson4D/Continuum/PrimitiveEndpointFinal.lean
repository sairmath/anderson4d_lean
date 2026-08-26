import Anderson4D.Continuum.PrimitiveEndpointExtremal

/-!
# Final endpoint-preserving lattice assembly

This file combines the non-extremal, extremal, and bare-leaf branches of
the endpoint-preserving Hepp-tree decomposition.  The endpoint bracket is
never discarded.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-- Extremal counterpart of
`primitiveEndpointTreeIncidenceSum_le_of_card_lt_aux`. -/
theorem primitiveEndpointTreeIncidenceSum_le_of_card_eq_aux
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t)
    (htotal : totalMultiplicity mu = 2 * n)
    (hcard : (nonrootBranches t).card = n - 2)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (Y : Finset (Fin (2 * n) → Z4))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointTreeIncidenceSum
        M n (by omega) t Y A x₀ x₁ ≤
      (volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          latticeBracketInvFourth x₀ x₁) *
        (((n * n : ℕ) : ℝ) *
          ((256 * (4 * C) * (K + 1)) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2)))) := by
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
        (((n * n : ℕ) : ℝ) *
          ((256 * (4 * C) * (K + 1)) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2)))) := by
      apply mul_le_mul_of_nonneg_left _ hK₀
      exact
        sum_activeExtremal_le_final
          (mul_nonneg (by norm_num) hC.1.le)
          ht hroot mu hn htotal hnL hcard
    _ = _ := by rfl

/-- A common nonnegative raw bound for every tree branch. -/
def primitiveEndpointTreeRawBound
    (C : ℝ) (M n K : ℕ) (t : PlaneTree)
    (x₀ x₁ : Z4) : ℝ :=
  latticeBracketInvFourth x₀ x₁ *
    ((8 * (K + 1) : ℝ) ^ n *
        (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) +
      (volumeEstimateFinalConstant ^ t.leafCount *
        (1 + 2 * (t.leafCount : ℝ)) ^ 2) *
        ((((2 ^ n : ℕ) : ℝ) *
            ((32 * (4 * C) * (K + 1)) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (n - 2)))) +
          (((n * n : ℕ) : ℝ) *
            ((256 * (4 * C) * (K + 1)) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (n - 2))))))

theorem primitiveEndpointTreeRawBound_nonneg
    {C : ℝ} (hC : 0 ≤ C)
    (M n K : ℕ) (t : PlaneTree) (x₀ x₁ : Z4) :
    0 ≤ primitiveEndpointTreeRawBound C M n K t x₀ x₁ := by
  unfold primitiveEndpointTreeRawBound
  have hvol : 0 ≤ volumeEstimateFinalConstant := by
    unfold volumeEstimateFinalConstant
    positivity
  have hsmall :
      0 ≤ (32 * (4 * C) * (K + 1) : ℝ) := by
    positivity
  have hlarge :
      0 ≤ (256 * (4 * C) * (K + 1) : ℝ) := by
    positivity
  exact mul_nonneg
    (latticeBracketInvFourth_nonneg x₀ x₁)
    (add_nonneg
      (mul_nonneg (pow_nonneg (by positivity) n) (by positivity))
      (mul_nonneg
        (mul_nonneg (pow_nonneg hvol t.leafCount) (sq_nonneg _))
        (add_nonneg
          (mul_nonneg (by positivity)
            (mul_nonneg (pow_nonneg hsmall n) (by positivity)))
          (mul_nonneg (by positivity)
            (mul_nonneg (pow_nonneg hlarge n) (by positivity))))))

private theorem primitiveEndpointTreeIncidenceSum_eq_zero_of_noActive
    {M n : ℕ} {hn : 1 ≤ n} {t : PlaneTree}
    {Y : Finset (Fin (2 * n) → Z4)}
    {A : Finset (Fin (2 * n))} {x₀ x₁ : Z4}
    (hactive :
      ¬Nonempty
        (PrimitiveActiveEndpointData
          t M n hn Y A x₀ x₁)) :
    primitiveEndpointTreeIncidenceSum M n hn t Y A x₀ x₁ = 0 := by
  rw [primitiveEndpointTreeIncidenceSum_eq_active]
  apply Finset.sum_eq_zero
  intro d hd
  exact False.elim (hactive ⟨d⟩)

/-- Uniform raw bound for the tree slice which actually occurs in the
endpoint lattice cover. -/
theorem primitiveEndpointTreeTupleIncidence_le_rawBound
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n) {t : PlaneTree}
    (ht : t.isValid = true)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointTreeIncidenceSum M n (by omega) t
        (primitiveEndpointTreeTupleFamily
          M n (by omega) t A x₀ x₁)
        A x₀ x₁ ≤
      primitiveEndpointTreeRawBound C M n K t x₀ x₁ := by
  classical
  let Y :=
    primitiveEndpointTreeTupleFamily
      M n (by omega : 1 ≤ n) t A x₀ x₁
  rcases validTree_root_branch_or_eq_leaf ht with hroot | hleaf
  · let Active :=
      PrimitiveActiveEndpointData
        t M n (by omega : 1 ≤ n) Y A x₀ x₁
    by_cases hactive : Nonempty Active
    · let d : Active := Classical.choice hactive
      let mu : Multiplicities t := pairedMultiplicities d.1
      have htotal : totalMultiplicity mu = 2 * n :=
        RealizationData.toMultiplicities_total d.1.1 d.1.2.1
      have hcard :
          (nonrootBranches t).card ≤ n - 2 :=
        card_nonrootBranches_le_order_sub_two
          ht hroot mu n htotal
      by_cases hlt : (nonrootBranches t).card < n - 2
      · have hraw :=
          primitiveEndpointTreeIncidenceSum_le_of_card_lt
            hC hn ht hroot hlt hnL Y A x₀ x₁
        calc
          primitiveEndpointTreeIncidenceSum M n (by omega) t
              Y A x₀ x₁ ≤
            (volumeEstimateFinalConstant ^ t.leafCount *
                (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
                latticeBracketInvFourth x₀ x₁) *
              (((2 ^ n : ℕ) : ℝ) *
                ((32 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))) := hraw
          _ ≤ primitiveEndpointTreeRawBound C M n K t x₀ x₁ := by
            let Vp : ℝ :=
              volumeEstimateFinalConstant ^ t.leafCount *
                (1 + 2 * (t.leafCount : ℝ)) ^ 2
            let S : ℝ :=
              ((2 ^ n : ℕ) : ℝ) *
                ((32 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))
            let E : ℝ :=
              ((n * n : ℕ) : ℝ) *
                ((256 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))
            let Lf : ℝ :=
              (8 * (K + 1) : ℝ) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  (n - 2))
            have hb :=
              latticeBracketInvFourth_nonneg x₀ x₁
            have hvol : 0 ≤ volumeEstimateFinalConstant := by
              unfold volumeEstimateFinalConstant
              positivity
            have hVp : 0 ≤ Vp := by
              exact mul_nonneg
                (pow_nonneg hvol t.leafCount) (sq_nonneg _)
            have hbaseSmall :
                0 ≤ (32 * (4 * C) * (K + 1) : ℝ) := by
              exact mul_nonneg
                (mul_nonneg (by norm_num)
                  (mul_nonneg (by norm_num) hC.1.le))
                (add_nonneg (Nat.cast_nonneg K) zero_le_one)
            have hbaseLarge :
                0 ≤ (256 * (4 * C) * (K + 1) : ℝ) := by
              exact mul_nonneg
                (mul_nonneg (by norm_num)
                  (mul_nonneg (by norm_num) hC.1.le))
                (add_nonneg (Nat.cast_nonneg K) zero_le_one)
            have hS : 0 ≤ S := by
              exact mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (pow_nonneg hbaseSmall n)
                  (by positivity))
            have hE : 0 ≤ E := by
              exact mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (pow_nonneg hbaseLarge n)
                  (by positivity))
            have hLf : 0 ≤ Lf := by
              exact mul_nonneg (pow_nonneg (by positivity) n)
                (by positivity)
            calc
              (volumeEstimateFinalConstant ^ t.leafCount *
                    (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
                    latticeBracketInvFourth x₀ x₁) *
                  (((2 ^ n : ℕ) : ℝ) *
                    ((32 * (4 * C) * (K + 1)) ^ n *
                      (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                        (n - 2)))) =
                latticeBracketInvFourth x₀ x₁ * (Vp * S) := by
                  dsimp only [Vp, S]
                  ring
              _ ≤ latticeBracketInvFourth x₀ x₁ *
                  (Lf + Vp * (S + E)) := by
                apply mul_le_mul_of_nonneg_left _ hb
                exact
                  (mul_le_mul_of_nonneg_left
                    (le_add_of_nonneg_right hE) hVp).trans
                    (le_add_of_nonneg_left hLf)
              _ = primitiveEndpointTreeRawBound
                  C M n K t x₀ x₁ := by
                unfold primitiveEndpointTreeRawBound
                dsimp only [Vp, S, E, Lf]
      · have heq :
          (nonrootBranches t).card = n - 2 := by omega
        have hraw :=
          primitiveEndpointTreeIncidenceSum_le_of_card_eq_aux
            hC hn ht hroot mu htotal heq hnL Y A x₀ x₁
        calc
          primitiveEndpointTreeIncidenceSum M n (by omega) t
              Y A x₀ x₁ ≤
            (volumeEstimateFinalConstant ^ t.leafCount *
                (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
                latticeBracketInvFourth x₀ x₁) *
              (((n * n : ℕ) : ℝ) *
                ((256 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))) := hraw
          _ ≤ primitiveEndpointTreeRawBound C M n K t x₀ x₁ := by
            let Vp : ℝ :=
              volumeEstimateFinalConstant ^ t.leafCount *
                (1 + 2 * (t.leafCount : ℝ)) ^ 2
            let S : ℝ :=
              ((2 ^ n : ℕ) : ℝ) *
                ((32 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))
            let E : ℝ :=
              ((n * n : ℕ) : ℝ) *
                ((256 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))
            let Lf : ℝ :=
              (8 * (K + 1) : ℝ) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  (n - 2))
            have hb :=
              latticeBracketInvFourth_nonneg x₀ x₁
            have hvol : 0 ≤ volumeEstimateFinalConstant := by
              unfold volumeEstimateFinalConstant
              positivity
            have hVp : 0 ≤ Vp := by
              exact mul_nonneg
                (pow_nonneg hvol t.leafCount) (sq_nonneg _)
            have hbaseSmall :
                0 ≤ (32 * (4 * C) * (K + 1) : ℝ) := by
              exact mul_nonneg
                (mul_nonneg (by norm_num)
                  (mul_nonneg (by norm_num) hC.1.le))
                (add_nonneg (Nat.cast_nonneg K) zero_le_one)
            have hbaseLarge :
                0 ≤ (256 * (4 * C) * (K + 1) : ℝ) := by
              exact mul_nonneg
                (mul_nonneg (by norm_num)
                  (mul_nonneg (by norm_num) hC.1.le))
                (add_nonneg (Nat.cast_nonneg K) zero_le_one)
            have hS : 0 ≤ S := by
              exact mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (pow_nonneg hbaseSmall n)
                  (by positivity))
            have hE : 0 ≤ E := by
              exact mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg (pow_nonneg hbaseLarge n)
                  (by positivity))
            have hLf : 0 ≤ Lf := by
              exact mul_nonneg (pow_nonneg (by positivity) n)
                (by positivity)
            calc
              (volumeEstimateFinalConstant ^ t.leafCount *
                    (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
                    latticeBracketInvFourth x₀ x₁) *
                  (((n * n : ℕ) : ℝ) *
                    ((256 * (4 * C) * (K + 1)) ^ n *
                      (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                        (n - 2)))) =
                latticeBracketInvFourth x₀ x₁ * (Vp * E) := by
                  dsimp only [Vp, E]
                  ring
              _ ≤ latticeBracketInvFourth x₀ x₁ *
                  (Lf + Vp * (S + E)) := by
                apply mul_le_mul_of_nonneg_left _ hb
                exact
                  (mul_le_mul_of_nonneg_left
                    (le_add_of_nonneg_left hS) hVp).trans
                    (le_add_of_nonneg_left hLf)
              _ = primitiveEndpointTreeRawBound
                  C M n K t x₀ x₁ := by
                unfold primitiveEndpointTreeRawBound
                dsimp only [Vp, S, E, Lf]
    · have hzero :
          primitiveEndpointTreeIncidenceSum M n (by omega) t
              Y A x₀ x₁ = 0 :=
        primitiveEndpointTreeIncidenceSum_eq_zero_of_noActive
          (by simpa only [Active] using hactive)
      rw [hzero]
      exact
        primitiveEndpointTreeRawBound_nonneg
          hC.1.le M n K t x₀ x₁
  · subst t
    have hleafBound :=
      primitiveEndpointTreeIncidenceSum_leaf_le_factorialLog
        hn hnL A x₀ x₁
    calc
      primitiveEndpointTreeIncidenceSum M n (by omega) leaf
          Y A x₀ x₁ ≤
        (8 * (K + 1) : ℝ) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) *
            latticeBracketInvFourth x₀ x₁ := by
        simpa only [Y] using hleafBound
      _ ≤ primitiveEndpointTreeRawBound C M n K leaf x₀ x₁ := by
        let Vp : ℝ :=
          volumeEstimateFinalConstant ^ leaf.leafCount *
            (1 + 2 * (leaf.leafCount : ℝ)) ^ 2
        let S : ℝ :=
          ((2 ^ n : ℕ) : ℝ) *
            ((32 * (4 * C) * (K + 1)) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (n - 2)))
        let E : ℝ :=
          ((n * n : ℕ) : ℝ) *
            ((256 * (4 * C) * (K + 1)) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                (n - 2)))
        let Lf : ℝ :=
          (8 * (K + 1) : ℝ) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
              (n - 2))
        have hb :=
          latticeBracketInvFourth_nonneg x₀ x₁
        have hvol : 0 ≤ volumeEstimateFinalConstant := by
          unfold volumeEstimateFinalConstant
          positivity
        have hVp : 0 ≤ Vp := by
          exact mul_nonneg
            (pow_nonneg hvol leaf.leafCount) (sq_nonneg _)
        have hbaseSmall :
            0 ≤ (32 * (4 * C) * (K + 1) : ℝ) := by
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (mul_nonneg (by norm_num) hC.1.le))
            (add_nonneg (Nat.cast_nonneg K) zero_le_one)
        have hbaseLarge :
            0 ≤ (256 * (4 * C) * (K + 1) : ℝ) := by
          exact mul_nonneg
            (mul_nonneg (by norm_num)
              (mul_nonneg (by norm_num) hC.1.le))
            (add_nonneg (Nat.cast_nonneg K) zero_le_one)
        have hS : 0 ≤ S := by
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (pow_nonneg hbaseSmall n)
              (by positivity))
        have hE : 0 ≤ E := by
          exact mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (pow_nonneg hbaseLarge n)
              (by positivity))
        have hVpSE : 0 ≤ Vp * (S + E) :=
          mul_nonneg hVp (add_nonneg hS hE)
        calc
          (8 * (K + 1) : ℝ) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  (n - 2)) *
              latticeBracketInvFourth x₀ x₁ =
            latticeBracketInvFourth x₀ x₁ * Lf := by
              dsimp only [Lf]
              ring
          _ ≤ latticeBracketInvFourth x₀ x₁ *
              (Lf + Vp * (S + E)) := by
            apply mul_le_mul_of_nonneg_left _ hb
            exact le_add_of_nonneg_right hVpSE
          _ = primitiveEndpointTreeRawBound
              C M n K leaf x₀ x₁ := by
            unfold primitiveEndpointTreeRawBound
            dsimp only [Vp, S, E, Lf]

/-- Complete discrete endpoint estimate, retaining only a finite sum of
explicit nonnegative raw tree bounds. -/
theorem primitiveEndpointLatticeSum_le_rawTreeSum
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointLatticeSum M n (by omega) A x₀ x₁ ≤
      ∑ t ∈ rdec_treeEnum (2 * n),
        primitiveEndpointTreeRawBound C M n K t x₀ x₁ := by
  calc
    primitiveEndpointLatticeSum M n (by omega) A x₀ x₁ ≤
      ∑ t ∈ rdec_treeEnum (2 * n),
        primitiveEndpointTreeIncidenceSum M n (by omega) t
          (primitiveEndpointTreeTupleFamily
            M n (by omega) t A x₀ x₁)
          A x₀ x₁ :=
      primitiveEndpointLatticeSum_le_treeIncidence
        M n (by omega) A x₀ x₁
    _ ≤ ∑ t ∈ rdec_treeEnum (2 * n),
        primitiveEndpointTreeRawBound C M n K t x₀ x₁ := by
      apply Finset.sum_le_sum
      intro t ht
      exact
        primitiveEndpointTreeTupleIncidence_le_rawBound
          hC hn (rdec_mem_treeEnum.mp ht).1 hnL A x₀ x₁

private theorem one_add_two_mul_le_four_pow
    (r : ℕ) (hr : 1 ≤ r) :
    1 + 2 * r ≤ 4 ^ r := by
  induction r with
  | zero => omega
  | succ r ih =>
      by_cases hr0 : r = 0
      · subst r
        norm_num
      · have hir : 1 + 2 * r ≤ 4 ^ r :=
          ih (Nat.one_le_iff_ne_zero.mpr hr0)
        calc
          1 + 2 * (r + 1) ≤ 4 * (1 + 2 * r) := by omega
          _ ≤ 4 * 4 ^ r := Nat.mul_le_mul_left 4 hir
          _ = 4 ^ (r + 1) := by
            rw [pow_succ]
            ring

private theorem one_add_two_mul_sq_le_sixteen_pow
    (r : ℕ) (hr : 1 ≤ r) :
    (1 + 2 * (r : ℝ)) ^ 2 ≤ (16 : ℝ) ^ r := by
  have hnat :
      (1 + 2 * r) ^ 2 ≤ 16 ^ r := by
    calc
      (1 + 2 * r) ^ 2 ≤ (4 ^ r) ^ 2 :=
        Nat.pow_le_pow_left
          (one_add_two_mul_le_four_pow r hr) 2
      _ = 16 ^ r := by
        rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
        norm_num
  exact_mod_cast hnat

private theorem one_le_volumeEstimateFinalConstant :
    (1 : ℝ) ≤ volumeEstimateFinalConstant := by
  unfold volumeEstimateFinalConstant
  have hexp : (1 : ℝ) ≤ Real.exp 12 :=
    Real.one_le_exp (by norm_num)
  have hstep : (1 : ℝ) ≤ step5VolumeConstant := by
    norm_num [step5VolumeConstant, step5LatticeConstant]
  nlinarith

/-- Uniformize the only tree-dependent scalar in the raw bound using
`leafCount ≤ 2n` from the enumerating carrier. -/
theorem primitiveEndpointTreeRawBound_le_uniform
    {C : ℝ} (hC : 0 ≤ C)
    {M n K : ℕ} {t : PlaneTree}
    (hleaf : t.leafCount ≤ 2 * n)
    (x₀ x₁ : Z4) :
    primitiveEndpointTreeRawBound C M n K t x₀ x₁ ≤
      latticeBracketInvFourth x₀ x₁ *
        ((8 * (K + 1) : ℝ) ^ n *
            (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) +
          (16 * volumeEstimateFinalConstant) ^ (2 * n) *
            ((((2 ^ n : ℕ) : ℝ) *
                ((32 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))) +
              (((n * n : ℕ) : ℝ) *
                ((256 * (4 * C) * (K + 1)) ^ n *
                  (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                    (n - 2)))))) := by
  unfold primitiveEndpointTreeRawBound
  have hr : 1 ≤ t.leafCount := one_le_leafCount t
  have hpoly :=
    one_add_two_mul_sq_le_sixteen_pow t.leafCount hr
  have hvol0 : 0 ≤ volumeEstimateFinalConstant :=
    zero_le_one.trans one_le_volumeEstimateFinalConstant
  have hvol16 : (1 : ℝ) ≤ 16 * volumeEstimateFinalConstant := by
    nlinarith [one_le_volumeEstimateFinalConstant]
  have hVp :
      volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 ≤
        (16 * volumeEstimateFinalConstant) ^ (2 * n) := by
    calc
      volumeEstimateFinalConstant ^ t.leafCount *
          (1 + 2 * (t.leafCount : ℝ)) ^ 2 ≤
        volumeEstimateFinalConstant ^ t.leafCount *
          16 ^ t.leafCount :=
        mul_le_mul_of_nonneg_left hpoly
          (pow_nonneg hvol0 t.leafCount)
      _ = (16 * volumeEstimateFinalConstant) ^ t.leafCount := by
        rw [mul_pow]
        ring
      _ ≤ (16 * volumeEstimateFinalConstant) ^ (2 * n) := by
        exact pow_le_pow_right₀ hvol16 hleaf
  have htail :
      0 ≤ (((((2 ^ n : ℕ) : ℝ) *
              ((32 * (4 * C) * (K + 1)) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  (n - 2)))) +
            (((n * n : ℕ) : ℝ) *
              ((256 * (4 * C) * (K + 1)) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  (n - 2)))))) := by
    have hs :
        0 ≤ (32 * (4 * C) * (K + 1) : ℝ) := by
      positivity
    have he :
        0 ≤ (256 * (4 * C) * (K + 1) : ℝ) := by
      positivity
    positivity
  apply mul_le_mul_of_nonneg_left _ 
    (latticeBracketInvFourth_nonneg x₀ x₁)
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right hVp htail)

/-- Sum the raw bounds over the exponentially bounded tree carrier. -/
theorem primitiveEndpointLatticeSum_le_uniformTreeBound
    {C : ℝ} (hC : PermSumEstimate C)
    {M n K : ℕ} (hn : 2 ≤ n)
    (hnL : n ≤ K * (Nat.log 2 (4 * M) + 1))
    (A : Finset (Fin (2 * n))) (x₀ x₁ : Z4) :
    primitiveEndpointLatticeSum M n (by omega) A x₀ x₁ ≤
      ((4 ^ (4 * (2 * n)) : ℕ) : ℝ) *
        (latticeBracketInvFourth x₀ x₁ *
          ((8 * (K + 1) : ℝ) ^ n *
              (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) +
            (16 * volumeEstimateFinalConstant) ^ (2 * n) *
              ((((2 ^ n : ℕ) : ℝ) *
                  ((32 * (4 * C) * (K + 1)) ^ n *
                    (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                      (n - 2)))) +
                (((n * n : ℕ) : ℝ) *
                  ((256 * (4 * C) * (K + 1)) ^ n *
                    (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                      (n - 2))))))) := by
  let B : ℝ :=
    latticeBracketInvFourth x₀ x₁ *
      ((8 * (K + 1) : ℝ) ^ n *
          (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^ (n - 2)) +
        (16 * volumeEstimateFinalConstant) ^ (2 * n) *
          ((((2 ^ n : ℕ) : ℝ) *
              ((32 * (4 * C) * (K + 1)) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  (n - 2)))) +
            (((n * n : ℕ) : ℝ) *
              ((256 * (4 * C) * (K + 1)) ^ n *
                (((Nat.log 2 (4 * M) + 1 : ℕ) : ℝ) ^
                  (n - 2))))))
  have hraw :=
    primitiveEndpointLatticeSum_le_rawTreeSum
      hC hn hnL A x₀ x₁
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hC0 : 0 ≤ C := hC.1.le
    have hbr : 0 ≤ latticeBracketInvFourth x₀ x₁ :=
      latticeBracketInvFourth_nonneg x₀ x₁
    have hvol : 0 ≤ volumeEstimateFinalConstant :=
      zero_le_one.trans one_le_volumeEstimateFinalConstant
    positivity
  calc
    primitiveEndpointLatticeSum M n (by omega) A x₀ x₁ ≤
      ∑ t ∈ rdec_treeEnum (2 * n),
        primitiveEndpointTreeRawBound C M n K t x₀ x₁ := hraw
    _ ≤ ∑ _t ∈ rdec_treeEnum (2 * n), B := by
      apply Finset.sum_le_sum
      intro t ht
      exact
        primitiveEndpointTreeRawBound_le_uniform
          hC.1.le (rdec_mem_treeEnum.mp ht).2 x₀ x₁
    _ = ((rdec_treeEnum (2 * n)).card : ℝ) * B := by
      simp
    _ ≤ ((4 ^ (4 * (2 * n)) : ℕ) : ℝ) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast rdec_card_treeEnum_le (2 * n)
    _ = _ := by rfl

end

end Anderson4D
