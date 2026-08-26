import Anderson4D.Combinatorics.FactorialBounds
import Anderson4D.ForMathlib.ConnectedParent
import Anderson4D.HeppTree.BranchExcess
import Anderson4D.HeppTree.LatticeBallCount
import Anderson4D.HeppTree.OrderingBound

/-!
# Volume iteration for Proposition 5.6

This file isolates the scalar bookkeeping in paper §5.3, Steps 5--6.
`step5_parent_volume_bound` combines the lattice-ball estimate (5.23) with
the parent-function replacement for the weighted Cayley calculation in
(5.24)--(5.25).  `volume_iteration_bound` then combines its iterated form
with the geometric ancestor sum (5.27) and the ordering estimate (5.21), and
produces the explicit version of (5.28).

The geometric construction which injects admissible embeddings into the
parent-function sum is deliberately outside this file.  Its output is the
single `hiterate` hypothesis of `volume_iteration_bound`; this keeps the
analytic bookkeeping independent of the concrete cluster-cover carrier.
-/

namespace Anderson4D

open scoped BigOperators

/-! ## Finite products with one distinguished root -/

private theorem prod_ite_root_eq_prod_erase
    {α R : Type*} [Fintype α] [DecidableEq α] [CommMonoid R]
    (root : α) (f : α → R) :
    (∏ v : α, if v = root then 1 else f v) =
      ∏ v ∈ (Finset.univ.erase root), f v := by
  classical
  rw [← Finset.prod_erase_mul (s := Finset.univ)
    (f := fun v => if v = root then 1 else f v)
    (Finset.mem_univ root)]
  simp only [if_pos, mul_one]
  apply Finset.prod_congr rfl
  intro v hv
  simp only [Finset.mem_erase] at hv
  simp [hv.1]

private theorem card_univ_erase
    {α : Type*} [Fintype α] [DecidableEq α] (root : α) :
    (Finset.univ.erase root).card = Fintype.card α - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ root), Finset.card_univ]

/-! ## The one-branch parent-function estimate, (5.23)--(5.25) -/

/-- Explicit absolute constant in the parent-function implementation of
paper (5.25).  The factor `3888` is the four-dimensional lattice-ball
constant from (5.23), and `16` absorbs `q^(q-1)` into `q!` for `q ≥ 2`. -/
def step5VolumeConstant : ℕ := 16 * step5LatticeConstant

private theorem pow_pred_le_sixteen_pow_pred_mul_factorial
    (q : ℕ) (hq : 2 ≤ q) :
    q ^ (q - 1) ≤ 16 ^ (q - 1) * q.factorial := by
  have hfour : 4 ^ q ≤ 16 ^ (q - 1) := by
    calc
      4 ^ q ≤ 4 ^ (2 * (q - 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ = 16 ^ (q - 1) := by
        rw [pow_mul]
        norm_num
  exact (pow_pred_le_four_pow_mul_factorial q).trans
    (Nat.mul_le_mul_right q.factorial hfour)

private theorem one_add_weight_prod_le_exp
    {α : Type*} [Fintype α] [DecidableEq α]
    (root : α) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∏ i ∈ Finset.univ.erase root, (1 + w i) ^ 4) ≤
      Real.exp (4 * ∑ i, w i) := by
  classical
  let s : Finset α := Finset.univ.erase root
  have hpoint (i : α) :
      (1 + w i) ^ 4 ≤ Real.exp (4 * w i) := by
    have h := pow_le_pow_left₀ (by linarith [hw i] : (0 : ℝ) ≤ 1 + w i)
      (by simpa [add_comm] using Real.add_one_le_exp (w i)) 4
    calc
      (1 + w i) ^ 4 ≤ Real.exp (w i) ^ 4 := h
      _ = Real.exp (4 * w i) := by
        rw [← Real.exp_nat_mul]
        norm_num
  calc
    (∏ i ∈ Finset.univ.erase root, (1 + w i) ^ 4)
        ≤ ∏ i ∈ s, Real.exp (4 * w i) := by
          apply Finset.prod_le_prod
          · intro i hi
            positivity
          · intro i hi
            exact hpoint i
    _ ≤ ∏ i : α, Real.exp (4 * w i) := by
      exact Finset.prod_le_prod_of_subset_of_one_le
        (Finset.erase_subset root Finset.univ)
        (fun i hi => (Real.exp_pos _).le)
        (fun i hi hnot =>
          Real.one_le_exp (mul_nonneg (by norm_num) (hw i)))
    _ = Real.exp (4 * ∑ i, w i) := by
      rw [← Real.exp_sum, ← Finset.mul_sum]

private theorem parent_power_le_factorial_exp
    {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hq : 2 ≤ Fintype.card α) :
    ((Fintype.card α : ℝ) + ∑ i, w i) ^ (Fintype.card α - 1) ≤
      (16 : ℝ) ^ (Fintype.card α - 1) *
        (Fintype.card α).factorial * Real.exp (∑ i, w i) := by
  let q := Fintype.card α
  let S : ℝ := ∑ i, w i
  have hqpos_nat : 0 < q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqpos_nat
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  have hsplit : (q : ℝ) + S = (q : ℝ) * (1 + S / q) := by
    field_simp
  have hone : 1 + S / (q : ℝ) ≤ Real.exp (S / q) :=
    by simpa [add_comm] using Real.add_one_le_exp (S / q)
  have hpow :
      (1 + S / (q : ℝ)) ^ (q - 1) ≤
        Real.exp (S / q) ^ (q - 1) :=
    pow_le_pow_left₀ (by positivity) hone _
  have hfrac : (((q - 1 : ℕ) : ℝ) / q) ≤ 1 := by
    rw [div_le_one hqpos]
    exact_mod_cast Nat.sub_le q 1
  have hexponent :
      ((q - 1 : ℕ) : ℝ) * (S / q) ≤ S := by
    calc
      ((q - 1 : ℕ) : ℝ) * (S / q) =
          (((q - 1 : ℕ) : ℝ) / q) * S := by ring
      _ ≤ 1 * S := mul_le_mul_of_nonneg_right hfrac hS
      _ = S := one_mul S
  have hexp :
      Real.exp (S / q) ^ (q - 1) ≤ Real.exp S := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hexponent
  have hfactorial_nat :
      q ^ (q - 1) ≤ 16 ^ (q - 1) * q.factorial :=
    pow_pred_le_sixteen_pow_pred_mul_factorial q hq
  have hfactorial :
      (q : ℝ) ^ (q - 1) ≤
        (16 : ℝ) ^ (q - 1) * q.factorial := by
    exact_mod_cast hfactorial_nat
  change ((q : ℝ) + S) ^ (q - 1) ≤
    (16 : ℝ) ^ (q - 1) * q.factorial * Real.exp S
  rw [hsplit, mul_pow]
  calc
    (q : ℝ) ^ (q - 1) * (1 + S / q) ^ (q - 1)
        ≤ (q : ℝ) ^ (q - 1) * Real.exp S :=
      mul_le_mul_of_nonneg_left (hpow.trans hexp) (by positivity)
    _ ≤ ((16 : ℝ) ^ (q - 1) * q.factorial) * Real.exp S :=
      mul_le_mul_of_nonneg_right hfactorial (Real.exp_pos _).le

/-- **Paper (5.23)--(5.25), parent-function form.**

At a branch with `q ≥ 2` children, `w i = tildeN_i / N_root`.
For every non-root child, `step5LatticeConstant * N_root^4` is the
four-dimensional ball count from (5.23), `(1 + w (p i))` is the chosen
parent-cluster factor, and `(1 + w i)^4` is the child-radius factor.
Summing over the enlarged space of all rooted parent functions gives the
right side of (5.25), with a fully explicit absolute constant. -/
theorem step5_parent_volume_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (root : α) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hq : 2 ≤ Fintype.card α) (Nroot : ℝ) :
    (∑ p : α → α,
        fullParentWeight root
          (fun i => 1 + w i)
          (fun i =>
            (step5LatticeConstant : ℝ) * Nroot ^ 4 * (1 + w i) ^ 4)
          p)
      ≤ (Fintype.card α).factorial *
          (step5VolumeConstant : ℝ) ^ (Fintype.card α - 1) *
          Nroot ^ (4 * (Fintype.card α - 1)) *
          Real.exp (6 * ∑ i, w i) := by
  classical
  let q := Fintype.card α
  let S : ℝ := ∑ i, w i
  let C : ℝ := step5LatticeConstant
  let P : ℝ := ∏ i ∈ Finset.univ.erase root, (1 + w i) ^ 4
  have hsum : (∑ i : α, (1 + w i)) = (q : ℝ) + S := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, q, S]
    ring
  have hcard := card_univ_erase root
  have hexact :
      (∑ p : α → α,
          fullParentWeight root
            (fun i => 1 + w i)
            (fun i => C * Nroot ^ 4 * (1 + w i) ^ 4) p) =
        ((q : ℝ) + S) ^ (q - 1) *
          (C * Nroot ^ 4) ^ (q - 1) * P := by
    rw [sum_fullParentWeight, hsum, prod_ite_root_eq_prod_erase]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    ring
  have hparent :
      ((q : ℝ) + S) ^ (q - 1) ≤
        (16 : ℝ) ^ (q - 1) * q.factorial * Real.exp S :=
    parent_power_le_factorial_exp w hw hq
  have hP : P ≤ Real.exp (4 * S) :=
    one_add_weight_prod_le_exp root w hw
  have hPnonneg : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro i hi
    positivity
  have hbase :
      ((q : ℝ) + S) ^ (q - 1) * P ≤
        (16 : ℝ) ^ (q - 1) * q.factorial *
          Real.exp (6 * S) := by
    calc
      ((q : ℝ) + S) ^ (q - 1) * P
          ≤ ((16 : ℝ) ^ (q - 1) * q.factorial * Real.exp S) *
              Real.exp (4 * S) :=
        mul_le_mul hparent hP hPnonneg (by positivity)
      _ = (16 : ℝ) ^ (q - 1) * q.factorial *
            Real.exp (5 * S) := by
        rw [show 5 * S = S + 4 * S by ring, Real.exp_add]
        ring
      _ ≤ (16 : ℝ) ^ (q - 1) * q.factorial *
            Real.exp (6 * S) := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.exp_le_exp.mpr (by
            have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
            linarith)
        · positivity
  rw [hexact]
  have hscale : 0 ≤ (C * Nroot ^ 4) ^ (q - 1) := by
    positivity
  calc
    ((q : ℝ) + S) ^ (q - 1) * (C * Nroot ^ 4) ^ (q - 1) * P =
        (C * Nroot ^ 4) ^ (q - 1) *
          (((q : ℝ) + S) ^ (q - 1) * P) := by ring
    _ ≤ (C * Nroot ^ 4) ^ (q - 1) *
          ((16 : ℝ) ^ (q - 1) * q.factorial *
            Real.exp (6 * S)) :=
      mul_le_mul_of_nonneg_left hbase hscale
    _ = (q.factorial : ℝ) *
          (step5VolumeConstant : ℝ) ^ (q - 1) *
          Nroot ^ (4 * (q - 1)) * Real.exp (6 * S) := by
      simp only [step5VolumeConstant, C, Nat.cast_mul, Nat.cast_ofNat]
      rw [mul_pow, pow_mul]
      ring

/-! ## Iteration over the Hepp tree, (5.27)--(5.29) -/

open PlaneTree

/-- Scale monomial occurring in (5.26)--(5.29). -/
noncomputable def branchScaleProduct
    {t : PlaneTree} (Nm : HeppMarking t) : ℝ :=
  ∏ v ∈ BranchNodes t,
    (scaleN Nm v : ℝ) ^ (4 * (childCount t v.1 - 1))

/-- Reordered exponent cost from (5.27).  Expanding every `tildeN` and
swapping the two finite sums turns the paper's double sum into this form. -/
noncomputable def ancestorRatioCost
    {t : PlaneTree} (Nm : HeppMarking t) : ℝ :=
  ∑ v ∈ BranchNodes t,
    (childCount t v.1 : ℝ) *
      ∑ u ∈ strictBranchAncestors v,
        (scaleN Nm v : ℝ) / scaleN Nm u

theorem ancestorRatioCost_nonneg
    {t : PlaneTree} (Nm : HeppMarking t) :
    0 ≤ ancestorRatioCost Nm := by
  unfold ancestorRatioCost
  positivity

/-- Paper (5.27), exposed under the name consumed by the iteration. -/
theorem ancestorRatioCost_le_two_mul_leafCount
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t) :
    ancestorRatioCost Nm ≤ 2 * (t.leafCount : ℝ) :=
  sum_childCount_mul_ancestor_ratio_le_two_mul_leafCount t ht Nm

theorem branchScaleProduct_nonneg
    {t : PlaneTree} (Nm : HeppMarking t) :
    0 ≤ branchScaleProduct Nm := by
  unfold branchScaleProduct
  positivity

/-- **Paper (5.23), (5.25), (5.27), and (5.28), combined.**

`hiterate` is exactly (5.26), obtained by recursively applying
`step5_parent_volume_bound`; its constant is therefore the explicit
`step5VolumeConstant`.  The conclusion discharges both remaining global
costs: (5.27) contributes `exp (12 r)`, and (5.21) contributes `256^r`
times the order-forgetting automorphism cardinality. -/
theorem volume_iteration_bound
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t)
    (J : ℝ)
    (hiterate :
      J ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (∏ v ∈ BranchNodes t, ((childCount t v.1).factorial : ℝ)) *
        branchScaleProduct Nm *
        Real.exp (6 * ancestorRatioCost Nm)) :
    J ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (256 : ℝ) ^ t.leafCount *
        Real.exp (12 * (t.leafCount : ℝ)) *
        (t.autCard : ℝ) * branchScaleProduct Nm := by
  have horderingNat := prod_branchNodes_factorial_le t ht
  have hordering :
      (∏ v ∈ BranchNodes t, ((childCount t v.1).factorial : ℝ)) ≤
        (256 : ℝ) ^ t.leafCount * t.autCard := by
    exact_mod_cast
      (horderingNat.trans_eq (by
        rw [pow_mul]
        norm_num))
  have hratio := ancestorRatioCost_le_two_mul_leafCount ht Nm
  have hexp :
      Real.exp (6 * ancestorRatioCost Nm) ≤
        Real.exp (12 * (t.leafCount : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hC : 0 ≤
      (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) := by positivity
  have hscale := branchScaleProduct_nonneg Nm
  calc
    J ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (∏ v ∈ BranchNodes t,
            ((childCount t v.1).factorial : ℝ)) *
          branchScaleProduct Nm *
          Real.exp (6 * ancestorRatioCost Nm) := hiterate
    _ ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          ((256 : ℝ) ^ t.leafCount * t.autCard) *
          branchScaleProduct Nm *
          Real.exp (12 * (t.leafCount : ℝ)) := by
      gcongr
    _ = (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (256 : ℝ) ^ t.leafCount *
          Real.exp (12 * (t.leafCount : ℝ)) *
          (t.autCard : ℝ) * branchScaleProduct Nm := by ring

/-- Gain-preserving version of `volume_iteration_bound`.  Taking
`gain = N_(f₀ ∨ f₁)⁻⁴` is precisely the Step 6 estimate (5.29): at the
lowest common ancestor one lattice-placement factor is replaced by `1`,
and all later scalar bookkeeping leaves that gain untouched. -/
theorem volume_iteration_bound_with_gain
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t)
    (J gain : ℝ) (hgain : 0 ≤ gain)
    (hiterate :
      J ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (∏ v ∈ BranchNodes t, ((childCount t v.1).factorial : ℝ)) *
        branchScaleProduct Nm *
        Real.exp (6 * ancestorRatioCost Nm) * gain) :
    J ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (256 : ℝ) ^ t.leafCount *
        Real.exp (12 * (t.leafCount : ℝ)) *
        (t.autCard : ℝ) * branchScaleProduct Nm * gain := by
  let K : ℝ :=
    (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
      (∏ v ∈ BranchNodes t, ((childCount t v.1).factorial : ℝ)) *
      branchScaleProduct Nm *
      Real.exp (6 * ancestorRatioCost Nm)
  have hK :
      K ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (256 : ℝ) ^ t.leafCount *
        Real.exp (12 * (t.leafCount : ℝ)) *
        (t.autCard : ℝ) * branchScaleProduct Nm :=
    volume_iteration_bound ht Nm K (le_refl K)
  calc
    J ≤ K * gain := hiterate
    _ ≤ ((step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
          (256 : ℝ) ^ t.leafCount *
          Real.exp (12 * (t.leafCount : ℝ)) *
          (t.autCard : ℝ) * branchScaleProduct Nm) * gain :=
      mul_le_mul_of_nonneg_right hK hgain

/-- The concrete nonnegative gain used in paper (5.29). -/
noncomputable def lcaScaleGain
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) : ℝ :=
  ((scaleN Nm v : ℝ) ^ 4)⁻¹

theorem lcaScaleGain_nonneg
    {t : PlaneTree} (Nm : HeppMarking t) (v : VPos t) :
    0 ≤ lcaScaleGain Nm v := by
  unfold lcaScaleGain
  positivity

/-- Paper (5.29) with the lowest-common-ancestor vertex supplied explicitly.
The geometric caller instantiates `v` with `f₀ ∨ f₁`. -/
theorem volume_iteration_pair_bound
    {t : PlaneTree} (ht : t.isValid = true) (Nm : HeppMarking t)
    (v : VPos t) (J01 : ℝ)
    (hiterate :
      J01 ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (∏ u ∈ BranchNodes t, ((childCount t u.1).factorial : ℝ)) *
        branchScaleProduct Nm *
        Real.exp (6 * ancestorRatioCost Nm) * lcaScaleGain Nm v) :
    J01 ≤ (step5VolumeConstant : ℝ) ^ (t.leafCount - 1) *
        (256 : ℝ) ^ t.leafCount *
        Real.exp (12 * (t.leafCount : ℝ)) *
        (t.autCard : ℝ) * branchScaleProduct Nm *
        lcaScaleGain Nm v :=
  volume_iteration_bound_with_gain ht Nm J01 (lcaScaleGain Nm v)
    (lcaScaleGain_nonneg Nm v) hiterate

end Anderson4D
