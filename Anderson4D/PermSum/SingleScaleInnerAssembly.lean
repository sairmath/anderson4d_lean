import Anderson4D.PermSum.SingleScaleBridge

/-!
# Honest finite assembly for the fixed-class inner sum

This file supplies the finite-sum layer between the local copy estimate in
`SingleScaleBridge` and the parity bookkeeping in paper (5.87)--(5.92).
The carrier is the paper's labeled-copy carrier

`Σ l : HeppLeaf t, Fin (leafMultiplicity mu l)`.

Conditioning on copies already used by a partial permutation is represented
by deleting a finite set from each `(N,X)` fiber.  The resulting one- and
two-variable sums are proved to be sub-sums of the unrestricted copy sums;
no independence or product-separability of the two edge kernels is assumed.

The last section isolates the purely numerical parity ledger: one parity can
lose at most twenty gains, the two parity exceptional sets have union of
cardinality at most forty, and geometric-mean interpolation changes the gain
exponent from `1/8` to `1/16`.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-! ## Labeled copies and conditioned local choices -/

/-- The distinct copies of all leaves.  This is the codomain of a labeled
arrangement in the factorial ledger. -/
abbrev HeppLabeledCopy {t : PlaneTree} (mu : Multiplicities t) :=
  Σ l : HeppLeaf t, Fin (leafMultiplicity mu l)

/-- The lattice point carried by a labeled copy. -/
def labeledCopyPoint {t : PlaneTree} {mu : Multiplicities t}
    (z : HeppLeaf t → Fin 4 → ℤ) (c : HeppLabeledCopy mu) :
    Fin 4 → ℤ :=
  z c.1

/-- All labeled copies whose leaf lies in the fixed `(N,X)` fiber `a`. -/
def labeledCopiesAtNX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (a : NXClass) :
    Finset (HeppLabeledCopy mu) :=
  Finset.univ.filter fun c => singleScaleSigma1 Nm mu c.1 = a

/-- Copies in a fixed fiber which have not occurred in the already exposed
part of a labeled permutation. -/
def conditionedCopiesAtNX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (used : Finset (HeppLabeledCopy mu)) (a : NXClass) :
    Finset (HeppLabeledCopy mu) :=
  labeledCopiesAtNX Nm mu a \ used

theorem conditionedCopiesAtNX_subset {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (used : Finset (HeppLabeledCopy mu)) (a : NXClass) :
    conditionedCopiesAtNX Nm mu used a ⊆ labeledCopiesAtNX Nm mu a :=
  Finset.sdiff_subset

theorem mem_labeledCopiesAtNX_iff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) (c : HeppLabeledCopy mu) :
    c ∈ labeledCopiesAtNX Nm mu a ↔
      singleScaleSigma1 Nm mu c.1 = a := by
  simp [labeledCopiesAtNX]

theorem mem_conditionedCopiesAtNX_iff {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (used : Finset (HeppLabeledCopy mu)) (a : NXClass)
    (c : HeppLabeledCopy mu) :
    c ∈ conditionedCopiesAtNX Nm mu used a ↔
      singleScaleSigma1 Nm mu c.1 = a ∧ c ∉ used := by
  simp [conditionedCopiesAtNX, labeledCopiesAtNX]

/-! ### Link to the factorial-ledger arrangement carrier -/

/-- Copies occupying a finite set of positions in a labeled arrangement. -/
def arrangementUsedCopies {t : PlaneTree} {mu : Multiplicities t} {M : ℕ}
    (σ : Fin M ≃ HeppLabeledCopy mu) (J : Finset (Fin M)) :
    Finset (HeppLabeledCopy mu) :=
  J.image σ

theorem arrangement_copy_not_mem_used {t : PlaneTree}
    {mu : Multiplicities t} {M : ℕ}
    (σ : Fin M ≃ HeppLabeledCopy mu) (J : Finset (Fin M))
    {j : Fin M} (hj : j ∉ J) :
    σ j ∉ arrangementUsedCopies σ J := by
  intro hmem
  obtain ⟨i, hi, his⟩ := Finset.mem_image.mp hmem
  have hij : i = j := σ.injective his
  exact hj (hij ▸ hi)

/-- A position not yet exposed by the backward summation is one of the
conditioned local choices in its fixed `(N,X)` class. -/
theorem arrangement_copy_mem_conditionedNX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {M : ℕ}
    (σ : Fin M ≃ HeppLabeledCopy mu) (J : Finset (Fin M))
    {j : Fin M} (hj : j ∉ J) (a : NXClass)
    (ha : singleScaleSigma1 Nm mu (σ j).1 = a) :
    σ j ∈ conditionedCopiesAtNX Nm mu
      (arrangementUsedCopies σ J) a := by
  rw [mem_conditionedCopiesAtNX_iff]
  exact ⟨ha, arrangement_copy_not_mem_used σ J hj⟩

/-- The induced leaf word of every labeled arrangement is an admissible
word in the factorial ledger.  This records that the local carrier above
does not introduce a different notion of "valid word". -/
theorem arrangement_inducedWord_valid {t : PlaneTree}
    (mu : Multiplicities t) {M : ℕ}
    (σ : Fin M ≃ HeppLabeledCopy mu) :
    inducedWord (leafMultiplicity mu) σ ∈
      validWords (M := M) (leafMultiplicity mu) :=
  inducedWord_mem_validWords (leafMultiplicity mu) σ

/-- Two distinct, not-yet-exposed positions give a legal conditioned pair:
the second choice sees both the previously used positions and the first new
copy.  This is the exact local selection made in a labeled permutation. -/
theorem arrangement_pair_mem_conditionedNX {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {M : ℕ}
    (σ : Fin M ≃ HeppLabeledCopy mu) (J : Finset (Fin M))
    {j k : Fin M} (hj : j ∉ J) (hk : k ∉ J) (hjk : j ≠ k)
    (a b : NXClass)
    (ha : singleScaleSigma1 Nm mu (σ j).1 = a)
    (hb : singleScaleSigma1 Nm mu (σ k).1 = b) :
    σ j ∈ conditionedCopiesAtNX Nm mu
        (arrangementUsedCopies σ J) a ∧
      σ k ∈ conditionedCopiesAtNX Nm mu
        (insert (σ j) (arrangementUsedCopies σ J)) b := by
  constructor
  · exact arrangement_copy_mem_conditionedNX Nm mu σ J hj a ha
  · rw [mem_conditionedCopiesAtNX_iff]
    refine ⟨hb, ?_⟩
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => hjk (σ.injective h.symm),
      arrangement_copy_not_mem_used σ J hk⟩

/-- A sum over all labeled copies in a fiber is exactly the multiplicity
weighted leaf sum used by `nxCopyWeightedSum`. -/
theorem sum_labeledCopiesAtNX_eq_nxCopyWeightedSum {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (a : NXClass)
    (f : (Fin 4 → ℤ) → ℝ) :
    (∑ c ∈ labeledCopiesAtNX Nm mu a, f (labeledCopyPoint z c)) =
      nxCopyWeightedSum Nm mu z a f := by
  classical
  unfold labeledCopiesAtNX labeledCopyPoint nxCopyWeightedSum leavesAtNX
  rw [Finset.sum_filter, Fintype.sum_sigma]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l _hl
  by_cases hla : singleScaleSigma1 Nm mu l = a
  · simp [hla]
  · simp [hla]

/-- Dropping already-used copies only decreases a nonnegative local sum. -/
theorem sum_conditionedCopiesAtNX_le_nxCopyWeightedSum {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (used : Finset (HeppLabeledCopy mu)) (a : NXClass)
    (f : (Fin 4 → ℤ) → ℝ)
    (hf : ∀ c ∈ labeledCopiesAtNX Nm mu a,
      0 ≤ f (labeledCopyPoint z c)) :
    (∑ c ∈ conditionedCopiesAtNX Nm mu used a,
        f (labeledCopyPoint z c)) ≤
      nxCopyWeightedSum Nm mu z a f := by
  rw [← sum_labeledCopiesAtNX_eq_nxCopyWeightedSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (conditionedCopiesAtNX_subset Nm mu used a)
    (fun c hc _ => hf c hc)

/-! ## A conditioned two-variable block -/

/-- The honest conditional local sum for two consecutive positions of a
labeled permutation.  The second copy is selected after inserting the first
one into `used`, so the two positions can never reuse the same labeled copy.
The first copy may nevertheless have the same underlying leaf as the second
when the incoming edge is skipped, exactly as in Proposition 5.10. -/
noncomputable def conditionedNXPairSum {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (used : Finset (HeppLabeledCopy mu))
    (skipA skipB : Bool) (u : Fin 4 → ℤ) : ℝ :=
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  ∑ x ∈ conditionedCopiesAtNX Nm mu used a,
    ca.lambda R skipA u (labeledCopyPoint z x) *
      ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) b,
        strongLambda ca cb R skipB
          (labeledCopyPoint z x) (labeledCopyPoint z y)

private theorem conditionedNXPairSum_nonneg {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (used : Finset (HeppLabeledCopy mu))
    (skipA skipB : Bool) (u : Fin 4 → ℤ) :
    0 ≤ conditionedNXPairSum ht hroot Nm mu z hz R ha hb
      used skipA skipB u := by
  unfold conditionedNXPairSum
  apply Finset.sum_nonneg
  intro x _hx
  apply mul_nonneg
  · unfold lambda
    split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro y _hy
    unfold strongLambda
    split_ifs <;> positivity

/-- Forgetting both the used-copy condition and the inequality between the
two labeled copies enlarges the conditional block to the unrestricted
copy-level sum from `SingleScaleBridge`. -/
theorem conditionedNXPairSum_le_nxCoupledCopyPairSum {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (used : Finset (HeppLabeledCopy mu))
    (skipA skipB : Bool) (u : Fin 4 → ℤ) :
    conditionedNXPairSum ht hroot Nm mu z hz R ha hb
        used skipA skipB u ≤
      nxCoupledCopyPairSum ht hroot Nm mu z hz R
        ha hb skipA skipB u := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  have hinner (x : HeppLabeledCopy mu)
      (_hx : x ∈ labeledCopiesAtNX Nm mu a) :
      (∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) b,
          strongLambda ca cb R skipB
            (labeledCopyPoint z x) (labeledCopyPoint z y)) ≤
        nxCopyWeightedSum Nm mu z b fun y =>
          strongLambda ca cb R skipB (labeledCopyPoint z x) y := by
    exact sum_conditionedCopiesAtNX_le_nxCopyWeightedSum
      Nm mu z (insert x used) b
      (fun y => strongLambda ca cb R skipB (labeledCopyPoint z x) y)
      (fun y _hy => by
        unfold strongLambda
        split_ifs <;> positivity)
  unfold conditionedNXPairSum nxCoupledCopyPairSum
  dsimp only
  calc
    (∑ x ∈ conditionedCopiesAtNX Nm mu used a,
        ca.lambda R skipA u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) b,
            strongLambda ca cb R skipB
              (labeledCopyPoint z x) (labeledCopyPoint z y)) ≤
      ∑ x ∈ conditionedCopiesAtNX Nm mu used a,
        ca.lambda R skipA u (labeledCopyPoint z x) *
          nxCopyWeightedSum Nm mu z b fun y =>
            strongLambda ca cb R skipB (labeledCopyPoint z x) y := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (hinner x (conditionedCopiesAtNX_subset Nm mu used a hx))
        (by
          unfold lambda
          split_ifs <;> positivity)
    _ ≤ nxCopyWeightedSum Nm mu z a (fun x =>
        ca.lambda R skipA u x *
          nxCopyWeightedSum Nm mu z b fun y =>
            strongLambda ca cb R skipB x y) := by
      exact sum_conditionedCopiesAtNX_le_nxCopyWeightedSum
        Nm mu z used a
        (fun x => ca.lambda R skipA u x *
          nxCopyWeightedSum Nm mu z b fun y =>
            strongLambda ca cb R skipB x y)
        (fun x _hx => mul_nonneg
          (by
            unfold lambda
            split_ifs <;> positivity)
          (by
            unfold nxCopyWeightedSum
            apply Finset.sum_nonneg
            intro l _hl
            exact mul_nonneg (by positivity) (by
              unfold strongLambda
              split_ifs <;> positivity)))

/-! ## A conditioned one-variable block -/

/-- The honest conditional local sum for a position that cannot be paired
in the chosen parity. -/
noncomputable def conditionedNXSingleSum {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (used : Finset (HeppLabeledCopy mu))
    (skipped : Bool) (u : Fin 4 → ℤ) : ℝ :=
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  ∑ x ∈ conditionedCopiesAtNX Nm mu used a,
    ca.lambda R skipped u (labeledCopyPoint z x)

/-- The exact dyadic right-hand factor in the one-variable estimate (5.92),
before a universal comparison constant. -/
noncomputable def paperDyadicSingleRoughTarget {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (a : NXClass) (skipped : Bool) : ℝ :=
  (a.2 : ℝ) * paperDyadicY Nm mu a *
    if skipped then R⁻¹ ^ 2 else (a.1 : ℝ)⁻¹ ^ 2

theorem paperDyadicSingleRoughTarget_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (a : NXClass) (skipped : Bool) :
    0 ≤ paperDyadicSingleRoughTarget Nm mu R a skipped := by
  unfold paperDyadicSingleRoughTarget
  have hY : 0 ≤ paperDyadicY Nm mu a := by
    unfold paperDyadicY singleScaleSigma2 dyadicFloor
    positivity
  split_ifs <;> exact mul_nonneg
    (mul_nonneg (by positivity) hY) (sq_nonneg _)

/-- Copy-level, conditioned version of the one-variable rough estimate
(5.92).  The explicit constant `16` audits the two copies-to-points loss,
the dyadic cardinality loss, and the use of the separation scale `N/2`. -/
theorem conditionedNXSingleSum_le_sixteen_mul_target {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a : NXClass} (ha : a ∈ nxCarrier Nm mu)
    (used : Finset (HeppLabeledCopy mu))
    (skipped : Bool) (u : Fin 4 → ℤ) :
    conditionedNXSingleSum ht hroot Nm mu z hz R ha used skipped u ≤
      16 * paperDyadicSingleRoughTarget Nm mu R a skipped := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  have hcond :
      conditionedNXSingleSum ht hroot Nm mu z hz R ha used skipped u ≤
        nxCopyWeightedSum Nm mu z a (fun x =>
          ca.lambda R skipped u x) := by
    exact sum_conditionedCopiesAtNX_le_nxCopyWeightedSum
      Nm mu z used a (fun x => ca.lambda R skipped u x)
      (fun x _hx => by
        unfold lambda
        split_ifs <;> positivity)
  have hcopy :
      nxCopyWeightedSum Nm mu z a (fun x => ca.lambda R skipped u x) ≤
        2 * ca.singleInner R skipped u := by
    have h :=
      nxCopyWeightedSum_le_two_mul_pointWeightedSum
        Nm mu z hz ha (fun x => ca.lambda R skipped u x)
        (fun x _hx => by
          unfold lambda
          split_ifs <;> positivity)
    simpa [singleInner, nxPointWeightedSum, ca] using h
  have hsingle := singleInner_le_5_92 ca R skipped u
  have hY :
      ca.Y ≤ 2 * paperDyadicY Nm mu a := by
    have hcardNat :
        ca.points.card ≤ 2 * (singleScaleSigma2 Nm mu a).2 :=
      Nat.le_of_lt
        (nxClassCluster_card_bounds ht hroot Nm mu z hz ha).2
    unfold Y paperDyadicY
    exact_mod_cast hcardNat
  have hX : ca.X = (a.2 : ℝ) := rfl
  have hN :
      ca.N⁻¹ ^ 2 = 4 * (a.1 : ℝ)⁻¹ ^ 2 := by
    rw [nxClassCluster_N ht hroot Nm mu z hz a ha]
    have haN : (a.1 : ℝ) ≠ 0 := by
      exact_mod_cast (by
        have := two_le_nxClass_scale ht hroot Nm mu ha
        omega : a.1 ≠ 0)
    field_simp [haN]
    ring
  calc
    conditionedNXSingleSum ht hroot Nm mu z hz R ha used skipped u ≤
        nxCopyWeightedSum Nm mu z a (fun x =>
          ca.lambda R skipped u x) := hcond
    _ ≤ 2 * ca.singleInner R skipped u := hcopy
    _ ≤ 2 * (ca.X * ca.Y *
        (if skipped then R⁻¹ ^ 2 else ca.N⁻¹ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsingle (by norm_num)
    _ ≤ 16 * paperDyadicSingleRoughTarget Nm mu R a skipped := by
      cases skipped with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [hX, hN]
          unfold paperDyadicSingleRoughTarget
          simp only [Bool.false_eq_true, if_false]
          have hfactor :
              0 ≤ (a.2 : ℝ) * (a.1 : ℝ)⁻¹ ^ 2 := by
            positivity
          have hscaled :
              (a.2 : ℝ) * ca.Y * (a.1 : ℝ)⁻¹ ^ 2 ≤
                (a.2 : ℝ) * (2 * paperDyadicY Nm mu a) *
                  (a.1 : ℝ)⁻¹ ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hY (by positivity))
              (sq_nonneg _)
          calc
            2 * ((a.2 : ℝ) * ca.Y *
                (4 * (a.1 : ℝ)⁻¹ ^ 2)) =
              2 * (((a.2 : ℝ) * ca.Y *
                (a.1 : ℝ)⁻¹ ^ 2) * 4) := by ring
            _ ≤
              2 * (((a.2 : ℝ) *
                (2 * paperDyadicY Nm mu a) *
                  (a.1 : ℝ)⁻¹ ^ 2) * 4) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hscaled (by norm_num))
                  (by norm_num)
            _ = 16 * ((a.2 : ℝ) * paperDyadicY Nm mu a *
                (a.1 : ℝ)⁻¹ ^ 2) := by ring
      | true =>
          simp only [if_true]
          unfold paperDyadicSingleRoughTarget
          simp only [if_true, hX]
          have hfactor :
              0 ≤ (a.2 : ℝ) * R⁻¹ ^ 2 := by
            positivity
          have hscaled :
              (a.2 : ℝ) * ca.Y * R⁻¹ ^ 2 ≤
                (a.2 : ℝ) * (2 * paperDyadicY Nm mu a) *
                  R⁻¹ ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hY (by positivity))
              (sq_nonneg _)
          calc
            2 * ((a.2 : ℝ) * ca.Y * R⁻¹ ^ 2) ≤
                2 * ((a.2 : ℝ) *
                  (2 * paperDyadicY Nm mu a) * R⁻¹ ^ 2) :=
              mul_le_mul_of_nonneg_left hscaled (by norm_num)
            _ ≤ 16 * ((a.2 : ℝ) *
                  paperDyadicY Nm mu a * R⁻¹ ^ 2) := by
              have htarget :
                  0 ≤ (a.2 : ℝ) *
                    paperDyadicY Nm mu a * R⁻¹ ^ 2 := by
                exact mul_nonneg
                  (mul_nonneg (by positivity) (by
                    unfold paperDyadicY singleScaleSigma2 dyadicFloor
                    positivity))
                  (sq_nonneg _)
              nlinarith

/-! ## The rough two-variable block (5.90) -/

/-- The dyadic target in (5.90) is the product of its two one-variable
(5.92) factors. -/
noncomputable def paperDyadicPairRoughTarget {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (R : ℝ)
    (a b : NXClass) (skipA skipB : Bool) : ℝ :=
  paperDyadicSingleRoughTarget Nm mu R a skipA *
    paperDyadicSingleRoughTarget Nm mu R b skipB

theorem paperDyadicPairRoughTarget_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (R : ℝ)
    (a b : NXClass) (skipA skipB : Bool) :
    0 ≤ paperDyadicPairRoughTarget Nm mu R a b skipA skipB :=
  mul_nonneg
    (paperDyadicSingleRoughTarget_nonneg Nm mu R a skipA)
    (paperDyadicSingleRoughTarget_nonneg Nm mu R b skipB)

private theorem strongLambda_le_lambda (a b : XYCluster) (R : ℝ)
    (skipped : Bool) (x y : Fin 4 → ℤ) :
    strongLambda a b R skipped x y ≤ b.lambda R skipped x y := by
  cases skipped with
  | true =>
      simp [strongLambda, lambda]
  | false =>
      simp only [strongLambda, lambda, Bool.false_eq_true, if_false]
      by_cases hstrong : max a.N b.N ≤ znorm (x - y)
      · rw [if_pos hstrong,
          if_pos ((le_max_right a.N b.N).trans hstrong)]
      · rw [if_neg hstrong]
        positivity

/-- Conditioned copy-level form of the rough pair estimate (5.90).  It is
obtained by two honest one-variable eliminations, hence the audited constant
`16² = 256`. -/
theorem conditionedNXPairSum_le_256_mul_roughTarget {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (used : Finset (HeppLabeledCopy mu))
    (skipA skipB : Bool) (u : Fin 4 → ℤ) :
    conditionedNXPairSum ht hroot Nm mu z hz R ha hb
        used skipA skipB u ≤
      256 * paperDyadicPairRoughTarget Nm mu R
        a b skipA skipB := by
  let ca := nxClassCluster ht hroot Nm mu z hz a ha
  let cb := nxClassCluster ht hroot Nm mu z hz b hb
  let targetA := paperDyadicSingleRoughTarget Nm mu R a skipA
  let targetB := paperDyadicSingleRoughTarget Nm mu R b skipB
  have hinner (x : HeppLabeledCopy mu) :
      (∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) b,
          strongLambda ca cb R skipB
            (labeledCopyPoint z x) (labeledCopyPoint z y)) ≤
        16 * targetB := by
    calc
      (∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) b,
          strongLambda ca cb R skipB
            (labeledCopyPoint z x) (labeledCopyPoint z y)) ≤
        ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) b,
          cb.lambda R skipB
            (labeledCopyPoint z x) (labeledCopyPoint z y) := by
          exact Finset.sum_le_sum fun y _hy =>
            strongLambda_le_lambda ca cb R skipB
              (labeledCopyPoint z x) (labeledCopyPoint z y)
      _ = conditionedNXSingleSum ht hroot Nm mu z hz R hb
            (insert x used) skipB (labeledCopyPoint z x) := by
          rfl
      _ ≤ 16 * targetB := by
          exact conditionedNXSingleSum_le_sixteen_mul_target
            ht hroot Nm mu z hz R hb
            (insert x used) skipB (labeledCopyPoint z x)
  have houter :
      conditionedNXSingleSum ht hroot Nm mu z hz R ha
          used skipA u ≤
        16 * targetA :=
    conditionedNXSingleSum_le_sixteen_mul_target
      ht hroot Nm mu z hz R ha used skipA u
  have htargetB : 0 ≤ targetB :=
    paperDyadicSingleRoughTarget_nonneg Nm mu R b skipB
  unfold conditionedNXPairSum
  dsimp only
  calc
    (∑ x ∈ conditionedCopiesAtNX Nm mu used a,
        ca.lambda R skipA u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) b,
            strongLambda ca cb R skipB
              (labeledCopyPoint z x) (labeledCopyPoint z y)) ≤
      ∑ x ∈ conditionedCopiesAtNX Nm mu used a,
        ca.lambda R skipA u (labeledCopyPoint z x) *
          (16 * targetB) := by
      exact Finset.sum_le_sum fun x _hx =>
        mul_le_mul_of_nonneg_left (hinner x) (by
          unfold lambda
          split_ifs <;> positivity)
    _ = conditionedNXSingleSum ht hroot Nm mu z hz R ha
          used skipA u * (16 * targetB) := by
      unfold conditionedNXSingleSum
      dsimp only
      rw [Finset.sum_mul]
    _ ≤ (16 * targetA) * (16 * targetB) :=
      mul_le_mul_of_nonneg_right houter
        (mul_nonneg (by norm_num) htargetB)
    _ = 256 * paperDyadicPairRoughTarget Nm mu R
          a b skipA skipB := by
      unfold paperDyadicPairRoughTarget targetA targetB
      ring

/-! ## Backward elimination of a whole parity -/

/-- Two consecutive positions eliminated together.  `skipLeft` refers to
the edge from the already fixed point into `left`; `skipRight` refers to the
edge between the two positions. -/
structure NXPairBlock {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) where
  left : ActiveNXClass Nm mu
  right : ActiveNXClass Nm mu
  skipLeft : Bool
  skipRight : Bool

/-- The exact paper dyadic target attached to a paired elimination block. -/
noncomputable def nxPairBlockTarget {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (p : NXPairBlock Nm mu) : ℝ :=
  paperDyadicPairTarget Nm mu p.left.1 p.right.1
    p.skipLeft p.skipRight

theorem nxPairBlockTarget_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (p : NXPairBlock Nm mu) :
    0 ≤ nxPairBlockTarget Nm mu p :=
  paperDyadicPairTarget_nonneg Nm mu _ _ _ _

/-- The actual nested finite sum obtained by eliminating consecutive pairs
from left to right.  `used` is threaded through the recursion, so choices in
different blocks are also distinct.  The endpoint of a block becomes the
fixed preceding point for the next block; this is the finite Fubini step
behind the paper's instruction to sum in decreasing position order. -/
noncomputable def conditionedNXPairChainSum {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) :
    List (NXPairBlock Nm mu) →
      Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) → ℝ
  | [], _used, _u => 1
  | p :: ps, used, u =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXPairChainSum ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y)

theorem conditionedNXPairChainSum_nonneg {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (ps : List (NXPairBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    0 ≤ conditionedNXPairChainSum ht hroot Nm mu z hz R ps used u := by
  induction ps generalizing used u with
  | nil =>
      simp [conditionedNXPairChainSum]
  | cons p ps ih =>
      simp only [conditionedNXPairChainSum]
      apply Finset.sum_nonneg
      intro x _hx
      apply mul_nonneg
      · unfold lambda
        split_ifs <;> positivity
      · apply Finset.sum_nonneg
        intro y _hy
        exact mul_nonneg
          (by
            unfold strongLambda
            split_ifs <;> positivity)
          (ih _ _)

/-- If the remaining chain is uniformly bounded by `K`, eliminating the
current conditioned pair costs its honest local conditional sum times `K`.
This is the explicit finite Fubini/monotonicity lemma used in the induction
below. -/
private theorem conditionedNXPairChainSum_cons_le {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (p : NXPairBlock Nm mu) (ps : List (NXPairBlock Nm mu))
    (K : ℝ)
    (htail : ∀ (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ),
      conditionedNXPairChainSum ht hroot Nm mu z hz R ps used u ≤ K)
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    conditionedNXPairChainSum ht hroot Nm mu z hz R (p :: ps) used u ≤
      conditionedNXPairSum ht hroot Nm mu z hz R
        p.left.2 p.right.2 used p.skipLeft p.skipRight u * K := by
  let ca :=
    nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
  let cb :=
    nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
  simp only [conditionedNXPairChainSum]
  unfold conditionedNXPairSum
  dsimp only
  calc
    (∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXPairChainSum ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y)) ≤
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) * K := by
      apply Finset.sum_le_sum
      intro x _hx
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro y _hy
        exact mul_le_mul_of_nonneg_left
          (htail (insert y (insert x used)) (labeledCopyPoint z y))
          (by
            unfold strongLambda
            split_ifs <;> positivity)
      · unfold lambda
        split_ifs <;> positivity
    _ = (∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
              (labeledCopyPoint z x) (labeledCopyPoint z y)) * K := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← Finset.sum_mul]
      ring

/-- **One-parity fixed-class assembly.**  The sum is over honest distinct
labeled-copy choices and is nested in the elimination order.  Every local
bound is the uniform copy-level (5.91) theorem; induction, rather than an
assumed factorization, yields the product of dyadic targets. -/
theorem conditionedNXPairChainSum_le_targetProduct :
    ∃ C : ℝ, 0 < C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (ps : List (NXPairBlock Nm mu))
          (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ),
          conditionedNXPairChainSum ht hroot Nm mu z hz (R : ℝ)
              ps used u ≤
            (ps.map fun p => C * nxPairBlockTarget Nm mu p).prod := by
  obtain ⟨C, hC, hlocal⟩ :=
    nxCoupledCopyPairSum_le_paperDyadicPairTarget
  refine ⟨C, hC, ?_⟩
  intro t ht hroot Nm mu z hz R hR ps
  induction ps with
  | nil =>
      intro used u
      simp [conditionedNXPairChainSum]
  | cons p ps ih =>
      intro used u
      let K : ℝ :=
        (ps.map fun q => C * nxPairBlockTarget Nm mu q).prod
      have hK : 0 ≤ K := by
        unfold K
        apply List.prod_nonneg
        intro x hx
        obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp hx
        exact mul_nonneg hC.le (nxPairBlockTarget_nonneg Nm mu q)
      have hstep :
          conditionedNXPairChainSum ht hroot Nm mu z hz (R : ℝ)
              (p :: ps) used u ≤
            conditionedNXPairSum ht hroot Nm mu z hz (R : ℝ)
                p.left.2 p.right.2 used p.skipLeft p.skipRight u * K :=
        conditionedNXPairChainSum_cons_le
          ht hroot Nm mu z hz (R : ℝ) p ps K
          (fun used' u' => ih used' u') used u
      have hcond :
          conditionedNXPairSum ht hroot Nm mu z hz (R : ℝ)
              p.left.2 p.right.2 used p.skipLeft p.skipRight u ≤
            nxCoupledCopyPairSum ht hroot Nm mu z hz (R : ℝ)
              p.left.2 p.right.2 p.skipLeft p.skipRight u :=
        conditionedNXPairSum_le_nxCoupledCopyPairSum
          ht hroot Nm mu z hz (R : ℝ)
          p.left.2 p.right.2 used p.skipLeft p.skipRight u
      have hpair :
          nxCoupledCopyPairSum ht hroot Nm mu z hz (R : ℝ)
              p.left.2 p.right.2 p.skipLeft p.skipRight u ≤
            C * nxPairBlockTarget Nm mu p := by
        simpa [nxPairBlockTarget] using
          hlocal ht hroot Nm mu z hz R hR
            p.left.2 p.right.2 p.skipLeft p.skipRight u
      calc
        conditionedNXPairChainSum ht hroot Nm mu z hz (R : ℝ)
            (p :: ps) used u ≤
          conditionedNXPairSum ht hroot Nm mu z hz (R : ℝ)
              p.left.2 p.right.2 used p.skipLeft p.skipRight u * K := hstep
        _ ≤ (C * nxPairBlockTarget Nm mu p) * K :=
          mul_le_mul_of_nonneg_right (hcond.trans hpair) hK
        _ = ((p :: ps).map fun q =>
            C * nxPairBlockTarget Nm mu q).prod := by
          simp [K]

/-! ### One- and two-variable blocks in the same parity -/

/-- The elimination schedule for one parity.  Interior positions occur in
`pair` blocks; parity endpoints and the split around the minimal-scale
position occur in `single` blocks. -/
inductive NXParityBlock {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
  | single (a : ActiveNXClass Nm mu) (skipped : Bool)
  | pair (p : NXPairBlock Nm mu)
  | roughPair (p : NXPairBlock Nm mu)

/-- Local target for a mixed one-parity schedule. -/
noncomputable def nxParityBlockTarget {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (R : ℝ) :
    NXParityBlock Nm mu → ℝ
  | .single a skipped =>
      paperDyadicSingleRoughTarget Nm mu R a.1 skipped
  | .pair p => nxPairBlockTarget Nm mu p
  | .roughPair p =>
      paperDyadicPairRoughTarget Nm mu R p.left.1 p.right.1
        p.skipLeft p.skipRight

theorem nxParityBlockTarget_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) (R : ℝ)
    (p : NXParityBlock Nm mu) :
    0 ≤ nxParityBlockTarget Nm mu R p := by
  cases p with
  | single a skipped =>
      exact paperDyadicSingleRoughTarget_nonneg Nm mu R a.1 skipped
  | pair p =>
      exact nxPairBlockTarget_nonneg Nm mu p
  | roughPair p =>
      exact paperDyadicPairRoughTarget_nonneg Nm mu R
        p.left.1 p.right.1 p.skipLeft p.skipRight

/-- Honest nested sum for an arbitrary schedule of single and paired
eliminations.  As above, the used-copy set is threaded through every choice. -/
noncomputable def conditionedNXParityChainSum {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) :
    List (NXParityBlock Nm mu) →
      Finset (HeppLabeledCopy mu) → (Fin 4 → ℤ) → ℝ
  | [], _used, _u => 1
  | .single a skipped :: ps, used, u =>
      let ca := nxClassCluster ht hroot Nm mu z hz a.1 a.2
      ∑ x ∈ conditionedCopiesAtNX Nm mu used a.1,
        ca.lambda R skipped u (labeledCopyPoint z x) *
          conditionedNXParityChainSum ht hroot Nm mu z hz R ps
            (insert x used) (labeledCopyPoint z x)
  | .pair p :: ps, used, u =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXParityChainSum ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y)
  | .roughPair p :: ps, used, u =>
      let ca :=
        nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
      let cb :=
        nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXParityChainSum ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y)

theorem conditionedNXParityChainSum_nonneg {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (ps : List (NXParityBlock Nm mu))
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    0 ≤ conditionedNXParityChainSum ht hroot Nm mu z hz R ps used u := by
  induction ps generalizing used u with
  | nil =>
      simp [conditionedNXParityChainSum]
  | cons p ps ih =>
      cases p with
      | single a skipped =>
          simp only [conditionedNXParityChainSum]
          apply Finset.sum_nonneg
          intro x _hx
          exact mul_nonneg
            (by
              unfold lambda
              split_ifs <;> positivity)
            (ih _ _)
      | pair p =>
          simp only [conditionedNXParityChainSum]
          apply Finset.sum_nonneg
          intro x _hx
          apply mul_nonneg
          · unfold lambda
            split_ifs <;> positivity
          · apply Finset.sum_nonneg
            intro y _hy
            exact mul_nonneg
              (by
                unfold strongLambda
                split_ifs <;> positivity)
              (ih _ _)
      | roughPair p =>
          simp only [conditionedNXParityChainSum]
          apply Finset.sum_nonneg
          intro x _hx
          apply mul_nonneg
          · unfold lambda
            split_ifs <;> positivity
          · apply Finset.sum_nonneg
            intro y _hy
            exact mul_nonneg
              (by
                unfold strongLambda
                split_ifs <;> positivity)
              (ih _ _)

private theorem conditionedNXParityChainSum_single_cons_le
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (a : ActiveNXClass Nm mu) (skipped : Bool)
    (ps : List (NXParityBlock Nm mu)) (K : ℝ)
    (htail : ∀ (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ),
      conditionedNXParityChainSum ht hroot Nm mu z hz R ps used u ≤ K)
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    conditionedNXParityChainSum ht hroot Nm mu z hz R
        (.single a skipped :: ps) used u ≤
      conditionedNXSingleSum ht hroot Nm mu z hz R a.2
        used skipped u * K := by
  let ca := nxClassCluster ht hroot Nm mu z hz a.1 a.2
  simp only [conditionedNXParityChainSum]
  unfold conditionedNXSingleSum
  dsimp only
  calc
    (∑ x ∈ conditionedCopiesAtNX Nm mu used a.1,
        ca.lambda R skipped u (labeledCopyPoint z x) *
          conditionedNXParityChainSum ht hroot Nm mu z hz R ps
            (insert x used) (labeledCopyPoint z x)) ≤
      ∑ x ∈ conditionedCopiesAtNX Nm mu used a.1,
        ca.lambda R skipped u (labeledCopyPoint z x) * K := by
      apply Finset.sum_le_sum
      intro x _hx
      exact mul_le_mul_of_nonneg_left
        (htail (insert x used) (labeledCopyPoint z x))
        (by
          unfold lambda
          split_ifs <;> positivity)
    _ = (∑ x ∈ conditionedCopiesAtNX Nm mu used a.1,
        ca.lambda R skipped u (labeledCopyPoint z x)) * K := by
      rw [Finset.sum_mul]

private theorem conditionedNXParityChainSum_pair_cons_le
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (p : NXPairBlock Nm mu)
    (ps : List (NXParityBlock Nm mu)) (K : ℝ)
    (htail : ∀ (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ),
      conditionedNXParityChainSum ht hroot Nm mu z hz R ps used u ≤ K)
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    conditionedNXParityChainSum ht hroot Nm mu z hz R
        (.pair p :: ps) used u ≤
      conditionedNXPairSum ht hroot Nm mu z hz R
        p.left.2 p.right.2 used p.skipLeft p.skipRight u * K := by
  let ca :=
    nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
  let cb :=
    nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
  simp only [conditionedNXParityChainSum]
  unfold conditionedNXPairSum
  dsimp only
  calc
    (∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXParityChainSum ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y)) ≤
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
              (labeledCopyPoint z x) (labeledCopyPoint z y) * K := by
      apply Finset.sum_le_sum
      intro x _hx
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro y _hy
        exact mul_le_mul_of_nonneg_left
          (htail (insert y (insert x used)) (labeledCopyPoint z y))
          (by
            unfold strongLambda
            split_ifs <;> positivity)
      · unfold lambda
        split_ifs <;> positivity
    _ = (∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
              (labeledCopyPoint z x) (labeledCopyPoint z y)) * K := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← Finset.sum_mul]
      ring

private theorem conditionedNXParityChainSum_roughPair_cons_le
    {t : PlaneTree}
    (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
    (R : ℝ) (p : NXPairBlock Nm mu)
    (ps : List (NXParityBlock Nm mu)) (K : ℝ)
    (htail : ∀ (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ),
      conditionedNXParityChainSum ht hroot Nm mu z hz R ps used u ≤ K)
    (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ) :
    conditionedNXParityChainSum ht hroot Nm mu z hz R
        (.roughPair p :: ps) used u ≤
      conditionedNXPairSum ht hroot Nm mu z hz R
        p.left.2 p.right.2 used p.skipLeft p.skipRight u * K := by
  let ca :=
    nxClassCluster ht hroot Nm mu z hz p.left.1 p.left.2
  let cb :=
    nxClassCluster ht hroot Nm mu z hz p.right.1 p.right.2
  simp only [conditionedNXParityChainSum]
  unfold conditionedNXPairSum
  dsimp only
  calc
    (∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
                (labeledCopyPoint z x) (labeledCopyPoint z y) *
              conditionedNXParityChainSum ht hroot Nm mu z hz R ps
                (insert y (insert x used)) (labeledCopyPoint z y)) ≤
      ∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
              (labeledCopyPoint z x) (labeledCopyPoint z y) * K := by
      apply Finset.sum_le_sum
      intro x _hx
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro y _hy
        exact mul_le_mul_of_nonneg_left
          (htail (insert y (insert x used)) (labeledCopyPoint z y))
          (by
            unfold strongLambda
            split_ifs <;> positivity)
      · unfold lambda
        split_ifs <;> positivity
    _ = (∑ x ∈ conditionedCopiesAtNX Nm mu used p.left.1,
        ca.lambda R p.skipLeft u (labeledCopyPoint z x) *
          ∑ y ∈ conditionedCopiesAtNX Nm mu (insert x used) p.right.1,
            strongLambda ca cb R p.skipRight
              (labeledCopyPoint z x) (labeledCopyPoint z y)) * K := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← Finset.sum_mul]
      ring

/-- **Mixed one-parity assembly.**  This is the paper-facing finite
elimination theorem for a fixed class sequence: it allows the at most four
one-variable boundary blocks (5.92) and all two-variable blocks (5.91) in
one nested sum.  The universal constant is outside every schedule and every
conditioning set. -/
theorem conditionedNXParityChainSum_le_targetProduct :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (ps : List (NXParityBlock Nm mu))
          (used : Finset (HeppLabeledCopy mu)) (u : Fin 4 → ℤ),
          conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
              ps used u ≤
            (ps.map fun p =>
              C * nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
  obtain ⟨C₀, hC₀, hpair⟩ :=
    nxCoupledCopyPairSum_le_paperDyadicPairTarget
  let C := max 256 C₀
  have hC256 : 256 ≤ C := le_max_left _ _
  have hC16 : 16 ≤ C := (by norm_num : (16 : ℝ) ≤ 256).trans hC256
  have hC0 : C₀ ≤ C := le_max_right _ _
  refine ⟨C, hC256, ?_⟩
  intro t ht hroot Nm mu z hz R hR ps
  induction ps with
  | nil =>
      intro used u
      simp [conditionedNXParityChainSum]
  | cons p ps ih =>
      intro used u
      let K : ℝ :=
        (ps.map fun q =>
          C * nxParityBlockTarget Nm mu (R : ℝ) q).prod
      have hK : 0 ≤ K := by
        unfold K
        apply List.prod_nonneg
        intro x hx
        obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp hx
        exact mul_nonneg (le_trans (by norm_num) hC16)
          (nxParityBlockTarget_nonneg Nm mu (R : ℝ) q)
      cases p with
      | single a skipped =>
          have hstep :=
            conditionedNXParityChainSum_single_cons_le
              ht hroot Nm mu z hz (R : ℝ) a skipped ps K
              (fun used' u' => ih used' u') used u
          have hlocal :=
            conditionedNXSingleSum_le_sixteen_mul_target
              ht hroot Nm mu z hz (R : ℝ) a.2 used skipped u
          have hweaken :
              16 * paperDyadicSingleRoughTarget Nm mu (R : ℝ)
                  a.1 skipped ≤
                C * paperDyadicSingleRoughTarget Nm mu (R : ℝ)
                  a.1 skipped :=
            mul_le_mul_of_nonneg_right hC16
              (paperDyadicSingleRoughTarget_nonneg
                Nm mu (R : ℝ) a.1 skipped)
          calc
            conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
                (.single a skipped :: ps) used u ≤
              conditionedNXSingleSum ht hroot Nm mu z hz (R : ℝ)
                a.2 used skipped u * K := hstep
            _ ≤ (C * paperDyadicSingleRoughTarget Nm mu (R : ℝ)
                a.1 skipped) * K :=
              mul_le_mul_of_nonneg_right (hlocal.trans hweaken) hK
            _ = ((.single a skipped :: ps).map fun q =>
                C * nxParityBlockTarget Nm mu (R : ℝ) q).prod := by
              change
                (C * paperDyadicSingleRoughTarget Nm mu (R : ℝ)
                    a.1 skipped) * K =
                  (C * paperDyadicSingleRoughTarget Nm mu (R : ℝ)
                    a.1 skipped) *
                    (ps.map fun q =>
                      C * nxParityBlockTarget Nm mu (R : ℝ) q).prod
              rfl
      | pair p =>
          have hstep :=
            conditionedNXParityChainSum_pair_cons_le
              ht hroot Nm mu z hz (R : ℝ) p ps K
              (fun used' u' => ih used' u') used u
          have hcond :=
            conditionedNXPairSum_le_nxCoupledCopyPairSum
              ht hroot Nm mu z hz (R : ℝ)
              p.left.2 p.right.2 used p.skipLeft p.skipRight u
          have hp :=
            hpair ht hroot Nm mu z hz R hR
              p.left.2 p.right.2 p.skipLeft p.skipRight u
          have hp' :
              nxCoupledCopyPairSum ht hroot Nm mu z hz (R : ℝ)
                  p.left.2 p.right.2 p.skipLeft p.skipRight u ≤
                C₀ * nxPairBlockTarget Nm mu p := by
            simpa [nxPairBlockTarget] using hp
          have hweaken :
              C₀ * nxPairBlockTarget Nm mu p ≤
                C * nxPairBlockTarget Nm mu p :=
            mul_le_mul_of_nonneg_right hC0
              (nxPairBlockTarget_nonneg Nm mu p)
          calc
            conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
                (.pair p :: ps) used u ≤
              conditionedNXPairSum ht hroot Nm mu z hz (R : ℝ)
                p.left.2 p.right.2 used p.skipLeft p.skipRight u * K :=
              hstep
            _ ≤ (C * nxPairBlockTarget Nm mu p) * K := by
              exact mul_le_mul_of_nonneg_right
                (hcond.trans (hp'.trans hweaken)) hK
            _ = ((.pair p :: ps).map fun q =>
                C * nxParityBlockTarget Nm mu (R : ℝ) q).prod := by
              change
                (C * nxPairBlockTarget Nm mu p) * K =
                  (C * nxPairBlockTarget Nm mu p) *
                    (ps.map fun q =>
                      C * nxParityBlockTarget Nm mu (R : ℝ) q).prod
              rfl
      | roughPair p =>
          have hstep :=
            conditionedNXParityChainSum_roughPair_cons_le
              ht hroot Nm mu z hz (R : ℝ) p ps K
              (fun used' u' => ih used' u') used u
          have hlocal :=
            conditionedNXPairSum_le_256_mul_roughTarget
              ht hroot Nm mu z hz (R : ℝ)
              p.left.2 p.right.2 used p.skipLeft p.skipRight u
          let roughTarget :=
            paperDyadicPairRoughTarget Nm mu (R : ℝ)
              p.left.1 p.right.1 p.skipLeft p.skipRight
          have hweaken :
              256 * roughTarget ≤ C * roughTarget :=
            mul_le_mul_of_nonneg_right hC256
              (paperDyadicPairRoughTarget_nonneg Nm mu (R : ℝ)
                p.left.1 p.right.1 p.skipLeft p.skipRight)
          calc
            conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
                (.roughPair p :: ps) used u ≤
              conditionedNXPairSum ht hroot Nm mu z hz (R : ℝ)
                p.left.2 p.right.2 used p.skipLeft p.skipRight u * K :=
              hstep
            _ ≤ (C * roughTarget) * K :=
              mul_le_mul_of_nonneg_right (hlocal.trans hweaken) hK
            _ = ((.roughPair p :: ps).map fun q =>
                C * nxParityBlockTarget Nm mu (R : ℝ) q).prod := by
              change
                (C * roughTarget) * K =
                  (C * roughTarget) *
                    (ps.map fun q =>
                      C * nxParityBlockTarget Nm mu (R : ℝ) q).prod
              rfl

/-! ## The twenty/forty-exception parity ledger -/

/-- A conservative explicit certificate for the gains spoiled by the rough
and one-variable local estimates in one parity.  Six interior operations may
touch three neighboring gains each and one boundary operation may touch two,
which is the paper's `6 · 3 + 1 · 2 = 20` audit. -/
structure ParityExceptionLedger (κ ι : Type*) [DecidableEq ι] where
  interiorOps : Finset κ
  boundaryOps : Finset κ
  affected : κ → Finset ι
  interior_card : interiorOps.card ≤ 6
  boundary_card : boundaryOps.card ≤ 1
  affected_interior : ∀ k ∈ interiorOps, (affected k).card ≤ 3
  affected_boundary : ∀ k ∈ boundaryOps, (affected k).card ≤ 2

/-- All gains discarded by the certified exceptional local operations. -/
def ParityExceptionLedger.exceptions {κ ι : Type*} [DecidableEq ι]
    (d : ParityExceptionLedger κ ι) : Finset ι :=
  (d.interiorOps.biUnion d.affected) ∪
    (d.boundaryOps.biUnion d.affected)

/-- One parity discards at most twenty gains, with the constant obtained
from the explicit local-operation ledger rather than assumed as a field. -/
theorem ParityExceptionLedger.card_exceptions_le_twenty
    {κ ι : Type*} [DecidableEq ι]
    (d : ParityExceptionLedger κ ι) :
    d.exceptions.card ≤ 20 := by
  have hi :
      (d.interiorOps.biUnion d.affected).card ≤ 18 := by
    calc
      (d.interiorOps.biUnion d.affected).card ≤
          ∑ k ∈ d.interiorOps, (d.affected k).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ d.interiorOps, 3 :=
        Finset.sum_le_sum fun k hk => d.affected_interior k hk
      _ = 3 * d.interiorOps.card := by
        simp [mul_comm]
      _ ≤ 3 * 6 := Nat.mul_le_mul_left 3 d.interior_card
      _ = 18 := by norm_num
  have hb :
      (d.boundaryOps.biUnion d.affected).card ≤ 2 := by
    calc
      (d.boundaryOps.biUnion d.affected).card ≤
          ∑ k ∈ d.boundaryOps, (d.affected k).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ d.boundaryOps, 2 :=
        Finset.sum_le_sum fun k hk => d.affected_boundary k hk
      _ = 2 * d.boundaryOps.card := by
        simp [mul_comm]
      _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 d.boundary_card
      _ = 2 := by norm_num
  unfold exceptions
  exact (Finset.card_union_le _ _).trans (by omega)

/-- Combining the even and odd exceptional ledgers loses at most forty
gain indices. -/
theorem two_parity_exception_union_card_le_forty
    {ι : Type*} [DecidableEq ι] (evenExceptional oddExceptional : Finset ι)
    (he : evenExceptional.card ≤ 20) (ho : oddExceptional.card ≤ 20) :
    (evenExceptional ∪ oddExceptional).card ≤ 40 :=
  (Finset.card_union_le _ _).trans (by omega)

/-! ### Interpolation changes `1/8` to `1/16` -/

/-- A generic ratio gain, used only for the interpolation identity. -/
noncomputable def ratioGain (θ r : ℝ) : ℝ :=
  min 1 (r ^ θ)

theorem ratioGain_nonneg (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ ratioGain θ r := by
  unfold ratioGain
  exact le_min zero_le_one (Real.rpow_nonneg hr _)

/-- Pointwise interpolation identity underlying the sentence after (5.87):
the square root of a `1/8` gain is the corresponding `1/16` gain. -/
theorem sqrt_ratioGain_eighth {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (ratioGain (1 / 8 : ℝ) r) =
      ratioGain (1 / 16 : ℝ) r := by
  rcases le_total r 1 with hr1 | h1r
  · have h8 : r ^ (1 / 8 : ℝ) ≤ 1 :=
      Real.rpow_le_one hr hr1 (by norm_num)
    have h16 : r ^ (1 / 16 : ℝ) ≤ 1 :=
      Real.rpow_le_one hr hr1 (by norm_num)
    unfold ratioGain
    rw [min_eq_right h8, min_eq_right h16,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hr]
    congr 1
    norm_num
  · have h8 : 1 ≤ r ^ (1 / 8 : ℝ) :=
      Real.one_le_rpow h1r (by norm_num)
    have h16 : 1 ≤ r ^ (1 / 16 : ℝ) :=
      Real.one_le_rpow h1r (by norm_num)
    unfold ratioGain
    rw [min_eq_left h8, min_eq_left h16]
    norm_num

/-- Square root commutes with the retained finite product of `1/8` gains,
turning every retained factor into exponent `1/16`. -/
theorem sqrt_prod_ratioGain_eighth {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (ratio : ι → ℝ) (hratio : ∀ i ∈ s, 0 ≤ ratio i) :
    Real.sqrt (∏ i ∈ s, ratioGain (1 / 8 : ℝ) (ratio i)) =
      ∏ i ∈ s, ratioGain (1 / 16 : ℝ) (ratio i) := by
  rw [Real.sqrt_prod s
    (fun i hi => ratioGain_nonneg _ (hratio i hi))]
  exact Finset.prod_congr rfl fun i hi =>
    sqrt_ratioGain_eighth (hratio i hi)

/-- The retained even and odd index sets join to the complement of the
union of their exceptions. -/
theorem parity_retained_union {ι : Type*} [DecidableEq ι]
    (blocks even odd evenExceptional oddExceptional : Finset ι)
    (hparts : even ∪ odd = blocks) (hdisj : Disjoint even odd)
    (he : evenExceptional ⊆ even) (ho : oddExceptional ⊆ odd) :
    (even \ evenExceptional) ∪ (odd \ oddExceptional) =
      blocks \ (evenExceptional ∪ oddExceptional) := by
  ext i
  constructor
  · intro hi
    simp only [Finset.mem_union, Finset.mem_sdiff] at hi ⊢
    constructor
    · rw [← hparts, Finset.mem_union]
      exact hi.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    · simp only [not_or]
      rcases hi with hi | hi
      · refine ⟨hi.2, ?_⟩
        intro hio
        exact Finset.disjoint_left.mp hdisj hi.1 (ho hio)
      · refine ⟨?_, hi.2⟩
        intro hie
        exact Finset.disjoint_left.mp hdisj (he hie) hi.1
  · intro hi
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at hi ⊢
    have hiblocks := hi.1
    rw [← hparts, Finset.mem_union] at hiblocks
    exact hiblocks.elim
      (fun hie => Or.inl ⟨hie, hi.2.1⟩)
      (fun hio => Or.inr ⟨hio, hi.2.2⟩)

/-- Exact product form of even/odd interpolation after deleting their two
exceptional sets.  Together with the following geometric-mean lemma this is
the formal content of the paper's transition from at most twenty exceptions
per parity to at most forty exceptions and exponent `1/16`. -/
theorem sqrt_even_mul_odd_gain_eq_sixteenth {ι : Type*}
    [DecidableEq ι]
    (blocks even odd evenExceptional oddExceptional : Finset ι)
    (hparts : even ∪ odd = blocks) (hdisj : Disjoint even odd)
    (he : evenExceptional ⊆ even) (ho : oddExceptional ⊆ odd)
    (ratio : ι → ℝ) (hratio : ∀ i ∈ blocks, 0 ≤ ratio i) :
    Real.sqrt
        ((∏ i ∈ even \ evenExceptional,
            ratioGain (1 / 8 : ℝ) (ratio i)) *
          ∏ i ∈ odd \ oddExceptional,
            ratioGain (1 / 8 : ℝ) (ratio i)) =
      ∏ i ∈ blocks \ (evenExceptional ∪ oddExceptional),
        ratioGain (1 / 16 : ℝ) (ratio i) := by
  have hkeepDisj :
      Disjoint (even \ evenExceptional) (odd \ oddExceptional) :=
    hdisj.mono Finset.sdiff_subset Finset.sdiff_subset
  rw [← Finset.prod_union hkeepDisj]
  rw [sqrt_prod_ratioGain_eighth
    ((even \ evenExceptional) ∪ (odd \ oddExceptional)) ratio]
  · rw [parity_retained_union blocks even odd
      evenExceptional oddExceptional hparts hdisj he ho]
  · intro i hi
    rw [parity_retained_union blocks even odd
      evenExceptional oddExceptional hparts hdisj he ho] at hi
    exact hratio i (Finset.mem_sdiff.mp hi).1

/-- If a nonnegative quantity satisfies the even and odd estimates, it is
bounded by their geometric mean.  This lemma performs the interpolation
rather than assuming it as an opaque global summation step. -/
theorem le_geometricMean_of_le_both {x a b : ℝ}
    (hx : 0 ≤ x) (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hxa : x ≤ a) (hxb : x ≤ b) :
    x ≤ Real.sqrt (a * b) := by
  have hsq : x * x ≤ a * b :=
    mul_le_mul hxa hxb hx ha
  calc
    x = Real.sqrt (x * x) := (Real.sqrt_mul_self hx).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt hsq

/-!
## Remaining statement-boundary obligations for the literal (5.87)

The analytic and finite-Fubini parts are closed above.  The following
position-level bookkeeping is intentionally not hidden in a hypothesis here:

* construct, from `Fin m`, the split at the minimal-scale position and the
  even/odd `NXParityBlock` schedules, proving at most four `single` blocks;
* select at most three skipped-edge blocks as `roughPair` and prove that their
  explicit `(N/R)²` factors give `(N_root/R)^(min (2s) 3)`;
* map those single/rough blocks to a concrete `ParityExceptionLedger`, and
  discharge its `6` interior plus `1` boundary operation bounds;
* compare the heterogeneous `single`/`roughPair` targets with the common
  refined target in (5.87), paying the explicit `Y^(1/2)` and `Ξ⁻¹`
  losses, proving that at most twenty such factors occur and absorbing
  the resulting `m^20` into a universal exponential;
* supply the mirrored elimination theorem on the left of the minimal-scale
  anchor (or an equivalent reversal argument), including the reversed
  ratio gain, the shared `used` set, and the anchor/cross-side
  distinct-copy bookkeeping;
* identify the arrangement sum after fixing the `(N,X)` word with the
  corresponding conditioned chain, then reinsert `R^(2s)` and the factorial
  ledger at the statement boundary.

Thus no theorem in this file is named as Proposition 5.10 or as (5.87)
itself; the declarations above are the strict, reusable middle layer needed
to close that final position-level assembly.
-/

end XYCluster
end
end Anderson4D
