import Anderson4D.Parametrix.PerrPhysicalBridge

/-!
# Explicit boundary algebra for the parametrix error

This file identifies the two concrete factor residuals with the finite
boundary sums in paper (3.21).  The argument is entirely algebraic:
graded compositions are classified by their first or last block, and
the resulting recurrence is inserted into the already proved finite
telescope.

No inverse of the Green operator and no pointwise kernel realization is
used here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-! ## The one-block operators -/

/-- The bounded operator carried by one graded block. -/
def gradedBlockL2Factor
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (d : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  Kop greenL2Op
    (continuousMultiplicationOp
      (renormWordWeightContinuousMap
        M ρ lam ε ω hξ d))

/-- The degree-one (mollified-noise) block. -/
def gradedNoiseL2Factor
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    TorusL2 →L[ℂ] TorusL2 :=
  gradedBlockL2Factor M ρ lam ε ω hξ 1

/-- The positive counterterm operator.  The sign is chosen so that a
graded block of size `2q` is its negative. -/
def gradedCountertermL2Factor
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (q : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  -gradedBlockL2Factor M ρ lam ε ω hξ (2 * q)

@[simp]
theorem renormWordL2Factor_cons
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (d : ℕ) (word : List ℕ) :
    renormWordL2Factor M ρ lam ε ω hξ (d :: word) =
      gradedBlockL2Factor M ρ lam ε ω hξ d *
        renormWordL2Factor M ρ lam ε ω hξ word :=
  rfl

@[simp]
theorem gradedBlockL2Factor_one
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    gradedBlockL2Factor M ρ lam ε ω hξ 1 =
      gradedNoiseL2Factor M ρ lam ε ω hξ :=
  rfl

theorem gradedBlockL2Factor_even
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    {d : ℕ} (hd : Even d) :
    gradedBlockL2Factor M ρ lam ε ω hξ d =
      -gradedCountertermL2Factor
        M ρ lam ε ω hξ (d / 2) := by
  obtain ⟨q, hq⟩ := hd
  have hhalf : d / 2 = q := by
    rw [hq]
    omega
  have htwice : 2 * (d / 2) = d := by
    rw [hhalf, hq]
    omega
  unfold gradedCountertermL2Factor
  rw [htwice, neg_neg]

theorem gradedBlockL2Factor_eq_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    {d : ℕ} (hone : d ≠ 1) (hodd : ¬Even d) :
    gradedBlockL2Factor M ρ lam ε ω hξ d = 0 := by
  have hweight :
      renormWordWeightContinuousMap
          M ρ lam ε ω hξ d = 0 := by
    apply ContinuousMap.ext
    intro z
    simp [renormWordWeightContinuousMap,
      renormWordWeight, hone, hodd]
  unfold gradedBlockL2Factor
  rw [hweight]
  change greenL2Op * continuousMultiplicationLM 0 = 0
  rw [map_zero, mul_zero]

/-! ## The mollified potential is the finite sum of graded blocks -/

private theorem continuousMap_finsetSum_apply
    {ι : Type*} (s : Finset ι) (f : ι → C(T4, ℂ))
    (z : T4) :
    (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih]

theorem mollifiedPotentialContinuousMap_eq_gradedWeights
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    mollifiedPotentialContinuousMap M ρ lam ε ω hξ =
      renormWordWeightContinuousMap
          M ρ lam ε ω hξ 1 +
        ∑ q ∈ Finset.Icc 1 (truncOrder ε),
          renormWordWeightContinuousMap
            M ρ lam ε ω hξ (2 * q) := by
  apply ContinuousMap.ext
  intro z
  have hweight :
      ∀ q ∈ Finset.Icc 1 (truncOrder ε),
        renormWordWeightContinuousMap
            M ρ lam ε ω hξ (2 * q) z =
          -(renormC2q ρ lam ε q : ℂ) := by
    intro q hq
    have hqpos : 0 < q := by
      exact (Finset.mem_Icc.mp hq).1
    have hne : 2 * q ≠ 1 := by omega
    have heven : Even (2 * q) := even_two_mul q
    have hhalf : 2 * q / 2 = q := by omega
    simp [renormWordWeightContinuousMap,
      renormWordWeight, hne, heven, hhalf]
  simp only [ContinuousMap.add_apply]
  rw [continuousMap_finsetSum_apply]
  rw [Finset.sum_congr rfl hweight]
  unfold mollifiedPotentialContinuousMap
  unfold mollifiedPotentialC multFun renormCEps
  simp [renormWordWeightContinuousMap,
    renormWordWeight, Finset.sum_neg_distrib]
  ring

theorem mollifiedPotentialL2Op_eq_gradedBlocks
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    Kop greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω) =
      gradedNoiseL2Factor M ρ lam ε ω hξ -
        ∑ q ∈ Finset.Icc 1 (truncOrder ε),
          gradedCountertermL2Factor
            M ρ lam ε ω hξ q := by
  rw [mollifiedPotentialL2Op, dif_pos hξ]
  change
    greenL2Op *
        continuousMultiplicationOp
          (mollifiedPotentialContinuousMap
            M ρ lam ε ω hξ) =
      _
  rw [mollifiedPotentialContinuousMap_eq_gradedWeights]
  change
    greenL2Op *
        continuousMultiplicationLM
          (renormWordWeightContinuousMap
              M ρ lam ε ω hξ 1 +
            ∑ q ∈ Finset.Icc 1 (truncOrder ε),
              renormWordWeightContinuousMap
                M ρ lam ε ω hξ (2 * q)) =
      _
  rw [map_add, map_sum]
  rw [mul_add, Finset.mul_sum]
  unfold gradedNoiseL2Factor gradedCountertermL2Factor
  unfold gradedBlockL2Factor Kop
  rw [Finset.sum_neg_distrib]
  abel

/-! ## Head and tail classification of operator words -/

/-- Reverse is packaged as an equivalence so that it can be composed
with `compositionHeadEquiv`. -/
def compositionReverseEquiv (n : ℕ) :
    Composition n ≃ Composition n where
  toFun := Composition.reverse
  invFun := Composition.reverse
  left_inv := Composition.reverse_reverse
  right_inv := Composition.reverse_reverse

/-- Classify a nonempty composition by its last block. -/
def compositionTailEquiv (n : ℕ) :
    Composition (n + 1) ≃
      Σ k : Fin (n + 1),
        Composition (n - k.val) :=
  (compositionReverseEquiv (n + 1)).trans <|
    (compositionHeadEquiv n).trans <|
      Equiv.sigmaCongrRight fun k =>
        compositionReverseEquiv (n - k.val)

theorem compositionTailEquiv_symm_blocks
    (n : ℕ) (k : Fin (n + 1))
    (c : Composition (n - k.val)) :
    ((compositionTailEquiv n).symm ⟨k, c⟩).blocks =
      c.blocks ++ [k.val + 1] := by
  simp [compositionTailEquiv, compositionReverseEquiv,
    compositionHeadEquiv, compositionPrepend]

/-- Appending one last block appends its operator on the right. -/
theorem renormWordL2Factor_append_single
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (word : List ℕ) (d : ℕ) :
    renormWordL2Factor
        M ρ lam ε ω hξ (word ++ [d]) =
      renormWordL2Factor M ρ lam ε ω hξ word *
        gradedBlockL2Factor M ρ lam ε ω hξ d := by
  induction word with
  | nil =>
      simp [renormWordL2Factor, gradedBlockL2Factor]
  | cons a word ih =>
      simp only [List.cons_append, renormWordL2Factor_cons, ih]
      rw [mul_assoc]

/-- Operator order `n+1`, classified by the first block. -/
theorem gradedParametrixL2FactorOrder_succ_eq_sum_head
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) :
    gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ (n + 1) =
      ∑ k : Fin (n + 1),
        gradedBlockL2Factor
            M ρ lam ε ω hξ (k.val + 1) *
          gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ (n - k.val) := by
  unfold gradedParametrixL2FactorOrder
  calc
    (∑ c : Composition (n + 1),
        renormWordL2Factor M ρ lam ε ω hξ c.blocks) =
      ∑ p :
          Σ k : Fin (n + 1),
            Composition (n - k.val),
        renormWordL2Factor M ρ lam ε ω hξ
          (((compositionHeadEquiv n).symm p).blocks) := by
            symm
            exact (compositionHeadEquiv n).symm.sum_comp
              (fun c : Composition (n + 1) =>
                renormWordL2Factor
                  M ρ lam ε ω hξ c.blocks)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Fintype.sum_congr
      intro k
      calc
        (∑ c : Composition (n - k.val),
            renormWordL2Factor M ρ lam ε ω hξ
              (((compositionHeadEquiv n).symm ⟨k, c⟩).blocks)) =
            ∑ c : Composition (n - k.val),
              gradedBlockL2Factor
                  M ρ lam ε ω hξ (k.val + 1) *
                renormWordL2Factor
                  M ρ lam ε ω hξ c.blocks := by
                    apply Fintype.sum_congr
                    intro c
                    rfl
        _ = _ := by rw [Finset.mul_sum]

/-- Operator order `n+1`, classified by the last block. -/
theorem gradedParametrixL2FactorOrder_succ_eq_sum_tail
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) :
    gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ (n + 1) =
      ∑ k : Fin (n + 1),
        gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ (n - k.val) *
          gradedBlockL2Factor
            M ρ lam ε ω hξ (k.val + 1) := by
  unfold gradedParametrixL2FactorOrder
  calc
    (∑ c : Composition (n + 1),
        renormWordL2Factor M ρ lam ε ω hξ c.blocks) =
      ∑ p :
          Σ k : Fin (n + 1),
            Composition (n - k.val),
        renormWordL2Factor M ρ lam ε ω hξ
          (((compositionTailEquiv n).symm p).blocks) := by
            symm
            exact (compositionTailEquiv n).symm.sum_comp
              (fun c : Composition (n + 1) =>
                renormWordL2Factor
                  M ρ lam ε ω hξ c.blocks)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Fintype.sum_congr
      intro k
      calc
        (∑ c : Composition (n - k.val),
            renormWordL2Factor M ρ lam ε ω hξ
              (((compositionTailEquiv n).symm ⟨k, c⟩).blocks)) =
            ∑ c : Composition (n - k.val),
              renormWordL2Factor
                  M ρ lam ε ω hξ c.blocks *
                gradedBlockL2Factor
                  M ρ lam ε ω hξ (k.val + 1) := by
                    apply Fintype.sum_congr
                    intro c
                    rw [compositionTailEquiv_symm_blocks]
                    exact renormWordL2Factor_append_single
                      M ρ lam ε ω hξ c.blocks (k.val + 1)
        _ = _ := by rw [Finset.sum_mul]

/-! ## The two operator recurrences -/

/-- `headSelector_sum` needs only additive group structure.  This
version applies to the noncommutative operator ring. -/
theorem headSelector_sum_addCommGroup
    {R : Type*} [AddCommGroup R]
    (n : ℕ) (A : R) (B : ℕ → R) :
    (∑ k : Fin (n + 1),
      if k.val = 0 then A
      else if Even (k.val + 1) then
        -B ((k.val + 1) / 2)
      else 0) =
      A - ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
        B q := by
  have hsplit :
      (∑ k : Fin (n + 1),
        if k.val = 0 then A
        else if Even (k.val + 1) then
          -B ((k.val + 1) / 2)
        else 0) =
        (∑ k : Fin (n + 1),
          if k.val = 0 then A else 0) +
        ∑ k : Fin (n + 1),
          if Even (k.val + 1) then
            -B ((k.val + 1) / 2)
          else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val = 0
    · simp [hk]
    · simp [hk]
  rw [hsplit]
  have hzero :
      (∑ k : Fin (n + 1),
        if k.val = 0 then A else 0) = A := by
    rw [Fin.sum_univ_succ]
    simp
  rw [hzero]
  have htailSum :
      (∑ k : Fin (n + 1),
        if Even (k.val + 1) then
          -B ((k.val + 1) / 2)
        else 0) =
        -(∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          B q) := by
    calc
      (∑ k : Fin (n + 1),
          if Even (k.val + 1) then
            -B ((k.val + 1) / 2)
          else 0) =
        ∑ k :
            {k : Fin (n + 1) //
              Even (k.val + 1)},
          -B ((k.val + 1) / 2) := by
            rw [← Finset.sum_filter]
            apply Finset.sum_subtype
            intro k
            simp
      _ =
        ∑ q :
            {q : ℕ //
              q ∈ Finset.Icc 1 ((n + 1) / 2)},
          -B q.val := by
            calc
              _ =
                  ∑ q :
                      {q : ℕ //
                        q ∈ Finset.Icc 1
                          ((n + 1) / 2)},
                    -B ((((evenHeadIndexEquiv n) q).val.val +
                      1) / 2) := by
                        symm
                        exact (evenHeadIndexEquiv n).sum_comp
                          (fun k =>
                            -B ((k.val.val + 1) / 2))
              _ = _ := by
                apply Fintype.sum_congr
                intro q
                congr 2
                have hinv :=
                  (evenHeadIndexEquiv n).left_inv q
                have hval :=
                  congrArg Subtype.val hinv
                change
                  ((evenHeadIndex n q).val.val + 1) / 2 =
                    q.val
                simpa only [evenHeadIndexEquiv,
                  evenHeadOrder] using hval
      _ =
        -(∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          B q) := by
            rw [← Finset.sum_neg_distrib]
            symm
            apply Finset.sum_subtype
            intro q
            rfl
  rw [htailSum]
  simp only [sub_eq_add_neg]

/-- First-block recurrence for the graded operator orders. -/
theorem gradedParametrixL2FactorOrder_succ_eq_noise_sub_counterterms
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) :
    gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ (n + 1) =
      gradedNoiseL2Factor M ρ lam ε ω hξ *
          gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ n -
        ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          gradedCountertermL2Factor
              M ρ lam ε ω hξ q *
            gradedParametrixL2FactorOrder
              M ρ lam ε ω hξ (n + 1 - 2 * q) := by
  rw [gradedParametrixL2FactorOrder_succ_eq_sum_head]
  let A :=
    gradedNoiseL2Factor M ρ lam ε ω hξ *
      gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ n
  let B : ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun q =>
      gradedCountertermL2Factor M ρ lam ε ω hξ q *
        gradedParametrixL2FactorOrder
          M ρ lam ε ω hξ (n + 1 - 2 * q)
  calc
    (∑ k : Fin (n + 1),
        gradedBlockL2Factor
            M ρ lam ε ω hξ (k.val + 1) *
          gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ (n - k.val)) =
      ∑ k : Fin (n + 1),
        if k.val = 0 then A
        else if Even (k.val + 1) then
          -B ((k.val + 1) / 2)
        else 0 := by
          apply Fintype.sum_congr
          intro k
          by_cases hk : k.val = 0
          · rw [if_pos hk]
            have hkfin : k = 0 := Fin.ext hk
            subst k
            rfl
          · rw [if_neg hk]
            by_cases heven : Even (k.val + 1)
            · rw [if_pos heven]
              have htwice :
                  2 * ((k.val + 1) / 2) =
                    k.val + 1 := by
                obtain ⟨q, hq⟩ := heven
                rw [hq]
                omega
              have htail :
                  n - k.val =
                    n + 1 -
                      2 * ((k.val + 1) / 2) := by
                omega
              rw [gradedBlockL2Factor_even
                M ρ lam ε ω hξ heven, htail]
              rw [neg_mul]
            · rw [if_neg heven,
                gradedBlockL2Factor_eq_zero
                  M ρ lam ε ω hξ (by omega) heven,
                zero_mul]
    _ = A - ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
        B q :=
      headSelector_sum_addCommGroup n A B
    _ = _ := by
      rfl

/-- Last-block recurrence, needed for the residual on the other side. -/
theorem gradedParametrixL2FactorOrder_succ_eq_noise_sub_counterterms_right
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) :
    gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ (n + 1) =
      gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ n *
          gradedNoiseL2Factor M ρ lam ε ω hξ -
        ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
          gradedParametrixL2FactorOrder
                M ρ lam ε ω hξ (n + 1 - 2 * q) *
            gradedCountertermL2Factor
              M ρ lam ε ω hξ q := by
  rw [gradedParametrixL2FactorOrder_succ_eq_sum_tail]
  let A :=
    gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ n *
      gradedNoiseL2Factor M ρ lam ε ω hξ
  let B : ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun q =>
      gradedParametrixL2FactorOrder
          M ρ lam ε ω hξ (n + 1 - 2 * q) *
        gradedCountertermL2Factor M ρ lam ε ω hξ q
  calc
    (∑ k : Fin (n + 1),
        gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ (n - k.val) *
          gradedBlockL2Factor
            M ρ lam ε ω hξ (k.val + 1)) =
      ∑ k : Fin (n + 1),
        if k.val = 0 then A
        else if Even (k.val + 1) then
          -B ((k.val + 1) / 2)
        else 0 := by
          apply Fintype.sum_congr
          intro k
          by_cases hk : k.val = 0
          · rw [if_pos hk]
            have hkfin : k = 0 := Fin.ext hk
            subst k
            rfl
          · rw [if_neg hk]
            by_cases heven : Even (k.val + 1)
            · rw [if_pos heven]
              have htwice :
                  2 * ((k.val + 1) / 2) =
                    k.val + 1 := by
                obtain ⟨q, hq⟩ := heven
                rw [hq]
                omega
              have htail :
                  n - k.val =
                    n + 1 -
                      2 * ((k.val + 1) / 2) := by
                omega
              rw [gradedBlockL2Factor_even
                M ρ lam ε ω hξ heven, htail]
              rw [mul_neg]
            · rw [if_neg heven,
                gradedBlockL2Factor_eq_zero
                  M ρ lam ε ω hξ (by omega) heven,
                mul_zero]
    _ = A - ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
        B q :=
      headSelector_sum_addCommGroup n A B
    _ = _ := by
      rfl

/-! ## The explicit boundary residuals -/

/-- First-block boundary sum in (3.21), corresponding to
`(1 - K) Q - 1`. -/
def gradedPerrRightBoundary
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (A : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  -(gradedNoiseL2Factor M ρ lam ε ω hξ *
      gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ A) +
    ∑ r ∈ Finset.range (A + 1),
      ∑ q ∈ (Finset.Icc 1 A).filter
        (fun q => A < r + 2 * q),
        gradedCountertermL2Factor
            M ρ lam ε ω hξ q *
          gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ r

/-- Last-block boundary sum in (3.21), corresponding to
`Q (1 - K) - 1`. -/
def gradedPerrLeftBoundary
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (A : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  -(gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ A *
      gradedNoiseL2Factor M ρ lam ε ω hξ) +
    ∑ r ∈ Finset.range (A + 1),
      ∑ q ∈ (Finset.Icc 1 A).filter
        (fun q => A < r + 2 * q),
        gradedParametrixL2FactorOrder
              M ρ lam ε ω hξ r *
          gradedCountertermL2Factor
            M ρ lam ε ω hξ q

theorem gradedPerrRightResidual_eq_boundary
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (A : ℕ) (hA : A = truncOrder ε) :
    (1 - Kop greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω)) *
        gradedTruncatedParametrixL2Factor
          M ρ lam ε ω hξ A -
      1 =
        gradedPerrRightBoundary
          M ρ lam ε ω hξ A := by
  let P : ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun n =>
      gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ n
  let N : ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun n =>
      gradedNoiseL2Factor M ρ lam ε ω hξ * P n
  let C : ℕ → ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun q r =>
      gradedCountertermL2Factor
          M ρ lam ε ω hξ q *
        P r
  have hrec :
      ∀ m ∈ Finset.Icc 1 A,
        N (m - 1) =
          P m +
            ∑ q ∈ Finset.Icc 1 (m / 2),
              C q (m - 2 * q) := by
    intro m hm
    have hmpos : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hsucc : m - 1 + 1 = m := by omega
    have horder :=
      gradedParametrixL2FactorOrder_succ_eq_noise_sub_counterterms
        M ρ lam ε ω hξ (m - 1)
    have horder' :
        P m =
          N (m - 1) -
            ∑ q ∈ Finset.Icc 1 (m / 2),
              C q (m - 2 * q) := by
      simpa only [P, N, C, hsucc] using horder
    rw [horder']
    abel
  have htelescope :=
    parametrixTelescopeIcc A P N C hrec
  have hK :=
    mollifiedPotentialL2Op_eq_gradedBlocks
      M ρ lam ε ω hξ
  rw [← hA] at hK
  have hNsum :
      (∑ m ∈ Finset.range (A + 1), N m) =
        gradedNoiseL2Factor M ρ lam ε ω hξ *
          ∑ m ∈ Finset.range (A + 1), P m := by
    unfold N
    rw [Finset.mul_sum]
  have hCsum :
      (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ Finset.Icc 1 A, C q r) =
        (∑ q ∈ Finset.Icc 1 A,
            gradedCountertermL2Factor
              M ρ lam ε ω hξ q) *
          ∑ r ∈ Finset.range (A + 1), P r := by
    unfold C
    rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
  have hPzero : P 0 = 1 := by
    exact gradedParametrixL2FactorOrder_zero
      M ρ lam ε ω hξ
  rw [hNsum, hCsum, hPzero] at htelescope
  simp only [Nat.not_le] at htelescope
  unfold gradedTruncatedParametrixL2Factor
  unfold gradedPerrRightBoundary
  rw [hK]
  change
    (1 -
          (gradedNoiseL2Factor M ρ lam ε ω hξ -
            ∑ q ∈ Finset.Icc 1 A,
              gradedCountertermL2Factor
                M ρ lam ε ω hξ q)) *
        (∑ m ∈ Finset.range (A + 1), P m) -
      1 =
    -(N A) +
      ∑ r ∈ Finset.range (A + 1),
        ∑ q ∈ (Finset.Icc 1 A).filter
          (fun q => A < r + 2 * q),
          C q r
  calc
    (1 -
          (gradedNoiseL2Factor M ρ lam ε ω hξ -
            ∑ q ∈ Finset.Icc 1 A,
              gradedCountertermL2Factor
                M ρ lam ε ω hξ q)) *
        (∑ m ∈ Finset.range (A + 1), P m) -
      1 =
        ((∑ m ∈ Finset.range (A + 1), P m) -
            gradedNoiseL2Factor M ρ lam ε ω hξ *
              (∑ m ∈ Finset.range (A + 1), P m) +
            (∑ q ∈ Finset.Icc 1 A,
              gradedCountertermL2Factor
                M ρ lam ε ω hξ q) *
              (∑ m ∈ Finset.range (A + 1), P m)) -
          1 := by noncomm_ring
    _ = _ := by
      rw [htelescope]
      abel

theorem gradedPerrLeftResidual_eq_boundary
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (A : ℕ) (hA : A = truncOrder ε) :
    gradedTruncatedParametrixL2Factor
          M ρ lam ε ω hξ A *
        (1 - Kop greenL2Op
          (mollifiedPotentialL2Op M ρ lam ε ω)) -
      1 =
        gradedPerrLeftBoundary
          M ρ lam ε ω hξ A := by
  let P : ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun n =>
      gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ n
  let N : ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun n =>
      P n * gradedNoiseL2Factor M ρ lam ε ω hξ
  let C : ℕ → ℕ → TorusL2 →L[ℂ] TorusL2 :=
    fun q r =>
      P r *
        gradedCountertermL2Factor
          M ρ lam ε ω hξ q
  have hrec :
      ∀ m ∈ Finset.Icc 1 A,
        N (m - 1) =
          P m +
            ∑ q ∈ Finset.Icc 1 (m / 2),
              C q (m - 2 * q) := by
    intro m hm
    have hmpos : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hsucc : m - 1 + 1 = m := by omega
    have horder :=
      gradedParametrixL2FactorOrder_succ_eq_noise_sub_counterterms_right
        M ρ lam ε ω hξ (m - 1)
    have horder' :
        P m =
          N (m - 1) -
            ∑ q ∈ Finset.Icc 1 (m / 2),
              C q (m - 2 * q) := by
      simpa only [P, N, C, hsucc] using horder
    rw [horder']
    abel
  have htelescope :=
    parametrixTelescopeIcc A P N C hrec
  have hK :=
    mollifiedPotentialL2Op_eq_gradedBlocks
      M ρ lam ε ω hξ
  rw [← hA] at hK
  have hNsum :
      (∑ m ∈ Finset.range (A + 1), N m) =
        (∑ m ∈ Finset.range (A + 1), P m) *
          gradedNoiseL2Factor M ρ lam ε ω hξ := by
    unfold N
    rw [Finset.sum_mul]
  have hCsum :
      (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ Finset.Icc 1 A, C q r) =
        (∑ r ∈ Finset.range (A + 1), P r) *
          ∑ q ∈ Finset.Icc 1 A,
            gradedCountertermL2Factor
              M ρ lam ε ω hξ q := by
    unfold C
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hPzero : P 0 = 1 := by
    exact gradedParametrixL2FactorOrder_zero
      M ρ lam ε ω hξ
  rw [hNsum, hCsum, hPzero] at htelescope
  simp only [Nat.not_le] at htelescope
  unfold gradedTruncatedParametrixL2Factor
  unfold gradedPerrLeftBoundary
  rw [hK]
  change
    (∑ m ∈ Finset.range (A + 1), P m) *
          (1 -
            (gradedNoiseL2Factor M ρ lam ε ω hξ -
              ∑ q ∈ Finset.Icc 1 A,
                gradedCountertermL2Factor
                  M ρ lam ε ω hξ q)) -
        1 =
      -(N A) +
        ∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ (Finset.Icc 1 A).filter
            (fun q => A < r + 2 * q),
            C q r
  calc
    (∑ m ∈ Finset.range (A + 1), P m) *
          (1 -
            (gradedNoiseL2Factor M ρ lam ε ω hξ -
              ∑ q ∈ Finset.Icc 1 A,
                gradedCountertermL2Factor
                  M ρ lam ε ω hξ q)) -
        1 =
      ((∑ m ∈ Finset.range (A + 1), P m) -
          (∑ m ∈ Finset.range (A + 1), P m) *
            gradedNoiseL2Factor M ρ lam ε ω hξ +
          (∑ m ∈ Finset.range (A + 1), P m) *
            (∑ q ∈ Finset.Icc 1 A,
              gradedCountertermL2Factor
                M ρ lam ε ω hξ q)) -
        1 := by noncomm_ring
    _ = _ := by
      rw [htelescope]
      abel

/-! ## Proof-independent boundary random variables -/

/-- Totalized explicit first-block boundary residual. -/
def canonicalPerrRightBoundary
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 := by
  classical
  exact fun ω =>
    if hξ : Continuous (M.xiEps ρ ε ω) then
      gradedPerrRightBoundary M ρ lam ε ω hξ A
    else 0

/-- Totalized explicit last-block boundary residual. -/
def canonicalPerrLeftBoundary
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 := by
  classical
  exact fun ω =>
    if hξ : Continuous (M.xiEps ρ ε ω) then
      gradedPerrLeftBoundary M ρ lam ε ω hξ A
    else 0

theorem canonicalPerrRightRemainder_eq_boundary_of_continuous
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (hA : A = truncOrder ε)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    canonicalPerrRightRemainder M ρ lam ε A ω =
      canonicalPerrRightBoundary M ρ lam ε A ω := by
  unfold canonicalPerrRightRemainder
  unfold canonicalGradedTruncatedParametrixL2Factor
  unfold canonicalPerrRightBoundary
  rw [dif_pos hξ, dif_pos hξ]
  exact gradedPerrRightResidual_eq_boundary
    M ρ lam ε ω hξ A hA

theorem canonicalPerrLeftRemainder_eq_boundary_of_continuous
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (hA : A = truncOrder ε)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    canonicalPerrLeftRemainder M ρ lam ε A ω =
      canonicalPerrLeftBoundary M ρ lam ε A ω := by
  unfold canonicalPerrLeftRemainder
  unfold canonicalGradedTruncatedParametrixL2Factor
  unfold canonicalPerrLeftBoundary
  rw [dif_pos hξ, dif_pos hξ]
  exact gradedPerrLeftResidual_eq_boundary
    M ρ lam ε ω hξ A hA

/-- At positive scale both canonical residuals are almost surely the
explicit boundary sums from (3.21). -/
theorem ae_canonicalPerrRemainders_eq_boundaries
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      canonicalPerrRightRemainder
            M ρ lam ε (truncOrder ε) ω =
        canonicalPerrRightBoundary
            M ρ lam ε (truncOrder ε) ω ∧
      canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε) ω =
        canonicalPerrLeftBoundary
          M ρ lam ε (truncOrder ε) ω := by
  filter_upwards [M.ae_continuous_xiEps ρ hε] with ω hξ
  exact ⟨
    canonicalPerrRightRemainder_eq_boundary_of_continuous
      M ρ lam ε (truncOrder ε) rfl ω hξ,
    canonicalPerrLeftRemainder_eq_boundary_of_continuous
      M ρ lam ε (truncOrder ε) rfl ω hξ⟩

/-- The canonical good-event estimate now asks for a first-moment
bound only on the explicit boundary sums of (3.21), rather than on
opaque residual variables. -/
theorem
    measureReal_compl_canonicalConstructedL2ParametrixGoodEvent_le_of_boundaries
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ truncOrder ε → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε (truncOrder ε) ω)
    (hintBoundary :
      Integrable
        (fun ω =>
          ‖canonicalPerrLeftBoundary
              M ρ lam ε (truncOrder ε) ω‖ +
            ‖canonicalPerrRightBoundary
              M ρ lam ε (truncOrder ε) ω‖)
        (volume : Measure M.Ω))
    (δR : ℝ)
    (hfirstBoundary :
      (∫ ω,
          ‖canonicalPerrLeftBoundary
              M ρ lam ε (truncOrder ε) ω‖ +
            ‖canonicalPerrRightBoundary
              M ρ lam ε (truncOrder ε) ω‖
        ∂(volume : Measure M.Ω)) ≤ δR) :
    (volume : Measure M.Ω).real
        (canonicalL2ParametrixGoodEvent
          M ρ lam ε (truncOrder ε)
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε (truncOrder ε))
          (canonicalPerrLeftRemainder
            M ρ lam ε (truncOrder ε))
          (canonicalPerrRightRemainder
            M ρ lam ε (truncOrder ε)))ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε (truncOrder ε) /
        (ε ^ (-14 : ℤ)) ^ 2 +
      δR / ε ^ 28 := by
  have hboundary :=
    ae_canonicalPerrRemainders_eq_boundaries
      M ρ lam hε
  have hnorm :
      (fun ω =>
        ‖canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε) ω‖ +
          ‖canonicalPerrRightRemainder
              M ρ lam ε (truncOrder ε) ω‖) =ᵐ[
        (volume : Measure M.Ω)]
      fun ω =>
        ‖canonicalPerrLeftBoundary
              M ρ lam ε (truncOrder ε) ω‖ +
          ‖canonicalPerrRightBoundary
              M ρ lam ε (truncOrder ε) ω‖ := by
    filter_upwards [hboundary] with ω hω
    rw [hω.1, hω.2]
  have hintR :
      Integrable
        (fun ω =>
          ‖canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε) ω‖ +
            ‖canonicalPerrRightRemainder
              M ρ lam ε (truncOrder ε) ω‖)
        (volume : Measure M.Ω) :=
    hintBoundary.congr hnorm.symm
  have hfirstR :
      (∫ ω,
          ‖canonicalPerrLeftRemainder
              M ρ lam ε (truncOrder ε) ω‖ +
            ‖canonicalPerrRightRemainder
              M ρ lam ε (truncOrder ε) ω‖
        ∂(volume : Measure M.Ω)) ≤ δR := by
    rw [integral_congr_ae hnorm]
    exact hfirstBoundary
  exact
    measureReal_compl_canonicalConstructedL2ParametrixGoodEvent_le
      hfubini hwick hdet
      houter hpower hlam hε hεle hagree
      hintR δR hfirstR

end PartialPairing

end

end Anderson4D
