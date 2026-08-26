import Anderson4D.DetParametrix.Paper42_Moment.R324FrequencyRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324TreeIntegrability
import Anderson4D.Continuum.FourPointFourier

/-!
# Aggregate endpoint Fourier loss for R-324

Paper Section 4.2, Step 2 first collapses all within-half primitive
intervals while the physical integrand is signed.  In the decay branch,
Step 4 then integrates each external Green leg before taking the absolute
value.  Every leg contributes its exact Green Fourier coefficient.  If the
endpoint belongs to a collapsed interval, the remaining phase difference
costs a factor at most two; passing from the inserted primitive estimate
back to the ordinary one costs `ε⁻²`.  We uniformly pay that latter cost
also in the easy branch.

This file isolates the resulting bookkeeping from both the primitive-block
product reindexing and the central high-frequency routing.  In particular,
the four actual Green coefficients aggregate directly to
`16 * r324EndpointLoss`; no endpoint-decay inequality is left for the final
countable-routing caller to postulate.  Its endpoint-separated identities
are also usable as exact Fubini normal forms, but their pointwise norm bounds
must not be moved in front of the signed interval collapses.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- Cost of one external endpoint.  `shortcut = true` is the branch in
which an extracted difference reaches that endpoint. -/
def r324EndpointBranchCost (ε : ℝ) (shortcut : Bool) : ℝ :=
  (if shortcut then 2 else 1) * ε⁻¹ ^ (2 : ℕ)

theorem r324EndpointBranchCost_nonneg
    (ε : ℝ) (shortcut : Bool) :
    0 ≤ r324EndpointBranchCost ε shortcut := by
  unfold r324EndpointBranchCost
  positivity

/-- Both endpoint branches are controlled by the same explicit uniform
loss. -/
theorem r324EndpointBranchCost_le
    (ε : ℝ) (shortcut : Bool) :
    r324EndpointBranchCost ε shortcut ≤
      2 * ε⁻¹ ^ (2 : ℕ) := by
  cases shortcut with
  | false =>
      simp only [r324EndpointBranchCost, Bool.false_eq_true,
        ↓reduceIte, one_mul]
      nlinarith [sq_nonneg ε⁻¹]
  | true =>
      simp [r324EndpointBranchCost]

/-- One actual external Green Fourier coefficient, with the explicit
ordinary-versus-inserted branch cost attached. -/
def r324EndpointFourierWeight
    (ε : ℝ) (k : Z4) (shortcut : Bool) : ℝ :=
  r324EndpointBranchCost ε shortcut *
    ‖∫ z : T4,
      charT4 k z * (greenFn z : ℂ) ∂paperMeasure‖

theorem r324EndpointFourierWeight_nonneg
    (ε : ℝ) (k : Z4) (shortcut : Bool) :
    0 ≤ r324EndpointFourierWeight ε k shortcut :=
  mul_nonneg
    (r324EndpointBranchCost_nonneg ε shortcut)
    (norm_nonneg _)

/-- A single endpoint keeps the exact Euclidean Japanese-bracket Green
decay. -/
theorem r324EndpointFourierWeight_le
    (ε : ℝ) (k : Z4) (shortcut : Bool) :
    r324EndpointFourierWeight ε k shortcut ≤
      2 * ε⁻¹ ^ (2 : ℕ) *
        paperSecondOrderModeDecay k := by
  unfold r324EndpointFourierWeight
  rw [norm_paperFourierCoeff_greenFn_eq]
  exact mul_le_mul_of_nonneg_right
    (r324EndpointBranchCost_le ε shortcut)
    (paperSecondOrderModeDecay_nonneg k)

/-- The four external endpoint flags, in `(x,y,z,w)` order. -/
abbrev R324EndpointFlags := Fin 4 → Bool

/-- Product of the four concrete endpoint Fourier weights.  The two left
copy endpoints carry `α`, and the two right copy endpoints carry `β`. -/
def r324FourEndpointFourierWeight
    (ε : ℝ) (α β : Z4)
    (flags : R324EndpointFlags) : ℝ :=
  r324EndpointFourierWeight ε α (flags 0) *
    r324EndpointFourierWeight ε α (flags 1) *
    r324EndpointFourierWeight ε β (flags 2) *
    r324EndpointFourierWeight ε β (flags 3)

theorem r324FourEndpointFourierWeight_nonneg
    (ε : ℝ) (α β : Z4)
    (flags : R324EndpointFlags) :
    0 ≤ r324FourEndpointFourierWeight ε α β flags := by
  unfold r324FourEndpointFourierWeight
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (r324EndpointFourierWeight_nonneg ε α (flags 0))
        (r324EndpointFourierWeight_nonneg ε α (flags 1)))
      (r324EndpointFourierWeight_nonneg ε β (flags 2)))
    (r324EndpointFourierWeight_nonneg ε β (flags 3))

/-- Four genuine Green Fourier integrations, four uniform `ε⁻²`
sacrifices, and at most four factors of two give precisely the paper's
endpoint loss up to the universal factor `16`. -/
theorem r324FourEndpointFourierWeight_le
    (ε : ℝ) (α β : Z4)
    (flags : R324EndpointFlags) :
    r324FourEndpointFourierWeight ε α β flags ≤
      16 * r324EndpointLoss ε α β := by
  have hx :=
    r324EndpointFourierWeight_le ε α (flags 0)
  have hy :=
    r324EndpointFourierWeight_le ε α (flags 1)
  have hz :=
    r324EndpointFourierWeight_le ε β (flags 2)
  have hw :=
    r324EndpointFourierWeight_le ε β (flags 3)
  have hx0 :=
    r324EndpointFourierWeight_nonneg ε α (flags 0)
  have hy0 :=
    r324EndpointFourierWeight_nonneg ε α (flags 1)
  have hz0 :=
    r324EndpointFourierWeight_nonneg ε β (flags 2)
  have hw0 :=
    r324EndpointFourierWeight_nonneg ε β (flags 3)
  have hα :=
    paperSecondOrderModeDecay_nonneg α
  have hβ :=
    paperSecondOrderModeDecay_nonneg β
  have hε : 0 ≤ ε⁻¹ ^ (2 : ℕ) := sq_nonneg ε⁻¹
  let A : ℝ :=
    r324EndpointFourierWeight ε α (flags 0)
  let B : ℝ :=
    r324EndpointFourierWeight ε α (flags 1)
  let C : ℝ :=
    r324EndpointFourierWeight ε β (flags 2)
  let D : ℝ :=
    r324EndpointFourierWeight ε β (flags 3)
  let a : ℝ :=
    2 * ε⁻¹ ^ (2 : ℕ) * paperSecondOrderModeDecay α
  let b : ℝ :=
    2 * ε⁻¹ ^ (2 : ℕ) * paperSecondOrderModeDecay β
  have ha : 0 ≤ a :=
    mul_nonneg (mul_nonneg (by norm_num) hε) hα
  have hb : 0 ≤ b :=
    mul_nonneg (mul_nonneg (by norm_num) hε) hβ
  have hAB : A * B ≤ a * a :=
    mul_le_mul hx hy hy0 ha
  have hCD : C * D ≤ b * b :=
    mul_le_mul hz hw hw0 hb
  have hCD0 : 0 ≤ C * D :=
    mul_nonneg hz0 hw0
  unfold r324FourEndpointFourierWeight
  calc
    r324EndpointFourierWeight ε α (flags 0) *
          r324EndpointFourierWeight ε α (flags 1) *
          r324EndpointFourierWeight ε β (flags 2) *
          r324EndpointFourierWeight ε β (flags 3)
        = (A * B) * (C * D) := by
      dsimp only [A, B, C, D]
      ring
    _ ≤ (a * a) * (b * b) :=
      mul_le_mul hAB hCD hCD0
        (mul_nonneg ha ha)
    _ =
        (2 * ε⁻¹ ^ (2 : ℕ) *
            paperSecondOrderModeDecay α) *
          (2 * ε⁻¹ ^ (2 : ℕ) *
            paperSecondOrderModeDecay α) *
          (2 * ε⁻¹ ^ (2 : ℕ) *
            paperSecondOrderModeDecay β) *
          (2 * ε⁻¹ ^ (2 : ℕ) *
            paperSecondOrderModeDecay β) := by
      dsimp only [a, b]
      ring
    _ = 16 * r324EndpointLoss ε α β := by
      unfold r324EndpointLoss
      rw [← paperSecondOrderModeDecay_sq,
        ← paperSecondOrderModeDecay_sq,
        ← four_endpoint_invSq_loss]
      ring

/-- Endpoint-weighted countable budget before the central frequency
decay is applied. -/
def r324EndpointWeightedBudget
    (ε : ℝ) (α β : Z4)
    (baseWeight : ℕ → ℝ)
    (flags : ℕ → R324EndpointFlags) : ℝ :=
  ∑' a,
    baseWeight a *
      r324FourEndpointFourierWeight ε α β (flags a)

/-- Direct countable aggregate form used by the routing construction.
The endpoint bound is proved here from the four concrete Fourier
coefficients; downstream code only supplies the endpoint-free summable
base weights. -/
theorem r324EndpointWeightedBudget_le
    (ε : ℝ) (α β : Z4)
    (baseWeight : ℕ → ℝ)
    (flags : ℕ → R324EndpointFlags)
    (hbase : Summable baseWeight)
    (hbaseNonneg : ∀ a, 0 ≤ baseWeight a) :
    r324EndpointWeightedBudget ε α β baseWeight flags ≤
      (16 * ∑' a, baseWeight a) *
        r324EndpointLoss ε α β := by
  have hdom :
      ∀ a,
        baseWeight a *
            r324FourEndpointFourierWeight ε α β (flags a) ≤
          baseWeight a * (16 * r324EndpointLoss ε α β) := by
    intro a
    exact mul_le_mul_of_nonneg_left
      (r324FourEndpointFourierWeight_le
        ε α β (flags a))
      (hbaseNonneg a)
  have hsummableDom :
      Summable fun a =>
        baseWeight a *
          (16 * r324EndpointLoss ε α β) :=
    hbase.mul_right _
  have hsummableEndpoint :
      Summable fun a =>
        baseWeight a *
          r324FourEndpointFourierWeight ε α β (flags a) :=
    hsummableDom.of_nonneg_of_le
      (fun a =>
        mul_nonneg (hbaseNonneg a)
          (r324FourEndpointFourierWeight_nonneg
            ε α β (flags a)))
      hdom
  unfold r324EndpointWeightedBudget
  calc
    (∑' a,
        baseWeight a *
          r324FourEndpointFourierWeight ε α β (flags a)) ≤
        ∑' a,
          baseWeight a *
            (16 * r324EndpointLoss ε α β) :=
      hsummableEndpoint.tsum_le_tsum hdom hsummableDom
    _ = (16 * ∑' a, baseWeight a) *
          r324EndpointLoss ε α β := by
      rw [tsum_mul_right]
      ring

/-! ## Concrete Fourier integration of a Green-tree endpoint -/

/-- The terminal vertex of every expanded increasing Green tree is a leaf.
Its Fourier integration therefore factors exactly into one translated Green
coefficient and the tree with that leaf removed. -/
theorem integral_char_mul_increasingTreeGreenProduct_snoc
    {n : ℕ} (parent : IncreasingTreeParent (n + 1))
    (v : Fin (n + 1) → T4) (k : Z4) :
    (∫ y : T4,
        charT4 k y *
          increasingTreeGreenProduct parent (Fin.snoc v y)
        ∂paperMeasure) =
      translatedGreenMode k (v parent.last) *
        increasingTreeGreenProduct parent.init v := by
  calc
    (∫ y : T4,
        charT4 k y *
          increasingTreeGreenProduct parent (Fin.snoc v y)
        ∂paperMeasure) =
        ∫ y : T4,
          (charT4 k y *
            (greenFn (y - v parent.last) : ℂ)) *
              increasingTreeGreenProduct parent.init v
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      rw [increasingTreeGreenProduct_snoc]
      ring
    _ =
        (∫ y : T4,
          charT4 k y *
            (greenFn (y - v parent.last) : ℂ)
          ∂paperMeasure) *
            increasingTreeGreenProduct parent.init v := by
      rw [integral_mul_const]
    _ = translatedGreenMode k (v parent.last) *
          increasingTreeGreenProduct parent.init v := by
      rfl

theorem norm_translatedGreenMode
    (k : Z4) (z : T4) :
    ‖translatedGreenMode k z‖ =
      paperSecondOrderModeDecay k := by
  rw [translatedGreenMode_eq, norm_mul, norm_charT4,
    one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  · rfl
  · positivity

/-- Norm form of the concrete leaf integration. -/
theorem norm_integral_char_mul_increasingTreeGreenProduct_snoc
    {n : ℕ} (parent : IncreasingTreeParent (n + 1))
    (v : Fin (n + 1) → T4) (k : Z4) :
    ‖∫ y : T4,
        charT4 k y *
          increasingTreeGreenProduct parent (Fin.snoc v y)
        ∂paperMeasure‖ =
      paperSecondOrderModeDecay k *
        ‖increasingTreeGreenProduct parent.init v‖ := by
  rw [integral_char_mul_increasingTreeGreenProduct_snoc,
    norm_mul, norm_translatedGreenMode]

/-! ## Endpoint-first coefficients, before taking absolute values -/

/-- An external Green leg, with the optional endpoint difference which is
created when that leg belongs to an extracted interval.  The orientation is
the one occurring at the right endpoint of a deterministic profile. -/
def r324OutgoingEndpointKernel
    (u v : T4) (shortcut : Bool) (y : T4) : ℂ :=
  (greenFn (u - y) : ℂ) -
    if shortcut then (greenFn (v - y) : ℂ) else 0

/-- The corresponding incoming external Green leg. -/
def r324IncomingEndpointKernel
    (u v : T4) (shortcut : Bool) (x : T4) : ℂ :=
  (greenFn (x - u) : ℂ) -
    if shortcut then (greenFn (x - v) : ℂ) else 0

/-- Fourier coefficient of either orientation of an endpoint leg. -/
def r324EndpointCoefficient
    (k : Z4) (u v : T4) (shortcut : Bool) : ℂ :=
  translatedGreenMode k u -
    if shortcut then translatedGreenMode k v else 0

theorem integral_char_mul_r324IncomingEndpointKernel
    (k : Z4) (u v : T4) (shortcut : Bool) :
    (∫ x : T4,
        charT4 k x *
          r324IncomingEndpointKernel u v shortcut x
        ∂paperMeasure) =
      r324EndpointCoefficient k u v shortcut := by
  cases shortcut with
  | false =>
      simp [r324IncomingEndpointKernel,
        r324EndpointCoefficient, translatedGreenMode]
  | true =>
      simp only [r324IncomingEndpointKernel,
        r324EndpointCoefficient, ↓reduceIte]
      simp_rw [mul_sub]
      rw [integral_sub]
      · rfl
      · change Integrable (greenModeFactor k u) paperMeasure
        exact integrable_greenModeFactor k u
      · change Integrable (greenModeFactor k v) paperMeasure
        exact integrable_greenModeFactor k v

/-- Reversing the Green argument does not change the endpoint Fourier
coefficient, because the Green kernel is even. -/
theorem integral_char_mul_r324OutgoingEndpointKernel
    (k : Z4) (u v : T4) (shortcut : Bool) :
    (∫ y : T4,
        charT4 k y *
          r324OutgoingEndpointKernel u v shortcut y
        ∂paperMeasure) =
      r324EndpointCoefficient k u v shortcut := by
  have horient (a : T4) :
      (fun y : T4 =>
          charT4 k y * (greenFn (a - y) : ℂ)) =
        fun y : T4 =>
          charT4 k y * (greenFn (y - a) : ℂ) := by
    funext y
    have hgreen :
        greenFn (a - y) = greenFn (y - a) := by
      have h :=
        (greenFn_memE.neg_invariant (a - y)).symm
      simpa only [neg_sub] using h
    rw [hgreen]
  cases shortcut with
  | false =>
      simp only [r324OutgoingEndpointKernel,
        r324EndpointCoefficient, Bool.false_eq_true,
        ↓reduceIte, sub_zero]
      rw [horient]
      rfl
  | true =>
      simp only [r324OutgoingEndpointKernel,
        r324EndpointCoefficient, ↓reduceIte]
      simp_rw [mul_sub]
      rw [integral_sub]
      · rw [horient u, horient v]
        rfl
      · rw [horient u]
        change Integrable (greenModeFactor k u) paperMeasure
        exact integrable_greenModeFactor k u
      · rw [horient v]
        change Integrable (greenModeFactor k v) paperMeasure
        exact integrable_greenModeFactor k v

/-- The optional endpoint difference costs at most a factor two, while
retaining the exact Euclidean Green multiplier. -/
theorem norm_r324EndpointCoefficient_le
    (k : Z4) (u v : T4) (shortcut : Bool) :
    ‖r324EndpointCoefficient k u v shortcut‖ ≤
      (if shortcut then 2 else 1) *
        paperSecondOrderModeDecay k := by
  cases shortcut with
  | false =>
      simp [r324EndpointCoefficient, norm_translatedGreenMode]
  | true =>
      simp only [r324EndpointCoefficient, ↓reduceIte]
      calc
        ‖translatedGreenMode k u -
            translatedGreenMode k v‖ ≤
          ‖translatedGreenMode k u‖ +
            ‖translatedGreenMode k v‖ :=
          norm_sub_le _ _
        _ = 2 * paperSecondOrderModeDecay k := by
          rw [norm_translatedGreenMode,
            norm_translatedGreenMode]
          ring

theorem paperSecondOrderModeDecay_neg (k : Z4) :
    paperSecondOrderModeDecay (-k) =
      paperSecondOrderModeDecay k := by
  unfold paperSecondOrderModeDecay paperModeNormSq
  simp only [Pi.neg_apply, Int.cast_neg, neg_sq]

/-- The four endpoint anchors for `(x,y,z,w)`.  The first coordinate is
the ordinary endpoint and the second is the subtraction anchor. -/
abbrev R324EndpointAnchors := Fin 4 → T4 × T4

/-- Product of the four genuine endpoint-first Fourier coefficients, in
the exact mode order `(α,β,-α,-β)` of (4.18). -/
def r324FourEndpointCoefficientWeight
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) : ℝ :=
  ‖r324EndpointCoefficient α
      (anchors 0).1 (anchors 0).2 (flags 0)‖ *
    ‖r324EndpointCoefficient β
      (anchors 1).1 (anchors 1).2 (flags 1)‖ *
    ‖r324EndpointCoefficient (-α)
      (anchors 2).1 (anchors 2).2 (flags 2)‖ *
    ‖r324EndpointCoefficient (-β)
      (anchors 3).1 (anchors 3).2 (flags 3)‖

theorem r324FourEndpointCoefficientWeight_nonneg
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) :
    0 ≤ r324FourEndpointCoefficientWeight
      α β anchors flags := by
  unfold r324FourEndpointCoefficientWeight
  positivity

/-- Fourier integration before absolute values gives the full
`⟨α⟩⁻⁴⟨β⟩⁻⁴` endpoint decay.  At most four endpoint differences account
for the universal factor `16`. -/
theorem r324FourEndpointCoefficientWeight_le
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) :
    r324FourEndpointCoefficientWeight α β anchors flags ≤
      16 * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β := by
  have hx :=
    norm_r324EndpointCoefficient_le α
      (anchors 0).1 (anchors 0).2 (flags 0)
  have hy :=
    norm_r324EndpointCoefficient_le β
      (anchors 1).1 (anchors 1).2 (flags 1)
  have hz :=
    norm_r324EndpointCoefficient_le (-α)
      (anchors 2).1 (anchors 2).2 (flags 2)
  have hw :=
    norm_r324EndpointCoefficient_le (-β)
      (anchors 3).1 (anchors 3).2 (flags 3)
  have hx0 :
      0 ≤ ‖r324EndpointCoefficient α
        (anchors 0).1 (anchors 0).2 (flags 0)‖ :=
    norm_nonneg _
  have hy0 :
      0 ≤ ‖r324EndpointCoefficient β
        (anchors 1).1 (anchors 1).2 (flags 1)‖ :=
    norm_nonneg _
  have hz0 :
      0 ≤ ‖r324EndpointCoefficient (-α)
        (anchors 2).1 (anchors 2).2 (flags 2)‖ :=
    norm_nonneg _
  have hw0 :
      0 ≤ ‖r324EndpointCoefficient (-β)
        (anchors 3).1 (anchors 3).2 (flags 3)‖ :=
    norm_nonneg _
  have hcost (b : Bool) :
      0 ≤ (if b then (2 : ℝ) else 1) := by
    cases b <;> norm_num
  have hcostLe (b : Bool) :
      (if b then (2 : ℝ) else 1) ≤ 2 := by
    cases b <;> norm_num
  have hα := paperSecondOrderModeDecay_nonneg α
  have hβ := paperSecondOrderModeDecay_nonneg β
  have hαneg := paperSecondOrderModeDecay_nonneg (-α)
  have hβneg := paperSecondOrderModeDecay_nonneg (-β)
  have hprod :=
    mul_le_mul
      (mul_le_mul
        (mul_le_mul hx hy hy0
          (mul_nonneg (hcost (flags 0)) hα))
        hz hz0
        (mul_nonneg
          (mul_nonneg (hcost (flags 0)) hα)
          (mul_nonneg (hcost (flags 1)) hβ)))
      hw hw0
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (hcost (flags 0)) hα)
          (mul_nonneg (hcost (flags 1)) hβ))
        (mul_nonneg (hcost (flags 2)) hαneg))
  calc
    r324FourEndpointCoefficientWeight α β anchors flags ≤
        ((if flags 0 then (2 : ℝ) else 1) *
            paperSecondOrderModeDecay α) *
          ((if flags 1 then (2 : ℝ) else 1) *
            paperSecondOrderModeDecay β) *
          ((if flags 2 then (2 : ℝ) else 1) *
            paperSecondOrderModeDecay (-α)) *
          ((if flags 3 then (2 : ℝ) else 1) *
            paperSecondOrderModeDecay (-β)) :=
      hprod
    _ ≤
        (2 * paperSecondOrderModeDecay α) *
          (2 * paperSecondOrderModeDecay β) *
          (2 * paperSecondOrderModeDecay (-α)) *
          (2 * paperSecondOrderModeDecay (-β)) := by
      gcongr
      · exact hcostLe (flags 0)
      · exact hcostLe (flags 1)
      · exact hcostLe (flags 2)
      · exact hcostLe (flags 3)
    _ = 16 * paperFourthOrderModeDecay α *
          paperFourthOrderModeDecay β := by
      rw [paperSecondOrderModeDecay_neg α,
        paperSecondOrderModeDecay_neg β,
        ← paperSecondOrderModeDecay_sq,
        ← paperSecondOrderModeDecay_sq]
      ring

/-- The four possible ordinary-versus-inserted sacrifices cost exactly
`ε⁻⁸`; this is kept separate from the genuine Fourier coefficient. -/
def r324SacrificedEndpointCoefficientWeight
    (ε : ℝ) (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) : ℝ :=
  ε⁻¹ ^ (8 : ℕ) *
    r324FourEndpointCoefficientWeight α β anchors flags

theorem r324SacrificedEndpointCoefficientWeight_le
    (ε : ℝ) (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) :
    r324SacrificedEndpointCoefficientWeight
        ε α β anchors flags ≤
      16 * r324EndpointLoss ε α β := by
  unfold r324SacrificedEndpointCoefficientWeight
    r324EndpointLoss
  have hε : 0 ≤ ε⁻¹ ^ (8 : ℕ) := by positivity
  calc
    ε⁻¹ ^ (8 : ℕ) *
          r324FourEndpointCoefficientWeight α β anchors flags ≤
        ε⁻¹ ^ (8 : ℕ) *
          (16 * paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) :=
      mul_le_mul_of_nonneg_left
        (r324FourEndpointCoefficientWeight_le
          α β anchors flags) hε
    _ = 16 *
          (ε⁻¹ ^ (8 : ℕ) *
            paperFourthOrderModeDecay α *
            paperFourthOrderModeDecay β) := by
      ring

/-! ## Exact four-leg integration for a grouped collapsed core -/

/-- Four separated endpoint legs multiplying an arbitrary core which is
already summed over the relevant primitive-pairing fibre.  The nesting is
chosen to match the `(x,y,z,w)` integral order in (4.18). -/
def r324EndpointSeparatedIntegrand
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) (core : ℂ)
    (x y z w : T4) : ℂ :=
  (charT4 α x *
      r324IncomingEndpointKernel
        (anchors 0).1 (anchors 0).2 (flags 0) x) *
    (charT4 β y *
      r324OutgoingEndpointKernel
        (anchors 1).1 (anchors 1).2 (flags 1) y) *
    (charT4 (-α) z *
      r324IncomingEndpointKernel
        (anchors 2).1 (anchors 2).2 (flags 2) z) *
    (charT4 (-β) w *
      r324OutgoingEndpointKernel
        (anchors 3).1 (anchors 3).2 (flags 3) w) *
    core

private theorem integral_const_mul_incomingEndpoint_mul_const
    (c d : ℂ) (k : Z4) (u v : T4) (shortcut : Bool) :
    (∫ x : T4,
        c * (charT4 k x *
          r324IncomingEndpointKernel u v shortcut x) * d
        ∂paperMeasure) =
      c * r324EndpointCoefficient k u v shortcut * d := by
  rw [integral_mul_const, integral_const_mul,
    integral_char_mul_r324IncomingEndpointKernel]

private theorem integral_const_mul_outgoingEndpoint_mul_const
    (c d : ℂ) (k : Z4) (u v : T4) (shortcut : Bool) :
    (∫ x : T4,
        c * (charT4 k x *
          r324OutgoingEndpointKernel u v shortcut x) * d
        ∂paperMeasure) =
      c * r324EndpointCoefficient k u v shortcut * d := by
  rw [integral_mul_const, integral_const_mul,
    integral_char_mul_r324OutgoingEndpointKernel]

/-- **Endpoint-first identity.**  The four external variables are
integrated before any norm is taken.  The core may already contain an
entire primitive-pairing/configuration fibre, so this lemma does not move an
absolute value through the cancellation required by Proposition 4.1. -/
theorem integral_r324EndpointSeparatedIntegrand
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) (core : ℂ) :
    (∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand
          α β anchors flags core x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure) =
      r324EndpointCoefficient α
          (anchors 0).1 (anchors 0).2 (flags 0) *
        (r324EndpointCoefficient β
          (anchors 1).1 (anchors 1).2 (flags 1) *
        (r324EndpointCoefficient (-α)
          (anchors 2).1 (anchors 2).2 (flags 2) *
        (r324EndpointCoefficient (-β)
          (anchors 3).1 (anchors 3).2 (flags 3) *
          core))) := by
  let A : T4 → ℂ := fun x =>
    charT4 α x *
      r324IncomingEndpointKernel
        (anchors 0).1 (anchors 0).2 (flags 0) x
  let B : T4 → ℂ := fun y =>
    charT4 β y *
      r324OutgoingEndpointKernel
        (anchors 1).1 (anchors 1).2 (flags 1) y
  let C : T4 → ℂ := fun z =>
    charT4 (-α) z *
      r324IncomingEndpointKernel
        (anchors 2).1 (anchors 2).2 (flags 2) z
  let D : T4 → ℂ := fun w =>
    charT4 (-β) w *
      r324OutgoingEndpointKernel
        (anchors 3).1 (anchors 3).2 (flags 3) w
  let a :=
    r324EndpointCoefficient α
      (anchors 0).1 (anchors 0).2 (flags 0)
  let b :=
    r324EndpointCoefficient β
      (anchors 1).1 (anchors 1).2 (flags 1)
  let c :=
    r324EndpointCoefficient (-α)
      (anchors 2).1 (anchors 2).2 (flags 2)
  let d :=
    r324EndpointCoefficient (-β)
      (anchors 3).1 (anchors 3).2 (flags 3)
  change
    (∫ x, ∫ y, ∫ z, ∫ w,
      A x * B y * C z * D w * core
      ∂paperMeasure ∂paperMeasure
      ∂paperMeasure ∂paperMeasure) =
        a * (b * (c * (d * core)))
  have hw (x y z : T4) :
      (∫ w, A x * B y * C z * D w * core
        ∂paperMeasure) =
        A x * B y * C z * d * core := by
    simpa only [A, B, C, D, d, mul_assoc] using
      integral_const_mul_outgoingEndpoint_mul_const
        (A x * B y * C z) core (-β)
        (anchors 3).1 (anchors 3).2 (flags 3)
  have hW :
      (∫ x, ∫ y, ∫ z, ∫ w,
          A x * B y * C z * D w * core
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure) =
        ∫ x, ∫ y, ∫ z,
          A x * B y * C z * d * core
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hw x y)
  rw [hW]
  have hz (x y : T4) :
      (∫ z, A x * B y * C z * d * core
        ∂paperMeasure) =
        A x * B y * c * (d * core) := by
    simpa only [A, B, C, c, mul_assoc] using
      integral_const_mul_incomingEndpoint_mul_const
        (A x * B y) (d * core) (-α)
        (anchors 2).1 (anchors 2).2 (flags 2)
  have hZ :
      (∫ x, ∫ y, ∫ z,
          A x * B y * C z * d * core
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure) =
        ∫ x, ∫ y,
          A x * B y * c * (d * core)
          ∂paperMeasure ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (hz x)
  rw [hZ]
  have hy (x : T4) :
      (∫ y, A x * B y * c * (d * core)
        ∂paperMeasure) =
        A x * b * (c * (d * core)) := by
    simpa only [A, B, b, mul_assoc] using
      integral_const_mul_outgoingEndpoint_mul_const
        (A x) (c * (d * core)) β
        (anchors 1).1 (anchors 1).2 (flags 1)
  have hY :
      (∫ x, ∫ y,
          A x * B y * c * (d * core)
          ∂paperMeasure ∂paperMeasure) =
        ∫ x, A x * b * (c * (d * core))
          ∂paperMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hy
  rw [hY]
  calc
    (∫ x, A x * b * (c * (d * core))
        ∂paperMeasure) =
        ∫ x, A x * (b * (c * (d * core)))
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x, A x ∂paperMeasure) *
          (b * (c * (d * core))) := by
      rw [integral_mul_const]
    _ = a * (b * (c * (d * core))) := by
      dsimp only [A, a]
      rw [integral_char_mul_r324IncomingEndpointKernel]

/-- Norm form of the endpoint-first identity. -/
theorem norm_integral_r324EndpointSeparatedIntegrand
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) (core : ℂ) :
    ‖∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand
          α β anchors flags core x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure‖ =
      r324FourEndpointCoefficientWeight α β anchors flags *
        ‖core‖ := by
  rw [integral_r324EndpointSeparatedIntegrand]
  unfold r324FourEndpointCoefficientWeight
  simp only [norm_mul]
  ring

/-- After the four ordinary-versus-inserted sacrifices, the exact grouped
endpoint-first term is controlled by the paper's endpoint loss. -/
theorem sacrificed_norm_integral_r324EndpointSeparatedIntegrand_le
    (ε : ℝ) (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags) (core : ℂ) :
    ε⁻¹ ^ (8 : ℕ) *
        ‖∫ x, ∫ y, ∫ z, ∫ w,
          r324EndpointSeparatedIntegrand
            α β anchors flags core x y z w
          ∂paperMeasure ∂paperMeasure
          ∂paperMeasure ∂paperMeasure‖ ≤
      (16 * r324EndpointLoss ε α β) * ‖core‖ := by
  rw [norm_integral_r324EndpointSeparatedIntegrand]
  have hcore : 0 ≤ ‖core‖ := norm_nonneg _
  calc
    ε⁻¹ ^ (8 : ℕ) *
          (r324FourEndpointCoefficientWeight
            α β anchors flags * ‖core‖) =
        r324SacrificedEndpointCoefficientWeight
            ε α β anchors flags * ‖core‖ := by
      unfold r324SacrificedEndpointCoefficientWeight
      ring
    _ ≤ (16 * r324EndpointLoss ε α β) * ‖core‖ :=
      mul_le_mul_of_nonneg_right
        (r324SacrificedEndpointCoefficientWeight_le
          ε α β anchors flags) hcore

end

end Anderson4D
