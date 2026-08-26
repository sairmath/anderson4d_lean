import Anderson4D.Continuum.SingularConv
import Anderson4D.DetParametrix.Core.Kernels

/-!
# The primitive-pairing kernel and the exact Proposition 4.1 predicate

Paper: P-4.1 — Prop 4.1 statement layer — (4.2)–(4.4)

This file freezes the statement layer of Deng--Shen Proposition 4.1,
equations (4.2)--(4.4).  In particular:

* `primitiveFullPairings n` is the finite class of primitive full pairings
  of the paper interval `[1, 2n]` (represented by `Fin (2 * n)`);
* `primitiveKernel` is (4.2), for arbitrary chain inputs
  `G_j : T4 → ℝ`;
* `primitiveKernelInserted` is the same expression with the additional
  factor `ε² + max_{i,j} |x_i-x_j|²` from (4.4);
* `PrimitiveEstimateRegime`, `primitiveKernelMajorant`, and
  `primitiveInsertedMajorant` make every constant hidden by the paper's
  `≲` notation explicit;
* `Prop41BoundPredicate` is only a `Prop`-valued specification.  The
  difficult estimate is deliberately **not** asserted as a theorem here.

The endpoint tuple uses the already frozen `assemble` convention.  Paper
indices are shifted down by one throughout.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Primitive full pairings -/

/-- Primitive full pairings of the paper interval `[1, 2n]`.

`IsFull` excludes singles and `IsPrimitive` excludes every proper fully
paired subinterval.  Both conditions are needed: primitivity alone permits
partial pairings. -/
def primitiveFullPairings (n : ℕ) :
    Finset (PartialPairing (Fin (2 * n))) :=
  Finset.univ.filter fun κ => κ.IsFull ∧ IsPrimitive κ

@[simp] theorem mem_primitiveFullPairings {n : ℕ}
    {κ : PartialPairing (Fin (2 * n))} :
    κ ∈ primitiveFullPairings n ↔ κ.IsFull ∧ IsPrimitive κ := by
  simp [primitiveFullPairings]

/-- At the first paper order there is exactly one full pairing.  It is
primitive, so the primitive sum in (4.2) has one term. -/
theorem primitiveFullPairings_one_card :
    (primitiveFullPairings 1).card = 1 := by
  decide

/-! ## Endpoint assembly and chain edges -/

/-- Assemble `x₁ = z`, `x₂, …, x_{2n-1}`, and `x_{2n} = w`.

The proof `hn` excludes the junk arithmetic branch `n = 0` and witnesses
`2n = (2n-2)+2`, so this is exactly the project's common `assemble`
operation rather than a second endpoint convention. -/
def primitiveAssemble (n : ℕ) (hn : 1 ≤ n) (z w : T4)
    (v : Fin (2 * n - 2) → T4) : Fin (2 * n) → T4 :=
  fun j =>
    assemble z w v
      (Fin.cast (by omega : 2 * n = (2 * n - 2) + 2) j)

/-- The last slot `x_{2n}` of the primitive tuple. -/
def primitiveLast (n : ℕ) (hn : 1 ≤ n) : Fin (2 * n) :=
  ⟨2 * n - 1, by omega⟩

/-- The slot occupied by the internal variable with index `i`. -/
def primitiveInternalIdx (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (2 * n - 2)) : Fin (2 * n) :=
  Fin.cast (by omega : (2 * n - 2) + 2 = 2 * n) (varIdx i)

@[simp] theorem primitiveAssemble_zero (n : ℕ) (hn : 1 ≤ n)
    (z w : T4) (v : Fin (2 * n - 2) → T4) :
    primitiveAssemble n hn z w v
      (⟨0, by omega⟩ : Fin (2 * n)) = z := by
  simp [primitiveAssemble]

@[simp] theorem primitiveAssemble_last (n : ℕ) (hn : 1 ≤ n)
    (z w : T4) (v : Fin (2 * n - 2) → T4) :
    primitiveAssemble n hn z w v (primitiveLast n hn) = w := by
  unfold primitiveAssemble primitiveLast assemble
  simp only [Fin.cast_mk]
  rw [dif_neg (by omega), dif_pos (by omega)]

@[simp] theorem primitiveAssemble_internal (n : ℕ) (hn : 1 ≤ n)
    (z w : T4) (v : Fin (2 * n - 2) → T4)
    (i : Fin (2 * n - 2)) :
    primitiveAssemble n hn z w v (primitiveInternalIdx n hn i) = v i := by
  simp [primitiveAssemble, primitiveInternalIdx]

/-- Left endpoint of chain edge `j`, with paper edge indices shifted from
`1..2n-1` to `Fin (2n-1)`. -/
def primitiveEdgeLeft (n : ℕ) (hn : 1 ≤ n)
    (j : Fin (2 * n - 1)) : Fin (2 * n) :=
  ⟨j.val, by omega⟩

/-- Right endpoint of chain edge `j`. -/
def primitiveEdgeRight (n : ℕ) (hn : 1 ≤ n)
    (j : Fin (2 * n - 1)) : Fin (2 * n) :=
  ⟨j.val + 1, by omega⟩

/-! ## The two integrands in (4.2) and (4.4) -/

/-- The chain product `∏_{j=1}^{2n-1} G_j(x_j-x_{j+1})`. -/
def primitiveChainProduct (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (x : Fin (2 * n) → T4) : ℝ :=
  ∏ j : Fin (2 * n - 1),
    G j (x (primitiveEdgeLeft n hn j) -
      x (primitiveEdgeRight n hn j))

/-- The covariance product `∏_{ {i,j}∈κ } η_ε(x_i-x_j)`.

Every unordered pair is counted once, at its smaller endpoint. -/
def primitiveCovarianceProduct (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) : ℝ :=
  ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
    ρ.etaEpsT4 ε (x i - x (κ i))

/-- The integrand of (4.2), before endpoint assembly. -/
def primitiveIntegrand (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) : ℝ :=
  primitiveChainProduct n hn G x *
    primitiveCovarianceProduct ρ ε n κ x

/-- Squared diameter of a nonempty finite torus tuple:
`max_{i,j} |x_i-x_j|²`, with the project distance `torusDistSq`. -/
def torusTupleDiameterSq {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → T4) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    Finset.univ.sup' Finset.univ_nonempty fun j =>
      torusDistSq (x i - x j)

theorem torusDistSq_sub_le_torusTupleDiameterSq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → T4) (i j : ι) :
    torusDistSq (x i - x j) ≤ torusTupleDiameterSq x := by
  have hinner :
      torusDistSq (x i - x j) ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun k => torusDistSq (x i - x k)) :=
    Finset.le_sup' (f := fun k => torusDistSq (x i - x k)) (by simp)
  have houter :
      (Finset.univ.sup' Finset.univ_nonempty
          (fun k => torusDistSq (x i - x k))) ≤
        torusTupleDiameterSq x :=
    Finset.le_sup'
      (f := fun k =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun l => torusDistSq (x k - x l))) (by simp)
  exact hinner.trans houter

theorem torusTupleDiameterSq_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → T4) :
    0 ≤ torusTupleDiameterSq x := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  exact (torusDistSq_nonneg (x i - x i)).trans
    (torusDistSq_sub_le_torusTupleDiameterSq x i i)

/-- The (4.4) integrand, with the paper's insertion
`ε² + max_{i,j}|x_i-x_j|²`. -/
def primitiveInsertedIntegrand (ρ : SmoothCutoff) (ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) : ℝ :=
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  (ε ^ 2 + torusTupleDiameterSq x) *
    primitiveIntegrand ρ ε n hn G κ x

/-! ## The kernels -/

/-- The two-endpoint form of `J_{2n,prim}` in (4.2).

All `2n-2` internal variables use `paperMeasure`; the global coupling is
`λ_ε^{2n}` exactly as in the paper.  Bochner integrals retain mathlib's
junk value off integrability; Proposition 4.1's analytic proof supplies
the needed integrability. -/
def primitiveKernel (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) : ℝ :=
  lamEps lam ε ^ (2 * n) *
    ∑ κ ∈ primitiveFullPairings n,
      ∫ v : Fin (2 * n - 2) → T4,
        primitiveIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn z w v)
        ∂(Measure.pi fun _ => paperMeasure)

/-- The inserted two-endpoint kernel from (4.4). -/
def primitiveKernelInserted (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) : ℝ :=
  lamEps lam ε ^ (2 * n) *
    ∑ κ ∈ primitiveFullPairings n,
      ∫ v : Fin (2 * n - 2) → T4,
        primitiveInsertedIntegrand ρ ε n hn G κ
          (primitiveAssemble n hn z w v)
        ∂(Measure.pi fun _ => paperMeasure)

/-- The one-variable kernel denoted `J_{2n,prim}(z)` in (4.3), obtained by
fixing the second endpoint at the group identity. -/
def primitiveKernelDiff (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (z : T4) : ℝ :=
  primitiveKernel ρ lam ε n hn G z 0

/-- The one-variable inserted kernel denoted `J̃_{2n,prim}(z)` in (4.4). -/
def primitiveKernelInsertedDiff (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (z : T4) : ℝ :=
  primitiveKernelInserted ρ lam ε n hn G z 0

/-! ## Closed structural and positivity interfaces -/

private theorem eta_nonneg (ρ : SmoothCutoff) (x : R4) :
    0 ≤ ρ.eta x := by
  exact MeasureTheory.integral_nonneg fun y =>
    mul_nonneg (ρ.nonneg y) (ρ.nonneg (x - y))

private theorem etaEpsT4_nonneg (ρ : SmoothCutoff) (ε : ℝ) (z : T4) :
    0 ≤ ρ.etaEpsT4 ε z := by
  unfold SmoothCutoff.etaEpsT4
  exact tsum_nonneg fun k =>
    mul_nonneg ((even_two_mul 2).pow_nonneg ε⁻¹)
      (eta_nonneg ρ fun i =>
        ε⁻¹ * (torusLift z i + 2 * Real.pi * (k i : ℝ)))

theorem primitiveCovarianceProduct_nonneg (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) :
    0 ≤ primitiveCovarianceProduct ρ ε n κ x := by
  apply Finset.prod_nonneg
  intro i hi
  exact etaEpsT4_nonneg ρ ε (x i - x (κ i))

theorem primitiveChainProduct_nonneg (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z) (x : Fin (2 * n) → T4) :
    0 ≤ primitiveChainProduct n hn G x := by
  apply Finset.prod_nonneg
  intro j hj
  exact hG j _

theorem primitiveIntegrand_nonneg (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z) (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) :
    0 ≤ primitiveIntegrand ρ ε n hn G κ x :=
  mul_nonneg (primitiveChainProduct_nonneg n hn G hG x)
    (primitiveCovarianceProduct_nonneg ρ ε n κ x)

theorem primitiveInsertedIntegrand_nonneg (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z) (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) :
    0 ≤ primitiveInsertedIntegrand ρ ε n hn G κ x := by
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  exact mul_nonneg
    (add_nonneg (sq_nonneg ε) (torusTupleDiameterSq_nonneg x))
    (primitiveIntegrand_nonneg ρ ε n hn G hG κ x)

theorem primitiveKernel_nonneg (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z) (z w : T4) :
    0 ≤ primitiveKernel ρ lam ε n hn G z w := by
  apply mul_nonneg
  · exact (even_two_mul n).pow_nonneg (lamEps lam ε)
  · apply Finset.sum_nonneg
    intro κ hκ
    exact MeasureTheory.integral_nonneg fun v =>
      primitiveIntegrand_nonneg ρ ε n hn G hG κ
        (primitiveAssemble n hn z w v)

theorem primitiveKernelInserted_nonneg (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, 0 ≤ G j z) (z w : T4) :
    0 ≤ primitiveKernelInserted ρ lam ε n hn G z w := by
  apply mul_nonneg
  · exact (even_two_mul n).pow_nonneg (lamEps lam ε)
  · apply Finset.sum_nonneg
    intro κ hκ
    exact MeasureTheory.integral_nonneg fun v =>
      primitiveInsertedIntegrand_nonneg ρ ε n hn G hG κ
        (primitiveAssemble n hn z w v)

/-! ## Exact hypotheses and majorants for Proposition 4.1 -/

/-- The two hypotheses on every input `G_j` in Proposition 4.1:
hyperoctahedral invariance and the normalized pointwise bound
`|G_j(z)| ≤ |z|⁻²`. -/
def IsAdmissiblePrimitiveInput (n : ℕ)
    (G : Fin (2 * n - 1) → T4 → ℝ) : Prop :=
  (∀ j, MemEClassT4 (G j)) ∧
    ∀ j z, |G j z| ≤ invSqKer z

/-- Exact replacement for the support indicator `1_{|z| ≲ ε}`.

The hidden support constant is the explicit parameter `supportConstant`;
the squared formulation avoids a square root:
`torusDistSq z ≤ (supportConstant * ε)²`. -/
def primitiveSupportIndicator (supportConstant ε : ℝ) (z : T4) : ℝ :=
  if torusDistSq z ≤ (supportConstant * ε) ^ 2 then 1 else 0

theorem primitiveSupportIndicator_nonneg
    (supportConstant ε : ℝ) (z : T4) :
    0 ≤ primitiveSupportIndicator supportConstant ε z := by
  unfold primitiveSupportIndicator
  split <;> positivity

@[simp] theorem primitiveSupportIndicator_eq_one
    {supportConstant ε : ℝ} {z : T4}
    (h : torusDistSq z ≤ (supportConstant * ε) ^ 2) :
    primitiveSupportIndicator supportConstant ε z = 1 := by
  simp [primitiveSupportIndicator, h]

@[simp] theorem primitiveSupportIndicator_eq_zero
    {supportConstant ε : ℝ} {z : T4}
    (h : ¬torusDistSq z ≤ (supportConstant * ε) ^ 2) :
    primitiveSupportIndicator supportConstant ε z = 0 := by
  simp [primitiveSupportIndicator, h]

/-- The explicit parameter regime behind `1 ≤ n ≲ |log ε|`.

`orderConstant` is the hidden constant in the order restriction and
`supportConstant` is the (independent) hidden constant in the local
indicator.  The endpoint `ε = 1` is retained because the requested
theorem regime is `0 < ε ≤ 1`; the order inequality itself makes that
endpoint vacuous for `n ≥ 1`. -/
def PrimitiveEstimateRegime (n : ℕ) (lam ε orderConstant
    supportConstant C : ℝ) : Prop :=
  1 ≤ n ∧
    0 < ε ∧ ε ≤ 1 ∧
    0 < lam ∧
    0 < orderConstant ∧
    0 < supportConstant ∧
    0 < C ∧
    (n : ℝ) ≤ orderConstant * |Real.log ε|

/-- Every order up to the paper's actual truncation
`A = ⌊|log ε|⌋` lies in the order-constant-one primitive regime.

This is the explicit compatibility bridge between (3.11) and
Proposition 4.1; keeping it next to the regime definition prevents a
smaller hidden order constant from silently breaking the final
parametrix assembly. -/
theorem primitiveEstimateRegime_of_le_truncOrder
    {n : ℕ} (hn : 1 ≤ n)
    {lam ε supportConstant C : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlam : 0 < lam)
    (hsupport : 0 < supportConstant) (hC : 0 < C)
    (hntrunc : n ≤ truncOrder ε) :
    PrimitiveEstimateRegime n lam ε 1 supportConstant C := by
  refine
    ⟨hn, hε, hε1, hlam, zero_lt_one,
      hsupport, hC, ?_⟩
  simp only [one_mul]
  exact
    (Nat.cast_le.mpr hntrunc).trans
      (Nat.floor_le (abs_nonneg (Real.log ε)))

/-- Exact right-hand side of (4.3):
`(Cλ)^{2n}[ε⁻⁴/|log ε| · |z|⁻² 1_{|z|≤cε}
 + |log ε|⁻²(|z|²+ε²)⁻³]`. -/
def primitiveKernelMajorant (C lam ε supportConstant : ℝ)
    (n : ℕ) (z : T4) : ℝ :=
  (C * lam) ^ (2 * n) *
    (((ε⁻¹) ^ 4 / |Real.log ε|) * invSqKer z *
        primitiveSupportIndicator supportConstant ε z +
      (1 / |Real.log ε| ^ 2) *
        (torusDistSq z + ε ^ 2)⁻¹ ^ 3)

/-- Exact right-hand side of (4.4), whose two changes from (4.3) are
`ε⁻⁴ → ε⁻²` and decay power `3 → 2`. -/
def primitiveInsertedMajorant (C lam ε supportConstant : ℝ)
    (n : ℕ) (z : T4) : ℝ :=
  (C * lam) ^ (2 * n) *
    (((ε⁻¹) ^ 2 / |Real.log ε|) * invSqKer z *
        primitiveSupportIndicator supportConstant ε z +
      (1 / |Real.log ε| ^ 2) *
        (torusDistSq z + ε ^ 2)⁻¹ ^ 2)

theorem primitiveKernelMajorant_nonneg
    {C lam ε supportConstant : ℝ} {n : ℕ} {z : T4}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) :
    0 ≤ primitiveKernelMajorant C lam ε supportConstant n z := by
  unfold primitiveKernelMajorant
  apply mul_nonneg
  · exact pow_nonneg (mul_nonneg hC hlam) _
  · apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z)
    · exact mul_nonneg
        (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 3)

theorem primitiveInsertedMajorant_nonneg
    {C lam ε supportConstant : ℝ} {n : ℕ} {z : T4}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) :
    0 ≤ primitiveInsertedMajorant C lam ε supportConstant n z := by
  unfold primitiveInsertedMajorant
  apply mul_nonneg
  · exact pow_nonneg (mul_nonneg hC hlam) _
  · apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (div_nonneg (by positivity) (abs_nonneg _))
          (invSqKer_nonneg z))
        (primitiveSupportIndicator_nonneg supportConstant ε z)
    · exact mul_nonneg
        (div_nonneg zero_le_one (sq_nonneg _))
        (pow_nonneg
          (inv_nonneg.mpr
            (add_nonneg (torusDistSq_nonneg z) (sq_nonneg ε))) 2)

/-- The two pointwise inequalities (4.3)--(4.4), with no hidden
constants.  This is a predicate, not a proved theorem. -/
def PrimitiveKernelBounds (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (supportConstant C : ℝ) : Prop :=
  ∀ z : T4,
    |primitiveKernelDiff ρ lam ε n hn G z| ≤
        primitiveKernelMajorant C lam ε supportConstant n z ∧
      |primitiveKernelInsertedDiff ρ lam ε n hn G z| ≤
        primitiveInsertedMajorant C lam ε supportConstant n z

/-- Proposition 4.1 specification.

In the explicit small-scale and order regime, admissible `G_j` produce an
`E`-class primitive kernel
and satisfy both estimates (4.3)--(4.4).  No existential constant and no
`≲` notation are hidden in this predicate. -/
def Prop41BoundPredicate (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (orderConstant supportConstant C : ℝ) : Prop :=
  PrimitiveEstimateRegime n lam ε orderConstant supportConstant C →
    IsAdmissiblePrimitiveInput n G →
      MemEClassT4 (primitiveKernelDiff ρ lam ε n hn G) ∧
        MemEClassT4 (primitiveKernelInsertedDiff ρ lam ε n hn G) ∧
          PrimitiveKernelBounds ρ lam ε n hn G supportConstant C

/-- Global quantifier closure of Proposition 4.1.

The three constants are chosen once, before `λ`, `ε`, the perturbative
order, and the input kernels.  Keeping this wrapper is essential: merely
proving `Prop41BoundPredicate` after fixing all those parameters would allow
the constants to depend on the inputs and would not formalize the paper's
uniform estimate. -/
def Proposition41 (ρ : SmoothCutoff) : Prop :=
  ∃ orderConstant supportConstant C : ℝ,
    0 < orderConstant ∧ 0 < supportConstant ∧ 0 < C ∧
      ∀ (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        Prop41BoundPredicate ρ lam ε n hn G
          orderConstant supportConstant C

end

end Anderson4D
