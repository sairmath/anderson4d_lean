import Anderson4D.Continuum.GreenBounds
import Anderson4D.DetParametrix.Core.ReductionPrimitive
import Mathlib.Order.Filter.Finite

/-!
# Off-diagonal representatives for the R-322 primitive input

Proposition 4.1 freezes its input hypothesis as the literal pointwise bound
`|G z| ≤ invSqKer z`.  Since `invSqKer 0 = 0`, the free Green function and
the kernels produced by proper-block collapse do not satisfy that normalized
statement at the identity.  This is only a representative issue: all uses of
those inputs inside a nontrivial primitive integral are insensitive to their
value on the singleton `{0}`.

This file records the bridge explicitly.  We zero a kernel at the identity,
prove that this preserves the paper's class `E`, normalize its off-diagonal
constant, and establish the null-diagonal facts needed to compare primitive
integrals.  No estimate or output predicate is assumed here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Zeroed and normalized representatives -/

/-- Replace the value of a kernel at the torus identity by zero. -/
def offDiagonalRepresentative (f : T4 → ℝ) (z : T4) : ℝ :=
  if z = 0 then 0 else f z

@[simp]
theorem offDiagonalRepresentative_zero (f : T4 → ℝ) :
    offDiagonalRepresentative f 0 = 0 := by
  simp [offDiagonalRepresentative]

theorem offDiagonalRepresentative_eq
    (f : T4 → ℝ) {z : T4} (hz : z ≠ 0) :
    offDiagonalRepresentative f z = f z := by
  simp [offDiagonalRepresentative, hz]

/-- Scaling which turns an off-diagonal bound
`|f z| ≤ C * invSqKer z` into the normalized Proposition 4.1 bound. -/
def normalizedOffDiagonalRepresentative
    (C : ℝ) (f : T4 → ℝ) (z : T4) : ℝ :=
  C⁻¹ * offDiagonalRepresentative f z

@[simp]
theorem normalizedOffDiagonalRepresentative_zero
    (C : ℝ) (f : T4 → ℝ) :
    normalizedOffDiagonalRepresentative C f 0 = 0 := by
  simp [normalizedOffDiagonalRepresentative]

private theorem permuteT4_ne_zero
    (σ : Equiv.Perm (Fin dim)) {z : T4} (hz : z ≠ 0) :
    permuteT4 σ z ≠ 0 := by
  intro h
  apply hz
  apply (permuteT4MeasurableEquiv σ).injective
  simpa only [permuteT4MeasurableEquiv_apply, permuteT4_zero] using h

private theorem coordinateFlipT4_ne_zero
    (i : Fin dim) {z : T4} (hz : z ≠ 0) :
    coordinateFlipT4 i z ≠ 0 := by
  intro h
  apply hz
  apply (coordinateFlipMeasurableEquiv i).injective
  simpa only [coordinateFlipMeasurableEquiv_apply,
    coordinateFlipT4_zero] using h

/-- Zeroing at the identity preserves the hyperoctahedral class `E`. -/
theorem offDiagonalRepresentative_memE
    {f : T4 → ℝ} (hf : MemEClassT4 f) :
    MemEClassT4 (offDiagonalRepresentative f) where
  perm_invariant := by
    intro σ z
    change offDiagonalRepresentative f (permuteT4 σ z) =
      offDiagonalRepresentative f z
    by_cases hz : z = 0
    · subst z
      simp
    · rw [offDiagonalRepresentative_eq _ hz,
        show offDiagonalRepresentative f (permuteT4 σ z) = f (permuteT4 σ z) from
          offDiagonalRepresentative_eq _
            (permuteT4_ne_zero σ hz)]
      exact hf.perm_invariant σ z
  even_coord := by
    intro i z
    change offDiagonalRepresentative f (coordinateFlipT4 i z) =
      offDiagonalRepresentative f z
    by_cases hz : z = 0
    · subst z
      simp
    · rw [offDiagonalRepresentative_eq _ hz,
        show offDiagonalRepresentative f (coordinateFlipT4 i z) =
            f (coordinateFlipT4 i z) from
          offDiagonalRepresentative_eq _
            (coordinateFlipT4_ne_zero i hz)]
      exact hf.even_coord i z

/-- Constant scaling preserves the hyperoctahedral class `E`. -/
theorem normalizedOffDiagonalRepresentative_memE
    (C : ℝ) {f : T4 → ℝ} (hf : MemEClassT4 f) :
    MemEClassT4 (normalizedOffDiagonalRepresentative C f) where
  perm_invariant := by
    intro σ z
    unfold normalizedOffDiagonalRepresentative
    rw [(offDiagonalRepresentative_memE hf).perm_invariant σ z]
  even_coord := by
    intro i z
    unfold normalizedOffDiagonalRepresentative
    rw [(offDiagonalRepresentative_memE hf).even_coord i z]

/-- Zeroing at one point does not change a kernel almost everywhere. -/
theorem offDiagonalRepresentative_ae_eq
    (f : T4 → ℝ) :
    offDiagonalRepresentative f =ᵐ[paperMeasure] f := by
  filter_upwards
      [compl_mem_ae_iff.mpr (paperMeasure_singleton (0 : T4))]
      with z hz
  rw [offDiagonalRepresentative_eq]
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz

/-- The normalized representative satisfies the literal input bound required
by Proposition 4.1. -/
theorem normalizedOffDiagonalRepresentative_le
    {C : ℝ} (hC : 0 < C) {f : T4 → ℝ}
    (hbound : ∀ z : T4, z ≠ 0 →
      |f z| ≤ C * invSqKer z)
    (z : T4) :
    |normalizedOffDiagonalRepresentative C f z| ≤
      invSqKer z := by
  by_cases hz : z = 0
  · subst z
    simpa only [normalizedOffDiagonalRepresentative_zero,
      abs_zero] using invSqKer_nonneg (0 : T4)
  · rw [normalizedOffDiagonalRepresentative,
      offDiagonalRepresentative_eq f hz, abs_mul,
      abs_of_pos (inv_pos.mpr hC)]
    calc
      C⁻¹ * |f z| ≤ C⁻¹ * (C * invSqKer z) :=
        mul_le_mul_of_nonneg_left (hbound z hz)
          (inv_nonneg.mpr hC.le)
      _ = invSqKer z := by
        field_simp

/-- Family form of the preceding construction, matching the exact input
type of Proposition 4.1. -/
theorem normalizedOffDiagonalRepresentative_admissible
    {n : ℕ} {C : Fin (2 * n - 1) → ℝ}
    (hC : ∀ j, 0 < C j)
    {G : Fin (2 * n - 1) → T4 → ℝ}
    (hmem : ∀ j, MemEClassT4 (G j))
    (hbound : ∀ j z, z ≠ 0 →
      |G j z| ≤ C j * invSqKer z) :
    IsAdmissiblePrimitiveInput n
      (fun j => normalizedOffDiagonalRepresentative (C j) (G j)) := by
  constructor
  · intro j
    exact normalizedOffDiagonalRepresentative_memE
      (C j) (hmem j)
  · intro j z
    exact normalizedOffDiagonalRepresentative_le
      (hC j) (hbound j) z

/-! ## Null diagonals in finite paper products -/

/-- Distinct coordinates of a finite tuple sampled from the paper product
measure are unequal almost surely.  This is the precise measure-theoretic
fact that permits off-diagonal representatives in primitive chains. -/
theorem ae_pi_eval_ne_eval
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∀ᵐ v : Fin (n + 1) → T4
        ∂(Measure.pi fun _ => paperMeasure),
      v i ≠ v j := by
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => T4) i
  let μtail :=
    Measure.pi fun _ : Fin n => paperMeasure
  have htarget :
      ∀ᵐ p : T4 × (Fin n → T4)
          ∂(paperMeasure.prod μtail),
        p.1 ≠ p.2 k := by
    rw [Measure.ae_prod_iff_ae_ae]
    · filter_upwards with x
      exact (Measure.ae_eval_ne
        (fun _ : Fin n => paperMeasure) k x).mono
          fun v hv => Ne.symm hv
    · exact (measurableSet_eq_fun
        (f := fun p : T4 × (Fin n → T4) => p.1)
        (g := fun p : T4 × (Fin n → T4) => p.2 k)
        measurable_fst
        ((measurable_pi_apply k).comp measurable_snd)).compl
  have hp :
      MeasurePreserving e
        (Measure.pi fun _ : Fin (n + 1) => paperMeasure)
        (paperMeasure.prod μtail) := by
    simpa only [e, μtail] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => paperMeasure) i)
  have hpull :
      ∀ᵐ v : Fin (n + 1) → T4
          ∂(Measure.pi fun _ => paperMeasure),
        (e v).1 ≠ (e v).2 k :=
    hp.quasiMeasurePreserving.tendsto_ae htarget
  filter_upwards [hpull] with v hv
  change v i ≠ v (i.succAbove k) at hv
  simpa only [hk] using hv

/-- Cardinality-generic form of `ae_pi_eval_ne_eval`. -/
theorem ae_pi_eval_ne_eval_of_pos
    {m : ℕ} (hm : 0 < m) (i j : Fin m) (hij : i ≠ j) :
    ∀ᵐ v : Fin m → T4
        ∂(Measure.pi fun _ => paperMeasure),
      v i ≠ v j := by
  cases m with
  | zero => omega
  | succ n =>
      exact ae_pi_eval_ne_eval i j hij

/-- A fixed coordinate of a nonempty paper-product tuple avoids any fixed
torus point almost surely. -/
theorem ae_pi_eval_ne_const
    {m : ℕ} (i : Fin m) (x : T4) :
    ∀ᵐ v : Fin m → T4
        ∂(Measure.pi fun _ => paperMeasure),
      v i ≠ x := by
  letI : NullSingletonClass paperMeasure :=
    ⟨paperMeasure_singleton⟩
  exact Measure.ae_eval_ne
    (fun _ : Fin m => paperMeasure) i x

/-! ## Primitive-chain edge diagonals -/

/-- At order at least two, every edge in an assembled primitive chain is
off the diagonal almost surely.  Endpoint edges use the nullity of a
coordinate hyperplane; internal edges use `ae_pi_eval_ne_eval_of_pos`. -/
theorem ae_primitiveEdge_sub_ne_zero
    (n : ℕ) (hn : 2 ≤ n) (z w : T4)
    (j : Fin (2 * n - 1)) :
    ∀ᵐ v : Fin (2 * n - 2) → T4
        ∂(Measure.pi fun _ => paperMeasure),
      primitiveAssemble n (by omega) z w v
          (primitiveEdgeLeft n (by omega) j) -
        primitiveAssemble n (by omega) z w v
          (primitiveEdgeRight n (by omega) j) ≠ 0 := by
  by_cases hfirst : j.val = 0
  · let i0 : Fin (2 * n - 2) := ⟨0, by omega⟩
    filter_upwards [ae_pi_eval_ne_const i0 z] with v hv
    apply sub_ne_zero.mpr
    have hleft :
        primitiveEdgeLeft n (by omega) j =
          (⟨0, by omega⟩ : Fin (2 * n)) := by
      apply Fin.ext
      exact hfirst
    have hright :
        primitiveEdgeRight n (by omega) j =
          primitiveInternalIdx n (by omega) i0 := by
      apply Fin.ext
      change j.val + 1 = i0.val + 1
      simp [i0, hfirst]
    rw [hleft, primitiveAssemble_zero, hright,
      primitiveAssemble_internal]
    exact Ne.symm hv
  · by_cases hlast : j.val + 1 = 2 * n - 1
    · let ilast : Fin (2 * n - 2) :=
        ⟨2 * n - 3, by omega⟩
      filter_upwards [ae_pi_eval_ne_const ilast w] with v hv
      apply sub_ne_zero.mpr
      have hleft :
          primitiveEdgeLeft n (by omega) j =
            primitiveInternalIdx n (by omega) ilast := by
        apply Fin.ext
        change j.val = ilast.val + 1
        simp only [ilast]
        omega
      have hright :
          primitiveEdgeRight n (by omega) j =
            primitiveLast n (by omega) := by
        apply Fin.ext
        exact hlast
      rw [hleft, primitiveAssemble_internal, hright,
        primitiveAssemble_last]
      exact hv
    · let ileft : Fin (2 * n - 2) :=
        ⟨j.val - 1, by
          have hj := j.isLt
          omega⟩
      let iright : Fin (2 * n - 2) :=
        ⟨j.val, by
          have hj := j.isLt
          omega⟩
      have hne : ileft ≠ iright := by
        intro h
        have hval := congrArg Fin.val h
        change j.val - 1 = j.val at hval
        omega
      filter_upwards
          [ae_pi_eval_ne_eval_of_pos (by omega)
            ileft iright hne] with v hv
      apply sub_ne_zero.mpr
      have hleft :
          primitiveEdgeLeft n (by omega) j =
            primitiveInternalIdx n (by omega) ileft := by
        apply Fin.ext
        change j.val = ileft.val + 1
        simp only [ileft]
        omega
      have hright :
          primitiveEdgeRight n (by omega) j =
            primitiveInternalIdx n (by omega) iright := by
        apply Fin.ext
        rfl
      rw [hleft, primitiveAssemble_internal, hright,
        primitiveAssemble_internal]
      exact hv

/-! ## Congruence of primitive kernels under singleton changes -/

/-- At order at least two, changing every chain input only at the identity
does not change the chain product almost everywhere. -/
theorem primitiveChainProduct_congr_ae_offDiagonal
    (n : ℕ) (hn : 2 ≤ n)
    (G G' : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, z ≠ 0 → G j z = G' j z)
    (z w : T4) :
    (fun v : Fin (2 * n - 2) → T4 =>
      primitiveChainProduct n (by omega) G
        (primitiveAssemble n (by omega) z w v)) =ᵐ[
          Measure.pi fun _ => paperMeasure]
    (fun v : Fin (2 * n - 2) → T4 =>
      primitiveChainProduct n (by omega) G'
        (primitiveAssemble n (by omega) z w v)) := by
  have hall :
      ∀ᵐ v : Fin (2 * n - 2) → T4
          ∂(Measure.pi fun _ => paperMeasure),
        ∀ j : Fin (2 * n - 1),
          primitiveAssemble n (by omega) z w v
              (primitiveEdgeLeft n (by omega) j) -
            primitiveAssemble n (by omega) z w v
              (primitiveEdgeRight n (by omega) j) ≠ 0 :=
    Filter.eventually_all.2 fun j =>
      ae_primitiveEdge_sub_ne_zero n hn z w j
  filter_upwards [hall] with v hv
  unfold primitiveChainProduct
  apply Finset.prod_congr rfl
  intro j _hj
  exact hG j _ (hv j)

/-- The primitive integrand is insensitive almost everywhere to
off-diagonal-equivalent chain inputs. -/
theorem primitiveIntegrand_congr_ae_offDiagonal
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 2 ≤ n)
    (G G' : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, z ≠ 0 → G j z = G' j z)
    (κ : PartialPairing (Fin (2 * n)))
    (z w : T4) :
    (fun v : Fin (2 * n - 2) → T4 =>
      primitiveIntegrand ρ ε n (by omega) G κ
        (primitiveAssemble n (by omega) z w v)) =ᵐ[
          Measure.pi fun _ => paperMeasure]
    (fun v : Fin (2 * n - 2) → T4 =>
      primitiveIntegrand ρ ε n (by omega) G' κ
        (primitiveAssemble n (by omega) z w v)) := by
  filter_upwards
      [primitiveChainProduct_congr_ae_offDiagonal
        n hn G G' hG z w] with v hv
  unfold primitiveIntegrand
  rw [hv]

/-- For primitive order at least two, the kernel depends only on the
off-diagonal representatives of its input functions. -/
theorem primitiveKernel_congr_offDiagonal
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 2 ≤ n)
    (G G' : Fin (2 * n - 1) → T4 → ℝ)
    (hG : ∀ j z, z ≠ 0 → G j z = G' j z)
    (z w : T4) :
    primitiveKernel ρ lam ε n (by omega) G z w =
      primitiveKernel ρ lam ε n (by omega) G' z w := by
  unfold primitiveKernel
  apply congrArg (fun a : ℝ => lamEps lam ε ^ (2 * n) * a)
  apply Finset.sum_congr rfl
  intro κ _hκ
  apply integral_congr_ae
  exact primitiveIntegrand_congr_ae_offDiagonal
    ρ ε n hn G G' hG κ z w

/-- In particular, zeroing all chain inputs at the identity leaves every
primitive kernel of order at least two unchanged. -/
theorem primitiveKernel_offDiagonalRepresentative
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 2 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    primitiveKernel ρ lam ε n (by omega) G z w =
      primitiveKernel ρ lam ε n (by omega)
        (fun j => offDiagonalRepresentative (G j)) z w := by
  apply primitiveKernel_congr_offDiagonal
    ρ lam ε n hn G
      (fun j => offDiagonalRepresentative (G j))
  intro j u hu
  exact (offDiagonalRepresentative_eq (G j) hu).symm

/-! ## Constant scaling of primitive inputs -/

/-- Multiplying every chain input by one constant contributes one copy of
that constant for each of the `2n-1` chain edges. -/
theorem primitiveChainProduct_const_mul
    (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (x : Fin (2 * n) → T4) :
    primitiveChainProduct n hn
        (fun j z => C * G j z) x =
      C ^ (2 * n - 1) *
        primitiveChainProduct n hn G x := by
  unfold primitiveChainProduct
  rw [Finset.prod_mul_distrib]
  simp

/-- Constant scaling at the integrand level. -/
theorem primitiveIntegrand_const_mul
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) :
    primitiveIntegrand ρ ε n hn
        (fun j z => C * G j z) κ x =
      C ^ (2 * n - 1) *
        primitiveIntegrand ρ ε n hn G κ x := by
  unfold primitiveIntegrand
  rw [primitiveChainProduct_const_mul]
  ring

/-- Constant scaling at the primitive-kernel level. -/
theorem primitiveKernel_const_mul
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (C : ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    primitiveKernel ρ lam ε n hn
        (fun j u => C * G j u) z w =
      C ^ (2 * n - 1) *
        primitiveKernel ρ lam ε n hn G z w := by
  unfold primitiveKernel
  simp_rw [primitiveIntegrand_const_mul,
    integral_const_mul]
  rw [← Finset.mul_sum]
  ring

/-- Exact comparison between an unnormalized input family and its normalized
off-diagonal representative.  The restriction `n ≥ 2` is essential only for
the singleton-congruence step. -/
theorem primitiveKernel_eq_pow_mul_normalized
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 2 ≤ n)
    {C : ℝ} (hC : 0 < C)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    primitiveKernel ρ lam ε n (by omega) G z w =
      C ^ (2 * n - 1) *
        primitiveKernel ρ lam ε n (by omega)
          (fun j =>
            normalizedOffDiagonalRepresentative C (G j))
          z w := by
  rw [primitiveKernel_offDiagonalRepresentative
    ρ lam ε n hn G z w]
  have hfamily :
      (fun j : Fin (2 * n - 1) =>
        offDiagonalRepresentative (G j)) =
      (fun j u =>
        C * normalizedOffDiagonalRepresentative C (G j) u) := by
    funext j u
    unfold normalizedOffDiagonalRepresentative
    field_simp
  rw [hfamily, primitiveKernel_const_mul]

/-! ## The free Green input -/

/-- The constant from the paper's free Green estimate supplies the exact
off-diagonal input bound used by normalization. -/
theorem greenFn_abs_le_mul_invSqKer
    {C : ℝ}
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ C / torusDistSq z)
    (z : T4) (hz : z ≠ 0) :
    |greenFn z| ≤ C * invSqKer z := by
  have hdist : torusDistSq z ≠ 0 := by
    intro hzero
    exact hz ((torusDistSq_eq_zero_iff z).mp hzero)
  simpa only [abs_of_nonneg (greenFn_nonneg z),
    invSqKer, div_eq_mul_inv] using hgreen z hdist

/-- A positive constant in the off-diagonal Green estimate produces an
admissible family for Proposition 4.1 at every order. -/
theorem normalizedGreenFn_admissible
    (n : ℕ) {C : ℝ} (hC : 0 < C)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ C / torusDistSq z) :
    IsAdmissiblePrimitiveInput n
      (fun _ =>
        normalizedOffDiagonalRepresentative C greenFn) := by
  apply normalizedOffDiagonalRepresentative_admissible
    (C := fun _ : Fin (2 * n - 1) => C)
  · intro _
    exact hC
  · intro _
    exact greenFn_memE
  · intro _ z hz
    exact greenFn_abs_le_mul_invSqKer hgreen z hz

/-- Proposition 4.1 applied to the normalized Green representative gives a
fully explicit bound for the actual free-Green primitive kernel.  The factor
`Cgreen^(2n-1)` is the exact cost of undoing the input normalization. -/
theorem primitiveKernelDiff_greenFn_le_scaledMajorant
    (ρ : SmoothCutoff)
    {orderConstant supportConstant Cprop Cgreen lam ε : ℝ}
    {n : ℕ} (hn : 2 ≤ n)
    (hCgreen : 0 < Cgreen)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ Cgreen / torusDistSq z)
    (hprop41 :
      Prop41BoundPredicate ρ lam ε n (by omega)
        (fun _ =>
          normalizedOffDiagonalRepresentative Cgreen greenFn)
        orderConstant supportConstant Cprop)
    (hreg :
      PrimitiveEstimateRegime n lam ε
        orderConstant supportConstant Cprop)
    (z : T4) :
    |primitiveKernelDiff ρ lam ε n (by omega)
        (fun _ => greenFn) z| ≤
      Cgreen ^ (2 * n - 1) *
        primitiveKernelMajorant Cprop lam ε
          supportConstant n z := by
  obtain ⟨_hmem, _hinserted, hbounds⟩ :=
    hprop41 hreg
      (normalizedGreenFn_admissible n hCgreen hgreen)
  unfold primitiveKernelDiff
  rw [primitiveKernel_eq_pow_mul_normalized
    ρ lam ε n hn hCgreen (fun _ => greenFn) z 0,
    abs_mul, abs_of_nonneg (pow_nonneg hCgreen.le _)]
  exact mul_le_mul_of_nonneg_left
    (by
      simpa only [primitiveKernelDiff, sub_zero] using
        (hbounds z).1)
    (pow_nonneg hCgreen.le _)

/-- R-322 terminal-sum form of
`primitiveKernelDiff_greenFn_le_scaledMajorant`. -/
theorem sum_detJ_primitive_le_scaledMajorant
    (ρ : SmoothCutoff)
    {orderConstant supportConstant Cprop Cgreen lam ε : ℝ}
    {n : ℕ} (hn : 2 ≤ n)
    (hCgreen : 0 < Cgreen)
    (hgreen : ∀ z : T4, torusDistSq z ≠ 0 →
      greenFn z ≤ Cgreen / torusDistSq z)
    (hprop41 :
      Prop41BoundPredicate ρ lam ε n (by omega)
        (fun _ =>
          normalizedOffDiagonalRepresentative Cgreen greenFn)
        orderConstant supportConstant Cprop)
    (hreg :
      PrimitiveEstimateRegime n lam ε
        orderConstant supportConstant Cprop)
    (z : T4) :
    |∑ σ ∈ primitiveFullPairings n,
        detJ ρ lam ε n σ z 0| ≤
      Cgreen ^ (2 * n - 1) *
        primitiveKernelMajorant Cprop lam ε
          supportConstant n z := by
  rw [sum_detJ_primitive_eq_primitiveKernel
    ρ lam ε n (by omega) z 0]
  simpa only [primitiveKernelDiff, sub_zero] using
    primitiveKernelDiff_greenFn_le_scaledMajorant
      ρ hn hCgreen hgreen hprop41 hreg z

end

end Anderson4D
