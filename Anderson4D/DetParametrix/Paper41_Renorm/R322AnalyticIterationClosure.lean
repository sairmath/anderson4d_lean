import Anderson4D.DetParametrix.Paper41_Renorm.R322OneBlockCollapse
import Anderson4D.Continuum.PrimitiveProposition41

/-!
# Analytic iteration closure for R-322

Paper Section 4.1 replaces different chain edges by collapsed kernels carrying
different normalization constants.  A common normalization would raise the
largest such constant to the number of surviving chain edges and would destroy
the exact perturbative-order ledger.  This file therefore first proves the
heterogeneous scaling identity: one scale factor is extracted from each chain
edge, and no scale is counted twice.

The resulting Proposition 4.1 interface is the terminal analytic operation in
the successive interval reduction.  The actual selector/Fubini routing is kept
separate from this normalization ledger.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Heterogeneous scaling of primitive chain inputs -/

/-- Multiplying the `j`-th primitive-chain input by its own scalar `A j`
extracts exactly the product of the edge scalars. -/
theorem primitiveChainProduct_family_mul
    (n : ℕ) (hn : 1 ≤ n)
    (A : Fin (2 * n - 1) → ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (x : Fin (2 * n) → T4) :
    primitiveChainProduct n hn
        (fun j z => A j * G j z) x =
      (∏ j, A j) *
        primitiveChainProduct n hn G x := by
  unfold primitiveChainProduct
  rw [Finset.prod_mul_distrib]

/-- Heterogeneous edge scaling at the primitive-integrand level. -/
theorem primitiveIntegrand_family_mul
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (A : Fin (2 * n - 1) → ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) :
    primitiveIntegrand ρ ε n hn
        (fun j z => A j * G j z) κ x =
      (∏ j, A j) *
        primitiveIntegrand ρ ε n hn G κ x := by
  unfold primitiveIntegrand
  rw [primitiveChainProduct_family_mul]
  ring

/-- Heterogeneous edge scaling at the two-endpoint primitive-kernel level. -/
theorem primitiveKernel_family_mul
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 1 ≤ n)
    (A : Fin (2 * n - 1) → ℝ)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    primitiveKernel ρ lam ε n hn
        (fun j u => A j * G j u) z w =
      (∏ j, A j) *
        primitiveKernel ρ lam ε n hn G z w := by
  unfold primitiveKernel
  simp_rw [primitiveIntegrand_family_mul,
    integral_const_mul]
  rw [← Finset.mul_sum]
  ring

/-! ## Exact edgewise normalization -/

/-- Off the diagonal, an input is exactly its positive normalization
constant times its normalized representative. -/
theorem mul_normalizedOffDiagonalRepresentative_eq
    {C : ℝ} (hC : 0 < C) (f : T4 → ℝ)
    {z : T4} (hz : z ≠ 0) :
    C * normalizedOffDiagonalRepresentative C f z =
      f z := by
  rw [normalizedOffDiagonalRepresentative,
    offDiagonalRepresentative_eq f hz]
  field_simp

/-- At primitive order at least two, an arbitrary positive normalization
constant can be extracted independently from every chain edge.

The order restriction is exactly the one needed for the null-diagonal
congruence: at order one there are no internal variables, so the endpoint
diagonal must instead be handled by the explicit order-one theorem. -/
theorem primitiveKernel_eq_prod_mul_normalizedFamily
    (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (hn : 2 ≤ n)
    (C : Fin (2 * n - 1) → ℝ)
    (hC : ∀ j, 0 < C j)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (z w : T4) :
    primitiveKernel ρ lam ε n (by omega) G z w =
      (∏ j, C j) *
        primitiveKernel ρ lam ε n (by omega)
          (fun j =>
            normalizedOffDiagonalRepresentative
              (C j) (G j))
          z w := by
  calc
    primitiveKernel ρ lam ε n (by omega) G z w =
        primitiveKernel ρ lam ε n (by omega)
          (fun j u =>
            C j *
              normalizedOffDiagonalRepresentative
                (C j) (G j) u)
          z w := by
      apply primitiveKernel_congr_offDiagonal
        ρ lam ε n hn
      intro j u hu
      exact
        (mul_normalizedOffDiagonalRepresentative_eq
          (hC j) (G j) hu).symm
    _ =
        (∏ j, C j) *
          primitiveKernel ρ lam ε n (by omega)
            (fun j =>
              normalizedOffDiagonalRepresentative
                (C j) (G j))
            z w :=
      primitiveKernel_family_mul
        ρ lam ε n (by omega) C
          (fun j =>
            normalizedOffDiagonalRepresentative
              (C j) (G j))
          z w

/-! ## Terminal Proposition 4.1 with exact edge scales -/

/-- Proposition 4.1 applied after edgewise normalization.

Each surviving generalized chain edge contributes its own factor `Cedge j`
exactly once.  This is the terminal estimate needed after all proper
primitive blocks in paper (4.13) have been removed. -/
theorem primitiveKernelDiff_le_prod_edgeScales_mul_majorant
    (ρ : SmoothCutoff)
    {lam ε supportConstant primitiveConstant : ℝ}
    {n : ℕ} (hn : 2 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (Cedge : Fin (2 * n - 1) → ℝ)
    (hCedge : ∀ j, 0 < Cedge j)
    (hmem : ∀ j, MemEClassT4 (G j))
    (hbound : ∀ j z, z ≠ 0 →
      |G j z| ≤ Cedge j * invSqKer z)
    (hprop :
      ∀ (H : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n H →
          MemEClassT4
              (primitiveKernelDiff
                ρ lam ε n (by omega) H) ∧
            MemEClassT4
              (primitiveKernelInsertedDiff
                ρ lam ε n (by omega) H) ∧
            PrimitiveKernelBounds
              ρ lam ε n (by omega) H
                supportConstant primitiveConstant)
    (z : T4) :
    |primitiveKernelDiff ρ lam ε n (by omega) G z| ≤
      (∏ j, Cedge j) *
        primitiveKernelMajorant
          primitiveConstant lam ε supportConstant n z := by
  let H : Fin (2 * n - 1) → T4 → ℝ :=
    fun j =>
      normalizedOffDiagonalRepresentative
        (Cedge j) (G j)
  have hinput : IsAdmissiblePrimitiveInput n H :=
    normalizedOffDiagonalRepresentative_admissible
      hCedge hmem hbound
  have hbounds :
      PrimitiveKernelBounds
        ρ lam ε n (by omega) H
          supportConstant primitiveConstant :=
    (hprop H hinput).2.2
  have hprod : 0 ≤ ∏ j, Cedge j :=
    Finset.prod_nonneg fun j _ => (hCedge j).le
  unfold primitiveKernelDiff
  rw [primitiveKernel_eq_prod_mul_normalizedFamily
    ρ lam ε n hn Cedge hCedge G z 0,
    abs_mul, abs_of_nonneg hprod]
  exact mul_le_mul_of_nonneg_left
    (by
      simpa only [H, primitiveKernelDiff, sub_zero] using
        (hbounds z).1)
    hprod

/-- Direct truncation-range specialization of the preceding terminal
estimate to the proved Proposition 4.1. -/
theorem
    exists_primitiveKernelDiff_le_prod_edgeScales_mul_majorant_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant primitiveConstant : ℝ,
      0 < supportConstant ∧ 0 < primitiveConstant ∧
      ∀ (lam ε : ℝ) (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ)
        (Cedge : Fin (2 * n - 1) → ℝ),
        0 < lam → 0 < ε → ε ≤ 1 →
        n ≤ truncOrder ε →
        (∀ j, 0 < Cedge j) →
        (∀ j, MemEClassT4 (G j)) →
        (∀ j z, z ≠ 0 →
          |G j z| ≤ Cedge j * invSqKer z) →
        ∀ z : T4,
          |primitiveKernelDiff
              ρ lam ε n (by omega) G z| ≤
            (∏ j, Cedge j) *
              primitiveKernelMajorant
                primitiveConstant lam ε
                  supportConstant n z := by
  obtain ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, hprop⟩ :=
    proposition41_at_truncation ρ
  refine
    ⟨supportConstant, primitiveConstant,
      hsupport, hprimitiveConstant, ?_⟩
  intro lam ε n hn G Cedge
    hlam hε hε1 hntrunc hCedge hmem hbound z
  apply
    primitiveKernelDiff_le_prod_edgeScales_mul_majorant
      ρ hn G Cedge hCedge hmem hbound
  intro H hinput
  exact
    hprop lam ε n (by omega) H
      hlam hε hε1 hntrunc hinput

/-! ## Exact perturbative ledger for collapsed edge histories -/

/-- Scale carried by one surviving chain edge after the primitive blocks in
`orders` have successively been collapsed into that edge. -/
def r322CollapsedEdgeScale
    (base K C lam : ℝ) (orders : List ℕ) : ℝ :=
  base * K ^ orders.length *
    (C * lam) ^ (2 * orders.sum)

/-- Multiplying all surviving edge scales counts each base edge and each
removed primitive block exactly once. -/
theorem prod_r322CollapsedEdgeScale
    {ι : Type*} [Fintype ι]
    (base : ι → ℝ) (K C lam : ℝ)
    (orders : ι → List ℕ) :
    (∏ i,
        r322CollapsedEdgeScale
          (base i) K C lam (orders i)) =
      (∏ i, base i) *
        K ^ (∑ i, (orders i).length) *
        (C * lam) ^
          (2 * ∑ i, (orders i).sum) := by
  unfold r322CollapsedEdgeScale
  simp only [Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [show
      (∑ i, 2 * (orders i).sum) =
        2 * ∑ i, (orders i).sum by
    rw [Finset.mul_sum]]

/-- A removed-order power combines exactly with the order power already
present in the Proposition 4.1 majorant. -/
theorem pow_mul_primitiveKernelMajorant_eq_order_add
    (C lam ε supportConstant : ℝ)
    (removedOrder terminalOrder : ℕ) (z : T4) :
    (C * lam) ^ (2 * removedOrder) *
        primitiveKernelMajorant
          C lam ε supportConstant terminalOrder z =
      primitiveKernelMajorant
        C lam ε supportConstant
          (removedOrder + terminalOrder) z := by
  unfold primitiveKernelMajorant
  rw [show
      2 * (removedOrder + terminalOrder) =
        2 * removedOrder + 2 * terminalOrder by omega,
    pow_add]
  ring

/-- Terminal ledger after all proper blocks have been routed into the
surviving generalized chain edges.  Apart from the base Green constants and
one universal collapse constant per proper block, the perturbative powers
combine to the sum of removed and terminal primitive orders. -/
theorem prod_r322CollapsedEdgeScale_mul_terminalMajorant
    {ι : Type*} [Fintype ι]
    (base : ι → ℝ) (K C lam ε supportConstant : ℝ)
    (orders : ι → List ℕ)
    (terminalOrder : ℕ) (z : T4) :
    (∏ i,
        r322CollapsedEdgeScale
          (base i) K C lam (orders i)) *
        primitiveKernelMajorant
          C lam ε supportConstant terminalOrder z =
      (∏ i, base i) *
        K ^ (∑ i, (orders i).length) *
        primitiveKernelMajorant
          C lam ε supportConstant
          ((∑ i, (orders i).sum) + terminalOrder) z := by
  rw [prod_r322CollapsedEdgeScale]
  let P : ℝ :=
    (∏ i, base i) *
      K ^ (∑ i, (orders i).length)
  calc
    P * (C * lam) ^ (2 * ∑ i, (orders i).sum) *
          primitiveKernelMajorant
            C lam ε supportConstant terminalOrder z =
        P *
          ((C * lam) ^ (2 * ∑ i, (orders i).sum) *
            primitiveKernelMajorant
              C lam ε supportConstant terminalOrder z) := by
      ring
    _ =
        P *
          primitiveKernelMajorant
            C lam ε supportConstant
            ((∑ i, (orders i).sum) + terminalOrder) z := by
      rw [pow_mul_primitiveKernelMajorant_eq_order_add]
    _ = _ := rfl

end

end Anderson4D
