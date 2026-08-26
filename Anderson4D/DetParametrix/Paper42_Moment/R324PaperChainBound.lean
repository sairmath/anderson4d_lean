import Anderson4D.DetParametrix.Paper42_Moment.R324WithinHalfQuantitativeStep
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperCentralGap
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointErasedPhaseABoundary

/-!
# The terminal half chain, bounded leg by leg

Paper: R-324 — §4.2 Step 3, the chain side of the one-head factorization

At a terminal within-half prefix every scheduled subinterval has been
removed, so no outgoing slot is reserved and the chain product is the
plain product of the current edge kernels over the active slots.  The
slotwise certificate `R324WithinHalfEdgeCertificate` bounds each of those
kernels by `scale · |z|⁻²`, so the whole chain is bounded by a scale
product times a product of `|z|⁻²` legs.

That product of legs is precisely what the nested one-head factorization
needs on the chain side: the block's own edges plus the two boundary
edges of `ctx.connector`, with the cut edge absent and compensated by the
central gap factor (`R324PaperCentralGap`).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- At a terminal prefix no outgoing slot is reserved, so every active
chain slot carries its current edge kernel. -/
theorem residualChainEdgeFactor_terminal
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hterminal : res.remaining = [])
    (x y : T4) (v : Fin m → T4) {edge : Fin (m + 1)}
    (hedge : edge ∈ res.activeEdgeSlots) :
    res.residualChainEdgeFactor x y v edge =
      res.state.edges edge (res.edgeDisplacement x y v edge) := by
  unfold residualChainEdgeFactor
  rw [if_pos hedge, if_neg]
  intro hmem
  rw [remainingOutgoingSlots, hterminal] at hmem
  simp at hmem

/-- The terminal chain product is the plain product over the active
slots. -/
theorem residualChainProduct_terminal
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hterminal : res.remaining = [])
    (x y : T4) (v : Fin m → T4) :
    res.residualChainProduct x y v =
      ∏ edge ∈ res.activeEdgeSlots,
        res.state.edges edge (res.edgeDisplacement x y v edge) := by
  classical
  unfold residualChainProduct
  rw [← Finset.prod_subset (Finset.subset_univ res.activeEdgeSlots)
    (fun edge _ hedge => by
      unfold residualChainEdgeFactor
      rw [if_neg hedge])]
  exact Finset.prod_congr rfl fun edge hedge =>
    res.residualChainEdgeFactor_terminal hterminal x y v hedge

/-- **The terminal half chain, bounded leg by leg.**

Every active slot's kernel obeys the slotwise certificate, so the chain
product is dominated by the product of the slot scales times the product
of the `|z|⁻²` legs at the corresponding displacements.  The displacement
hypothesis is the off-diagonal one the certificate needs. -/
theorem abs_residualChainProduct_le
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    {scale : Fin (m + 1) → ℝ}
    (cert : R324WithinHalfEdgeCertificate res.state scale)
    (hterminal : res.remaining = [])
    (x y : T4) (v : Fin m → T4)
    (hne : ∀ edge ∈ res.activeEdgeSlots,
      res.edgeDisplacement x y v edge ≠ 0) :
    |res.residualChainProduct x y v| ≤
      (∏ edge ∈ res.activeEdgeSlots, scale edge) *
        ∏ edge ∈ res.activeEdgeSlots,
          invSqKer (res.edgeDisplacement x y v edge) := by
  classical
  rw [res.residualChainProduct_terminal hterminal x y v, Finset.abs_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun edge _ => abs_nonneg _) ?_
  intro edge hedge
  exact cert.bound edge _ (hne edge hedge)

/-- **The endpoint-erased terminal half chain, bounded leg by leg.**

Paper Step 3 starts only after the two external boundary slots of each half
have been integrated out.  On the resulting endpoint-erased slot set the
same terminal edge certificate therefore gives the precise product bound
needed by the nested cross-shell partition, without carrying either
external endpoint edge into a `connector`. -/
theorem abs_endpointErasedSignedChain_le
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    {scale : Fin (m + 1) → ℝ}
    (cert : R324WithinHalfEdgeCertificate res.state scale)
    (hterminal : res.remaining = [])
    (x y : T4) (v : Fin m → T4)
    (hne : ∀ edge ∈ res.endpointErasedActiveEdgeSlots hactive,
      res.edgeDisplacement x y v edge ≠ 0) :
    |res.endpointErasedSignedChain hactive x y v| ≤
      res.endpointErasedScaleProduct hactive scale *
        ∏ edge ∈ res.endpointErasedActiveEdgeSlots hactive,
          invSqKer (res.edgeDisplacement x y v edge) := by
  classical
  unfold endpointErasedSignedChain endpointErasedScaleProduct
  rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun edge _ => abs_nonneg _) ?_
  intro edge hedge
  have hedgeActive : edge ∈ res.activeEdgeSlots :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hedge).2).2
  rw [res.residualChainEdgeFactor_terminal
    hterminal x y v hedgeActive]
  exact cert.bound edge _ (hne edge hedge)

end R324WithinHalfResidualPrefix

end

end Anderson4D
