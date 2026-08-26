import Anderson4D.DetParametrix.Paper42_Moment.R324CertifiedTwoHalfPhysicalCollapse

/-!
# Endpoint-erased Phase-A boundary for R-324

Paper (4.19) integrates the four external variables before the nested
cross-cut reductions which produce (4.20).  Accordingly, this file only
separates the two boundary slots of each completed within-half production
chain from its endpoint-independent interior slots.

No absolute value is taken here.  The signed kernels produced by the
within-half Proposition 4.1 iteration remain untouched.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- The actual scale family stored at the terminal constructor of a
certified Phase-A trace. -/
def terminalScale
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) :
    Fin (m + 1) → ℝ :=
  match trace with
  | .terminal _ terminalScale _ _ => terminalScale
  | @R324WithinHalfCertifiedAnalyticTrace.step
      _ _ _ _ _
      _ _ _ _ _ _ _ _ next => next.terminalScale

/-- The terminal edge certificate carried by a certified Phase-A trace. -/
theorem terminalCertificate
    {res :
      R324WithinHalfResidualPrefix ρ lam ε pairing}
    {scale : Fin (m + 1) → ℝ}
    (trace :
      R324WithinHalfCertifiedAnalyticTrace res scale) :
    R324WithinHalfEdgeCertificate
      trace.terminalPrefix.state trace.terminalScale :=
  match trace with
  | .terminal _ _ _ certificate => certificate
  | @R324WithinHalfCertifiedAnalyticTrace.step
      _ _ _ _ _
      _ _ _ _ _ _ _ _ next => next.terminalCertificate

end R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- The active slot leaving the last surviving internal vertex.  This is
the outgoing external boundary slot of a completed half-chain. -/
def terminalOutgoingEdgeSlot
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    Fin (m + 1) :=
  r324InternalVertexEdgeSlot
    (res.state.active.max' hactive)

theorem terminalOutgoingEdgeSlot_ne_zero
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    res.terminalOutgoingEdgeSlot hactive ≠ 0 := by
  intro hzero
  have hval := congrArg Fin.val hzero
  simp only [terminalOutgoingEdgeSlot,
    r324InternalVertexEdgeSlot, Fin.val_zero] at hval
  omega

theorem terminalOutgoingEdgeSlot_mem_activeEdgeSlots
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    res.terminalOutgoingEdgeSlot hactive ∈
      res.activeEdgeSlots := by
  apply res.internalVertexEdgeSlot_mem_activeEdgeSlots
  exact Finset.max'_mem res.state.active hactive

/-- Active signed chain slots after deleting the incoming and outgoing
external boundary slots. -/
def endpointErasedActiveEdgeSlots
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    Finset (Fin (m + 1)) :=
  (res.activeEdgeSlots.erase 0).erase
    (res.terminalOutgoingEdgeSlot hactive)

/-- The signed terminal interior chain.  Its slot set contains neither
external boundary edge.  Endpoint independence of the displayed
displacements is proved separately from this multiplicative ledger. -/
def endpointErasedSignedChain
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  ∏ edge ∈ res.endpointErasedActiveEdgeSlots hactive,
    res.residualChainEdgeFactor x y v edge

/-- Incoming signed boundary factor of one completed half-chain. -/
def incomingBoundaryFactor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  res.residualChainEdgeFactor x y v 0

/-- Outgoing signed boundary factor of one completed half-chain. -/
def outgoingBoundaryFactor
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) : ℝ :=
  res.residualChainEdgeFactor x y v
    (res.terminalOutgoingEdgeSlot hactive)

/-- Exact signed decomposition of a completed half-chain into its two
external boundary factors and the endpoint-erased interior product. -/
theorem residualChainProduct_eq_boundary_mul_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (x y : T4) (v : Fin m → T4) :
    res.residualChainProduct x y v =
      res.incomingBoundaryFactor x y v *
        res.outgoingBoundaryFactor hactive x y v *
        res.endpointErasedSignedChain hactive x y v := by
  unfold residualChainProduct
  calc
    (∏ edge, res.residualChainEdgeFactor x y v edge) =
        ∏ edge ∈ res.activeEdgeSlots,
          res.residualChainEdgeFactor x y v edge := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro edge _hedgeUniv hedge
      unfold residualChainEdgeFactor
      rw [if_neg hedge]
    _ =
        res.residualChainEdgeFactor x y v 0 *
          res.residualChainEdgeFactor x y v
            (res.terminalOutgoingEdgeSlot hactive) *
          (∏ edge ∈
              res.endpointErasedActiveEdgeSlots hactive,
            res.residualChainEdgeFactor x y v edge) := by
      have houtNe :
          res.terminalOutgoingEdgeSlot hactive ≠ 0 :=
        res.terminalOutgoingEdgeSlot_ne_zero hactive
      have houtMem :
          res.terminalOutgoingEdgeSlot hactive ∈
            res.activeEdgeSlots.erase 0 :=
        Finset.mem_erase.mpr
          ⟨houtNe,
            res.terminalOutgoingEdgeSlot_mem_activeEdgeSlots
              hactive⟩
      have hzeroSplit :=
        Finset.mul_prod_erase res.activeEdgeSlots
          (fun edge =>
            res.residualChainEdgeFactor x y v edge)
          res.zero_mem_activeEdgeSlots
      have houtSplit :=
        Finset.mul_prod_erase
          (res.activeEdgeSlots.erase 0)
          (fun edge =>
            res.residualChainEdgeFactor x y v edge)
          houtMem
      rw [← hzeroSplit, ← houtSplit]
      simp only [endpointErasedActiveEdgeSlots, mul_assoc]
    _ = _ := rfl

/-- Product of the certified scales on the endpoint-erased active slots. -/
def endpointErasedScaleProduct
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (scale : Fin (m + 1) → ℝ) : ℝ :=
  ∏ edge ∈ res.endpointErasedActiveEdgeSlots hactive,
    scale edge

/-- The scale ledger uses exactly the same two-boundary slot partition as
the signed chain identity. -/
theorem activeEdgeScaleProduct_eq_boundary_mul_endpointErased
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (scale : Fin (m + 1) → ℝ) :
    (∏ edge ∈ res.activeEdgeSlots, scale edge) =
      scale 0 *
        scale (res.terminalOutgoingEdgeSlot hactive) *
        res.endpointErasedScaleProduct hactive scale := by
  have houtNe :
      res.terminalOutgoingEdgeSlot hactive ≠ 0 :=
    res.terminalOutgoingEdgeSlot_ne_zero hactive
  have houtMem :
      res.terminalOutgoingEdgeSlot hactive ∈
        res.activeEdgeSlots.erase 0 :=
    Finset.mem_erase.mpr
      ⟨houtNe,
        res.terminalOutgoingEdgeSlot_mem_activeEdgeSlots
          hactive⟩
  have hzeroSplit :=
    Finset.mul_prod_erase res.activeEdgeSlots scale
      res.zero_mem_activeEdgeSlots
  have houtSplit :=
    Finset.mul_prod_erase
      (res.activeEdgeSlots.erase 0) scale houtMem
  rw [← hzeroSplit, ← houtSplit]
  simp only [endpointErasedScaleProduct, endpointErasedActiveEdgeSlots, mul_assoc]

end R324WithinHalfResidualPrefix

end

end Anderson4D
