import Anderson4D.DetParametrix.Paper42_Moment.R324TerminalJointIntegrabilityProducer

/-!
# Terminal residual-sum joint integrability for R-324

This module closes the analytic premise isolated by
`R324EndpointJointIntegrabilityAdapter`.  The two completed within-half
Green chains are separately integrable on their endpoint/internal product
spaces.  A measure-preserving regrouping puts their product on the exact
four-endpoint/terminal-coordinate carrier used by the endpoint Fubini
theorem.  The complete residual primitive sum is then attached as one
bounded measurable factor.

No termwise norm of the primitive sum, target integrability certificate, or
moment estimate is assumed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## Measurability of the terminal reconstruction and cross factor -/

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)

/-- Reconstructing the ambient tuple from the surviving coordinates is
measurable for the product measurable spaces. -/
theorem measurable_reconstruct :
    Measurable res.reconstruct := by
  apply measurable_pi_lambda
  intro i
  unfold reconstruct
  split_ifs with hi
  · exact
      measurable_pi_apply
        (⟨i, hi⟩ : res.SurvivingCoordinate)
  · exact measurable_const

end R324WithinHalfResidualPrefix

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The doubled ambient tuple assembled from the two terminal sparse
carriers is measurable. -/
theorem measurable_terminalDoubledReconstruct :
    Measurable terminal.terminalDoubledReconstruct := by
  apply measurable_pi_lambda
  intro k
  generalize hs :
      (momentDoubleFinEquiv m).symm k = s
  cases s with
  | inl i =>
      have hleft :
          Measurable
            (fun p :
                (terminal.left.SurvivingCoordinate → T4) ×
                  (terminal.right.SurvivingCoordinate → T4) =>
              terminal.left.reconstruct p.1) :=
        terminal.left.measurable_reconstruct.comp measurable_fst
      simp only [terminalDoubledReconstruct, hs]
      change
        Measurable
          ((fun f : Fin m → T4 => f i) ∘
            fun p :
                (terminal.left.SurvivingCoordinate → T4) ×
                  (terminal.right.SurvivingCoordinate → T4) =>
              terminal.left.reconstruct p.1)
      exact (measurable_pi_apply i).comp hleft
  | inr j =>
      have hright :
          Measurable
            (fun p :
                (terminal.left.SurvivingCoordinate → T4) ×
                  (terminal.right.SurvivingCoordinate → T4) =>
              terminal.right.reconstruct p.2) :=
        terminal.right.measurable_reconstruct.comp measurable_snd
      simp only [terminalDoubledReconstruct, hs]
      change
        Measurable
          ((fun f : Fin m → T4 => f j) ∘
            fun p :
                (terminal.left.SurvivingCoordinate → T4) ×
                  (terminal.right.SurvivingCoordinate → T4) =>
              terminal.right.reconstruct p.2)
      exact (measurable_pi_apply j).comp hright

/-- The grouped residual primitive sum is measurable on the exact product
of the two terminal sparse carriers. -/
theorem measurable_residualSumCrossFactor
    (π : κp.singles ≃ κm.singles) :
    Measurable
      (fun p :
          (terminal.left.SurvivingCoordinate → T4) ×
            (terminal.right.SurvivingCoordinate → T4) =>
        terminal.residualSumCrossFactor π p.1 p.2) := by
  unfold residualSumCrossFactor
  exact
    Complex.measurable_ofReal.comp
      ((ρ.measurable_r324ResidualPrimitiveSumProduct
          ε κp κm π).comp
        terminal.measurable_terminalDoubledReconstruct)

/-- At positive mollification scale the grouped residual primitive sum has
a uniform norm bound on the terminal product carrier. -/
theorem exists_norm_residualSumCrossFactor_le
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (π : κp.singles ≃ κm.singles) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ p :
          (terminal.left.SurvivingCoordinate → T4) ×
            (terminal.right.SurvivingCoordinate → T4),
        ‖terminal.residualSumCrossFactor π p.1 p.2‖ ≤ bound := by
  obtain ⟨bound, hbound0, hbound⟩ :=
    ρ.exists_norm_r324ResidualPrimitiveSumProduct_le
      hε hε1 κp κm π
  refine ⟨bound, hbound0, ?_⟩
  intro p
  simpa only [residualSumCrossFactor,
    Complex.norm_real] using
    hbound (terminal.terminalDoubledReconstruct p)

end R324TwoHalfTerminalData

/-! ## Exact endpoint/internal product regrouping -/

/-- Move the middle coordinate of a right-associated product to the front.
This local copy keeps the terminal integrability module independent of the
ambient full-tuple regrouping API. -/
private def r324TerminalJI_moveMiddleMeasurableEquiv
    (A B C : Type*) [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] :
    A × (B × C) ≃ᵐ B × (A × C) :=
  (MeasurableEquiv.prodAssoc
      (α := A) (β := B) (γ := C)).symm.trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
      (MeasurableEquiv.refl C)).trans
      (MeasurableEquiv.prodAssoc
        (α := B) (β := A) (γ := C)))

private theorem
    r324TerminalJI_measurePreserving_moveMiddleMeasurableEquiv
    {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (τ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving
      (r324TerminalJI_moveMiddleMeasurableEquiv A B C)
      (μ.prod (ν.prod τ))
      (ν.prod (μ.prod τ)) := by
  exact
    (measurePreserving_prodAssoc ν μ τ).comp
      (((Measure.measurePreserving_swap
          (μ := μ) (ν := ν)).prod
        (MeasurePreserving.id τ)).comp
          (measurePreserving_prodAssoc μ ν τ).symm)

/-- Regroup
`((x,y,z,w),(vₗ,vᵣ))` as the two independent triples
`((x,y,vₗ),(z,w,vᵣ))`. -/
private def r324TerminalJI_endpointInternalSplitMeasurableEquiv
    (L R : Type*) [MeasurableSpace L] [MeasurableSpace R] :
    (T4 × (T4 × (T4 × T4))) × (L × R) ≃ᵐ
      (T4 × (T4 × L)) × (T4 × (T4 × R)) :=
  ((MeasurableEquiv.prodAssoc
      (α := T4) (β := T4 × (T4 × T4))
      (γ := L × R)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      ((MeasurableEquiv.prodAssoc
        (α := T4) (β := T4 × T4)
        (γ := L × R)).trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodAssoc
            (α := T4) (β := T4)
            (γ := L × R)))))).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (r324TerminalJI_moveMiddleMeasurableEquiv
            T4 L R)))).trans
      ((MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (r324TerminalJI_moveMiddleMeasurableEquiv
            T4 L (T4 × R)))).trans
        ((MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodAssoc
            (α := T4) (β := L)
            (γ := T4 × (T4 × R))).symm).trans
          (MeasurableEquiv.prodAssoc
            (α := T4)
            (β := T4 × L)
            (γ := T4 × (T4 × R)).symm))))

@[simp]
private theorem
    r324TerminalJI_endpointInternalSplitMeasurableEquiv_apply
    (L R : Type*) [MeasurableSpace L] [MeasurableSpace R]
    (p : (T4 × (T4 × (T4 × T4))) × (L × R)) :
    r324TerminalJI_endpointInternalSplitMeasurableEquiv L R p =
      ((p.1.1, p.1.2.1, p.2.1),
        (p.1.2.2.1, p.1.2.2.2, p.2.2)) := by
  rfl

private theorem
    r324TerminalJI_measurePreserving_endpointInternalSplitMeasurableEquiv
    {L R : Type*} [MeasurableSpace L] [MeasurableSpace R]
    (μL : Measure L) (μR : Measure R)
    [SFinite μL] [SFinite μR] :
    MeasurePreserving
      (r324TerminalJI_endpointInternalSplitMeasurableEquiv L R)
      ((paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod paperMeasure))).prod
        (μL.prod μR))
      ((paperMeasure.prod (paperMeasure.prod μL)).prod
        (paperMeasure.prod (paperMeasure.prod μR))) := by
  have h0a :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc
          (α := T4) (β := T4 × (T4 × T4))
          (γ := L × R))
        ((paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod paperMeasure))).prod
          (μL.prod μR))
        (paperMeasure.prod
          ((paperMeasure.prod
              (paperMeasure.prod paperMeasure)).prod
            (μL.prod μR))) :=
    measurePreserving_prodAssoc paperMeasure
      (paperMeasure.prod (paperMeasure.prod paperMeasure))
      (μL.prod μR)
  have h0b :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          ((MeasurableEquiv.prodAssoc
            (α := T4) (β := T4 × T4)
            (γ := L × R)).trans
            (MeasurableEquiv.prodCongr
              (MeasurableEquiv.refl T4)
              (MeasurableEquiv.prodAssoc
                (α := T4) (β := T4)
                (γ := L × R)))))
        (paperMeasure.prod
          ((paperMeasure.prod
              (paperMeasure.prod paperMeasure)).prod
            (μL.prod μR)))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod (μL.prod μR))))) := by
    exact
      (MeasurePreserving.id paperMeasure).prod
        (((MeasurePreserving.id paperMeasure).prod
          (measurePreserving_prodAssoc
            paperMeasure paperMeasure (μL.prod μR))).comp
          (measurePreserving_prodAssoc paperMeasure
            (paperMeasure.prod paperMeasure)
            (μL.prod μR)))
  have h1 :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (MeasurableEquiv.prodCongr
              (MeasurableEquiv.refl T4)
              (r324TerminalJI_moveMiddleMeasurableEquiv
                T4 L R))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod (μL.prod μR)))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (μL.prod (paperMeasure.prod μR))))) :=
    (MeasurePreserving.id paperMeasure).prod
      ((MeasurePreserving.id paperMeasure).prod
        ((MeasurePreserving.id paperMeasure).prod
          (r324TerminalJI_measurePreserving_moveMiddleMeasurableEquiv
            paperMeasure μL μR)))
  have h2 :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.refl T4)
            (r324TerminalJI_moveMiddleMeasurableEquiv
              T4 L (T4 × R))))
        (paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod
              (μL.prod (paperMeasure.prod μR)))))
        (paperMeasure.prod
          (paperMeasure.prod
            (μL.prod
              (paperMeasure.prod
                (paperMeasure.prod μR))))) :=
    (MeasurePreserving.id paperMeasure).prod
      ((MeasurePreserving.id paperMeasure).prod
        (r324TerminalJI_measurePreserving_moveMiddleMeasurableEquiv
          paperMeasure μL (paperMeasure.prod μR)))
  have h3 :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (MeasurableEquiv.prodAssoc
            (α := T4) (β := L)
            (γ := T4 × (T4 × R))).symm)
        (paperMeasure.prod
          (paperMeasure.prod
            (μL.prod
              (paperMeasure.prod
                (paperMeasure.prod μR)))))
        (paperMeasure.prod
          ((paperMeasure.prod μL).prod
            (paperMeasure.prod
              (paperMeasure.prod μR)))) :=
    (MeasurePreserving.id paperMeasure).prod
      (measurePreserving_prodAssoc
        paperMeasure μL
        (paperMeasure.prod (paperMeasure.prod μR))).symm
  have h4 :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc
          (α := T4) (β := T4 × L)
          (γ := T4 × (T4 × R)).symm)
        (paperMeasure.prod
          ((paperMeasure.prod μL).prod
            (paperMeasure.prod
              (paperMeasure.prod μR))))
        ((paperMeasure.prod (paperMeasure.prod μL)).prod
          (paperMeasure.prod
            (paperMeasure.prod μR))) :=
    (measurePreserving_prodAssoc paperMeasure
      (paperMeasure.prod μL)
      (paperMeasure.prod (paperMeasure.prod μR))).symm
  simpa only [
    r324TerminalJI_endpointInternalSplitMeasurableEquiv,
    MeasurableEquiv.coe_trans, Function.comp_assoc] using
      h4.comp (h3.comp (h2.comp (h1.comp (h0b.comp h0a))))

/-! ## The genuine producer -/

namespace R324TwoHalfTerminalData

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    (terminal : R324TwoHalfTerminalData ρ lam ε κp κm)

/-- The two certified terminal half chains are jointly integrable on the
literal four-endpoint/terminal-coordinate carrier.  This is the reusable
bare analytic core of the residual-sum producer below: no covariance or
selector factor has yet been attached. -/
theorem terminalChainProductsJointIntegrable_of_edgeCertificates
    (leftScale rightScale : Fin (m + 1) → ℝ)
    (hleftCertificate :
      R324WithinHalfEdgeCertificate
        terminal.left.state leftScale)
    (hrightCertificate :
      R324WithinHalfEdgeCertificate
        terminal.right.state rightScale) :
    Integrable
      (fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
        (terminal.left.residualChainProduct
            ep.1.1 ep.1.2.1
            (terminal.left.reconstruct ep.2.1) : ℂ) *
          (terminal.right.residualChainProduct
            ep.1.2.2.1 ep.1.2.2.2
            (terminal.right.reconstruct ep.2.2) : ℂ))
      ((paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod paperMeasure))).prod
        ((Measure.pi fun _ :
            terminal.left.SurvivingCoordinate => paperMeasure).prod
          (Measure.pi fun _ :
            terminal.right.SurvivingCoordinate => paperMeasure))) := by
  let μL :=
    Measure.pi fun _ :
      terminal.left.SurvivingCoordinate => paperMeasure
  let μR :=
    Measure.pi fun _ :
      terminal.right.SurvivingCoordinate => paperMeasure
  have hleftReal :=
    terminal.left.integrable_terminalResidualChainProduct
      terminal.left_remaining leftScale hleftCertificate
  have hrightReal :=
    terminal.right.integrable_terminalResidualChainProduct
      terminal.right_remaining rightScale hrightCertificate
  have hsource :
      Integrable
        (fun p :
            (T4 × (T4 ×
              (terminal.left.SurvivingCoordinate → T4))) ×
              (T4 × (T4 ×
                (terminal.right.SurvivingCoordinate → T4))) =>
          (terminal.left.residualChainProduct
              p.1.1 p.1.2.1
              (terminal.left.reconstruct p.1.2.2) : ℂ) *
            (terminal.right.residualChainProduct
              p.2.1 p.2.2.1
              (terminal.right.reconstruct p.2.2.2) : ℂ))
        ((paperMeasure.prod (paperMeasure.prod μL)).prod
          (paperMeasure.prod (paperMeasure.prod μR))) := by
    exact hleftReal.ofReal.mul_prod hrightReal.ofReal
  let e :=
    r324TerminalJI_endpointInternalSplitMeasurableEquiv
      (terminal.left.SurvivingCoordinate → T4)
      (terminal.right.SurvivingCoordinate → T4)
  have hp :
      MeasurePreserving e
        ((paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod paperMeasure))).prod
          (μL.prod μR))
        ((paperMeasure.prod (paperMeasure.prod μL)).prod
          (paperMeasure.prod (paperMeasure.prod μR))) := by
    simpa only [e, μL, μR] using
      r324TerminalJI_measurePreserving_endpointInternalSplitMeasurableEquiv
        μL μR
  have htransport :
      Integrable
        ((fun p :
            (T4 × (T4 ×
              (terminal.left.SurvivingCoordinate → T4))) ×
              (T4 × (T4 ×
                (terminal.right.SurvivingCoordinate → T4))) =>
          (terminal.left.residualChainProduct
              p.1.1 p.1.2.1
              (terminal.left.reconstruct p.1.2.2) : ℂ) *
            (terminal.right.residualChainProduct
              p.2.1 p.2.2.1
              (terminal.right.reconstruct p.2.2.2) : ℂ)) ∘ e)
        ((paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod paperMeasure))).prod
          (μL.prod μR)) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hsource
  change
    Integrable
      (fun ep :
          (T4 × (T4 × (T4 × T4))) ×
            ((terminal.left.SurvivingCoordinate → T4) ×
              (terminal.right.SurvivingCoordinate → T4)) =>
        (terminal.left.residualChainProduct
            ep.1.1 ep.1.2.1
            (terminal.left.reconstruct ep.2.1) : ℂ) *
          (terminal.right.residualChainProduct
            ep.1.2.2.1 ep.1.2.2.2
            (terminal.right.reconstruct ep.2.2) : ℂ))
      ((paperMeasure.prod
          (paperMeasure.prod
            (paperMeasure.prod paperMeasure))).prod
        (μL.prod μR))
  apply htransport.congr
  filter_upwards with ep
  rfl

/-- The two terminal edge certificates and positive-scale covariance bound
produce the exact unphased joint-integrability premise of the endpoint
adapter. -/
theorem terminalResidualSumJointIntegrable_of_edgeCertificates
    (π : κp.singles ≃ κm.singles)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (leftScale rightScale : Fin (m + 1) → ℝ)
    (hleftCertificate :
      R324WithinHalfEdgeCertificate
        terminal.left.state leftScale)
    (hrightCertificate :
      R324WithinHalfEdgeCertificate
        terminal.right.state rightScale) :
    terminal.TerminalResidualSumJointIntegrable π := by
  let μL :=
    Measure.pi fun _ :
      terminal.left.SurvivingCoordinate => paperMeasure
  let μR :=
    Measure.pi fun _ :
      terminal.right.SurvivingCoordinate => paperMeasure
  have hbare :
      Integrable
        (fun ep :
            (T4 × (T4 × (T4 × T4))) ×
              ((terminal.left.SurvivingCoordinate → T4) ×
                (terminal.right.SurvivingCoordinate → T4)) =>
          (terminal.left.residualChainProduct
              ep.1.1 ep.1.2.1
              (terminal.left.reconstruct ep.2.1) : ℂ) *
            (terminal.right.residualChainProduct
              ep.1.2.2.1 ep.1.2.2.2
              (terminal.right.reconstruct ep.2.2) : ℂ))
        ((paperMeasure.prod
            (paperMeasure.prod
              (paperMeasure.prod paperMeasure))).prod
          (μL.prod μR)) := by
    simpa only [μL, μR] using
      terminal.terminalChainProductsJointIntegrable_of_edgeCertificates
        leftScale rightScale hleftCertificate hrightCertificate
  obtain ⟨bound, _hbound0, hbound⟩ :=
    terminal.exists_norm_residualSumCrossFactor_le
      hε hε1 π
  have hcrossMeas :
      Measurable
        (fun ep :
            (T4 × (T4 × (T4 × T4))) ×
              ((terminal.left.SurvivingCoordinate → T4) ×
                (terminal.right.SurvivingCoordinate → T4)) =>
          terminal.residualSumCrossFactor
            π ep.2.1 ep.2.2) :=
    (terminal.measurable_residualSumCrossFactor π).comp
      measurable_snd
  have hwithCross :=
    hbare.mul_bdd hcrossMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ep =>
        hbound ep.2)
  unfold TerminalResidualSumJointIntegrable
  apply hwithCross.congr
  filter_upwards with ep
  unfold terminalResidualSumPhysicalCore
  rw [terminal.left_residualIntegrand_eq_chain,
    terminal.right_residualIntegrand_eq_chain]

/-- Specialization of the preceding producer to the terminal data packaged
by two certified within-half traces. -/
theorem terminalResidualSumJointIntegrable_ofCertifiedTraces
    {leftRes :
      R324WithinHalfResidualPrefix ρ lam ε κp}
    {rightRes :
      R324WithinHalfResidualPrefix ρ lam ε κm}
    {leftInitialScale rightInitialScale :
      Fin (m + 1) → ℝ}
    (leftTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        leftRes leftInitialScale)
    (rightTrace :
      R324WithinHalfResidualPrefix.R324WithinHalfCertifiedAnalyticTrace
        rightRes rightInitialScale)
    (π : κp.singles ≃ κm.singles)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (leftTerminalScale rightTerminalScale :
      Fin (m + 1) → ℝ)
    (hleftCertificate :
      R324WithinHalfEdgeCertificate
        leftTrace.terminalPrefix.state leftTerminalScale)
    (hrightCertificate :
      R324WithinHalfEdgeCertificate
        rightTrace.terminalPrefix.state rightTerminalScale) :
    (R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace).TerminalResidualSumJointIntegrable π :=
  (R324TwoHalfTerminalData.ofCertifiedTraces
      leftTrace rightTrace).terminalResidualSumJointIntegrable_of_edgeCertificates
    π hε hε1 leftTerminalScale rightTerminalScale
    hleftCertificate hrightCertificate

end R324TwoHalfTerminalData

end

end Anderson4D
