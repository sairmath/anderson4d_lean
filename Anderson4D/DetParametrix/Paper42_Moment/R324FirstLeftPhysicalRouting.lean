import Anderson4D.DetParametrix.Paper42_Moment.R324SignedPhaseAOneBlockUpdate
import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectedBlockBochnerFubini

/-!
# One genuine first-left routing step for the physical R-324 core

This module starts from the original `deterministicMomentIntegrand`, not
from a packaged post-collapse object.  It reindexes one realized
within-half signature fibre, puts the selected spatial block inside all
complementary coordinates, and forms the complete primitive covariance
sum there before any norm is taken.

This is the exact representation-order step preceding an analytic block
collapse.  The selected-Green factorization through the heterogeneous
`detJWith` input of
`integral_completePrimitiveAtEndpoints_eq_replacementEdge`, together with
the iteration over the other within-half blocks, forms the residual bridge.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Bochner-valued signature routing -/

/-- Bochner-valued form of the exact first-left signature Fubini step.
The selected primitive pairing coordinate is summed inside its selected
spatial integral, while all dependent discrete data and complementary
spatial coordinates remain outside. -/
theorem integral_sum_momentSignatureFiber_eq_firstLeft_selected_bochner
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (Φ :
      MomentSignatureFiberAt e₀ →
        (Fin (2 * m) → T4) → E)
    (hΦ :
      ∀ e,
        Integrable (Φ e)
          (Measure.pi fun _ : Fin (2 * m) =>
            paperMeasure)) :
    (∫ v,
        ∑ e : MomentSignatureFiberAt e₀, Φ e v
        ∂Measure.pi fun _ : Fin (2 * m) =>
          paperMeasure) =
      ∑ ω : R324FirstLeftOuterCoordinate e₀ hleft,
        ∫ vC :
            (i : {i : Fin (2 * m) //
              ¬r324FirstLeftSelected e₀ hleft i}) → T4,
          ∫ vB :
              (i : {i : Fin (2 * m) //
                r324FirstLeftSelected e₀ hleft i}) → T4,
            ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
              Φ (r324FirstLeftReconstruct
                  e₀ hleft ω κB)
                ((MeasurableEquiv.piEquivPiSubtypeProd
                    (fun _ : Fin (2 * m) => T4)
                    (r324FirstLeftSelected e₀ hleft)).symm
                  (vB, vC))
            ∂Measure.pi fun _ :
                {i : Fin (2 * m) //
                  r324FirstLeftSelected e₀ hleft i} =>
              paperMeasure
          ∂Measure.pi fun _ :
              {i : Fin (2 * m) //
                ¬r324FirstLeftSelected e₀ hleft i} =>
            paperMeasure := by
  classical
  let blockTerm :
      R324FirstLeftOuterCoordinate e₀ hleft →
        R324FirstLeftBlockCoordinate e₀ hleft →
          (Fin (2 * m) → T4) → E :=
    fun ω κB =>
      Φ (r324FirstLeftReconstruct e₀ hleft ω κB)
  have hblockTerm :
      ∀ ω κB,
        Integrable (blockTerm ω κB)
          (Measure.pi fun _ : Fin (2 * m) =>
            paperMeasure) := by
    intro ω κB
    exact hΦ _
  have houter :
      ∀ ω,
        Integrable
          (fun v => ∑ κB, blockTerm ω κB v)
          (Measure.pi fun _ : Fin (2 * m) =>
            paperMeasure) := by
    intro ω
    simpa using
      (integrable_finsetSum Finset.univ
        (fun κB _hκB => hblockTerm ω κB))
  calc
    (∫ v,
        ∑ e : MomentSignatureFiberAt e₀, Φ e v
        ∂Measure.pi fun _ : Fin (2 * m) =>
          paperMeasure) =
        ∫ v,
          ∑ ω : R324FirstLeftOuterCoordinate e₀ hleft,
            ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
              blockTerm ω κB v
          ∂Measure.pi fun _ : Fin (2 * m) =>
            paperMeasure := by
      apply integral_congr_ae
      filter_upwards with v
      exact
        sum_momentSignatureFiber_eq_firstLeftOuter_block
          e₀ hleft (fun e => Φ e v)
    _ =
        ∑ ω : R324FirstLeftOuterCoordinate e₀ hleft,
          ∫ v,
            ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
              blockTerm ω κB v
            ∂Measure.pi fun _ : Fin (2 * m) =>
              paperMeasure := by
      simpa using
        (integral_finsetSum Finset.univ
          (fun ω _hω => houter ω))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ω _hω
      simpa only [blockTerm] using
        integral_pi_eq_integral_complement_integral_selected_bochner
          paperMeasure
          (r324FirstLeftSelected e₀ hleft)
          (fun v => ∑ κB, blockTerm ω κB v)
          (houter ω)

/-! ## The original physical deterministic fibre -/

/-- **One actual signed phase-A representation-order step.**

For one realized first-left block, the original deterministic contraction
fibre is routed through the exact selected-coordinate product measure.
Inside that integral the selected pairing coordinate is the complete
primitive covariance sum, multiplied by the genuine complementary factor
from the original integrand.  No covariance is Fourier-expanded and no
absolute value is introduced.

The section-integrability hypothesis is the precise Fubini premise.  It is
available for almost every endpoint quadruple from the already proved
joint physical integrability; upgrading it to the endpoint-integrated
global iteration is left to the next bridge.
-/
theorem integral_sum_deterministicMomentIntegrand_eq_firstLeft_primitive
    {m : ℕ} (ρ : SmoothCutoff) (ε : ℝ)
    (α β : Z4) (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (x y z w : T4)
    (hint :
      ∀ e : MomentSignatureFiberAt e₀,
        Integrable
          (fun v =>
            deterministicMomentIntegrand ρ ε m α β
              e.1.1 e.1.2.1 e.1.2.2 x y z w v)
          (Measure.pi fun _ : Fin (2 * m) =>
            paperMeasure)) :
    (∫ v,
        ∑ e : MomentSignatureFiberAt e₀,
          deterministicMomentIntegrand ρ ε m α β
            e.1.1 e.1.2.1 e.1.2.2 x y z w v
        ∂Measure.pi fun _ : Fin (2 * m) =>
          paperMeasure) =
      ∑ ω : R324FirstLeftOuterCoordinate e₀ hleft,
        ∫ vC :
            (i : {i : Fin (2 * m) //
              ¬r324FirstLeftSelected e₀ hleft i}) → T4,
          ∫ vB :
              (i : {i : Fin (2 * m) //
                r324FirstLeftSelected e₀ hleft i}) → T4,
            let v :=
              (MeasurableEquiv.piEquivPiSubtypeProd
                (fun _ : Fin (2 * m) => T4)
                (r324FirstLeftSelected e₀ hleft)).symm
                  (vB, vC)
            r324FirstLeftOuterFactor ρ ε α β e₀ hleft ω
                x y z w v *
              ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
                (primitiveCovarianceProduct ρ ε
                  (residualBlockOrder
                    (selectedExtractionBlock
                      e₀.1 Finset.univ hleft))
                  κB.1
                  (fun i =>
                    v (leftMomentIndex
                      ((residualPrimitiveBlockOrderIso e₀.1
                        (selectedExtractionBlock
                          e₀.1 Finset.univ hleft)
                        (selectRel_isRelFullyPaired
                          e₀.1 Finset.univ hleft).isFullyPairedOn
                        i).1))) : ℂ)
            ∂Measure.pi fun _ :
                {i : Fin (2 * m) //
                  r324FirstLeftSelected e₀ hleft i} =>
              paperMeasure
          ∂Measure.pi fun _ :
              {i : Fin (2 * m) //
                ¬r324FirstLeftSelected e₀ hleft i} =>
            paperMeasure := by
  let Φ :
      MomentSignatureFiberAt e₀ →
        (Fin (2 * m) → T4) → ℂ :=
    fun e v =>
      deterministicMomentIntegrand ρ ε m α β
        e.1.1 e.1.2.1 e.1.2.2 x y z w v
  rw [
    integral_sum_momentSignatureFiber_eq_firstLeft_selected_bochner
      e₀ hleft Φ hint]
  apply Finset.sum_congr rfl
  intro ω _hω
  apply integral_congr_ae
  filter_upwards with vC
  apply integral_congr_ae
  filter_upwards with vB
  exact
    sum_deterministicMomentIntegrand_r324FirstLeftReconstruct_eq
      ρ ε α β e₀ hleft ω x y z w
        ((MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : Fin (2 * m) => T4)
          (r324FirstLeftSelected e₀ hleft)).symm
            (vB, vC))

end

end Anderson4D
