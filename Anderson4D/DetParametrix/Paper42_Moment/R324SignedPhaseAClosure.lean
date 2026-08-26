import Anderson4D.DetParametrix.Paper42_Moment.R324SignedFiberStabilization
import Anderson4D.DetParametrix.Paper41_Renorm.R322SelectedBlockKernelClosure

/-!
# Signed within-half collapse for R-324

Paper Section 4.2 first fixes only the two within-half endpoint signatures.
The primitive pairing on a selected within-half block is then summed and
its spatial variables are integrated before an absolute value is taken.
The residual cross-single equivalence, the other half, and every
complementary spatial coordinate remain outside this operation.

This file packages that exact phase-A order.  It deliberately does not fix
a residual-chain signature and does not use the nonnegative enlarged
primitive-partition fibre.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Stable first-left coordinates -/

/-- The complete primitive pairing coordinate on the first selected left
block. -/
abbrev R324FirstLeftBlockCoordinate
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :=
  {τ : PartialPairing
      (Fin (2 * residualBlockOrder
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft))) //
    τ ∈ primitiveFullPairings
      (residualBlockOrder
        (selectedExtractionBlock
          e₀.1 Finset.univ hleft))}

/-- All discrete coordinates which remain outside the first-left primitive
sum.  The single carrier is stabilized at the reference block coordinate,
so this type does not mention the varying primitive coordinate. -/
abbrev R324FirstLeftOuterCoordinate
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :=
  Σ κC :
      ExtractionComplementFiberAt
        e₀.1 (m - 1) Finset.univ hleft,
    Σ κm : ReductionEndpointFiberAt e₀.2.1,
      (firstBlockReferenceEndpointFiber
        e₀.1 hleft κC).1.singles ≃ κm.1.singles

/-- Reassemble one member of the original within-half signature fibre from
the stable outer coordinates and one complete primitive left-block
coordinate. -/
def r324FirstLeftReconstruct
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (ω : R324FirstLeftOuterCoordinate e₀ hleft)
    (κB : R324FirstLeftBlockCoordinate e₀ hleft) :
    MomentSignatureFiberAt e₀ :=
  (momentSignatureFiberEquivCoordinates e₀).symm
    ⟨(reductionEndpointFiberEquivBlockComplement
        e₀.1 hleft).symm (κB, ω.1),
      ω.2.1,
      (firstBlockCrossEquivStabilization
        e₀.1 hleft κB ω.1 ω.2.1.1).symm
          ω.2.2⟩

/-- The signed within-half fibre sum is exactly an outer sum over the
residual data followed by the complete primitive coordinate sum. -/
theorem sum_momentSignatureFiber_eq_firstLeftOuter_block
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    {A : Type*} [AddCommMonoid A]
    (F : MomentSignatureFiberAt e₀ → A) :
    (∑ e : MomentSignatureFiberAt e₀, F e) =
      ∑ ω : R324FirstLeftOuterCoordinate e₀ hleft,
        ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
          F (r324FirstLeftReconstruct e₀ hleft ω κB) := by
  rw [sum_momentSignatureFiber_eq_firstLeftBlock_stable]
  simp only [Fintype.sum_sigma]
  rfl

/-! ## Exact selected-coordinate Fubini routing -/

/-- Predicate selecting the doubled spatial coordinates belonging to the
first left primitive block. -/
def r324FirstLeftSelected
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (i : Fin (2 * m)) : Prop :=
  i ∈ (selectedExtractionBlock
    e₀.1 Finset.univ hleft).image leftMomentIndex

instance instDecidablePredR324FirstLeftSelected
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b) :
    DecidablePred (r324FirstLeftSelected e₀ hleft) := by
  intro i
  unfold r324FirstLeftSelected
  infer_instance

/-- **Exact signed first-left phase-A Fubini identity.**

The complete primitive pairing sum stays inside the selected-coordinate
integral.  All complementary spatial coordinates and all dependent
discrete data stay outside.  No norm, triangle inequality, or residual
signature grouping occurs in this identity. -/
theorem integral_sum_momentSignatureFiber_eq_firstLeft_selected
    {m : ℕ} (e₀ : MomentContraction m)
    (hleft :
      ∃ a b,
        IsRelFullyPaired e₀.1
          (Finset.univ : Finset (Fin m)) a b)
    (Φ :
      MomentSignatureFiberAt e₀ →
        (Fin (2 * m) → T4) → ℝ)
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
          (Fin (2 * m) → T4) → ℝ :=
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
    _ =
        ∑ ω : R324FirstLeftOuterCoordinate e₀ hleft,
          ∫ vC :
              (i : {i : Fin (2 * m) //
                ¬r324FirstLeftSelected e₀ hleft i}) → T4,
            ∫ vB :
                (i : {i : Fin (2 * m) //
                  r324FirstLeftSelected e₀ hleft i}) → T4,
              ∑ κB : R324FirstLeftBlockCoordinate e₀ hleft,
                blockTerm ω κB
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
      apply Finset.sum_congr rfl
      intro ω _hω
      simpa only [blockTerm] using
        integral_pi_eq_integral_complement_integral_selected
          paperMeasure
          (r324FirstLeftSelected e₀ hleft)
          (fun v => ∑ κB, blockTerm ω κB v)
          (houter ω)

end

end Anderson4D
