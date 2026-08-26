import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointAllShift
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperFullFullFrequency
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedBranchDichotomy

/-!
# The two actual endpoint branches

The refined schedule has exactly the dichotomy used in paper Section 4.2:
either a residual single survives in both halves, or every contraction in
the refined fibre is full/full.  This file is only the logical case split.
All signed removals and endpoint integrations stay inside the two producer
interfaces below.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Step 4(A) after all signed removals in the residual branch. -/
def R324PaperResidualEndpointWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    0 < epsilon -> epsilon <= 1 / 4 ->
      1 <= abs (Real.log epsilon) -> 2 <= m ->
        m <= truncOrder epsilon ->
          forall p : R324RefinedScheduleIndex m,
            (r324RefinedScheduleRepresentative p).1.singles.Nonempty ->
            abs (lamEps 1 epsilon) ^ (2 * m) *
                  norm (r324RefinedPhysicalIntegral
                    rho epsilon m alpha beta p) <=
                (paperFourthOrderModeDecay alpha *
                    paperFourthOrderModeDecay beta) *
                  (epsilon⁻¹ ^ (8 : Nat) *
                    ∫ z, primitiveInsertedMajorant
                      primitiveConstant 1 epsilon supportConstant m z
                      ∂paperMeasure)

/-- Step 4(A) after all signed removals in the full/full fibre branch. -/
def R324PaperFullEndpointWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    0 < epsilon -> epsilon <= 1 / 4 ->
      1 <= abs (Real.log epsilon) -> 2 <= m ->
        m <= truncOrder epsilon ->
          forall p : R324RefinedScheduleIndex m,
            (forall e : MomentContraction m,
              e ∈ momentRefinedContractionFiber m p.1.1 p.2.1 ->
                e.1.IsFull ∧ e.2.1.IsFull) ->
            abs (lamEps 1 epsilon) ^ (2 * m) *
                  norm (r324RefinedPhysicalIntegral
                    rho epsilon m alpha beta p) <=
                (paperFourthOrderModeDecay alpha *
                    paperFourthOrderModeDecay beta) *
                  (epsilon⁻¹ ^ (8 : Nat) *
                    ∫ z, primitiveInsertedMajorant
                      primitiveConstant 1 epsilon supportConstant m z
                      ∂paperMeasure)

/-- The only quantitative full/full endpoint calculation: at zero
conserved shift the two full Step-1 halves supply the four ordinary-`J`
sacrifices.  The nonzero-shift case is Fourier orthogonality and is added
below for free. -/
def R324PaperFullEndpointZeroShiftWeightedMajorantBound
    (rho : SmoothCutoff) (primitiveConstant supportConstant : Real) : Prop :=
  forall {epsilon : Real} (m : Nat) (alpha beta : Z4),
    0 < epsilon -> epsilon <= 1 / 4 ->
      1 <= abs (Real.log epsilon) -> 2 <= m ->
        m <= truncOrder epsilon -> alpha + beta = 0 ->
          forall p : R324RefinedScheduleIndex m,
            (forall e : MomentContraction m,
              e ∈ momentRefinedContractionFiber m p.1.1 p.2.1 ->
                e.1.IsFull ∧ e.2.1.IsFull) ->
            abs (lamEps 1 epsilon) ^ (2 * m) *
                  norm (r324RefinedPhysicalIntegral
                    rho epsilon m alpha beta p) <=
                (paperFourthOrderModeDecay alpha *
                    paperFourthOrderModeDecay beta) *
                  (epsilon⁻¹ ^ (8 : Nat) *
                    ∫ z, primitiveInsertedMajorant
                      primitiveConstant 1 epsilon supportConstant m z
                      ∂paperMeasure)

/-! ## Harmless enlargement of the primitive constant -/

/-- The residual endpoint producer is monotone in its primitive constant.
This lets independently constructed endpoint branches be joined by taking
one maximum only after both paper-order proofs are complete. -/
theorem R324PaperResidualEndpointWeightedMajorantBound.mono_primitive
    {rho : SmoothCutoff} {C C' supportConstant : Real}
    (hC : 0 <= C) (hCC' : C <= C')
    (h : R324PaperResidualEndpointWeightedMajorantBound
      rho C supportConstant) :
    R324PaperResidualEndpointWeightedMajorantBound
      rho C' supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    p hsingles
  refine (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    p hsingles).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply mul_le_mul_of_nonneg_left
    · exact integral_primitiveInsertedMajorant_mono_const
        hC hCC' 1 hepsilon supportConstant m
    · positivity
  · exact mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)

/-- The full/full endpoint producer is monotone in its primitive constant. -/
theorem R324PaperFullEndpointWeightedMajorantBound.mono_primitive
    {rho : SmoothCutoff} {C C' supportConstant : Real}
    (hC : 0 <= C) (hCC' : C <= C')
    (h : R324PaperFullEndpointWeightedMajorantBound
      rho C supportConstant) :
    R324PaperFullEndpointWeightedMajorantBound
      rho C' supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    p hfibre
  refine (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    p hfibre).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply mul_le_mul_of_nonneg_left
    · exact integral_primitiveInsertedMajorant_mono_const
        hC hCC' 1 hepsilon supportConstant m
    · positivity
  · exact mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)

/-- The zero-shift full/full endpoint producer is likewise monotone in its
primitive constant. -/
theorem R324PaperFullEndpointZeroShiftWeightedMajorantBound.mono_primitive
    {rho : SmoothCutoff} {C C' supportConstant : Real}
    (hC : 0 <= C) (hCC' : C <= C')
    (h : R324PaperFullEndpointZeroShiftWeightedMajorantBound
      rho C supportConstant) :
    R324PaperFullEndpointZeroShiftWeightedMajorantBound
      rho C' supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hshift p hfibre
  refine (h m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    hshift p hfibre).trans ?_
  apply mul_le_mul_of_nonneg_left
  · apply mul_le_mul_of_nonneg_left
    · exact integral_primitiveInsertedMajorant_mono_const
        hC hCC' 1 hepsilon supportConstant m
    · positivity
  · exact mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
      (paperFourthOrderModeDecay_nonneg beta)

/-- A zero-shift quantitative full/full producer already gives the
arbitrary-shift full/full producer: a nonzero conserved Fourier mode
vanishes exactly before any estimate. -/
theorem R324PaperFullEndpointZeroShiftWeightedMajorantBound.toAllShift
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hprimitive : 0 <= primitiveConstant)
    (hzero : R324PaperFullEndpointZeroShiftWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    R324PaperFullEndpointWeightedMajorantBound
      rho primitiveConstant supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
    p hfibre
  by_cases hshift : alpha + beta = 0
  · exact hzero m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc
      hshift p hfibre
  · have hepsilonOne : epsilon <= 1 :=
      hepsilonSmall.trans (by norm_num)
    have hphysical :
        r324RefinedPhysicalIntegral rho epsilon m alpha beta p = 0 :=
      by
        rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
          rho hepsilon hepsilonOne alpha beta p]
        apply Finset.sum_eq_zero
        intro e he
        exact
          rho.deterministicMomentContractionTerm_eq_zero_of_left_isFull
            hepsilon hepsilonOne alpha beta e hshift (hfibre e he).1
    rw [hphysical, norm_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg (paperFourthOrderModeDecay_nonneg alpha)
        (paperFourthOrderModeDecay_nonneg beta))
      (mul_nonneg (by positivity)
        (integral_nonneg fun z =>
          primitiveInsertedMajorant_nonneg hprimitive (by norm_num)))

/-- The residual/full dichotomy is exhaustive, so the two physical
producers give the arbitrary-shift endpoint estimate with no additional
analytic step. -/
theorem R324PaperEndpointAllShiftWeightedMajorantBound.of_scheduleCases
    {rho : SmoothCutoff} {primitiveConstant supportConstant : Real}
    (hresidual : R324PaperResidualEndpointWeightedMajorantBound
      rho primitiveConstant supportConstant)
    (hfull : R324PaperFullEndpointWeightedMajorantBound
      rho primitiveConstant supportConstant) :
    R324PaperEndpointAllShiftWeightedMajorantBound
      rho primitiveConstant supportConstant := by
  intro epsilon m alpha beta hepsilon hepsilonSmall hlog hm2 hmtrunc p
  rcases r324RefinedSchedule_branchDichotomy p with
    hsingles | hfibre
  · exact hresidual m alpha beta hepsilon hepsilonSmall hlog hm2
      hmtrunc p hsingles
  · exact hfull m alpha beta hepsilon hepsilonSmall hlog hm2
      hmtrunc p hfibre

/-- Independently produced residual and full/full constants can be merged
at the final schedule case split. -/
theorem R324PaperEndpointAllShiftWeightedMajorantBound.of_separateConstants
    {rho : SmoothCutoff} {residualConstant fullConstant supportConstant : Real}
    (hResidualConstant : 0 <= residualConstant)
    (hFullConstant : 0 <= fullConstant)
    (hresidual : R324PaperResidualEndpointWeightedMajorantBound
      rho residualConstant supportConstant)
    (hfull : R324PaperFullEndpointWeightedMajorantBound
      rho fullConstant supportConstant) :
    R324PaperEndpointAllShiftWeightedMajorantBound
      rho (max residualConstant fullConstant) supportConstant :=
  R324PaperEndpointAllShiftWeightedMajorantBound.of_scheduleCases
    (hresidual.mono_primitive hResidualConstant (le_max_left _ _))
    (hfull.mono_primitive hFullConstant (le_max_right _ _))

/-- Producer-facing version in which the full/full calculation is required
only at zero conserved shift; Fourier orthogonality supplies all other
full/full shifts before the two independent constants are merged. -/
theorem R324PaperEndpointAllShiftWeightedMajorantBound.of_residual_and_zeroShift
    {rho : SmoothCutoff} {residualConstant fullConstant supportConstant : Real}
    (hResidualConstant : 0 <= residualConstant)
    (hFullConstant : 0 <= fullConstant)
    (hresidual : R324PaperResidualEndpointWeightedMajorantBound
      rho residualConstant supportConstant)
    (hzero : R324PaperFullEndpointZeroShiftWeightedMajorantBound
      rho fullConstant supportConstant) :
    R324PaperEndpointAllShiftWeightedMajorantBound
      rho (max residualConstant fullConstant) supportConstant := by
  apply R324PaperEndpointAllShiftWeightedMajorantBound.of_separateConstants
    hResidualConstant hFullConstant hresidual
  exact hzero.toAllShift hFullConstant

end

end Anderson4D
