import Anderson4D.DetParametrix.Paper42_Moment.R324PaperResidualEndpointPatternProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperFullFullZeroShiftProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperEndpointCaseAssembly

/-!
# Complete paper Step 4(A) endpoint producer

The residual endpoint-pattern theorem and the already closed full/full
zero-shift theorem are the two branches of the refined schedule dichotomy.
This file merely chooses their common support radius, enlarges the primitive
constant once, and exposes the arbitrary-shift and physical endpoint bounds.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open R324WithinHalfResidualPrefix

/-- Complete arbitrary-shift endpoint majorant of paper Step 4(A). -/
theorem exists_r324PaperEndpointAllShiftWeightedMajorantBound
    (rho : SmoothCutoff) :
    ∃ primitiveConstant supportConstant : Real,
      0 < primitiveConstant ∧ 0 < supportConstant ∧
      R324PaperEndpointAllShiftWeightedMajorantBound
        rho primitiveConstant supportConstant := by
  obtain ⟨residualConstant, supportConstant,
      hResidualConstant, hSupport, hResidual⟩ :=
    exists_r324PaperResidualEndpointWeightedMajorantBound rho
  obtain ⟨fullConstant, hFullConstant, hFull⟩ :=
    exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound rho hSupport
  exact ⟨max residualConstant fullConstant, supportConstant,
    lt_max_of_lt_left hResidualConstant, hSupport,
    R324PaperEndpointAllShiftWeightedMajorantBound.of_residual_and_zeroShift
      hResidualConstant.le hFullConstant.le hResidual hFull⟩

/-- Numerical conversion of the completed Step 4(A) majorant. -/
theorem exists_r324PaperEndpointAllShiftPhysicalBound
    (rho : SmoothCutoff) :
    ∃ K : Real, 0 < K ∧ R324PaperEndpointAllShiftPhysicalBound rho K := by
  obtain ⟨primitiveConstant, supportConstant,
      hPrimitive, hSupport, hEndpoint⟩ :=
    exists_r324PaperEndpointAllShiftWeightedMajorantBound rho
  exact hEndpoint.toPhysicalBound hPrimitive hSupport

/-- The zero-conserved-shift endpoint input used by the Step 4 capstone. -/
theorem exists_r324PaperEndpointPhysicalBound
    (rho : SmoothCutoff) :
    ∃ K : Real, 0 ≤ K ∧ R324PaperEndpointPhysicalBound rho K := by
  obtain ⟨K, hK, hEndpoint⟩ :=
    exists_r324PaperEndpointAllShiftPhysicalBound rho
  exact ⟨K, hK.le, hEndpoint.toZeroShift⟩

end

end Anderson4D
