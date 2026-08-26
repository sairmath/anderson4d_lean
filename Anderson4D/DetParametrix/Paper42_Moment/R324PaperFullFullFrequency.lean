import Anderson4D.DetParametrix.Paper42_Moment.R324CrossSlotFrequencyConservation
import Anderson4D.DetParametrix.Paper42_Moment.R324ConcreteRoutingClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedBranchDichotomy

/-!
# The full/full branch has zero nonconserved external mode

This is the frequency-conservation part of paper Section 4.2 before the
Step-4 endpoint estimate.  A full/full contraction has no cross-copy
covariance slot.  Hence every nonzero Fourier configuration forces
`alpha + beta = 0`; at a nonzero external shift the complete refined fibre
vanishes.

The configuration expansion and its conservation theorem already exist.
This file only transports them through the exact full-pairing and refined
finite-fibre reindexings.  No estimate or triangle inequality is used.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (rho : SmoothCutoff)

/-- One full/full contraction term vanishes when the external shift is
nonzero.  This is the integrated Fourier-conservation statement, obtained
by reusing the existing exact configuration expansion. -/
theorem deterministicMomentContractionTerm_eq_zero_of_left_isFull
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonOne : epsilon <= 1)
    {m : Nat} (alpha beta : Z4) (e : MomentContraction m)
    (hexternal : alpha + beta ≠ 0) (hleft : e.1.IsFull) :
    deterministicMomentContractionTerm
        rho epsilon m alpha beta e = 0 := by
  let kappa := momentContractionEquivFullPairing m e
  have hintegrable : R324MomentIntegrable rho epsilon m alpha beta e :=
    r324MomentIntegrable_all rho hepsilon hepsilonOne alpha beta e
  have hphysical :
      deterministicMomentContractionTerm rho epsilon m alpha beta e =
        (∫ p,
          r324Flatten
            (momentFullPairingPhysicalIntegrand
              rho epsilon m alpha beta kappa) p
          ∂(r324PhysicalMeasure m)) := by
    have hfun :
        r324Flatten
            (momentFullPairingPhysicalIntegrand
              rho epsilon m alpha beta kappa) =
          r324Flatten
            (deterministicMomentIntegrand
              rho epsilon m alpha beta e.1 e.2.1 e.2.2) := by
      funext p
      unfold r324Flatten
      exact momentFullPairingPhysicalIntegrand_momentContraction
        rho epsilon m alpha beta e
          p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
    rw [hfun]
    exact
      (integral_r324Flatten_deterministicMomentIntegrand
        rho epsilon m alpha beta e hintegrable).symm
  rw [hphysical,
    rho.integral_momentFullPairingPhysicalIntegrand_eq_configuration_tsum
      hepsilon alpha beta kappa]
  have hzero : forall q,
      rho.r324FullPairingFourierIntegral epsilon alpha beta kappa q = 0 :=
    fun q => rho.r324FullPairingFourierIntegral_eq_zero_of_left_isFull
      epsilon alpha beta e.1 e.2.1 e.2.2 hexternal hleft q
  simp [hzero]

/-- A residual-refined fibre represented by two full halves vanishes at a
nonzero external shift.  Fullness propagates through the fibre by the
already proved endpoint-signature rigidity theorem. -/
theorem r324RefinedPhysicalIntegral_eq_zero_of_representative_isFull
    {epsilon : Real} (hepsilon : 0 < epsilon) (hepsilonOne : epsilon <= 1)
    {m : Nat} (alpha beta : Z4) (p : R324RefinedScheduleIndex m)
    (hexternal : alpha + beta ≠ 0)
    (hfull :
      (r324RefinedScheduleRepresentative p).1.IsFull ∧
        (r324RefinedScheduleRepresentative p).2.1.IsFull) :
    r324RefinedPhysicalIntegral rho epsilon m alpha beta p = 0 := by
  rw [r324RefinedPhysicalIntegral_eq_sum_contractionTerms
    rho hepsilon hepsilonOne alpha beta p]
  apply Finset.sum_eq_zero
  intro e he
  have heFull :=
    r324RefinedContractionFiber_isFull_of_representative_isFull
      p hfull he
  exact rho.deterministicMomentContractionTerm_eq_zero_of_left_isFull
    hepsilon hepsilonOne alpha beta e hexternal heFull.1

end SmoothCutoff

end

end Anderson4D
