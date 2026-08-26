import Anderson4D.DetParametrix.Paper42_Moment.R324PaperFullFullZeroShiftProducer
import Anderson4D.DetParametrix.Paper42_Moment.R324PaperHalfEndpointRoutes

/-!
# Uniform paper endpoint-route providers

This file extracts the common numerical setup used in paper Step 4(A).
Proposition 4.1, the local block closure, and the inserted primitive
majorant choose constants uniformly before the ambient order, pairing, and
incoming Fourier mode.  The resulting package is exactly the provider
consumed by the four structural endpoint routes.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace R324WithinHalfResidualPrefix

/-- Uniform construction of the analytic, budget, exceptional-head, and
initial-certificate inputs used by every one-half endpoint route at the
paper truncation.  No fullness assumption is needed: each literal residual
block has order at most the ambient half-order. -/
theorem exists_r324PaperHalfRouteProviders_at_truncation
    (rho : SmoothCutoff) :
    exists supportConstant C K A : Real,
      0 < supportConstant /\ 0 < C /\ 1 <= K /\ 1 <= A /\
        forall (lam eps : Real) (m : Nat)
          (pairing : PartialPairing (Fin m)) (incomingMode : Z4),
          0 < lam -> 0 < eps -> eps <= 1 ->
          1 <= abs (Real.log eps) -> m <= truncOrder eps ->
          0 < m ->
          Nonempty
            (R324PaperHalfRouteProviders
              (rho := rho) (C := C) (lam := lam) (eps := eps)
              (K := K) (A := A) pairing incomingMode) := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation rho
  obtain ⟨K0, hK0, hlocal⟩ :=
    exists_r324WithinHalf_localBlockClosure hsupport
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  obtain ⟨CballInserted, CregInserted,
      hCballInserted, hCregInserted, hInsertedIntegral⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  let Q : Real := (1 / 2 : Real) * max 1 (supportConstant ^ 2)
  let insertedMass : Real :=
    CballInserted * supportConstant ^ 2 + 2 * CregInserted
  let K : Real :=
    max 1 (max K0 (max (Q * insertedMass) (2 * insertedMass)))
  have hQ : 0 <= Q := by
    dsimp only [Q]
    positivity
  have hInsertedMass : 0 < insertedMass := by
    dsimp only [insertedMass]
    positivity
  have hKone : 1 <= K := by
    dsimp only [K]
    exact le_max_left _ _
  have hK0K : K0 <= K := by
    dsimp only [K]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hQInsertedK : Q * insertedMass <= K := by
    dsimp only [K]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hTwoInsertedK : 2 * insertedMass <= K := by
    dsimp only [K]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨supportConstant, C, K, A, hsupport, hC, hKone, hA, ?_⟩
  intro lam eps m pairing incomingMode hlam heps heps1 hlog htrunc hm
  let propProvider :
      R324WithinHalfProp41Provider
        rho C lam eps supportConstant pairing := by
    intro res head tail hremaining H hH
    exact hprop lam eps (residualBlockOrder head.2)
      (res.headContext head tail hremaining).one_le_blockOrder H
      hlam heps heps1
      ((res.headContext head tail hremaining).order_le_ambient.trans htrunc)
      hH
  let localProvider0 :
      R324WithinHalfLocalBlockProvider
        rho C lam eps K0 pairing := by
    intro res head tail hremaining scale certificate
    exact hlocal rho C lam eps m pairing
      res head tail hremaining scale certificate
      hC hlam heps heps1 hlog
      (fun H hH => propProvider res head tail hremaining H hH)
  let localProvider :
      R324WithinHalfLocalBlockProvider
        rho C lam eps K pairing :=
    R324WithinHalfLocalBlockProvider.mono_K
      hC.le hlam.le hK0K localProvider0
  let budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        rho C lam eps K A pairing :=
    r324WithinHalfBudgetLocalBlockProvider_of_localBlockProvider
      hA localProvider
  have hcharge : forall n : Nat, 1 <= n ->
      Q *
          (∫ z : T4,
            primitiveInsertedMajorant C lam eps
              supportConstant n z ∂paperMeasure) <=
        (C * lam) ^ (2 * n) * K := by
    intro n hn
    have hI := hInsertedIntegral C lam eps
      supportConstant n heps heps1 hsupport hlog
    have hpow : 0 <= (C * lam) ^ (2 * n) := by
      positivity
    have hmassDiv :
        insertedMass / abs (Real.log eps) <= insertedMass := by
      exact div_le_self hInsertedMass.le hlog
    calc
      Q * (∫ z : T4,
          primitiveInsertedMajorant C lam eps
            supportConstant n z ∂paperMeasure) <=
          Q * ((C * lam) ^ (2 * n) *
            (insertedMass / abs (Real.log eps))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [insertedMass] using hI) hQ
      _ <= Q * ((C * lam) ^ (2 * n) * insertedMass) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmassDiv hpow) hQ
      _ = (C * lam) ^ (2 * n) * (Q * insertedMass) := by
        ring
      _ <= (C * lam) ^ (2 * n) * K :=
        mul_le_mul_of_nonneg_left hQInsertedK hpow
  let headBudget :
      R324WithinHalfInsertedExceptionalHeadBudget
        rho C lam eps K pairing incomingMode :=
    r324WithinHalfInsertedExceptionalHeadBudget_of_prop41
      heps supportConstant C hC.le hlam.le
      (fun res head tail hremaining H hH =>
        propProvider res head tail hremaining H hH)
      (by
        intro n hn
        simpa only [Q, mul_assoc] using hcharge n hn)
      incomingMode
  have houtgoingCharge : forall n : Nat, 1 <= n ->
      2 *
          (∫ z : T4,
            primitiveInsertedMajorant C lam eps
              supportConstant n z ∂paperMeasure) <=
        (C * lam) ^ (2 * n) * K := by
    intro n _hn
    have hI := hInsertedIntegral C lam eps
      supportConstant n heps heps1 hsupport hlog
    have hpow : 0 <= (C * lam) ^ (2 * n) := by
      positivity
    have hmassDiv :
        insertedMass / abs (Real.log eps) <= insertedMass := by
      exact div_le_self hInsertedMass.le hlog
    calc
      2 * (∫ z : T4,
          primitiveInsertedMajorant C lam eps
            supportConstant n z ∂paperMeasure) <=
          2 * ((C * lam) ^ (2 * n) *
            (insertedMass / abs (Real.log eps))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [insertedMass] using hI) (by positivity)
      _ <= 2 * ((C * lam) ^ (2 * n) * insertedMass) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmassDiv hpow) (by positivity)
      _ = (C * lam) ^ (2 * n) * (2 * insertedMass) := by
        ring
      _ <= (C * lam) ^ (2 * n) * K :=
        mul_le_mul_of_nonneg_left hTwoInsertedK hpow
  exact ⟨{
    supportConstant := supportConstant
    supportConstant_pos := hsupport
    hm := hm
    heps := heps
    heps1 := heps1
    hC := hC.le
    hlam := hlam.le
    hK := hKone
    hA := hA
    prop41Provider := propProvider
    analyticProvider := localProvider
    budgetProvider := budgetProvider
    headBudget := headBudget
    outgoingInsertedBudget := houtgoingCharge
    initialCertificate := hinitial m }⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
