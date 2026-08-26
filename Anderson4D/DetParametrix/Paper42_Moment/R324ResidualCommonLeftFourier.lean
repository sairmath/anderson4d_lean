import Anderson4D.Continuum.CovarianceProductFourierDecay
import Anderson4D.DetParametrix.Paper42_Moment.R324ResidualPrimitiveCoordinateRealization
import Anderson4D.DetParametrix.Paper42_Moment.R324SingleProjectedMarkedPhysicalBridge

/-!
# Common-left Fourier decay of the residual covariance product

Paper: R-324 — §4.2 Step 4(B), residual common-left Fourier decay

Paper Step 4(B) translates the whole left copy, not one covariance endpoint
at a time.  Under that translation the within-left and within-right residual
covariances are invariant, while every cross-copy covariance sees the same
one-dimensional displacement.  This file records that exact grouped identity
and applies the existing eighth-order periodic integration-by-parts theorem.

The coordinate estimate first differentiates only the cross factors.  The
grouped producer then upgrades the two invariant within-half products by the
zeroth-order auxiliary estimate, so its final majorant is the complete
`auxiliaryCutoff` residual primitive sum.  No norm is taken before the complete
cross product has been Fourier transformed.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open scoped BigOperators
open MeasureTheory

/-! ## The common-left coordinate line -/

/-- Euclidean displacement by `t` in one coordinate. -/
def r324CoordinateDisplacementR4 (coord : Fin dim) (t : ℝ) : R4 :=
  Function.update 0 coord t

/-- The corresponding element of the four-dimensional torus. -/
def r324CoordinateDisplacementT4 (coord : Fin dim) (t : ℝ) : T4 :=
  periodizeR4 (r324CoordinateDisplacementR4 coord t)

/-- The coordinate subgroup has exactly the expected one-dimensional
Fourier character. -/
theorem charT4_coordinateDisplacementT4
    (mode : Z4) (coord : Fin dim) (t : ℝ) :
    charT4 mode (r324CoordinateDisplacementT4 coord t) =
      fourier (mode coord) (t : AddCircle (2 * Real.pi)) := by
  unfold charT4 r324CoordinateDisplacementT4
    r324CoordinateDisplacementR4 periodizeR4
  rw [Fintype.prod_eq_mul_prod_compl coord]
  simp only [Function.update_self]
  have hprod :
      (∏ x ∈ ({coord}ᶜ : Finset (Fin dim)),
        fourier (mode x)
          ((Function.update (0 : R4) coord t x : ℝ) :
            AddCircle (2 * Real.pi))) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    have hne : x ≠ coord := by
      simpa only [Finset.mem_compl, Finset.mem_singleton] using hx
    rw [Function.update_of_ne hne]
    simp
  rw [hprod, mul_one]

/-- Translate every vertex of the left copy by the same torus displacement,
and leave every vertex of the right copy fixed. -/
def r324CommonLeftMomentTranslation
    {m : ℕ} (v : Fin (2 * m) → T4)
    (coord : Fin dim) (t : ℝ) (j : Fin (2 * m)) : T4 :=
  if j.val < m then
    v j + r324CoordinateDisplacementT4 coord t
  else
    v j

@[simp]
theorem r324CommonLeftMomentTranslation_left
    {m : ℕ} (v : Fin (2 * m) → T4)
    (coord : Fin dim) (t : ℝ) (i : Fin m) :
    r324CommonLeftMomentTranslation v coord t (leftMomentIndex i) =
      v (leftMomentIndex i) + r324CoordinateDisplacementT4 coord t := by
  simp [r324CommonLeftMomentTranslation, leftMomentIndex]

@[simp]
theorem r324CommonLeftMomentTranslation_right
    {m : ℕ} (v : Fin (2 * m) → T4)
    (coord : Fin dim) (t : ℝ) (i : Fin m) :
    r324CommonLeftMomentTranslation v coord t (rightMomentIndex i) =
      v (rightMomentIndex i) := by
  simp [r324CommonLeftMomentTranslation, rightMomentIndex]

/-- A torus displacement written in the arbitrary Euclidean representative
used by the covariance derivative API. -/
theorem add_coordinateDisplacementT4_eq_periodizeR4_update
    (z : T4) (coord : Fin dim) (t : ℝ) :
    z + r324CoordinateDisplacementT4 coord t =
      periodizeR4
        (Function.update (torusLift z) coord (torusLift z coord + t)) := by
  funext j
  by_cases hj : j = coord
  · subst j
    simp [r324CoordinateDisplacementT4, r324CoordinateDisplacementR4,
      periodizeR4]
    exact (congrFun (periodizeR4_torusLift z) coord).symm
  · simp [r324CoordinateDisplacementT4, r324CoordinateDisplacementR4,
      periodizeR4, Function.update_of_ne hj]
    exact (congrFun (periodizeR4_torusLift z) j).symm

/-- One cross covariance under the common-left translation is exactly one
factor of the common coordinate-line product. -/
theorem etaEpsT4_commonLeftTranslation_eq_coordLineFactor
    (rho : SmoothCutoff) (eps : ℝ) (left right : T4)
    (coord : Fin dim) (t : ℝ) :
    rho.etaEpsT4 eps
        ((left + r324CoordinateDisplacementT4 coord t) - right) =
      rho.etaPeriodizationCoordLineFactor eps
        (torusLift (left - right)) coord
        (torusLift (left - right) coord) t := by
  have harg :
      (left + r324CoordinateDisplacementT4 coord t) - right =
        periodizeR4
          (Function.update (torusLift (left - right)) coord
            (torusLift (left - right) coord + t)) := by
    calc
      (left + r324CoordinateDisplacementT4 coord t) - right =
          (left - right) + r324CoordinateDisplacementT4 coord t := by
            abel
      _ = _ := add_coordinateDisplacementT4_eq_periodizeR4_update
        (left - right) coord t
  rw [harg, rho.etaEpsT4_periodizeR4_eq_etaPeriodizationR4]
  rfl

/-! ## The complete cross product -/

/-- The genuine residual cross-covariance product along a common-left
coordinate translation. -/
def r324MomentCrossCommonLeftCoordLineC
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) : ℂ :=
  (momentCrossCovarianceProduct rho eps m kappaPlus kappaMinus pi
      (r324CommonLeftMomentTranslation v coord t) : ℂ)

/-- The common-left cross line is literally the finite coordinate-line
product used by `CovarianceProductFourierDecay`. -/
theorem r324MomentCrossCommonLeftCoordLineC_eq_etaProductC
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) :
    r324MomentCrossCommonLeftCoordLineC
        rho eps kappaPlus kappaMinus pi v coord t =
      rho.etaPeriodizationCoordLineProductC
        (Finset.univ : Finset kappaPlus.singles) eps
        (fun i => torusLift
          (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)))
        (fun _ => coord)
        (fun i => torusLift
          (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)) coord)
        t := by
  unfold r324MomentCrossCommonLeftCoordLineC
    momentCrossCovarianceProduct
    SmoothCutoff.etaPeriodizationCoordLineProductC
    SmoothCutoff.etaPeriodizationCoordLineProduct
  push_cast
  apply Finset.prod_congr rfl
  intro i _hi
  rw [r324CommonLeftMomentTranslation_left,
    r324CommonLeftMomentTranslation_right]
  exact_mod_cast
    etaEpsT4_commonLeftTranslation_eq_coordLineFactor
      rho eps (v (leftMomentIndex i.1))
        (v (rightMomentIndex (pi i).1)) coord t

/-- The auxiliary coordinate-line product is the same cross product with
the cutoff replaced by `auxiliaryCutoff`. -/
theorem etaAuxiliaryCoordLineProduct_eq_crossCommonLeft
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) :
    rho.etaAuxiliaryCoordLineProduct
        (Finset.univ : Finset kappaPlus.singles) eps
        (fun i => torusLift
          (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)))
        (fun _ => coord)
        (fun i => torusLift
          (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)) coord)
        t =
      momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
        kappaPlus kappaMinus pi
        (r324CommonLeftMomentTranslation v coord t) := by
  unfold SmoothCutoff.etaAuxiliaryCoordLineProduct
    momentCrossCovarianceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  symm
  rw [r324CommonLeftMomentTranslation_left,
    r324CommonLeftMomentTranslation_right]
  exact etaEpsT4_commonLeftTranslation_eq_coordLineFactor
    rho.auxiliaryCutoff eps (v (leftMomentIndex i.1))
      (v (rightMomentIndex (pi i).1)) coord t

/-- Eighth-order Fourier decay of the entire cross family.  The norm is
taken only after the full cross product has been transformed. -/
theorem norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) → T4) (coord : Fin dim)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (neg_lt_self Real.pi_pos)
        (r324MomentCrossCommonLeftCoordLineC
          rho eps kappaPlus kappaMinus pi v coord) n‖ ≤
      |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        (((kappaPlus.singles.card : ℝ) ^ 8 *
          rho.etaDerivativeMajorantConstant ^ kappaPlus.singles.card *
          eps⁻¹ ^ 8) *
        ∫ t in -Real.pi..Real.pi,
          momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
            kappaPlus kappaMinus pi
            (r324CommonLeftMomentTranslation v coord t)) := by
  have hfun :
      r324MomentCrossCommonLeftCoordLineC
          rho eps kappaPlus kappaMinus pi v coord =
        rho.etaPeriodizationCoordLineProductC
          (Finset.univ : Finset kappaPlus.singles) eps
          (fun i => torusLift
            (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)))
          (fun _ => coord)
          (fun i => torusLift
            (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)) coord) := by
    funext t
    exact r324MomentCrossCommonLeftCoordLineC_eq_etaProductC
      rho eps kappaPlus kappaMinus pi v coord t
  rw [hfun]
  have h :=
    rho.norm_fourierCoeffOn_etaPeriodizationCoordLineProductC_le
      (Finset.univ : Finset kappaPlus.singles) heps
      (fun i => torusLift
        (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)))
      (fun _ => coord)
      (fun i => torusLift
        (v (leftMomentIndex i.1) - v (rightMomentIndex (pi i).1)) coord)
      hn
  simpa only [Finset.card_univ, Fintype.card_coe,
    etaAuxiliaryCoordLineProduct_eq_crossCommonLeft, mul_assoc] using h

/-! ## Reassembly on one realized residual coordinate -/

/-- Unmarked counterpart of the marker-preserving three-factor identity:
the covariance product on the residual carrier is the product of its
within-left, within-right, and cross-copy factors. -/
theorem pairingCovarianceProductOn_momentResidualActive_eq_threeFactor
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) → T4) :
    pairingCovarianceProductOn rho eps
        (momentCombinedPairing kappaPlus kappaMinus pi)
        (momentResidualActive kappaPlus kappaMinus) v =
      pairingCovarianceProductOn rho eps kappaPlus
          (finalActive kappaPlus) (fun i => v (leftMomentIndex i)) *
        pairingCovarianceProductOn rho eps kappaMinus
          (finalActive kappaMinus) (fun i => v (rightMomentIndex i)) *
        momentCrossCovarianceProduct rho eps m
          kappaPlus kappaMinus pi v := by
  have hLR := disjoint_r324LeftResidualPair_right kappaPlus kappaMinus
  have hLC := disjoint_r324LeftResidualPair_cross kappaPlus
  have hRC :=
    disjoint_r324RightResidualPair_cross kappaPlus kappaMinus
  have hLRC :
      Disjoint
        (r324LeftResidualPairLowerEndpoints kappaPlus ∪
          r324RightResidualPairLowerEndpoints kappaMinus)
        (momentCrossLowerEndpoints kappaPlus) :=
    Finset.disjoint_union_left.mpr ⟨hLC, hRC⟩
  have hleft :
      (∏ a ∈ r324LeftResidualPairLowerEndpoints kappaPlus,
          rho.etaEpsT4 eps
            (v a - v (momentCombinedPairing
              kappaPlus kappaMinus pi a))) =
        pairingCovarianceProductOn rho eps kappaPlus
          (finalActive kappaPlus) (fun i => v (leftMomentIndex i)) := by
    unfold r324LeftResidualPairLowerEndpoints pairingCovarianceProductOn
    rw [Finset.prod_image leftMomentIndex_injective.injOn]
    apply Finset.prod_congr rfl
    intro i hi
    have hnot : i ∉ kappaPlus.singles := by
      intro hsingle
      exact (ne_of_lt (Finset.mem_filter.mp hi).2)
        (PartialPairing.mem_singles.mp hsingle).symm
    rw [momentCombinedPairing_left_pair
      kappaPlus kappaMinus pi i hnot]
  have hright :
      (∏ a ∈ r324RightResidualPairLowerEndpoints kappaMinus,
          rho.etaEpsT4 eps
            (v a - v (momentCombinedPairing
              kappaPlus kappaMinus pi a))) =
        pairingCovarianceProductOn rho eps kappaMinus
          (finalActive kappaMinus) (fun i => v (rightMomentIndex i)) := by
    unfold r324RightResidualPairLowerEndpoints pairingCovarianceProductOn
    rw [Finset.prod_image rightMomentIndex_injective.injOn]
    apply Finset.prod_congr rfl
    intro i hi
    have hnot : i ∉ kappaMinus.singles := by
      intro hsingle
      exact (ne_of_lt (Finset.mem_filter.mp hi).2)
        (PartialPairing.mem_singles.mp hsingle).symm
    rw [momentCombinedPairing_right_pair
      kappaPlus kappaMinus pi i hnot]
  have hcross :
      (∏ a ∈ momentCrossLowerEndpoints kappaPlus,
          rho.etaEpsT4 eps
            (v a - v (momentCombinedPairing
              kappaPlus kappaMinus pi a))) =
        momentCrossCovarianceProduct rho eps m
          kappaPlus kappaMinus pi v := by
    rw [prod_momentCrossLowerEndpoints]
    unfold momentCrossCovarianceProduct
    rw [Finset.prod_subtype kappaPlus.singles (fun _ => Iff.rfl)]
    apply Finset.prod_congr rfl
    intro i _hi
    rw [momentCombinedPairing_left_single
      kappaPlus kappaMinus pi i.1 i.2]
  change
    (∏ a ∈ (momentResidualActive kappaPlus kappaMinus).filter
        (fun a => a < momentCombinedPairing kappaPlus kappaMinus pi a),
      rho.etaEpsT4 eps
        (v a - v (momentCombinedPairing kappaPlus kappaMinus pi a))) = _
  rw [r324ResidualLowerEndpoints_eq_threeWay kappaPlus kappaMinus pi,
    Finset.prod_union hLRC, Finset.prod_union hLR,
    hleft, hright, hcross]

/-- A complete within-left residual covariance product is invariant under
the common-left translation. -/
theorem pairingCovarianceProductOn_left_commonLeftTranslation
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (kappa : PartialPairing (Fin m))
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) :
    pairingCovarianceProductOn rho eps kappa (finalActive kappa)
        (fun i => r324CommonLeftMomentTranslation v coord t
          (leftMomentIndex i)) =
      pairingCovarianceProductOn rho eps kappa (finalActive kappa)
        (fun i => v (leftMomentIndex i)) := by
  unfold pairingCovarianceProductOn
  apply Finset.prod_congr rfl
  intro i _hi
  congr 1
  simp only [r324CommonLeftMomentTranslation_left]
  abel

/-- A complete within-right residual covariance product is unchanged by
the common-left translation. -/
theorem pairingCovarianceProductOn_right_commonLeftTranslation
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (kappa : PartialPairing (Fin m))
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) :
    pairingCovarianceProductOn rho eps kappa (finalActive kappa)
        (fun i => r324CommonLeftMomentTranslation v coord t
          (rightMomentIndex i)) =
      pairingCovarianceProductOn rho eps kappa (finalActive kappa)
        (fun i => v (rightMomentIndex i)) := by
  simp only [r324CommonLeftMomentTranslation_right]

/-- Zeroth-order member of the derivative majorant: every torus covariance
is bounded by the same covariance of `auxiliaryCutoff`. -/
theorem etaEpsT4_le_etaDerivativeMajorantConstant_mul_auxiliary
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps)
    (coord : Fin dim) (z : T4) :
    rho.etaEpsT4 eps z ≤
      rho.etaDerivativeMajorantConstant *
        rho.auxiliaryCutoff.etaEpsT4 eps z := by
  have h := rho.abs_iteratedDeriv_etaPeriodizationCoordLineFactor_le
    heps (torusLift z) coord (torusLift z coord) 0
    (r := 0) (by omega)
  simp only [iteratedDeriv_zero,
    SmoothCutoff.etaPeriodizationCoordLineFactor,
    Function.update_eq_self, add_zero, pow_zero, mul_one] at h
  rw [abs_of_nonneg
    (rho.etaPeriodizationR4_nonneg eps (torusLift z))] at h
  simpa only [← rho.etaEpsT4_periodizeR4_eq_etaPeriodizationR4,
    ← rho.auxiliaryCutoff.etaEpsT4_periodizeR4_eq_etaPeriodizationR4,
    periodizeR4_torusLift] using h

/-- Product form of the preceding zeroth-order majorant. -/
theorem pairingCovarianceProductOn_le_auxiliary
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps)
    (coord : Fin dim) {n : ℕ}
    (kappa : PartialPairing (Fin n)) (B : Finset (Fin n))
    (v : Fin n → T4) :
    pairingCovarianceProductOn rho eps kappa B v ≤
      rho.etaDerivativeMajorantConstant ^
          (B.filter (fun i => i < kappa i)).card *
        pairingCovarianceProductOn rho.auxiliaryCutoff eps kappa B v := by
  unfold pairingCovarianceProductOn
  calc
    (∏ i ∈ B.filter (fun i => i < kappa i),
        rho.etaEpsT4 eps (v i - v (kappa i))) ≤
        ∏ i ∈ B.filter (fun i => i < kappa i),
          (rho.etaDerivativeMajorantConstant *
            rho.auxiliaryCutoff.etaEpsT4 eps
              (v i - v (kappa i))) := by
      exact Finset.prod_le_prod
        (fun i _ => rho.etaEpsT4_nonneg eps _)
        (fun i _ =>
          etaEpsT4_le_etaDerivativeMajorantConstant_mul_auxiliary
            rho heps coord (v i - v (kappa i)))
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_filter]

/-- A convenient base at least one which absorbs every derivative-majorant
constant produced at a fixed perturbative order. -/
def r324ResidualFourierMajorantBase (rho : SmoothCutoff) : ℝ :=
  max 1 rho.etaDerivativeMajorantConstant

theorem one_le_r324ResidualFourierMajorantBase (rho : SmoothCutoff) :
    1 ≤ r324ResidualFourierMajorantBase rho := by
  exact le_max_left _ _

theorem etaDerivativeMajorantConstant_le_r324ResidualFourierMajorantBase
    (rho : SmoothCutoff) :
    rho.etaDerivativeMajorantConstant ≤
      r324ResidualFourierMajorantBase rho := by
  exact le_max_right _ _

/-- Order-padded zeroth-order covariance-product majorant. -/
theorem pairingCovarianceProductOn_le_auxiliary_orderPow
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps)
    (coord : Fin dim) {m : ℕ}
    (kappa : PartialPairing (Fin m)) (B : Finset (Fin m))
    (v : Fin m → T4) :
    pairingCovarianceProductOn rho eps kappa B v ≤
      r324ResidualFourierMajorantBase rho ^ m *
        pairingCovarianceProductOn rho.auxiliaryCutoff eps kappa B v := by
  have hraw := pairingCovarianceProductOn_le_auxiliary
    rho heps coord kappa B v
  have hcard : (B.filter (fun i => i < kappa i)).card ≤ m := by
    calc
      (B.filter (fun i => i < kappa i)).card ≤
          Fintype.card (Fin m) := Finset.card_le_univ _
      _ = m := Fintype.card_fin m
  have hpow :
      rho.etaDerivativeMajorantConstant ^
          (B.filter (fun i => i < kappa i)).card ≤
        r324ResidualFourierMajorantBase rho ^ m := by
    calc
      rho.etaDerivativeMajorantConstant ^
          (B.filter (fun i => i < kappa i)).card ≤
          r324ResidualFourierMajorantBase rho ^
            (B.filter (fun i => i < kappa i)).card :=
        pow_le_pow_left₀ rho.etaDerivativeMajorantConstant_pos.le
          (etaDerivativeMajorantConstant_le_r324ResidualFourierMajorantBase rho)
          _
      _ ≤ r324ResidualFourierMajorantBase rho ^ m :=
        pow_le_pow_right₀
          (one_le_r324ResidualFourierMajorantBase rho) hcard
  exact hraw.trans (mul_le_mul_of_nonneg_right hpow
    (Finset.prod_nonneg fun i _ =>
      rho.auxiliaryCutoff.etaEpsT4_nonneg eps (v i - v (kappa i))))

/-- The invariant two-half factor attached to one realized residual
coordinate. -/
def r324ResidualRealizedStationaryFactorC
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) : ℂ :=
  let realized :=
    r324RefinedContractionOfResidualCoordinates e0 he0 coordinates
  (pairingCovarianceProductOn rho eps realized.1.1
      (finalActive realized.1.1) (fun i => v (leftMomentIndex i)) : ℂ) *
    (pairingCovarianceProductOn rho eps realized.1.2.1
      (finalActive realized.1.2.1) (fun i => v (rightMomentIndex i)) : ℂ)

/-- Real-valued version of the invariant two-half factor. -/
def r324ResidualRealizedStationaryFactor
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) : ℝ :=
  let realized :=
    r324RefinedContractionOfResidualCoordinates e0 he0 coordinates
  pairingCovarianceProductOn rho eps realized.1.1
      (finalActive realized.1.1) (fun i => v (leftMomentIndex i)) *
    pairingCovarianceProductOn rho eps realized.1.2.1
      (finalActive realized.1.2.1) (fun i => v (rightMomentIndex i))

theorem r324ResidualRealizedStationaryFactorC_eq_coe
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) :
    r324ResidualRealizedStationaryFactorC
        rho eps e0 he0 coordinates v =
      (r324ResidualRealizedStationaryFactor
        rho eps e0 he0 coordinates v : ℂ) := by
  unfold r324ResidualRealizedStationaryFactorC
    r324ResidualRealizedStationaryFactor
  push_cast
  rfl

theorem r324ResidualRealizedStationaryFactor_nonneg
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) :
    0 ≤ r324ResidualRealizedStationaryFactor
      rho eps e0 he0 coordinates v := by
  unfold r324ResidualRealizedStationaryFactor
  exact mul_nonneg
    (Finset.prod_nonneg fun i _ => rho.etaEpsT4_nonneg eps _)
    (Finset.prod_nonneg fun i _ => rho.etaEpsT4_nonneg eps _)

theorem norm_r324ResidualRealizedStationaryFactorC
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) :
    ‖r324ResidualRealizedStationaryFactorC
        rho eps e0 he0 coordinates v‖ =
      r324ResidualRealizedStationaryFactor
        rho eps e0 he0 coordinates v := by
  rw [r324ResidualRealizedStationaryFactorC_eq_coe,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (r324ResidualRealizedStationaryFactor_nonneg
      rho eps e0 he0 coordinates v)]

/-- Both stationary half-products may be upgraded to the auxiliary cutoff
at an exponential-in-order cost. -/
theorem r324ResidualRealizedStationaryFactor_le_auxiliary
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps)
    (coord : Fin dim) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) :
    r324ResidualRealizedStationaryFactor
        rho eps e0 he0 coordinates v ≤
      r324ResidualFourierMajorantBase rho ^ (2 * m) *
        r324ResidualRealizedStationaryFactor
          rho.auxiliaryCutoff eps e0 he0 coordinates v := by
  let realized :=
    r324RefinedContractionOfResidualCoordinates e0 he0 coordinates
  have hleft := pairingCovarianceProductOn_le_auxiliary_orderPow
    rho heps coord realized.1.1 (finalActive realized.1.1)
      (fun i => v (leftMomentIndex i))
  have hright := pairingCovarianceProductOn_le_auxiliary_orderPow
    rho heps coord realized.1.2.1 (finalActive realized.1.2.1)
      (fun i => v (rightMomentIndex i))
  have hright0 : 0 ≤ pairingCovarianceProductOn rho eps realized.1.2.1
      (finalActive realized.1.2.1) (fun i => v (rightMomentIndex i)) :=
    Finset.prod_nonneg fun i _ => rho.etaEpsT4_nonneg eps _
  have hleftAux0 : 0 ≤
      pairingCovarianceProductOn rho.auxiliaryCutoff eps realized.1.1
        (finalActive realized.1.1) (fun i => v (leftMomentIndex i)) :=
    Finset.prod_nonneg fun i _ => rho.auxiliaryCutoff.etaEpsT4_nonneg eps _
  unfold r324ResidualRealizedStationaryFactor
  calc
    _ ≤
        (r324ResidualFourierMajorantBase rho ^ m *
          pairingCovarianceProductOn rho.auxiliaryCutoff eps realized.1.1
            (finalActive realized.1.1) (fun i => v (leftMomentIndex i))) *
        (r324ResidualFourierMajorantBase rho ^ m *
          pairingCovarianceProductOn rho.auxiliaryCutoff eps realized.1.2.1
            (finalActive realized.1.2.1)
            (fun i => v (rightMomentIndex i))) :=
      mul_le_mul hleft hright hright0
        (mul_nonneg
          (pow_nonneg
            (le_trans (by norm_num)
              (one_le_r324ResidualFourierMajorantBase rho)) _)
          hleftAux0)
    _ = _ := by
      dsimp [r324ResidualRealizedStationaryFactor]
      rw [show r324ResidualFourierMajorantBase rho ^ (2 * m) =
          r324ResidualFourierMajorantBase rho ^ m *
            r324ResidualFourierMajorantBase rho ^ m by
        rw [← pow_add]
        congr 1
        omega]
      ring

/-! ## One realized residual coordinate -/

/-- One realized residual-coordinate product along the common-left line. -/
def r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) : ℂ :=
  (r324ResidualPrimitiveCoordinateProduct rho eps
      e0.1 e0.2.1 e0.2.2 coordinates
      (r324CommonLeftMomentTranslation v coord t) : ℂ)

/-- Exact factorization of a realized residual-coordinate line into the
stationary within-half factor and the complete common-left cross line. -/
theorem r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_eq
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) :
    r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
        rho eps e0 coordinates v coord t =
      r324ResidualRealizedStationaryFactorC
          rho eps e0 he0 coordinates v *
        r324MomentCrossCommonLeftCoordLineC rho eps
          (r324RefinedContractionOfResidualCoordinates
            e0 he0 coordinates).1.1
          (r324RefinedContractionOfResidualCoordinates
            e0 he0 coordinates).1.2.1
          (r324RefinedContractionOfResidualCoordinates
            e0 he0 coordinates).1.2.2
          v coord t := by
  let realized :=
    r324RefinedContractionOfResidualCoordinates e0 he0 coordinates
  unfold r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
    r324ResidualRealizedStationaryFactorC
  rw [r324ResidualPrimitiveCoordinateProduct_eq_pairingCovarianceProductOn
    rho eps e0 he0 coordinates]
  rw [pairingCovarianceProductOn_momentResidualActive_eq_threeFactor]
  rw [pairingCovarianceProductOn_left_commonLeftTranslation,
    pairingCovarianceProductOn_right_commonLeftTranslation]
  unfold r324MomentCrossCommonLeftCoordLineC
  push_cast
  ring

/-- Nonnegativity of the complete residual cross product. -/
theorem momentCrossCovarianceProduct_nonneg_local
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) → T4) :
    0 ≤ momentCrossCovarianceProduct rho eps m
      kappaPlus kappaMinus pi v := by
  unfold momentCrossCovarianceProduct
  exact Finset.prod_nonneg fun i _ => rho.etaEpsT4_nonneg eps _

/-- Order-uniform version of the grouped cross Fourier estimate. -/
theorem norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le_orderPow
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (kappaPlus kappaMinus : PartialPairing (Fin m))
    (pi : kappaPlus.singles ≃ kappaMinus.singles)
    (v : Fin (2 * m) → T4) (coord : Fin dim)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (neg_lt_self Real.pi_pos)
        (r324MomentCrossCommonLeftCoordLineC
          rho eps kappaPlus kappaMinus pi v coord) n‖ ≤
      |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        (((m : ℝ) ^ 8 *
          r324ResidualFourierMajorantBase rho ^ m * eps⁻¹ ^ 8) *
        ∫ t in -Real.pi..Real.pi,
          momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
            kappaPlus kappaMinus pi
            (r324CommonLeftMomentTranslation v coord t)) := by
  have h := norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le
    rho heps kappaPlus kappaMinus pi v coord hn
  have hcard : kappaPlus.singles.card ≤ m := by
    calc
      kappaPlus.singles.card ≤ Fintype.card (Fin m) :=
        Finset.card_le_univ _
      _ = m := Fintype.card_fin m
  have hcardR : (kappaPlus.singles.card : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hcard
  have hcardPow :
      (kappaPlus.singles.card : ℝ) ^ 8 ≤ (m : ℝ) ^ 8 :=
    pow_le_pow_left₀ (by positivity) hcardR 8
  have hbasePow :
      rho.etaDerivativeMajorantConstant ^ kappaPlus.singles.card ≤
        r324ResidualFourierMajorantBase rho ^ m := by
    calc
      rho.etaDerivativeMajorantConstant ^ kappaPlus.singles.card ≤
          r324ResidualFourierMajorantBase rho ^ kappaPlus.singles.card :=
        pow_le_pow_left₀ rho.etaDerivativeMajorantConstant_pos.le
          (etaDerivativeMajorantConstant_le_r324ResidualFourierMajorantBase rho)
          _
      _ ≤ r324ResidualFourierMajorantBase rho ^ m :=
        pow_le_pow_right₀
          (one_le_r324ResidualFourierMajorantBase rho) hcard
  have hderivPow0 :
      0 ≤ rho.etaDerivativeMajorantConstant ^
        kappaPlus.singles.card :=
    pow_nonneg rho.etaDerivativeMajorantConstant_pos.le _
  have hint :
      0 ≤ ∫ t in -Real.pi..Real.pi,
        momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
          kappaPlus kappaMinus pi
          (r324CommonLeftMomentTranslation v coord t) := by
    exact intervalIntegral.integral_nonneg_of_forall
      (le_of_lt (neg_lt_self Real.pi_pos)) fun t =>
        momentCrossCovarianceProduct_nonneg_local
          rho.auxiliaryCutoff eps kappaPlus kappaMinus pi _
  exact h.trans (by
    gcongr)

/-- Recombination identity for the auxiliary coordinate product. -/
theorem integral_r324ResidualPrimitiveCoordinateCommonLeft_auxiliary_eq
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) (coord : Fin dim) :
    (∫ t in -Real.pi..Real.pi,
      r324ResidualPrimitiveCoordinateProduct rho.auxiliaryCutoff eps
        e0.1 e0.2.1 e0.2.2 coordinates
        (r324CommonLeftMomentTranslation v coord t)) =
      r324ResidualRealizedStationaryFactor
          rho.auxiliaryCutoff eps e0 he0 coordinates v *
        ∫ t in -Real.pi..Real.pi,
          momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.1
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.1
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.2
            (r324CommonLeftMomentTranslation v coord t) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  change
    r324ResidualPrimitiveCoordinateProduct rho.auxiliaryCutoff eps
        e0.1 e0.2.1 e0.2.2 coordinates
        (r324CommonLeftMomentTranslation v coord t) = _
  rw [r324ResidualPrimitiveCoordinateProduct_eq_pairingCovarianceProductOn
    rho.auxiliaryCutoff eps e0 he0 coordinates]
  rw [pairingCovarianceProductOn_momentResidualActive_eq_threeFactor]
  rw [pairingCovarianceProductOn_left_commonLeftTranslation,
    pairingCovarianceProductOn_right_commonLeftTranslation]
  unfold r324ResidualRealizedStationaryFactor
  rfl

/-- Fully auxiliary-cutoff, order-uniform decay for one realized residual
coordinate.  This is the form which recombines after summing coordinates. -/
theorem norm_fourierCoeffOn_r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_le_auxiliary
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) (coord : Fin dim)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (neg_lt_self Real.pi_pos)
        (r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
          rho eps e0 coordinates v coord) n‖ ≤
      |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        (((m : ℝ) ^ 8 *
          r324ResidualFourierMajorantBase rho ^ (3 * m) * eps⁻¹ ^ 8) *
        ∫ t in -Real.pi..Real.pi,
          r324ResidualPrimitiveCoordinateProduct rho.auxiliaryCutoff eps
            e0.1 e0.2.1 e0.2.2 coordinates
            (r324CommonLeftMomentTranslation v coord t)) := by
  have hfun :
      r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
          rho eps e0 coordinates v coord =
        fun t =>
          r324ResidualRealizedStationaryFactorC
              rho eps e0 he0 coordinates v *
            r324MomentCrossCommonLeftCoordLineC rho eps
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.2
              v coord t := by
    funext t
    exact r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_eq
      rho eps e0 he0 coordinates v coord t
  have hcross :=
    norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le_orderPow
      rho heps
      (r324RefinedContractionOfResidualCoordinates
        e0 he0 coordinates).1.1
      (r324RefinedContractionOfResidualCoordinates
        e0 he0 coordinates).1.2.1
      (r324RefinedContractionOfResidualCoordinates
        e0 he0 coordinates).1.2.2
      v coord hn
  have hstationary := r324ResidualRealizedStationaryFactor_le_auxiliary
    rho heps coord e0 he0 coordinates v
  have hint :
      0 ≤ ∫ t in -Real.pi..Real.pi,
        momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
          (r324RefinedContractionOfResidualCoordinates
            e0 he0 coordinates).1.1
          (r324RefinedContractionOfResidualCoordinates
            e0 he0 coordinates).1.2.1
          (r324RefinedContractionOfResidualCoordinates
            e0 he0 coordinates).1.2.2
          (r324CommonLeftMomentTranslation v coord t) := by
    exact intervalIntegral.integral_nonneg_of_forall
      (le_of_lt (neg_lt_self Real.pi_pos)) fun t =>
        momentCrossCovarianceProduct_nonneg_local
          rho.auxiliaryCutoff eps _ _ _ _
  have hcrossRhs0 :
      0 ≤ |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        (((m : ℝ) ^ 8 *
          r324ResidualFourierMajorantBase rho ^ m * eps⁻¹ ^ 8) *
        ∫ t in -Real.pi..Real.pi,
          momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.1
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.1
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.2
            (r324CommonLeftMomentTranslation v coord t)) := by
    exact mul_nonneg
      (mul_nonneg
        (pow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _)
        (inv_nonneg.mpr
          (mul_nonneg (by norm_num) Real.pi_pos.le)))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (pow_nonneg (Nat.cast_nonneg m) _)
            (pow_nonneg
              (le_trans (by norm_num)
                (one_le_r324ResidualFourierMajorantBase rho)) _))
          (pow_nonneg (inv_nonneg.mpr heps.le) _))
        hint)
  rw [hfun, fourierCoeffOn.const_mul, norm_mul,
    norm_r324ResidualRealizedStationaryFactorC]
  calc
    _ ≤ r324ResidualRealizedStationaryFactor
          rho eps e0 he0 coordinates v *
        (|(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
          (((m : ℝ) ^ 8 *
            r324ResidualFourierMajorantBase rho ^ m * eps⁻¹ ^ 8) *
          ∫ t in -Real.pi..Real.pi,
            momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.2
              (r324CommonLeftMomentTranslation v coord t))) :=
      mul_le_mul_of_nonneg_left hcross
        (r324ResidualRealizedStationaryFactor_nonneg
          rho eps e0 he0 coordinates v)
    _ ≤ (r324ResidualFourierMajorantBase rho ^ (2 * m) *
          r324ResidualRealizedStationaryFactor
            rho.auxiliaryCutoff eps e0 he0 coordinates v) *
        (|(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
          (((m : ℝ) ^ 8 *
            r324ResidualFourierMajorantBase rho ^ m * eps⁻¹ ^ 8) *
          ∫ t in -Real.pi..Real.pi,
            momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.2
              (r324CommonLeftMomentTranslation v coord t))) :=
      mul_le_mul_of_nonneg_right hstationary hcrossRhs0
    _ = _ := by
      rw [integral_r324ResidualPrimitiveCoordinateCommonLeft_auxiliary_eq
        rho eps e0 he0 coordinates v coord]
      have hpow :
          r324ResidualFourierMajorantBase rho ^ (3 * m) =
            r324ResidualFourierMajorantBase rho ^ (2 * m) *
              r324ResidualFourierMajorantBase rho ^ m := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      ring

/-- Eighth-order common-left Fourier decay for one realized residual
coordinate.  The analytic output is the mixed-cutoff product dictated by
the derivative allocation: the invariant factors keep `rho`, while every
cross factor uses `rho.auxiliaryCutoff`. -/
theorem norm_fourierCoeffOn_r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_le
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) (coord : Fin dim)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (neg_lt_self Real.pi_pos)
        (r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
          rho eps e0 coordinates v coord) n‖ ≤
      ‖r324ResidualRealizedStationaryFactorC
          rho eps e0 he0 coordinates v‖ *
        (|(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
          ((((r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.1.singles.card : ℝ) ^ 8 *
            rho.etaDerivativeMajorantConstant ^
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.1.singles.card *
            eps⁻¹ ^ 8) *
          ∫ t in -Real.pi..Real.pi,
            momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.2
              (r324CommonLeftMomentTranslation v coord t))) := by
  have hfun :
      r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
          rho eps e0 coordinates v coord =
        fun t =>
          r324ResidualRealizedStationaryFactorC
              rho eps e0 he0 coordinates v *
            r324MomentCrossCommonLeftCoordLineC rho eps
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.1
              (r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.2
              v coord t := by
    funext t
    exact r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_eq
      rho eps e0 he0 coordinates v coord t
  rw [hfun, fourierCoeffOn.const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le
      rho heps
      (r324RefinedContractionOfResidualCoordinates
        e0 he0 coordinates).1.1
      (r324RefinedContractionOfResidualCoordinates
        e0 he0 coordinates).1.2.1
      (r324RefinedContractionOfResidualCoordinates
        e0 he0 coordinates).1.2.2
      v coord hn)
    (norm_nonneg _)

/-! ## The grouped residual primitive sum -/

/-- The complete residual primitive sum along the common-left coordinate
line.  The finite primitive-coordinate family remains grouped inside this
function. -/
def r324ResidualPrimitiveSumCommonLeftCoordLineC
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) : ℂ :=
  (r324ResidualPrimitiveSumProduct rho eps
      e0.1 e0.2.1 e0.2.2
      (r324CommonLeftMomentTranslation v coord t) : ℂ)

/-- Exact finite-coordinate expansion of the grouped common-left line. -/
theorem r324ResidualPrimitiveSumCommonLeftCoordLineC_eq_sum
    (rho : SmoothCutoff) (eps : ℝ) {m : ℕ}
    (e0 : MomentContraction m)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (t : ℝ) :
    r324ResidualPrimitiveSumCommonLeftCoordLineC
        rho eps e0 v coord t =
      ∑ coordinates : R324ResidualPrimitiveCoordinates
          e0.1 e0.2.1 e0.2.2,
        r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
          rho eps e0 coordinates v coord t := by
  unfold r324ResidualPrimitiveSumCommonLeftCoordLineC
    r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
  rw [r324ResidualPrimitiveSumProduct_eq_sum_coordinates]
  push_cast
  rfl

/-- Every realized coordinate line is interval-integrable. -/
theorem intervalIntegrable_r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) (coord : Fin dim) :
    IntervalIntegrable
      (r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
        rho eps e0 coordinates v coord)
      volume (-Real.pi) Real.pi := by
  rw [show r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
      rho eps e0 coordinates v coord =
      fun t =>
        r324ResidualRealizedStationaryFactorC
            rho eps e0 he0 coordinates v *
          r324MomentCrossCommonLeftCoordLineC rho eps
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.1
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.1
            (r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.2
            v coord t by
    funext t
    exact r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_eq
      rho eps e0 he0 coordinates v coord t]
  have hcross : Continuous
      (r324MomentCrossCommonLeftCoordLineC rho eps
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.1
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.2.1
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.2.2
        v coord) := by
    rw [show r324MomentCrossCommonLeftCoordLineC rho eps
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.1
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.2.1
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.2.2
        v coord =
      rho.etaPeriodizationCoordLineProductC
        (Finset.univ : Finset
          (r324RefinedContractionOfResidualCoordinates
            e0 he0 coordinates).1.1.singles) eps
        (fun i => torusLift
          (v (leftMomentIndex i.1) -
            v (rightMomentIndex
              ((r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.2 i).1)))
        (fun _ => coord)
        (fun i => torusLift
          (v (leftMomentIndex i.1) -
            v (rightMomentIndex
              ((r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.2.2 i).1)) coord) by
      funext t
      exact r324MomentCrossCommonLeftCoordLineC_eq_etaProductC
        rho eps
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.1
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.2.1
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.2.2
        v coord t]
    exact (rho.contDiff_etaPeriodizationCoordLineProductC_eight
      (Finset.univ : Finset
        (r324RefinedContractionOfResidualCoordinates
          e0 he0 coordinates).1.1.singles)
      heps
      (fun i => torusLift
        (v (leftMomentIndex i.1) -
          v (rightMomentIndex
            ((r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.2 i).1)))
      (fun _ => coord)
      (fun i => torusLift
        (v (leftMomentIndex i.1) -
          v (rightMomentIndex
            ((r324RefinedContractionOfResidualCoordinates
              e0 he0 coordinates).1.2.2 i).1)) coord)).continuous
  exact (continuous_const.mul hcross).intervalIntegrable _ _

/-- Fourier coefficient commutes with the finite residual-coordinate sum.
This is the only triangle-inequality seam in the grouped theorem. -/
theorem fourierCoeffOn_r324ResidualPrimitiveSumCommonLeftCoordLineC_eq_sum
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) (coord : Fin dim) (n : ℤ) :
    fourierCoeffOn (neg_lt_self Real.pi_pos)
        (r324ResidualPrimitiveSumCommonLeftCoordLineC
          rho eps e0 v coord) n =
      ∑ coordinates : R324ResidualPrimitiveCoordinates
          e0.1 e0.2.1 e0.2.2,
        fourierCoeffOn (neg_lt_self Real.pi_pos)
          (r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
            rho eps e0 coordinates v coord) n := by
  have hline :
      r324ResidualPrimitiveSumCommonLeftCoordLineC
          rho eps e0 v coord =
        fun t =>
          ∑ coordinates : R324ResidualPrimitiveCoordinates
              e0.1 e0.2.1 e0.2.2,
            r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
              rho eps e0 coordinates v coord t := by
    funext t
    exact r324ResidualPrimitiveSumCommonLeftCoordLineC_eq_sum
      rho eps e0 v coord t
  rw [hline]
  simp_rw [fourierCoeffOn_eq_integral]
  simp_rw [Finset.smul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [Finset.smul_sum]
  · intro coordinates _hcoordinates
    exact
      (intervalIntegrable_r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
        rho heps e0 he0 coordinates v coord).continuousOn_smul
          (((map_continuous (fourier (-n))).comp
            (AddCircle.continuous_mk' _)).continuousOn)

/-- Grouped common-left Fourier estimate for the residual primitive sum.
It is honest but still mixed-cutoff: each summand keeps its invariant
within-half covariance factors at `rho`, while the transformed cross family
uses `rho.auxiliaryCutoff`. -/
theorem norm_fourierCoeffOn_r324ResidualPrimitiveSumCommonLeftCoordLineC_le
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) (coord : Fin dim)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (neg_lt_self Real.pi_pos)
        (r324ResidualPrimitiveSumCommonLeftCoordLineC
          rho eps e0 v coord) n‖ ≤
      ∑ coordinates : R324ResidualPrimitiveCoordinates
          e0.1 e0.2.1 e0.2.2,
        ‖r324ResidualRealizedStationaryFactorC
            rho eps e0 he0 coordinates v‖ *
          (|(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
            ((((r324RefinedContractionOfResidualCoordinates
                e0 he0 coordinates).1.1.singles.card : ℝ) ^ 8 *
              rho.etaDerivativeMajorantConstant ^
                (r324RefinedContractionOfResidualCoordinates
                  e0 he0 coordinates).1.1.singles.card *
              eps⁻¹ ^ 8) *
            ∫ t in -Real.pi..Real.pi,
              momentCrossCovarianceProduct rho.auxiliaryCutoff eps m
                (r324RefinedContractionOfResidualCoordinates
                  e0 he0 coordinates).1.1
                (r324RefinedContractionOfResidualCoordinates
                  e0 he0 coordinates).1.2.1
                (r324RefinedContractionOfResidualCoordinates
                  e0 he0 coordinates).1.2.2
                (r324CommonLeftMomentTranslation v coord t))) := by
  rw [fourierCoeffOn_r324ResidualPrimitiveSumCommonLeftCoordLineC_eq_sum
    rho heps e0 he0 v coord n]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun coordinates _ =>
      norm_fourierCoeffOn_r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_le
        rho heps e0 he0 coordinates v coord hn)

/-- Real auxiliary coordinate lines are interval-integrable. -/
theorem intervalIntegrable_r324ResidualPrimitiveCoordinateCommonLeft_auxiliary
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (coordinates : R324ResidualPrimitiveCoordinates
      e0.1 e0.2.1 e0.2.2)
    (v : Fin (2 * m) → T4) (coord : Fin dim) :
    IntervalIntegrable
      (fun t =>
        r324ResidualPrimitiveCoordinateProduct rho.auxiliaryCutoff eps
          e0.1 e0.2.1 e0.2.2 coordinates
          (r324CommonLeftMomentTranslation v coord t))
      volume (-Real.pi) Real.pi := by
  have hcomplex :=
    (intervalIntegrable_r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
      rho.auxiliaryCutoff heps e0 he0 coordinates v coord).norm
  have hnonneg (t : ℝ) :
      0 ≤ r324ResidualPrimitiveCoordinateProduct rho.auxiliaryCutoff eps
        e0.1 e0.2.1 e0.2.2 coordinates
        (r324CommonLeftMomentTranslation v coord t) := by
    rw [r324ResidualPrimitiveCoordinateProduct_eq_pairingCovarianceProductOn
      rho.auxiliaryCutoff eps e0 he0 coordinates]
    exact Finset.prod_nonneg fun i _ =>
      rho.auxiliaryCutoff.etaEpsT4_nonneg eps _
  have hfun :
      (fun t =>
        ‖r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
          rho.auxiliaryCutoff eps e0 coordinates v coord t‖) =
      (fun t =>
        r324ResidualPrimitiveCoordinateProduct rho.auxiliaryCutoff eps
          e0.1 e0.2.1 e0.2.2 coordinates
          (r324CommonLeftMomentTranslation v coord t)) := by
    funext t
    unfold r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
  rwa [hfun] at hcomplex

/-- **Grouped common-left residual Fourier producer.**  After upgrading the
two stationary families by the zeroth-order auxiliary estimate, the finite
coordinate sum recombines exactly into the complete residual primitive sum
of `auxiliaryCutoff`.  The loss remains exponential in the perturbative
order and is therefore absorbable into the paper's named base constant. -/
theorem norm_fourierCoeffOn_r324ResidualPrimitiveSumCommonLeftCoordLineC_le_auxiliary
    (rho : SmoothCutoff) {eps : ℝ} (heps : 0 < eps) {m : ℕ}
    (e0 : MomentContraction m)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (he0 : e0 ∈ momentRefinedContractionFiber m s r)
    (v : Fin (2 * m) → T4) (coord : Fin dim)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn (neg_lt_self Real.pi_pos)
        (r324ResidualPrimitiveSumCommonLeftCoordLineC
          rho eps e0 v coord) n‖ ≤
      (|(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
        ((m : ℝ) ^ 8 *
          r324ResidualFourierMajorantBase rho ^ (3 * m) * eps⁻¹ ^ 8)) *
        ∫ t in -Real.pi..Real.pi,
          r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
            e0.1 e0.2.1 e0.2.2
            (r324CommonLeftMomentTranslation v coord t) := by
  rw [fourierCoeffOn_r324ResidualPrimitiveSumCommonLeftCoordLineC_eq_sum
    rho heps e0 he0 v coord n]
  let common : ℝ :=
    |(n : ℝ)|⁻¹ ^ 8 * (2 * Real.pi)⁻¹ *
      ((m : ℝ) ^ 8 *
        r324ResidualFourierMajorantBase rho ^ (3 * m) * eps⁻¹ ^ 8)
  calc
    ‖∑ coordinates : R324ResidualPrimitiveCoordinates
          e0.1 e0.2.1 e0.2.2,
        fourierCoeffOn (neg_lt_self Real.pi_pos)
          (r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
            rho eps e0 coordinates v coord) n‖ ≤
        ∑ coordinates : R324ResidualPrimitiveCoordinates
            e0.1 e0.2.1 e0.2.2,
          ‖fourierCoeffOn (neg_lt_self Real.pi_pos)
            (r324ResidualPrimitiveCoordinateCommonLeftCoordLineC
              rho eps e0 coordinates v coord) n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ coordinates : R324ResidualPrimitiveCoordinates
            e0.1 e0.2.1 e0.2.2,
          common *
            ∫ t in -Real.pi..Real.pi,
              r324ResidualPrimitiveCoordinateProduct
                rho.auxiliaryCutoff eps
                e0.1 e0.2.1 e0.2.2 coordinates
                (r324CommonLeftMomentTranslation v coord t) := by
      apply Finset.sum_le_sum
      intro coordinates _hcoordinates
      simpa only [common, mul_assoc] using
        norm_fourierCoeffOn_r324ResidualPrimitiveCoordinateCommonLeftCoordLineC_le_auxiliary
          rho heps e0 he0 coordinates v coord hn
    _ = common *
        ∑ coordinates : R324ResidualPrimitiveCoordinates
            e0.1 e0.2.1 e0.2.2,
          ∫ t in -Real.pi..Real.pi,
            r324ResidualPrimitiveCoordinateProduct
              rho.auxiliaryCutoff eps
              e0.1 e0.2.1 e0.2.2 coordinates
              (r324CommonLeftMomentTranslation v coord t) := by
      rw [Finset.mul_sum]
    _ = common *
        ∫ t in -Real.pi..Real.pi,
          ∑ coordinates : R324ResidualPrimitiveCoordinates
              e0.1 e0.2.1 e0.2.2,
            r324ResidualPrimitiveCoordinateProduct
              rho.auxiliaryCutoff eps
              e0.1 e0.2.1 e0.2.2 coordinates
              (r324CommonLeftMomentTranslation v coord t) := by
      rw [intervalIntegral.integral_finsetSum]
      intro coordinates _hcoordinates
      exact
        intervalIntegrable_r324ResidualPrimitiveCoordinateCommonLeft_auxiliary
          rho heps e0 he0 coordinates v coord
    _ = common *
        ∫ t in -Real.pi..Real.pi,
          r324ResidualPrimitiveSumProduct rho.auxiliaryCutoff eps
            e0.1 e0.2.1 e0.2.2
            (r324CommonLeftMomentTranslation v coord t) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _ht
      exact (r324ResidualPrimitiveSumProduct_eq_sum_coordinates
        rho.auxiliaryCutoff eps e0.1 e0.2.1 e0.2.2 _).symm
    _ = _ := rfl

end

end Anderson4D
