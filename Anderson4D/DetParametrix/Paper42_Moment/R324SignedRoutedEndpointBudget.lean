import Anderson4D.DetParametrix.Paper42_Moment.R324GroupedCovarianceBudget
import Anderson4D.DetParametrix.Paper42_Moment.R324MarkedResidualComplementBudget

/-!
# Signed slot budgets for the routed R-324 endpoint series

The final central-frequency route must attach one reciprocal eighth-order
cost to a common-increment group without first replacing that group by the
sum of the absolute covariance coefficients.  This file splits the exact
grouped route weight into its finitely many marked-slot contributions.

The qualitative facts (integrability and summability) are proved from the
concrete grouped cores.  The quantitative input left to the primitive
collapse is slotwise, so the paper-scale total bound is no longer repeated
as a field of the constructor.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-! ## The two endpoint cases in paper Step 4 -/

/-- The two cases at one external endpoint after the within-half
reductions.

* `directFourier` is the case where the terminal endpoint is not contained
  in a removed fully-paired interval; its Green factor is Fourier integrated
  directly.
* `insertedSacrifice` is the case where the terminal endpoint belongs to
  such an interval; the same Fourier factor is retained, but the inserted
  primitive estimate is replaced by the ordinary one at cost `ε⁻²`.
-/
inductive R324EndpointReductionCase
  | directFourier
  | insertedSacrifice
  deriving DecidableEq, Fintype

/-- Interpret an outgoing endpoint-difference flag as the paper's
two-case split.  This applies only to a right endpoint: incoming endpoints
have a separate carrier-survival test below. -/
def r324EndpointReductionCaseOfFlag :
    Bool → R324EndpointReductionCase
  | false => .directFourier
  | true => .insertedSacrifice

/-- The incoming endpoint is direct precisely when the first internal
vertex survives all within-half primitive collapses.  If that vertex is
removed, its free Green leg must be Fourier-integrated before the
responsible block is absorbed, and the ordinary primitive estimate is
used at the paper's `ε⁻²` sacrifice.

At order zero there is no internal endpoint and the choice is immaterial;
we use the direct branch as the canonical empty-order value. -/
def r324IncomingEndpointReductionCase
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    R324EndpointReductionCase :=
  if hm : 0 < m then
    if (⟨0, hm⟩ : Fin m) ∈ finalActive κ then
      .directFourier
    else
      .insertedSacrifice
  else
    .directFourier

@[simp]
theorem r324IncomingEndpointReductionCase_eq_direct
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hm : 0 < m)
    (hfirst : (⟨0, hm⟩ : Fin m) ∈ finalActive κ) :
    r324IncomingEndpointReductionCase κ =
      .directFourier := by
  simp [r324IncomingEndpointReductionCase, hm, hfirst]

@[simp]
theorem r324IncomingEndpointReductionCase_eq_inserted
    {m : ℕ} (κ : PartialPairing (Fin m))
    (hm : 0 < m)
    (hfirst : (⟨0, hm⟩ : Fin m) ∉ finalActive κ) :
    r324IncomingEndpointReductionCase κ =
      .insertedSacrifice := by
  simp [r324IncomingEndpointReductionCase, hm, hfirst]

/-- Primitive-estimate cost of one endpoint case.  The factor two from a
Green difference belongs to the exact Fourier coefficient and is not
counted again here. -/
def r324EndpointPrimitiveSacrifice
    (ε : ℝ) : R324EndpointReductionCase → ℝ
  | .directFourier => 1
  | .insertedSacrifice => ε⁻¹ ^ (2 : ℕ)

theorem r324EndpointPrimitiveSacrifice_nonneg
    (ε : ℝ) (c : R324EndpointReductionCase) :
    0 ≤ r324EndpointPrimitiveSacrifice ε c := by
  cases c with
  | directFourier =>
      simp [r324EndpointPrimitiveSacrifice]
  | insertedSacrifice =>
      unfold r324EndpointPrimitiveSacrifice
      positivity

theorem r324EndpointPrimitiveSacrifice_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : R324EndpointReductionCase) :
    r324EndpointPrimitiveSacrifice ε c ≤
      ε⁻¹ ^ (2 : ℕ) := by
  cases c with
  | directFourier =>
      simp only [r324EndpointPrimitiveSacrifice]
      have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
      exact one_le_pow₀ hinv
  | insertedSacrifice =>
      exact le_rfl

/-- Explicit endpoint-case ledger for one refined schedule.

The incoming cases are governed by survival of the first internal vertex;
the outgoing cases are governed by extraction of the final chain edge.
These are distinct tests even though both ultimately select the same
ordinary-versus-inserted primitive estimate. -/
def r324RefinedEndpointReductionCase
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    Fin 4 → R324EndpointReductionCase :=
  let e := r324RefinedScheduleRepresentative p
  ![
    r324IncomingEndpointReductionCase e.1,
    r324EndpointReductionCaseOfFlag
      (r324OutgoingIsShortcut e.1),
    r324IncomingEndpointReductionCase e.2.1,
    r324EndpointReductionCaseOfFlag
      (r324OutgoingIsShortcut e.2.1)
  ]

@[simp]
theorem r324RefinedEndpointReductionCase_zero
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    r324RefinedEndpointReductionCase p 0 =
      r324IncomingEndpointReductionCase
        (r324RefinedScheduleRepresentative p).1 :=
  rfl

@[simp]
theorem r324RefinedEndpointReductionCase_two
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    r324RefinedEndpointReductionCase p 2 =
      r324IncomingEndpointReductionCase
        (r324RefinedScheduleRepresentative p).2.1 :=
  rfl

@[simp]
theorem r324RefinedEndpointReductionCase_one
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    r324RefinedEndpointReductionCase p 1 =
      r324EndpointReductionCaseOfFlag
        (r324OutgoingIsShortcut
          (r324RefinedScheduleRepresentative p).1) := by
  rfl

@[simp]
theorem r324RefinedEndpointReductionCase_three
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    r324RefinedEndpointReductionCase p 3 =
      r324EndpointReductionCaseOfFlag
        (r324OutgoingIsShortcut
          (r324RefinedScheduleRepresentative p).2.1) := by
  rfl

/-- Product of the four explicit primitive-estimate case costs. -/
def r324EndpointPrimitiveSacrificeProduct
    (ε : ℝ) (cases : Fin 4 → R324EndpointReductionCase) : ℝ :=
  ∏ j, r324EndpointPrimitiveSacrifice ε (cases j)

theorem r324EndpointPrimitiveSacrificeProduct_nonneg
    (ε : ℝ) (cases : Fin 4 → R324EndpointReductionCase) :
    0 ≤ r324EndpointPrimitiveSacrificeProduct ε cases := by
  unfold r324EndpointPrimitiveSacrificeProduct
  exact Finset.prod_nonneg fun j _ =>
    r324EndpointPrimitiveSacrifice_nonneg ε (cases j)

/-- Uniformizing the two cases only after all four endpoint Fourier
integrations costs at most `ε⁻⁸`. -/
theorem r324EndpointPrimitiveSacrificeProduct_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (cases : Fin 4 → R324EndpointReductionCase) :
    r324EndpointPrimitiveSacrificeProduct ε cases ≤
      ε⁻¹ ^ (8 : ℕ) := by
  unfold r324EndpointPrimitiveSacrificeProduct
  calc
    (∏ j : Fin 4,
        r324EndpointPrimitiveSacrifice ε (cases j)) ≤
        ∏ _j : Fin 4, ε⁻¹ ^ (2 : ℕ) := by
      apply Finset.prod_le_prod
      · intro j _hj
        exact r324EndpointPrimitiveSacrifice_nonneg ε (cases j)
      · intro j _hj
        exact r324EndpointPrimitiveSacrifice_le hε hε1 (cases j)
    _ = ε⁻¹ ^ (8 : ℕ) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- Every explicit endpoint-case cost is at least one in the paper
regime.  Thus introducing the case ledger never understates the exact
endpoint Fourier integral. -/
theorem one_le_r324EndpointPrimitiveSacrifice
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (c : R324EndpointReductionCase) :
    1 ≤ r324EndpointPrimitiveSacrifice ε c := by
  cases c with
  | directFourier =>
      simp [r324EndpointPrimitiveSacrifice]
  | insertedSacrifice =>
      unfold r324EndpointPrimitiveSacrifice
      exact one_le_pow₀ ((one_le_inv₀ hε).2 hε1)

theorem one_le_r324EndpointPrimitiveSacrificeProduct
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (cases : Fin 4 → R324EndpointReductionCase) :
    1 ≤ r324EndpointPrimitiveSacrificeProduct ε cases := by
  unfold r324EndpointPrimitiveSacrificeProduct
  exact Finset.one_le_prod fun j _ =>
    one_le_r324EndpointPrimitiveSacrifice hε hε1 (cases j)

/-- Endpoint coefficient budget before the two cases are uniformized.
The Fourier coefficients, and hence the `α`/`β` decays, are evaluated
before this nonnegative case cost is applied. -/
def r324CaseSeparatedEndpointWeight
    (ε : ℝ) (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (cases : Fin 4 → R324EndpointReductionCase) : ℝ :=
  r324EndpointPrimitiveSacrificeProduct ε cases *
    r324FourEndpointCoefficientWeight α β anchors flags

/-- The explicit two-case endpoint ledger gives exactly the same final
`ε⁻⁸⟨α⟩⁻⁴⟨β⟩⁻⁴` budget as the paper, while keeping the direct and
inserted-sacrifice branches distinguishable upstream. -/
theorem r324CaseSeparatedEndpointWeight_le
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (cases : Fin 4 → R324EndpointReductionCase) :
    r324CaseSeparatedEndpointWeight
        ε α β anchors flags cases ≤
      16 * r324EndpointLoss ε α β := by
  calc
    r324CaseSeparatedEndpointWeight
          ε α β anchors flags cases ≤
        r324SacrificedEndpointCoefficientWeight
          ε α β anchors flags := by
      unfold r324CaseSeparatedEndpointWeight
        r324SacrificedEndpointCoefficientWeight
      exact mul_le_mul_of_nonneg_right
        (r324EndpointPrimitiveSacrificeProduct_le
          hε hε1 cases)
        (r324FourEndpointCoefficientWeight_nonneg
          α β anchors flags)
    _ ≤ 16 * r324EndpointLoss ε α β :=
      r324SacrificedEndpointCoefficientWeight_le
        ε α β anchors flags

/-- Endpoint-first integration routed through the explicit case ledger.
This is the local statement used below by the new routed constructor; it
does not appeal to the old uniform-sacrifice endpoint theorem. -/
theorem norm_integral_r324EndpointSeparatedIntegrand_le_caseLedger
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (cases : Fin 4 → R324EndpointReductionCase)
    (core : ℂ) :
    ‖∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand
          α β anchors flags core x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure‖ ≤
      (16 * r324EndpointLoss ε α β) * ‖core‖ := by
  have hweight :
      r324FourEndpointCoefficientWeight α β anchors flags ≤
        r324CaseSeparatedEndpointWeight
          ε α β anchors flags cases := by
    unfold r324CaseSeparatedEndpointWeight
    calc
      r324FourEndpointCoefficientWeight α β anchors flags =
          1 *
            r324FourEndpointCoefficientWeight
              α β anchors flags := by ring
      _ ≤
          r324EndpointPrimitiveSacrificeProduct ε cases *
            r324FourEndpointCoefficientWeight
              α β anchors flags :=
        mul_le_mul_of_nonneg_right
          (one_le_r324EndpointPrimitiveSacrificeProduct
            hε hε1 cases)
          (r324FourEndpointCoefficientWeight_nonneg
            α β anchors flags)
  rw [norm_integral_r324EndpointSeparatedIntegrand]
  calc
    r324FourEndpointCoefficientWeight α β anchors flags *
          ‖core‖ ≤
        r324CaseSeparatedEndpointWeight
            ε α β anchors flags cases * ‖core‖ :=
      mul_le_mul_of_nonneg_right hweight (norm_nonneg core)
    _ ≤
        (16 * r324EndpointLoss ε α β) * ‖core‖ :=
      mul_le_mul_of_nonneg_right
        (r324CaseSeparatedEndpointWeight_le
          hε hε1 α β anchors flags cases)
        (norm_nonneg core)

/-- The canonical ledger attached to a refined schedule, with
carrier-survival tests at the two incoming endpoints and extraction-edge
tests at the two outgoing endpoints, controls its actual endpoint
integral. -/
theorem
    norm_integral_r324EndpointSeparatedIntegrand_le_refinedCaseLedger
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m)
    (v : Fin (2 * m) → T4)
    (core : ℂ) :
    ‖∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand α β
          (r324ContractionEndpointAnchors hm
            (r324RefinedScheduleRepresentative p) v)
          (r324ContractionEndpointFlags
            (r324RefinedScheduleRepresentative p))
          core x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure‖ ≤
      (16 * r324EndpointLoss ε α β) * ‖core‖ :=
  norm_integral_r324EndpointSeparatedIntegrand_le_caseLedger
    hε hε1 α β
    (r324ContractionEndpointAnchors hm
      (r324RefinedScheduleRepresentative p) v)
    (r324ContractionEndpointFlags
      (r324RefinedScheduleRepresentative p))
    (r324RefinedEndpointReductionCase p)
    core

/-- The genuine endpoint Fourier estimate before *any*
ordinary-versus-inserted primitive sacrifice is charged.  This is the
endpoint estimate used with the `ε⁸`-normalized route weight below. -/
theorem norm_integral_r324EndpointSeparatedIntegrand_le_fourierOnly
    (α β : Z4)
    (anchors : R324EndpointAnchors)
    (flags : R324EndpointFlags)
    (core : ℂ) :
    ‖∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand
          α β anchors flags core x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure‖ ≤
      (16 * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β) * ‖core‖ := by
  rw [norm_integral_r324EndpointSeparatedIntegrand]
  exact
    mul_le_mul_of_nonneg_right
      (r324FourEndpointCoefficientWeight_le
        α β anchors flags)
      (norm_nonneg core)

/-! ## Qualitative control of the signed grouped core -/

/-- The norm of a common-increment covariance group is bounded by the
fibrewise sum of the raw coefficient norms.  The norm is taken only after
the complete refined contraction fibre has been summed. -/
theorem norm_r324KeyGroupedCovarianceConfiguration_le
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324KeyGroupedCovarianceConfiguration hm ε p b v‖ ≤
      ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b := by
  let key : Fin m → Z4 :=
    r324NatEquivStandardConfigurations hm b
  let S :=
    {a : ℕ // r324RefinedRawIncrementKey hm p a = key}
  have hraw :
      Summable fun a =>
        ‖ρ.r324RefinedRawCovarianceConfiguration
          hm ε p a v‖ :=
    ρ.summable_norm_r324RefinedRawCovarianceConfiguration
      hm hε p v
  have hsub :
      Summable fun a : S =>
        ‖ρ.r324RefinedRawCovarianceConfiguration
          hm ε p a.1 v‖ :=
    hraw.subtype _
  unfold r324KeyGroupedCovarianceConfiguration
    r324KeyGroupedRefinedCovarianceWeight tsumByKey
  change
    ‖∑' a : S,
        ρ.r324RefinedRawCovarianceConfiguration
          hm ε p a.1 v‖ ≤
      ∑' a : S,
        ρ.r324RefinedRawCovarianceWeight hm ε p a.1
  calc
    ‖∑' a : S,
        ρ.r324RefinedRawCovarianceConfiguration
          hm ε p a.1 v‖ ≤
        ∑' a : S,
          ‖ρ.r324RefinedRawCovarianceConfiguration
            hm ε p a.1 v‖ :=
      norm_tsum_le_tsum_norm hsub
    _ = ∑' a : S,
          ρ.r324RefinedRawCovarianceWeight hm ε p a.1 := by
      apply tsum_congr
      intro a
      exact
        ρ.norm_r324RefinedRawCovarianceConfiguration
          hm ε p a.1 v

/-- Pointwise signed-core majorant.  The complete compatible primitive
fibre remains inside the norm on the left. -/
theorem norm_r324KeyGroupedRefinedEndpointCore_le
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) (b : ℕ)
    (v : Fin (2 * m) → T4) :
    ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖ ≤
      r324SelectedInteriorSkeletonNormDensity
          (r324RefinedScheduleRepresentative p).1
          (r324RefinedScheduleRepresentative p).2.1 v *
        ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b := by
  unfold r324KeyGroupedRefinedEndpointCore
    r324SelectedInteriorSkeletonNormDensity
  rw [norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (ρ.norm_r324KeyGroupedCovarianceConfiguration_le
      hm hε p b v)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Every signed common-increment internal core has finite `L¹` mass.
This closes the qualitative field of
`IntegratedPrimitiveCollapseBudget` without an analytic hypothesis. -/
theorem integrable_norm_r324KeyGroupedRefinedEndpointCore
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    Integrable
      (fun v : Fin (2 * m) → T4 =>
        ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  let e₀ := r324RefinedScheduleRepresentative p
  let W : ℝ :=
    ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b
  let majorant : (Fin (2 * m) → T4) → ℝ := fun v =>
    r324SelectedInteriorSkeletonNormDensity e₀.1 e₀.2.1 v * W
  have hmajorant : Integrable majorant
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
    dsimp only [majorant]
    exact
      (integrable_r324SelectedInteriorSkeletonNormDensity
        e₀.1 e₀.2.1).mul_const W
  have hmeas :
      AEStronglyMeasurable
        (fun v : Fin (2 * m) → T4 =>
          ‖ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
    let key : Fin m → Z4 :=
      r324NatEquivStandardConfigurations hm b
    let S :=
      {a : ℕ // r324RefinedRawIncrementKey hm p a = key}
    have hleft :
        Measurable fun v : Fin (2 * m) → T4 =>
          r324RenormalizedInteriorCore e₀.1
            (fun i => v (leftMomentIndex i)) :=
      (measurable_r324RenormalizedInteriorCore e₀.1).comp
        (measurable_pi_lambda _ fun i =>
          measurable_pi_apply (leftMomentIndex i))
    have hright :
        Measurable fun v : Fin (2 * m) → T4 =>
          r324RenormalizedInteriorCore e₀.2.1
            (fun i => v (rightMomentIndex i)) :=
      (measurable_r324RenormalizedInteriorCore e₀.2.1).comp
        (measurable_pi_lambda _ fun i =>
          measurable_pi_apply (rightMomentIndex i))
    have hraw :
        ∀ a : S,
          Measurable fun v : Fin (2 * m) → T4 =>
            ρ.r324RefinedRawEndpointCore hm ε p a.1 v := by
      intro a
      unfold r324RefinedRawEndpointCore
        r324RefinedRawCovarianceConfiguration
      dsimp only
      exact (hleft.mul hright).mul
        (ρ.measurable_r324CovarianceFourierConfigurationTerm
          ε _ _)
    have hsum :
        AEMeasurable
          (fun v : Fin (2 * m) → T4 =>
            ∑' a : S,
              ρ.r324RefinedRawEndpointCore hm ε p a.1 v)
          (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
      AEMeasurable.tsum fun a => (hraw a).aemeasurable
    have heq :
        (fun v : Fin (2 * m) → T4 =>
          ρ.r324KeyGroupedRefinedEndpointCore hm ε p b v) =ᵐ[
            Measure.pi fun _ : Fin (2 * m) => paperMeasure]
          (fun v =>
            ∑' a : S,
              ρ.r324RefinedRawEndpointCore hm ε p a.1 v) := by
      exact Filter.Eventually.of_forall fun v =>
        ρ.r324KeyGroupedRefinedEndpointCore_eq_tsumByKey
          hm ε p b v
    exact ((hsum.congr heq.symm).norm).aestronglyMeasurable
  apply Integrable.mono' hmajorant hmeas
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact
      ρ.norm_r324KeyGroupedRefinedEndpointCore_le
        hm hε p b v

/-- `L¹` mass of the two signed, endpoint-independent Green profiles for
one refined schedule. -/
def r324RefinedInteriorSkeletonL1
    {m : ℕ} (p : R324RefinedScheduleIndex m) : ℝ :=
  ∫ v : Fin (2 * m) → T4,
    r324SelectedInteriorSkeletonNormDensity
      (r324RefinedScheduleRepresentative p).1
      (r324RefinedScheduleRepresentative p).2.1 v
    ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)

theorem r324RefinedInteriorSkeletonL1_nonneg
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    0 ≤ r324RefinedInteriorSkeletonL1 p := by
  unfold r324RefinedInteriorSkeletonL1
  exact integral_nonneg fun v =>
    r324SelectedInteriorSkeletonNormDensity_nonneg _ _ v

/-- The signed grouped core is bounded by its schedule's exact Green
profile mass times the scalar covariance mass.  This estimate is used only
to prove qualitative summability, not for the paper-scale bound. -/
theorem r324GroupedRefinedCoreL1_le_skeleton_mul_covariance
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (p : R324RefinedScheduleIndex m) (b : ℕ) :
    ρ.r324GroupedRefinedCoreL1 hm ε (p, b) ≤
      r324RefinedInteriorSkeletonL1 p *
        ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b := by
  let e₀ := r324RefinedScheduleRepresentative p
  let W : ℝ :=
    ρ.r324KeyGroupedRefinedCovarianceWeight hm ε p b
  have hcore :=
    ρ.integrable_norm_r324KeyGroupedRefinedEndpointCore
      hm hε p b
  have hskeleton :=
    integrable_r324SelectedInteriorSkeletonNormDensity
      e₀.1 e₀.2.1
  have hmajor :
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          r324SelectedInteriorSkeletonNormDensity
            e₀.1 e₀.2.1 v * W)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
    hskeleton.mul_const W
  unfold r324GroupedRefinedCoreL1
    r324RefinedInteriorSkeletonL1
  change
    (∫ v, ‖ρ.r324KeyGroupedRefinedEndpointCore
        hm ε p b v‖
      ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) ≤
      (∫ v,
          r324SelectedInteriorSkeletonNormDensity
            e₀.1 e₀.2.1 v
        ∂Measure.pi fun _ : Fin (2 * m) => paperMeasure) * W
  rw [← integral_mul_const]
  exact integral_mono hcore hmajor fun v =>
    ρ.norm_r324KeyGroupedRefinedEndpointCore_le
      hm hε p b v

/-- A finite qualitative envelope for all refined Green-profile masses at
fixed order. -/
def r324AllRefinedInteriorSkeletonL1 (m : ℕ) : ℝ :=
  ∑ p : R324RefinedScheduleIndex m,
    r324RefinedInteriorSkeletonL1 p

theorem r324AllRefinedInteriorSkeletonL1_nonneg (m : ℕ) :
    0 ≤ r324AllRefinedInteriorSkeletonL1 m := by
  unfold r324AllRefinedInteriorSkeletonL1
  exact Finset.sum_nonneg fun p _ =>
    r324RefinedInteriorSkeletonL1_nonneg p

theorem r324RefinedInteriorSkeletonL1_le_all
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    r324RefinedInteriorSkeletonL1 p ≤
      r324AllRefinedInteriorSkeletonL1 m := by
  unfold r324AllRefinedInteriorSkeletonL1
  exact Finset.single_le_sum
    (fun q _ => r324RefinedInteriorSkeletonL1_nonneg q)
    (Finset.mem_univ p)

/-- The grouped route base weights are summable without assuming the
paper-scale estimate.  The coarse scalar majorant is confined to this
qualitative convergence proof. -/
theorem summable_r324GroupedRouteBaseWeight_signed
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    Summable (ρ.r324GroupedRouteBaseWeight lam hm ε) := by
  apply
    ρ.summable_r324GroupedRouteBaseWeight_of_coreCovarianceMajorant
      lam (r324AllRefinedInteriorSkeletonL1 m) hm hε
  intro p
  calc
    ρ.r324GroupedRefinedCoreL1 hm ε p ≤
        r324RefinedInteriorSkeletonL1 p.1 *
          ρ.r324KeyGroupedRefinedCovarianceWeight
            hm ε p.1 p.2 :=
      ρ.r324GroupedRefinedCoreL1_le_skeleton_mul_covariance
        hm hε p.1 p.2
    _ ≤ r324AllRefinedInteriorSkeletonL1 m *
          ρ.r324KeyGroupedRefinedCovarianceWeight
            hm ε p.1 p.2 :=
      mul_le_mul_of_nonneg_right
        (r324RefinedInteriorSkeletonL1_le_all p.1)
        (ρ.r324KeyGroupedRefinedCovarianceWeight_nonneg
          hm ε p.1 p.2)

/-- Endpoint-normalized complete grouped route weight.  The factor `ε⁸`
belongs to the primitive-collapse side and cancels the four possible
ordinary-versus-inserted sacrifices. -/
def r324EndpointNormalizedGroupedRouteBaseWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  ε ^ (8 : ℕ) *
    ρ.r324GroupedRouteBaseWeight lam hm ε p

theorem r324EndpointNormalizedGroupedRouteBaseWeight_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤
      ρ.r324EndpointNormalizedGroupedRouteBaseWeight
        lam hm ε p :=
  mul_nonneg (by positivity)
    (ρ.r324GroupedRouteBaseWeight_nonneg lam hm ε p)

theorem summable_r324EndpointNormalizedGroupedRouteBaseWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    Summable
      (ρ.r324EndpointNormalizedGroupedRouteBaseWeight
        lam hm ε) := by
  exact
    (ρ.summable_r324GroupedRouteBaseWeight_signed
      lam hm hε).mul_left (ε ^ (8 : ℕ))

/-! ## Local routed estimate with primitive-side normalization -/

/-- Local grouped routed estimate for the endpoint-normalized base
weight.  Only the genuine four Fourier coefficients are estimated at the
endpoint; the `ε⁻⁸` in `r324EndpointLoss` cancels the `ε⁸` carried by the
base weight.  The primitive branch costs are therefore paid exactly once,
inside the collapse data below. -/
theorem
    norm_r324GroupedEndpointConfigurationTerm_le_normalizedRouteWeight_mul_decay
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ)
    (hcore :
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          ‖ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2 v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure))
    (i : Fin m) :
    ‖r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)‖ ≤
      ((16 * r324EndpointLoss ε α β) *
          ρ.r324EndpointNormalizedGroupedRouteBaseWeight
            lam hm ε p) *
        eighthOrderFrequencyDecay
          ‖ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i‖ := by
  by_cases hzero :
      r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p.1)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2) =
        0
  · rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (r324EndpointLoss_nonneg ε α β))
        (ρ.r324EndpointNormalizedGroupedRouteBaseWeight_nonneg
          lam hm ε p))
      (eighthOrderFrequencyDecay_nonneg _)
  · have hincrement :
        ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i =
          z4EuclideanFrequency
            (r324NatEquivStandardConfigurations
              hm p.2 i) := by
      simp [r324ConcreteRefinedIncrement, hzero]
    rw [hincrement]
    let scale : ℝ :=
      16 * paperFourthOrderModeDecay α *
        paperFourthOrderModeDecay β
    let scalar : ℝ :=
      |lamEps lam ε| ^ (2 * m)
    let core :
        (Fin (2 * m) → T4) → ℂ :=
      ρ.r324KeyGroupedRefinedEndpointCore
        hm ε p.1 p.2
    let endpointIntegral :
        (Fin (2 * m) → T4) → ℂ := fun v =>
      ∫ x, ∫ y, ∫ z, ∫ w,
        r324EndpointSeparatedIntegrand α β
          (r324ContractionEndpointAnchors hm
            (r324RefinedScheduleRepresentative p.1) v)
          (r324ContractionEndpointFlags
            (r324RefinedScheduleRepresentative p.1))
          (core v) x y z w
        ∂paperMeasure ∂paperMeasure
        ∂paperMeasure ∂paperMeasure
    have hscale : 0 ≤ scale := by
      dsimp only [scale]
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (paperFourthOrderModeDecay_nonneg α))
        (paperFourthOrderModeDecay_nonneg β)
    have hscalar : 0 ≤ scalar := by
      dsimp only [scalar]
      positivity
    have hcore' :
        Integrable (fun v => ‖core v‖)
          (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      exact hcore
    have hmajor :
        Integrable (fun v => scale * ‖core v‖)
          (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
      simpa only [smul_eq_mul] using
        hcore'.const_mul scale
    have hpoint :
        ∀ v, ‖endpointIntegral v‖ ≤
          scale * ‖core v‖ := by
      intro v
      exact
        norm_integral_r324EndpointSeparatedIntegrand_le_fourierOnly
          α β
          (r324ContractionEndpointAnchors hm
            (r324RefinedScheduleRepresentative p.1) v)
          (r324ContractionEndpointFlags
            (r324RefinedScheduleRepresentative p.1))
          (core v)
    have hintegral :
        ‖∫ v, endpointIntegral v
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)‖ ≤
          ∫ v, scale * ‖core v‖
            ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) :=
      norm_integral_le_of_norm_le hmajor
        (Filter.Eventually.of_forall hpoint)
    have hmass :
        0 ≤ ρ.r324GroupedRefinedCoreL1 hm ε p :=
      ρ.r324GroupedRefinedCoreL1_nonneg hm ε p
    have htermCore :
        ‖r324GroupedEndpointConfigurationTerm
            hm ρ lam ε α β
            (r324RefinedScheduleRepresentative p.1)
            (ρ.r324KeyGroupedRefinedEndpointCore
              hm ε p.1 p.2)‖ ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p) := by
      unfold r324GroupedEndpointConfigurationTerm
      change
        ‖(lamEps lam ε ^ (2 * m) : ℂ) *
            ∫ v, endpointIntegral v
              ∂(Measure.pi fun _ : Fin (2 * m) =>
                paperMeasure)‖ ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p)
      rw [norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs]
      calc
        |lamEps lam ε| ^ (2 * m) *
              ‖∫ v, endpointIntegral v
                ∂(Measure.pi fun _ : Fin (2 * m) =>
                  paperMeasure)‖ ≤
            scalar *
              ∫ v, scale * ‖core v‖
                ∂(Measure.pi fun _ : Fin (2 * m) =>
                  paperMeasure) :=
          mul_le_mul_of_nonneg_left hintegral hscalar
        _ = scale *
              (scalar *
                ρ.r324GroupedRefinedCoreL1 hm ε p) := by
          rw [integral_const_mul]
          unfold r324GroupedRefinedCoreL1
          dsimp only [scalar]
          ring
    have hcost :
        r324GroupedIncrementCost hm p.2 i ≤
          ∑ j : Fin m,
            r324GroupedIncrementCost hm p.2 j :=
      Finset.single_le_sum
        (fun j _ =>
          (r324GroupedIncrementCost_pos hm p.2 j).le)
        (Finset.mem_univ i)
    have hdecay :
        0 ≤
          eighthOrderFrequencyDecay
            ‖z4EuclideanFrequency
              (r324NatEquivStandardConfigurations
                hm p.2 i)‖ :=
      eighthOrderFrequencyDecay_nonneg _
    have hbaseCore :
        0 ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p) :=
      mul_nonneg hscale (mul_nonneg hscalar hmass)
    calc
      ‖r324GroupedEndpointConfigurationTerm
          hm ρ lam ε α β
          (r324RefinedScheduleRepresentative p.1)
          (ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2)‖ ≤
          scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p) :=
        htermCore
      _ =
          (scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p)) *
            (r324GroupedIncrementCost hm p.2 i *
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency
                  (r324NatEquivStandardConfigurations
                    hm p.2 i)‖) := by
        rw [r324GroupedIncrementCost_mul_decay]
        ring
      _ ≤
          (scale *
            (scalar *
              ρ.r324GroupedRefinedCoreL1 hm ε p)) *
            ((∑ j : Fin m,
                r324GroupedIncrementCost hm p.2 j) *
              eighthOrderFrequencyDecay
                ‖z4EuclideanFrequency
                  (r324NatEquivStandardConfigurations
                    hm p.2 i)‖) := by
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcost hdecay)
            hbaseCore
      _ =
          ((16 * r324EndpointLoss ε α β) *
            ρ.r324EndpointNormalizedGroupedRouteBaseWeight
              lam hm ε p) *
            eighthOrderFrequencyDecay
              ‖z4EuclideanFrequency
                (r324NatEquivStandardConfigurations
                  hm p.2 i)‖ := by
        unfold r324EndpointNormalizedGroupedRouteBaseWeight
        unfold r324GroupedRouteBaseWeight
        unfold r324EndpointLoss
        dsimp only [scalar]
        field_simp [hε.ne']
        ring

/-- Raw-weight estimate for the pre-normalization helper API below. -/
theorem
    norm_r324GroupedEndpointConfigurationTerm_le_caseLedgerRouteWeight_mul_decay
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4)
    (p : R324RefinedScheduleIndex m × ℕ)
    (hcore :
      Integrable
        (fun v : Fin (2 * m) → T4 =>
          ‖ρ.r324KeyGroupedRefinedEndpointCore
            hm ε p.1 p.2 v‖)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure))
    (i : Fin m) :
    ‖r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)‖ ≤
      ((16 * r324EndpointLoss ε α β) *
          ρ.r324GroupedRouteBaseWeight lam hm ε p) *
        eighthOrderFrequencyDecay
          ‖ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i‖ :=
  ρ.norm_r324GroupedEndpointConfigurationTerm_le_groupedRouteBaseWeight_mul_decay
    lam hm hε hε1 α β p hcore i

/-! ## Exact finite marked-slot decomposition -/

/-- Contribution of one marked increment slot to the grouped route
weight.  The norm is still taken after the complete compatible primitive
fibre has been summed. -/
def r324SignedRouteSlotWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  |lamEps lam ε| ^ (2 * m) *
    ρ.r324GroupedRefinedCoreL1 hm ε p *
    r324GroupedIncrementCost hm p.2 i

/-- Endpoint-normalized marked-slot weight.  The factor `ε⁸` is kept on
the primitive-density side.  It cancels the four possible `ε⁻²`
ordinary-versus-inserted sacrifices before the hard-coded
`r324EndpointLoss` is attached by the routing layer. -/
def r324EndpointNormalizedSignedRouteSlotWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m × ℕ) : ℝ :=
  ε ^ (8 : ℕ) *
    ρ.r324SignedRouteSlotWeight lam hm ε i p

theorem r324SignedRouteSlotWeight_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤ ρ.r324SignedRouteSlotWeight lam hm ε i p := by
  unfold r324SignedRouteSlotWeight
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (ρ.r324GroupedRefinedCoreL1_nonneg hm ε p))
    (r324GroupedIncrementCost_pos hm p.2 i).le

theorem r324EndpointNormalizedSignedRouteSlotWeight_nonneg
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m × ℕ) :
    0 ≤
      ρ.r324EndpointNormalizedSignedRouteSlotWeight
        lam hm ε i p :=
  mul_nonneg (by positivity)
    (ρ.r324SignedRouteSlotWeight_nonneg lam hm ε i p)

/-- The old base weight is definitionally the finite sum of the genuine
marked-slot weights. -/
theorem r324GroupedRouteBaseWeight_eq_sum_signedRouteSlotWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) :
    ρ.r324GroupedRouteBaseWeight lam hm ε p =
      ∑ i : Fin m,
        ρ.r324SignedRouteSlotWeight lam hm ε i p := by
  unfold r324GroupedRouteBaseWeight
    r324SignedRouteSlotWeight
  rw [Finset.mul_sum]

/-- The normalized grouped weight is still exactly the finite sum of its
normalized marked-slot pieces. -/
theorem
    r324EndpointNormalizedGroupedRouteBaseWeight_eq_sum_slotWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (p : R324RefinedScheduleIndex m × ℕ) :
    ρ.r324EndpointNormalizedGroupedRouteBaseWeight
        lam hm ε p =
      ∑ i : Fin m,
        ρ.r324EndpointNormalizedSignedRouteSlotWeight
          lam hm ε i p := by
  unfold r324EndpointNormalizedGroupedRouteBaseWeight
    r324EndpointNormalizedSignedRouteSlotWeight
  rw [
    ρ.r324GroupedRouteBaseWeight_eq_sum_signedRouteSlotWeight,
    Finset.mul_sum]

/-- Each marked-slot weight is bounded by the complete base weight. -/
theorem r324SignedRouteSlotWeight_le_baseWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m) (ε : ℝ)
    (i : Fin m)
    (p : R324RefinedScheduleIndex m × ℕ) :
    ρ.r324SignedRouteSlotWeight lam hm ε i p ≤
      ρ.r324GroupedRouteBaseWeight lam hm ε p := by
  let A : ℝ :=
    |lamEps lam ε| ^ (2 * m) *
      ρ.r324GroupedRefinedCoreL1 hm ε p
  have hA : 0 ≤ A :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _)
      (ρ.r324GroupedRefinedCoreL1_nonneg hm ε p)
  have hcost :
      r324GroupedIncrementCost hm p.2 i ≤
        ∑ j : Fin m,
          r324GroupedIncrementCost hm p.2 j :=
    Finset.single_le_sum
      (fun j _ =>
        (r324GroupedIncrementCost_pos hm p.2 j).le)
      (Finset.mem_univ i)
  unfold r324SignedRouteSlotWeight
    r324GroupedRouteBaseWeight
  exact mul_le_mul_of_nonneg_left hcost hA

/-- Every marked-slot series is summable, independently of the
paper-scale quantitative collapse. -/
theorem summable_r324SignedRouteSlotWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) :
    Summable
      (ρ.r324SignedRouteSlotWeight lam hm ε i) := by
  exact
    (ρ.summable_r324GroupedRouteBaseWeight_signed
      lam hm hε).of_nonneg_of_le
      (ρ.r324SignedRouteSlotWeight_nonneg lam hm ε i)
      (ρ.r324SignedRouteSlotWeight_le_baseWeight lam hm ε i)

theorem summable_r324EndpointNormalizedSignedRouteSlotWeight
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (i : Fin m) :
    Summable
      (ρ.r324EndpointNormalizedSignedRouteSlotWeight
        lam hm ε i) := by
  exact
    (ρ.summable_r324SignedRouteSlotWeight
      lam hm hε i).mul_left (ε ^ (8 : ℕ))

/-- Exact exchange of the countable grouped sum with the finite marked
slot sum.  This is the cancellation-preserving boundary at which the
primitive collapse may estimate one selected high-frequency edge. -/
theorem tsum_r324GroupedRouteBaseWeight_eq_sum_slot_tsum
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    (∑' p,
      ρ.r324GroupedRouteBaseWeight lam hm ε p) =
      ∑ i : Fin m,
        ∑' p,
          ρ.r324SignedRouteSlotWeight lam hm ε i p := by
  calc
    (∑' p,
        ρ.r324GroupedRouteBaseWeight lam hm ε p) =
        ∑' p,
          ∑ i : Fin m,
            ρ.r324SignedRouteSlotWeight lam hm ε i p := by
      apply tsum_congr
      intro p
      exact
        ρ.r324GroupedRouteBaseWeight_eq_sum_signedRouteSlotWeight
          lam hm ε p
    _ = ∑ i : Fin m,
          ∑' p,
            ρ.r324SignedRouteSlotWeight lam hm ε i p := by
      rw [Summable.tsum_finsetSum
        (s := (Finset.univ : Finset (Fin m)))
        (fun i _hi =>
          ρ.summable_r324SignedRouteSlotWeight
            lam hm hε i)]

theorem
    tsum_r324EndpointNormalizedGroupedRouteBaseWeight_eq_sum_slot_tsum
    (lam : ℝ) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    (∑' p,
      ρ.r324EndpointNormalizedGroupedRouteBaseWeight
        lam hm ε p) =
      ∑ i : Fin m,
        ∑' p,
          ρ.r324EndpointNormalizedSignedRouteSlotWeight
            lam hm ε i p := by
  calc
    (∑' p,
        ρ.r324EndpointNormalizedGroupedRouteBaseWeight
          lam hm ε p) =
        ∑' p,
          ∑ i : Fin m,
            ρ.r324EndpointNormalizedSignedRouteSlotWeight
              lam hm ε i p := by
      apply tsum_congr
      intro p
      exact
        ρ.r324EndpointNormalizedGroupedRouteBaseWeight_eq_sum_slotWeight
          lam hm ε p
    _ = ∑ i : Fin m,
          ∑' p,
            ρ.r324EndpointNormalizedSignedRouteSlotWeight
              lam hm ε i p := by
      rw [Summable.tsum_finsetSum
        (s := (Finset.univ : Finset (Fin m)))
        (fun i _hi =>
          ρ.summable_r324EndpointNormalizedSignedRouteSlotWeight
            lam hm hε i)]

/-! ## Non-circular primitive-collapse consumer -/

/-- Quantitative output expected from the signed marked-edge primitive
collapse.  It bounds each marked slot separately; it does not contain the
downstream total `tsum_baseWeight_le` statement.

The endpoint cases are recoverable from
`r324RefinedEndpointReductionCase`, while the central-frequency cost is
attached only to `r324SignedRouteSlotWeight`. -/
structure SignedRoutedPrimitiveSlotBudget
    (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (slotAmplitude : Fin m → ℝ) : Prop where
  slot_tsum_le :
    ∀ i : Fin m,
      (∑' p,
        ρ.r324SignedRouteSlotWeight lam hm ε i p) ≤
          slotAmplitude i

/-- Slotwise budget for the endpoint-normalized weights used by the
paper-faithful routed constructor. -/
structure EndpointNormalizedSignedRoutedPrimitiveSlotBudget
    (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (slotAmplitude : Fin m → ℝ) : Prop where
  slot_tsum_le :
    ∀ i : Fin m,
      (∑' p,
        ρ.r324EndpointNormalizedSignedRouteSlotWeight
          lam hm ε i p) ≤
        slotAmplitude i

/-! ## Proposition 4.1 / phase-A input boundary -/

/-- The actual Proposition 4.1 majorant used by one endpoint case.
The direct branch retains the diameter insertion.  The sacrifice branch,
which occurs when the adjacent internal vertex is absorbed by a primitive
collapse, is the ordinary `J` majorant. -/
def r324EndpointCasePrimitiveMajorant
    (c : R324EndpointReductionCase)
    (C lam ε supportConstant : ℝ) (m : ℕ) (z : T4) : ℝ :=
  match c with
  | .directFourier =>
      primitiveInsertedMajorant C lam ε supportConstant m z
  | .insertedSacrifice =>
      primitiveKernelMajorant C lam ε supportConstant m z

/-- **Constructive ordinary-versus-inserted bridge.**

The direct branch is already inserted.  In the absorbed-vertex branch
the terminal density is the ordinary `J` majorant and Proposition 4.1's
diameter insertion is genuinely given up at cost `ε⁻²`.  The cost is
therefore charged to the primitive density, not to a Fourier coefficient.
This description applies equally to incoming and outgoing endpoints. -/
theorem r324EndpointCasePrimitiveMajorant_le_sacrifice_mul_inserted
    (c : R324EndpointReductionCase)
    (C lam supportConstant : ℝ) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) (z : T4) :
    r324EndpointCasePrimitiveMajorant
        c C lam ε supportConstant m z ≤
      r324EndpointPrimitiveSacrifice ε c *
        primitiveInsertedMajorant
          C lam ε supportConstant m z := by
  cases c with
  | directFourier =>
      simp [r324EndpointCasePrimitiveMajorant,
        r324EndpointPrimitiveSacrifice]
  | insertedSacrifice =>
      simpa [r324EndpointCasePrimitiveMajorant,
        r324EndpointPrimitiveSacrifice] using
        primitiveKernelMajorant_le_invSq_mul_inserted
          C lam ε supportConstant m z hε

/-- The case majorant is integrable in both branches. -/
theorem integrable_r324EndpointCasePrimitiveMajorant
    (c : R324EndpointReductionCase)
    (C lam supportConstant : ℝ) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable
      (r324EndpointCasePrimitiveMajorant
        c C lam ε supportConstant m)
      paperMeasure := by
  cases c with
  | directFourier =>
      exact
        integrable_primitiveInsertedMajorant
          C lam ε supportConstant m hε
  | insertedSacrifice =>
      exact
        integrable_primitiveKernelMajorant
          C lam ε supportConstant m hε

/-- The finite four-endpoint case pattern retained by the collapse
certificate. -/
abbrev R324EndpointReductionPattern :=
  Fin 4 → R324EndpointReductionCase

/-- Density majorant after applying the constructive one-endpoint bridge
at every endpoint in a case pattern. -/
def r324EndpointPatternAdjustedPrimitiveMajorant
    (ε : ℝ) (cases : R324EndpointReductionPattern)
    (C lam supportConstant : ℝ) (m : ℕ) (z : T4) : ℝ :=
  r324EndpointPrimitiveSacrificeProduct ε cases *
    primitiveInsertedMajorant
      C lam ε supportConstant m z

/-- Multiplying a four-case-adjusted density by `ε⁸` cancels all possible
ordinary-`J` sacrifices. -/
theorem eps_pow_eight_mul_endpointPatternAdjustedMajorant_le_inserted
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (cases : R324EndpointReductionPattern)
    {C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (supportConstant : ℝ) (m : ℕ) (z : T4) :
    ε ^ (8 : ℕ) *
        r324EndpointPatternAdjustedPrimitiveMajorant
          ε cases C lam supportConstant m z ≤
      primitiveInsertedMajorant
        C lam ε supportConstant m z := by
  have hcost :=
    r324EndpointPrimitiveSacrificeProduct_le
      hε hε1 cases
  have hscale :
      ε ^ (8 : ℕ) *
          r324EndpointPrimitiveSacrificeProduct ε cases ≤ 1 := by
    calc
      ε ^ (8 : ℕ) *
            r324EndpointPrimitiveSacrificeProduct ε cases ≤
          ε ^ (8 : ℕ) * ε⁻¹ ^ (8 : ℕ) :=
        mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = 1 := by
        field_simp [hε.ne']
  unfold r324EndpointPatternAdjustedPrimitiveMajorant
  calc
    ε ^ (8 : ℕ) *
          (r324EndpointPrimitiveSacrificeProduct ε cases *
            primitiveInsertedMajorant
              C lam ε supportConstant m z) =
        (ε ^ (8 : ℕ) *
          r324EndpointPrimitiveSacrificeProduct ε cases) *
            primitiveInsertedMajorant
              C lam ε supportConstant m z := by ring
    _ ≤
        1 *
          primitiveInsertedMajorant
            C lam ε supportConstant m z :=
      mul_le_mul_of_nonneg_right hscale
        (primitiveInsertedMajorant_nonneg hC hlam)
    _ =
        primitiveInsertedMajorant
          C lam ε supportConstant m z := by ring

/-- The canonical scalar output of the signed phase-A iteration and the
one-open-edge cross-terminal consumer.

For every possible routed slot, phase A splits the actual
relative-endpoint density by the four endpoint-case pattern.  The direct
branch retains `primitiveInsertedMajorant`; the absorbed-vertex branch uses
ordinary `primitiveKernelMajorant`, and the constructive theorem above
charges its `ε⁻²` loss to the density.  The four adjusted costs are then
cancelled by the `ε⁸` normalization before the routing layer introduces
`r324EndpointLoss`.

The forthcoming marker-preserving phase-A closure can instantiate the
fields directly by grouping schedules according to
`r324RefinedEndpointReductionCase`. -/
structure SignedRoutedPrimitiveSlotCollapseData
    (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (primitiveConstant supportConstant : ℝ) : Type where
  density :
    Fin m → R324EndpointReductionPattern → T4 → ℝ
  density_integrable :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern),
      Integrable (density i cases) paperMeasure
  normalized_slot_fiber_le_scaled_case_density_integrals :
    ∀ i : Fin m,
      (∑' p,
        ρ.r324EndpointNormalizedSignedRouteSlotWeight
          lam hm ε i p) ≤
        ∑ cases : R324EndpointReductionPattern,
          ∫ z,
            ε ^ (8 : ℕ) * density i cases z
            ∂paperMeasure
  pointwise_case_domination :
    ∀ (i : Fin m) (cases : R324EndpointReductionPattern)
      (z : T4),
      density i cases z ≤
        r324EndpointPatternAdjustedPrimitiveMajorant
          ε cases primitiveConstant lam supportConstant m z

/-- Construct the normalized collapse datum from the raw phase-A
case-fibre inequality.  This is the exact place where the `ε⁸`
normalization is moved through the countable sum and the finite family of
density integrals. -/
def signedRoutedPrimitiveSlotCollapseData_of_rawCaseDensities
    (lam ε : ℝ)
    {m : ℕ} (hm : 0 < m)
    (primitiveConstant supportConstant : ℝ)
    (density :
      Fin m → R324EndpointReductionPattern → T4 → ℝ)
    (density_integrable :
      ∀ (i : Fin m) (cases : R324EndpointReductionPattern),
        Integrable (density i cases) paperMeasure)
    (raw_slot_fiber_le_case_density_integrals :
      ∀ i : Fin m,
        (∑' p,
          ρ.r324SignedRouteSlotWeight lam hm ε i p) ≤
          ∑ cases : R324EndpointReductionPattern,
            ∫ z, density i cases z ∂paperMeasure)
    (pointwise_case_domination :
      ∀ (i : Fin m) (cases : R324EndpointReductionPattern)
        (z : T4),
        density i cases z ≤
          r324EndpointPatternAdjustedPrimitiveMajorant
            ε cases primitiveConstant lam supportConstant m z) :
    ρ.SignedRoutedPrimitiveSlotCollapseData
      lam ε m hm primitiveConstant supportConstant := by
  refine
    { density := density
      density_integrable := density_integrable
      normalized_slot_fiber_le_scaled_case_density_integrals := ?_
      pointwise_case_domination := pointwise_case_domination }
  intro i
  calc
    (∑' p,
        ρ.r324EndpointNormalizedSignedRouteSlotWeight
          lam hm ε i p) =
        ε ^ (8 : ℕ) *
          ∑' p,
            ρ.r324SignedRouteSlotWeight lam hm ε i p := by
      unfold r324EndpointNormalizedSignedRouteSlotWeight
      rw [tsum_mul_left]
    _ ≤
        ε ^ (8 : ℕ) *
          ∑ cases : R324EndpointReductionPattern,
            ∫ z, density i cases z ∂paperMeasure :=
      mul_le_mul_of_nonneg_left
        (raw_slot_fiber_le_case_density_integrals i)
        (by positivity)
    _ =
        ∑ cases : R324EndpointReductionPattern,
          ∫ z,
            ε ^ (8 : ℕ) * density i cases z
            ∂paperMeasure := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro cases _hcases
      rw [integral_const_mul]

/-- A concrete phase-A/cross-terminal certificate gives the normalized
slot budget.  The proof first uses the actual ordinary-`J` case costs in
the density, then cancels those costs with `ε⁸`; it never attaches the
cost to a Fourier coefficient. -/
theorem
    endpointNormalizedSignedRoutedPrimitiveSlotBudget_of_collapseData
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (primitiveConstant supportConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (d :
      ρ.SignedRoutedPrimitiveSlotCollapseData
        lam ε m hm primitiveConstant supportConstant) :
    ρ.EndpointNormalizedSignedRoutedPrimitiveSlotBudget
      lam ε m hm
        (fun _i =>
          16 *
            ∫ z,
              primitiveInsertedMajorant primitiveConstant lam ε
                supportConstant m z
              ∂paperMeasure) := by
  refine ⟨?_⟩
  intro i
  let I : ℝ :=
    ∫ z,
      primitiveInsertedMajorant primitiveConstant lam ε
        supportConstant m z
      ∂paperMeasure
  have hinserted :
      Integrable
        (primitiveInsertedMajorant primitiveConstant lam ε
          supportConstant m)
        paperMeasure :=
    integrable_primitiveInsertedMajorant
      primitiveConstant lam ε supportConstant m hε
  calc
    (∑' p,
        ρ.r324EndpointNormalizedSignedRouteSlotWeight
          lam hm ε i p) ≤
        ∑ cases : R324EndpointReductionPattern,
          ∫ z,
            ε ^ (8 : ℕ) * d.density i cases z
            ∂paperMeasure :=
      d.normalized_slot_fiber_le_scaled_case_density_integrals i
    _ ≤
        ∑ _cases : R324EndpointReductionPattern, I := by
      apply Finset.sum_le_sum
      intro cases _hcases
      dsimp only [I]
      apply integral_mono
        ((d.density_integrable i cases).const_mul
          (ε ^ (8 : ℕ)))
        hinserted
      intro z
      calc
        ε ^ (8 : ℕ) * d.density i cases z ≤
            ε ^ (8 : ℕ) *
              r324EndpointPatternAdjustedPrimitiveMajorant
                ε cases primitiveConstant lam
                  supportConstant m z :=
          mul_le_mul_of_nonneg_left
            (d.pointwise_case_domination i cases z)
            (by positivity)
        _ ≤
            primitiveInsertedMajorant primitiveConstant lam ε
              supportConstant m z :=
          eps_pow_eight_mul_endpointPatternAdjustedMajorant_le_inserted
            hε hε1 cases hprimitive hlam supportConstant m z
    _ = 16 * I := by
      have hcard :
          Fintype.card R324EndpointReductionCase = 2 := by
        rfl
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin]
      rw [hcard]
      norm_num [I]

/-- Slotwise signed primitive estimates construct the old downstream
budget.  Integrability and summability are theorems here, not fields
repeated as analytic assumptions. -/
theorem
    integratedPrimitiveCollapseBudget_of_signedRoutedPrimitiveSlots
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε)
    (slotAmplitude : Fin m → ℝ)
    (d :
      ρ.SignedRoutedPrimitiveSlotBudget
        lam ε m hm slotAmplitude) :
    ρ.IntegratedPrimitiveCollapseBudget
      lam ε m hm (∑ i, slotAmplitude i) := by
  refine
    { integrable_groupedCore := ?_
      summable_baseWeight :=
        ρ.summable_r324GroupedRouteBaseWeight_signed
          lam hm hε
      tsum_baseWeight_le := ?_ }
  · intro p
    exact
      ρ.integrable_norm_r324KeyGroupedRefinedEndpointCore
        hm hε p.1 p.2
  · rw [
      ρ.tsum_r324GroupedRouteBaseWeight_eq_sum_slot_tsum
        lam hm hε]
    exact Finset.sum_le_sum fun i _ => d.slot_tsum_le i

/-- Case-ledger routed consumer.  Its exact countable configuration expansion
uses the local estimate
the theorem above whose endpoint proof explicitly traverses the four
`R324EndpointReductionCase`s. -/
theorem
    countableCentralRoutedMomentReductionOutput_of_integratedPrimitiveCollapseBudget_caseLedger
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (α β : Z4) (amplitude : ℝ)
    (budget :
      ρ.IntegratedPrimitiveCollapseBudget
        lam ε m hm amplitude) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β
        ((16 * amplitude) *
          r324EndpointLoss ε α β) := by
  let concrete :=
    ρ.r324ConcreteRefinedCoreExpansion
      lam hm hε hmtrunc α β
  let routed :=
    concrete.toRefinedFourierRoutingData hε hε1
  apply
    routed.toCountableCentralRoutedMomentReductionOutput
      (ρ.r324GroupedRouteBaseWeight lam hm ε)
      amplitude
      budget.summable_baseWeight
      (ρ.r324GroupedRouteBaseWeight_nonneg lam hm ε)
      budget.tsum_baseWeight_le
  intro p i
  change
    ‖r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)‖ ≤
      ((16 * r324EndpointLoss ε α β) *
          ρ.r324GroupedRouteBaseWeight lam hm ε p) *
        eighthOrderFrequencyDecay
          ‖ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i‖
  exact
    ρ.norm_r324GroupedEndpointConfigurationTerm_le_caseLedgerRouteWeight_mul_decay
      lam hm hε hε1 α β p
      (budget.integrable_groupedCore p) i

/-- Direct routed-output constructor from the slotwise signed collapse.
The endpoint loss is introduced only after the explicit endpoint case
ledger and the central marked-slot budget have both closed. -/
theorem
    countableCentralRoutedMomentReductionOutput_of_signedRoutedPrimitiveSlots
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (α β : Z4)
    (slotAmplitude : Fin m → ℝ)
    (d :
      ρ.SignedRoutedPrimitiveSlotBudget
        lam ε m hm slotAmplitude) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β
        ((16 * (∑ i, slotAmplitude i)) *
          r324EndpointLoss ε α β) := by
  exact
    ρ.countableCentralRoutedMomentReductionOutput_of_integratedPrimitiveCollapseBudget_caseLedger
      lam hm hε hε1 hmtrunc α β
      (∑ i, slotAmplitude i)
      (ρ.integratedPrimitiveCollapseBudget_of_signedRoutedPrimitiveSlots
        lam hm hε slotAmplitude d)

/-! ## Canonical inserted-majorant amplitude and order absorption -/

/-- The exact normalized endpoint-free budget obtained from a
phase-A/cross-terminal certificate.  The factor `16` is the number of
four-endpoint case patterns; the only order-dependent loss is the literal
number `m` of possible marked slots. -/
theorem
    tsum_endpointNormalizedGroupedRouteBaseWeight_le_of_signedPrimitiveCollapse
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (primitiveConstant supportConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (d :
      ρ.SignedRoutedPrimitiveSlotCollapseData
        lam ε m hm primitiveConstant supportConstant) :
    (∑' p,
      ρ.r324EndpointNormalizedGroupedRouteBaseWeight
        lam hm ε p) ≤
      (m : ℝ) *
        (16 *
          ∫ z,
            primitiveInsertedMajorant primitiveConstant lam ε
              supportConstant m z
            ∂paperMeasure) := by
  let I : ℝ :=
    ∫ z,
      primitiveInsertedMajorant primitiveConstant lam ε
        supportConstant m z
      ∂paperMeasure
  have hslots :
      ρ.EndpointNormalizedSignedRoutedPrimitiveSlotBudget
        lam ε m hm (fun _i => 16 * I) := by
    exact
      ρ.endpointNormalizedSignedRoutedPrimitiveSlotBudget_of_collapseData
        lam hm hε hε1 primitiveConstant supportConstant
          hprimitive hlam d
  rw [
    ρ.tsum_r324EndpointNormalizedGroupedRouteBaseWeight_eq_sum_slot_tsum
      lam hm hε]
  calc
    (∑ i : Fin m,
        ∑' p,
          ρ.r324EndpointNormalizedSignedRouteSlotWeight
            lam hm ε i p) ≤
        ∑ _i : Fin m, 16 * I :=
      Finset.sum_le_sum fun i _ => hslots.slot_tsum_le i
    _ = (m : ℝ) * (16 * I) := by
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]

/-- Direct routed output at the unabsorbed canonical Proposition 4.1
integral.  Ordinary-`J` absorbed-vertex branches have already been paid on
the density side and cancelled by the normalized base weight. -/
theorem
    countableCentralRoutedMomentReductionOutput_of_signedRoutedPrimitiveCollapse
    (lam : ℝ)
    {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmtrunc : m ≤ truncOrder ε)
    (α β : Z4)
    (primitiveConstant supportConstant : ℝ)
    (hprimitive : 0 ≤ primitiveConstant)
    (hlam : 0 ≤ lam)
    (d :
      ρ.SignedRoutedPrimitiveSlotCollapseData
        lam ε m hm primitiveConstant supportConstant) :
    CountableCentralRoutedMomentReductionOutput
      ρ lam ε m α β
        ((16 *
            ((m : ℝ) *
              (16 *
                ∫ z,
                  primitiveInsertedMajorant primitiveConstant lam ε
                    supportConstant m z
                  ∂paperMeasure))) *
          r324EndpointLoss ε α β) := by
  let concrete :=
    ρ.r324ConcreteRefinedCoreExpansion
      lam hm hε hmtrunc α β
  let routed :=
    concrete.toRefinedFourierRoutingData hε hε1
  apply
    routed.toCountableCentralRoutedMomentReductionOutput
      (ρ.r324EndpointNormalizedGroupedRouteBaseWeight
        lam hm ε)
      ((m : ℝ) *
        (16 *
          ∫ z,
            primitiveInsertedMajorant primitiveConstant lam ε
              supportConstant m z
            ∂paperMeasure))
      (ρ.summable_r324EndpointNormalizedGroupedRouteBaseWeight
        lam hm hε)
      (ρ.r324EndpointNormalizedGroupedRouteBaseWeight_nonneg
        lam hm ε)
      (ρ.tsum_endpointNormalizedGroupedRouteBaseWeight_le_of_signedPrimitiveCollapse
        lam hm hε hε1 primitiveConstant supportConstant
          hprimitive hlam d)
  intro p i
  change
    ‖r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (ρ.r324KeyGroupedRefinedEndpointCore
          hm ε p.1 p.2)‖ ≤
      ((16 * r324EndpointLoss ε α β) *
          ρ.r324EndpointNormalizedGroupedRouteBaseWeight
            lam hm ε p) *
        eighthOrderFrequencyDecay
          ‖ρ.r324ConcreteRefinedIncrement
            lam hm ε α β p i‖
  exact
    ρ.norm_r324GroupedEndpointConfigurationTerm_le_normalizedRouteWeight_mul_decay
      lam hm hε α β p
      (ρ.integrable_norm_r324KeyGroupedRefinedEndpointCore
        hm hε p.1 p.2) i

/-- The number of possible marked slots is exponentially harmless in the
exact exponent needed after extracting the leading coupling square. -/
theorem r324_order_le_two_pow_double_sub_two
    {m : ℕ} (hm : 1 ≤ m) :
    m ≤ 2 ^ (2 * m - 2) := by
  rcases m with _ | k
  · omega
  rcases k with _ | k
  · norm_num
  calc
    k + 2 ≤ 2 ^ (k + 2) :=
      Nat.lt_two_pow_self.le
    _ ≤ 2 ^ (2 * (k + 2) - 2) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Radial integration plus the exact `m`-slot sum has the standard
paper-scale coupling form.  The loss `m` is absorbed by
`m ≤ 2^(2m-2)`, so it changes only the named power constant
`C ↦ 2C`; no polynomial-in-order factor remains. -/
theorem exists_signedRoutedPrimitiveCollapse_paperAmplitude
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (lam ε : ℝ) (m : ℕ),
        0 ≤ lam →
        0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 1 ≤ m →
        16 *
            ((m : ℝ) *
              (16 *
                ∫ z,
                  primitiveInsertedMajorant primitiveConstant lam ε
                    supportConstant m z
                  ∂paperMeasure)) ≤
          lamEps lam ε ^ 2 * outerConstant *
            ((2 * primitiveConstant) * lam) ^ (2 * m - 2) := by
  obtain ⟨Cball, Creg, hCball, hCreg, hmajorant⟩ :=
    exists_integral_primitiveInsertedMajorant_le
  let K : ℝ :=
    Cball * supportConstant ^ 2 + 2 * Creg
  let outerConstant : ℝ :=
    256 * K * primitiveConstant ^ 2
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have houter : 0 < outerConstant := by
    dsimp only [outerConstant]
    positivity
  refine ⟨outerConstant, houter, ?_⟩
  intro lam ε m hlam hε hε1 hlog hm
  let I : ℝ :=
    ∫ z,
      primitiveInsertedMajorant primitiveConstant lam ε
        supportConstant m z
      ∂paperMeasure
  have hlogPos : 0 < |Real.log ε| :=
    zero_lt_one.trans_le hlog
  have hI :
      I ≤
        (primitiveConstant * lam) ^ (2 * m) *
          (K / |Real.log ε|) := by
    dsimp only [I, K]
    exact
      hmajorant primitiveConstant lam ε supportConstant m
        hε hε1 hsupport hlog
  have hcountNat :
      m ≤ 2 ^ (2 * m - 2) :=
    r324_order_le_two_pow_double_sub_two hm
  have hcount :
      (m : ℝ) ≤ (2 : ℝ) ^ (2 * m - 2) := by
    exact_mod_cast hcountNat
  have hbase :
      0 ≤ primitiveConstant * lam :=
    mul_nonneg hprimitive.le hlam
  have hexp :
      2 * m = (2 * m - 2) + 2 := by
    omega
  have horder :
      (m : ℝ) * (primitiveConstant * lam) ^ (2 * m) ≤
        primitiveConstant ^ 2 * lam ^ 2 *
          ((2 * primitiveConstant) * lam) ^
            (2 * m - 2) := by
    calc
      (m : ℝ) * (primitiveConstant * lam) ^ (2 * m) =
          (m : ℝ) *
            ((primitiveConstant * lam) ^ (2 * m - 2) *
              (primitiveConstant * lam) ^ 2) := by
        congr 1
        calc
          (primitiveConstant * lam) ^ (2 * m) =
              (primitiveConstant * lam) ^ ((2 * m - 2) + 2) :=
            congrArg
              (fun e : ℕ => (primitiveConstant * lam) ^ e) hexp
          _ =
              (primitiveConstant * lam) ^ (2 * m - 2) *
                (primitiveConstant * lam) ^ 2 :=
            pow_add _ _ _
      _ ≤
          (2 : ℝ) ^ (2 * m - 2) *
            ((primitiveConstant * lam) ^ (2 * m - 2) *
              (primitiveConstant * lam) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hcount
          (mul_nonneg
            (pow_nonneg hbase _)
            (pow_nonneg hbase 2))
      _ =
          primitiveConstant ^ 2 * lam ^ 2 *
            ((2 * primitiveConstant) * lam) ^
              (2 * m - 2) := by
        rw [show
          (2 * primitiveConstant) * lam =
            2 * (primitiveConstant * lam) by ring,
          mul_pow]
        ring
  calc
    16 * ((m : ℝ) * (16 * I)) ≤
        16 *
          ((m : ℝ) *
            (16 *
              ((primitiveConstant * lam) ^ (2 * m) *
                (K / |Real.log ε|)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hI (by norm_num))
          (by positivity))
        (by norm_num)
    _ =
        (256 * (K / |Real.log ε|)) *
          ((m : ℝ) *
            (primitiveConstant * lam) ^ (2 * m)) := by
      ring
    _ ≤
        (256 * (K / |Real.log ε|)) *
          (primitiveConstant ^ 2 * lam ^ 2 *
            ((2 * primitiveConstant) * lam) ^
              (2 * m - 2)) := by
      exact mul_le_mul_of_nonneg_left horder (by positivity)
    _ =
        lamEps lam ε ^ 2 * outerConstant *
          ((2 * primitiveConstant) * lam) ^
            (2 * m - 2) := by
      rw [lamEps_sq hlogPos]
      dsimp only [outerConstant]
      ring

/-- Phase A and the selected cross-terminal certificate therefore produce
the routed paper-scale output directly.  The conclusion is monotone from
the exact unabsorbed endpoint budget, so no target-shaped total estimate
is assumed. -/
theorem
    exists_countableCentralRoutedMomentReductionOutput_of_signedPrimitiveCollapse
    {primitiveConstant supportConstant : ℝ}
    (hprimitive : 0 < primitiveConstant)
    (hsupport : 0 < supportConstant) :
    ∃ outerConstant : ℝ, 0 < outerConstant ∧
      ∀ (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
        (hm : 0 < m) (α β : Z4),
        0 ≤ lam →
        0 < ε → ε ≤ 1 / 4 → 1 ≤ |Real.log ε| →
        m ≤ truncOrder ε →
        ρ.SignedRoutedPrimitiveSlotCollapseData
          lam ε m hm primitiveConstant supportConstant →
        CountableCentralRoutedMomentReductionOutput
          ρ lam ε m α β
            ((lamEps lam ε ^ 2 * outerConstant *
                ((2 * primitiveConstant) * lam) ^
                  (2 * m - 2)) *
              r324EndpointLoss ε α β) := by
  obtain ⟨outerConstant, houter, hamp⟩ :=
    exists_signedRoutedPrimitiveCollapse_paperAmplitude
      hprimitive hsupport
  refine ⟨outerConstant, houter, ?_⟩
  intro ρ lam ε m hm α β hlam hε hεsmall hlog
    hmtrunc d
  have hε1 : ε ≤ 1 :=
    hεsmall.trans (by norm_num)
  have hraw :=
    ρ.countableCentralRoutedMomentReductionOutput_of_signedRoutedPrimitiveCollapse
      lam hm hε hε1 hmtrunc α β
        primitiveConstant supportConstant hprimitive.le hlam d
  apply hraw.mono
  exact mul_le_mul_of_nonneg_right
    (hamp lam ε m hlam hε hε1 hlog hm)
    (r324EndpointLoss_nonneg ε α β)

end SmoothCutoff

end

end Anderson4D
