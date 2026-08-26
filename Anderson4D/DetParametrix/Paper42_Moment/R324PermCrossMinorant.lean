import Anderson4D.DetParametrix.Paper42_Moment.R324PermCrossGreenFloor
import Anderson4D.DetParametrix.Paper42_Moment.R324LedgerThreeClosure
import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324InteriorLogBudgetProof
import Anderson4D.DetParametrix.Paper41_Renorm.R322Normalize

/-!
# R324PermCross: the factorial minorant of the pure-cross fibre

The summed pure-cross density of the full permutation fibre is bounded
*below* by `g₀^{2(m+1)} · m! · (2π)^{4(m+4)}`: the two plain Green
chains are at least `g₀^{2(m+1)}` almost everywhere (the Green floor),
and each of the `m!` bijection entities contributes exactly one full
covariance mass `(2π)^{4(m+4)}` — the periodized covariance has total
mass one at every scale, and the `m` cross legs pair the `2m` internal
coordinates bijectively.

The bijection count `m!` survives *because* of injectivity: it is the
exact cardinality of the pure-cross fibre.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The exact covariance mass -/

/-- **Unit covariance mass.**  The periodized mollified covariance
integrates to exactly `‖ρ̂(0)‖² = 1` at every scale `0 < ε`. -/
theorem r324PermCross_integral_eta_eq_one
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∫ z, ρ.etaEpsT4 ε z ∂paperMeasure = 1 := by
  set V : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hVdef
  have hV0 : 0 < V := by rw [hVdef]; positivity
  have hint : ∀ k : Z4,
      Integrable
        (fun z : T4 => ρ.covarianceModeCoeff ε k * charT4 k z)
        paperMeasure := by
    intro k
    refine (integrable_const
      ‖ρ.covarianceModeCoeff ε k‖).mono'
      (Continuous.aestronglyMeasurable ?_) ?_
    · exact continuous_const.mul (continuous_charT4 k)
    · filter_upwards with z
      rw [norm_mul, norm_charT4, mul_one]
  have hnormint : ∀ k : Z4,
      (∫ z, ‖ρ.covarianceModeCoeff ε k * charT4 k z‖
        ∂paperMeasure) = V * ‖ρ.covarianceModeCoeff ε k‖ := by
    intro k
    have hfun :
        (fun z : T4 =>
          ‖ρ.covarianceModeCoeff ε k * charT4 k z‖) =
        fun _ : T4 => ‖ρ.covarianceModeCoeff ε k‖ := by
      funext z
      rw [norm_mul, norm_charT4, mul_one]
    rw [hfun, integral_const, measureReal_def, paperMeasure_univ,
      ENNReal.toReal_ofReal hV0.le, smul_eq_mul]
  have hsummable :
      Summable fun k : Z4 =>
        ∫ z, ‖ρ.covarianceModeCoeff ε k * charT4 k z‖
          ∂paperMeasure := by
    refine ((ρ.summable_norm_covarianceModeCoeff hε).mul_left
      V).congr fun k => ?_
    rw [hnormint k]
  have hswap :=
    integral_tsum_of_summable_integral_norm hint hsummable
  have hseries :
      (∫ z : T4,
        ∑' k : Z4, ρ.covarianceModeCoeff ε k * charT4 k z
        ∂paperMeasure) =
      ((∫ z, ρ.etaEpsT4 ε z ∂paperMeasure : ℝ) : ℂ) := by
    rw [show
        (fun z : T4 =>
          ∑' k : Z4, ρ.covarianceModeCoeff ε k * charT4 k z) =
        fun z : T4 => ((ρ.etaEpsT4 ε z : ℝ) : ℂ) from
      funext fun z =>
        ρ.complexFourierCovarianceT4_eq_etaEpsT4 hε z]
    exact integral_ofReal
  have hRHS :
      (∑' k : Z4,
        ∫ z, ρ.covarianceModeCoeff ε k * charT4 k z
          ∂paperMeasure) =
      ρ.covarianceModeCoeff ε 0 * ((V : ℝ) : ℂ) := by
    have hterm : ∀ k : Z4,
        (∫ z, ρ.covarianceModeCoeff ε k * charT4 k z
          ∂paperMeasure) =
        ρ.covarianceModeCoeff ε k *
          (if k = 0 then ((V : ℝ) : ℂ) else 0) := by
      intro k
      rw [integral_const_mul, integral_charT4_paper]
    rw [tsum_congr hterm]
    exact tsum_eq_single 0 fun k hk => by
      rw [if_neg hk, mul_zero]
  have hmass :
      ((∫ z, ρ.etaEpsT4 ε z ∂paperMeasure : ℝ) : ℂ) =
      ((NoiseModel.whiteNoiseFourierScale ^ 2 *
        ‖ρ.symbol ε 0‖ ^ 2 * V : ℝ) : ℂ) := by
    rw [← hseries, ← hswap, hRHS]
    unfold SmoothCutoff.covarianceModeCoeff
    push_cast
    ring
  have hmassR :
      (∫ z, ρ.etaEpsT4 ε z ∂paperMeasure) =
      NoiseModel.whiteNoiseFourierScale ^ 2 *
        ‖ρ.symbol ε 0‖ ^ 2 * V :=
    Complex.ofReal_injective hmass
  rw [hmassR, ρ.symbol_zero ε]
  rw [show ‖(1 : ℂ)‖ ^ 2 = 1 by rw [norm_one]; norm_num, mul_one]
  rw [hVdef]
  exact whiteNoiseFourierScale_sq_mul_pow_dim

/-- Shifted unit mass: `∫ η_ε(c - w) dw = 1` for every center `c`. -/
theorem r324PermCross_integral_eta_sub_eq_one
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (c : T4) :
    ∫ w, ρ.etaEpsT4 ε (c - w) ∂paperMeasure = 1 := by
  have heven : ∀ w : T4, ρ.etaEpsT4 ε (c - w) =
      ρ.etaEpsT4 ε (w - c) := by
    intro w
    rw [show c - w = -(w - c) from (neg_sub w c).symm,
      (ρ.etaEpsT4_memE ε).neg_invariant]
  rw [show (fun w => ρ.etaEpsT4 ε (c - w)) =
      fun w => ρ.etaEpsT4 ε (w - c) from funext heven]
  have hshift :
      (∫ w, ρ.etaEpsT4 ε (w - c) ∂paperMeasure) =
        ∫ w, ρ.etaEpsT4 ε w ∂paperMeasure := by
    rw [paperMeasure_eq_volume]
    simpa only [sub_eq_add_neg] using
      integral_add_right_eq_self (fun x => ρ.etaEpsT4 ε x) (-c)
  rw [hshift]
  exact r324PermCross_integral_eta_eq_one ρ hε

/-! ## Bounded integrability on finite measures -/

theorem r324PermCross_integrable_of_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} {B : ℝ}
    (hmeas : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hB : ∀ x, f x ≤ B) :
    Integrable f μ := by
  refine (integrable_const B).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
  exact hB x

instance r324PermCross_instFiniteMeasurePi (n : ℕ) :
    IsFiniteMeasure (Measure.pi fun _ : Fin n => paperMeasure) := by
  infer_instance

instance r324PermCross_instFiniteMeasurePhysical (m : ℕ) :
    IsFiniteMeasure (r324PhysicalMeasure m) := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure
  infer_instance

/-! ## The pairing reindex of the internal coordinates -/

/-- The explicit left/right decomposition of the doubled carrier. -/
def r324PermCrossPairEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) where
  toFun := Sum.elim leftMomentIndex rightMomentIndex
  invFun := fun j =>
    if h : j.val < m then Sum.inl ⟨j.val, h⟩
    else Sum.inr ⟨j.val - m, by have := j.isLt; omega⟩
  left_inv := by
    rintro (i | i)
    · have h : (leftMomentIndex i).val < m := i.isLt
      simp only [Sum.elim_inl]
      rw [dif_pos h]
      congr 1
    · have h : ¬ (rightMomentIndex (m := m) i).val < m := by
        simp only [rightMomentIndex]
        omega
      simp only [Sum.elim_inr]
      rw [dif_neg h]
      congr 1
      apply Fin.ext
      simp [rightMomentIndex]
  right_inv := by
    intro j
    dsimp only
    by_cases h : j.val < m
    · rw [dif_pos h, Sum.elim_inl]
      apply Fin.ext
      rfl
    · rw [dif_neg h, Sum.elim_inr]
      apply Fin.ext
      simp only [rightMomentIndex]
      have := j.isLt
      omega

@[simp] theorem r324PermCrossPairEquiv_inl (m : ℕ) (i : Fin m) :
    r324PermCrossPairEquiv m (Sum.inl i) = leftMomentIndex i := rfl

@[simp] theorem r324PermCrossPairEquiv_inr (m : ℕ) (i : Fin m) :
    r324PermCrossPairEquiv m (Sum.inr i) = rightMomentIndex i := rfl

/-- The measurable split of the doubled internal coordinates into the
left and right halves. -/
def r324PermCrossSplitEquiv (m : ℕ) :
    ((Fin m → T4) × (Fin m → T4)) ≃ᵐ (Fin (2 * m) → T4) :=
  (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m => T4)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * m) => T4)
      (r324PermCrossPairEquiv m))

theorem r324PermCrossSplitEquiv_apply_left (m : ℕ)
    (a b : Fin m → T4) (i : Fin m) :
    r324PermCrossSplitEquiv m (a, b) (leftMomentIndex i) = a i := by
  have happ : r324PermCrossSplitEquiv m (a, b) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * m) => T4)
        (r324PermCrossPairEquiv m))
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Fin m ⊕ Fin m => T4)).symm (a, b)) := rfl
  rw [← r324PermCrossPairEquiv_inl, happ,
    MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

theorem r324PermCrossSplitEquiv_apply_right (m : ℕ)
    (a b : Fin m → T4) (i : Fin m) :
    r324PermCrossSplitEquiv m (a, b) (rightMomentIndex i) = b i := by
  have happ : r324PermCrossSplitEquiv m (a, b) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * m) => T4)
        (r324PermCrossPairEquiv m))
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Fin m ⊕ Fin m => T4)).symm (a, b)) := rfl
  rw [← r324PermCrossPairEquiv_inr, happ,
    MeasurableEquiv.piCongrLeft_apply_apply]
  rfl

/-- The split preserves the product Haar measure. -/
theorem r324PermCross_measurePreserving_splitEquiv (m : ℕ) :
    MeasurePreserving (r324PermCrossSplitEquiv m)
      ((Measure.pi fun _ : Fin m => paperMeasure).prod
        (Measure.pi fun _ : Fin m => paperMeasure))
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  have hsum :=
    (measurePreserving_sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m => paperMeasure)).symm
  have hcongr :=
    measurePreserving_piCongrLeft
      (fun _ : Fin (2 * m) => paperMeasure)
      (r324PermCrossPairEquiv m)
  have hfun : (r324PermCrossSplitEquiv m :
      ((Fin m → T4) × (Fin m → T4)) → (Fin (2 * m) → T4)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * m) => T4)
        (r324PermCrossPairEquiv m)) ∘
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin m ⊕ Fin m => T4)).symm := rfl
  refine ⟨(r324PermCrossSplitEquiv m).measurable, ?_⟩
  rw [hfun, ← Measure.map_map
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * m) => T4)
      (r324PermCrossPairEquiv m)).measurable
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m => T4)).symm.measurable,
    hsum.map_eq, hcongr.map_eq]

/-! ## One covariance mass per pure-cross entity -/

/-- The identity pairing leaves every index single. -/
theorem r324PermCross_id_singles (m : ℕ) :
    (PartialPairing.id : PartialPairing (Fin m)).singles =
      Finset.univ := by
  ext i
  simp [PartialPairing.id_apply]

/-- Cardinality of the single set of the identity pairing. -/
theorem r324PermCross_card_id_singles (m : ℕ) :
    Fintype.card
      ↥(PartialPairing.id : PartialPairing (Fin m)).singles = m := by
  rw [Fintype.card_coe, r324PermCross_id_singles, Finset.card_univ,
    Fintype.card_fin]

/-- **Exact covariance mass of one pure-cross entity**: the physical
`v`-integral of its cross-covariance product is one paper volume per
internal coordinate pair. -/
theorem r324PermCross_integral_crossProd_pi
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ)
    (π : ↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
      ↥(PartialPairing.id : PartialPairing (Fin m)).singles) :
    ∫ v, momentCrossCovarianceProduct ρ ε m
        PartialPairing.id PartialPairing.id π v
      ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) =
      ((2 * Real.pi) ^ (dim : ℕ)) ^ m := by
  classical
  set V : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hVdef
  have hV0 : 0 < V := by rw [hVdef]; positivity
  obtain ⟨Cη, hCη0, hCηb⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  set B : ℝ := ε⁻¹ ^ (dim : ℕ) * Cη with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  -- transported integrand on the split space
  set G : ((Fin m → T4) × (Fin m → T4)) → ℝ := fun q =>
    ∏ i : ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
      ρ.etaEpsT4 ε (q.1 i.val - q.2 (π i).val) with hGdef
  have hGmeas : Measurable G := by
    rw [hGdef]
    apply Finset.measurable_prod
    intro i _
    exact (ρ.measurable_etaEpsT4 ε).comp
      (((measurable_pi_apply _).comp measurable_fst).sub
        ((measurable_pi_apply _).comp measurable_snd))
  have hG0 : ∀ q, 0 ≤ G q := fun q =>
    Finset.prod_nonneg fun i _ => ρ.etaEpsT4_nonneg ε _
  have hGB : ∀ q, G q ≤
      B ^ (Finset.univ
        (α := ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles)).card := by
    intro q
    rw [hGdef, ← Finset.prod_const]
    refine Finset.prod_le_prod
      (fun i _ => ρ.etaEpsT4_nonneg ε _) fun i _ => ?_
    rw [hBdef]
    exact hCηb hε hε1 _
  have hGint : Integrable G
      ((Measure.pi fun _ : Fin m => paperMeasure).prod
        (Measure.pi fun _ : Fin m => paperMeasure)) :=
    r324PermCross_integrable_of_bounded hGmeas hG0 hGB
  -- step 1: transport along the measure-preserving split
  have htransport :
      (∫ v, momentCrossCovarianceProduct ρ ε m
          PartialPairing.id PartialPairing.id π v
        ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure)) =
      ∫ q, G q
        ∂((Measure.pi fun _ : Fin m => paperMeasure).prod
          (Measure.pi fun _ : Fin m => paperMeasure)) := by
    rw [← (r324PermCross_measurePreserving_splitEquiv m).integral_comp
      (r324PermCrossSplitEquiv m).measurableEmbedding
      (fun v => momentCrossCovarianceProduct ρ ε m
        PartialPairing.id PartialPairing.id π v)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    obtain ⟨a, b⟩ := q
    unfold momentCrossCovarianceProduct
    rw [hGdef]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [r324PermCrossSplitEquiv_apply_left,
      r324PermCrossSplitEquiv_apply_right]
  -- step 2: Fubini and the per-pair unit masses
  have hinner : ∀ a : Fin m → T4,
      (∫ b, G (a, b)
        ∂(Measure.pi fun _ : Fin m => paperMeasure)) = 1 := by
    intro a
    set τ : ↥(PartialPairing.id : PartialPairing (Fin m)).singles →
        Fin m := fun i => (π i).val with hτdef
    have hτinj : Function.Injective τ := by
      intro i j hij
      exact π.injective (Subtype.val_injective hij)
    have hτbij : Function.Bijective τ := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨hτinj, ?_⟩
      rw [r324PermCross_card_id_singles, Fintype.card_fin]
    set τe : ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles ≃ Fin m :=
      Equiv.ofBijective τ hτbij with hτedef
    have hMP := measurePreserving_piCongrLeft
      (fun _ : Fin m => paperMeasure) τe
    rw [← hMP.integral_comp
      (MeasurableEquiv.piCongrLeft (fun _ : Fin m => T4)
        τe).measurableEmbedding
      (fun b => G (a, b))]
    have hpoint : ∀ c : ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles → T4,
        G (a, (MeasurableEquiv.piCongrLeft
          (fun _ : Fin m => T4) τe) c) =
          ∏ i : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles,
            ρ.etaEpsT4 ε (a i.val - c i) := by
      intro c
      rw [hGdef]
      dsimp only
      refine Finset.prod_congr rfl fun i _ => ?_
      have hτi : ((π i).val : Fin m) = τe i := rfl
      rw [hτi, MeasurableEquiv.piCongrLeft_apply_apply]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_fintype_prod_eq_prod
      (f := fun (i : ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles) (w : T4) =>
        ρ.etaEpsT4 ε (a i.val - w))]
    refine Finset.prod_eq_one fun i _ => ?_
    exact r324PermCross_integral_eta_sub_eq_one ρ hε _
  rw [htransport, integral_prod _ hGint]
  rw [integral_congr_ae
    (Filter.Eventually.of_forall fun a => by rw [hinner a])]
  rw [integral_const, measureReal_def, Measure.pi_univ]
  simp only [paperMeasure_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_pow hV0.le, ENNReal.toReal_ofReal
    (by positivity)]

/-! ## Peeling the four external variables -/

/-- Pushforward of the physical measure onto the internal
coordinates: four paper volumes times the internal product measure. -/
theorem r324PermCross_map_internal (m : ℕ) :
    (r324PhysicalMeasure m).map
        (fun p : R324PhysicalPoint m => p.2.2.2.2) =
      (paperMeasure Set.univ ^ 4) •
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure
  rw [show (fun p : R324PhysicalPoint m => p.2.2.2.2) =
      (fun v : Fin (2 * m) → T4 => v) ∘ Prod.snd ∘ Prod.snd ∘
        Prod.snd ∘ Prod.snd from rfl]
  rw [← Function.comp_assoc, ← Function.comp_assoc,
    ← Function.comp_assoc]
  rw [← Measure.map_map (by fun_prop) measurable_snd]
  rw [Measure.map_snd_prod]
  rw [Measure.map_smul]
  rw [← Measure.map_map (by fun_prop) measurable_snd]
  rw [Measure.map_snd_prod]
  rw [Measure.map_smul]
  rw [← Measure.map_map (by fun_prop) measurable_snd]
  rw [Measure.map_snd_prod]
  rw [Measure.map_smul]
  rw [show ((fun v : Fin (2 * m) → T4 => v) ∘ Prod.snd) =
      (Prod.snd : T4 × (Fin (2 * m) → T4) → (Fin (2 * m) → T4))
      from rfl]
  rw [Measure.map_snd_prod]
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  ring

/-- Integrals of internal-coordinate observables against the physical
measure carry four paper volumes. -/
theorem r324PermCross_integral_internal (m : ℕ)
    {F : (Fin (2 * m) → T4) → ℝ} (hF : Measurable F) :
    ∫ p, F p.2.2.2.2 ∂(r324PhysicalMeasure m) =
      ((2 * Real.pi) ^ (dim : ℕ)) ^ 4 *
        ∫ v, F v ∂(Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
  have hproj : Measurable
      (fun p : R324PhysicalPoint m => p.2.2.2.2) :=
    measurable_snd.snd.snd.snd
  rw [← integral_map hproj.aemeasurable hF.aestronglyMeasurable,
    r324PermCross_map_internal, integral_smul_measure]
  rw [paperMeasure_univ, ← ENNReal.ofReal_pow (by positivity),
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

/-- **Physical covariance mass of one pure-cross entity.** -/
theorem r324PermCross_integral_crossProd_physical
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ)
    (π : ↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
      ↥(PartialPairing.id : PartialPairing (Fin m)).singles) :
    ∫ p, momentCrossCovarianceProduct ρ ε m
        PartialPairing.id PartialPairing.id π p.2.2.2.2
      ∂(r324PhysicalMeasure m) =
      ((2 * Real.pi) ^ (dim : ℕ)) ^ (m + 4) := by
  have hFmeas : Measurable (fun v : Fin (2 * m) → T4 =>
      momentCrossCovarianceProduct ρ ε m
        PartialPairing.id PartialPairing.id π v) := by
    unfold momentCrossCovarianceProduct
    apply Finset.measurable_prod
    intro i _
    exact (ρ.measurable_etaEpsT4 ε).comp
      ((measurable_pi_apply _).sub (measurable_pi_apply _))
  rw [r324PermCross_integral_internal m hFmeas,
    r324PermCross_integral_crossProd_pi ρ hε hε1 m π,
    ← pow_add]
  congr 1
  ring

/-! ## Null diagonals on the physical space -/

theorem r324PermCross_measurableSet_ne {A : Type*} [MeasurableSpace A]
    {f g : A → T4} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {a | f a ≠ g a} :=
  (measurableSet_eq_fun hf hg).compl

theorem r324PermCross_ae_snd {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] {μ : Measure A} {ν : Measure B} [SFinite ν]
    {P : B → Prop} (hP : MeasurableSet {b | P b})
    (h : ∀ᵐ b ∂ν, P b) :
    ∀ᵐ p : A × B ∂(μ.prod ν), P p.2 := by
  have hset : MeasurableSet {p : A × B | P p.2} := measurable_snd hP
  rw [Measure.ae_prod_iff_ae_ae hset]
  exact Filter.Eventually.of_forall fun a => h

/-- The external `x` avoids every internal coordinate a.s. -/
theorem r324PermCross_ae_ne_x (m : ℕ) (j : Fin (2 * m)) :
    ∀ᵐ p : R324PhysicalPoint m ∂(r324PhysicalMeasure m),
      p.1 ≠ p.2.2.2.2 j := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure
  rw [Measure.ae_prod_iff_ae_ae
    (r324PermCross_measurableSet_ne measurable_fst
      ((measurable_pi_apply j).comp measurable_snd.snd.snd.snd))]
  refine Filter.Eventually.of_forall fun x => ?_
  refine r324PermCross_ae_snd
    (P := fun r : T4 × (T4 × (Fin (2 * m) → T4)) => x ≠ r.2.2 j)
    (r324PermCross_measurableSet_ne measurable_const
      ((measurable_pi_apply j).comp measurable_snd.snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun s : T4 × (Fin (2 * m) → T4) => x ≠ s.2 j)
    (r324PermCross_measurableSet_ne measurable_const
      ((measurable_pi_apply j).comp measurable_snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun v : Fin (2 * m) → T4 => x ≠ v j)
    (r324PermCross_measurableSet_ne measurable_const
      (measurable_pi_apply j)) ?_
  exact (ae_pi_eval_ne_const j x).mono fun v hv => hv.symm

/-- The external `y` avoids every internal coordinate a.s. -/
theorem r324PermCross_ae_ne_y (m : ℕ) (j : Fin (2 * m)) :
    ∀ᵐ p : R324PhysicalPoint m ∂(r324PhysicalMeasure m),
      p.2.1 ≠ p.2.2.2.2 j := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure
  refine r324PermCross_ae_snd
    (P := fun q : R324PhysicalRest m => q.1 ≠ q.2.2.2 j)
    (r324PermCross_measurableSet_ne measurable_fst
      ((measurable_pi_apply j).comp measurable_snd.snd.snd)) ?_
  rw [Measure.ae_prod_iff_ae_ae
    (r324PermCross_measurableSet_ne measurable_fst
      ((measurable_pi_apply j).comp measurable_snd.snd.snd))]
  refine Filter.Eventually.of_forall fun y => ?_
  refine r324PermCross_ae_snd
    (P := fun s : T4 × (Fin (2 * m) → T4) => y ≠ s.2 j)
    (r324PermCross_measurableSet_ne measurable_const
      ((measurable_pi_apply j).comp measurable_snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun v : Fin (2 * m) → T4 => y ≠ v j)
    (r324PermCross_measurableSet_ne measurable_const
      (measurable_pi_apply j)) ?_
  exact (ae_pi_eval_ne_const j y).mono fun v hv => hv.symm

/-- The external `z` avoids every internal coordinate a.s. -/
theorem r324PermCross_ae_ne_z (m : ℕ) (j : Fin (2 * m)) :
    ∀ᵐ p : R324PhysicalPoint m ∂(r324PhysicalMeasure m),
      p.2.2.1 ≠ p.2.2.2.2 j := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure
  refine r324PermCross_ae_snd
    (P := fun q : R324PhysicalRest m => q.2.1 ≠ q.2.2.2 j)
    (r324PermCross_measurableSet_ne (measurable_fst.comp measurable_snd)
      ((measurable_pi_apply j).comp measurable_snd.snd.snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun r : T4 × (T4 × (Fin (2 * m) → T4)) => r.1 ≠ r.2.2 j)
    (r324PermCross_measurableSet_ne measurable_fst
      ((measurable_pi_apply j).comp measurable_snd.snd)) ?_
  rw [Measure.ae_prod_iff_ae_ae
    (r324PermCross_measurableSet_ne measurable_fst
      ((measurable_pi_apply j).comp measurable_snd.snd))]
  refine Filter.Eventually.of_forall fun z => ?_
  refine r324PermCross_ae_snd
    (P := fun v : Fin (2 * m) → T4 => z ≠ v j)
    (r324PermCross_measurableSet_ne measurable_const
      (measurable_pi_apply j)) ?_
  exact (ae_pi_eval_ne_const j z).mono fun v hv => hv.symm

/-- The external `w` avoids every internal coordinate a.s. -/
theorem r324PermCross_ae_ne_w (m : ℕ) (j : Fin (2 * m)) :
    ∀ᵐ p : R324PhysicalPoint m ∂(r324PhysicalMeasure m),
      p.2.2.2.1 ≠ p.2.2.2.2 j := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure
  refine r324PermCross_ae_snd
    (P := fun q : R324PhysicalRest m => q.2.2.1 ≠ q.2.2.2 j)
    (r324PermCross_measurableSet_ne
      (measurable_fst.comp measurable_snd.snd)
      ((measurable_pi_apply j).comp measurable_snd.snd.snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun r : T4 × (T4 × (Fin (2 * m) → T4)) =>
      r.2.1 ≠ r.2.2 j)
    (r324PermCross_measurableSet_ne
      (measurable_fst.comp measurable_snd)
      ((measurable_pi_apply j).comp measurable_snd.snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun s : T4 × (Fin (2 * m) → T4) => s.1 ≠ s.2 j)
    (r324PermCross_measurableSet_ne measurable_fst
      ((measurable_pi_apply j).comp measurable_snd)) ?_
  rw [Measure.ae_prod_iff_ae_ae
    (r324PermCross_measurableSet_ne measurable_fst
      ((measurable_pi_apply j).comp measurable_snd))]
  refine Filter.Eventually.of_forall fun w => ?_
  exact (ae_pi_eval_ne_const j w).mono fun v hv => hv.symm

/-- Distinct internal coordinates are a.s. distinct. -/
theorem r324PermCross_ae_ne_vv (m : ℕ) {j j' : Fin (2 * m)}
    (hjj : j ≠ j') :
    ∀ᵐ p : R324PhysicalPoint m ∂(r324PhysicalMeasure m),
      p.2.2.2.2 j ≠ p.2.2.2.2 j' := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure
  refine r324PermCross_ae_snd
    (P := fun q : R324PhysicalRest m => q.2.2.2 j ≠ q.2.2.2 j')
    (r324PermCross_measurableSet_ne
      ((measurable_pi_apply j).comp measurable_snd.snd.snd)
      ((measurable_pi_apply j').comp measurable_snd.snd.snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun r : T4 × (T4 × (Fin (2 * m) → T4)) =>
      r.2.2 j ≠ r.2.2 j')
    (r324PermCross_measurableSet_ne
      ((measurable_pi_apply j).comp measurable_snd.snd)
      ((measurable_pi_apply j').comp measurable_snd.snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun s : T4 × (Fin (2 * m) → T4) => s.2 j ≠ s.2 j')
    (r324PermCross_measurableSet_ne
      ((measurable_pi_apply j).comp measurable_snd)
      ((measurable_pi_apply j').comp measurable_snd)) ?_
  refine r324PermCross_ae_snd
    (P := fun v : Fin (2 * m) → T4 => v j ≠ v j')
    (r324PermCross_measurableSet_ne (measurable_pi_apply j)
      (measurable_pi_apply j')) ?_
  exact ae_pi_eval_ne_eval_of_pos (Fin.pos j) j j' hjj

/-! ## The almost-everywhere chain floor -/

/-- Interior slots of the assembled tuple. -/
theorem r324PermCross_assemble_mid {m : ℕ} (x y : T4)
    (w : Fin m → T4) (j : Fin (m + 2))
    (h0 : j.val ≠ 0) (h1 : j.val ≠ m + 1) :
    assemble x y w j =
      w ⟨j.val - 1, by have := j.isLt; omega⟩ := by
  unfold assemble
  rw [dif_neg h0, dif_neg h1]

/-- Almost every physical point has all edges of an assembled chain off
the diagonal.  Stated for either half through the index embedding
`emb` (left or right copy) and external slots `X`, `Y`. -/
theorem r324PermCross_ae_assembled_edges (m : ℕ) (hm : 1 ≤ m)
    (emb : Fin m → Fin (2 * m)) (hemb : Function.Injective emb)
    (X Y : R324PhysicalPoint m → T4)
    (hX : ∀ j : Fin (2 * m), ∀ᵐ p ∂(r324PhysicalMeasure m),
      X p ≠ p.2.2.2.2 j)
    (hY : ∀ j : Fin (2 * m), ∀ᵐ p ∂(r324PhysicalMeasure m),
      Y p ≠ p.2.2.2.2 j) :
    ∀ᵐ p : R324PhysicalPoint m ∂(r324PhysicalMeasure m),
      ∀ e : Fin (m + 1),
        (assemble (X p) (Y p) fun i => p.2.2.2.2 (emb i))
            e.castSucc ≠
          (assemble (X p) (Y p) fun i => p.2.2.2.2 (emb i))
            e.succ := by
  rw [ae_all_iff]
  intro e
  by_cases he0 : e.val = 0
  · -- first edge: `X` against the first internal slot
    have hcast : (e.castSucc : Fin (m + 2)) = 0 := by
      apply Fin.ext
      simpa using he0
    have hsuccne0 : (e.succ : Fin (m + 2)).val ≠ 0 := by
      simp [Fin.val_succ]
    have hsuccne1 : (e.succ : Fin (m + 2)).val ≠ m + 1 := by
      simp only [Fin.val_succ, he0]
      omega
    filter_upwards [hX (emb ⟨0, by omega⟩)] with p hp
    rw [hcast, assemble_zero,
      r324PermCross_assemble_mid _ _ _ _ hsuccne0 hsuccne1]
    have hidx : (⟨(e.succ : Fin (m + 2)).val - 1, by
        have := (e.succ : Fin (m + 2)).isLt; omega⟩ : Fin m) =
        ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [Fin.val_succ, he0]
    rw [hidx]
    exact hp
  · by_cases hem : e.val = m
    · -- last edge: the last internal slot against `Y`
      have hsucc : (e.succ : Fin (m + 2)) = Fin.last (m + 1) := by
        apply Fin.ext
        simp [Fin.val_succ, hem]
      have hcastne0 : (e.castSucc : Fin (m + 2)).val ≠ 0 := by
        simpa using he0
      have hcastne1 : (e.castSucc : Fin (m + 2)).val ≠ m + 1 := by
        have := e.isLt
        simpa using by omega
      filter_upwards [hY (emb ⟨e.val - 1, by omega⟩)] with p hp
      rw [hsucc, assemble_last,
        r324PermCross_assemble_mid _ _ _ _ hcastne0 hcastne1]
      have hidx : (⟨(e.castSucc : Fin (m + 2)).val - 1, by
          have := (e.castSucc : Fin (m + 2)).isLt; omega⟩ : Fin m) =
          ⟨e.val - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hidx]
      exact fun h => hp h.symm
    · -- interior edge: two distinct internal slots
      have h0lt : 0 < e.val := Nat.pos_of_ne_zero he0
      have hltm : e.val < m := lt_of_le_of_ne
        (Nat.lt_succ_iff.mp e.isLt) hem
      have hcastne0 : (e.castSucc : Fin (m + 2)).val ≠ 0 := by
        simpa using he0
      have hcastne1 : (e.castSucc : Fin (m + 2)).val ≠ m + 1 := by
        simpa using by omega
      have hsuccne0 : (e.succ : Fin (m + 2)).val ≠ 0 := by
        simp [Fin.val_succ]
      have hsuccne1 : (e.succ : Fin (m + 2)).val ≠ m + 1 := by
        simp only [Fin.val_succ]
        omega
      have hne : emb ⟨e.val - 1, by omega⟩ ≠ emb ⟨e.val, hltm⟩ := by
        intro h
        have := hemb h
        have hval := congrArg Fin.val this
        simp only at hval
        omega
      filter_upwards [r324PermCross_ae_ne_vv m hne] with p hp
      rw [r324PermCross_assemble_mid _ _ _ _ hcastne0 hcastne1,
        r324PermCross_assemble_mid _ _ _ _ hsuccne0 hsuccne1]
      have hidx1 : (⟨(e.castSucc : Fin (m + 2)).val - 1, by
          have := (e.castSucc : Fin (m + 2)).isLt; omega⟩ : Fin m) =
          ⟨e.val - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      have hidx2 : (⟨(e.succ : Fin (m + 2)).val - 1, by
          have := (e.succ : Fin (m + 2)).isLt; omega⟩ : Fin m) =
          ⟨e.val, hltm⟩ := by
        apply Fin.ext
        simp [Fin.val_succ]
      rw [hidx1, hidx2]
      exact hp

theorem r324PermCross_leftMomentIndex_injective (m : ℕ) :
    Function.Injective (leftMomentIndex (m := m)) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [leftMomentIndex] at this
  exact Fin.ext this

theorem r324PermCross_rightMomentIndex_injective (m : ℕ) :
    Function.Injective (rightMomentIndex (m := m)) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [rightMomentIndex] at this
  apply Fin.ext
  omega

/-- Almost everywhere both plain chains sit above the Green floor. -/
theorem r324PermCross_ae_chains_floor (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ p : R324PhysicalPoint m ∂(r324PhysicalMeasure m),
      r324PermCrossGreenFloorConst ^ (2 * m + 2) ≤
        r324LedgerThreeLeftChain m p *
          r324LedgerThreeRightChain m p := by
  have hL := r324PermCross_ae_assembled_edges m hm
    (leftMomentIndex (m := m))
    (r324PermCross_leftMomentIndex_injective m)
    (fun p => p.1) (fun p => p.2.1)
    (r324PermCross_ae_ne_x m) (r324PermCross_ae_ne_y m)
  have hR := r324PermCross_ae_assembled_edges m hm
    (rightMomentIndex (m := m))
    (r324PermCross_rightMomentIndex_injective m)
    (fun p => p.2.2.1) (fun p => p.2.2.2.1)
    (r324PermCross_ae_ne_z m) (r324PermCross_ae_ne_w m)
  filter_upwards [hL, hR] with p hpL hpR
  have hg0 := r324PermCrossGreenFloorConst_pos
  have hLfloor : r324PermCrossGreenFloorConst ^ (m + 1) ≤
      r324LedgerThreeLeftChain m p := by
    unfold r324LedgerThreeLeftChain
    calc r324PermCrossGreenFloorConst ^ (m + 1) =
        ∏ _e : Fin (m + 1), r324PermCrossGreenFloorConst := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := by
          refine Finset.prod_le_prod (fun _ _ => hg0.le)
            fun e _ => ?_
          exact r324PermCross_greenFn_floor
            (sub_ne_zero.mpr (hpL e))
  have hRfloor : r324PermCrossGreenFloorConst ^ (m + 1) ≤
      r324LedgerThreeRightChain m p := by
    unfold r324LedgerThreeRightChain
    calc r324PermCrossGreenFloorConst ^ (m + 1) =
        ∏ _e : Fin (m + 1), r324PermCrossGreenFloorConst := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := by
          refine Finset.prod_le_prod (fun _ _ => hg0.le)
            fun e _ => ?_
          exact r324PermCross_greenFn_floor
            (sub_ne_zero.mpr (hpR e))
  calc r324PermCrossGreenFloorConst ^ (2 * m + 2) =
      r324PermCrossGreenFloorConst ^ (m + 1) *
        r324PermCrossGreenFloorConst ^ (m + 1) := by
        rw [← pow_add]
        congr 1
        ring
    _ ≤ r324LedgerThreeLeftChain m p *
        r324LedgerThreeRightChain m p :=
        mul_le_mul hLfloor hRfloor (by positivity)
          (r324LedgerThreeLeftChain_nonneg m p)

/-! ## Integrability of the fibre summands -/

/-- One pure-cross summand of the density is integrable: it is the real
part of the proved integrable flat contraction term at trivial
external modes. -/
theorem r324PermCross_integrable_summand
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ}
    (π : ↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
      ↥(PartialPairing.id : PartialPairing (Fin m)).singles) :
    Integrable (fun p : R324PhysicalPoint m =>
        r324LedgerThreeLeftChain m p *
          r324LedgerThreeRightChain m p *
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2)
      (r324PhysicalMeasure m) := by
  have hint : Integrable
      (r324Flatten (deterministicMomentIntegrand ρ ε m 0 0
        PartialPairing.id PartialPairing.id π))
      (r324PhysicalMeasure m) :=
    r324MomentIntegrable_all ρ hε hε1 0 0
      ⟨PartialPairing.id, PartialPairing.id, π⟩
  refine hint.re.congr
    (Filter.Eventually.of_forall fun p => ?_)
  have heq := r324LedgerThree_flatten_allCross_eq ρ ε (m := m) 0 0
    (e := ⟨PartialPairing.id, PartialPairing.id, π⟩) ⟨rfl, rfl⟩ p
  dsimp only at heq ⊢
  rw [heq]
  simp [charT4_zero, RCLike.re_to_complex]

/-- One cross-covariance product is integrable on the physical space. -/
theorem r324PermCross_integrable_crossProd_physical
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {m : ℕ}
    (π : ↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
      ↥(PartialPairing.id : PartialPairing (Fin m)).singles) :
    Integrable (fun p : R324PhysicalPoint m =>
        momentCrossCovarianceProduct ρ ε m
          PartialPairing.id PartialPairing.id π p.2.2.2.2)
      (r324PhysicalMeasure m) := by
  classical
  obtain ⟨Cη, hCη0, hCηb⟩ := ρ.exists_pos_etaEpsT4_uniform_bound
  refine r324PermCross_integrable_of_bounded
    (B := (ε⁻¹ ^ (dim : ℕ) * Cη) ^
      (Finset.univ (α := ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles)).card) ?_ ?_ ?_
  · unfold momentCrossCovarianceProduct
    apply Finset.measurable_prod
    intro i _
    exact (ρ.measurable_etaEpsT4 ε).comp
      (((measurable_pi_apply _).comp
          measurable_snd.snd.snd.snd).sub
        ((measurable_pi_apply _).comp
          measurable_snd.snd.snd.snd))
  · intro p
    exact Finset.prod_nonneg fun i _ => ρ.etaEpsT4_nonneg ε _
  · intro p
    unfold momentCrossCovarianceProduct
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod
      (fun i _ => ρ.etaEpsT4_nonneg ε _)
      (fun i _ => hCηb hε hε1 _)

/-! ## The factorial minorant -/

/-- Number of pure-cross permutation entities. -/
theorem r324PermCross_card_equiv (m : ℕ) :
    Fintype.card
      (↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles) =
      m.factorial := by
  rw [Fintype.card_equiv (Equiv.refl _),
    r324PermCross_card_id_singles]

/-- **The factorial minorant of the summed pure-cross fibre**: the
physical integral of the full permutation-fibre density is at least
`g₀^{2m+2} · m! · (2π)^{4(m+4)}`. -/
theorem r324PermCross_integral_crossDensity_ge
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    r324PermCrossGreenFloorConst ^ (2 * m + 2) *
        ((m.factorial : ℝ) *
          ((2 * Real.pi) ^ (dim : ℕ)) ^ (m + 4)) ≤
      ∫ p, r324LedgerThreeCrossDensity ρ ε m
          (r324LedgerThreePermEntities m) p
        ∂(r324PhysicalMeasure m) := by
  classical
  set g0 : ℝ := r324PermCrossGreenFloorConst with hg0def
  have hg0 := r324PermCrossGreenFloorConst_pos
  set V : ℝ := (2 * Real.pi) ^ (dim : ℕ) with hVdef
  -- the density is the sum of the permutation summands
  have hdens : ∀ p : R324PhysicalPoint m,
      r324LedgerThreeCrossDensity ρ ε m
        (r324LedgerThreePermEntities m) p =
      ∑ π : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
        r324LedgerThreeLeftChain m p *
          r324LedgerThreeRightChain m p *
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2 := by
    intro p
    unfold r324LedgerThreeCrossDensity
    rw [r324LedgerThree_sum_permEntities_cross, Finset.mul_sum]
  have hsumInt : Integrable (fun p : R324PhysicalPoint m =>
      ∑ π : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
        r324LedgerThreeLeftChain m p *
          r324LedgerThreeRightChain m p *
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2)
      (r324PhysicalMeasure m) :=
    integrable_finsetSum _ fun π _ =>
      r324PermCross_integrable_summand ρ hε hε1 π
  have hminInt : Integrable (fun p : R324PhysicalPoint m =>
      g0 ^ (2 * m + 2) *
        ∑ π : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles ≃
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2)
      (r324PhysicalMeasure m) :=
    (integrable_finsetSum _ fun π _ =>
      r324PermCross_integrable_crossProd_physical ρ hε hε1 π).const_mul _
  have hae : (fun p : R324PhysicalPoint m =>
      g0 ^ (2 * m + 2) *
        ∑ π : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles ≃
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2) ≤ᵐ[
      r324PhysicalMeasure m]
      fun p =>
        ∑ π : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles ≃
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
          r324LedgerThreeLeftChain m p *
            r324LedgerThreeRightChain m p *
            momentCrossCovarianceProduct ρ ε m
              PartialPairing.id PartialPairing.id π p.2.2.2.2 := by
    filter_upwards [r324PermCross_ae_chains_floor m hm] with p hp
    have hsum0 : (0 : ℝ) ≤
        ∑ π : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles ≃
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2 :=
      Finset.sum_nonneg fun π _ =>
        Finset.prod_nonneg fun i _ => ρ.etaEpsT4_nonneg ε _
    calc g0 ^ (2 * m + 2) * ∑ π, momentCrossCovarianceProduct ρ ε m
          PartialPairing.id PartialPairing.id π p.2.2.2.2 ≤
        (r324LedgerThreeLeftChain m p *
          r324LedgerThreeRightChain m p) *
          ∑ π, momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2 :=
        mul_le_mul_of_nonneg_right hp hsum0
      _ = ∑ π, r324LedgerThreeLeftChain m p *
          r324LedgerThreeRightChain m p *
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2 := by
        rw [Finset.mul_sum]
  have hlow : g0 ^ (2 * m + 2) *
      ((m.factorial : ℝ) * V ^ (m + 4)) =
      ∫ p, (g0 ^ (2 * m + 2) *
        ∑ π : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles ≃
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2)
        ∂(r324PhysicalMeasure m) := by
    rw [integral_const_mul, integral_finsetSum _
      (fun π _ => r324PermCross_integrable_crossProd_physical
        ρ hε hε1 π)]
    congr 1
    have hval : ∀ π : ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
        (∫ p, momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2
          ∂(r324PhysicalMeasure m)) = V ^ (m + 4) := fun π =>
      r324PermCross_integral_crossProd_physical ρ hε hε1 m π
    rw [Finset.sum_congr rfl fun π _ => hval π,
      Finset.sum_const, Finset.card_univ,
      r324PermCross_card_equiv, nsmul_eq_mul]
  calc g0 ^ (2 * m + 2) * ((m.factorial : ℝ) * V ^ (m + 4)) =
      ∫ p, (g0 ^ (2 * m + 2) *
        ∑ π : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles ≃
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
          momentCrossCovarianceProduct ρ ε m
            PartialPairing.id PartialPairing.id π p.2.2.2.2)
        ∂(r324PhysicalMeasure m) := hlow
    _ ≤ ∫ p, (∑ π : ↥(PartialPairing.id :
            PartialPairing (Fin m)).singles ≃
          ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
          r324LedgerThreeLeftChain m p *
            r324LedgerThreeRightChain m p *
            momentCrossCovarianceProduct ρ ε m
              PartialPairing.id PartialPairing.id π p.2.2.2.2)
        ∂(r324PhysicalMeasure m) :=
        integral_mono_ae hminInt hsumInt hae
    _ = ∫ p, r324LedgerThreeCrossDensity ρ ε m
          (r324LedgerThreePermEntities m) p
        ∂(r324PhysicalMeasure m) := by
        refine integral_congr_ae
          (Filter.Eventually.of_forall fun p => ?_)
        rw [hdens p]

end

end Anderson4D
