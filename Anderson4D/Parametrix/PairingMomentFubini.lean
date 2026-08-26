import Anderson4D.Parametrix.WickSpatialUniform
import Anderson4D.Parametrix.Identity
import Anderson4D.Parametrix.PairingMeasurability

/-!
# Noise--space Fubini for one doubled parametrix pairing

This file realizes the analytic Fubini output used in paper (3.24).  The
six physical variable groups are represented as four external points and
one doubled internal tuple.  The two copies are joined by the
measure-preserving `Fin m + Fin m = Fin (2m)` reindexing.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Anderson4D

noncomputable section

open MeasureTheory ComplexConjugate

/-- Complex spatial integrand of one within-copy pairing, without its
coupling factor. -/
def pairingHalfIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω)
    (x y : T4) (v : Fin m → T4) : ℂ :=
  charT4 α x * charT4 β y *
    (randIntegrand M ρ ε κ (assemble x y v) ω : ℂ)

/-- Frozen iterated physical integral of one pairing before multiplication
by `λ_ε^m`. -/
def pairingHalfIntegral
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω) : ℂ :=
  ∫ x, ∫ y, ∫ v : Fin m → T4,
    pairingHalfIntegrand M ρ ε m α β κ ω x y v
    ∂(Measure.pi fun _ => paperMeasure)
    ∂paperMeasure ∂paperMeasure

/-- One pairing coefficient is its unscaled physical integral times the
common coupling power. -/
theorem pmPairingCoeff_eq_lam_pow_mul_pairingHalfIntegral
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω) :
    pmPairingCoeff M ρ lam ε m α β κ ω =
      (lamEps lam ε ^ m : ℂ) *
        pairingHalfIntegral M ρ ε m α β κ ω := by
  unfold pmPairingCoeff pairingHalfIntegral pairingHalfIntegrand randRI
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [integral_const_mul]
  rw [integral_complex_ofReal]
  push_cast
  ring

/-- Negating both Fourier modes conjugates an individual pairing
coefficient. -/
theorem conj_pmPairingCoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) (ω : M.Ω) :
    conj (pmPairingCoeff M ρ lam ε m α β κ ω) =
      pmPairingCoeff M ρ lam ε m (-α) (-β) κ ω := by
  unfold pmPairingCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  simp only [map_mul, Complex.conj_ofReal, conj_charT4]

/-! ## The doubled finite tuple -/

/-- Split the doubled internal tuple into its left and right copies. -/
def momentDoublePiMeasurableEquiv
    (m : ℕ) (X : Type*) [MeasurableSpace X] :
    (Fin (2 * m) → X) ≃ᵐ
      (Fin m → X) × (Fin m → X) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (2 * m) => X)
      (momentDoubleFinEquiv m)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m => X))

@[simp]
theorem momentDoublePiMeasurableEquiv_apply
    (m : ℕ) (X : Type*) [MeasurableSpace X]
    (v : Fin (2 * m) → X) :
    momentDoublePiMeasurableEquiv m X v =
      (fun i => v (leftMomentIndex i),
        fun j => v (rightMomentIndex j)) := by
  apply Prod.ext
  · funext i
    rfl
  · funext j
    rfl

/-- The doubled-tuple split preserves the corresponding product Haar
measure. -/
theorem measurePreserving_momentDoublePi
    (m : ℕ) :
    MeasurePreserving
      (momentDoublePiMeasurableEquiv m T4)
      (Measure.pi fun _ : Fin (2 * m) => paperMeasure)
      ((Measure.pi fun _ : Fin m => paperMeasure).prod
        (Measure.pi fun _ : Fin m => paperMeasure)) := by
  let hcongr :=
    (measurePreserving_piCongrLeft
      (fun _ : Fin (2 * m) => paperMeasure)
      (momentDoubleFinEquiv m)).symm
  let hsum :=
    measurePreserving_sumPiEquivProdPi
      (fun _ : Fin m ⊕ Fin m => paperMeasure)
  exact hsum.comp hcongr

/-- A complex separated integrand factors after the concrete doubled-tuple
split. -/
theorem integral_momentDouble_mul
    (m : ℕ) (f g : (Fin m → T4) → ℂ) :
    (∫ v : Fin (2 * m) → T4,
        f (fun i => v (leftMomentIndex i)) *
          g (fun j => v (rightMomentIndex j))
        ∂(Measure.pi fun _ => paperMeasure)) =
      (∫ u : Fin m → T4, f u
          ∂(Measure.pi fun _ => paperMeasure)) *
        ∫ t : Fin m → T4, g t
          ∂(Measure.pi fun _ => paperMeasure) := by
  let e := momentDoublePiMeasurableEquiv m T4
  let μ := Measure.pi fun _ : Fin (2 * m) => paperMeasure
  let μm := Measure.pi fun _ : Fin m => paperMeasure
  have hp : MeasurePreserving e μ (μm.prod μm) :=
    measurePreserving_momentDoublePi m
  calc
    _ = ∫ p : (Fin m → T4) × (Fin m → T4),
        f p.1 * g p.2 ∂(μm.prod μm) := by
      simpa only [Function.comp_apply, e,
        momentDoublePiMeasurableEquiv_apply, μ, μm] using
        hp.integral_comp' (fun p => f p.1 * g p.2)
    _ = _ := integral_prod_mul f g

/-- The unscaled doubled physical integrand at one noise sample. -/
def pairingMomentRaw
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4)
    (κp κm : PartialPairing (Fin m)) (ω : M.Ω)
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  pairingHalfIntegrand M ρ ε m α β κp ω x y
      (fun i => v (leftMomentIndex i)) *
    pairingHalfIntegrand M ρ ε m (-α) (-β) κm ω z w
      (fun i => v (rightMomentIndex i))

/-- Frozen five-fold physical integral of the doubled raw integrand. -/
def pairingMomentRawSpatialIntegral
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4)
    (κp κm : PartialPairing (Fin m)) (ω : M.Ω) : ℂ :=
  ∫ x, ∫ y, ∫ z, ∫ w,
    ∫ v : Fin (2 * m) → T4,
      pairingMomentRaw M ρ ε m α β κp κm ω x y z w v
      ∂(Measure.pi fun _ => paperMeasure)
    ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure

/-- The doubled physical integral factors into the two copy integrals.
This identity is valid for totalized integrals and needs no sectionwise
integrability premise. -/
theorem pairingMomentRawSpatialIntegral_eq_mul
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4)
    (κp κm : PartialPairing (Fin m)) (ω : M.Ω) :
    pairingMomentRawSpatialIntegral
        M ρ ε m α β κp κm ω =
      pairingHalfIntegral M ρ ε m α β κp ω *
        pairingHalfIntegral M ρ ε m (-α) (-β) κm ω := by
  unfold pairingMomentRawSpatialIntegral pairingMomentRaw
  simp_rw [integral_momentDouble_mul m]
  simp_rw [integral_const_mul]
  simp_rw [integral_mul_const]
  unfold pairingHalfIntegral
  ring

/-- Product of two individual pairing coefficients as a scalar multiple
of the doubled raw physical integral. -/
theorem pmPairingCoeff_mul_conj_eq_rawSpatialIntegral
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4)
    (κp κm : PartialPairing (Fin m)) (ω : M.Ω) :
    pmPairingCoeff M ρ lam ε m α β κp ω *
        conj (pmPairingCoeff M ρ lam ε m α β κm ω) =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        pairingMomentRawSpatialIntegral
          M ρ ε m α β κp κm ω := by
  rw [conj_pmPairingCoeff]
  rw [pmPairingCoeff_eq_lam_pow_mul_pairingHalfIntegral,
    pmPairingCoeff_eq_lam_pow_mul_pairingHalfIntegral,
    pairingMomentRawSpatialIntegral_eq_mul]
  rw [show 2 * m = m + m by omega, pow_add]
  ring

/-! ## Joint noise--space integrand -/

/-- Left-associated carrier for one unintegrated pairing half. -/
abbrev PairingHalfPoint (M : NoiseModel) (m : ℕ) :=
  ((M.Ω × T4) × T4) × (Fin m → T4)

/-- Assemble the noise sample and all spatial variables of one pairing
half into the carrier used by the joint random-integrand theorem. -/
def pairingHalfTupleMap
    (M : NoiseModel) (m : ℕ) :
    PairingHalfPoint M m →
      M.Ω × (Fin (m + 2) → T4) :=
  fun p =>
    (p.1.1.1, assemble p.1.1.2 p.1.2 p.2)

theorem measurable_pairingHalfTupleMap
    (M : NoiseModel) (m : ℕ) :
    Measurable (pairingHalfTupleMap M m) := by
  have hω :
      Measurable fun p : PairingHalfPoint M m => p.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hx :
      Measurable fun p : PairingHalfPoint M m => p.1.1.2 :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hy :
      Measurable fun p : PairingHalfPoint M m => p.1.2 :=
    measurable_snd.comp measurable_fst
  have hassemble :
      Measurable fun p : PairingHalfPoint M m =>
        assemble p.1.1.2 p.1.2 p.2 :=
    (measurable_assemble_prod m).comp
      (hx.prodMk (hy.prodMk measurable_snd))
  exact hω.prodMk hassemble

/-- Select the left copy of the doubled physical tuple. -/
def pairingMomentLeftPoint
    (M : NoiseModel) (m : ℕ) :
    M.Ω × R324PhysicalPoint m → PairingHalfPoint M m :=
  fun p =>
    (((p.1, p.2.1), p.2.2.1),
      fun i => p.2.2.2.2.2 (leftMomentIndex i))

theorem measurable_pairingMomentLeftPoint
    (M : NoiseModel) (m : ℕ) :
    Measurable (pairingMomentLeftPoint M m) := by
  have hv :
      Measurable fun p : M.Ω × R324PhysicalPoint m =>
        p.2.2.2.2.2 :=
    measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))
  have hvp :
      Measurable fun p : M.Ω × R324PhysicalPoint m =>
        fun i : Fin m =>
          p.2.2.2.2.2 (leftMomentIndex i) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply (leftMomentIndex i)).comp hv
  exact
    (((measurable_fst.prodMk
      (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.comp
        (measurable_snd.comp measurable_snd))).prodMk hvp)

/-- Select the right copy of the doubled physical tuple. -/
def pairingMomentRightPoint
    (M : NoiseModel) (m : ℕ) :
    M.Ω × R324PhysicalPoint m → PairingHalfPoint M m :=
  fun p =>
    (((p.1, p.2.2.2.1), p.2.2.2.2.1),
      fun i => p.2.2.2.2.2 (rightMomentIndex i))

theorem measurable_pairingMomentRightPoint
    (M : NoiseModel) (m : ℕ) :
    Measurable (pairingMomentRightPoint M m) := by
  have hv :
      Measurable fun p : M.Ω × R324PhysicalPoint m =>
        p.2.2.2.2.2 :=
    measurable_snd.comp
      (measurable_snd.comp
        (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))
  have hvm :
      Measurable fun p : M.Ω × R324PhysicalPoint m =>
        fun i : Fin m =>
          p.2.2.2.2.2 (rightMomentIndex i) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply (rightMomentIndex i)).comp hv
  exact
    (((measurable_fst.prodMk
      (measurable_fst.comp
        (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))).prodMk
      (measurable_fst.comp
        (measurable_snd.comp
          (measurable_snd.comp
            (measurable_snd.comp measurable_snd))))).prodMk hvm)

/-- The Fourier phase of one pairing half is measurable on its carrier. -/
theorem measurable_pairingHalfPhase
    (M : NoiseModel) (m : ℕ) (α β : Z4) :
    Measurable fun p : PairingHalfPoint M m =>
      charT4 α p.1.1.2 * charT4 β p.1.2 := by
  apply Measurable.mul
  · exact
      (continuous_charT4 α).measurable.comp
        (measurable_snd.comp
          (measurable_fst.comp measurable_fst))
  · exact
      (continuous_charT4 β).measurable.comp
        (measurable_snd.comp measurable_fst)

/-- Named random factor of one pairing half.  Naming the composition avoids
forcing the elaborator to unfold the full Wick polynomial during every
measurability composition. -/
def pairingHalfRandom
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (p : PairingHalfPoint M m) : ℂ :=
  randIntegrand M ρ ε κ
    (pairingHalfTupleMap M m p).2
    (pairingHalfTupleMap M m p).1

theorem NoiseModel.measurable_pairingHalfRandom
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m)) :
    Measurable (pairingHalfRandom M ρ ε m κ) := by
  unfold pairingHalfRandom
  exact
    Complex.measurable_ofReal.comp
      ((M.measurable_randIntegrand_joint ρ ε κ).comp
        (measurable_pairingHalfTupleMap M m))

/-- Joint measurability of one unscaled pairing half. -/
theorem NoiseModel.measurable_pairingHalfIntegrand_joint
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) :
    Measurable fun p : PairingHalfPoint M m =>
      pairingHalfIntegrand M ρ ε m α β κ
        p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have h :
      Measurable fun p : PairingHalfPoint M m =>
        (charT4 α p.1.1.2 * charT4 β p.1.2) *
          pairingHalfRandom M ρ ε m κ p :=
    (measurable_pairingHalfPhase M m α β).mul
      (M.measurable_pairingHalfRandom ρ ε m κ)
  simpa only [pairingHalfRandom, pairingHalfTupleMap,
    pairingHalfIntegrand] using h

/-- Flatten the random doubled integrand onto noise times the genuine
R-324 physical product space. -/
def pairingMomentRawFlatten
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (p : M.Ω × R324PhysicalPoint m) : ℂ :=
  let pl := pairingMomentLeftPoint M m p
  let pr := pairingMomentRightPoint M m p
  pairingHalfIntegrand M ρ ε m α β κp
      pl.1.1.1 pl.1.1.2 pl.1.2 pl.2 *
    pairingHalfIntegrand M ρ ε m (-α) (-β) κm
      pr.1.1.1 pr.1.1.2 pr.1.2 pr.2

@[simp]
theorem pairingMomentRawFlatten_apply
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (ω : M.Ω) (p : R324PhysicalPoint m) :
    pairingMomentRawFlatten M ρ ε m α β κp κm (ω, p) =
      r324Flatten
        (pairingMomentRaw M ρ ε m α β κp κm ω) p := by
  rfl

/-- The raw doubled moment integrand is jointly Borel measurable in the
noise sample and all physical variables. -/
theorem NoiseModel.measurable_pairingMomentRawFlatten
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m)) :
    Measurable
      (pairingMomentRawFlatten M ρ ε m α β κp κm) := by
  have h :
      Measurable fun p : M.Ω × R324PhysicalPoint m =>
        let pl := pairingMomentLeftPoint M m p
        let pr := pairingMomentRightPoint M m p
        pairingHalfIntegrand M ρ ε m α β κp
            pl.1.1.1 pl.1.1.2 pl.1.2 pl.2 *
          pairingHalfIntegrand M ρ ε m (-α) (-β) κm
            pr.1.1.1 pr.1.1.2 pr.1.2 pr.2 :=
    ((M.measurable_pairingHalfIntegrand_joint
      ρ ε m α β κp).comp
        (measurable_pairingMomentLeftPoint M m)).mul
      ((M.measurable_pairingHalfIntegrand_joint
        ρ ε m (-α) (-β) κm).comp
          (measurable_pairingMomentRightPoint M m))
  change
    Measurable fun p : M.Ω × R324PhysicalPoint m =>
      let pl := pairingMomentLeftPoint M m p
      let pr := pairingMomentRightPoint M m p
      pairingHalfIntegrand M ρ ε m α β κp
          pl.1.1.1 pl.1.1.2 pl.1.2 pl.2 *
        pairingHalfIntegrand M ρ ε m (-α) (-β) κm
          pr.1.1.1 pr.1.1.2 pr.1.2 pr.2
  exact h

/-- Integrating the raw doubled integrand in the noise variable gives the
named expected Wick moment integrand. -/
theorem integral_pairingMomentRaw_eq_expectedWickMomentIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    (∫ ω,
        pairingMomentRaw M ρ ε m α β κp κm
          ω x y z w v
        ∂(volume : Measure M.Ω)) =
      expectedWickMomentIntegrand
        M ρ ε m α β κp κm x y z w v := by
  let phase : ℂ :=
    charT4 α x * charT4 β y *
      charT4 (-α) z * charT4 (-β) w
  let det : ℝ :=
    detIntegrand ρ ε m κp
        (assemble x y fun i => v (leftMomentIndex i)) *
      detIntegrand ρ ε m κm
        (assemble z w fun i => v (rightMomentIndex i))
  calc
    (∫ ω,
        pairingMomentRaw M ρ ε m α β κp κm
          ω x y z w v
        ∂(volume : Measure M.Ω)) =
      phase * (det : ℂ) *
        ∫ ω,
          (pairedWickProduct M ρ ε m κp κm
            x y z w v ω : ℂ)
          ∂(volume : Measure M.Ω) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      unfold pairingMomentRaw pairingHalfIntegrand
        randIntegrand pairedWickProduct
      dsimp only [phase, det]
      push_cast
      ring
    _ = phase * (det : ℂ) *
        ((∫ ω,
          pairedWickProduct M ρ ε m κp κm x y z w v ω
          ∂(volume : Measure M.Ω) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal]
    _ = expectedWickMomentIntegrand
        M ρ ε m α β κp κm x y z w v := by
      unfold expectedWickMomentIntegrand
      dsimp only [phase, det]
      push_cast
      ring

/-- Joint noise--space integrability is the single analytic premise needed
to obtain both integrability of a pairing-coefficient product and its exact
Fubini expansion. -/
def PairingMomentRawIntegrable
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m)) : Prop :=
  Integrable
    (pairingMomentRawFlatten M ρ ε m α β κp κm)
    ((volume : Measure M.Ω).prod (r324PhysicalMeasure m))

/-- Joint integrability of the raw noise--space term implies integrability
of the corresponding product of Fourier coefficients. -/
theorem pairingProduct_integrable_of_raw
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (hraw :
      PairingMomentRawIntegrable M ρ ε m α β κp κm) :
    Integrable
      (fun ω =>
        pmPairingCoeff M ρ lam ε m α β κp ω *
          conj (pmPairingCoeff M ρ lam ε m α β κm ω))
      (volume : Measure M.Ω) := by
  have hsections :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        Integrable
          (fun p : R324PhysicalPoint m =>
            pairingMomentRawFlatten
              M ρ ε m α β κp κm (ω, p))
          (r324PhysicalMeasure m) :=
    hraw.prod_right_ae
  have houter :
      Integrable
        (fun ω =>
          ∫ p : R324PhysicalPoint m,
            pairingMomentRawFlatten
              M ρ ε m α β κp κm (ω, p)
            ∂(r324PhysicalMeasure m))
        (volume : Measure M.Ω) :=
    hraw.integral_prod_left
  have hscaled :=
    houter.const_mul (lamEps lam ε ^ (2 * m) : ℂ)
  refine hscaled.congr ?_
  filter_upwards [hsections] with ω hω
  have hω' :
      Integrable
        (r324Flatten
          (pairingMomentRaw
            M ρ ε m α β κp κm ω))
        (r324PhysicalMeasure m) := by
    change
      Integrable
        (fun p : R324PhysicalPoint m =>
          pairingMomentRaw M ρ ε m α β κp κm
            ω p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
        (r324PhysicalMeasure m)
    exact hω
  change
    (lamEps lam ε ^ (2 * m) : ℂ) *
        (∫ p, r324Flatten
          (pairingMomentRaw M ρ ε m α β κp κm ω) p
          ∂(r324PhysicalMeasure m)) =
      _
  rw [r324_integral_product_eq_five
    (pairingMomentRaw M ρ ε m α β κp κm ω) hω']
  exact
    (pmPairingCoeff_mul_conj_eq_rawSpatialIntegral
      M ρ lam ε m α β κp κm ω).symm

/-- Joint integrability gives the exact noise--space Fubini identity for
one pair `(κp,κm)`. -/
theorem pairingProduct_fubini_of_raw
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (hraw :
      PairingMomentRawIntegrable M ρ ε m α β κp κm) :
    (∫ ω,
        pmPairingCoeff M ρ lam ε m α β κp ω *
          conj (pmPairingCoeff M ρ lam ε m α β κm ω)
        ∂(volume : Measure M.Ω)) =
      expectedWickMomentPairingTerm
        M ρ lam ε m α β κp κm := by
  have hsections :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        Integrable
          (fun p : R324PhysicalPoint m =>
            pairingMomentRawFlatten
              M ρ ε m α β κp κm (ω, p))
          (r324PhysicalMeasure m) :=
    hraw.prod_right_ae
  have hexpected :
      Integrable
        (r324Flatten
          (expectedWickMomentIntegrand
            M ρ ε m α β κp κm))
        (r324PhysicalMeasure m) := by
    have hinner :
        Integrable
          (fun p : R324PhysicalPoint m =>
            ∫ ω,
              pairingMomentRawFlatten
                M ρ ε m α β κp κm (ω, p)
              ∂(volume : Measure M.Ω))
          (r324PhysicalMeasure m) :=
      hraw.integral_prod_right
    refine hinner.congr ?_
    filter_upwards with p
    calc
      (∫ ω,
          pairingMomentRawFlatten
            M ρ ε m α β κp κm (ω, p)
          ∂(volume : Measure M.Ω)) =
        ∫ ω,
          r324Flatten
            (pairingMomentRaw
              M ρ ε m α β κp κm ω) p
          ∂(volume : Measure M.Ω) := by
            apply integral_congr_ae
            filter_upwards with ω
            exact pairingMomentRawFlatten_apply
              M ρ ε m α β κp κm ω p
      _ = r324Flatten
          (expectedWickMomentIntegrand
            M ρ ε m α β κp κm) p := by
            simpa only [r324Flatten] using
              (integral_pairingMomentRaw_eq_expectedWickMomentIntegrand
                M ρ ε m α β κp κm
                  p.1 p.2.1 p.2.2.1
                  p.2.2.2.1 p.2.2.2.2)
  calc
    (∫ ω,
        pmPairingCoeff M ρ lam ε m α β κp ω *
          conj (pmPairingCoeff M ρ lam ε m α β κm ω)
        ∂(volume : Measure M.Ω)) =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        ∫ ω, ∫ p : R324PhysicalPoint m,
          pairingMomentRawFlatten
            M ρ ε m α β κp κm (ω, p)
          ∂(r324PhysicalMeasure m)
          ∂(volume : Measure M.Ω) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hsections] with ω hω
      have hω' :
          Integrable
            (r324Flatten
              (pairingMomentRaw
                M ρ ε m α β κp κm ω))
            (r324PhysicalMeasure m) := by
        change
          Integrable
            (fun p : R324PhysicalPoint m =>
              pairingMomentRaw M ρ ε m α β κp κm
                ω p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
            (r324PhysicalMeasure m)
        exact hω
      change
        pmPairingCoeff M ρ lam ε m α β κp ω *
            conj (pmPairingCoeff M ρ lam ε m α β κm ω) =
          (lamEps lam ε ^ (2 * m) : ℂ) *
            (∫ p, r324Flatten
              (pairingMomentRaw
                M ρ ε m α β κp κm ω) p
              ∂(r324PhysicalMeasure m))
      rw [r324_integral_product_eq_five
        (pairingMomentRaw M ρ ε m α β κp κm ω) hω']
      exact pmPairingCoeff_mul_conj_eq_rawSpatialIntegral
        M ρ lam ε m α β κp κm ω
    _ = (lamEps lam ε ^ (2 * m) : ℂ) *
        ∫ p : R324PhysicalPoint m, ∫ ω,
          pairingMomentRawFlatten
            M ρ ε m α β κp κm (ω, p)
          ∂(volume : Measure M.Ω)
          ∂(r324PhysicalMeasure m) := by
      have hraw' :
          Integrable
            (Function.uncurry fun
              (ω : M.Ω) (p : R324PhysicalPoint m) =>
                pairingMomentRawFlatten
                  M ρ ε m α β κp κm (ω, p))
            ((volume : Measure M.Ω).prod
              (r324PhysicalMeasure m)) := by
        unfold PairingMomentRawIntegrable at hraw
        refine hraw.congr ?_
        filter_upwards with q
        rcases q with ⟨ω, p⟩
        rfl
      rw [integral_integral_swap hraw']
    _ = (lamEps lam ε ^ (2 * m) : ℂ) *
        ∫ p : R324PhysicalPoint m,
          r324Flatten
            (expectedWickMomentIntegrand
              M ρ ε m α β κp κm) p
          ∂(r324PhysicalMeasure m) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      calc
        (∫ ω,
            pairingMomentRawFlatten
              M ρ ε m α β κp κm (ω, p)
            ∂(volume : Measure M.Ω)) =
          ∫ ω,
            r324Flatten
              (pairingMomentRaw
                M ρ ε m α β κp κm ω) p
            ∂(volume : Measure M.Ω) := by
              apply integral_congr_ae
              filter_upwards with ω
              exact pairingMomentRawFlatten_apply
                M ρ ε m α β κp κm ω p
        _ = r324Flatten
            (expectedWickMomentIntegrand
              M ρ ε m α β κp κm) p := by
              simpa only [r324Flatten] using
                integral_pairingMomentRaw_eq_expectedWickMomentIntegrand
                  M ρ ε m α β κp κm
                    p.1 p.2.1 p.2.2.1
                    p.2.2.2.1 p.2.2.2.2
    _ = expectedWickMomentPairingTerm
        M ρ lam ε m α β κp κm := by
      unfold expectedWickMomentPairingTerm
      rw [r324_integral_product_eq_five _ hexpected]

/-! ## Discharging joint integrability by uniform Wick domination -/

/-- Deterministic factor of the raw pairing moment, before the two Wick
factors are attached. -/
def pairingMomentDeterministicFactor
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  charT4 α x * charT4 β y *
    charT4 (-α) z * charT4 (-β) w *
    ((detIntegrand ρ ε m κp
        (assemble x y fun i => v (leftMomentIndex i)) *
      detIntegrand ρ ε m κm
        (assemble z w fun i => v (rightMomentIndex i)) : ℝ) : ℂ)

/-- The raw random term is the deterministic factor times the paired Wick
product. -/
theorem pairingMomentRaw_eq_deterministic_mul_wick
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (ω : M.Ω) (x y z w : T4) (v : Fin (2 * m) → T4) :
    pairingMomentRaw M ρ ε m α β κp κm ω x y z w v =
      pairingMomentDeterministicFactor
          ρ ε m α β κp κm x y z w v *
        (pairedWickProduct M ρ ε m κp κm
          x y z w v ω : ℂ) := by
  unfold pairingMomentRaw pairingHalfIntegrand randIntegrand
    pairingMomentDeterministicFactor pairedWickProduct
  push_cast
  ring

/-- Joint integrability of the deterministic doubled profile, together
with the uniform Wick second-moment bound, implies full noise--space
integrability. -/
theorem pairingMomentRawIntegrable_of_deterministic
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (m : ℕ)
    (α β : Z4) (κp κm : PartialPairing (Fin m))
    (hdet :
      Integrable
        (r324Flatten
          (pairingMomentDeterministicFactor
            ρ ε m α β κp κm))
        (r324PhysicalMeasure m)) :
    PairingMomentRawIntegrable
      M ρ ε m α β κp κm := by
  obtain ⟨C, hC0, hC⟩ :=
    M.exists_uniform_integral_norm_wickAt_mul_bound
      ρ hε hε1 κp κm
  have hmeas :=
    M.measurable_pairingMomentRawFlatten
      ρ ε m α β κp κm
  unfold PairingMomentRawIntegrable
  rw [integrable_prod_iff'
    hmeas.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun p => by
      let xtp :=
        assemble p.1 p.2.1
          (fun i => p.2.2.2.2 (leftMomentIndex i))
      let xtm :=
        assemble p.2.2.1 p.2.2.2.1
          (fun i => p.2.2.2.2 (rightMomentIndex i))
      have hwick :
          Integrable
            (fun ω =>
              (pairedWickProduct M ρ ε m κp κm
                p.1 p.2.1 p.2.2.1 p.2.2.2.1
                p.2.2.2.2 ω : ℂ))
            (volume : Measure M.Ω) := by
        have hreal :=
          M.integrable_wickAt_mul
            ρ hε κp κm xtp xtm
        exact hreal.ofReal
      have hscaled :=
        hwick.const_mul
          (pairingMomentDeterministicFactor
            ρ ε m α β κp κm
              p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      refine hscaled.congr ?_
      filter_upwards with ω
      exact
        (pairingMomentRaw_eq_deterministic_mul_wick
          M ρ ε m α β κp κm ω
            p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2).symm
  · have houterMeas :
        AEStronglyMeasurable
          (fun p : R324PhysicalPoint m =>
            ∫ ω,
              ‖pairingMomentRawFlatten
                M ρ ε m α β κp κm (ω, p)‖
              ∂(volume : Measure M.Ω))
          (r324PhysicalMeasure m) := by
      exact
        hmeas.norm.stronglyMeasurable.integral_prod_left'
          |>.aestronglyMeasurable
    have hdom :
        Integrable
          (fun p : R324PhysicalPoint m =>
            C *
              ‖r324Flatten
                (pairingMomentDeterministicFactor
                  ρ ε m α β κp κm) p‖)
          (r324PhysicalMeasure m) :=
      hdet.norm.const_mul C
    apply hdom.mono houterMeas
    filter_upwards with p
    have hbound :=
      hC
        (assemble p.1 p.2.1
          (fun i => p.2.2.2.2 (leftMomentIndex i)))
        (assemble p.2.2.1 p.2.2.2.1
          (fun i => p.2.2.2.2 (rightMomentIndex i)))
    have heq :
        (∫ ω,
            ‖pairingMomentRawFlatten
              M ρ ε m α β κp κm (ω, p)‖
            ∂(volume : Measure M.Ω)) =
          ‖r324Flatten
              (pairingMomentDeterministicFactor
                ρ ε m α β κp κm) p‖ *
            ∫ ω,
              ‖pairedWickProduct M ρ ε m κp κm
                p.1 p.2.1 p.2.2.1 p.2.2.2.1
                p.2.2.2.2 ω‖
              ∂(volume : Measure M.Ω) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      rw [pairingMomentRawFlatten_apply]
      unfold r324Flatten
      rw [pairingMomentRaw_eq_deterministic_mul_wick]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun _ => norm_nonneg _), heq]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hC0 (norm_nonneg _))]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

end

end Anderson4D
