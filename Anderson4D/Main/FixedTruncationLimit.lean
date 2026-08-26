import Anderson4D.Continuum.LogAsymptotics
import Anderson4D.Continuum.PrimitiveR51Assembly
import Anderson4D.Main.FixedTruncationMoments

/-!
# Fixed-truncation limits from Proposition 3.6

This file carries out the analytic normalization used in paper
(3.36)--(3.37).  The factor `λ_ε^r` in Proposition 3.6 is cancelled only
on the positive side of zero, where `λ_ε > 0`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- Proposition 3.6 mode/order data attached to one real-expansion atom. -/
def FixedTruncationAtom.prop36Mode {s B : ℕ}
    (modes : Fin s → Z4 × Z4)
    (a : FixedTruncationAtom s B) :
    (Z4 × Z4) × ℕ :=
  (a.modePair modes, a.order)

/-- The Proposition 3.6 family attached to an assignment of atoms. -/
def fixedTruncationAssignmentModes
    {s B r : ℕ} (modes : Fin s → Z4 × Z4)
    (assignment : Fin r → FixedTruncationAtom s B) :
    Fin r → (Z4 × Z4) × ℕ :=
  fun i => (assignment i).prop36Mode modes

theorem fixedTruncationAssignmentModes_valid
    {s B B' r : ℕ} (hBB' : B ≤ B')
    (modes : Fin s → Z4 × Z4)
    (assignment : Fin r → FixedTruncationAtom s B) :
    ∀ i, 1 ≤ (fixedTruncationAssignmentModes modes assignment i).2 ∧
      (fixedTruncationAssignmentModes modes assignment i).2 ≤ B' := by
  intro i
  exact ⟨(assignment i).order_pos,
    (assignment i).order_le.trans hBB'⟩

/-- All clauses of Proposition 3.6 at one fixed order bound and family
size, retaining the single coefficient table shared by every mode
family. -/
structure Prop36FullData
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    (B r : ℕ) where
  coeff : ℕ → ℕ → ℝ
  constant : ℝ
  constant_pos : 0 < constant
  coeff_bound :
    ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → 1 ≤ m₂ →
      |coeff m₁ m₂| ≤
        constant * (constant * lam) ^ (m₁ + m₂ - 2)
  sum_identity :
    ∀ m : ℕ, 2 ≤ m →
      positiveAntidiagonalSum coeff m =
        if Even m then prop36MomentBase lam ^ (m - 2) else 0
  family_clause :
    ∀ modes : Fin r → (Z4 × Z4) × ℕ,
      (∀ j, 1 ≤ (modes j).2 ∧ (modes j).2 ≤ B) →
      (∀ ε : ℝ, ∀ j, Measurable
        (pmCoeff M ρ lam ε (modes j).2
          (modes j).1.1 (modes j).1.2)) ∧
      (∀ ε : ℝ, Integrable
        (fun ω => ∏ j, pmCoeff M ρ lam ε (modes j).2
          (modes j).1.1 (modes j).1.2 ω)) ∧
      ∃ C' : ℝ, 0 < C' ∧
        ∀ᶠ ε in nhdsWithin 0 (Ioi (0 : ℝ)),
          (‖(∫ ω, ∏ j, pmCoeff M ρ lam ε (modes j).2
                (modes j).1.1 (modes j).1.2 ω) -
              ∑ κ ∈ Finset.univ.filter
                  (fun κ : PartialPairing (Fin r) => κ.IsFull),
                ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
                  (∫ ω, pmCoeff M ρ lam ε (modes i).2
                      (modes i).1.1 (modes i).1.2 ω *
                    pmCoeff M ρ lam ε (modes (κ i)).2
                      (modes (κ i)).1.1 (modes (κ i)).1.2 ω)‖
            ≤ C' * lamEps lam ε ^ r / |Real.log ε|) ∧
          ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
            1 ≤ m₂ → m₂ ≤ B → ∀ α₁ β₁ α₂ β₂ : Z4,
            ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 * coeff m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
              ≤ C' * lamEps lam ε ^ 2 / |Real.log ε|

namespace Prop36

/-- Canonical full Proposition 3.6 data at `(B,r)`.  Both the
coefficient table and the uniform geometric constant are selected by
the shared external-input choice functions. -/
def fullData
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (B r : ℕ) :
    Prop36FullData M ρ lam B r where
    coeff := hP36.coefficientTable B r
    constant := hP36.boundConstant
    constant_pos := hP36.boundConstant_pos
    coeff_bound := (hP36.coefficientTable_spec B r).1
    sum_identity := by
      intro m hm
      simpa only [positiveAntidiagonalSum, prop36MomentBase] using
        (hP36.coefficientTable_spec B r).2.1 m hm
    family_clause := (hP36.coefficientTable_spec B r).2.2

/-- Proposition 3.6 supplies full data at every `(B,r)`. -/
theorem nonempty_fullData
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (B r : ℕ) :
    Nonempty (Prop36FullData M ρ lam B r) :=
  ⟨hP36.fullData B r⟩

end Prop36

/-- An `O(λ_ε^r / |log ε|)` complex error becomes `o(1)` after
normalization by `λ_ε^r`. -/
theorem tendsto_inv_lamEps_pow_mul_of_norm_sub_le
    {f : ℝ → ℂ} {z : ℂ} {lam C : ℝ} {r : ℕ}
    (hlam : 0 < lam)
    (hbound :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ‖f ε - (lamEps lam ε : ℂ) ^ r * z‖ ≤
          C * lamEps lam ε ^ r / |Real.log ε|) :
    Tendsto
      (fun ε =>
        (lamEps lam ε : ℂ)⁻¹ ^ r * f ε)
      (nhdsWithin 0 (Ioi 0)) (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero'
    (Eventually.of_forall fun ε =>
      norm_nonneg
        ((lamEps lam ε : ℂ)⁻¹ ^ r * f ε - z))
    ?_ (tendsto_const_div_abs_log_nhdsGT_zero C)
  filter_upwards [hbound, eventually_lamEps_pos hlam,
    eventually_abs_log_pos] with ε hε hlamε hlog
  have hlamεne : lamEps lam ε ≠ 0 := ne_of_gt hlamε
  have hlamεneC : (lamEps lam ε : ℂ) ≠ 0 := by
    exact_mod_cast hlamεne
  have hcancelC :
      (lamEps lam ε : ℂ) ^ r *
          (lamEps lam ε : ℂ)⁻¹ ^ r = 1 := by
    rw [← mul_pow]
    simp only [mul_inv_cancel₀ hlamεneC, one_pow]
  have hcancelC' :
      (lamEps lam ε : ℂ)⁻¹ ^ r *
          (lamEps lam ε : ℂ) ^ r = 1 := by
    rw [mul_comm]
    exact hcancelC
  have hcancelR :
      (lamEps lam ε)⁻¹ ^ r * lamEps lam ε ^ r = 1 := by
    rw [← mul_pow]
    simp only [inv_mul_cancel₀ hlamεne, one_pow]
  calc
    ‖(lamEps lam ε : ℂ)⁻¹ ^ r * f ε - z‖ =
        ‖(lamEps lam ε : ℂ)⁻¹ ^ r *
          (f ε - (lamEps lam ε : ℂ) ^ r * z)‖ := by
      congr 1
      rw [mul_sub]
      rw [← mul_assoc, hcancelC', one_mul]
    _ = ‖(lamEps lam ε : ℂ)⁻¹ ^ r‖ *
        ‖f ε - (lamEps lam ε : ℂ) ^ r * z‖ :=
      norm_mul _ _
    _ ≤ ‖(lamEps lam ε : ℂ)⁻¹ ^ r‖ *
        (C * lamEps lam ε ^ r / |Real.log ε|) := by
      exact mul_le_mul_of_nonneg_left hε (norm_nonneg _)
    _ = C / |Real.log ε| := by
      rw [norm_pow, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hlamε]
      calc
        (lamEps lam ε)⁻¹ ^ r *
              (C * lamEps lam ε ^ r / |Real.log ε|) =
            (C / |Real.log ε|) *
              ((lamEps lam ε)⁻¹ ^ r *
                lamEps lam ε ^ r) := by ring
        _ = C / |Real.log ε| := by rw [hcancelR, mul_one]

/-- Difference form of the preceding normalization lemma. -/
theorem tendsto_inv_lamEps_pow_mul_sub_of_norm_sub_le
    {f g : ℝ → ℂ} {lam C : ℝ} {r : ℕ}
    (hlam : 0 < lam)
    (hbound :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ‖f ε - g ε‖ ≤
          C * lamEps lam ε ^ r / |Real.log ε|) :
    Tendsto
      (fun ε =>
        (lamEps lam ε : ℂ)⁻¹ ^ r * (f ε - g ε))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  apply tendsto_inv_lamEps_pow_mul_of_norm_sub_le
    (f := fun ε => f ε - g ε) (z := 0) hlam
  simpa only [mul_zero, sub_zero] using hbound

/-- Covariance clause (3.27), after division by `λ_ε²`. -/
theorem tendsto_normalized_pmCoeff_pair
    (M : NoiseModel) (ρ : SmoothCutoff)
    {lam C X : ℝ} (hlam : 0 < lam)
    (m₁ m₂ : ℕ) (α₁ β₁ α₂ β₂ : Z4)
    (hbound :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
              pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
            (lamEps lam ε ^ 2 * X : ℝ) •
              fourPointHCoeff α₁ β₁ α₂ β₂‖
          ≤ C * lamEps lam ε ^ 2 / |Real.log ε|) :
    Tendsto
      (fun ε =>
        (lamEps lam ε : ℂ)⁻¹ ^ 2 *
          ∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
            pmCoeff M ρ lam ε m₂ α₂ β₂ ω)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 ((X : ℂ) * fourPointHCoeff α₁ β₁ α₂ β₂)) := by
  apply tendsto_inv_lamEps_pow_mul_of_norm_sub_le hlam
  filter_upwards [hbound] with ε hε
  convert hε using 1
  simp only [Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_pow]
  ring

/-- One pair covariance from a Proposition 3.6 family. -/
def prop36PairMoment
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {r : ℕ} (family : Fin r → (Z4 × Z4) × ℕ)
    (i j : Fin r) : ℂ :=
  ∫ ω, pmCoeff M ρ lam ε (family i).2
      (family i).1.1 (family i).1.2 ω *
    pmCoeff M ρ lam ε (family j).2
      (family j).1.1 (family j).1.2 ω

/-- The limiting pair covariance specified by one coefficient table. -/
def prop36PairLimit
    (𝔛 : ℕ → ℕ → ℝ)
    {r : ℕ} (family : Fin r → (Z4 × Z4) × ℕ)
    (i j : Fin r) : ℂ :=
  (𝔛 (family i).2 (family j).2 : ℂ) *
    fourPointHCoeff
      (family i).1.1 (family i).1.2
      (family j).1.1 (family j).1.2

/-- A full pairing has one selected lower endpoint per pair, hence twice
the number of displayed covariance factors is the family size. -/
theorem two_mul_card_fullPairingRepresentatives
    {r : ℕ} (κ : PartialPairing (Fin r)) (hκ : κ.IsFull) :
    2 * (κ.pairSupport.filter (fun i => i < κ i)).card = r := by
  rw [card_pairSupport_filter_lt_eq_pairs]
  have hcard := κ.card_pairSupport
  rw [PartialPairing.isFull_iff_pairSupport_eq_univ.mp hκ] at hcard
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard.symm

/-- Every normalized pair covariance in a fixed Proposition 3.6 family
converges to the covariance prescribed by its coefficient table. -/
theorem tendsto_normalized_prop36PairMoment
    (M : NoiseModel) (ρ : SmoothCutoff)
    {lam C : ℝ} (hlam : 0 < lam)
    {B r : ℕ} (𝔛 : ℕ → ℕ → ℝ)
    (family : Fin r → (Z4 × Z4) × ℕ)
    (hvalid : ∀ i, 1 ≤ (family i).2 ∧ (family i).2 ≤ B)
    (hcov :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
          1 ≤ m₂ → m₂ ≤ B → ∀ α₁ β₁ α₂ β₂ : Z4,
          ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 * 𝔛 m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
            ≤ C * lamEps lam ε ^ 2 / |Real.log ε|)
    (i j : Fin r) :
    Tendsto
      (fun ε => (lamEps lam ε : ℂ)⁻¹ ^ 2 *
        prop36PairMoment M ρ lam ε family i j)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (prop36PairLimit 𝔛 family i j)) := by
  apply tendsto_normalized_pmCoeff_pair M ρ hlam
  filter_upwards [hcov] with ε hε
  exact hε (family i).2 (family j).2
    (hvalid i).1 (hvalid i).2
    (hvalid j).1 (hvalid j).2
    (family i).1.1 (family i).1.2
    (family j).1.1 (family j).1.2

/-- Termwise full-pairing limit after the exact `λ_ε^r`
normalization ledger. -/
theorem tendsto_normalized_fullPairingProduct
    (M : NoiseModel) (ρ : SmoothCutoff)
    {lam C : ℝ} (hlam : 0 < lam)
    {B r : ℕ} (𝔛 : ℕ → ℕ → ℝ)
    (family : Fin r → (Z4 × Z4) × ℕ)
    (hvalid : ∀ i, 1 ≤ (family i).2 ∧ (family i).2 ≤ B)
    (hcov :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
          1 ≤ m₂ → m₂ ≤ B → ∀ α₁ β₁ α₂ β₂ : Z4,
          ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 * 𝔛 m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
            ≤ C * lamEps lam ε ^ 2 / |Real.log ε|)
    (κ : PartialPairing (Fin r)) (hκ : κ.IsFull) :
    Tendsto
      (fun ε =>
        (lamEps lam ε : ℂ)⁻¹ ^ r *
          ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
            prop36PairMoment M ρ lam ε family i (κ i))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        prop36PairLimit 𝔛 family i (κ i))) := by
  let edges := κ.pairSupport.filter (fun i => i < κ i)
  have hprod :
      Tendsto
        (fun ε =>
          ∏ i ∈ edges,
            ((lamEps lam ε : ℂ)⁻¹ ^ 2 *
              prop36PairMoment M ρ lam ε family i (κ i)))
        (nhdsWithin 0 (Ioi 0))
        (𝓝 (∏ i ∈ edges,
          prop36PairLimit 𝔛 family i (κ i))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_normalized_prop36PairMoment
      M ρ hlam 𝔛 family hvalid hcov i (κ i)
  refine hprod.congr' (Eventually.of_forall fun ε => ?_)
  have hcard :
      2 * (κ.pairSupport.filter (fun i => i < κ i)).card = r :=
    two_mul_card_fullPairingRepresentatives κ hκ
  dsimp only [edges]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_const]
  rw [← pow_mul]
  rw [hcard]

/-- Finite sum of all normalized full-pairing products. -/
theorem tendsto_normalized_fullPairingSum
    (M : NoiseModel) (ρ : SmoothCutoff)
    {lam C : ℝ} (hlam : 0 < lam)
    {B r : ℕ} (𝔛 : ℕ → ℕ → ℝ)
    (family : Fin r → (Z4 × Z4) × ℕ)
    (hvalid : ∀ i, 1 ≤ (family i).2 ∧ (family i).2 ≤ B)
    (hcov :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
          1 ≤ m₂ → m₂ ≤ B → ∀ α₁ β₁ α₂ β₂ : Z4,
          ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 * 𝔛 m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
            ≤ C * lamEps lam ε ^ 2 / |Real.log ε|) :
    Tendsto
      (fun ε =>
        (lamEps lam ε : ℂ)⁻¹ ^ r *
          ∑ κ ∈ Finset.univ.filter
              (fun κ : PartialPairing (Fin r) => κ.IsFull),
            ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
              prop36PairMoment M ρ lam ε family i (κ i))
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∑ κ ∈ Finset.univ.filter
          (fun κ : PartialPairing (Fin r) => κ.IsFull),
        ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
          prop36PairLimit 𝔛 family i (κ i))) := by
  let fulls :=
    Finset.univ.filter
      (fun κ : PartialPairing (Fin r) => κ.IsFull)
  have hsum :
      Tendsto
        (fun ε =>
          ∑ κ ∈ fulls,
            (lamEps lam ε : ℂ)⁻¹ ^ r *
              ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
                prop36PairMoment M ρ lam ε family i (κ i))
        (nhdsWithin 0 (Ioi 0))
        (𝓝 (∑ κ ∈ fulls,
          ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
            prop36PairLimit 𝔛 family i (κ i))) := by
    apply tendsto_finsetSum
    intro κ hκ
    exact tendsto_normalized_fullPairingProduct
      M ρ hlam 𝔛 family hvalid hcov κ
        (Finset.mem_filter.mp hκ).2
  refine hsum.congr' (Eventually.of_forall fun ε => ?_)
  dsimp only [fulls]
  rw [Finset.mul_sum]

/-- Proposition 3.6 Wick factorization (3.26) plus its covariance clause
(3.27): a normalized joint product converges to the full-pairing sum of
the prescribed limiting covariances. -/
theorem tendsto_normalized_prop36Product
    (M : NoiseModel) (ρ : SmoothCutoff)
    {lam C : ℝ} (hlam : 0 < lam)
    {B r : ℕ} (𝔛 : ℕ → ℕ → ℝ)
    (family : Fin r → (Z4 × Z4) × ℕ)
    (hvalid : ∀ i, 1 ≤ (family i).2 ∧ (family i).2 ≤ B)
    (hfactor :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ‖(∫ ω, ∏ j, pmCoeff M ρ lam ε
              (family j).2 (family j).1.1 (family j).1.2 ω) -
            ∑ κ ∈ Finset.univ.filter
                (fun κ : PartialPairing (Fin r) => κ.IsFull),
              ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
                prop36PairMoment M ρ lam ε family i (κ i)‖
          ≤ C * lamEps lam ε ^ r / |Real.log ε|)
    (hcov :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
          1 ≤ m₂ → m₂ ≤ B → ∀ α₁ β₁ α₂ β₂ : Z4,
          ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 * 𝔛 m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
            ≤ C * lamEps lam ε ^ 2 / |Real.log ε|) :
    Tendsto
      (fun ε =>
        (lamEps lam ε : ℂ)⁻¹ ^ r *
          ∫ ω, ∏ j, pmCoeff M ρ lam ε
            (family j).2 (family j).1.1 (family j).1.2 ω)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∑ κ ∈ Finset.univ.filter
          (fun κ : PartialPairing (Fin r) => κ.IsFull),
        ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
          prop36PairLimit 𝔛 family i (κ i))) := by
  let joint : ℝ → ℂ := fun ε =>
    ∫ ω, ∏ j, pmCoeff M ρ lam ε
      (family j).2 (family j).1.1 (family j).1.2 ω
  let pairingSum : ℝ → ℂ := fun ε =>
    ∑ κ ∈ Finset.univ.filter
        (fun κ : PartialPairing (Fin r) => κ.IsFull),
      ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        prop36PairMoment M ρ lam ε family i (κ i)
  have herr :
      Tendsto
        (fun ε => (lamEps lam ε : ℂ)⁻¹ ^ r *
          (joint ε - pairingSum ε))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    apply tendsto_inv_lamEps_pow_mul_sub_of_norm_sub_le hlam
    simpa only [joint, pairingSum] using hfactor
  have hpairs :=
    tendsto_normalized_fullPairingSum
      M ρ hlam 𝔛 family hvalid hcov
  have hadd := herr.add hpairs
  convert hadd using 1
  · funext ε
    dsimp only [joint, pairingSum]
    ring
  · simp

/-- Direct assignment-level API from one coherent Proposition 3.6 data
table. -/
theorem Prop36FullData.tendsto_assignmentProduct
    {M : NoiseModel} {ρ : SmoothCutoff}
    {lam : ℝ} (hlam : 0 < lam)
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    {B s : ℕ} (hBB' : B ≤ B')
    (modes : Fin s → Z4 × Z4)
    (assignment : Fin r → FixedTruncationAtom s B) :
    Tendsto
      (fun ε =>
        (lamEps lam ε : ℂ)⁻¹ ^ r *
          ∫ ω, ∏ j, pmCoeff M ρ lam ε
            (assignment j).order
            ((assignment j).modePair modes).1
            ((assignment j).modePair modes).2 ω)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (∑ κ ∈ Finset.univ.filter
          (fun κ : PartialPairing (Fin r) => κ.IsFull),
        ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
          prop36PairLimit data.coeff
            (fixedTruncationAssignmentModes modes assignment)
            i (κ i))) := by
  let family :=
    fixedTruncationAssignmentModes modes assignment
  have hvalid :
      ∀ i, 1 ≤ (family i).2 ∧ (family i).2 ≤ B' :=
    fixedTruncationAssignmentModes_valid hBB' modes assignment
  obtain ⟨_hmeasurable, _hintegrable, C', _hC', hevent⟩ :=
    data.family_clause family hvalid
  have hfactor :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ‖(∫ ω, ∏ j, pmCoeff M ρ lam ε
              (family j).2 (family j).1.1 (family j).1.2 ω) -
            ∑ κ ∈ Finset.univ.filter
                (fun κ : PartialPairing (Fin r) => κ.IsFull),
              ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
                prop36PairMoment M ρ lam ε family i (κ i)‖
          ≤ C' * lamEps lam ε ^ r / |Real.log ε| :=
    hevent.mono fun ε hε => by
      simpa only [prop36PairMoment] using hε.1
  have hcov :
      ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B' →
          1 ≤ m₂ → m₂ ≤ B' → ∀ α₁ β₁ α₂ β₂ : Z4,
          ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 * data.coeff m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
            ≤ C' * lamEps lam ε ^ 2 / |Real.log ε| :=
    hevent.mono fun ε hε => hε.2
  simpa only [family, fixedTruncationAssignmentModes,
    FixedTruncationAtom.prop36Mode] using
    tendsto_normalized_prop36Product
      M ρ hlam data.coeff family hvalid hfactor hcov

/-- Complex presentation of the limiting `r`-th moment of a real
fixed-truncation functional. -/
def fixedTruncationMomentLimit
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) : ℂ :=
  ∑ assignment : Fin r → FixedTruncationAtom s B,
    (∏ i, (assignment i).coeff c) *
      ∑ κ ∈ Finset.univ.filter
          (fun κ : PartialPairing (Fin r) => κ.IsFull),
        ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
          prop36PairLimit data.coeff
            (fixedTruncationAssignmentModes modes assignment)
            i (κ i)

/-- Every atom-assignment product is integrable, using the regularity
clause recorded with Proposition 3.6. -/
theorem Prop36FullData.integrable_assignmentAtomProduct
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    {B s : ℕ} (hBB' : B ≤ B')
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (assignment : Fin r → FixedTruncationAtom s B)
    (ε : ℝ) :
    Integrable
      (fun ω =>
        ∏ i, fixedTruncationAtomTerm
          M ρ lam ε modes c (assignment i) ω) := by
  let family :=
    fixedTruncationAssignmentModes modes assignment
  have hvalid :
      ∀ i, 1 ≤ (family i).2 ∧ (family i).2 ≤ B' :=
    fixedTruncationAssignmentModes_valid hBB' modes assignment
  obtain ⟨_hmeasurable, hintegrable, _rest⟩ :=
    data.family_clause family hvalid
  have hraw := hintegrable ε
  have hscaled :=
    hraw.const_mul
      ((∏ i, (assignment i).coeff c) *
        (lamEps lam ε : ℂ)⁻¹ ^ r)
  apply hscaled.congr
  filter_upwards with ω
  rw [prod_fixedTruncationAtomTerm]
  simp only [family, fixedTruncationAssignmentModes,
    FixedTruncationAtom.prop36Mode]

/-- Exact expectation ledger for one atom assignment. -/
theorem integral_assignmentAtomProduct
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B r s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (assignment : Fin r → FixedTruncationAtom s B)
    (ε : ℝ) :
    (∫ ω, ∏ i, fixedTruncationAtomTerm
        M ρ lam ε modes c (assignment i) ω) =
      (∏ i, (assignment i).coeff c) *
        ((lamEps lam ε : ℂ)⁻¹ ^ r *
          ∫ ω, ∏ i, pmCoeff M ρ lam ε (assignment i).order
            ((assignment i).modePair modes).1
            ((assignment i).modePair modes).2 ω) := by
  rw [integral_congr_ae
    (Eventually.of_forall fun ω =>
      prod_fixedTruncationAtomTerm
        M ρ lam ε modes c assignment ω)]
  rw [integral_const_mul]
  ring

/-- Integrability of every complexified fixed-truncation power. -/
theorem Prop36FullData.integrable_fixedTruncationComplexPow
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    {B s : ℕ} (hBB' : B ≤ B')
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ε : ℝ) :
    Integrable
      (fun ω =>
        (fixedTruncationReal
          M ρ lam ε B s modes c ω : ℂ) ^ r) := by
  have hsum :
      Integrable
        (fun ω =>
          ∑ assignment : Fin r → FixedTruncationAtom s B,
            ∏ i, fixedTruncationAtomTerm
              M ρ lam ε modes c (assignment i) ω) := by
    apply integrable_finsetSum
    intro assignment hassignment
    exact data.integrable_assignmentAtomProduct
      hBB' modes c assignment ε
  apply hsum.congr
  filter_upwards with ω
  exact
    (ofReal_fixedTruncationReal_pow_eq_sum_assignments
      M ρ lam ε B s r modes c ω).symm

/-- Integrating the finite assignment expansion is lossless. -/
theorem Prop36FullData.integral_fixedTruncationComplexPow
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    {B s : ℕ} (hBB' : B ≤ B')
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ε : ℝ) :
    (∫ ω,
      (fixedTruncationReal
        M ρ lam ε B s modes c ω : ℂ) ^ r) =
      ∑ assignment : Fin r → FixedTruncationAtom s B,
        ∫ ω, ∏ i, fixedTruncationAtomTerm
          M ρ lam ε modes c (assignment i) ω := by
  calc
    (∫ ω,
        (fixedTruncationReal
          M ρ lam ε B s modes c ω : ℂ) ^ r) =
        ∫ ω,
          ∑ assignment : Fin r → FixedTruncationAtom s B,
            ∏ i, fixedTruncationAtomTerm
              M ρ lam ε modes c (assignment i) ω := by
      apply integral_congr_ae
      filter_upwards with ω
      exact
        ofReal_fixedTruncationReal_pow_eq_sum_assignments
          M ρ lam ε B s r modes c ω
    _ = _ := by
      apply integral_finsetSum
      intro assignment hassignment
      exact data.integrable_assignmentAtomProduct
        hBB' modes c assignment ε

/-- Fixed-`B` convergence of every complexified raw moment, directly
from Proposition 3.6. -/
theorem Prop36FullData.tendsto_fixedTruncationComplexMoment
    {M : NoiseModel} {ρ : SmoothCutoff}
    {lam : ℝ} (hlam : 0 < lam)
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    {B s : ℕ} (hBB' : B ≤ B')
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Tendsto
      (fun ε =>
        ∫ ω,
          (fixedTruncationReal
            M ρ lam ε B s modes c ω : ℂ) ^ r)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (fixedTruncationMomentLimit data B modes c)) := by
  have hsum :
      Tendsto
        (fun ε =>
          ∑ assignment : Fin r → FixedTruncationAtom s B,
            (∏ i, (assignment i).coeff c) *
              ((lamEps lam ε : ℂ)⁻¹ ^ r *
                ∫ ω, ∏ i, pmCoeff M ρ lam ε
                  (assignment i).order
                  ((assignment i).modePair modes).1
                  ((assignment i).modePair modes).2 ω))
        (nhdsWithin 0 (Ioi 0))
        (𝓝 (fixedTruncationMomentLimit data B modes c)) := by
    unfold fixedTruncationMomentLimit
    apply tendsto_finsetSum
    intro assignment hassignment
    exact Tendsto.const_mul
      (∏ i, (assignment i).coeff c)
      (data.tendsto_assignmentProduct
        hlam hBB' modes assignment)
  refine hsum.congr' (Eventually.of_forall fun ε => ?_)
  change _ =
    ∫ ω,
      (fixedTruncationReal
        M ρ lam ε B s modes c ω : ℂ) ^ r
  rw [data.integral_fixedTruncationComplexPow hBB' modes c ε]
  apply Finset.sum_congr rfl
  intro assignment hassignment
  exact (integral_assignmentAtomProduct
    (M := M) (ρ := ρ) (lam := lam)
    modes c assignment ε).symm

end

end Anderson4D
