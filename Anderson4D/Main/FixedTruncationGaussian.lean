import Anderson4D.Probability.FullPairingRecursion
import Anderson4D.Main.FixedTruncationLimit
import Anderson4D.Main.GaussianPSD

/-!
# Gaussian identification of fixed-truncation moments

This file identifies the finite full-pairing limit supplied by
Proposition 3.6 with the moments of one centered real Gaussian.  It first
regroups atom assignments by finite multilinearity, then evaluates the
single constant-covariance Wick recursion.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology

/-- The zero-mode four-point coefficient is strictly nonzero.  This
single test mode makes the coefficient table in (3.27) unique on every
overlap of two Proposition 3.6 witnesses. -/
theorem fourPointHCoeff_zero_ne_zero :
    fourPointHCoeff (0 : Z4) 0 0 0 ≠ 0 := by
  rw [fourPointHCoeff_eq_indicator]
  simp only [zero_add]
  simp [greenModeWeight, Real.pi_ne_zero]

/-- Although Proposition 3.6 presents its witness after fixing `B` and
`r`, the covariance asymptotic forces any two witnesses to agree on
their common order range. -/
theorem Prop36FullData.coeff_eq_of_le
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hlam : 0 < lam)
    {B₁ B₂ r₁ r₂ : ℕ}
    (data₁ : Prop36FullData M ρ lam B₁ r₁)
    (data₂ : Prop36FullData M ρ lam B₂ r₂)
    {m₁ m₂ : ℕ}
    (hm₁pos : 1 ≤ m₁) (hm₁B₁ : m₁ ≤ B₁) (hm₁B₂ : m₁ ≤ B₂)
    (hm₂pos : 1 ≤ m₂) (hm₂B₁ : m₂ ≤ B₁) (hm₂B₂ : m₂ ≤ B₂) :
    data₁.coeff m₁ m₂ = data₂.coeff m₁ m₂ := by
  let family₁ : Fin r₁ → (Z4 × Z4) × ℕ :=
    fun _ => (((0 : Z4), (0 : Z4)), m₁)
  let family₂ : Fin r₂ → (Z4 × Z4) × ℕ :=
    fun _ => (((0 : Z4), (0 : Z4)), m₁)
  have hvalid₁ :
      ∀ i, 1 ≤ (family₁ i).2 ∧ (family₁ i).2 ≤ B₁ :=
    fun _ => ⟨hm₁pos, hm₁B₁⟩
  have hvalid₂ :
      ∀ i, 1 ≤ (family₂ i).2 ∧ (family₂ i).2 ≤ B₂ :=
    fun _ => ⟨hm₁pos, hm₁B₂⟩
  obtain ⟨_hmeas₁, _hint₁, C₁, _hC₁, hevent₁⟩ :=
    data₁.family_clause family₁ hvalid₁
  obtain ⟨_hmeas₂, _hint₂, C₂, _hC₂, hevent₂⟩ :=
    data₂.family_clause family₂ hvalid₂
  have hbound₁ :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ‖(∫ ω, pmCoeff M ρ lam ε m₁ 0 0 ω *
              pmCoeff M ρ lam ε m₂ 0 0 ω) -
            (lamEps lam ε ^ 2 * data₁.coeff m₁ m₂ : ℝ) •
              fourPointHCoeff 0 0 0 0‖
          ≤ C₁ * lamEps lam ε ^ 2 / |Real.log ε| :=
    hevent₁.mono fun ε hε =>
      hε.2 m₁ m₂ hm₁pos hm₁B₁ hm₂pos hm₂B₁ 0 0 0 0
  have hbound₂ :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        ‖(∫ ω, pmCoeff M ρ lam ε m₁ 0 0 ω *
              pmCoeff M ρ lam ε m₂ 0 0 ω) -
            (lamEps lam ε ^ 2 * data₂.coeff m₁ m₂ : ℝ) •
              fourPointHCoeff 0 0 0 0‖
          ≤ C₂ * lamEps lam ε ^ 2 / |Real.log ε| :=
    hevent₂.mono fun ε hε =>
      hε.2 m₁ m₂ hm₁pos hm₁B₂ hm₂pos hm₂B₂ 0 0 0 0
  have ht₁ :=
    tendsto_normalized_pmCoeff_pair
      M ρ hlam m₁ m₂ 0 0 0 0 hbound₁
  have ht₂ :=
    tendsto_normalized_pmCoeff_pair
      M ρ hlam m₁ m₂ 0 0 0 0 hbound₂
  have heq :
      (data₁.coeff m₁ m₂ : ℂ) * fourPointHCoeff 0 0 0 0 =
        (data₂.coeff m₁ m₂ : ℂ) * fourPointHCoeff 0 0 0 0 :=
    tendsto_nhds_unique ht₁ ht₂
  have hcoeffC :
      (data₁.coeff m₁ m₂ : ℂ) =
        (data₂.coeff m₁ m₂ : ℂ) := by
    exact mul_right_cancel₀ fourPointHCoeff_zero_ne_zero heq
  exact_mod_cast hcoeffC

/-- Limiting covariance between two atoms in the real-part expansion. -/
def fixedTruncationAtomPairLimit
    (X : ℕ → ℕ → ℝ) {B s : ℕ}
    (modes : Fin s → Z4 × Z4)
    (a b : FixedTruncationAtom s B) : ℂ :=
  (X a.order b.order : ℂ) *
    fourPointHCoeff
      (a.modePair modes).1 (a.modePair modes).2
      (b.modePair modes).1 (b.modePair modes).2

/-- Variance obtained after summing every pair of atoms. -/
def fixedTruncationPairVariance
    (X : ℕ → ℕ → ℝ) (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) : ℂ :=
  ∑ a : FixedTruncationAtom s B,
    ∑ b : FixedTruncationAtom s B,
      a.coeff c * b.coeff c *
        fixedTruncationAtomPairLimit X modes a b

theorem fixedTruncationPairVariance_congr
    {X Y : ℕ → ℕ → ℝ} {B s : ℕ}
    (hXY : ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
      1 ≤ m₂ → m₂ ≤ B → X m₁ m₂ = Y m₁ m₂)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    fixedTruncationPairVariance X B modes c =
      fixedTruncationPairVariance Y B modes c := by
  unfold fixedTruncationPairVariance
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  unfold fixedTruncationAtomPairLimit
  rw [hXY a.order b.order a.order_pos a.order_le
    b.order_pos b.order_le]

theorem Prop36FullData.fixedTruncationPairVariance_eq
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hlam : 0 < lam)
    {B₁ B₂ r₁ r₂ B s : ℕ}
    (data₁ : Prop36FullData M ρ lam B₁ r₁)
    (data₂ : Prop36FullData M ρ lam B₂ r₂)
    (hBB₁ : B ≤ B₁) (hBB₂ : B ≤ B₂)
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    fixedTruncationPairVariance data₁.coeff B modes c =
      fixedTruncationPairVariance data₂.coeff B modes c := by
  apply fixedTruncationPairVariance_congr
  intro m₁ m₂ hm₁pos hm₁B hm₂pos hm₂B
  exact data₁.coeff_eq_of_le hlam data₂
    hm₁pos (hm₁B.trans hBB₁) (hm₁B.trans hBB₂)
    hm₂pos (hm₂B.trans hBB₁) (hm₂B.trans hBB₂)

theorem prop36PairLimit_assignment_eq_atomPairLimit
    (X : ℕ → ℕ → ℝ) {B s r : ℕ}
    (modes : Fin s → Z4 × Z4)
    (assignment : Fin r → FixedTruncationAtom s B)
    (i j : Fin r) :
    prop36PairLimit X
        (fixedTruncationAssignmentModes modes assignment) i j =
      fixedTruncationAtomPairLimit X modes
        (assignment i) (assignment j) := by
  rfl

/-- The explicit full-pairing sum for one atom assignment is the
recursive Wick sum for the atom covariance kernel. -/
theorem assignmentFullPairingSum_eq_finWickPairing
    (X : ℕ → ℕ → ℝ) {B s r : ℕ}
    (modes : Fin s → Z4 × Z4)
    (assignment : Fin r → FixedTruncationAtom s B) :
    (∑ κ ∈ Finset.univ.filter
        (fun κ : PartialPairing (Fin r) => κ.IsFull),
      ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        prop36PairLimit X
          (fixedTruncationAssignmentModes modes assignment)
          i (κ i)) =
      finWickPairing
        (fixedTruncationAtomPairLimit X modes)
        r assignment := by
  calc
    (∑ κ ∈ Finset.univ.filter
        (fun κ : PartialPairing (Fin r) => κ.IsFull),
      ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
        prop36PairLimit X
          (fixedTruncationAssignmentModes modes assignment)
          i (κ i)) =
        PartialPairing.fullCovarianceSum
          (fixedTruncationAtomPairLimit X modes) assignment := by
      rw [PartialPairing.fullCovarianceSum_eq_filter_sum]
      apply Finset.sum_congr rfl
      intro κ hκ
      apply Finset.prod_congr rfl
      intro i hi
      exact prop36PairLimit_assignment_eq_atomPairLimit
        X modes assignment i (κ i)
    _ = _ :=
      PartialPairing.fullCovarianceSum_fin_eq_finWickPairing
        (fixedTruncationAtomPairLimit X modes) r assignment

/-- All atom assignments regroup into one full-pairing sum with the
summed pair variance on every edge. -/
theorem fixedTruncationMomentLimit_eq_finWickPairing
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' r : ℕ} (data : Prop36FullData M ρ lam B' r)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    fixedTruncationMomentLimit data B modes c =
      finWickPairing
        (fun _ _ : Fin r =>
          fixedTruncationPairVariance data.coeff B modes c)
        r id := by
  unfold fixedTruncationMomentLimit
  simp_rw [assignmentFullPairingSum_eq_finWickPairing
    data.coeff modes]
  let C :
      (Fin r × FixedTruncationAtom s B) →
        (Fin r × FixedTruncationAtom s B) → ℂ :=
    fun p q =>
      fixedTruncationAtomPairLimit data.coeff modes p.2 q.2
  let w : Fin r → FixedTruncationAtom s B → ℂ :=
    fun _ a => a.coeff c
  have hmulti :=
    finiteAssignmentExpansion_eq_finWickPairing C w r id
  calc
    (∑ assignment : Fin r → FixedTruncationAtom s B,
        (∏ i, (assignment i).coeff c) *
          finWickPairing
            (fixedTruncationAtomPairLimit data.coeff modes)
            r assignment) =
        ∑ assignment : Fin r → FixedTruncationAtom s B,
          finiteAssignmentWeight w id assignment *
            finWickPairing C r
              (fun i => (id i, assignment i)) := by
      apply Fintype.sum_congr
      intro assignment
      congr 1
      have hcomp :=
        finWickPairing_comp C
          (fun i : Fin r => (i, assignment i)) r id
      calc
        finWickPairing
            (fixedTruncationAtomPairLimit data.coeff modes)
            r assignment =
            finWickPairing
              (fun i j =>
                fixedTruncationAtomPairLimit data.coeff modes
                  (assignment i) (assignment j))
              r id := by
          simpa only [Function.comp_apply, id_eq] using
            (finWickPairing_comp
              (fixedTruncationAtomPairLimit data.coeff modes)
              assignment r id)
        _ = finWickPairing C r
              (fun i => (id i, assignment i)) := by
          simpa only [C, Function.comp_apply, id_eq] using hcomp.symm
    _ = finWickPairing
          (fun _ _ : Fin r =>
            fixedTruncationPairVariance data.coeff B modes c)
          r id := by
      rw [hmulti]
      congr 1

/-- The second full-pairing limit is the summed atom covariance itself. -/
theorem fixedTruncationMomentLimit_two
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' : ℕ} (data : Prop36FullData M ρ lam B' 2)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    fixedTruncationMomentLimit data B modes c =
      fixedTruncationPairVariance data.coeff B modes c := by
  rw [fixedTruncationMomentLimit_eq_finWickPairing]
  simp [finWickPairing]

/-- For the canonical `r=2` witness, the finite summed covariance is
real and nonnegative because it is the limit of genuine real squares. -/
theorem Prop36.canonicalPairVariance_real_nonneg
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    let V :=
      fixedTruncationPairVariance
        (hP36.fullData B 2).coeff B modes c
    V.im = 0 ∧ 0 ≤ V.re := by
  let data := hP36.fullData B 2
  let V :=
    fixedTruncationPairVariance data.coeff B modes c
  have htComplex :
      Tendsto
        (fun ε =>
          ∫ ω,
            (fixedTruncationReal
              M ρ lam ε B s modes c ω : ℂ) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 V) := by
    simpa only [V, fixedTruncationMomentLimit_two] using
      data.tendsto_fixedTruncationComplexMoment
        hlam le_rfl modes c
  have hIntegralIm (ε : ℝ) :
      (∫ ω,
        (fixedTruncationReal
          M ρ lam ε B s modes c ω : ℂ) ^ 2).im = 0 := by
    change RCLike.im
      (∫ ω,
        (fixedTruncationReal
          M ρ lam ε B s modes c ω : ℂ) ^ 2) = 0
    rw [← integral_im
      (data.integrable_fixedTruncationComplexPow
        le_rfl modes c ε)]
    calc
      (∫ x,
          RCLike.im
            ((fixedTruncationReal
              M ρ lam ε B s modes c x : ℂ) ^ 2)) =
          ∫ _x : M.Ω, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards with x
        exact RCLike.im_ofReal_pow
          (fixedTruncationReal
            M ρ lam ε B s modes c x) 2
      _ = 0 := integral_zero M.Ω ℝ
  have hIntegralRe (ε : ℝ) :
      (∫ ω,
        (fixedTruncationReal
          M ρ lam ε B s modes c ω : ℂ) ^ 2).re =
        ∫ ω,
          fixedTruncationReal
            M ρ lam ε B s modes c ω ^ 2 := by
    change RCLike.re
      (∫ ω,
        (fixedTruncationReal
          M ρ lam ε B s modes c ω : ℂ) ^ 2) =
        ∫ ω,
          fixedTruncationReal
            M ρ lam ε B s modes c ω ^ 2
    rw [← integral_re
      (data.integrable_fixedTruncationComplexPow
        le_rfl modes c ε)]
    apply integral_congr_ae
    filter_upwards with ω
    exact RCLike.re_ofReal_pow
      (fixedTruncationReal
        M ρ lam ε B s modes c ω) 2
  have hIm :
      V.im = 0 := by
    have htIm :=
      (Complex.continuous_im.tendsto V).comp htComplex
    have htIm' :
        Tendsto (fun _ : ℝ => (0 : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 V.im) :=
      htIm.congr'
        (Filter.Eventually.of_forall fun ε => by
          simp only [Function.comp_apply]
          exact hIntegralIm ε)
    exact tendsto_nhds_unique htIm' tendsto_const_nhds
  have hRe :
      Tendsto
        (fun ε =>
          ∫ ω,
            fixedTruncationReal
              M ρ lam ε B s modes c ω ^ 2)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 V.re) := by
    have htRe :=
      (Complex.continuous_re.tendsto V).comp htComplex
    exact htRe.congr'
      (Filter.Eventually.of_forall fun ε => by
        simp only [Function.comp_apply]
        exact hIntegralRe ε)
  have hnonneg :
      0 ≤ V.re := by
    apply ge_of_tendsto hRe
    exact Filter.Eventually.of_forall fun ε =>
      integral_nonneg fun ω => sq_nonneg _
  exact ⟨hIm, hnonneg⟩

/-- Canonical nonnegative finite-truncation variance. -/
def fixedTruncationGaussianVariance
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) : ℝ≥0 :=
  ⟨(fixedTruncationPairVariance
      (hP36.fullData B 2).coeff B modes c).re,
    (hP36.canonicalPairVariance_real_nonneg
      hlam B modes c).2⟩

theorem ofReal_fixedTruncationGaussianVariance
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    ((fixedTruncationGaussianVariance
        hP36 hlam B modes c : ℝ≥0) : ℝ) =
      (fixedTruncationPairVariance
        (hP36.fullData B 2).coeff B modes c).re := rfl

theorem complex_ofReal_fixedTruncationGaussianVariance
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    (((fixedTruncationGaussianVariance
        hP36 hlam B modes c : ℝ≥0) : ℝ) : ℂ) =
      fixedTruncationPairVariance
        (hP36.fullData B 2).coeff B modes c := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    exact
      (hP36.canonicalPairVariance_real_nonneg
        hlam B modes c).1.symm

/-- Every chosen moment-order witness gives the moments of the same
canonical finite-truncation Gaussian. -/
theorem Prop36.fixedTruncationMomentLimit_eq_gaussianMoment
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B n : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    fixedTruncationMomentLimit
        (hP36.fullData B n) B modes c =
      (centeredGaussianMoment
        (fixedTruncationGaussianVariance
          hP36 hlam B modes c) n : ℂ) := by
  let dataN := hP36.fullData B n
  let dataTwo := hP36.fullData B 2
  let Vn :=
    fixedTruncationPairVariance dataN.coeff B modes c
  let Vtwo :=
    fixedTruncationPairVariance dataTwo.coeff B modes c
  let v :=
    fixedTruncationGaussianVariance hP36 hlam B modes c
  have hV : Vn = Vtwo := by
    exact dataN.fixedTruncationPairVariance_eq
      hlam dataTwo le_rfl le_rfl modes c
  have hVcast : (((v : ℝ≥0) : ℝ) : ℂ) = Vtwo := by
    simpa only [v, dataTwo] using
      complex_ofReal_fixedTruncationGaussianVariance
        hP36 hlam B modes c
  rw [fixedTruncationMomentLimit_eq_finWickPairing]
  change
    finWickPairing (fun _ _ : Fin n => Vn) n id =
      (centeredGaussianMoment v n : ℂ)
  rw [hV, ← hVcast]
  obtain ⟨q, hq | hq⟩ := n.even_or_odd'
  · subst n
    rw [finWickPairing_const_even,
      centeredGaussianMoment_even]
    push_cast
    rfl
  · subst n
    rw [finWickPairing_const_odd,
      centeredGaussianMoment_odd]
    norm_num

/-- Real part of the complexified power integral is the ordinary real
raw moment. -/
theorem Prop36FullData.integral_fixedTruncationComplexPow_re
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    {B' n : ℕ} (data : Prop36FullData M ρ lam B' n)
    {B s : ℕ} (hBB' : B ≤ B')
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ε : ℝ) :
    (∫ ω,
      (fixedTruncationReal
        M ρ lam ε B s modes c ω : ℂ) ^ n).re =
      ∫ ω,
        fixedTruncationReal
          M ρ lam ε B s modes c ω ^ n := by
  change RCLike.re
    (∫ ω,
      (fixedTruncationReal
        M ρ lam ε B s modes c ω : ℂ) ^ n) =
      ∫ ω,
        fixedTruncationReal
          M ρ lam ε B s modes c ω ^ n
  rw [← integral_re
    (data.integrable_fixedTruncationComplexPow
      hBB' modes c ε)]
  apply integral_congr_ae
  filter_upwards with ω
  exact RCLike.re_ofReal_pow
    (fixedTruncationReal
      M ρ lam ε B s modes c ω) n

/-- Fixed-`B` convergence of every ordinary real moment to the
canonical centered Gaussian moment. -/
theorem Prop36.tendsto_fixedTruncationRealMoment
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B n : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Tendsto
      (fun ε =>
        ∫ ω,
          fixedTruncationReal
            M ρ lam ε B s modes c ω ^ n)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (centeredGaussianMoment
        (fixedTruncationGaussianVariance
          hP36 hlam B modes c) n)) := by
  let data := hP36.fullData B n
  have htComplex :=
    data.tendsto_fixedTruncationComplexMoment
      hlam le_rfl modes c
  rw [hP36.fixedTruncationMomentLimit_eq_gaussianMoment
    hlam B n modes c] at htComplex
  have htRe :=
    (Complex.continuous_re.tendsto
      (centeredGaussianMoment
        (fixedTruncationGaussianVariance
          hP36 hlam B modes c) n : ℂ)).comp htComplex
  simpa only [Complex.ofReal_re] using
    htRe.congr'
      (Filter.Eventually.of_forall fun ε =>
        data.integral_fixedTruncationComplexPow_re
          le_rfl modes c ε)

/-- The fixed-truncation scalar is almost-everywhere measurable, as
required for its pushforward law. -/
theorem Prop36.aemeasurable_fixedTruncationReal
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ε : ℝ) :
    AEMeasurable
      (fixedTruncationReal M ρ lam ε B s modes c)
      (volume : Measure M.Ω) := by
  let data := hP36.fullData B 1
  have hComplex :=
    (data.integrable_fixedTruncationComplexPow
      le_rfl modes c ε).aestronglyMeasurable
  have hRe :=
    RCLike.continuous_re.comp_aestronglyMeasurable hComplex
  have heq :
      (fun x =>
        RCLike.re
          ((fixedTruncationReal
            M ρ lam ε B s modes c x : ℂ) ^ 1)) =
        fixedTruncationReal M ρ lam ε B s modes c := by
    funext x
    rw [pow_one]
    change
      ((fixedTruncationReal
        M ρ lam ε B s modes c x : ℂ)).re =
        fixedTruncationReal M ρ lam ε B s modes c x
    exact Complex.ofReal_re _
  rw [← heq]
  exact hRe.aemeasurable

/-- Every finite raw moment of the fixed-truncation scalar exists. -/
theorem Prop36.memLp_fixedTruncationReal
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam)
    (B n : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ε : ℝ) :
    MemLp
      (fixedTruncationReal M ρ lam ε B s modes c)
      n (volume : Measure M.Ω) := by
  have hAE :=
    (hP36.aemeasurable_fixedTruncationReal
      B modes c ε).aestronglyMeasurable
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.cast_zero] using
      memLp_zero_iff_aestronglyMeasurable.mpr hAE
  · apply (integrable_norm_rpow_iff hAE
      (by exact_mod_cast hn) (by simp)).mp
    let data := hP36.fullData B n
    have hnorm :=
      (data.integrable_fixedTruncationComplexPow
        le_rfl modes c ε).norm
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast,
      norm_pow, Complex.norm_real, Real.norm_eq_abs] using hnorm

/-- Pushforward law of one fixed-truncation Cramér--Wold scalar. -/
def fixedTruncationLaw
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (B s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Measure ℝ :=
  Measure.map
    (fixedTruncationReal M ρ lam ε B s modes c)
    (volume : Measure M.Ω)

/-- Fixed-truncation convergence in law, in the characteristic-function
form needed by the final two-limit argument. -/
theorem Prop36.tendsto_fixedTruncationCharFun
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (B : ℕ) {s : ℕ}
    (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Tendsto
      (fun ε =>
        charFun
          (fixedTruncationLaw
            M ρ lam ε B s modes c) 1)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (charFun
        (gaussianReal 0
          (fixedTruncationGaussianVariance
            hP36 hlam B modes c)) 1)) := by
  let μ : ℝ → Measure ℝ :=
    fun ε =>
      fixedTruncationLaw M ρ lam ε B s modes c
  let v : ℝ≥0 :=
    fixedTruncationGaussianVariance
      hP36 hlam B modes c
  have hAE (ε : ℝ) :
      AEMeasurable
        (fixedTruncationReal M ρ lam ε B s modes c)
        (volume : Measure M.Ω) :=
    hP36.aemeasurable_fixedTruncationReal B modes c ε
  letI (ε : ℝ) : IsProbabilityMeasure (μ ε) := by
    dsimp only [μ, fixedTruncationLaw]
    exact Measure.isProbabilityMeasure_map (hAE ε)
  apply tendsto_charFun_one_of_moments_gaussian μ v
  · intro ε n
    apply (memLp_map_measure_iff
      aestronglyMeasurable_id (hAE ε)).2
    simpa only [Function.id_comp] using
      hP36.memLp_fixedTruncationReal B n modes c ε
  · intro n
    have hmom :=
      hP36.tendsto_fixedTruncationRealMoment
        hlam B n modes c
    refine hmom.congr' (Filter.Eventually.of_forall fun ε => ?_)
    dsimp only [μ, fixedTruncationLaw]
    rw [integral_map (hAE ε) (by fun_prop)]

end

end Anderson4D
