import Anderson4D.DetParametrix.Paper42_Moment.R324BracketRegionSplit
import Anderson4D.DetParametrix.Paper42_Moment.R324BracketHeadHarvest

/-!
# The head harvest at both copies: the `⟨α⟩⁻⁴` half of the tail ledger
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The measure on the two innermost physical variables `(w, v)`. -/
def r324TailInnerMeasure (m : ℕ) :
    Measure (T4 × (Fin (2 * m) → T4)) :=
  paperMeasure.prod (Measure.pi fun _ : Fin (2 * m) => paperMeasure)

instance instSFiniteR324TailInnerMeasure (m : ℕ) :
    SFinite (r324TailInnerMeasure m) := by
  unfold r324TailInnerMeasure
  infer_instance

/-- **The three outer peels.**  The physical integral, written with the
three external variables `x, y, z` integrated *innermost*, in that order.
This is the order in which the external characters are harvested. -/
theorem r324Tail_integral_peel {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : R324PhysicalPoint m → E)
    (hf : Integrable f (r324PhysicalMeasure m)) :
    (∫ p, f p ∂(r324PhysicalMeasure m)) =
      ∫ s, ∫ z, ∫ y, ∫ x, f (x, y, z, s)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure
        ∂(r324TailInnerMeasure m) := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure at hf ⊢
  unfold r324TailInnerMeasure
  rw [integral_prod_symm _ hf, integral_prod_symm _ hf.integral_prod_right,
    integral_prod_symm _ hf.integral_prod_right.integral_prod_right]

/-! ## Both head Green edges removed -/

/-- The summed flat core with the head chain edge of **both** copies
deleted.  Both deleted edges are entity independent, so no cancellation
inside `F` is spent; the result depends only on the two tail external
points `y, w` and the internal variables `v`. -/
def r324CMDoubleHeadlessCore
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (F : Finset (MomentContraction m))
    (y w : T4) (v : Fin (2 * m) → T4) : ℝ :=
  ∑ e ∈ F,
    (r324DetHeadless ρ ε m e.1
        (assemble y y fun i => v (leftMomentIndex i)) *
      r324DetHeadless ρ ε m e.2.1
        (assemble w w fun i => v (rightMomentIndex i)) *
      momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v)

/-- **The two-head split of the summed core.**  Both head Green edges
factor out of the entity sum. -/
theorem r324CMFlatCore_eq_heads_mul_doubleHeadless
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (x y z : T4) (s : T4 × (Fin (2 * m) → T4)) :
    r324CMFlatCore ρ ε m F (x, y, z, s) =
      greenFn (x - s.2 (leftMomentIndex ⟨0, hm⟩)) *
        (greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) *
          r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2) := by
  unfold r324CMFlatCore r324CMDoubleHeadlessCore
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _he => ?_
  rw [detIntegrand_assemble_eq_head_mul_headless ρ ε hm e.1 x y
      (fun i => s.2 (leftMomentIndex i)),
    detIntegrand_assemble_eq_head_mul_headless ρ ε hm e.2.1 z s.1
      (fun i => s.2 (rightMomentIndex i))]
  ring

/-! ## Integrability of the character-times-core integrand -/

theorem r324Tail_integrable_charCore
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) (F : Finset (MomentContraction m)) :
    Integrable
      (fun p => r324ExternalChar m α β p *
        ((r324CMFlatCore ρ ε m F p : ℝ) : ℂ))
      (r324PhysicalMeasure m) := by
  have h : Integrable
      (fun p => ∑ e ∈ F,
        r324Flatten
          (deterministicMomentIntegrand ρ ε m α β e.1 e.2.1 e.2.2) p)
      (r324PhysicalMeasure m) :=
    integrable_finsetSum _
      (fun e _ => r324MomentIntegrable_all ρ hε hε1 α β e)
  exact h.congr (Filter.Eventually.of_forall fun p =>
    r324CM_sum_flatten_eq_char_mul_core ρ ε m α β F p)

theorem r324Tail_integrable_absCore
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (F : Finset (MomentContraction m)) :
    Integrable (fun p => |r324CMFlatCore ρ ε m F p|)
      (r324PhysicalMeasure m) := by
  have h := (r324Tail_integrable_charCore ρ hε hε1 0 0 F).norm
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  show ‖r324ExternalChar m 0 0 p * ((r324CMFlatCore ρ ε m F p : ℝ) : ℂ)‖ =
    |r324CMFlatCore ρ ε m F p|
  rw [norm_mul, norm_r324ExternalChar, one_mul, Complex.norm_real,
    Real.norm_eq_abs]

/-! ## The two head Fourier coefficients -/

theorem paperFourthOrderModeDecay_eq_sq (k : Z4) :
    paperFourthOrderModeDecay k =
      paperSecondOrderModeDecay k * paperSecondOrderModeDecay k := by
  unfold paperFourthOrderModeDecay paperSecondOrderModeDecay
  rw [sq, mul_inv]

theorem translatedGreenMode_eq_paper (k : Z4) (z : T4) :
    translatedGreenMode k z =
      charT4 k z * ((paperSecondOrderModeDecay k : ℝ) : ℂ) := by
  rw [translatedGreenMode_eq]
  rfl

/-- The `y`-Fourier coefficient of the double-headless core: the tail
harvest at the left copy, **with the entity sum still inside**. -/
def r324TailBetaCoefficient
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (β : Z4)
    (F : Finset (MomentContraction m))
    (s : T4 × (Fin (2 * m) → T4)) : ℂ :=
  ∫ y, charT4 β y *
      ((r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2 : ℝ) : ℂ)
    ∂paperMeasure

/-- **The head-harvested integral.**  What is left of clause B after the
two head Green edges have been integrated against their characters: the
two head characters now sit at the *internal* anchors
`v (leftMomentIndex i)` and `v (rightMomentIndex i)`, which is where the
external mode `α` enters the internal covariance sum. -/
def r324TailHeadHarvest
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (F : Finset (MomentContraction m)) (i : Fin m) : ℂ :=
  ∫ s, charT4 α (s.2 (leftMomentIndex i)) *
      charT4 (-α) (s.2 (rightMomentIndex i)) *
      charT4 (-β) s.1 * r324TailBetaCoefficient ρ ε m β F s
    ∂(r324TailInnerMeasure m)

/-! ## The three inner integrations -/

theorem r324Tail_inner_x
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m) (α β : Z4)
    (F : Finset (MomentContraction m))
    (y z : T4) (s : T4 × (Fin (2 * m) → T4)) :
    (∫ x, r324ExternalChar m α β (x, y, z, s) *
        ((r324CMFlatCore ρ ε m F (x, y, z, s) : ℝ) : ℂ)
      ∂paperMeasure) =
      (charT4 β y *
          ((r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2 : ℝ) : ℂ)) *
        (translatedGreenMode α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
          (charT4 (-α) z *
            ((greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) : ℝ) : ℂ)) *
          charT4 (-β) s.1) := by
  have hpt : ∀ x : T4,
      r324ExternalChar m α β (x, y, z, s) *
          ((r324CMFlatCore ρ ε m F (x, y, z, s) : ℝ) : ℂ) =
        (charT4 α x *
            ((greenFn (x - s.2 (leftMomentIndex ⟨0, hm⟩)) : ℝ) : ℂ)) *
          ((charT4 β y *
              ((r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2 : ℝ) : ℂ)) *
            (charT4 (-α) z *
              ((greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) : ℝ) : ℂ)) *
            charT4 (-β) s.1) := by
    intro x
    rw [r324CMFlatCore_eq_heads_mul_doubleHeadless ρ ε hm F x y z s]
    unfold r324ExternalChar
    push_cast
    ring
  simp only [hpt]
  rw [integral_mul_const]
  show translatedGreenMode α (s.2 (leftMomentIndex ⟨0, hm⟩)) * _ = _
  ring

theorem r324Tail_inner_xy
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m) (α β : Z4)
    (F : Finset (MomentContraction m))
    (z : T4) (s : T4 × (Fin (2 * m) → T4)) :
    (∫ y, ∫ x, r324ExternalChar m α β (x, y, z, s) *
        ((r324CMFlatCore ρ ε m F (x, y, z, s) : ℝ) : ℂ)
      ∂paperMeasure ∂paperMeasure) =
      r324TailBetaCoefficient ρ ε m β F s *
        (translatedGreenMode α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
          (charT4 (-α) z *
            ((greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) : ℝ) : ℂ)) *
          charT4 (-β) s.1) := by
  simp only [r324Tail_inner_x ρ ε hm α β F _ z s]
  rw [integral_mul_const]
  rfl

theorem r324Tail_inner_xyz
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m) (α β : Z4)
    (F : Finset (MomentContraction m))
    (s : T4 × (Fin (2 * m) → T4)) :
    (∫ z, ∫ y, ∫ x, r324ExternalChar m α β (x, y, z, s) *
        ((r324CMFlatCore ρ ε m F (x, y, z, s) : ℝ) : ℂ)
      ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      ((paperFourthOrderModeDecay α : ℝ) : ℂ) *
        (charT4 α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
          charT4 (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) *
          charT4 (-β) s.1 * r324TailBetaCoefficient ρ ε m β F s) := by
  have hpt : ∀ z : T4,
      (∫ y, ∫ x, r324ExternalChar m α β (x, y, z, s) *
          ((r324CMFlatCore ρ ε m F (x, y, z, s) : ℝ) : ℂ)
        ∂paperMeasure ∂paperMeasure) =
        (charT4 (-α) z *
            ((greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) : ℝ) : ℂ)) *
          (r324TailBetaCoefficient ρ ε m β F s *
            translatedGreenMode α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
            charT4 (-β) s.1) := by
    intro z
    rw [r324Tail_inner_xy ρ ε hm α β F z s]
    ring
  simp only [hpt]
  rw [integral_mul_const]
  show translatedGreenMode (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) * _ = _
  rw [translatedGreenMode_eq_paper, translatedGreenMode_eq_paper,
    paperSecondOrderModeDecay_neg, paperFourthOrderModeDecay_eq_sq]
  push_cast
  ring

/-! ## The exact head harvest -/

/-- **The head harvest, exactly.**  The clause-B left-hand side is the
fourth-order mode decay `⟨α⟩⁻⁴` times the head-harvested integral.  This
is an *identity*, so the remaining decay factors still multiply on: no
estimate has been spent, and the entity sum has never left the
integrand. -/
theorem r324Tail_sum_eq_alphaDecay_mul_headHarvest
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4)
    (F : Finset (MomentContraction m)) :
    (∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e) =
      ((paperFourthOrderModeDecay α : ℝ) : ℂ) *
        r324TailHeadHarvest ρ ε m α β F ⟨0, hm⟩ := by
  rw [r324CM_sum_term_eq_core_fourier ρ hε hε1 α β F,
    r324Tail_integral_peel _ (r324Tail_integrable_charCore ρ hε hε1 α β F)]
  simp only [r324Tail_inner_xyz ρ ε hm α β F]
  rw [integral_const_mul]
  rfl

/-! ## The absolute value side -/

/-- The three inner integrations of the **modulus** of the core: the two
head Green edges have unit paper mass and are nonnegative, so they
disappear. -/
theorem r324Tail_absCore_triple
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (hm : 0 < m)
    (F : Finset (MomentContraction m))
    (s : T4 × (Fin (2 * m) → T4)) :
    (∫ z, ∫ y, ∫ x, |r324CMFlatCore ρ ε m F (x, y, z, s)|
      ∂paperMeasure ∂paperMeasure ∂paperMeasure) =
      ∫ y, |r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2| ∂paperMeasure := by
  have hz : ∀ z : T4,
      (∫ y, ∫ x, |r324CMFlatCore ρ ε m F (x, y, z, s)|
        ∂paperMeasure ∂paperMeasure) =
        greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) *
          ∫ y, |r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2|
            ∂paperMeasure := by
    intro z
    have hx : ∀ y : T4,
        (∫ x, |r324CMFlatCore ρ ε m F (x, y, z, s)| ∂paperMeasure) =
          greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) *
            |r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2| := by
      intro y
      have hpt : ∀ x : T4,
          |r324CMFlatCore ρ ε m F (x, y, z, s)| =
            greenFn (x - s.2 (leftMomentIndex ⟨0, hm⟩)) *
              (greenFn (z - s.2 (rightMomentIndex ⟨0, hm⟩)) *
                |r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2|) := by
        intro x
        rw [r324CMFlatCore_eq_heads_mul_doubleHeadless ρ ε hm F x y z s,
          abs_mul, abs_mul, abs_of_nonneg (greenFn_nonneg _),
          abs_of_nonneg (greenFn_nonneg _)]
      simp only [hpt]
      rw [integral_mul_const, integral_greenFn_sub, one_mul]
    simp only [hx]
    rw [integral_const_mul]
  simp only [hz]
  rw [integral_mul_const, integral_greenFn_sub, one_mul]

theorem r324Tail_integrable_absDouble
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (F : Finset (MomentContraction m)) :
    Integrable
      (fun s => ∫ y, |r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2|
        ∂paperMeasure)
      (r324TailInnerMeasure m) := by
  have h := r324Tail_integrable_absCore ρ hε hε1 (m := m) F
  unfold r324PhysicalMeasure r324PhysicalRestMeasure at h
  unfold r324TailInnerMeasure
  refine (h.integral_prod_right.integral_prod_right.integral_prod_right).congr
    (Filter.Eventually.of_forall fun s => ?_)
  exact r324Tail_absCore_triple ρ ε hm F s

/-- The physical `L¹` norm of the core, with the two head Green edges
integrated out. -/
theorem r324Tail_integral_absCore_eq
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (F : Finset (MomentContraction m)) :
    (∫ p, |r324CMFlatCore ρ ε m F p| ∂(r324PhysicalMeasure m)) =
      ∫ s, ∫ y, |r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2|
        ∂paperMeasure ∂(r324TailInnerMeasure m) := by
  rw [r324Tail_integral_peel _ (r324Tail_integrable_absCore ρ hε hε1 F)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
    r324Tail_absCore_triple ρ ε hm F s)

/-! ## The modulus corollary -/

/-- **The head harvest is bounded by the clause-A carrier.**  Dropping
the three unimodular characters and the `y`-oscillation costs nothing
beyond the triangle inequality. -/
theorem r324Tail_norm_headHarvest_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4)
    (F : Finset (MomentContraction m)) :
    ‖r324TailHeadHarvest ρ ε m α β F ⟨0, hm⟩‖ ≤
      ∫ p, |r324CMFlatCore ρ ε m F p| ∂(r324PhysicalMeasure m) := by
  rw [r324Tail_integral_absCore_eq ρ hε hε1 hm F]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun s => norm_nonneg _)
    (r324Tail_integrable_absDouble ρ hε hε1 hm F)
    (Filter.Eventually.of_forall fun s => ?_)
  have hnorm : ‖charT4 α (s.2 (leftMomentIndex ⟨0, hm⟩)) *
      charT4 (-α) (s.2 (rightMomentIndex ⟨0, hm⟩)) *
      charT4 (-β) s.1 * r324TailBetaCoefficient ρ ε m β F s‖ =
      ‖r324TailBetaCoefficient ρ ε m β F s‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_charT4, norm_charT4,
      norm_charT4, mul_one, mul_one, one_mul]
  refine le_trans (le_of_eq hnorm) ?_
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ‖charT4 β y *
      ((r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2 : ℝ) : ℂ)‖ =
    |r324CMDoubleHeadlessCore ρ ε m F y s.1 s.2|
  rw [norm_mul, norm_charT4, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **The `⟨α⟩⁻⁴` half of the tail ledger, unconditionally.**  Both head
Green edges are entity independent, so both harvests factor out of the
entity sum, yielding exactly the clause-A carrier. -/
theorem r324Tail_norm_sum_le_fourthOrder_alpha
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (hm : 0 < m) (α β : Z4)
    (F : Finset (MomentContraction m)) :
    ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
      paperFourthOrderModeDecay α *
        ∫ p, |r324CMFlatCore ρ ε m F p| ∂(r324PhysicalMeasure m) := by
  rw [r324Tail_sum_eq_alphaDecay_mul_headHarvest ρ hε hε1 hm α β F, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (paperFourthOrderModeDecay_nonneg α)]
  exact mul_le_mul_of_nonneg_left
    (r324Tail_norm_headHarvest_le ρ hε hε1 hm α β F)
    (paperFourthOrderModeDecay_nonneg α)

/-- The clause-A carrier bound, in the `|core|` form. -/
theorem r324Tail_integral_absCore_le
    {ρ : SmoothCutoff} {K : ℝ} (hA : R324CappedDensityLedger ρ K)
    {ε : ℝ} (m : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (hm2 : 2 ≤ m) (hcap : m ≤ truncOrder ε)
    (F : Finset (MomentContraction m)) :
    (∫ p, |r324CMFlatCore ρ ε m F p| ∂(r324PhysicalMeasure m)) ≤
      K ^ m * |Real.log ε| ^ (m - 1) := by
  have h := hA m hε hε1 hlog hm2 hcap F
  refine le_trans (le_of_eq ?_) h
  exact (integral_congr_ae (Filter.Eventually.of_forall fun p =>
    r324CMFlatDensity_eq_abs_core ρ ε m 0 0 F p)).symm

/-- **The `⟨α⟩⁻⁴` ledger.**  Clause B graded by the `α`-endpoint decay
alone, for an arbitrary entity set and every `m ≥ 2`. -/
theorem r324Tail_norm_sum_le_alphaLedger
    {ρ : SmoothCutoff} {K : ℝ} (hA : R324CappedDensityLedger ρ K)
    {ε : ℝ} (m : ℕ) (α β : Z4)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlog : 1 ≤ |Real.log ε|)
    (hm2 : 2 ≤ m) (hcap : m ≤ truncOrder ε)
    (F : Finset (MomentContraction m)) :
    ‖∑ e ∈ F, deterministicMomentContractionTerm ρ ε m α β e‖ ≤
      K ^ m * |Real.log ε| ^ (m - 1) * paperFourthOrderModeDecay α := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm2
  refine le_trans
    (r324Tail_norm_sum_le_fourthOrder_alpha ρ hε hε1 hm α β F) ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right
    (r324Tail_integral_absCore_le hA m hε hε1 hlog hm2 hcap F)
    (paperFourthOrderModeDecay_nonneg α)

end

end Anderson4D
