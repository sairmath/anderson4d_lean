import Anderson4D.Parametrix.GoodEvent

/-!
# Two-sided parametrix inversion in the bounded-operator algebra

The paper controls two remainders produced by the left and right
parametrix identities.  This file isolates the exact Banach-algebra
argument those estimates feed:

* if `A Q = 1 + Rᵣ` and `Q A = 1 + Rₗ`;
* and both remainder norms are less than one;
* then `A` is a unit, with inverse
  `Q (1 + Rᵣ)⁻¹ = (1 + Rₗ)⁻¹ Q`;
* the inverse differs from `Q` by at most a geometric remainder.

For the Anderson realization one takes `A = 1 - K`.  The actual
kernel-to-operator work in P-err must still construct the bounded
operator `Q` and prove the two displayed identities; no such analytic
input is assumed here.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-! ## Inverting `1 + R` -/

/-- The Neumann inverse of `1 + R`, written using the project's
canonical inverse of `1 - (-R)`. -/
def oneAddNeumannInverse
    (R : H →L[ℂ] H) (hR : ‖R‖ < 1) :
    H →L[ℂ] H :=
  neumannInverse (-R) (by simpa using hR)

omit [Nontrivial H] in
theorem one_add_mul_oneAddNeumannInverse
    (R : H →L[ℂ] H) (hR : ‖R‖ < 1) :
    (1 + R) * oneAddNeumannInverse R hR = 1 := by
  unfold oneAddNeumannInverse neumannInverse
  let u := Units.oneSub (-R) (by simpa using hR)
  have hu : (u : H →L[ℂ] H) = 1 + R := by
    simp [u]
  rw [← hu]
  exact_mod_cast u.mul_inv

omit [Nontrivial H] in
theorem oneAddNeumannInverse_mul_one_add
    (R : H →L[ℂ] H) (hR : ‖R‖ < 1) :
    oneAddNeumannInverse R hR * (1 + R) = 1 := by
  unfold oneAddNeumannInverse neumannInverse
  let u := Units.oneSub (-R) (by simpa using hR)
  have hu : (u : H →L[ℂ] H) = 1 + R := by
    simp [u]
  rw [← hu]
  exact_mod_cast u.inv_mul

theorem norm_oneAddNeumannInverse_le
    (R : H →L[ℂ] H) (hR : ‖R‖ < 1) :
    ‖oneAddNeumannInverse R hR‖ ≤ (1 - ‖R‖)⁻¹ := by
  unfold oneAddNeumannInverse
  simpa using norm_neumannInverse_le (-R) (by simpa using hR)

omit [Nontrivial H] in
theorem oneAddNeumannInverse_sub_one
    (R : H →L[ℂ] H) (hR : ‖R‖ < 1) :
    oneAddNeumannInverse R hR - 1 =
      -(oneAddNeumannInverse R hR * R) := by
  have hmul := oneAddNeumannInverse_mul_one_add R hR
  have hexpand :
      oneAddNeumannInverse R hR +
          oneAddNeumannInverse R hR * R = 1 := by
    simpa only [mul_add, mul_one] using hmul
  rw [← hexpand]
  abel

theorem norm_oneAddNeumannInverse_sub_one_le
    (R : H →L[ℂ] H) (hR : ‖R‖ < 1) :
    ‖oneAddNeumannInverse R hR - 1‖ ≤
      (1 - ‖R‖)⁻¹ * ‖R‖ := by
  rw [oneAddNeumannInverse_sub_one R hR, norm_neg]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_oneAddNeumannInverse_le R hR) (norm_nonneg R))

/-! ## Corrected left and right inverses -/

/-- Right inverse candidate obtained from `A Q = 1 + Rᵣ`. -/
def correctedParametrixRightInverse
    (Q Rright : H →L[ℂ] H) (hRright : ‖Rright‖ < 1) :
    H →L[ℂ] H :=
  Q * oneAddNeumannInverse Rright hRright

/-- Left inverse candidate obtained from `Q A = 1 + Rₗ`. -/
def correctedParametrixLeftInverse
    (Q Rleft : H →L[ℂ] H) (hRleft : ‖Rleft‖ < 1) :
    H →L[ℂ] H :=
  oneAddNeumannInverse Rleft hRleft * Q

omit [Nontrivial H] in
theorem correctedParametrixRightInverse_spec
    (A Q Rright : H →L[ℂ] H)
    (hAQ : A * Q = 1 + Rright)
    (hRright : ‖Rright‖ < 1) :
    A * correctedParametrixRightInverse Q Rright hRright = 1 := by
  unfold correctedParametrixRightInverse
  rw [← mul_assoc, hAQ,
    one_add_mul_oneAddNeumannInverse Rright hRright]

omit [Nontrivial H] in
theorem correctedParametrixLeftInverse_spec
    (A Q Rleft : H →L[ℂ] H)
    (hQA : Q * A = 1 + Rleft)
    (hRleft : ‖Rleft‖ < 1) :
    correctedParametrixLeftInverse Q Rleft hRleft * A = 1 := by
  unfold correctedParametrixLeftInverse
  rw [mul_assoc, hQA,
    oneAddNeumannInverse_mul_one_add Rleft hRleft]

omit [Nontrivial H] in
/-- A left and a right inverse of the same operator coincide. -/
theorem correctedParametrixLeftInverse_eq_rightInverse
    (A Q Rleft Rright : H →L[ℂ] H)
    (hAQ : A * Q = 1 + Rright)
    (hQA : Q * A = 1 + Rleft)
    (hRleft : ‖Rleft‖ < 1)
    (hRright : ‖Rright‖ < 1) :
    correctedParametrixLeftInverse Q Rleft hRleft =
      correctedParametrixRightInverse Q Rright hRright := by
  let L := correctedParametrixLeftInverse Q Rleft hRleft
  let R := correctedParametrixRightInverse Q Rright hRright
  have hleft : L * A = 1 :=
    correctedParametrixLeftInverse_spec A Q Rleft hQA hRleft
  have hright : A * R = 1 :=
    correctedParametrixRightInverse_spec A Q Rright hAQ hRright
  calc
    L = L * 1 := (mul_one L).symm
    _ = L * (A * R) := by rw [hright]
    _ = (L * A) * R := mul_assoc _ _ _
    _ = R := by rw [hleft, one_mul]

omit [Nontrivial H] in
/-- The two error identities and norm bounds produce an honest unit. -/
theorem isUnit_of_twoSidedParametrix
    (A Q Rleft Rright : H →L[ℂ] H)
    (hAQ : A * Q = 1 + Rright)
    (hQA : Q * A = 1 + Rleft)
    (hRleft : ‖Rleft‖ < 1)
    (hRright : ‖Rright‖ < 1) :
    IsUnit A := by
  apply isUnit_iff_exists.mpr
  refine
    ⟨correctedParametrixRightInverse Q Rright hRright,
      correctedParametrixRightInverse_spec
        A Q Rright hAQ hRright, ?_⟩
  rw [← correctedParametrixLeftInverse_eq_rightInverse
    A Q Rleft Rright hAQ hQA hRleft hRright]
  exact correctedParametrixLeftInverse_spec
    A Q Rleft hQA hRleft

omit [Nontrivial H] in
theorem inverseUnit_eq_correctedParametrixRightInverse
    (A Q Rleft Rright : H →L[ℂ] H)
    (hAQ : A * Q = 1 + Rright)
    (hQA : Q * A = 1 + Rleft)
    (hRleft : ‖Rleft‖ < 1)
    (hRright : ‖Rright‖ < 1) :
    ((((isUnit_of_twoSidedParametrix
      A Q Rleft Rright hAQ hQA hRleft hRright).unit)⁻¹ :
        (H →L[ℂ] H)ˣ) : H →L[ℂ] H) =
      correctedParametrixRightInverse Q Rright hRright := by
  let hunit :=
    isUnit_of_twoSidedParametrix
      A Q Rleft Rright hAQ hQA hRleft hRright
  let B := correctedParametrixRightInverse Q Rright hRright
  have hval : (hunit.unit : H →L[ℂ] H) = A :=
    hunit.unit_spec
  have hinv :
      ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) * A = 1 := by
    calc
      ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) * A =
          ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) *
            (hunit.unit : H →L[ℂ] H) := by rw [hval]
      _ = 1 := by exact_mod_cast hunit.unit.inv_mul
  have hright : A * B = 1 :=
    correctedParametrixRightInverse_spec
      A Q Rright hAQ hRright
  calc
    ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) =
        ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) * 1 :=
      (mul_one _).symm
    _ = ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) *
        (A * B) := by rw [hright]
    _ = (((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) *
        A) * B := mul_assoc _ _ _
    _ = B := by rw [hinv, one_mul]

/-! ## Quantitative error -/

omit [Nontrivial H] in
theorem correctedParametrixRightInverse_sub
    (Q Rright : H →L[ℂ] H)
    (hRright : ‖Rright‖ < 1) :
    correctedParametrixRightInverse Q Rright hRright - Q =
      Q * (oneAddNeumannInverse Rright hRright - 1) := by
  unfold correctedParametrixRightInverse
  rw [mul_sub, mul_one]

theorem norm_correctedParametrixRightInverse_sub_le
    (Q Rright : H →L[ℂ] H)
    (hRright : ‖Rright‖ < 1) :
    ‖correctedParametrixRightInverse Q Rright hRright - Q‖ ≤
      ‖Q‖ * ((1 - ‖Rright‖)⁻¹ * ‖Rright‖) := by
  rw [correctedParametrixRightInverse_sub Q Rright hRright]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left
      (norm_oneAddNeumannInverse_sub_one_le Rright hRright)
      (norm_nonneg Q))

theorem norm_correctedParametrixRightInverse_sub_le_two
    (Q Rright : H →L[ℂ] H)
    (hRright : ‖Rright‖ < 1 / 2) :
    ‖correctedParametrixRightInverse Q Rright
        (hRright.trans (by norm_num)) - Q‖ ≤
      2 * ‖Q‖ * ‖Rright‖ := by
  let hR : ‖Rright‖ < 1 := hRright.trans (by norm_num)
  have hden : 0 < 1 - ‖Rright‖ := sub_pos.mpr hR
  have hinv : (1 - ‖Rright‖)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith
  calc
    ‖correctedParametrixRightInverse Q Rright hR - Q‖ ≤
        ‖Q‖ * ((1 - ‖Rright‖)⁻¹ * ‖Rright‖) :=
      norm_correctedParametrixRightInverse_sub_le Q Rright hR
    _ ≤ ‖Q‖ * (2 * ‖Rright‖) := by
      gcongr
    _ = 2 * ‖Q‖ * ‖Rright‖ := by ring

/-! ## Anderson specialization -/

/-- Two-sided parametrix data for the factorized bounded Anderson
operator `1 - G M`. -/
structure AndersonParametrixData
    (G M Q Rleft Rright : H →L[ℂ] H) : Prop where
  rightIdentity : (1 - Kop G M) * Q = 1 + Rright
  leftIdentity : Q * (1 - Kop G M) = 1 + Rleft

omit [Nontrivial H] in
theorem lopInvertible_of_parametrix_remainders
    (G M Q Rleft Rright : H →L[ℂ] H)
    (hdata : AndersonParametrixData G M Q Rleft Rright)
    (hRleft : ‖Rleft‖ < 1)
    (hRright : ‖Rright‖ < 1) :
    LopInvertible G M :=
  isUnit_of_twoSidedParametrix
    (1 - Kop G M) Q Rleft Rright
    hdata.rightIdentity hdata.leftIdentity hRleft hRright

omit [Nontrivial H] in
theorem inverseGreen_eq_correctedParametrix_mul
    (G M Q Rleft Rright : H →L[ℂ] H)
    (hdata : AndersonParametrixData G M Q Rleft Rright)
    (hRleft : ‖Rleft‖ < 1)
    (hRright : ‖Rright‖ < 1) :
    inverseGreen G M
        (lopInvertible_of_parametrix_remainders
          G M Q Rleft Rright hdata hRleft hRright) =
      correctedParametrixRightInverse Q Rright hRright * G := by
  unfold inverseGreen
  have hproof :
      lopInvertible_of_parametrix_remainders
          G M Q Rleft Rright hdata hRleft hRright =
        isUnit_of_twoSidedParametrix
          (1 - Kop G M) Q Rleft Rright
          hdata.rightIdentity hdata.leftIdentity hRleft hRright :=
    Subsingleton.elim _ _
  rw [hproof]
  rw [inverseUnit_eq_correctedParametrixRightInverse
    (1 - Kop G M) Q Rleft Rright
    hdata.rightIdentity hdata.leftIdentity hRleft hRright]

theorem norm_inverseGreen_sub_parametrix_mul_le
    (G M Q Rleft Rright : H →L[ℂ] H)
    (hdata : AndersonParametrixData G M Q Rleft Rright)
    (hRleft : ‖Rleft‖ < 1)
    (hRright : ‖Rright‖ < 1) :
    ‖inverseGreen G M
        (lopInvertible_of_parametrix_remainders
          G M Q Rleft Rright hdata hRleft hRright) -
      Q * G‖ ≤
        ‖Q‖ * ((1 - ‖Rright‖)⁻¹ * ‖Rright‖) * ‖G‖ := by
  rw [inverseGreen_eq_correctedParametrix_mul
    G M Q Rleft Rright hdata hRleft hRright]
  have hfactor :
      correctedParametrixRightInverse Q Rright hRright * G -
          Q * G =
        (correctedParametrixRightInverse Q Rright hRright - Q) * G := by
    rw [sub_mul]
  rw [hfactor]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_correctedParametrixRightInverse_sub_le
        Q Rright hRright) (norm_nonneg G))

theorem norm_inverseGreen_sub_parametrix_mul_le_two
    (G M Q Rleft Rright : H →L[ℂ] H)
    (hdata : AndersonParametrixData G M Q Rleft Rright)
    (hRleft : ‖Rleft‖ < 1 / 2)
    (hRright : ‖Rright‖ < 1 / 2) :
    ‖inverseGreen G M
        (lopInvertible_of_parametrix_remainders
          G M Q Rleft Rright hdata
            (hRleft.trans (by norm_num))
            (hRright.trans (by norm_num))) -
      Q * G‖ ≤
        2 * ‖Q‖ * ‖Rright‖ * ‖G‖ := by
  let hRl : ‖Rleft‖ < 1 := hRleft.trans (by norm_num)
  let hRr : ‖Rright‖ < 1 := hRright.trans (by norm_num)
  rw [inverseGreen_eq_correctedParametrix_mul
    G M Q Rleft Rright hdata hRl hRr]
  have hfactor :
      correctedParametrixRightInverse Q Rright hRr * G -
          Q * G =
        (correctedParametrixRightInverse Q Rright hRr - Q) * G := by
    rw [sub_mul]
  rw [hfactor]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_correctedParametrixRightInverse_sub_le_two
        Q Rright hRright) (norm_nonneg G))

/-! ## Random good event and Chebyshev estimate -/

/-- The paper-shaped good event: both left and right remainder norms
are smaller than one half. -/
def twoSidedParametrixGoodEvent
    {Ω : Type*}
    (Rleft Rright : Ω → H →L[ℂ] H) : Set Ω :=
  {ω | ‖Rleft ω‖ < 1 / 2 ∧ ‖Rright ω‖ < 1 / 2}

omit [CompleteSpace H] [Nontrivial H] in
theorem compl_twoSidedParametrixGoodEvent
    {Ω : Type*}
    (Rleft Rright : Ω → H →L[ℂ] H) :
    (twoSidedParametrixGoodEvent Rleft Rright)ᶜ =
      operatorBadEvent Rleft (1 / 2) ∪
        operatorBadEvent Rright (1 / 2) := by
  ext ω
  change
    ¬ (‖Rleft ω‖ < 1 / 2 ∧ ‖Rright ω‖ < 1 / 2) ↔
      1 / 2 ≤ ‖Rleft ω‖ ∨ 1 / 2 ≤ ‖Rright ω‖
  constructor
  · intro h
    by_cases hleft : ‖Rleft ω‖ < 1 / 2
    · exact Or.inr (le_of_not_gt fun hright => h ⟨hleft, hright⟩)
    · exact Or.inl (le_of_not_gt hleft)
  · intro h hgood
    rcases h with hleft | hright
    · exact (not_lt_of_ge hleft) hgood.1
    · exact (not_lt_of_ge hright) hgood.2

omit [CompleteSpace H] [Nontrivial H] in
theorem measureReal_compl_twoSidedParametrixGoodEvent_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (Rleft Rright : Ω → H →L[ℂ] H)
    (δleft δright : ℝ)
    (hintLeft : Integrable (fun ω => ‖Rleft ω‖ ^ 2) μ)
    (hintRight : Integrable (fun ω => ‖Rright ω‖ ^ 2) μ)
    (hsecondLeft :
      (∫ ω, ‖Rleft ω‖ ^ 2 ∂μ) ≤ δleft)
    (hsecondRight :
      (∫ ω, ‖Rright ω‖ ^ 2 ∂μ) ≤ δright) :
    μ.real (twoSidedParametrixGoodEvent Rleft Rright)ᶜ ≤
      4 * (δleft + δright) := by
  rw [compl_twoSidedParametrixGoodEvent]
  calc
    μ.real
        (operatorBadEvent Rleft (1 / 2) ∪
          operatorBadEvent Rright (1 / 2)) ≤
        μ.real (operatorBadEvent Rleft (1 / 2)) +
          μ.real (operatorBadEvent Rright (1 / 2)) :=
      measureReal_union_le _ _
    _ ≤ 4 * δleft + 4 * δright :=
      add_le_add
        (measureReal_operatorBadEvent_half_le
          μ Rleft δleft hintLeft hsecondLeft)
        (measureReal_operatorBadEvent_half_le
          μ Rright δright hintRight hsecondRight)
    _ = 4 * (δleft + δright) := by ring

omit [CompleteSpace H] [Nontrivial H] in
/-- First-moment Markov inequality for an operator norm.  This is the
form used by paper (3.32), whose hypotheses control
`𝔼 (‖R‖ + ‖R'‖)` rather than the squares. -/
theorem mul_measureReal_operatorBadEvent_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → H →L[ℂ] H) (r : ℝ)
    (hint : Integrable (fun ω => ‖R ω‖) μ) :
    r * μ.real (operatorBadEvent R r) ≤
      ∫ ω, ‖R ω‖ ∂μ := by
  simpa only [operatorBadEvent] using
    (mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := fun ω => ‖R ω‖)
      (ae_of_all μ fun ω => norm_nonneg (R ω))
      hint r)

omit [CompleteSpace H] [Nontrivial H] in
theorem measureReal_operatorBadEvent_half_le_of_firstMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → H →L[ℂ] H) (δ : ℝ)
    (hint : Integrable (fun ω => ‖R ω‖) μ)
    (hfirst : (∫ ω, ‖R ω‖ ∂μ) ≤ δ) :
    μ.real (operatorBadEvent R (1 / 2)) ≤ 2 * δ := by
  have hmark :=
    mul_measureReal_operatorBadEvent_le μ R (1 / 2)
      hint
  have hnonneg :
      0 ≤ μ.real (operatorBadEvent R (1 / 2)) :=
    measureReal_nonneg
  nlinarith

omit [CompleteSpace H] [Nontrivial H] in
/-- Paper-shaped Chebyshev estimate from the expected sum of the two
remainder norms. -/
theorem measureReal_compl_twoSidedParametrixGoodEvent_le_of_firstMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (Rleft Rright : Ω → H →L[ℂ] H)
    (δleft δright : ℝ)
    (hintLeft : Integrable (fun ω => ‖Rleft ω‖) μ)
    (hintRight : Integrable (fun ω => ‖Rright ω‖) μ)
    (hfirstLeft :
      (∫ ω, ‖Rleft ω‖ ∂μ) ≤ δleft)
    (hfirstRight :
      (∫ ω, ‖Rright ω‖ ∂μ) ≤ δright) :
    μ.real (twoSidedParametrixGoodEvent Rleft Rright)ᶜ ≤
      2 * (δleft + δright) := by
  rw [compl_twoSidedParametrixGoodEvent]
  calc
    μ.real
        (operatorBadEvent Rleft (1 / 2) ∪
          operatorBadEvent Rright (1 / 2)) ≤
        μ.real (operatorBadEvent Rleft (1 / 2)) +
          μ.real (operatorBadEvent Rright (1 / 2)) :=
      measureReal_union_le _ _
    _ ≤ 2 * δleft + 2 * δright :=
      add_le_add
        (measureReal_operatorBadEvent_half_le_of_firstMoment
          μ Rleft δleft hintLeft hfirstLeft)
        (measureReal_operatorBadEvent_half_le_of_firstMoment
          μ Rright δright hintRight hfirstRight)
    _ = 2 * (δleft + δright) := by ring

omit [Nontrivial H] in
theorem lopInvertible_on_twoSidedParametrixGoodEvent
    {Ω : Type*}
    (G M Q Rleft Rright : Ω → H →L[ℂ] H)
    (hdata : ∀ ω,
      AndersonParametrixData
        (G ω) (M ω) (Q ω) (Rleft ω) (Rright ω))
    {ω : Ω}
    (hω : ω ∈ twoSidedParametrixGoodEvent Rleft Rright) :
    LopInvertible (G ω) (M ω) :=
  lopInvertible_of_parametrix_remainders
    (G ω) (M ω) (Q ω) (Rleft ω) (Rright ω)
    (hdata ω) (hω.1.trans (by norm_num))
      (hω.2.trans (by norm_num))

theorem norm_inverseGreen_sub_parametrix_mul_on_goodEvent
    {Ω : Type*}
    (G M Q Rleft Rright : Ω → H →L[ℂ] H)
    (hdata : ∀ ω,
      AndersonParametrixData
        (G ω) (M ω) (Q ω) (Rleft ω) (Rright ω))
    {ω : Ω}
    (hω : ω ∈ twoSidedParametrixGoodEvent Rleft Rright) :
    ‖inverseGreen (G ω) (M ω)
        (lopInvertible_on_twoSidedParametrixGoodEvent
          G M Q Rleft Rright hdata hω) -
      Q ω * G ω‖ ≤
        2 * ‖Q ω‖ * ‖Rright ω‖ * ‖G ω‖ := by
  have hproof :
      lopInvertible_on_twoSidedParametrixGoodEvent
          G M Q Rleft Rright hdata hω =
        lopInvertible_of_parametrix_remainders
          (G ω) (M ω) (Q ω) (Rleft ω) (Rright ω)
          (hdata ω)
          (hω.1.trans (by norm_num))
          (hω.2.trans (by norm_num)) :=
    Subsingleton.elim _ _
  rw [hproof]
  exact norm_inverseGreen_sub_parametrix_mul_le_two
    (G ω) (M ω) (Q ω) (Rleft ω) (Rright ω)
    (hdata ω) hω.1 hω.2

end

end Anderson4D
