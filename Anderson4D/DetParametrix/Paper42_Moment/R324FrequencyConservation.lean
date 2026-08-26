import Anderson4D.DetParametrix.Paper42_Moment.R324FourierIntegrability

/-!
# Frequency conservation for R-324 Fourier configurations

The Fourier configuration expansion becomes useful only after recording
the exact conservation law hidden in the physical integral.  We translate
all variables in the left parametrix copy by a common torus element.
Haar invariance fixes the integral, while its character multiplier is
`α + β` plus the signed sum of the assigned covariance modes.  Hence a
nonzero configuration integral satisfies the required conservation law.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Character algebra in the spatial argument -/

@[simp]
theorem charT4_add_argument (k : Z4) (x y : T4) :
    charT4 k (x + y) = charT4 k x * charT4 k y := by
  unfold charT4
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [fourier_apply, fourier_apply, fourier_apply]
  rw [Pi.add_apply, smul_add, AddCircle.toCircle_add]
  rfl

@[simp]
theorem charT4_neg_argument (k : Z4) (x : T4) :
    charT4 k (-x) = charT4 (-k) x := by
  unfold charT4
  apply Finset.prod_congr rfl
  intro i _hi
  rw [fourier_apply, fourier_apply]
  rw [Pi.neg_apply, Pi.neg_apply, smul_neg, neg_smul]

@[simp]
theorem charT4_sub_argument (k : Z4) (x y : T4) :
    charT4 k (x - y) = charT4 k x * charT4 (-k) y := by
  rw [sub_eq_add_neg, charT4_add_argument]
  rw [charT4_neg_argument]

/-! ## Translating exactly the left physical copy -/

/-- Translate the internal coordinates belonging to the left copy and
leave the right-copy coordinates fixed. -/
def r324LeftInternalTranslateMeasurableEquiv
    (m : ℕ) (a : T4) :
    (Fin (2 * m) → T4) ≃ᵐ (Fin (2 * m) → T4) :=
  MeasurableEquiv.piCongrRight fun i =>
    if i.val < m then
      MeasurableEquiv.addRight a
    else
      MeasurableEquiv.refl T4

@[simp]
theorem r324LeftInternalTranslateMeasurableEquiv_apply
    (m : ℕ) (a : T4) (v : Fin (2 * m) → T4)
    (i : Fin (2 * m)) :
    r324LeftInternalTranslateMeasurableEquiv m a v i =
      if i.val < m then v i + a else v i := by
  unfold r324LeftInternalTranslateMeasurableEquiv
  change
    (Equiv.piCongrRight
      (fun i =>
        (if i.val < m then
          MeasurableEquiv.addRight a
        else
          MeasurableEquiv.refl T4).toEquiv) v) i =
      if i.val < m then v i + a else v i
  rw [Equiv.piCongrRight_apply, Pi.map_apply]
  split_ifs <;> rfl

/-- Simultaneously translate `x`, `y`, and all left internal coordinates. -/
def r324TranslateLeftPhysicalMeasurableEquiv
    (m : ℕ) (a : T4) :
    R324PhysicalPoint m ≃ᵐ R324PhysicalPoint m :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.addRight a)
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.addRight a)
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (r324LeftInternalTranslateMeasurableEquiv m a))))

@[simp]
theorem r324TranslateLeftPhysicalMeasurableEquiv_apply
    (m : ℕ) (a : T4) (p : R324PhysicalPoint m) :
    r324TranslateLeftPhysicalMeasurableEquiv m a p =
      (p.1 + a,
        (p.2.1 + a,
          (p.2.2.1,
            (p.2.2.2.1,
              fun i =>
                if i.val < m then p.2.2.2.2 i + a
                else p.2.2.2.2 i)))) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · funext i
          exact
            r324LeftInternalTranslateMeasurableEquiv_apply
              m a p.2.2.2.2 i

/-- The left-copy translation preserves the genuine physical measure. -/
theorem measurePreserving_r324TranslateLeftPhysical
    (m : ℕ) (a : T4) :
    MeasurePreserving
      (r324TranslateLeftPhysicalMeasurableEquiv m a)
      (r324PhysicalMeasure m)
      (r324PhysicalMeasure m) := by
  have hadd :
      MeasurePreserving (fun x : T4 => x + a)
        paperMeasure paperMeasure := by
    rw [paperMeasure_eq_volume]
    exact measurePreserving_add_right (volume : Measure T4) a
  have hpi :
      MeasurePreserving
        (r324LeftInternalTranslateMeasurableEquiv m a)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure)
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure) := by
    have hfun :
        (r324LeftInternalTranslateMeasurableEquiv m a :
          (Fin (2 * m) → T4) → (Fin (2 * m) → T4)) =
          fun v i =>
            if i.val < m then v i + a else v i := by
      funext v i
      exact
        r324LeftInternalTranslateMeasurableEquiv_apply
          m a v i
    rw [hfun]
    exact measurePreserving_pi
      (fun _ : Fin (2 * m) => paperMeasure)
      (fun _ : Fin (2 * m) => paperMeasure)
      (f := fun i x =>
        if i.val < m then x + a else x)
      (fun i => by
        by_cases hi : i.val < m
        · simp only [hi, if_pos]
          exact hadd
        · simp only [hi]
          change MeasurePreserving id paperMeasure paperMeasure
          exact MeasurePreserving.id paperMeasure)
  have hprod :=
    hadd.prod
      (hadd.prod
        ((MeasurePreserving.id paperMeasure).prod
          ((MeasurePreserving.id paperMeasure).prod hpi)))
  have hfun :
      (r324TranslateLeftPhysicalMeasurableEquiv m a :
        R324PhysicalPoint m → R324PhysicalPoint m) =
        Prod.map (fun x : T4 => x + a)
          (Prod.map (fun y : T4 => y + a)
            (Prod.map id
              (Prod.map id
                (r324LeftInternalTranslateMeasurableEquiv m a)))) := by
    funext p
    rfl
  rw [hfun]
  simpa only [r324PhysicalMeasure,
    r324PhysicalRestMeasure] using hprod

/-! ## Translation multipliers of one configuration -/

/-- A renormalized Green skeleton depends only on coordinate
differences. -/
theorem renormalizedGreenSkeleton_add_const
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x : Fin (m + 2) → T4) (a : T4) :
    renormalizedGreenSkeleton κ (fun i => x i + a) =
      renormalizedGreenSkeleton κ x := by
  rw [renormalizedGreenSkeleton_eq_differenceProduct]
  unfold expandedGreenDifferenceProduct
  apply Finset.prod_congr rfl
  intro i _hi
  unfold originalGreenEdge extractedShortcutGreenEdge
  by_cases h : i ∈ extractedRightEdges κ
  · simp only [h, ↓reduceDIte, add_sub_add_right_eq_sub]
  · simp only [h, ↓reduceDIte, sub_zero,
      add_sub_add_right_eq_sub]

/-- Signed contribution of one covariance pair to translation of the
left copy. -/
def SmoothCutoff.r324LeftPairModeContribution
    {m : ℕ}
    (κ : PartialPairing (Fin (2 * m)))
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4)
    (j : Fin (κ.pairSupport.filter (fun i => i < κ i)).card) :
    Z4 :=
  let i := (SmoothCutoff.r324PairFinEquiv κ j).1
  (if i.val < m then q j else 0) -
    (if (κ i).val < m then q j else 0)

/-- Total signed covariance mode carried by the left physical copy. -/
def SmoothCutoff.r324LeftModeSum
    {m : ℕ}
    (κ : PartialPairing (Fin (2 * m)))
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4) :
    Z4 :=
  ∑ j, SmoothCutoff.r324LeftPairModeContribution κ q j

namespace SmoothCutoff

variable (ρ : SmoothCutoff)

/-- Translation multiplier of one enumerated covariance pair. -/
theorem r324PairModeTerm_translateLeft
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4)
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4)
    (j : Fin (κ.pairSupport.filter (fun i => i < κ i)).card)
    (a : T4) :
    ρ.r324PairModeTerm ε κ
        (r324LeftInternalTranslateMeasurableEquiv m a v) j (q j) =
      ρ.r324PairModeTerm ε κ v j (q j) *
        charT4
          (r324LeftPairModeContribution κ q j) a := by
  let i := (r324PairFinEquiv κ j).1
  change
    ρ.r324CovarianceModeTerm ε
        (r324LeftInternalTranslateMeasurableEquiv m a v i -
          r324LeftInternalTranslateMeasurableEquiv m a v (κ i))
        (q j) =
      ρ.r324CovarianceModeTerm ε
          (v i - v (κ i)) (q j) *
        charT4
          ((if i.val < m then q j else 0) -
            (if (κ i).val < m then q j else 0)) a
  by_cases hi : i.val < m <;>
    by_cases hκi : (κ i).val < m
  all_goals
    rw [r324LeftInternalTranslateMeasurableEquiv_apply,
      r324LeftInternalTranslateMeasurableEquiv_apply]
  · simp only [hi, hκi, if_pos, sub_self,
      charT4_zero, mul_one, add_sub_add_right_eq_sub]
  · simp only [hi, hκi, if_pos, if_false,
      sub_zero]
    unfold r324CovarianceModeTerm
    rw [show v i + a - v (κ i) =
      (v i - v (κ i)) + a by abel]
    rw [charT4_add_argument]
    ring
  · simp only [hi, hκi, if_pos, if_false,
      zero_sub]
    unfold r324CovarianceModeTerm
    rw [show v i - (v (κ i) + a) =
      (v i - v (κ i)) - a by abel]
    rw [charT4_sub_argument]
    ring
  · simp only [hi, hκi, if_false, sub_self,
      charT4_zero, mul_one]

/-- Product characters turn the sum of signed pair contributions into
one character. -/
theorem prod_charT4_r324LeftPairModeContribution
    {m : ℕ}
    (κ : PartialPairing (Fin (2 * m)))
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4)
    (a : T4) :
    (∏ j,
      charT4 (r324LeftPairModeContribution κ q j) a) =
      charT4 (r324LeftModeSum κ q) a := by
  classical
  unfold r324LeftModeSum
  induction (Finset.univ :
      Finset
        (Fin
          (κ.pairSupport.filter (fun i => i < κ i)).card)) using
      Finset.induction_on with
  | empty =>
      simp
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        charT4_add, ih]

/-- Translation multiplier of the entire covariance configuration. -/
theorem r324CovarianceFourierConfigurationTerm_translateLeft
    {m : ℕ} (ε : ℝ)
    (κ : PartialPairing (Fin (2 * m)))
    (v : Fin (2 * m) → T4)
    (q :
      Fin (κ.pairSupport.filter (fun i => i < κ i)).card → Z4)
    (a : T4) :
    ρ.r324CovarianceFourierConfigurationTerm ε κ
        (r324LeftInternalTranslateMeasurableEquiv m a v) q =
      ρ.r324CovarianceFourierConfigurationTerm ε κ v q *
        charT4 (r324LeftModeSum κ q) a := by
  unfold r324CovarianceFourierConfigurationTerm
    finSeriesAssignmentTerm
  simp_rw [ρ.r324PairModeTerm_translateLeft ε κ v q]
  rw [Finset.prod_mul_distrib,
    prod_charT4_r324LeftPairModeContribution]

/-! ## Conservation in the integrated configuration -/

theorem momentFourierPhase_translateLeft
    (α β : Z4) (x y z w a : T4) :
    momentFourierPhase α β (x + a) (y + a) z w =
      momentFourierPhase α β x y z w *
        charT4 (α + β) a := by
  unfold momentFourierPhase
  rw [charT4_add_argument, charT4_add_argument,
    charT4_add]
  ring

theorem assemble_r324LeftInternalTranslate_left
    {m : ℕ} (x y a : T4)
    (v : Fin (2 * m) → T4) :
    assemble (x + a) (y + a)
        (fun i =>
          r324LeftInternalTranslateMeasurableEquiv m a v
            (leftMomentIndex i)) =
      fun j =>
        assemble x y
          (fun i => v (leftMomentIndex i)) j + a := by
  have hv :
      (fun i =>
        r324LeftInternalTranslateMeasurableEquiv m a v
          (leftMomentIndex i)) =
        fun i => v (leftMomentIndex i) + a := by
    funext i
    rw [r324LeftInternalTranslateMeasurableEquiv_apply]
    rw [if_pos]
    exact i.isLt
  rw [hv]
  funext j
  unfold assemble
  split_ifs <;> rfl

theorem r324LeftInternalTranslate_right
    {m : ℕ} (a : T4)
    (v : Fin (2 * m) → T4) :
    (fun i =>
      r324LeftInternalTranslateMeasurableEquiv m a v
        (rightMomentIndex i)) =
      fun i => v (rightMomentIndex i) := by
  funext i
  rw [r324LeftInternalTranslateMeasurableEquiv_apply]
  rw [if_neg]
  simp only [rightMomentIndex]
  omega

/-- A translated configuration integrand picks up exactly the character
of the external mode plus the signed left-copy covariance mode. -/
theorem r324Flatten_fullPairingFourierIntegrand_translateLeft
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4)
    (a : T4) (p : R324PhysicalPoint m) :
    r324Flatten
        (ρ.r324FullPairingFourierIntegrand ε α β κ q)
        (r324TranslateLeftPhysicalMeasurableEquiv m a p) =
      r324Flatten
          (ρ.r324FullPairingFourierIntegrand ε α β κ q) p *
        charT4
          ((α + β) + r324LeftModeSum κ.1 q) a := by
  let e := (momentContractionEquivFullPairing m).symm κ
  rw [r324TranslateLeftPhysicalMeasurableEquiv_apply]
  have hleft :
      assemble (p.1 + a) (p.2.1 + a)
          (fun i =>
            if (leftMomentIndex i).val < m then
              p.2.2.2.2 (leftMomentIndex i) + a
            else
              p.2.2.2.2 (leftMomentIndex i)) =
        fun j =>
          assemble p.1 p.2.1
            (fun i => p.2.2.2.2 (leftMomentIndex i)) j + a := by
    have hv :
        (fun i =>
          if (leftMomentIndex i).val < m then
            p.2.2.2.2 (leftMomentIndex i) + a
          else
            p.2.2.2.2 (leftMomentIndex i)) =
          fun i =>
            p.2.2.2.2 (leftMomentIndex i) + a := by
      funext i
      have hlt : (leftMomentIndex i).val < m := i.isLt
      rw [if_pos hlt]
    rw [hv]
    funext j
    unfold assemble
    split_ifs <;> rfl
  have hright :
      (fun i =>
        if (rightMomentIndex i).val < m then
          p.2.2.2.2 (rightMomentIndex i) + a
        else
          p.2.2.2.2 (rightMomentIndex i)) =
        fun i => p.2.2.2.2 (rightMomentIndex i) := by
    funext i
    rw [if_neg]
    simp only [rightMomentIndex]
    omega
  have hv :
      (fun i : Fin (2 * m) =>
        if i.val < m then p.2.2.2.2 i + a
        else p.2.2.2.2 i) =
        r324LeftInternalTranslateMeasurableEquiv
          m a p.2.2.2.2 := by
    funext i
    exact
      (r324LeftInternalTranslateMeasurableEquiv_apply
        m a p.2.2.2.2 i).symm
  unfold r324Flatten r324FullPairingFourierIntegrand
  dsimp only
  rw [momentFourierPhase_translateLeft]
  rw [hleft]
  rw [renormalizedGreenSkeleton_add_const]
  rw [hright, hv]
  rw [ρ.r324CovarianceFourierConfigurationTerm_translateLeft]
  simp only [charT4_add]
  ring

/-- Haar invariance makes a configuration integral an eigenvector of
every left-copy translation. -/
theorem r324FullPairingFourierIntegral_eq_mul_character
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4)
    (a : T4) :
    ρ.r324FullPairingFourierIntegral ε α β κ q =
      ρ.r324FullPairingFourierIntegral ε α β κ q *
        charT4
          ((α + β) + r324LeftModeSum κ.1 q) a := by
  let F : R324PhysicalPoint m → ℂ := fun p =>
    r324Flatten
      (ρ.r324FullPairingFourierIntegrand ε α β κ q) p
  let E := r324TranslateLeftPhysicalMeasurableEquiv m a
  have hp :
      MeasurePreserving E
        (r324PhysicalMeasure m)
        (r324PhysicalMeasure m) :=
    measurePreserving_r324TranslateLeftPhysical m a
  unfold r324FullPairingFourierIntegral
  change
    (∫ p, F p ∂(r324PhysicalMeasure m)) =
      (∫ p, F p ∂(r324PhysicalMeasure m)) *
        charT4
          ((α + β) + r324LeftModeSum κ.1 q) a
  calc
    (∫ p, F p ∂(r324PhysicalMeasure m)) =
        ∫ p, F (E p) ∂(r324PhysicalMeasure m) := by
      exact (hp.integral_comp' F).symm
    _ = ∫ p,
          F p *
            charT4
              ((α + β) + r324LeftModeSum κ.1 q) a
          ∂(r324PhysicalMeasure m) := by
      apply integral_congr_ae
      filter_upwards with p
      exact
        ρ.r324Flatten_fullPairingFourierIntegrand_translateLeft
          ε α β κ q a p
    _ = (∫ p, F p ∂(r324PhysicalMeasure m)) *
          charT4
            ((α + β) + r324LeftModeSum κ.1 q) a := by
      rw [integral_mul_const]

/-- Every nontrivial torus frequency has a point where its character is
not one. -/
theorem exists_charT4_ne_one_of_ne_zero
    (k : Z4) (hk : k ≠ 0) :
    ∃ a : T4, charT4 k a ≠ 1 := by
  by_contra h
  push Not at h
  have hIntegral :
      (∫ a : T4, charT4 k a ∂paperMeasure) =
        ∫ a : T4, charT4 0 a ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards with a
    rw [h a, charT4_zero]
  have hzero :
      (∫ a : T4, charT4 k a ∂paperMeasure) = 0 := by
    rw [integral_charT4_paper, if_neg hk]
  have hvolume :
      (∫ a : T4, charT4 0 a ∂paperMeasure) =
        (((2 * Real.pi) ^ dim : ℝ) : ℂ) := by
    rw [integral_charT4_paper, if_pos rfl]
  have hbad :
      (((2 * Real.pi) ^ dim : ℝ) : ℂ) = 0 := by
    rw [← hvolume, ← hIntegral, hzero]
  exact
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (by positivity :
        0 < (2 * Real.pi) ^ dim))) hbad

/-- A Fourier configuration violating frequency conservation has zero
physical integral. -/
theorem r324FullPairingFourierIntegral_eq_zero_of_frequency_ne
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4)
    (hfrequency :
      (α + β) + r324LeftModeSum κ.1 q ≠ 0) :
    ρ.r324FullPairingFourierIntegral ε α β κ q = 0 := by
  obtain ⟨a, ha⟩ :=
    exists_charT4_ne_one_of_ne_zero
      ((α + β) + r324LeftModeSum κ.1 q) hfrequency
  let I := ρ.r324FullPairingFourierIntegral ε α β κ q
  let c :=
    charT4 ((α + β) + r324LeftModeSum κ.1 q) a
  have hmul : I = I * c := by
    exact
      ρ.r324FullPairingFourierIntegral_eq_mul_character
        ε α β κ q a
  have hfactor : I * (1 - c) = 0 := by
    calc
      I * (1 - c) = I - I * c := by ring
      _ = 0 := sub_eq_zero.mpr hmul
  have hnonzero : (1 : ℂ) - c ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm ha)
  exact (mul_eq_zero.mp hfactor).resolve_right hnonzero

/-- Therefore every nonzero integrated configuration satisfies the exact
left-copy conservation law. -/
theorem r324LeftModeSum_eq_neg_external_of_integral_ne_zero
    {m : ℕ} (ε : ℝ) (α β : Z4)
    (κ :
      {τ : PartialPairing (Fin (2 * m)) // τ.IsFull})
    (q :
      Fin (κ.1.pairSupport.filter (fun i => i < κ.1 i)).card → Z4)
    (hne :
      ρ.r324FullPairingFourierIntegral ε α β κ q ≠ 0) :
    r324LeftModeSum κ.1 q = -(α + β) := by
  by_contra hbad
  apply hne
  apply
    ρ.r324FullPairingFourierIntegral_eq_zero_of_frequency_ne
      ε α β κ q
  intro hzero
  exact hbad (eq_neg_of_add_eq_zero_right hzero)

end SmoothCutoff

end

end Anderson4D
