import Anderson4D.Parametrix.PairingGlobalIntegrability
import Anderson4D.Parametrix.IdentityGradedComparison

/-!
# Global analytic closure for the parametrix identity

The algebraic proof of Proposition 3.4 keeps every use of Fubini in an
explicit fixed-endpoint ledger.  Those ledgers are not extra hypotheses:
after integrating both external endpoints, the random pairing profiles are
jointly integrable.  This file converts that global fact into the
almost-everywhere endpoint statements needed by the identity proof.

The endpoint diagonal remains exceptional, as it must in four dimensions.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

/-- Separating the new head variable from the old internal variables
preserves integrability. -/
theorem integrable_headTailVariables
    (n : ℕ) (f : (Fin (n + 1) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure)) :
    Integrable
      (fun p : T4 × (Fin n → T4) =>
        f (Fin.cons p.1 p.2))
      (paperMeasure.prod
        (Measure.pi fun _ : Fin n =>
          paperMeasure)) := by
  let e := headTailVariablesEquiv n
  let μold :=
    Measure.pi fun _ : Fin (n + 1) =>
      paperMeasure
  let μtail :=
    Measure.pi fun _ : Fin n =>
      paperMeasure
  let μtarget := paperMeasure.prod μtail
  have hp :
      MeasurePreserving e μold μtarget := by
    simpa only [e, headTailVariablesEquiv,
      μold, μtarget, μtail] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => paperMeasure)
        (0 : Fin (n + 1)))
  have htarget :
      Integrable
        (fun p => f (e.symm p)) μtarget := by
    have hiff :=
      hp.integrable_comp_emb
        e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext u
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  convert htarget using 1
  · funext p
    rcases p with ⟨z, v⟩
    exact congrArg f
      (headTailVariablesEquiv_symm_apply n z v).symm

/-- The paper-order case-(3) variables may be rearranged into
`(z,w,remaining)` without changing integrability. -/
theorem integrable_caseThreeVariables
    (q r : ℕ)
    (f : (Fin (2 * (q + 1) + r) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ :
          Fin (2 * (q + 1) + r) =>
            paperMeasure)) :
    Integrable
      (fun p :
          T4 ×
            (T4 × (Fin (2 * q + r) → T4)) =>
        f (caseThreeAmbientInternal
          q r p.1 p.2.1 p.2.2))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure))) := by
  let e := caseThreeVariablesEquiv q r
  let μold :=
    Measure.pi fun _ :
      Fin (2 * (q + 1) + r) => paperMeasure
  let μt :=
    Measure.pi fun _ :
      Fin (2 * q + r) => paperMeasure
  let μtarget :=
    paperMeasure.prod (paperMeasure.prod μt)
  have hp :
      MeasurePreserving e μold μtarget := by
    simpa only [e, μold, μtarget, μt] using
      measurePreserving_caseThreeVariablesEquiv q r
  have htarget :
      Integrable
        (fun p => f (e.symm p)) μtarget := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext u
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  convert htarget using 1
  funext p
  rcases p with ⟨z, w, t⟩
  exact congrArg f
    (caseThreeVariablesEquiv_symm_apply
      q r z w t).symm

/-- The old variables of an actual case-(3) contraction may be rearranged
into the closed-prefix endpoint and the remaining variables. -/
theorem integrable_caseThreeContractionVariables
    (q r : ℕ)
    (f : (Fin (2 * q + 1 + r) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ :
          Fin (2 * q + 1 + r) =>
            paperMeasure)) :
    Integrable
      (fun p :
          T4 × (Fin (2 * q + r) → T4) =>
        f (caseThreeContractionInternal
          q r p.1 p.2))
      (paperMeasure.prod
        (Measure.pi fun _ => paperMeasure)) := by
  let e := caseThreeContractionVariablesEquiv q r
  let μold :=
    Measure.pi fun _ :
      Fin (2 * q + 1 + r) => paperMeasure
  let μt :=
    Measure.pi fun _ :
      Fin (2 * q + r) => paperMeasure
  let μtarget := paperMeasure.prod μt
  have hp :
      MeasurePreserving e μold μtarget := by
    simpa only [e, μold, μtarget, μt] using
      measurePreserving_caseThreeContractionVariablesEquiv
        q r
  have htarget :
      Integrable
        (fun p => f (e.symm p)) μtarget := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext u
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  convert htarget using 1
  funext p
  rcases p with ⟨w, t⟩
  exact congrArg f
    (caseThreeContractionVariablesEquiv_symm_apply
      q r w t).symm

/-- The preceding contraction-variable permutation may be performed under
an additional outer variable. -/
theorem integrable_outer_caseThreeContractionVariables
    (q r : ℕ)
    (f :
      T4 → (Fin (2 * q + 1 + r) → T4) → ℝ)
    (hf :
      Integrable
        (fun p :
            T4 ×
              (Fin (2 * q + 1 + r) → T4) =>
          f p.1 p.2)
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure))) :
    Integrable
      (fun p :
          T4 ×
            (T4 × (Fin (2 * q + r) → T4)) =>
        f p.1
          (caseThreeContractionInternal
            q r p.2.1 p.2.2))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure))) := by
  let e :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl T4)
      (caseThreeContractionVariablesEquiv q r)
  let μold :=
    paperMeasure.prod
      (Measure.pi fun _ :
        Fin (2 * q + 1 + r) => paperMeasure)
  let μt :=
    Measure.pi fun _ :
      Fin (2 * q + r) => paperMeasure
  let μtarget :=
    paperMeasure.prod (paperMeasure.prod μt)
  have hp :
      MeasurePreserving e μold μtarget := by
    exact
      (MeasurePreserving.id paperMeasure).prod
        (measurePreserving_caseThreeContractionVariablesEquiv
          q r)
  have htarget :
      Integrable
        (fun p => f (e.symm p).1 (e.symm p).2)
        μtarget := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p =>
          f (e.symm p).1 (e.symm p).2)
    apply hiff.mp
    convert hf using 1
    funext p
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  convert htarget using 1
  funext p
  rcases p with ⟨z, w, t⟩
  have he :
      e.symm (z, (w, t)) =
        (z, caseThreeContractionInternal
          q r w t) := by
    apply Prod.ext
    · rfl
    · exact
        caseThreeContractionVariablesEquiv_symm_apply
          q r w t
  rw [he]

/-- Fully joint integrability of two three-variable kernels supplies the
six nested conditions used by `integral3_add`. -/
theorem nestedIntegrablePair3_of_joint
    {k : ℕ}
    {left right :
      T4 → T4 → (Fin k → T4) → ℝ}
    (hleft :
      Integrable
        (fun p : T4 × (T4 × (Fin k → T4)) =>
          left p.1 p.2.1 p.2.2)
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure))))
    (hright :
      Integrable
        (fun p : T4 × (T4 × (Fin k → T4)) =>
          right p.1 p.2.1 p.2.2)
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure)))) :
    NestedIntegrablePair3
      paperMeasure paperMeasure
      (Measure.pi fun _ : Fin k => paperMeasure)
      left right := by
  have hleftX := hleft.prod_right_ae
  have hrightX := hright.prod_right_ae
  refine
    { left_inner := ?_,
      right_inner := ?_,
      left_middle := ?_,
      right_middle := ?_,
      left_outer := ?_,
      right_outer := ?_ }
  · filter_upwards [hleftX] with x hx
    exact hx.prod_right_ae
  · filter_upwards [hrightX] with x hx
    exact hx.prod_right_ae
  · filter_upwards [hleftX] with x hx
    exact hx.integral_prod_left
  · filter_upwards [hrightX] with x hx
    exact hx.integral_prod_left
  · have houter := hleft.integral_prod_left
    refine houter.congr ?_
    filter_upwards [hleftX] with x hx
    exact integral_prod _ hx
  · have houter := hright.integral_prod_left
    refine houter.congr ?_
    filter_upwards [hrightX] with x hx
    exact integral_prod _ hx

/-- Joint integrability of a created Wick term follows from the global
integrability of the corresponding head-single random profile. -/
theorem integrable_leftCreationWeightedCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω)
    (hnew :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n (Sum.inl κ))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure)) :
    Integrable
      (fun p : T4 × (Fin n → T4) =>
        leftCreationWeightedCore
          M ρ ε κ x p.1 y p.2 ω)
      (paperMeasure.prod
        (Measure.pi fun _ => paperMeasure)) := by
  have hsplit :=
    integrable_headTailVariables n
      (fun u =>
        randIntegrand M ρ ε
          (wickHeadEquiv n (Sum.inl κ))
          (assemble x y u) ω)
      hnew
  refine hsplit.congr ?_
  filter_upwards with p
  rcases p with ⟨z, v⟩
  have hpoint :=
    headSingleCreationTerm_eq_randIntegrand
      M ρ ε n κ (assemble x y (Fin.cons z v)) ω
  rw [ambientTailTuple_assemble_cons,
    assemble_cons_first_internal, assemble_zero] at hpoint
  exact hpoint.symm

/-- A genuinely joint `(new head, old variables)` integrability statement
discharges all four nested-Fubini fields of the Wick split ledger. -/
theorem leftPairingSplitIntegrability_of_joint
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω)
    (hcreation :
      Integrable
        (fun p : T4 × (Fin n → T4) =>
          leftCreationWeightedCore
            M ρ ε κ x p.1 y p.2 ω)
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure)))
    (hcontraction :
      ∀ j : Fin κ.singles.card,
        Integrable
          (fun p : T4 × (Fin n → T4) =>
            leftRankedContractionWeightedCore
              M ρ ε κ j x p.1 y p.2 ω)
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure))) :
    LeftPairingSplitIntegrability
      M ρ ε n κ x y ω where
  creation_inner := hcreation.prod_right_ae
  contraction_inner := by
    exact Filter.eventually_all.2 fun j =>
      (hcontraction j).prod_right_ae
  creation_outer := hcreation.integral_prod_left
  contraction_outer := fun j =>
    (hcontraction j).integral_prod_left

/-- Each individual Wick-contraction term is jointly integrable in both
endpoints and all old internal variables.  Its deterministic factor is the
head-single profile; the covariance and the Wick polynomial form a bounded
measurable multiplier on a continuous noise sample. -/
theorem integrable_leftRankedContraction_flat
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card)
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    Integrable
      (fun p : PairingHalfPhysicalPoint (n + 1) =>
        (leftRankedContractionWeightedCore
          M ρ ε κ j p.1 (p.2.2 0) p.2.1
            (Fin.tail p.2.2) ω : ℂ))
      (pairingHalfPhysicalMeasure (n + 1)) := by
  let d : MarkedSingle (Fin n) :=
    rankedSingleEquiv (Fin n) ⟨κ, j⟩
  let created : PartialPairing (Fin (n + 1)) :=
    wickHeadEquiv n (Sum.inl κ)
  let contracted : PartialPairing (Fin (n + 1)) :=
    wickHeadEquiv n (Sum.inr d)
  obtain ⟨Cη, hCη, hη⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  obtain ⟨B, hB, hwick⟩ :=
    M.exists_uniform_norm_wickAt_bound_of_continuous
      ρ hε hε1 contracted ω hξ
  let weight : PairingHalfPhysicalPoint (n + 1) → ℂ :=
    fun p =>
      (ρ.etaEpsT4 ε
          (p.2.2 0 - p.2.2 d.index.succ) : ℂ) *
        pairingHalfWickWeight
          M ρ ε (n + 1) 0 0 contracted ω p
  have hu :
      Measurable fun p : PairingHalfPhysicalPoint (n + 1) =>
        p.2.2 :=
    measurable_snd.comp measurable_snd
  have hu0 :
      Measurable fun p : PairingHalfPhysicalPoint (n + 1) =>
        p.2.2 0 :=
    (measurable_pi_apply 0).comp hu
  have hud :
      Measurable fun p : PairingHalfPhysicalPoint (n + 1) =>
        p.2.2 d.index.succ :=
    (measurable_pi_apply d.index.succ).comp hu
  have hweightMeas : Measurable weight := by
    unfold weight
    exact
      (Complex.measurable_ofReal.comp
        ((ρ.measurable_etaEpsT4 ε).comp
          (hu0.sub hud))).mul
        (M.measurable_pairingHalfWickWeight
          ρ ε (n + 1) 0 0 contracted ω)
  have hweightBound :
      ∀ p : PairingHalfPhysicalPoint (n + 1),
        ‖weight p‖ ≤
          (ε⁻¹ ^ (dim : ℕ) * Cη) * B := by
    intro p
    unfold weight
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ρ.etaEpsT4_nonneg ε _)]
    have hpairingWeight :
        pairingHalfWickWeight
            M ρ ε (n + 1) 0 0 contracted ω p =
          (wickAt M ρ ε contracted
            (assemble p.1 p.2.1 p.2.2) ω : ℂ) := by
      simp only [pairingHalfWickWeight, charT4_zero,
        one_mul, pairingHalfFixedTupleMap]
    rw [hpairingWeight, Complex.norm_real,
      Real.norm_eq_abs]
    exact
      mul_le_mul
        (hη hε hε1 _)
        (hwick _)
        (abs_nonneg _)
        (by positivity)
  have hproduct :=
    (integrable_detIntegrand_flat
      ρ hε hε1 created).mul_bdd
      hweightMeas.aestronglyMeasurable
      (.of_forall hweightBound)
  refine hproduct.congr ?_
  filter_upwards with p
  have htail :
      ambientTailTuple
          (by omega : 1 ≤ n + 1)
          (assemble p.1 p.2.1 p.2.2) =
        assemble (p.2.2 0) p.2.1
          (Fin.tail p.2.2) := by
    conv_lhs =>
      rw [show
        p.2.2 =
          Fin.cons (p.2.2 0) (Fin.tail p.2.2) by
            exact (Fin.cons_self_tail p.2.2).symm]
    exact
      ambientTailTuple_assemble_cons
        n p.1 (p.2.2 0) p.2.1
          (Fin.tail p.2.2)
  have hx1 :
      assemble p.1 p.2.1 p.2.2 1 =
        p.2.2 0 := by
    conv_lhs =>
      rw [show
        p.2.2 =
          Fin.cons (p.2.2 0) (Fin.tail p.2.2) by
            exact (Fin.cons_self_tail p.2.2).symm]
    exact
      assemble_cons_first_internal
        n p.1 (p.2.2 0) p.2.1
          (Fin.tail p.2.2)
  have hdet :=
    detIntegrand_wickHeadEquiv_creation
      ρ ε n κ (assemble p.1 p.2.1 p.2.2)
  rw [assemble_zero, hx1, htail] at hdet
  have hwickEq :=
    wickAt_wickHeadEquiv_contraction
      M ρ ε
        (rankedSingleEquiv (Fin n) ⟨κ, j⟩)
        (assemble p.1 p.2.1 p.2.2) ω
  rw [htail] at hwickEq
  simp only [rankedSingleEquiv_pairing] at hwickEq
  rw [rankedSingleEquiv_idxOf] at hwickEq
  have hcoord :
      p.2.2
          (rankedSingleEquiv
            (Fin n) ⟨κ, j⟩).index.succ =
        (wickAtSingleLabels κ
            (assemble (p.2.2 0) p.2.1
              (Fin.tail p.2.2))).get
          (wickRankIndex κ
            (assemble (p.2.2 0) p.2.1
              (Fin.tail p.2.2)) j) := by
    rw [wickAtSingleLabels_get_wickRankIndex]
    simp only [rankedSingleEquiv_index,
      assemble_varIdx]
    rfl
  have hreal :
      detIntegrand ρ ε (n + 1)
          (wickHeadEquiv n (Sum.inl κ))
          (assemble p.1 p.2.1 p.2.2) *
        (ρ.etaEpsT4 ε
            (p.2.2 0 -
              p.2.2
                (rankedSingleEquiv
                  (Fin n) ⟨κ, j⟩).index.succ) *
          wickAt M ρ ε
            (wickHeadEquiv n
              (Sum.inr
                (rankedSingleEquiv
                  (Fin n) ⟨κ, j⟩)))
            (assemble p.1 p.2.1 p.2.2) ω) =
        leftRankedContractionWeightedCore
          M ρ ε κ j p.1 (p.2.2 0) p.2.1
            (Fin.tail p.2.2) ω := by
    unfold leftRankedContractionWeightedCore
    unfold leftRankedContractionCore
    rw [hdet, hwickEq, hcoord]
    simp only [wickRankIndex_val]
    ring
  unfold weight created contracted d
  have hcomplex := congrArg Complex.ofReal hreal
  simpa only [pairingHalfWickWeight, charT4_zero,
    one_mul, pairingHalfFixedTupleMap,
    Complex.ofReal_mul] using hcomplex

/-! ## Free Green convolution of one pairing profile -/

/-- Drop the first internal variable of an order-`r+1` physical tuple and
use it as the left endpoint of an order-`r` tuple. -/
def pairingDropHeadPhysicalMap (r : ℕ) :
    PairingHalfPhysicalPoint (r + 1) →
      PairingHalfPhysicalPoint r :=
  fun p => (p.2.2 0, (p.2.1, Fin.tail p.2.2))

theorem measurable_pairingDropHeadPhysicalMap (r : ℕ) :
    Measurable (pairingDropHeadPhysicalMap r) := by
  have hu :
      Measurable fun p : PairingHalfPhysicalPoint (r + 1) =>
        p.2.2 :=
    measurable_snd.comp measurable_snd
  have hu0 :
      Measurable fun p : PairingHalfPhysicalPoint (r + 1) =>
        p.2.2 0 :=
    (measurable_pi_apply 0).comp hu
  have htail :
      Measurable fun p : PairingHalfPhysicalPoint (r + 1) =>
        Fin.tail p.2.2 := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply i.succ).comp hu
  exact hu0.prodMk
    ((measurable_fst.comp measurable_snd).prodMk htail)

/-- Before integrating the new head variable, a free Green convolution of
one random pairing profile is jointly integrable in all spatial variables. -/
theorem integrable_green_mul_randIntegrand_flat
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℕ) (τ : PartialPairing (Fin r))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    Integrable
      (fun p : PairingHalfPhysicalPoint (r + 1) =>
        (greenFn (p.1 - p.2.2 0) *
          randIntegrand M ρ ε τ
            (assemble (p.2.2 0) p.2.1
              (Fin.tail p.2.2)) ω : ℂ))
      (pairingHalfPhysicalMeasure (r + 1)) := by
  let created : PartialPairing (Fin (r + 1)) :=
    wickHeadEquiv r (Sum.inl τ)
  obtain ⟨B, hB, hwick⟩ :=
    M.exists_uniform_norm_wickAt_bound_of_continuous
      ρ hε hε1 τ ω hξ
  let weight : PairingHalfPhysicalPoint (r + 1) → ℂ :=
    fun p =>
      pairingHalfWickWeight
        M ρ ε r 0 0 τ ω
          (pairingDropHeadPhysicalMap r p)
  have hweightMeas : Measurable weight := by
    exact
      (M.measurable_pairingHalfWickWeight
        ρ ε r 0 0 τ ω).comp
          (measurable_pairingDropHeadPhysicalMap r)
  have hweightBound :
      ∀ p : PairingHalfPhysicalPoint (r + 1),
        ‖weight p‖ ≤ B := by
    intro p
    have hweightEq :
        weight p =
          (wickAt M ρ ε τ
            (assemble (p.2.2 0) p.2.1
              (Fin.tail p.2.2)) ω : ℂ) := by
      simp only [weight, pairingHalfWickWeight,
        charT4_zero, one_mul,
        pairingDropHeadPhysicalMap,
        pairingHalfFixedTupleMap]
    rw [hweightEq, Complex.norm_real,
      Real.norm_eq_abs]
    exact hwick _
  have hproduct :=
    (integrable_detIntegrand_flat
      ρ hε hε1 created).mul_bdd
      hweightMeas.aestronglyMeasurable
      (.of_forall hweightBound)
  refine hproduct.congr ?_
  filter_upwards with p
  have htail :
      ambientTailTuple
          (by omega : 1 ≤ r + 1)
          (assemble p.1 p.2.1 p.2.2) =
        assemble (p.2.2 0) p.2.1
          (Fin.tail p.2.2) := by
    conv_lhs =>
      rw [show
        p.2.2 =
          Fin.cons (p.2.2 0) (Fin.tail p.2.2) by
            exact (Fin.cons_self_tail p.2.2).symm]
    exact
      ambientTailTuple_assemble_cons
        r p.1 (p.2.2 0) p.2.1
          (Fin.tail p.2.2)
  have hx1 :
      assemble p.1 p.2.1 p.2.2 1 =
        p.2.2 0 := by
    conv_lhs =>
      rw [show
        p.2.2 =
          Fin.cons (p.2.2 0) (Fin.tail p.2.2) by
            exact (Fin.cons_self_tail p.2.2).symm]
    exact
      assemble_cons_first_internal
        r p.1 (p.2.2 0) p.2.1
          (Fin.tail p.2.2)
  have hdet :=
    detIntegrand_wickHeadEquiv_creation
      ρ ε r τ (assemble p.1 p.2.1 p.2.2)
  rw [assemble_zero, hx1, htail] at hdet
  have hreal :
      detIntegrand ρ ε (r + 1)
          (wickHeadEquiv r (Sum.inl τ))
          (assemble p.1 p.2.1 p.2.2) *
        wickAt M ρ ε τ
          (assemble (p.2.2 0) p.2.1
            (Fin.tail p.2.2)) ω =
        greenFn (p.1 - p.2.2 0) *
          randIntegrand M ρ ε τ
            (assemble (p.2.2 0) p.2.1
              (Fin.tail p.2.2)) ω := by
    rw [hdet]
    unfold randIntegrand
    ring
  unfold weight created
  have hcomplex := congrArg Complex.ofReal hreal
  simpa only [pairingHalfWickWeight,
    charT4_zero, one_mul,
    pairingDropHeadPhysicalMap,
    pairingHalfFixedTupleMap,
    Complex.ofReal_mul] using hcomplex

/-- Consequently the free Green convolution of `randRI` is integrable for
almost every endpoint pair. -/
theorem ae_ae_integrable_green_mul_randRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℕ) (τ : PartialPairing (Fin r))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      Integrable
        (fun z : T4 =>
          greenFn (x - z) *
            randRI M ρ lam ε r τ z y ω)
        paperMeasure := by
  have hglobal :=
    integrable_green_mul_randIntegrand_flat
      M ρ hε hε1 r τ ω hξ
  unfold pairingHalfPhysicalMeasure at hglobal
  filter_upwards [hglobal.prod_right_ae] with x hx
  filter_upwards [hx.prod_right_ae] with y hy
  have hreal :
      Integrable
        (fun u : Fin (r + 1) → T4 =>
          greenFn (x - u 0) *
            randIntegrand M ρ ε τ
              (assemble (u 0) y
                (Fin.tail u)) ω)
        (Measure.pi fun _ => paperMeasure) := by
    have hre := hy.re
    convert hre using 1
    funext u
    change
      greenFn (x - u 0) *
          randIntegrand M ρ ε τ
            (assemble (u 0) y (Fin.tail u)) ω =
        Complex.re
          ((greenFn (x - u 0) : ℂ) *
            (randIntegrand M ρ ε τ
              (assemble (u 0) y (Fin.tail u)) ω : ℂ))
    simp
  have hjoint :=
    integrable_headTailVariables r
      (fun u : Fin (r + 1) → T4 =>
        greenFn (x - u 0) *
          randIntegrand M ρ ε τ
            (assemble (u 0) y
              (Fin.tail u)) ω)
      hreal
  have hjoint' :
      Integrable
        (fun p : T4 × (Fin r → T4) =>
          greenFn (x - p.1) *
            randIntegrand M ρ ε τ
              (assemble p.1 y p.2) ω)
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure)) := by
    convert hjoint using 1
    funext p
    simp only [Fin.cons_zero, Fin.tail_cons]
  have houter := hjoint'.integral_prod_left
  have hscaled :=
    houter.const_mul (lamEps lam ε ^ r)
  refine hscaled.congr ?_
  filter_upwards with z
  unfold randRI
  rw [integral_const_mul]
  ring

/-- The contraction terms in the fixed-endpoint Wick split are jointly
integrable for almost every endpoint pair, simultaneously over the finite
set of Wick ranks. -/
theorem ae_ae_integrable_leftRankedContractionWeightedCore
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      ∀ j : Fin κ.singles.card,
        Integrable
          (fun p : T4 × (Fin n → T4) =>
            leftRankedContractionWeightedCore
              M ρ ε κ j x p.1 y p.2 ω)
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure)) := by
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ j : Fin κ.singles.card,
          ∀ᵐ y ∂paperMeasure,
            Integrable
              (fun u : Fin (n + 1) → T4 =>
                (leftRankedContractionWeightedCore
                  M ρ ε κ j x (u 0) y
                    (Fin.tail u) ω : ℂ))
              (Measure.pi fun _ => paperMeasure) := by
    exact Filter.eventually_all.2 fun j => by
      have hglobal :=
        integrable_leftRankedContraction_flat
          M ρ hε hε1 n κ j ω hξ
      unfold pairingHalfPhysicalMeasure at hglobal
      filter_upwards [hglobal.prod_right_ae] with x hx
      exact hx.prod_right_ae
  filter_upwards [hallX] with x hx
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ j : Fin κ.singles.card,
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              (leftRankedContractionWeightedCore
                M ρ ε κ j x (u 0) y
                  (Fin.tail u) ω : ℂ))
            (Measure.pi fun _ => paperMeasure) :=
    Filter.eventually_all.2 fun j => hx j
  filter_upwards [hallY] with y hy
  intro j
  have hreal :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          leftRankedContractionWeightedCore
            M ρ ε κ j x (u 0) y
              (Fin.tail u) ω)
        (Measure.pi fun _ => paperMeasure) := by
    have hre := (hy j).re
    convert hre using 1
    funext u
    exact Complex.ofReal_re _
  have hsplit :=
    integrable_headTailVariables n
      (fun u : Fin (n + 1) → T4 =>
        leftRankedContractionWeightedCore
          M ρ ε κ j x (u 0) y
            (Fin.tail u) ω)
      hreal
  convert hsplit using 1
  funext p
  simp only [Fin.cons_zero, Fin.tail_cons]

/-- The complete Wick-split ledger is automatic for almost every endpoint
pair on every continuous mollified-noise sample. -/
theorem ae_ae_leftPairingSplitIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      LeftPairingSplitIntegrability
        M ρ ε n κ x y ω := by
  have hnew :=
    M.ae_ae_integrable_randIntegrand_all
      ρ hε hε1 (n + 1) ω hξ
  have hcontract :=
    ae_ae_integrable_leftRankedContractionWeightedCore
      M ρ hε hε1 n κ ω hξ
  filter_upwards [hnew, hcontract] with x hx hcx
  filter_upwards [hx, hcx] with y hy hcy
  have hcreatedReal :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n (Sum.inl κ))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure) := by
    have hre :=
      (hy (wickHeadEquiv n (Sum.inl κ))).re
    convert hre using 1
    funext u
    exact Complex.ofReal_re _
  exact
    leftPairingSplitIntegrability_of_joint
      M ρ ε n κ x y ω
      (integrable_leftCreationWeightedCore
        M ρ ε n κ x y ω hcreatedReal)
      hcy

/-- The integrability of one outer noise--pairing convolution follows from
the already constructed Wick-split ledger. -/
theorem integrable_leftPairingOuter_of_split
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω)
    (hint :
      LeftPairingSplitIntegrability
        M ρ ε n κ x y ω) :
    Integrable
      (fun z : T4 =>
        greenFn (x - z) *
          (M.xiEps ρ ε ω z *
            randRI M ρ lam ε n κ z y ω))
      paperMeasure := by
  let μv := Measure.pi fun _ : Fin n => paperMeasure
  let C : T4 → (Fin n → T4) → ℝ :=
    fun z v =>
      leftCreationWeightedCore
        M ρ ε κ x z y v ω
  let R :
      Fin κ.singles.card →
        T4 → (Fin n → T4) → ℝ :=
    fun j z v =>
      leftRankedContractionWeightedCore
        M ρ ε κ j x z y v ω
  have hinner :
      ∀ᵐ z ∂paperMeasure,
        (∫ v : Fin n → T4,
            greenFn (x - z) *
              leftNoisePairingCore
                M ρ ε κ z y v ω ∂μv) =
          (∫ v : Fin n → T4, C z v ∂μv) +
            ∑ j : Fin κ.singles.card,
              ∫ v : Fin n → T4, R j z v ∂μv := by
    filter_upwards
      [hint.creation_inner,
        hint.contraction_inner] with
      z hcreation hcontraction
    have hpoint (v : Fin n → T4) :
        greenFn (x - z) *
            leftNoisePairingCore
              M ρ ε κ z y v ω =
          C z v +
            ∑ j : Fin κ.singles.card,
              R j z v := by
      rw [leftNoisePairingCore_eq_create_add_contract]
      dsimp only [C, R,
        leftCreationWeightedCore,
        leftRankedContractionWeightedCore]
      rw [mul_add, Finset.mul_sum]
    calc
      _ =
          ∫ v : Fin n → T4,
            (C z v +
              ∑ j : Fin κ.singles.card,
                R j z v) ∂μv := by
        apply integral_congr_ae
        filter_upwards with v
        exact hpoint v
      _ =
          (∫ v : Fin n → T4, C z v ∂μv) +
            ∫ v : Fin n → T4,
              ∑ j : Fin κ.singles.card,
                R j z v ∂μv := by
        rw [integral_add]
        · exact hcreation
        · exact integrable_finsetSum _ fun j _ =>
            hcontraction j
      _ = _ := by
        rw [integral_finsetSum]
        intro j _hj
        exact hcontraction j
  have hparts :
      Integrable
        (fun z : T4 =>
          (∫ v : Fin n → T4, C z v ∂μv) +
            ∑ j : Fin κ.singles.card,
              ∫ v : Fin n → T4, R j z v ∂μv)
        paperMeasure :=
    hint.creation_outer.add
      (integrable_finsetSum _ fun j _ =>
        hint.contraction_outer j)
  have hraw :
      Integrable
        (fun z : T4 =>
          ∫ v : Fin n → T4,
            greenFn (x - z) *
              leftNoisePairingCore
                M ρ ε κ z y v ω ∂μv)
        paperMeasure := by
    refine hparts.congr ?_
    filter_upwards [hinner] with z hz
    exact hz.symm
  have hscaled :=
    hraw.const_mul (lamEps lam ε ^ n)
  refine hscaled.congr ?_
  filter_upwards with z
  unfold leftNoisePairingCore randRI
  have hfactor :
      (∫ v : Fin n → T4,
          greenFn (x - z) *
            (M.xiEps ρ ε ω z *
              randIntegrand M ρ ε κ
                (assemble z y v) ω) ∂μv) =
        (greenFn (x - z) *
          M.xiEps ρ ε ω z) *
          ∫ v : Fin n → T4,
            randIntegrand M ρ ε κ
              (assemble z y v) ω ∂μv := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with v
    ring
  rw [hfactor]
  ring

/-- The paper-facing outer noise source ledger holds almost everywhere,
simultaneously over the finite family of old partial pairings. -/
theorem ae_ae_leftOrderSourceIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      LeftOrderSourceIntegrability
        M ρ lam ε n x y ω := by
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ κ : PartialPairing (Fin n),
          ∀ᵐ y ∂paperMeasure,
            LeftPairingSplitIntegrability
              M ρ ε n κ x y ω :=
    Filter.eventually_all.2 fun κ =>
      ae_ae_leftPairingSplitIntegrability
        M ρ hε hε1 n κ ω hξ
  filter_upwards [hallX] with x hx
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ κ : PartialPairing (Fin n),
          LeftPairingSplitIntegrability
            M ρ ε n κ x y ω :=
    Filter.eventually_all.2 fun κ => hx κ
  filter_upwards [hallY] with y hy
  refine ⟨?_⟩
  intro κ
  exact
    integrable_leftPairingOuter_of_split
      M ρ lam ε n κ x y ω (hy κ)

/-! ## Marked contractions and the case-(3) head ledger -/

/-- The weighted contraction core indexed directly by a marked old
single. -/
def leftMarkedContractionWeightedCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (d : MarkedSingle (Fin n))
    (x z y : T4) (v : Fin n → T4)
    (ω : M.Ω) : ℝ :=
  greenFn (x - z) *
    (detIntegrand ρ ε n d.pairing
        (assemble z y v) *
      (ρ.etaEpsT4 ε
          (z - assemble z y v (varIdx d.index)) *
        wickPolynomial
          (fun a b : T4 =>
            ρ.etaEpsT4 ε (a - b))
          (fun a ω' =>
            M.xiEps ρ ε ω' a)
          ((wickAtSingleLabels d.pairing
              (assemble z y v)).eraseIdx
            (d.pairing.singles.sort.idxOf
              d.index)) ω))

/-- Rank indexing and marked-single indexing give the same unintegrated
weighted contraction core. -/
theorem leftRankedContractionWeightedCore_eq_marked
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card)
    (x z y : T4) (v : Fin n → T4)
    (ω : M.Ω) :
    leftRankedContractionWeightedCore
        M ρ ε κ j x z y v ω =
      leftMarkedContractionWeightedCore
        M ρ ε
          (rankedSingleEquiv (Fin n) ⟨κ, j⟩)
          x z y v ω := by
  unfold leftRankedContractionWeightedCore
  unfold leftRankedContractionCore
  unfold leftMarkedContractionWeightedCore
  simp only [rankedSingleEquiv_pairing]
  rw [rankedSingleEquiv_idxOf]
  simp only [rankedSingleEquiv_index,
    wickRankIndex_val]
  rw [wickAtSingleLabels_get_wickRankIndex]

/-- Every directly marked contraction has the same almost-everywhere
joint integrability as its ranked presentation. -/
theorem ae_ae_integrable_leftMarkedContractionWeightedCore
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {n : ℕ} (d : MarkedSingle (Fin n))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      Integrable
        (fun p : T4 × (Fin n → T4) =>
          leftMarkedContractionWeightedCore
            M ρ ε d x p.1 y p.2 ω)
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure)) := by
  let s : RankedSingle (Fin n) :=
    (rankedSingleEquiv (Fin n)).symm d
  have hs :
      rankedSingleEquiv (Fin n) s = d :=
    (rankedSingleEquiv (Fin n)).apply_symm_apply d
  have hrank :=
    ae_ae_integrable_leftRankedContractionWeightedCore
      M ρ hε hε1 n s.1 ω hξ
  filter_upwards [hrank] with x hx
  filter_upwards [hx] with y hy
  refine (hy s.2).congr ?_
  filter_upwards with p
  rw [leftRankedContractionWeightedCore_eq_marked]
  exact congrArg
    (fun d' =>
      leftMarkedContractionWeightedCore
        M ρ ε d' x p.1 y p.2 ω) hs

/-- The head-contraction ledger used in paper case (3) is an automatic
specialization of marked-contraction integrability. -/
theorem ae_ae_caseThreeHeadContractionIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q r : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      CaseThreeHeadContractionIntegrability
        M ρ ε q r x y ω := by
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ (σ :
            {σ :
                PartialPairing
                  (Fin (2 * (q + 1))) //
              IsNonSplit σ})
          (τ : PartialPairing (Fin r)),
          ∀ᵐ y ∂paperMeasure,
            Integrable
              (fun p :
                  T4 ×
                    (Fin (2 * q + 1 + r) → T4) =>
                leftMarkedContractionWeightedCore
                  M ρ ε
                    (caseThreeHeadDeletionData
                      q r σ.1 τ σ.2)
                  x p.1 y p.2 ω)
              (paperMeasure.prod
                (Measure.pi fun _ => paperMeasure)) := by
    exact Filter.eventually_all.2 fun σ =>
      Filter.eventually_all.2 fun τ =>
        ae_ae_integrable_leftMarkedContractionWeightedCore
          M ρ hε hε1
            (caseThreeHeadDeletionData
              q r σ.1 τ σ.2) ω hξ
  filter_upwards [hallX] with x hx
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ (σ :
            {σ :
                PartialPairing
                  (Fin (2 * (q + 1))) //
              IsNonSplit σ})
          (τ : PartialPairing (Fin r)),
          Integrable
            (fun p :
                T4 ×
                  (Fin (2 * q + 1 + r) → T4) =>
              leftMarkedContractionWeightedCore
                M ρ ε
                  (caseThreeHeadDeletionData
                    q r σ.1 τ σ.2)
                x p.1 y p.2 ω)
            (paperMeasure.prod
              (Measure.pi fun _ => paperMeasure)) :=
    Filter.eventually_all.2 fun σ =>
      Filter.eventually_all.2 fun τ => hx σ τ
  filter_upwards [hallY] with y hy
  intro σ τ
  filter_upwards
    [(hy σ τ).prod_right_ae] with z hz
  convert hz using 1
  funext v
  rfl

/-! ## Automatic closure of the case-(3) summation ledger -/

/-- For one fixed non-split prefix and one fixed tail pairing, all three
analytic fields used by the case-(3) summation are automatic almost
everywhere in the external endpoints. -/
theorem ae_ae_caseThreeSummationIntegrability_fixed
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      NestedIntegrablePair3
          paperMeasure paperMeasure
          (Measure.pi fun _ : Fin (2 * q + r) =>
            paperMeasure)
          (fun z w t =>
            caseThreeAmbientCore
              M ρ ε q r σ τ x z w y ω t)
          (fun z w t =>
            caseThreeDiagonalCore
              M ρ ε q r σ τ x z w y ω t) ∧
        Integrable
          (fun v : Fin (2 * (q + 1) + r) → T4 =>
            randIntegrand M ρ ε (appendPairing σ τ)
              (assemble x y v) ω)
          (Measure.pi fun _ => paperMeasure) ∧
        Integrable
          (fun z : T4 =>
            greenFn (x - z) *
              detJMass ρ lam ε (q + 1) σ *
              randRI M ρ lam ε r τ z y ω)
          paperMeasure := by
  have hambient :=
    M.ae_ae_integrable_randIntegrand
      ρ hε hε1 (2 * (q + 1) + r)
        (appendPairing σ τ) ω hξ
  have hjoint :=
    ae_ae_integrable_leftMarkedContractionWeightedCore
      M ρ hε hε1
        (caseThreeHeadDeletionData q r σ τ hσ)
        ω hξ
  have hdelta :=
    ae_ae_integrable_green_mul_randRI
      M ρ lam hε hε1 r τ ω hξ
  filter_upwards [hambient, hjoint, hdelta] with
    x hx hcontractionX hdeltaX
  filter_upwards [hx, hcontractionX, hdeltaX] with
    y hambientComplex hcontraction hfree
  have hambientReal :
      Integrable
        (fun v : Fin (2 * (q + 1) + r) → T4 =>
          randIntegrand M ρ ε (appendPairing σ τ)
            (assemble x y v) ω)
        (Measure.pi fun _ => paperMeasure) := by
    have hre := hambientComplex.re
    convert hre using 1
    funext v
    exact Complex.ofReal_re _
  have hambientJoint :
      Integrable
        (fun p :
            T4 ×
              (T4 × (Fin (2 * q + r) → T4)) =>
          caseThreeAmbientCore
            M ρ ε q r σ τ x p.1 p.2.1 y ω p.2.2)
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure))) := by
    have hperm :=
      integrable_caseThreeVariables q r
        (fun v =>
          randIntegrand M ρ ε (appendPairing σ τ)
            (assemble x y v) ω)
        hambientReal
    convert hperm using 1
    funext p
    rfl
  have hjointCore :
      Integrable
        (fun p :
            T4 ×
              (T4 × (Fin (2 * q + r) → T4)) =>
          greenFn (x - p.1) *
            caseThreeJointCore
              M ρ ε q r σ τ
                p.1 p.2.1 y ω p.2.2)
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure))) := by
    have hperm :=
      integrable_outer_caseThreeContractionVariables
        q r
        (fun z v =>
          leftMarkedContractionWeightedCore
            M ρ ε
              (caseThreeHeadDeletionData q r σ τ hσ)
              x z y v ω)
        hcontraction
    refine hperm.congr ?_
    filter_upwards with p
    change
      caseThreeHeadContractionWeightedCore
          M ρ ε q r σ τ hσ x p.1 y
            (caseThreeContractionInternal
              q r p.2.1 p.2.2) ω =
        greenFn (x - p.1) *
          caseThreeJointCore
            M ρ ε q r σ τ
              p.1 p.2.1 y ω p.2.2
    exact
      caseThreeHeadContractionWeightedCore_reindex
        M ρ ε q r σ τ hσ
          x p.1 p.2.1 y p.2.2 ω
  have hdiagonalJoint :
      Integrable
        (fun p :
            T4 ×
              (T4 × (Fin (2 * q + r) → T4)) =>
          caseThreeDiagonalCore
            M ρ ε q r σ τ x p.1 p.2.1 y ω p.2.2)
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure))) := by
    have hsub := hjointCore.sub hambientJoint
    refine hsub.congr ?_
    filter_upwards with p
    have hpoint :=
      caseThreeJointCore_eq_ambient_add_diagonal
        M ρ ε q r σ τ hσ
          x p.1 p.2.1 y p.2.2 ω
    change
      greenFn (x - p.1) *
            caseThreeJointCore
              M ρ ε q r σ τ
                p.1 p.2.1 y ω p.2.2 -
          caseThreeAmbientCore
            M ρ ε q r σ τ
              x p.1 p.2.1 y ω p.2.2 =
        caseThreeDiagonalCore
          M ρ ε q r σ τ
            x p.1 p.2.1 y ω p.2.2
    rw [hpoint]
    unfold caseThreeAmbientCore caseThreeDiagonalCore
    ring
  have hdelta' :=
    hfree.const_mul
      (detJMass ρ lam ε (q + 1) σ)
  have hdeltaTarget :
      Integrable
        (fun z : T4 =>
          greenFn (x - z) *
            detJMass ρ lam ε (q + 1) σ *
            randRI M ρ lam ε r τ z y ω)
        paperMeasure := by
    refine hdelta'.congr ?_
    filter_upwards with z
    ring
  exact
    ⟨nestedIntegrablePair3_of_joint
        hambientJoint hdiagonalJoint,
      hambientReal, hdeltaTarget⟩

/-- The complete finite case-(3) summation ledger is automatic almost
everywhere in the external endpoints. -/
theorem ae_ae_caseThreeSummationIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q r : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      CaseThreeSummationIntegrability
        M ρ lam ε q r x y ω := by
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ (σ :
            {σ :
                PartialPairing
                  (Fin (2 * (q + 1))) //
              IsNonSplit σ})
          (τ : PartialPairing (Fin r)),
          ∀ᵐ y ∂paperMeasure,
            NestedIntegrablePair3
                paperMeasure paperMeasure
                (Measure.pi fun _ : Fin (2 * q + r) =>
                  paperMeasure)
                (fun z w t =>
                  caseThreeAmbientCore
                    M ρ ε q r σ.1 τ
                      x z w y ω t)
                (fun z w t =>
                  caseThreeDiagonalCore
                    M ρ ε q r σ.1 τ
                      x z w y ω t) ∧
              Integrable
                (fun v :
                    Fin (2 * (q + 1) + r) → T4 =>
                  randIntegrand M ρ ε
                    (appendPairing σ.1 τ)
                    (assemble x y v) ω)
                (Measure.pi fun _ => paperMeasure) ∧
              Integrable
                (fun z : T4 =>
                  greenFn (x - z) *
                    detJMass ρ lam ε (q + 1) σ.1 *
                    randRI M ρ lam ε r τ z y ω)
                paperMeasure := by
    exact Filter.eventually_all.2 fun σ =>
      Filter.eventually_all.2 fun τ =>
        ae_ae_caseThreeSummationIntegrability_fixed
          M ρ lam hε hε1 q r σ.1 τ σ.2 ω hξ
  filter_upwards [hallX] with x hx
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ (σ :
            {σ :
                PartialPairing
                  (Fin (2 * (q + 1))) //
              IsNonSplit σ})
          (τ : PartialPairing (Fin r)),
          NestedIntegrablePair3
                paperMeasure paperMeasure
                (Measure.pi fun _ : Fin (2 * q + r) =>
                  paperMeasure)
                (fun z w t =>
                  caseThreeAmbientCore
                    M ρ ε q r σ.1 τ
                      x z w y ω t)
                (fun z w t =>
                  caseThreeDiagonalCore
                    M ρ ε q r σ.1 τ
                      x z w y ω t) ∧
            Integrable
              (fun v :
                  Fin (2 * (q + 1) + r) → T4 =>
                randIntegrand M ρ ε
                  (appendPairing σ.1 τ)
                  (assemble x y v) ω)
              (Measure.pi fun _ => paperMeasure) ∧
            Integrable
              (fun z : T4 =>
                greenFn (x - z) *
                  detJMass ρ lam ε (q + 1) σ.1 *
                  randRI M ρ lam ε r τ z y ω)
              paperMeasure :=
    Filter.eventually_all.2 fun σ =>
      Filter.eventually_all.2 fun τ =>
        hx σ τ
  filter_upwards [hallY] with y hy
  refine
    { split := ?_,
      ambient := ?_,
      delta := ?_ }
  · intro σ hσ τ
    exact (hy ⟨σ, hσ⟩ τ).1
  · intro σ hσ τ
    exact (hy ⟨σ, hσ⟩ τ).2.1
  · intro σ hσ τ
    exact (hy ⟨σ, hσ⟩ τ).2.2

/-- All minimal-prefix case-(3) ledgers at one old order hold
simultaneously almost everywhere. -/
theorem ae_ae_leftWithPrefixCaseThreeIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      LeftWithPrefixCaseThreeIntegrability
        M ρ lam ε n x y ω := by
  let Q := Finset.Icc 1 ((n + 1) / 2)
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ q : Q,
          ∀ᵐ y ∂paperMeasure,
            CaseThreeHeadContractionIntegrability
                M ρ ε (q.1 - 1) (n + 1 - 2 * q.1)
                  x y ω ∧
              CaseThreeSummationIntegrability
                M ρ lam ε (q.1 - 1)
                  (n + 1 - 2 * q.1) x y ω := by
    exact Filter.eventually_all.2 fun q => by
      have hhead :=
        ae_ae_caseThreeHeadContractionIntegrability
          M ρ hε hε1 (q.1 - 1)
            (n + 1 - 2 * q.1) ω hξ
      have hsum :=
        ae_ae_caseThreeSummationIntegrability
          M ρ lam hε hε1 (q.1 - 1)
            (n + 1 - 2 * q.1) ω hξ
      filter_upwards [hhead, hsum] with x hx hsx
      filter_upwards [hx, hsx] with y hy hsy
      exact ⟨hy, hsy⟩
  filter_upwards [hallX] with x hx
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ q : Q,
          CaseThreeHeadContractionIntegrability
                M ρ ε (q.1 - 1) (n + 1 - 2 * q.1)
                  x y ω ∧
            CaseThreeSummationIntegrability
              M ρ lam ε (q.1 - 1)
                (n + 1 - 2 * q.1) x y ω :=
    Filter.eventually_all.2 fun q => hx q
  filter_upwards [hallY] with y hy
  refine
    { contraction := ?_,
      summation := ?_ }
  · intro q hq
    exact (hy ⟨q, hq⟩).1
  · intro q hq
    exact (hy ⟨q, hq⟩).2

end PartialPairing

end

end Anderson4D
