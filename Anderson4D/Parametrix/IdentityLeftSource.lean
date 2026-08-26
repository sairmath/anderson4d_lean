import Anderson4D.Parametrix.IdentityHeadNoPrefix

/-!
# The left noise source in the parametrix identity

This module integrates the Wick creation--contraction formula against
the new Green edge.  It keeps analytic linearity hypotheses explicit:
the finite pairing and contraction sums are exchanged with Bochner
integrals only under the corresponding termwise integrability facts.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- The unintegrated left-composition source attached to one old
pairing. -/
def leftNoisePairingCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (κ : PartialPairing (Fin n))
    (z y : T4) (v : Fin n → T4)
    (ω : M.Ω) : ℝ :=
  M.xiEps ρ ε ω z *
    randIntegrand M ρ ε κ
      (assemble z y v) ω

/-- The creation summand before multiplication by the outer Green
kernel. -/
def leftCreationCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (κ : PartialPairing (Fin n))
    (z y : T4) (v : Fin n → T4)
    (ω : M.Ω) : ℝ :=
  detIntegrand ρ ε n κ
      (assemble z y v) *
    wickPolynomial
      (fun a b : T4 => ρ.etaEpsT4 ε (a - b))
      (fun a ω' => M.xiEps ρ ε ω' a)
      (z :: wickAtSingleLabels κ
        (assemble z y v)) ω

/-- The contraction summand at an increasing rank before multiplication
by the outer Green kernel. -/
def leftRankedContractionCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card)
    (z y : T4) (v : Fin n → T4)
    (ω : M.Ω) : ℝ :=
  detIntegrand ρ ε n κ
      (assemble z y v) *
    (ρ.etaEpsT4 ε
        (z -
          (wickAtSingleLabels κ
            (assemble z y v)).get
              (wickRankIndex κ
                (assemble z y v) j)) *
      wickPolynomial
        (fun a b : T4 => ρ.etaEpsT4 ε (a - b))
        (fun a ω' => M.xiEps ρ ε ω' a)
        ((wickAtSingleLabels κ
          (assemble z y v)).eraseIdx
            (wickRankIndex κ
              (assemble z y v) j).val) ω)

/-- Increasing-rank transport between the cardinality of the single set
and the definitionally equal Wick-label length. -/
def wickRankEquiv
    {n : ℕ} (κ : PartialPairing (Fin n))
    (xt : Fin (n + 2) → T4) :
    Fin κ.singles.card ≃
      Fin (wickAtSingleLabels κ xt).length :=
  (Fin.castOrderIso
    (wickAtSingleLabels_length κ xt).symm).toEquiv

@[simp]
theorem wickRankEquiv_apply
    {n : ℕ} (κ : PartialPairing (Fin n))
    (xt : Fin (n + 2) → T4)
    (j : Fin κ.singles.card) :
    wickRankEquiv κ xt j =
      wickRankIndex κ xt j := by
  rfl

/-- Pointwise Wick creation--contraction, with the recursive list index
reindexed to the increasing rank of an ambient single. -/
theorem leftNoisePairingCore_eq_create_add_contract
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (κ : PartialPairing (Fin n))
    (z y : T4) (v : Fin n → T4)
    (ω : M.Ω) :
    leftNoisePairingCore M ρ ε κ z y v ω =
      leftCreationCore M ρ ε κ z y v ω +
        ∑ j : Fin κ.singles.card,
          leftRankedContractionCore
            M ρ ε κ j z y v ω := by
  unfold leftNoisePairingCore
  rw [xi_mul_randIntegrand_eq_create_add_contract]
  unfold leftCreationCore
  unfold leftRankedContractionCore
  apply congrArg
    (detIntegrand ρ ε n κ
      (assemble z y v) *
      wickPolynomial
        (fun a b : T4 =>
          ρ.etaEpsT4 ε (a - b))
        (fun a ω' => M.xiEps ρ ε ω' a)
        (z :: wickAtSingleLabels κ
          (assemble z y v)) ω + ·)
  simpa only [wickRankEquiv_apply] using
    ((wickRankEquiv κ (assemble z y v)).sum_comp
      (fun j =>
        detIntegrand ρ ε n κ
            (assemble z y v) *
          (ρ.etaEpsT4 ε
              (z -
                (wickAtSingleLabels κ
                  (assemble z y v)).get j) *
            wickPolynomial
              (fun a b : T4 =>
                ρ.etaEpsT4 ε (a - b))
              (fun a ω' =>
                M.xiEps ρ ε ω' a)
              ((wickAtSingleLabels κ
                (assemble z y v)).eraseIdx j) ω))).symm

/-- The creation core with the new outer Green edge. -/
def leftCreationWeightedCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (κ : PartialPairing (Fin n))
    (x z y : T4) (v : Fin n → T4)
    (ω : M.Ω) : ℝ :=
  greenFn (x - z) *
    leftCreationCore M ρ ε κ z y v ω

/-- A ranked contraction core with the new outer Green edge. -/
def leftRankedContractionWeightedCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    {n : ℕ} (κ : PartialPairing (Fin n))
    (j : Fin κ.singles.card)
    (x z y : T4) (v : Fin n → T4)
    (ω : M.Ω) : ℝ :=
  greenFn (x - z) *
    leftRankedContractionCore
      M ρ ε κ j z y v ω

/-- The actual left-composition source for one old pairing, before the
finite sum over old pairings. -/
def leftNoisePairingContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (n + 1) *
    ∫ z : T4, ∫ v : Fin n → T4,
      greenFn (x - z) *
        leftNoisePairingCore
          M ρ ε κ z y v ω
      ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure

/-- Exact analytic hypotheses for distributing the two nested integrals
over the creation term and the finite contraction sum.

The inner conditions are deliberately almost-everywhere in the outer
variable.  This is both the precise Fubini hypothesis used below and the
correct four-dimensional statement: on exceptional endpoint diagonals a
two-Green product can have the borderline singularity `|x|⁻⁴`. -/
structure LeftPairingSplitIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω) : Prop where
  creation_inner :
    ∀ᵐ z ∂paperMeasure,
      Integrable
        (fun v : Fin n → T4 =>
          leftCreationWeightedCore
            M ρ ε κ x z y v ω)
        (Measure.pi fun _ => paperMeasure)
  contraction_inner :
    ∀ᵐ z ∂paperMeasure, ∀ j : Fin κ.singles.card,
      Integrable
        (fun v : Fin n → T4 =>
          leftRankedContractionWeightedCore
            M ρ ε κ j x z y v ω)
        (Measure.pi fun _ => paperMeasure)
  creation_outer :
    Integrable
      (fun z : T4 =>
        ∫ v : Fin n → T4,
          leftCreationWeightedCore
            M ρ ε κ x z y v ω
          ∂(Measure.pi fun _ => paperMeasure))
      paperMeasure
  contraction_outer :
    ∀ j : Fin κ.singles.card,
      Integrable
        (fun z : T4 =>
          ∫ v : Fin n → T4,
            leftRankedContractionWeightedCore
              M ρ ε κ j x z y v ω
            ∂(Measure.pi fun _ => paperMeasure))
        paperMeasure

/-- The integrated left source for one old pairing is its Wick creation
contribution plus every ranked contraction contribution. -/
theorem leftNoisePairingContribution_eq_create_add_contract
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω)
    (hint :
      LeftPairingSplitIntegrability
        M ρ ε n κ x y ω) :
    leftNoisePairingContribution
        M ρ lam ε n κ x y ω =
      headSingleCreationContribution
          M ρ lam ε n κ x y ω +
        ∑ j : Fin κ.singles.card,
          rankedContractionContribution
            M ρ lam ε n κ j x y ω := by
  let μv :=
    Measure.pi fun _ : Fin n => paperMeasure
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
  have hpoint (z : T4) (v : Fin n → T4) :
      greenFn (x - z) *
          leftNoisePairingCore
            M ρ ε κ z y v ω =
        C z v + ∑ j : Fin κ.singles.card,
          R j z v := by
    rw [leftNoisePairingCore_eq_create_add_contract]
    dsimp only [C, R,
      leftCreationWeightedCore,
      leftRankedContractionWeightedCore]
    rw [mul_add, Finset.mul_sum]
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
      [hint.creation_inner, hint.contraction_inner] with
      z hcreation hcontraction
    calc
      _ =
          ∫ v : Fin n → T4,
            (C z v +
              ∑ j : Fin κ.singles.card,
                R j z v) ∂μv := by
        apply integral_congr_ae
        filter_upwards with v
        exact hpoint z v
      _ =
          (∫ v : Fin n → T4, C z v ∂μv) +
            ∫ v : Fin n → T4,
              ∑ j : Fin κ.singles.card,
                R j z v ∂μv := by
        rw [integral_add]
        · exact hcreation
        · apply integrable_finsetSum
          intro j _hj
          exact hcontraction j
      _ = _ := by
        rw [integral_finsetSum]
        intro j _hj
        exact hcontraction j
  have houter :
      (∫ z : T4,
          ∫ v : Fin n → T4,
            greenFn (x - z) *
              leftNoisePairingCore
                M ρ ε κ z y v ω
            ∂μv ∂paperMeasure) =
        (∫ z : T4, ∫ v : Fin n → T4,
          C z v ∂μv ∂paperMeasure) +
          ∑ j : Fin κ.singles.card,
            ∫ z : T4, ∫ v : Fin n → T4,
              R j z v ∂μv ∂paperMeasure := by
    calc
      _ =
          ∫ z : T4,
            ((∫ v : Fin n → T4,
                C z v ∂μv) +
              ∑ j : Fin κ.singles.card,
                ∫ v : Fin n → T4,
                  R j z v ∂μv)
            ∂paperMeasure := by
        apply integral_congr_ae
        filter_upwards [hinner] with z hz
        exact hz
      _ =
          (∫ z : T4, ∫ v : Fin n → T4,
            C z v ∂μv ∂paperMeasure) +
            ∫ z : T4,
              ∑ j : Fin κ.singles.card,
                ∫ v : Fin n → T4,
                  R j z v ∂μv
              ∂paperMeasure := by
        rw [integral_add]
        · exact hint.creation_outer
        · apply integrable_finsetSum
          intro j _hj
          exact hint.contraction_outer j
      _ = _ := by
        rw [integral_finsetSum]
        intro j _hj
        exact hint.contraction_outer j
  unfold leftNoisePairingContribution
  unfold headSingleCreationContribution
  unfold rankedContractionContribution
  change
    lamEps lam ε ^ (n + 1) * _ =
      lamEps lam ε ^ (n + 1) * _ +
        ∑ j : Fin κ.singles.card,
          lamEps lam ε ^ (n + 1) * _
  rw [houter, mul_add, Finset.mul_sum]
  rfl

/-- The full left noise source at old order `n`, summed over all old
partial pairings. -/
def leftNoiseOrderContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ κ : PartialPairing (Fin n),
    leftNoisePairingContribution
      M ρ lam ε n κ x y ω

/-- Summing the termwise Wick split gives the creation sum plus the
nested ranked-contraction sum. -/
theorem leftNoiseOrderContribution_eq_create_add_contract
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      ∀ κ : PartialPairing (Fin n),
        LeftPairingSplitIntegrability
          M ρ ε n κ x y ω) :
    leftNoiseOrderContribution
        M ρ lam ε n x y ω =
      (∑ κ : PartialPairing (Fin n),
        headSingleCreationContribution
          M ρ lam ε n κ x y ω) +
        ∑ κ : PartialPairing (Fin n),
          ∑ j : Fin κ.singles.card,
            rankedContractionContribution
              M ρ lam ε n κ j x y ω := by
  unfold leftNoiseOrderContribution
  calc
    _ =
        ∑ κ : PartialPairing (Fin n),
          (headSingleCreationContribution
              M ρ lam ε n κ x y ω +
            ∑ j : Fin κ.singles.card,
              rankedContractionContribution
                M ρ lam ε n κ j x y ω) := by
      apply Fintype.sum_congr
      intro κ
      exact
        leftNoisePairingContribution_eq_create_add_contract
          M ρ lam ε n κ x y ω (hint κ)
    _ = _ := Finset.sum_add_distrib

/-- Case (1) is now completely identified inside the full left source;
the remaining nested sum consists precisely of paired-head terms. -/
theorem leftNoiseOrderContribution_eq_headSingle_add_contractions
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hsplit :
      ∀ κ : PartialPairing (Fin n),
        LeftPairingSplitIntegrability
          M ρ ε n κ x y ω)
    (hcreation :
      ∀ κ : PartialPairing (Fin n),
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n (Sum.inl κ))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure)) :
    leftNoiseOrderContribution
        M ρ lam ε n x y ω =
      (∑ κ :
          {κ : PartialPairing (Fin (n + 1)) //
            HeadIsSingle κ},
        randRI M ρ lam ε (n + 1)
          κ.1 x y ω) +
        ∑ κ : PartialPairing (Fin n),
          ∑ j : Fin κ.singles.card,
            rankedContractionContribution
              M ρ lam ε n κ j x y ω := by
  rw [leftNoiseOrderContribution_eq_create_add_contract
    M ρ lam ε n x y ω hsplit]
  rw [sum_headSingleCreationContribution_eq_headSingleRandRI
    M ρ lam ε n x y ω hcreation]

/-- Predicate separating the two paired-head branches after adjoining
the new head to marked-single data. -/
def markedHasHeadPrefix {n : ℕ}
    (d : MarkedSingle (Fin n)) : Prop :=
  HasFullyPairedHeadPrefix
    (wickHeadEquiv n (Sum.inr d))

instance {n : ℕ} :
    DecidablePred
      (markedHasHeadPrefix (n := n)) :=
  fun _ => Classical.dec _

/-- Any finite sum over marked singles splits into the no-prefix and
with-prefix branches. -/
theorem sum_markedSingle_noPrefix_add_withPrefix
    {n : ℕ} {R : Type*} [AddCommMonoid R]
    (f : MarkedSingle (Fin n) → R) :
    (∑ d : MarkedSingle (Fin n), f d) =
      (∑ d :
          {d : MarkedSingle (Fin n) //
            ¬markedHasHeadPrefix d},
        f d.1) +
        ∑ d :
          {d : MarkedSingle (Fin n) //
            markedHasHeadPrefix d},
          f d.1 := by
  let e :=
    Equiv.sumCompl
      (markedHasHeadPrefix (n := n))
  have h := e.sum_comp f
  rw [Fintype.sum_sum_type] at h
  simpa only [e, Equiv.sumCompl_apply_inl,
    Equiv.sumCompl_apply_inr, add_comm] using h.symm

/-- The nested Wick ranks reindex to marked singles and then split into
paper cases (2) and (3), without changing multiplicities. -/
theorem sum_rankedContractionContribution_eq_headBranches
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) :
    (∑ κ : PartialPairing (Fin n),
        ∑ j : Fin κ.singles.card,
          rankedContractionContribution
            M ρ lam ε n κ j x y ω) =
      (∑ d :
          {d : MarkedSingle (Fin n) //
            ¬markedHasHeadPrefix d},
        headPairedContractionContribution
          M ρ lam ε n d.1 x y ω) +
        ∑ d :
          {d : MarkedSingle (Fin n) //
            markedHasHeadPrefix d},
          headPairedContractionContribution
            M ρ lam ε n d.1 x y ω := by
  calc
    _ =
        ∑ κ : PartialPairing (Fin n),
          ∑ j : Fin κ.singles.card,
            headPairedContractionContribution
              M ρ lam ε n
                (rankedSingleEquiv
                  (Fin n) ⟨κ, j⟩)
                x y ω := by
      apply Fintype.sum_congr
      intro κ
      apply Fintype.sum_congr
      intro j
      exact rankedContractionContribution_eq_headPaired
        M ρ lam ε n κ j x y ω
    _ =
        ∑ d : MarkedSingle (Fin n),
          headPairedContractionContribution
            M ρ lam ε n d x y ω :=
      sum_rankedSingle
        (fun d =>
          headPairedContractionContribution
            M ρ lam ε n d x y ω)
    _ = _ :=
      sum_markedSingle_noPrefix_add_withPrefix
        (fun d =>
          headPairedContractionContribution
            M ρ lam ε n d x y ω)

/-- The predicate-only no-prefix subtype is canonically the
`HeadPairedNoPrefix` subtype used by the paper-facing pairing split. -/
def noPrefixMarkedPredicateEquiv (n : ℕ) :
    {d : MarkedSingle (Fin n) //
      ¬markedHasHeadPrefix d} ≃
      {d : MarkedSingle (Fin n) //
        HeadPairedNoPrefix
          (wickHeadEquiv n (Sum.inr d))} where
  toFun d :=
    ⟨d.1,
      ⟨wickHeadEquiv_contraction_not_isSingle
          n d.1,
        d.2⟩⟩
  invFun d := ⟨d.1, d.2.2⟩
  left_inv d := by
    apply Subtype.ext
    rfl
  right_inv d := by
    apply Subtype.ext
    rfl

/-- The whole no-prefix marked branch is the case-(2) random-kernel
sum. -/
theorem sum_markedNoPrefixContribution_eq_randRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      ∀ d :
          {d : MarkedSingle (Fin n) //
            ¬markedHasHeadPrefix d},
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n
                (Sum.inr d.1))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure)) :
    (∑ d :
        {d : MarkedSingle (Fin n) //
          ¬markedHasHeadPrefix d},
      headPairedContractionContribution
        M ρ lam ε n d.1 x y ω) =
      ∑ κ :
          {κ : PartialPairing (Fin (n + 1)) //
            HeadPairedNoPrefix κ},
        randRI M ρ lam ε (n + 1)
          κ.1 x y ω := by
  let e := noPrefixMarkedPredicateEquiv n
  calc
    _ =
        ∑ d :
            {d : MarkedSingle (Fin n) //
              ¬markedHasHeadPrefix d},
          headPairedContractionContribution
            M ρ lam ε n (e d).1 x y ω := by
      apply Fintype.sum_congr
      intro d
      rfl
    _ =
        ∑ d :
            {d : MarkedSingle (Fin n) //
              HeadPairedNoPrefix
                (wickHeadEquiv n
                  (Sum.inr d))},
          headPairedContractionContribution
            M ρ lam ε n d.1 x y ω := by
      exact e.sum_comp
        (fun d =>
          headPairedContractionContribution
            M ρ lam ε n d.1 x y ω)
    _ = _ :=
      sum_headPairedNoPrefixContribution_eq_randRI
        M ρ lam ε n x y ω
        (fun d => by
          have hd :
              (e.symm d).1 = d.1 := rfl
          simpa only [hd] using hint (e.symm d))

/-- Left source after closing cases (1) and (2).  The sole remaining
summand is the with-prefix branch handled by the case-(3) block
factorization. -/
theorem leftNoiseOrderContribution_eq_caseOne_caseTwo_add_caseThreeSource
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hsplit :
      ∀ κ : PartialPairing (Fin n),
        LeftPairingSplitIntegrability
          M ρ ε n κ x y ω)
    (hcreation :
      ∀ κ : PartialPairing (Fin n),
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n (Sum.inl κ))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure))
    (hnoPrefix :
      ∀ d :
          {d : MarkedSingle (Fin n) //
            ¬markedHasHeadPrefix d},
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n
                (Sum.inr d.1))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure)) :
    leftNoiseOrderContribution
        M ρ lam ε n x y ω =
      (∑ κ :
          {κ : PartialPairing (Fin (n + 1)) //
            HeadIsSingle κ},
        randRI M ρ lam ε (n + 1)
          κ.1 x y ω) +
        (∑ κ :
            {κ : PartialPairing (Fin (n + 1)) //
              HeadPairedNoPrefix κ},
          randRI M ρ lam ε (n + 1)
            κ.1 x y ω) +
          ∑ d :
              {d : MarkedSingle (Fin n) //
                markedHasHeadPrefix d},
            headPairedContractionContribution
              M ρ lam ε n d.1 x y ω := by
  rw [leftNoiseOrderContribution_eq_headSingle_add_contractions
    M ρ lam ε n x y ω hsplit hcreation]
  rw [sum_rankedContractionContribution_eq_headBranches]
  rw [sum_markedNoPrefixContribution_eq_randRI
    M ρ lam ε n x y ω hnoPrefix]
  abel

end PartialPairing

end

end Anderson4D
