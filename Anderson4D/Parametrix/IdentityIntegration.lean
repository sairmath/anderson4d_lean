import Anderson4D.Parametrix.IdentityExtraction

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

/-! ## Minimal hypotheses for linearity of three nested totalized integrals -/

/-- The six exact integrability conditions needed to distribute three
nested Bochner integrals over `left + right`.

They are deliberately stated at the nesting levels at which
`MeasureTheory.integral_add` is used:

* both innermost integrands are integrable almost everywhere in `(x,y)`;
* both resulting middle integrands are integrable almost everywhere in `x`;
* both resulting outer integrands are integrable.
-/
structure NestedIntegrablePair3
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μα : Measure α) (μβ : Measure β) (μγ : Measure γ)
    (left right : α → β → γ → ℝ) : Prop where
  left_inner :
    ∀ᵐ x ∂μα, ∀ᵐ y ∂μβ,
      Integrable (left x y) μγ
  right_inner :
    ∀ᵐ x ∂μα, ∀ᵐ y ∂μβ,
      Integrable (right x y) μγ
  left_middle :
    ∀ᵐ x ∂μα,
      Integrable
        (fun y => ∫ z, left x y z ∂μγ) μβ
  right_middle :
    ∀ᵐ x ∂μα,
      Integrable
        (fun y => ∫ z, right x y z ∂μγ) μβ
  left_outer :
    Integrable
      (fun x => ∫ y, ∫ z, left x y z ∂μγ ∂μβ) μα
  right_outer :
    Integrable
      (fun x => ∫ y, ∫ z, right x y z ∂μγ ∂μβ) μα

theorem integral3_add
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μα : Measure α} {μβ : Measure β} {μγ : Measure γ}
    {left right : α → β → γ → ℝ}
    (h :
      NestedIntegrablePair3 μα μβ μγ left right) :
    (∫ x, ∫ y, ∫ z,
        (left x y z + right x y z)
        ∂μγ ∂μβ ∂μα) =
      (∫ x, ∫ y, ∫ z,
        left x y z ∂μγ ∂μβ ∂μα) +
      ∫ x, ∫ y, ∫ z,
        right x y z ∂μγ ∂μβ ∂μα := by
  calc
    (∫ x, ∫ y, ∫ z,
        (left x y z + right x y z)
        ∂μγ ∂μβ ∂μα) =
        ∫ x, ∫ y,
          ((∫ z, left x y z ∂μγ) +
            ∫ z, right x y z ∂μγ)
          ∂μβ ∂μα := by
      apply integral_congr_ae
      filter_upwards [h.left_inner, h.right_inner] with x hleft hright
      apply integral_congr_ae
      filter_upwards [hleft, hright] with y hlefty hrighty
      exact integral_add hlefty hrighty
    _ =
        ∫ x,
          ((∫ y, ∫ z, left x y z ∂μγ ∂μβ) +
            ∫ y, ∫ z, right x y z ∂μγ ∂μβ)
          ∂μα := by
      apply integral_congr_ae
      filter_upwards [h.left_middle, h.right_middle] with
        x hleft hright
      exact integral_add hleft hright
    _ = _ :=
      integral_add h.left_outer h.right_outer

/-! ## Pointwise ambient and diagonal pieces -/

def caseThreeAmbientCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x z w y : T4) (ω : M.Ω)
    (t : Fin (2 * q + r) → T4) : ℝ :=
  randIntegrand M ρ ε
    (appendPairing σ τ)
    (assemble x y
      (caseThreeAmbientInternal q r z w t)) ω

def caseThreeDiagonalCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x z w y : T4) (ω : M.Ω)
    (t : Fin (2 * q + r) → T4) : ℝ :=
  greenFn (x - z) *
    detJintegrand ρ ε (q + 1) σ
      (detJTupleSucc q z w
        (fun i => t (Fin.castAdd r i))) *
    randIntegrand M ρ ε τ
      (setTupleFirst z
        (caseThreeTailTuple q r w y t)) ω

def caseThreeAmbientContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (2 * (q + 1) + r) *
    ∫ z : T4, ∫ w : T4,
      ∫ t : Fin (2 * q + r) → T4,
        caseThreeAmbientCore
          M ρ ε q r σ τ x z w y ω t
        ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure ∂paperMeasure

def caseThreeDiagonalContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (2 * (q + 1) + r) *
    ∫ z : T4, ∫ w : T4,
      ∫ t : Fin (2 * q + r) → T4,
        caseThreeDiagonalCore
          M ρ ε q r σ τ x z w y ω t
        ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure ∂paperMeasure

theorem caseThreeJointContribution_eq_ambient_add_diagonal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x y : T4) (ω : M.Ω)
    (hint :
      NestedIntegrablePair3
        paperMeasure paperMeasure
        (Measure.pi fun _ : Fin (2 * q + r) =>
          paperMeasure)
        (fun z w t =>
          caseThreeAmbientCore
            M ρ ε q r σ τ x z w y ω t)
        (fun z w t =>
          caseThreeDiagonalCore
            M ρ ε q r σ τ x z w y ω t)) :
    caseThreeJointContribution
        M ρ lam ε q r σ τ x y ω =
      caseThreeAmbientContribution
          M ρ lam ε q r σ τ x y ω +
        caseThreeDiagonalContribution
          M ρ lam ε q r σ τ x y ω := by
  let μt :=
    Measure.pi fun _ : Fin (2 * q + r) =>
      paperMeasure
  let ambient : T4 → T4 →
      (Fin (2 * q + r) → T4) → ℝ :=
    fun z w t =>
      caseThreeAmbientCore
        M ρ ε q r σ τ x z w y ω t
  let diagonal : T4 → T4 →
      (Fin (2 * q + r) → T4) → ℝ :=
    fun z w t =>
      caseThreeDiagonalCore
        M ρ ε q r σ τ x z w y ω t
  have hsplit :
      (∫ z : T4, ∫ w : T4,
          ∫ t : Fin (2 * q + r) → T4,
            (ambient z w t + diagonal z w t)
            ∂μt ∂paperMeasure ∂paperMeasure) =
        (∫ z : T4, ∫ w : T4,
          ∫ t : Fin (2 * q + r) → T4,
            ambient z w t
            ∂μt ∂paperMeasure ∂paperMeasure) +
        ∫ z : T4, ∫ w : T4,
          ∫ t : Fin (2 * q + r) → T4,
            diagonal z w t
            ∂μt ∂paperMeasure ∂paperMeasure := by
    exact integral3_add hint
  have hpoint :
      (∫ z : T4, ∫ w : T4,
          greenFn (x - z) *
            (∫ t : Fin (2 * q + r) → T4,
              caseThreeJointCore
                M ρ ε q r σ τ z w y ω t
              ∂μt)
          ∂paperMeasure ∂paperMeasure) =
        ∫ z : T4, ∫ w : T4,
          ∫ t : Fin (2 * q + r) → T4,
            (ambient z w t + diagonal z w t)
            ∂μt ∂paperMeasure ∂paperMeasure := by
    apply integral_congr_ae
    filter_upwards with z
    apply integral_congr_ae
    filter_upwards with w
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    exact
      caseThreeJointCore_eq_ambient_add_diagonal
        M ρ ε q r σ τ hσ x z w y t ω
  unfold caseThreeJointContribution
  unfold caseThreeAmbientContribution
  unfold caseThreeDiagonalContribution
  change
    lamEps lam ε ^ (2 * (q + 1) + r) * _ =
      lamEps lam ε ^ (2 * (q + 1) + r) * _ +
        lamEps lam ε ^ (2 * (q + 1) + r) * _
  rw [hpoint, hsplit]
  ring

theorem setTupleFirst_caseThreeTailTuple
    (q r : ℕ) (z w y : T4)
    (t : Fin (2 * q + r) → T4) :
    setTupleFirst z
        (caseThreeTailTuple q r w y t) =
      assemble z y
        (fun j => t (Fin.natAdd (2 * q) j)) := by
  funext j
  unfold setTupleFirst caseThreeTailTuple
  unfold assemble
  split_ifs <;> rfl

/-- The separated diagonal core without the outer Green factor. -/
def caseThreeDiagonalJointCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (z w y : T4) (ω : M.Ω)
    (t : Fin (2 * q + r) → T4) : ℝ :=
  detJintegrand ρ ε (q + 1) σ
      (detJTupleSucc q z w
        (fun i => t (Fin.castAdd r i))) *
    randIntegrand M ρ ε τ
      (assemble z y
        (fun j => t (Fin.natAdd (2 * q) j))) ω

theorem caseThreeDiagonalCore_eq
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x z w y : T4) (ω : M.Ω)
    (t : Fin (2 * q + r) → T4) :
    caseThreeDiagonalCore
        M ρ ε q r σ τ x z w y ω t =
      greenFn (x - z) *
        caseThreeDiagonalJointCore
          M ρ ε q r σ τ z w y ω t := by
  unfold caseThreeDiagonalCore
  unfold caseThreeDiagonalJointCore
  rw [setTupleFirst_caseThreeTailTuple]
  ring

/-- Finite-product Fubini for the diagonal summand. -/
theorem integral_caseThreeDiagonalJointCore_eq_mul
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (z w y : T4) (ω : M.Ω) :
    (∫ t : Fin (2 * q + r) → T4,
        caseThreeDiagonalJointCore
          M ρ ε q r σ τ z w y ω t
        ∂(Measure.pi fun _ => paperMeasure)) =
      (∫ u : Fin (2 * q) → T4,
          detJintegrand ρ ε (q + 1) σ
            (detJTupleSucc q z w u)
          ∂(Measure.pi fun _ => paperMeasure)) *
        ∫ v : Fin r → T4,
          randIntegrand M ρ ε τ
            (assemble z y v) ω
          ∂(Measure.pi fun _ => paperMeasure) := by
  simpa only [caseThreeDiagonalJointCore] using
    integral_finAdd_mul (2 * q) r
      (fun u =>
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w u))
      (fun v =>
        randIntegrand M ρ ε τ
          (assemble z y v) ω)

/-- The same factorization with the outer Green factor restored. -/
theorem integral_caseThreeDiagonalCore_eq_mul
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x z w y : T4) (ω : M.Ω) :
    (∫ t : Fin (2 * q + r) → T4,
        caseThreeDiagonalCore
          M ρ ε q r σ τ x z w y ω t
        ∂(Measure.pi fun _ => paperMeasure)) =
      greenFn (x - z) *
        ((∫ u : Fin (2 * q) → T4,
            detJintegrand ρ ε (q + 1) σ
              (detJTupleSucc q z w u)
            ∂(Measure.pi fun _ => paperMeasure)) *
          ∫ v : Fin r → T4,
            randIntegrand M ρ ε τ
              (assemble z y v) ω
            ∂(Measure.pi fun _ => paperMeasure)) := by
  simp_rw [caseThreeDiagonalCore_eq]
  rw [integral_const_mul,
    integral_caseThreeDiagonalJointCore_eq_mul]

/-- The joint-coordinate diagonal contribution is exactly the existing
collapsed-delta contribution. -/
theorem caseThreeDiagonalContribution_eq_delta
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) :
    caseThreeDiagonalContribution
        M ρ lam ε q r σ τ x y ω =
      caseThreeDeltaContribution
        M ρ lam ε (q + 1) r σ τ x y ω := by
  unfold caseThreeDiagonalContribution
  simp_rw [integral_caseThreeDiagonalCore_eq_mul]
  let a := lamEps lam ε
  let J : T4 → T4 → ℝ := fun z w =>
    ∫ u : Fin (2 * q) → T4,
      detJintegrand ρ ε (q + 1) σ
        (detJTupleSucc q z w u)
      ∂(Measure.pi fun _ => paperMeasure)
  let R : T4 → ℝ := fun z =>
    ∫ v : Fin r → T4,
      randIntegrand M ρ ε τ
        (assemble z y v) ω
      ∂(Measure.pi fun _ => paperMeasure)
  change
    a ^ (2 * (q + 1) + r) *
        ∫ z, ∫ w,
          greenFn (x - z) * (J z w * R z)
          ∂paperMeasure ∂paperMeasure =
      caseThreeDeltaContribution
        M ρ lam ε (q + 1) r σ τ x y ω
  calc
    a ^ (2 * (q + 1) + r) *
        ∫ z, ∫ w,
          greenFn (x - z) * (J z w * R z)
          ∂paperMeasure ∂paperMeasure =
        ∫ z,
          a ^ (2 * (q + 1) + r) *
            (∫ w,
              greenFn (x - z) * (J z w * R z)
              ∂paperMeasure)
          ∂paperMeasure := by
      rw [integral_const_mul]
    _ =
        ∫ z, ∫ w,
          a ^ (2 * (q + 1) + r) *
            (greenFn (x - z) * (J z w * R z))
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      exact
        (integral_const_mul
          (a ^ (2 * (q + 1) + r))
          (fun w =>
            greenFn (x - z) * (J z w * R z))).symm
    _ = _ := by
      unfold caseThreeDeltaContribution
      simp only [detJ]
      unfold randRI
      apply integral_congr_ae
      filter_upwards with z
      change
        (∫ w,
          a ^ (2 * (q + 1) + r) *
            (greenFn (x - z) * (J z w * R z))
          ∂paperMeasure) =
        greenFn (x - z) *
          (∫ w, a ^ (2 * (q + 1)) * J z w
            ∂paperMeasure) *
          (a ^ r * R z)
      rw [pow_add]
      calc
        (∫ w,
            (a ^ (2 * (q + 1)) * a ^ r) *
              (greenFn (x - z) * (J z w * R z))
            ∂paperMeasure) =
            ∫ w,
              (a ^ (2 * (q + 1)) * J z w) *
                (greenFn (x - z) * (a ^ r * R z))
              ∂paperMeasure := by
          apply integral_congr_ae
          filter_upwards with w
          ring
        _ =
            (∫ w, a ^ (2 * (q + 1)) * J z w
              ∂paperMeasure) *
              (greenFn (x - z) * (a ^ r * R z)) := by
          rw [integral_mul_const]
        _ = _ := by ring

/-- **Integrated case-(3) split, paper (3.18)–(3.19).**  Under exactly
the six nested integrability conditions needed for linearity of the
three iterated Bochner integrals, the raw joint contribution is the
ambient renormalized contribution plus the paper's existing collapsed
delta contribution. -/
theorem caseThreeJointContribution_eq_ambient_add_delta
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x y : T4) (ω : M.Ω)
    (hint :
      NestedIntegrablePair3
        paperMeasure paperMeasure
        (Measure.pi fun _ : Fin (2 * q + r) =>
          paperMeasure)
        (fun z w t =>
          caseThreeAmbientCore
            M ρ ε q r σ τ x z w y ω t)
        (fun z w t =>
          caseThreeDiagonalCore
            M ρ ε q r σ τ x z w y ω t)) :
    caseThreeJointContribution
        M ρ lam ε q r σ τ x y ω =
      caseThreeAmbientContribution
          M ρ lam ε q r σ τ x y ω +
        caseThreeDeltaContribution
          M ρ lam ε (q + 1) r σ τ x y ω := by
  rw [caseThreeJointContribution_eq_ambient_add_diagonal
    M ρ lam ε q r σ τ hσ x y ω hint]
  rw [caseThreeDiagonalContribution_eq_delta]

end PartialPairing

end

end Anderson4D
