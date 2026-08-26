import Anderson4D.Parametrix.IdentityGlobalClosure
import Anderson4D.Parametrix.CoefficientAgreement

/-!
# Almost-everywhere coefficient closure for Proposition 3.4

The global integrability results give endpoint sections in either Fubini
order.  The right-endpoint-first order is the one needed by the strong
induction in the parametrix recurrence: after fixing `y`, the preceding
order is substituted under the `z` integral.

No almost-everywhere quantifiers are commuted abstractly here.  Instead,
the underlying jointly integrable functions are transported by the
measure-preserving permutation `(x,y,v) ↦ (y,x,v)` before Fubini is
applied.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

/-! ## A measure-preserving endpoint permutation -/

/-- Move the middle coordinate of a right-associated product to the
front. -/
def moveMiddleMeasurableEquiv
    (A B C : Type*) [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] :
    A × (B × C) ≃ᵐ B × (A × C) :=
  (MeasurableEquiv.prodAssoc
      (α := A) (β := B) (γ := C)).symm.trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
      (MeasurableEquiv.refl C)).trans
      (MeasurableEquiv.prodAssoc
        (α := B) (β := A) (γ := C)))

theorem measurePreserving_moveMiddleMeasurableEquiv
    {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (τ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving
      (moveMiddleMeasurableEquiv A B C)
      (μ.prod (ν.prod τ))
      (ν.prod (μ.prod τ)) := by
  exact
    (measurePreserving_prodAssoc ν μ τ).comp
      (((Measure.measurePreserving_swap
          (μ := μ) (ν := ν)).prod
        (MeasurePreserving.id τ)).comp
          (measurePreserving_prodAssoc μ ν τ).symm)

theorem integrable_moveMiddle
    {A B C E : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    [NormedAddCommGroup E]
    {μ : Measure A} {ν : Measure B} {τ : Measure C}
    [SFinite μ] [SFinite ν] [SFinite τ]
    (f : A → B → C → E)
    (hf :
      Integrable
        (fun p : A × (B × C) =>
          f p.1 p.2.1 p.2.2)
        (μ.prod (ν.prod τ))) :
    Integrable
      (fun p : B × (A × C) =>
        f p.2.1 p.1 p.2.2)
      (ν.prod (μ.prod τ)) := by
  let e := moveMiddleMeasurableEquiv A B C
  have hp :
      MeasurePreserving e
        (μ.prod (ν.prod τ))
        (ν.prod (μ.prod τ)) :=
    measurePreserving_moveMiddleMeasurableEquiv μ ν τ
  have htarget :
      Integrable
        (fun p : B × (A × C) =>
          f (e.symm p).1 (e.symm p).2.1
            (e.symm p).2.2)
        (ν.prod (μ.prod τ)) := by
    exact hp.symm.integrable_comp_of_integrable hf
  convert htarget using 1
  funext p
  rfl

/-! ## Right-endpoint-first pairing sections -/

/-- The global random-pairing profile gives its internal-variable
integrability with the right endpoint quantified first. -/
theorem ae_ae_integrable_randIntegrand_all_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      ∀ κ : PartialPairing (Fin m),
        Integrable
          (fun v : Fin m → T4 =>
            (randIntegrand M ρ ε κ
              (assemble x y v) ω : ℂ))
          (Measure.pi fun _ : Fin m =>
            paperMeasure) := by
  have hall :
      ∀ κ : PartialPairing (Fin m),
        Integrable
          (fun p : PairingHalfPhysicalPoint m =>
            (randIntegrand M ρ ε κ
              (assemble p.1 p.2.1 p.2.2) ω : ℂ))
          (pairingHalfPhysicalMeasure m) := by
    intro κ
    exact
      M.integrable_randIntegrand_flat
        ρ hε hε1 m κ ω hξ
  have hallSwapped :
      ∀ κ : PartialPairing (Fin m),
        Integrable
          (fun p :
              T4 × (T4 × (Fin m → T4)) =>
            (randIntegrand M ρ ε κ
              (assemble p.2.1 p.1 p.2.2) ω : ℂ))
          (paperMeasure.prod
            (paperMeasure.prod
              (Measure.pi fun _ => paperMeasure))) := by
    intro κ
    apply integrable_moveMiddle
      (fun x y v =>
        (randIntegrand M ρ ε κ
          (assemble x y v) ω : ℂ))
    simpa only [pairingHalfPhysicalMeasure] using
      hall κ
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ κ : PartialPairing (Fin m),
          Integrable
            (fun p : T4 × (Fin m → T4) =>
              (randIntegrand M ρ ε κ
                (assemble p.1 y p.2) ω : ℂ))
            (paperMeasure.prod
              (Measure.pi fun _ => paperMeasure)) :=
    Filter.eventually_all.2 fun κ =>
      (hallSwapped κ).prod_right_ae
  filter_upwards [hallY] with y hy
  exact Filter.eventually_all.2 fun κ =>
    (hy κ).prod_right_ae

/-- Every ranked Wick contraction has the same right-endpoint-first
sections. -/
theorem
    ae_ae_integrable_leftRankedContractionWeightedCore_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      ∀ j : Fin κ.singles.card,
        Integrable
          (fun p : T4 × (Fin n → T4) =>
            leftRankedContractionWeightedCore
              M ρ ε κ j x p.1 y p.2 ω)
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure)) := by
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ j : Fin κ.singles.card,
          ∀ᵐ x ∂paperMeasure,
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
      have hglobal' :
          Integrable
            (fun p :
                T4 ×
                  (T4 × (Fin (n + 1) → T4)) =>
              (leftRankedContractionWeightedCore
                M ρ ε κ j p.1 (p.2.2 0)
                  p.2.1 (Fin.tail p.2.2) ω : ℂ))
            (paperMeasure.prod
              (paperMeasure.prod
                (Measure.pi fun _ => paperMeasure))) := by
        simpa only [pairingHalfPhysicalMeasure] using
          hglobal
      have hswapped :
          Integrable
            (fun p :
                T4 ×
                  (T4 × (Fin (n + 1) → T4)) =>
              (leftRankedContractionWeightedCore
                M ρ ε κ j p.2.1
                  (p.2.2 0) p.1 (Fin.tail p.2.2) ω : ℂ))
            (paperMeasure.prod
              (paperMeasure.prod
                (Measure.pi fun _ => paperMeasure))) := by
        exact
          integrable_moveMiddle
            (A := T4) (B := T4)
            (C := Fin (n + 1) → T4) (E := ℂ)
            (μ := paperMeasure) (ν := paperMeasure)
            (τ := Measure.pi fun _ => paperMeasure)
            (fun x y u =>
              (leftRankedContractionWeightedCore
                M ρ ε κ j x (u 0) y
                  (Fin.tail u) ω : ℂ))
            hglobal'
      filter_upwards [hswapped.prod_right_ae] with y hy
      exact hy.prod_right_ae
  filter_upwards [hallY] with y hy
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ j : Fin κ.singles.card,
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              (leftRankedContractionWeightedCore
                M ρ ε κ j x (u 0) y
                  (Fin.tail u) ω : ℂ))
            (Measure.pi fun _ => paperMeasure) :=
    Filter.eventually_all.2 fun j => hy j
  filter_upwards [hallX] with x hx
  intro j
  have hreal :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          leftRankedContractionWeightedCore
            M ρ ε κ j x (u 0) y
              (Fin.tail u) ω)
        (Measure.pi fun _ => paperMeasure) := by
    have hre := (hx j).re
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

/-- The complete fixed-pairing Wick split is available in the
right-endpoint-first Fubini order. -/
theorem ae_ae_leftPairingSplitIntegrability_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      LeftPairingSplitIntegrability
        M ρ ε n κ x y ω := by
  have hnew :=
    ae_ae_integrable_randIntegrand_all_rightFirst
      M ρ hε hε1 (n + 1) ω hξ
  have hcontract :=
    ae_ae_integrable_leftRankedContractionWeightedCore_rightFirst
      M ρ hε hε1 n κ ω hξ
  filter_upwards [hnew, hcontract] with y hy hcy
  filter_upwards [hy, hcy] with x hx hcx
  have hcreatedReal :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n (Sum.inl κ))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure) := by
    have hre :=
      (hx (wickHeadEquiv n (Sum.inl κ))).re
    convert hre using 1
    funext u
    exact Complex.ofReal_re _
  exact
    leftPairingSplitIntegrability_of_joint
      M ρ ε n κ x y ω
      (integrable_leftCreationWeightedCore
        M ρ ε n κ x y ω hcreatedReal)
      hcx

/-- The finite old-pairing source ledger is available with `y`
quantified first. -/
theorem ae_ae_leftOrderSourceIntegrability_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      LeftOrderSourceIntegrability
        M ρ lam ε n x y ω := by
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ κ : PartialPairing (Fin n),
          ∀ᵐ x ∂paperMeasure,
            LeftPairingSplitIntegrability
              M ρ ε n κ x y ω :=
    Filter.eventually_all.2 fun κ =>
      ae_ae_leftPairingSplitIntegrability_rightFirst
        M ρ hε hε1 n κ ω hξ
  filter_upwards [hallY] with y hy
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ κ : PartialPairing (Fin n),
          LeftPairingSplitIntegrability
            M ρ ε n κ x y ω :=
    Filter.eventually_all.2 fun κ => hy κ
  filter_upwards [hallX] with x hx
  refine ⟨?_⟩
  intro κ
  exact
    integrable_leftPairingOuter_of_split
      M ρ lam ε n κ x y ω (hx κ)

/-- Directly marked contractions inherit the right-endpoint-first
sections from their ranked presentation. -/
theorem
    ae_ae_integrable_leftMarkedContractionWeightedCore_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {n : ℕ} (d : MarkedSingle (Fin n))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
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
    ae_ae_integrable_leftRankedContractionWeightedCore_rightFirst
      M ρ hε hε1 n s.1 ω hξ
  filter_upwards [hrank] with y hy
  filter_upwards [hy] with x hx
  refine (hx s.2).congr ?_
  filter_upwards with p
  rw [leftRankedContractionWeightedCore_eq_marked]
  exact congrArg
    (fun d' =>
      leftMarkedContractionWeightedCore
        M ρ ε d' x p.1 y p.2 ω) hs

/-- The free Green convolution of one pairing profile also has
right-endpoint-first sections. -/
theorem ae_ae_integrable_green_mul_randRI_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℕ) (τ : PartialPairing (Fin r))
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      Integrable
        (fun z : T4 =>
          greenFn (x - z) *
            randRI M ρ lam ε r τ z y ω)
        paperMeasure := by
  have hglobal :=
    integrable_green_mul_randIntegrand_flat
      M ρ hε hε1 r τ ω hξ
  have hglobal' :
      Integrable
        (fun p :
            T4 × (T4 × (Fin (r + 1) → T4)) =>
          (greenFn (p.1 - p.2.2 0) *
            randIntegrand M ρ ε τ
              (assemble (p.2.2 0) p.2.1
                (Fin.tail p.2.2)) ω : ℂ))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure))) := by
    simpa only [pairingHalfPhysicalMeasure] using
      hglobal
  have hswapped :
      Integrable
        (fun p :
            T4 × (T4 × (Fin (r + 1) → T4)) =>
          (greenFn (p.2.1 - p.2.2 0) *
            randIntegrand M ρ ε τ
              (assemble (p.2.2 0) p.1
                (Fin.tail p.2.2)) ω : ℂ))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ => paperMeasure))) := by
    exact
      integrable_moveMiddle
        (A := T4) (B := T4)
        (C := Fin (r + 1) → T4) (E := ℂ)
        (μ := paperMeasure) (ν := paperMeasure)
        (τ := Measure.pi fun _ => paperMeasure)
        (fun x y u =>
          (greenFn (x - u 0) *
            randIntegrand M ρ ε τ
              (assemble (u 0) y
                (Fin.tail u)) ω : ℂ))
        hglobal'
  filter_upwards [hswapped.prod_right_ae] with y hy
  filter_upwards [hy.prod_right_ae] with x hx
  have hreal :
      Integrable
        (fun u : Fin (r + 1) → T4 =>
          greenFn (x - u 0) *
            randIntegrand M ρ ε τ
              (assemble (u 0) y
                (Fin.tail u)) ω)
        (Measure.pi fun _ => paperMeasure) := by
    have hre := hx.re
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

/-! ## Right-endpoint-first case-(3) ledgers -/

/-- Local jointly integrable data imply the three fixed-prefix
case-(3) summation fields. -/
theorem caseThreeSummationIntegrability_fixed_of_local
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x y : T4) (ω : M.Ω)
    (hambientComplex :
      Integrable
        (fun v : Fin (2 * (q + 1) + r) → T4 =>
          (randIntegrand M ρ ε (appendPairing σ τ)
            (assemble x y v) ω : ℂ))
        (Measure.pi fun _ => paperMeasure))
    (hcontraction :
      Integrable
        (fun p :
            T4 × (Fin (2 * q + 1 + r) → T4) =>
          leftMarkedContractionWeightedCore
            M ρ ε
              (caseThreeHeadDeletionData q r σ τ hσ)
              x p.1 y p.2 ω)
        (paperMeasure.prod
          (Measure.pi fun _ => paperMeasure)))
    (hfree :
      Integrable
        (fun z : T4 =>
          greenFn (x - z) *
            randRI M ρ lam ε r τ z y ω)
        paperMeasure) :
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

/-- One fixed case-(3) prefix/tail pair has all summation fields in the
right-endpoint-first order. -/
theorem
    ae_ae_caseThreeSummationIntegrability_fixed_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
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
    ae_ae_integrable_randIntegrand_all_rightFirst
      M ρ hε hε1 (2 * (q + 1) + r) ω hξ
  have hjoint :=
    ae_ae_integrable_leftMarkedContractionWeightedCore_rightFirst
      M ρ hε hε1
        (caseThreeHeadDeletionData q r σ τ hσ)
        ω hξ
  have hdelta :=
    ae_ae_integrable_green_mul_randRI_rightFirst
      M ρ lam hε hε1 r τ ω hξ
  filter_upwards [hambient, hjoint, hdelta] with
    y hy hcontractionY hdeltaY
  filter_upwards [hy, hcontractionY, hdeltaY] with
    x hambientAll hcontraction hfree
  exact
    caseThreeSummationIntegrability_fixed_of_local
      M ρ lam ε q r σ τ hσ x y ω
      (hambientAll (appendPairing σ τ))
      hcontraction hfree

/-- The complete finite summation ledger is simultaneous in the
right-endpoint-first order. -/
theorem ae_ae_caseThreeSummationIntegrability_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q r : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      CaseThreeSummationIntegrability
        M ρ lam ε q r x y ω := by
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ (σ :
            {σ :
                PartialPairing
                  (Fin (2 * (q + 1))) //
              IsNonSplit σ})
          (τ : PartialPairing (Fin r)),
          ∀ᵐ x ∂paperMeasure,
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
        ae_ae_caseThreeSummationIntegrability_fixed_rightFirst
          M ρ lam hε hε1 q r σ.1 τ σ.2 ω hξ
  filter_upwards [hallY] with y hy
  have hallX :
      ∀ᵐ x ∂paperMeasure,
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
      Filter.eventually_all.2 fun τ => hy σ τ
  filter_upwards [hallX] with x hx
  refine
    { split := ?_,
      ambient := ?_,
      delta := ?_ }
  · intro σ hσ τ
    exact (hx ⟨σ, hσ⟩ τ).1
  · intro σ hσ τ
    exact (hx ⟨σ, hσ⟩ τ).2.1
  · intro σ hσ τ
    exact (hx ⟨σ, hσ⟩ τ).2.2

/-- The actual marked head contractions used by case (3) are
simultaneous in the right-endpoint-first order. -/
theorem
    ae_ae_caseThreeHeadContractionIntegrability_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (q r : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      CaseThreeHeadContractionIntegrability
        M ρ ε q r x y ω := by
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ (σ :
            {σ :
                PartialPairing
                  (Fin (2 * (q + 1))) //
              IsNonSplit σ})
          (τ : PartialPairing (Fin r)),
          ∀ᵐ x ∂paperMeasure,
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
        ae_ae_integrable_leftMarkedContractionWeightedCore_rightFirst
          M ρ hε hε1
            (caseThreeHeadDeletionData
              q r σ.1 τ σ.2) ω hξ
  filter_upwards [hallY] with y hy
  have hallX :
      ∀ᵐ x ∂paperMeasure,
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
      Filter.eventually_all.2 fun τ => hy σ τ
  filter_upwards [hallX] with x hx
  intro σ τ
  filter_upwards
    [(hx σ τ).prod_right_ae] with z hz
  convert hz using 1
  funext v
  rfl

/-- Every minimal-prefix case-(3) ledger at one order is simultaneous
in the right-endpoint-first order. -/
theorem
    ae_ae_leftWithPrefixCaseThreeIntegrability_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      LeftWithPrefixCaseThreeIntegrability
        M ρ lam ε n x y ω := by
  let Q := Finset.Icc 1 ((n + 1) / 2)
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ q : Q,
          ∀ᵐ x ∂paperMeasure,
            CaseThreeHeadContractionIntegrability
                M ρ ε (q.1 - 1) (n + 1 - 2 * q.1)
                  x y ω ∧
              CaseThreeSummationIntegrability
                M ρ lam ε (q.1 - 1)
                  (n + 1 - 2 * q.1) x y ω := by
    exact Filter.eventually_all.2 fun q => by
      have hhead :=
        ae_ae_caseThreeHeadContractionIntegrability_rightFirst
          M ρ hε hε1 (q.1 - 1)
            (n + 1 - 2 * q.1) ω hξ
      have hsum :=
        ae_ae_caseThreeSummationIntegrability_rightFirst
          M ρ lam hε hε1 (q.1 - 1)
            (n + 1 - 2 * q.1) ω hξ
      filter_upwards [hhead, hsum] with y hy hsy
      filter_upwards [hy, hsy] with x hx hsx
      exact ⟨hx, hsx⟩
  filter_upwards [hallY] with y hy
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ q : Q,
          CaseThreeHeadContractionIntegrability
                M ρ ε (q.1 - 1) (n + 1 - 2 * q.1)
                  x y ω ∧
            CaseThreeSummationIntegrability
              M ρ lam ε (q.1 - 1)
                (n + 1 - 2 * q.1) x y ω :=
    Filter.eventually_all.2 fun q => hy q
  filter_upwards [hallX] with x hx
  refine
    { contraction := ?_,
      summation := ?_ }
  · intro q hq
    exact (hx ⟨q, hq⟩).1
  · intro q hq
    exact (hx ⟨q, hq⟩).2

/-! ## Right-endpoint-first graded recurrence -/

theorem ae_ae_renormWordIntegrable_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (word : List ℕ) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      RenormWordIntegrable
        M ρ lam ε word x y ω := by
  have hglobal :=
    integrable_renormWordIntegrandOnTuple_global
      M ρ lam ε ω hξ word
  have hswapped :
      Integrable
        (fun p :
            T4 ×
              (T4 × (Fin word.length → T4)) =>
          (renormWordIntegrandOnTuple
            M ρ lam ε word
            (assemble p.2.1 p.1 p.2.2) ω : ℂ))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin word.length =>
              paperMeasure))) := by
    exact
      integrable_moveMiddle
        (A := T4) (B := T4)
        (C := Fin word.length → T4) (E := ℂ)
        (μ := paperMeasure) (ν := paperMeasure)
        (τ := Measure.pi fun _ => paperMeasure)
        (fun x y v =>
          (renormWordIntegrandOnTuple
            M ρ lam ε word
            (assemble x y v) ω : ℂ))
        hglobal
  filter_upwards [hswapped.prod_right_ae] with y hy
  filter_upwards [hy.prod_right_ae] with x hx
  unfold RenormWordIntegrable
  have hxRe := hx.re
  convert hxRe using 1
  funext v
  exact Complex.ofReal_re _

theorem
    ae_ae_gradedParametrix_succ_eq_noise_sub_counterterms_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) :
    ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
      gradedParametrix M ρ lam ε (n + 1) x y ω =
        gradedParametrixNoiseSource
            M ρ lam ε n x y ω -
          gradedOrderCountertermSum
            M ρ lam ε n x y ω := by
  have hallY :
      ∀ᵐ y ∂paperMeasure,
        ∀ k : Fin (n + 1),
          ∀ c : Composition (n - k.val),
            ∀ᵐ x ∂paperMeasure,
              RenormWordIntegrable M ρ lam ε
                ((k.val + 1) :: c.blocks) x y ω := by
    exact Filter.eventually_all.2 fun k =>
      Filter.eventually_all.2 fun c =>
        ae_ae_renormWordIntegrable_rightFirst
          M ρ lam ε ω hξ
            ((k.val + 1) :: c.blocks)
  filter_upwards [hallY] with y hy
  have hallX :
      ∀ᵐ x ∂paperMeasure,
        ∀ k : Fin (n + 1),
          ∀ c : Composition (n - k.val),
            RenormWordIntegrable M ρ lam ε
              ((k.val + 1) :: c.blocks) x y ω := by
    exact Filter.eventually_all.2 fun k =>
      Filter.eventually_all.2 fun c =>
        hy k c
  filter_upwards [hallX] with x hx
  exact
    gradedParametrix_succ_eq_noise_sub_counterterms
      M ρ lam ε n x y ω hx

/-! ## Strong induction for the pairing/graded comparison -/

/-- On every continuous sample, the paper pairing expansion and the
graded word expansion agree with the right endpoint quantified first.
This is the Fubini orientation needed to substitute the induction
hypothesis under the source and counterterm convolutions. -/
theorem ae_ae_parametrixP_eq_gradedParametrix_rightFirst
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω)) :
    ∀ n : ℕ,
      ∀ᵐ y ∂paperMeasure, ∀ᵐ x ∂paperMeasure,
        parametrixP M ρ lam ε n x y ω =
          gradedParametrix M ρ lam ε n x y ω := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
    cases order with
    | zero =>
      filter_upwards with y
      filter_upwards with x
      rw [parametrixP_zero, gradedParametrix_zero]
    | succ n =>
      have hsource :=
        ae_ae_leftOrderSourceIntegrability_rightFirst
          M ρ lam hε hε1 n ω hξ
      have hsplit :
          ∀ᵐ y ∂paperMeasure,
            ∀ κ : PartialPairing (Fin n),
              ∀ᵐ x ∂paperMeasure,
                LeftPairingSplitIntegrability
                  M ρ ε n κ x y ω :=
        Filter.eventually_all.2 fun κ =>
          ae_ae_leftPairingSplitIntegrability_rightFirst
            M ρ hε hε1 n κ ω hξ
      have hraw :=
        ae_ae_integrable_randIntegrand_all_rightFirst
          M ρ hε hε1 (n + 1) ω hξ
      have hcase :=
        ae_ae_leftWithPrefixCaseThreeIntegrability_rightFirst
          M ρ lam hε hε1 n ω hξ
      have hgraded :=
        ae_ae_gradedParametrix_succ_eq_noise_sub_counterterms_rightFirst
          M ρ lam ε ω hξ n
      have hprevious :=
        ih n (by omega)
      let Q := Finset.Icc 1 ((n + 1) / 2)
      have htails :
          ∀ᵐ y ∂paperMeasure,
            ∀ q : Q,
              ∀ᵐ z ∂paperMeasure,
                parametrixP M ρ lam ε
                    (n + 1 - 2 * q.1) z y ω =
                  gradedParametrix M ρ lam ε
                    (n + 1 - 2 * q.1) z y ω := by
        exact Filter.eventually_all.2 fun q => by
          have hqbounds := Finset.mem_Icc.mp q.2
          apply ih (n + 1 - 2 * q.1)
          omega
      filter_upwards
        [hsource, hsplit, hraw, hcase,
          hgraded, hprevious, htails] with
        y hsourceY hsplitY hrawY hcaseY
          hgradedY hpreviousY htailsY
      have hsplitX :
          ∀ᵐ x ∂paperMeasure,
            ∀ κ : PartialPairing (Fin n),
              LeftPairingSplitIntegrability
                M ρ ε n κ x y ω :=
        Filter.eventually_all.2 fun κ => hsplitY κ
      filter_upwards
        [hsourceY, hsplitX, hrawY, hcaseY,
          hgradedY] with
        x hsourceX hsplitAtX hrawAtX
          hcaseAtX hgradedAtX
      have hcreation :
          ∀ κ : PartialPairing (Fin n),
            Integrable
              (fun u : Fin (n + 1) → T4 =>
                randIntegrand M ρ ε
                  (wickHeadEquiv n (Sum.inl κ))
                  (assemble x y u) ω)
              (Measure.pi fun _ => paperMeasure) := by
        intro κ
        have hre :=
          (hrawAtX
            (wickHeadEquiv n (Sum.inl κ))).re
        convert hre using 1
        funext u
        exact Complex.ofReal_re _
      have hnoPrefix :
          ∀ d :
              {d : MarkedSingle (Fin n) //
                ¬markedHasHeadPrefix d},
            Integrable
              (fun u : Fin (n + 1) → T4 =>
                randIntegrand M ρ ε
                  (wickHeadEquiv n (Sum.inr d.1))
                  (assemble x y u) ω)
              (Measure.pi fun _ => paperMeasure) := by
        intro d
        have hre :=
          (hrawAtX
            (wickHeadEquiv n (Sum.inr d.1))).re
        convert hre using 1
        funext u
        exact Complex.ofReal_re _
      have hactual :=
        leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms
          M ρ lam ε n x y ω
          hsourceX hsplitAtX hcreation hnoPrefix
          (leftWithPrefixContractionSum_eq_randRISum_add_countertermSum
            M ρ lam ε n x y ω hcaseAtX)
      have hsourceEq :
          leftParametrixNoiseSource
              M ρ lam ε n x y ω =
            gradedParametrixNoiseSource
              M ρ lam ε n x y ω := by
        unfold leftParametrixNoiseSource
        unfold gradedParametrixNoiseSource
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hpreviousY] with z hz
        rw [hz]
        ring
      have hcounterEq :
          leftOrderCountertermSum
              M ρ lam ε n x y ω =
            gradedOrderCountertermSum
              M ρ lam ε n x y ω := by
        unfold leftOrderCountertermSum
        unfold gradedOrderCountertermSum
        apply Finset.sum_congr rfl
        intro q hq
        rw [caseThreeCountertermBlock_eq]
        unfold gradedCountertermBlock
        congr 1
        apply integral_congr_ae
        filter_upwards [htailsY ⟨q, hq⟩] with z hz
        rw [hz]
      calc
        parametrixP M ρ lam ε (n + 1) x y ω =
            leftParametrixNoiseSource
                M ρ lam ε n x y ω -
              leftOrderCountertermSum
                M ρ lam ε n x y ω := by
                  linarith
        _ =
            gradedParametrixNoiseSource
                M ρ lam ε n x y ω -
              gradedOrderCountertermSum
                M ρ lam ε n x y ω := by
                  rw [hsourceEq, hcounterEq]
        _ =
            gradedParametrix M ρ lam ε (n + 1)
              x y ω :=
          hgradedAtX.symm

/-- The same equality in the paper's coefficient-integration order.
The preceding right-first theorem supplies every lower-order equality
under the `z` convolutions, so no interchange of abstract a.e.
quantifiers is used. -/
theorem ae_ae_parametrixP_eq_gradedParametrix
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ω : M.Ω) (hξ : Continuous (M.xiEps ρ ε ω))
    (order : ℕ) :
    ∀ᵐ x ∂paperMeasure, ∀ᵐ y ∂paperMeasure,
      parametrixP M ρ lam ε order x y ω =
        gradedParametrix M ρ lam ε order x y ω := by
  cases order with
  | zero =>
    filter_upwards with x
    filter_upwards with y
    rw [parametrixP_zero, gradedParametrix_zero]
  | succ n =>
    have hsource :=
      ae_ae_leftOrderSourceIntegrability
        M ρ lam hε hε1 n ω hξ
    have hsplit :
        ∀ᵐ x ∂paperMeasure,
          ∀ κ : PartialPairing (Fin n),
            ∀ᵐ y ∂paperMeasure,
              LeftPairingSplitIntegrability
                M ρ ε n κ x y ω :=
      Filter.eventually_all.2 fun κ =>
        ae_ae_leftPairingSplitIntegrability
          M ρ hε hε1 n κ ω hξ
    have hraw :=
      M.ae_ae_integrable_randIntegrand_all
        ρ hε hε1 (n + 1) ω hξ
    have hcase :=
      ae_ae_leftWithPrefixCaseThreeIntegrability
        M ρ lam hε hε1 n ω hξ
    have hgraded :=
      ae_ae_gradedParametrix_succ_eq_noise_sub_counterterms
        M ρ lam ε ω hξ n
    have hprevious :=
      ae_ae_parametrixP_eq_gradedParametrix_rightFirst
        M ρ lam hε hε1 ω hξ n
    let Q := Finset.Icc 1 ((n + 1) / 2)
    have htails :
        ∀ᵐ y ∂paperMeasure,
          ∀ q : Q,
            ∀ᵐ z ∂paperMeasure,
              parametrixP M ρ lam ε
                  (n + 1 - 2 * q.1) z y ω =
                gradedParametrix M ρ lam ε
                  (n + 1 - 2 * q.1) z y ω :=
      Filter.eventually_all.2 fun q =>
        ae_ae_parametrixP_eq_gradedParametrix_rightFirst
          M ρ lam hε hε1 ω hξ
            (n + 1 - 2 * q.1)
    filter_upwards
      [hsource, hsplit, hraw, hcase, hgraded] with
      x hsourceX hsplitX hrawX hcaseX hgradedX
    have hsplitY :
        ∀ᵐ y ∂paperMeasure,
          ∀ κ : PartialPairing (Fin n),
            LeftPairingSplitIntegrability
              M ρ ε n κ x y ω :=
      Filter.eventually_all.2 fun κ => hsplitX κ
    filter_upwards
      [hsourceX, hsplitY, hrawX, hcaseX,
        hgradedX, hprevious, htails] with
      y hsourceAtY hsplitAtY hrawAtY
        hcaseAtY hgradedAtY hpreviousY htailsY
    have hcreation :
        ∀ κ : PartialPairing (Fin n),
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              randIntegrand M ρ ε
                (wickHeadEquiv n (Sum.inl κ))
                (assemble x y u) ω)
            (Measure.pi fun _ => paperMeasure) := by
      intro κ
      have hre :=
        (hrawAtY
          (wickHeadEquiv n (Sum.inl κ))).re
      convert hre using 1
      funext u
      exact Complex.ofReal_re _
    have hnoPrefix :
        ∀ d :
            {d : MarkedSingle (Fin n) //
              ¬markedHasHeadPrefix d},
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              randIntegrand M ρ ε
                (wickHeadEquiv n (Sum.inr d.1))
                (assemble x y u) ω)
            (Measure.pi fun _ => paperMeasure) := by
      intro d
      have hre :=
        (hrawAtY
          (wickHeadEquiv n (Sum.inr d.1))).re
      convert hre using 1
      funext u
      exact Complex.ofReal_re _
    have hactual :=
      leftParametrixNoiseSource_eq_parametrix_succ_add_counterterms
        M ρ lam ε n x y ω
        hsourceAtY hsplitAtY hcreation hnoPrefix
        (leftWithPrefixContractionSum_eq_randRISum_add_countertermSum
          M ρ lam ε n x y ω hcaseAtY)
    have hsourceEq :
        leftParametrixNoiseSource
            M ρ lam ε n x y ω =
          gradedParametrixNoiseSource
            M ρ lam ε n x y ω := by
      unfold leftParametrixNoiseSource
      unfold gradedParametrixNoiseSource
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hpreviousY] with z hz
      rw [hz]
      ring
    have hcounterEq :
        leftOrderCountertermSum
            M ρ lam ε n x y ω =
          gradedOrderCountertermSum
            M ρ lam ε n x y ω := by
      unfold leftOrderCountertermSum
      unfold gradedOrderCountertermSum
      apply Finset.sum_congr rfl
      intro q hq
      rw [caseThreeCountertermBlock_eq]
      unfold gradedCountertermBlock
      congr 1
      apply integral_congr_ae
      filter_upwards [htailsY ⟨q, hq⟩] with z hz
      rw [hz]
    calc
      parametrixP M ρ lam ε (n + 1) x y ω =
          leftParametrixNoiseSource
              M ρ lam ε n x y ω -
            leftOrderCountertermSum
              M ρ lam ε n x y ω := by
                linarith
      _ =
          gradedParametrixNoiseSource
              M ρ lam ε n x y ω -
            gradedOrderCountertermSum
              M ρ lam ε n x y ω := by
                rw [hsourceEq, hcounterEq]
      _ =
          gradedParametrix M ρ lam ε (n + 1)
            x y ω :=
        hgradedAtY.symm

/-- Proposition 3.4 now supplies the exact integrated coefficient
agreement required by the physical `L²` bridge on every continuous
sample. -/
theorem parametrixGradedCoefficientAgreement_of_continuous
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    ParametrixGradedCoefficientAgreement
      M ρ lam ε A ω := by
  apply
    parametrixGradedCoefficientAgreement_of_ae_kernel_eq
  intro n _hn
  exact
    ae_ae_parametrixP_eq_gradedParametrix
      M ρ lam hε hε1 ω hξ n

/-- The agreement is automatic on the full-measure event of continuous
mollified-noise samples. -/
theorem ae_parametrixGradedCoefficientAgreement
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (A : ℕ) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      ParametrixGradedCoefficientAgreement
        M ρ lam ε A ω := by
  filter_upwards [M.ae_continuous_xiEps ρ hε] with
    ω hξ
  exact
    parametrixGradedCoefficientAgreement_of_continuous
      M ρ lam hε hε1 A ω hξ

end PartialPairing

end

end Anderson4D
