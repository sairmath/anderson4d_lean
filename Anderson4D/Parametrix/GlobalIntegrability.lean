import Anderson4D.Parametrix.L2NeumannActionAll

/-!
# Global Green-chain integrability

The Fourier-coefficient form of Proposition 3.4 integrates both external
kernel variables.  At that level every finite Green chain is genuinely
integrable, even though a fixed-endpoint section can fail on the diagonal
in four dimensions.  This file records the measure-preserving change of
variables from recursive weighted paths to the paper's flat
`(x,y,internal variables)` coordinates.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- Separate the terminal coordinate of a finite path, retaining the
preceding coordinates in their original order. -/
def globalPathLastEquiv (n : ℕ) :
    (Fin (n + 1) → T4) ≃ᵐ
      T4 × (Fin n → T4) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => T4) (Fin.last n)

@[simp]
theorem globalPathLastEquiv_symm_apply
    (n : ℕ) (y : T4) (v : Fin n → T4) :
    (globalPathLastEquiv n).symm (y, v) =
      Fin.snoc v y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [globalPathLastEquiv]
  · simp [globalPathLastEquiv]

theorem measurePreserving_globalPathLastEquiv
    (n : ℕ) :
    MeasurePreserving
      (globalPathLastEquiv n)
      (Measure.pi fun _ : Fin (n + 1) =>
        paperMeasure)
      (paperMeasure.prod
        (Measure.pi fun _ : Fin n =>
          paperMeasure)) := by
  simpa only [globalPathLastEquiv,
    Fin.succAbove_last] using
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => paperMeasure)
      (Fin.last n))

/-- Apply the terminal-coordinate equivalence under a separate left
endpoint. -/
def globalFlatPathEquiv (n : ℕ) :
    (T4 × (Fin (n + 1) → T4)) ≃ᵐ
      T4 × (T4 × (Fin n → T4)) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl T4)
    (globalPathLastEquiv n)

theorem measurePreserving_globalFlatPathEquiv
    (n : ℕ) :
    MeasurePreserving
      (globalFlatPathEquiv n)
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n =>
            paperMeasure))) := by
  exact
    (MeasurePreserving.id paperMeasure).prod
      (measurePreserving_globalPathLastEquiv n)

/-- Every flat Green chain with continuous vertex weights is jointly
integrable in both endpoints and all internal vertices. -/
theorem integrable_continuousNeumannFlatIntegrand_joint
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    Integrable
      (fun p : T4 × (T4 × (Fin n → T4)) =>
        continuousNeumannFlatIntegrand
          m β n p.1 p.2.1 p.2.2)
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n =>
            paperMeasure))) := by
  let source : T4 × (Fin (n + 1) → T4) → ℂ :=
    fun p =>
      weightedGreenPath
        (neumannActionPathWeight m β n)
        p.1 p.2
  have hsource :
      Integrable source
        (paperMeasure.prod
          (Measure.pi fun _ : Fin (n + 1) =>
            paperMeasure)) := by
    simpa only [source] using
      integrable_weightedGreenPath_joint
        (neumannActionPathWeight m β n)
  let e := globalFlatPathEquiv n
  have hp := measurePreserving_globalFlatPathEquiv n
  have htarget :
      Integrable (fun p => source (e.symm p))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin n =>
              paperMeasure))) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => source (e.symm p))
    apply hiff.mp
    convert hsource using 1
    funext p
    exact congrArg source (e.symm_apply_apply p)
  convert htarget using 1
  funext p
  rcases p with ⟨x, y, v⟩
  change
    continuousNeumannFlatIntegrand m β n x y v =
      source (e.symm (x, y, v))
  have he :
      e.symm (x, y, v) =
        (x, Fin.snoc v y) := by
    apply Prod.ext
    · rfl
    · exact globalPathLastEquiv_symm_apply n y v
  rw [he]
  exact
    (weightedGreenPath_neumann_snoc
      m β n x y v).symm

/-- The unweighted flat Green chain is the universal integrable
majorant used for globally integrated random kernels. -/
theorem integrable_flatGreenChain_joint (n : ℕ) :
    Integrable
      (fun p : T4 × (T4 × (Fin n → T4)) =>
        ∏ e : Fin (n + 1),
          (greenFn
            ((assemble p.1 p.2.1 p.2.2) e.castSucc -
              (assemble p.1 p.2.1 p.2.2) e.succ) : ℂ))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n =>
            paperMeasure))) := by
  let oneMap : C(T4, ℂ) :=
    ContinuousMap.const T4 1
  have h :=
    integrable_continuousNeumannFlatIntegrand_joint
      oneMap 0 n
  convert h using 1
  funext p
  unfold continuousNeumannFlatIntegrand
  simp only [oneMap, ContinuousMap.const_apply,
    Finset.prod_const_one, mul_one, charT4_zero]

/-- Any uniformly bounded measurable factor may be multiplied into the
universal Green chain without losing integrability. -/
theorem integrable_bounded_mul_flatGreenChain_joint
    (n : ℕ)
    (weight :
      T4 × (T4 × (Fin n → T4)) → ℂ)
    (hweight :
      AEStronglyMeasurable weight
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin n =>
              paperMeasure))))
    (C : ℝ)
    (hbound : ∀ᵐ p ∂(paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n =>
            paperMeasure))),
      ‖weight p‖ ≤ C) :
    Integrable
      (fun p : T4 × (T4 × (Fin n → T4)) =>
        weight p *
          ∏ e : Fin (n + 1),
            (greenFn
              ((assemble p.1 p.2.1 p.2.2) e.castSucc -
                (assemble p.1 p.2.1 p.2.2) e.succ) : ℂ))
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ : Fin n =>
            paperMeasure))) := by
  exact
    (integrable_flatGreenChain_joint n).bdd_mul
      hweight hbound

end

end Anderson4D
