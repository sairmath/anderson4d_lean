import Anderson4D.Main.GaussianPSD
import Anderson4D.Main.Theorem
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Finite-mode convergence in law

This file upgrades the frozen scalar characteristic-function statement to
the realified finite-family convergence-in-distribution formulation of the
main theorem.  The random vector uses the manifestly measurable Fredholm
realization.  At every positive mollification scale this realization agrees
almost surely with the samplewise resolvent coefficients occurring in
`MainStatement`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology

/-- The measurable realification of a finite family of Fredholm Fourier
coefficients.  `false` is the real coordinate and `true` the imaginary
coordinate. -/
def measurableFredholmFiniteModeVector
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) (ω : M.Ω) :
    EuclideanSpace ℝ (Fin s × Bool) :=
  WithLp.toLp 2 fun p =>
    match p.2 with
    | false =>
        (measurableFredholmModeHcoeff
          M ρ lam ε (modes p.1).1 (modes p.1).2 ω).re
    | true =>
        (measurableFredholmModeHcoeff
          M ρ lam ε (modes p.1).1 (modes p.1).2 ω).im

/-- The literal samplewise Fredholm vector.  This need not be manifestly
measurable from its definition, but at every positive scale it is almost
surely equal to `measurableFredholmFiniteModeVector`. -/
def fredholmFiniteModeVector
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) (ω : M.Ω) :
    EuclideanSpace ℝ (Fin s × Bool) :=
  WithLp.toLp 2 fun p =>
    match p.2 with
    | false =>
        (fredholmModeHcoeff
          M ρ lam ε (modes p.1).1 (modes p.1).2 ω).re
    | true =>
        (fredholmModeHcoeff
          M ρ lam ε (modes p.1).1 (modes p.1).2 ω).im

theorem measurable_measurableFredholmFiniteModeVector
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) :
    Measurable
      (measurableFredholmFiniteModeVector
        M ρ lam ε s modes) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  rintro ⟨j, b⟩
  cases b
  · exact Complex.measurable_re.comp
      (measurable_measurableFredholmModeHcoeff
        M ρ lam ε (modes j).1 (modes j).2)
  · exact Complex.measurable_im.comp
      (measurable_measurableFredholmModeHcoeff
        M ρ lam ε (modes j).1 (modes j).2)

/-- The realified measurable representative agrees almost surely with
the literal samplewise Fredholm mode family. -/
theorem ae_measurableFredholmFiniteModeVector_eq_fredholmFiniteModeVector
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (s : ℕ) (modes : Fin s → Z4 × Z4) :
    measurableFredholmFiniteModeVector
        M ρ lam ε s modes =ᵐ[(volume : Measure M.Ω)]
      fredholmFiniteModeVector M ρ lam ε s modes := by
  have hall :
      ∀ᵐ ω ∂(volume : Measure M.Ω), ∀ j : Fin s,
        measurableFredholmModeHcoeff
            M ρ lam ε (modes j).1 (modes j).2 ω =
          fredholmModeHcoeff
            M ρ lam ε (modes j).1 (modes j).2 ω := by
    have hallFinset :=
      (Filter.eventually_all_finset Finset.univ).2
        (fun j _ =>
          ae_measurableFredholmModeHcoeff_eq_fredholmModeHcoeff
            M ρ lam hε (modes j).1 (modes j).2)
    filter_upwards [hallFinset] with ω hω
    intro j
    exact hω j (Finset.mem_univ j)
  filter_upwards [hall] with ω hω
  ext p
  rcases p with ⟨j, b⟩
  cases b
  · exact congrArg Complex.re (hω j)
  · exact congrArg Complex.im (hω j)

theorem aemeasurable_fredholmFiniteModeVector
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (s : ℕ) (modes : Fin s → Z4 × Z4) :
    AEMeasurable
      (fredholmFiniteModeVector M ρ lam ε s modes)
      (volume : Measure M.Ω) :=
  (measurable_measurableFredholmFiniteModeVector
      M ρ lam ε s modes).aemeasurable.congr
    (ae_measurableFredholmFiniteModeVector_eq_fredholmFiniteModeVector
      M ρ lam hε s modes)

/-- Pairing the realified vector against a real test vector is exactly the
scalar finite-mode observable with the corresponding complex coefficients. -/
theorem inner_measurableFredholmFiniteModeVector
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) (ω : M.Ω)
    (t : EuclideanSpace ℝ (Fin s × Bool)) :
    ⟪measurableFredholmFiniteModeVector
        M ρ lam ε s modes ω, t⟫_ℝ =
      measurableFredholmFiniteModeReal M ρ lam ε s modes
        (complexCoeffOfRealified (t : Fin s × Bool → ℝ)) ω := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_prod_type, measurableFredholmFiniteModeVector,
    measurableFredholmFiniteModeReal, complexCoeffOfRealified]
  simp only [Fintype.sum_bool]
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

/-- Lévy's reverse implication over an arbitrary countably generated
source filter, obtained by testing every sequence converging to that
filter and applying mathlib's sequence-indexed Lévy theorem. -/
theorem ProbabilityMeasure.tendsto_of_filter_tendsto_charFun
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → ProbabilityMeasure E) (μ₀ : ProbabilityMeasure E)
    (h : ∀ t : E,
      Tendsto (fun i => charFun (μ i) t) l
        (𝓝 (charFun μ₀ t))) :
    Tendsto μ l (𝓝 μ₀) := by
  apply Filter.tendsto_of_seq_tendsto
  intro u hu
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
  intro t
  exact (h t).comp hu

/-- The law of the measurable finite-mode Fredholm vector. -/
def measurableFredholmFiniteModeLaw
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin s × Bool)) :=
  MeasureTheory.ProbabilityMeasure.map
    (⟨(volume : Measure M.Ω), inferInstance⟩ :
      ProbabilityMeasure M.Ω)
    (measurable_measurableFredholmFiniteModeVector
      M ρ lam ε s modes).aemeasurable

/-- At every positive scale the law used in `MainLawStatement` is
literally the push-forward law of the samplewise Fredholm vector. -/
theorem measurableFredholmFiniteModeLaw_eq_map_fredholmFiniteModeVector
    (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (s : ℕ) (modes : Fin s → Z4 × Z4) :
    (measurableFredholmFiniteModeLaw
        M ρ lam ε s modes :
      Measure (EuclideanSpace ℝ (Fin s × Bool))) =
      (volume : Measure M.Ω).map
        (fredholmFiniteModeVector M ρ lam ε s modes) := by
  unfold measurableFredholmFiniteModeLaw
    MeasureTheory.ProbabilityMeasure.map
  exact Measure.map_congr
    (ae_measurableFredholmFiniteModeVector_eq_fredholmFiniteModeVector
      M ρ lam hε s modes)

/-- The finite-family convergence-in-distribution form of the main
statement.  The limit is the explicit realified Gaussian law. -/
def MainLawStatement (M : NoiseModel) (ρ : SmoothCutoff) : Prop :=
  ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, lam ∈ Set.Ioo 0 lam₀ →
    ∀ (s : ℕ) (modes : Fin s → Z4 × Z4),
      Tendsto
        (fun ε : ℝ => measurableFredholmFiniteModeLaw
          M ρ lam ε s modes)
        (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
        (𝓝 (gaussianLimitLaw lam modes))

/-- The scalar Cramér--Wold characteristic-function statement implies the
finite-family convergence-in-distribution statement. -/
theorem mainLawStatement_of_mainStatement
    (M : NoiseModel) (ρ : SmoothCutoff)
    (hmain : MainStatement M ρ) :
    MainLawStatement M ρ := by
  rcases hmain with ⟨lam₀, hlam₀, hmain⟩
  refine ⟨min lam₀ Real.pi, lt_min hlam₀ Real.pi_pos, ?_⟩
  intro lam hlam s modes
  have hlamMain : lam ∈ Set.Ioo (0 : ℝ) lam₀ :=
    ⟨hlam.1, lt_of_lt_of_le hlam.2 (min_le_left _ _)⟩
  have hlamPi : lam < Real.pi :=
    lt_of_lt_of_le hlam.2 (min_le_right _ _)
  have hlamSq : lam ^ 2 < 2 * Real.pi ^ 2 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith [sq_pos_of_pos hpi, mul_self_lt_mul_self hlam.1.le hlamPi]
  let X : ℝ → M.Ω → EuclideanSpace ℝ (Fin s × Bool) :=
    fun ε => measurableFredholmFiniteModeVector
      M ρ lam ε s modes
  apply ProbabilityMeasure.tendsto_of_filter_tendsto_charFun
  intro t
  let c : Fin s → ℂ :=
    complexCoeffOfRealified (t : Fin s × Bool → ℝ)
  have hscalar := hmain lam hlamMain s modes c
  have hpositive :
      ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioo (0 : ℝ) 1), 0 < ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε.1
  have hsource :
      (fun ε : ℝ =>
        charFun
          (measurableFredholmFiniteModeLaw
            M ρ lam ε s modes)
          t) =ᶠ[
            nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)]
        fun ε : ℝ =>
          ∫ ω, Complex.exp (Complex.I *
            (fredholmFiniteModeReal
              M ρ lam ε s modes c ω : ℂ))
    ∂(volume : Measure M.Ω) := by
    filter_upwards [hpositive] with ε hε
    rw [charFun_eq_integral_innerProbChar]
    change
      (∫ v : EuclideanSpace ℝ (Fin s × Bool),
        BoundedContinuousFunction.innerProbChar t v
        ∂(volume : Measure M.Ω).map (X ε)) =
      ∫ ω, Complex.exp (Complex.I *
        (fredholmFiniteModeReal
          M ρ lam ε s modes c ω : ℂ))
        ∂(volume : Measure M.Ω)
    rw [integral_map
        ((measurable_measurableFredholmFiniteModeVector
          M ρ lam ε s modes).aemeasurable)
        (BoundedContinuousFunction.innerProbChar t).continuous.aestronglyMeasurable]
    rw [show (fun ω =>
        BoundedContinuousFunction.innerProbChar t (X ε ω)) =
        (fun ω => Complex.exp (Complex.I *
          (measurableFredholmFiniteModeReal
            M ρ lam ε s modes c ω : ℂ))) by
      funext ω
      rw [BoundedContinuousFunction.innerProbChar_apply,
        inner_measurableFredholmFiniteModeVector]
      simp [c, mul_comm]]
    exact integral_exp_I_measurableFredholm_eq_fredholm
      M ρ lam hε s modes c
  have ht :
      WithLp.toLp 2 (realifiedLinearCoeff c) = t := by
    calc
      WithLp.toLp 2 (realifiedLinearCoeff c) =
          WithLp.toLp 2 (t : Fin s × Bool → ℝ) := by
        rw [show realifiedLinearCoeff c =
            (t : Fin s × Bool → ℝ) by
          simp [c]]
      _ = t := WithLp.toLp_ofLp 2 t
  rw [show charFun (gaussianLimitLaw lam modes) t =
      ((Real.exp (-(limitVar lam modes c) / 2) : ℝ) : ℂ) by
    rw [← ht]
    rw [charFun_gaussianLimitLaw_realifiedLinearCoeff_of_subcritical
      lam modes hlamSq c]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring]
  exact hscalar.congr' hsource.symm

/-- Conditional convergence in law, directly from the conditional
characteristic-function theorem. -/
theorem mainConditionalLaw_of_mainConditional
    (M : NoiseModel) (ρ : SmoothCutoff)
    (hmain : MainConditional M ρ) :
    Prop36Family M ρ → MainLawStatement M ρ :=
  fun h36 => mainLawStatement_of_mainStatement M ρ (hmain h36)

end

end Anderson4D
