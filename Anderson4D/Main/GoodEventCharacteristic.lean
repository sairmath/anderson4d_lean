import Anderson4D.Main.GeometricTruncation
import Anderson4D.Parametrix.FredholmCoefficientBridge

/-!
# Good-event replacement at the characteristic-function level

Paper §3.4 Step 2 only needs to replace the parametrix by the true
resolvent in finitely many scalar Fourier tests.  This file proves that
replacement directly for characteristic functions, avoiding any
unnecessary tightness or Prokhorov argument.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- The complex unit-circle exponential has norm one. -/
theorem norm_exp_I_mul_ofReal (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num

/-- Quantitative fixed-mode replacement estimate.

On `good`, the two real phases differ by at most `error`; on its
complement the two unit-circle values differ by at most two. -/
theorem norm_integral_exp_I_sub_le_error_add_bad
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (good : Set Ω) (hgood : MeasurableSet good)
    (error : ℝ) (herror : 0 ≤ error)
    (hclose : ∀ ω ∈ good, ‖X ω - Y ω‖ ≤ error) :
    ‖(∫ ω, Complex.exp (Complex.I * (X ω : ℂ)) ∂μ) -
        ∫ ω, Complex.exp (Complex.I * (Y ω : ℂ)) ∂μ‖ ≤
      error + 2 * μ.real goodᶜ := by
  let f : Ω → ℂ :=
    fun ω => Complex.exp (Complex.I * (X ω : ℂ))
  let g : Ω → ℂ :=
    fun ω => Complex.exp (Complex.I * (Y ω : ℂ))
  let d : Ω → ℝ := fun ω => ‖f ω - g ω‖
  have hfAE : AEMeasurable f μ := by
    exact Complex.measurable_exp.comp_aemeasurable
      ((Complex.measurable_ofReal.comp_aemeasurable hX).const_mul
        Complex.I)
  have hgAE : AEMeasurable g μ := by
    exact Complex.measurable_exp.comp_aemeasurable
      ((Complex.measurable_ofReal.comp_aemeasurable hY).const_mul
        Complex.I)
  have hf : Integrable f μ := by
    apply Integrable.of_bound hfAE.aestronglyMeasurable 1
    filter_upwards with ω
    exact le_of_eq (norm_exp_I_mul_ofReal (X ω))
  have hg : Integrable g μ := by
    apply Integrable.of_bound hgAE.aestronglyMeasurable 1
    filter_upwards with ω
    exact le_of_eq (norm_exp_I_mul_ofReal (Y ω))
  have hdPoint (ω : Ω) : d ω ≤ 2 := by
    calc
      d ω = ‖f ω - g ω‖ := rfl
      _ ≤ ‖f ω‖ + ‖g ω‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show ‖f ω‖ = 1 by
          exact norm_exp_I_mul_ofReal (X ω)]
        rw [show ‖g ω‖ = 1 by
          exact norm_exp_I_mul_ofReal (Y ω)]
        norm_num
  have hd : Integrable d μ := by
    apply Integrable.of_bound
      (hfAE.sub hgAE).norm.aestronglyMeasurable 2
    filter_upwards with ω
    change ‖d ω‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hdPoint ω
  have hgoodBound :
      ∫ ω in good, d ω ∂μ ≤ error := by
    calc
      ∫ ω in good, d ω ∂μ ≤
          ∫ _ω in good, error ∂μ := by
        apply setIntegral_mono_on hd.integrableOn
          (integrable_const error).integrableOn hgood
        intro ω hω
        exact
          (norm_exp_I_mul_sub_exp_I_mul_le (X ω) (Y ω)).trans
            (hclose ω hω)
      _ = μ.real good * error := by
        rw [setIntegral_const, smul_eq_mul]
      _ ≤ error := by
        nlinarith [measureReal_nonneg (μ := μ) (s := good),
          measureReal_le_one (μ := μ) (s := good)]
  have hbadBound :
      ∫ ω in goodᶜ, d ω ∂μ ≤ 2 * μ.real goodᶜ := by
    calc
      ∫ ω in goodᶜ, d ω ∂μ ≤
          ∫ _ω in goodᶜ, (2 : ℝ) ∂μ := by
        apply setIntegral_mono_on hd.integrableOn
          (integrable_const (2 : ℝ)).integrableOn hgood.compl
        intro ω hω
        exact hdPoint ω
      _ = μ.real goodᶜ * 2 := by
        rw [setIntegral_const, smul_eq_mul]
      _ = 2 * μ.real goodᶜ := by ring
  change ‖(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ‖ ≤ _
  calc
    ‖(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ‖ =
        ‖∫ ω, f ω - g ω ∂μ‖ := by
      rw [integral_sub hf hg]
    _ ≤ ∫ ω, d ω ∂μ :=
      norm_integral_le_integral_norm (μ := μ) (f := fun ω => f ω - g ω)
    _ = (∫ ω in good, d ω ∂μ) +
        ∫ ω in goodᶜ, d ω ∂μ :=
      (integral_add_compl hgood hd).symm
    _ ≤ error + 2 * μ.real goodᶜ :=
      add_le_add hgoodBound hbadBound

/-- Characteristic-function convergence is unchanged by a uniformly
small error on measurable events whose complements vanish in
probability. -/
theorem tendsto_integral_exp_I_of_goodEvent_replace
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {l : Filter ι} {z : ℂ}
    (X Y : ι → Ω → ℝ)
    (hXlim :
      Tendsto
        (fun i => ∫ ω,
          Complex.exp (Complex.I * (X i ω : ℂ)) ∂μ)
        l (𝓝 z))
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hY : ∀ i, AEMeasurable (Y i) μ)
    (good : ι → Set Ω) (hgood : ∀ i, MeasurableSet (good i))
    (error : ι → ℝ)
    (herror_nonneg : ∀ᶠ i in l, 0 ≤ error i)
    (herror : Tendsto error l (𝓝 0))
    (hbad : Tendsto (fun i => μ.real (good i)ᶜ) l (𝓝 0))
    (hclose :
      ∀ᶠ i in l, ∀ ω ∈ good i,
        ‖X i ω - Y i ω‖ ≤ error i) :
    Tendsto
      (fun i => ∫ ω,
        Complex.exp (Complex.I * (Y i ω : ℂ)) ∂μ)
      l (𝓝 z) := by
  have hbound :
      Tendsto
        (fun i => error i + 2 * μ.real (good i)ᶜ)
        l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      herror.add (hbad.const_mul 2)
  have hdist :
      Tendsto
        (fun i =>
          dist
            (∫ ω, Complex.exp
              (Complex.I * (X i ω : ℂ)) ∂μ)
            (∫ ω, Complex.exp
              (Complex.I * (Y i ω : ℂ)) ∂μ))
        l (𝓝 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun _ => dist_nonneg)
      _ hbound
    filter_upwards [herror_nonneg, hclose] with i hi hclosei
    rw [dist_eq_norm]
    exact norm_integral_exp_I_sub_le_error_add_bad
      μ (X i) (Y i) (hX i) (hY i)
      (good i) (hgood i) (error i) hi hclosei
  exact hXlim.congr_dist hdist

/-- The real scalar formed from a fixed finite family of true
resolvent Fourier coefficients. -/
def fullResolventReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) : ℝ :=
  measurableFredholmFiniteModeReal
    M ρ lam ε s modes c ω

/-- A finite real Fourier test of the true Fredholm resolvent is
measurable.  The underlying measurable potential realization agrees
almost surely with the samplewise mollified potential for `ε > 0`. -/
theorem measurable_fullResolventReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ) :
    Measurable
      (fullResolventReal M ρ lam ε s modes c) := by
  unfold fullResolventReal
  exact measurable_measurableFredholmFiniteModeReal
    M ρ lam ε s modes c

/-- Complete assembly interface: (3.24) controls the moving
parametrix, while the Step 2 good event transfers its characteristic
function to the true resolvent modes. -/
theorem Prop36.tendsto_fullResolventChar_of_second_moment_and_goodEvent
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (hP36 : Prop36 M ρ lam) (hlam : 0 < lam)
    (hsmall : hP36.boundConstant * lam < 1)
    (hsub : lam ^ 2 < 2 * Real.pi ^ 2)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (K q : ℝ) (hK : 0 ≤ K) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsecond :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ∀ j : Fin s, ∀ n : ℕ, 1 ≤ n → n ≤ truncOrder ε →
          MemLp
            (pmCoeff M ρ lam ε n
              (modes j).1 (modes j).2)
            2 (volume : Measure M.Ω) ∧
          ∫ ω,
              ‖pmCoeff M ρ lam ε n
                (modes j).1 (modes j).2 ω‖ ^ 2 ≤
            (‖(lamEps lam ε : ℂ)‖ * K * q ^ (n - 1)) ^ 2)
    (good : ℝ → Set M.Ω)
    (hgood : ∀ ε, MeasurableSet (good ε))
    (error : ℝ → ℝ)
    (herror_nonneg :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        0 ≤ error ε)
    (herror :
      Tendsto error
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (𝓝 0))
    (hbad :
      Tendsto (fun ε => (volume : Measure M.Ω).real (good ε)ᶜ)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (𝓝 0))
    (hclose :
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        ∀ ω ∈ good ε,
          ‖fullParametrixReal M ρ lam ε s modes c ω -
            fullResolventReal M ρ lam ε s modes c ω‖ ≤
          error ε) :
    Tendsto
      (fun ε => ∫ ω,
        Complex.exp
          (Complex.I *
            (fullResolventReal
              M ρ lam ε s modes c ω : ℂ)))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (𝓝 (Complex.exp (-((limitVar lam modes c : ℂ) / 2)))) := by
  apply tendsto_integral_exp_I_of_goodEvent_replace
    (volume : Measure M.Ω)
    (fun ε => fullParametrixReal M ρ lam ε s modes c)
    (fun ε => fullResolventReal M ρ lam ε s modes c)
    (hP36.tendsto_fullParametrixChar_of_geometric_second_moment_bound
      hlam hsmall hsub modes c K q hK hq0 hq1 hsecond)
    _ (fun ε =>
      (measurable_fullResolventReal
        M ρ lam ε s modes c).aemeasurable)
    good hgood error
    herror_nonneg herror hbad hclose
  intro ε
  change
    AEMeasurable
      (fixedTruncationReal
        M ρ lam ε (truncOrder ε) s modes c)
      (volume : Measure M.Ω)
  exact hP36.aemeasurable_fixedTruncationReal
    (truncOrder ε) modes c ε

/-- Restrict the positive-side characteristic-function limit to the
paper's `(0,1)` parameter range and present the real Gaussian
characteristic function in the exact form used by `MainStatement`. -/
theorem tendsto_fullResolventChar_on_Ioo_of_Ioi
    {M : NoiseModel} (ρ : SmoothCutoff) (lam : ℝ)
    {s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (h :
      Tendsto
        (fun ε => ∫ ω,
          Complex.exp
            (Complex.I *
              (fullResolventReal
                M ρ lam ε s modes c ω : ℂ)))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (𝓝 (Complex.exp
          (-((limitVar lam modes c : ℂ) / 2))))) :
    Tendsto
      (fun ε => ∫ ω,
        Complex.exp
          (Complex.I *
            (fullResolventReal
              M ρ lam ε s modes c ω : ℂ)))
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1))
      (𝓝 (((Real.exp
        (-(limitVar lam modes c) / 2) : ℝ) : ℂ))) := by
  have hsubset :
      Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi 0 :=
    fun _ hε => hε.1
  have hrestricted :=
    h.mono_left
      (nhdsWithin_mono 0 hsubset)
  rw [Complex.ofReal_exp]
  convert hrestricted using 1
  apply congrArg (fun z : ℂ => 𝓝 z)
  apply congrArg Complex.exp
  push_cast
  ring

end

end Anderson4D
