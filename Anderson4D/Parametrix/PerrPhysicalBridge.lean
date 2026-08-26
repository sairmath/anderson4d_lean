import Anderson4D.Parametrix.GradedIntegrability
import Anderson4D.Parametrix.IdentityGradedComparison
import Anderson4D.Parametrix.L2NeumannActionAll
import Anderson4D.Parametrix.L2Quantitative

/-!
# The physical/operator bridge for the finite parametrix

The pairing definition of the finite parametrix is convenient for the
probabilistic estimates, while inversion needs a bounded factor of the
form `Q * G`.  This file constructs that factor from the finite graded
resolvent words.  Every word is a finite product of bounded Green and
multiplication operators, so no inverse of the smoothing Green operator
is introduced.

The analytic comparison with the pairing expansion is deliberately kept
separate from the algebraic construction.  In particular, no pointwise
kernel realization is postulated at exceptional noise samples.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace PartialPairing

private theorem ae_coe_finsetSum_torusL2
    {ι : Type*} (s : Finset ι)
    (F : ι → TorusL2) :
    ∀ᵐ x ∂haarT4,
      ((((∑ i ∈ s, F i) : TorusL2) : T4 → ℂ) x) =
        ∑ i ∈ s, ((F i : TorusL2) : T4 → ℂ) x := by
  filter_upwards
    [Lp.coeFn_fun_finsetSum
      (μ := haarT4) s F] with x hx
  exact hx

/-! ## Bounded operators attached to graded words -/

/-- Continuous complex realization of one graded-word vertex weight. -/
def renormWordWeightContinuousMap
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (d : ℕ) : C(T4, ℂ) where
  toFun z := (renormWordWeight M ρ lam ε d z ω : ℂ)
  continuous_toFun := by
    apply Complex.continuous_ofReal.comp
    unfold renormWordWeight
    by_cases hd : d = 1
    · simp only [hd, if_true]
      exact continuous_const.mul hξ
    · simp only [hd, if_false]
      by_cases heven : Even d
      · rw [if_pos heven]
        exact continuous_const
      · rw [if_neg heven]
        exact continuous_const

@[simp]
theorem renormWordWeightContinuousMap_apply
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (d : ℕ) (z : T4) :
    renormWordWeightContinuousMap
        M ρ lam ε ω hξ d z =
      (renormWordWeight M ρ lam ε d z ω : ℂ) :=
  rfl

/-- The bounded factor represented by a graded word.  Multiplication by
`greenL2Op` on the right restores the final Green edge of the physical
kernel. -/
def renormWordL2Factor
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    List ℕ → TorusL2 →L[ℂ] TorusL2
  | [] => 1
  | d :: word =>
      Kop greenL2Op
          (continuousMultiplicationOp
            (renormWordWeightContinuousMap
              M ρ lam ε ω hξ d)) *
        renormWordL2Factor M ρ lam ε ω hξ word

/-- The order-`n` bounded factor, summed over all compositions of the
graded order. -/
def gradedParametrixL2FactorOrder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  ∑ c : Composition n,
    renormWordL2Factor M ρ lam ε ω hξ c.blocks

/-- The finite factorized parametrix through graded order `A`. -/
def gradedTruncatedParametrixL2Factor
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (A : ℕ) : TorusL2 →L[ℂ] TorusL2 :=
  ∑ n ∈ Finset.range (A + 1),
    gradedParametrixL2FactorOrder
      M ρ lam ε ω hξ n

/-! ## Word actions on Fourier characters -/

/-- Continuous representative of a graded word acting on a Fourier
character after its final Green factor is restored. -/
def renormWordContinuousAction
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) : List ℕ → C(T4, ℂ)
  | [] => greenPhysicalConvolution (charT4Continuous β)
  | d :: word =>
      greenPhysicalConvolution
        (renormWordWeightContinuousMap
            M ρ lam ε ω hξ d *
          renormWordContinuousAction
            M ρ lam ε ω hξ β word)

/-- Exact `L²` realization of the recursive continuous word action. -/
theorem renormWordL2Factor_mul_green_apply_char
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (word : List ℕ) :
    (renormWordL2Factor M ρ lam ε ω hξ word *
        greenL2Op) (charT4Lp 2 β) =
      ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ
        (renormWordContinuousAction
          M ρ lam ε ω hξ β word) := by
  induction word with
  | nil =>
      simpa [renormWordL2Factor,
        renormWordContinuousAction] using
        greenL2Op_continuousMap (charT4Continuous β)
  | cons d word ih =>
      simp only [renormWordL2Factor,
        renormWordContinuousAction, Kop,
        mul_assoc, mul_apply_eq_comp]
      have ihApply :
          renormWordL2Factor M ρ lam ε ω hξ word
              (greenL2Op (charT4Lp 2 β)) =
            ContinuousMap.toLp (E := ℂ) 2 haarT4 ℂ
              (renormWordContinuousAction
                M ρ lam ε ω hξ β word) := by
        simpa only [mul_apply_eq_comp] using ih
      rw [ihApply, continuousMultiplicationOp_toLp]
      exact greenL2Op_continuousMap _

/-- Vertex weights for the flat path attached to one graded word.  The
last vertex carries the input character. -/
def renormWordActionPathWeight
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) :
    (word : List ℕ) → Fin (word.length + 1) → C(T4, ℂ)
  | [], _ => charT4Continuous β
  | d :: word, i =>
      Fin.cases
        (renormWordWeightContinuousMap
          M ρ lam ε ω hξ d)
        (renormWordActionPathWeight
          M ρ lam ε ω hξ β word)
        i

@[simp]
theorem renormWordActionPathWeight_cons_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (d : ℕ) (word : List ℕ) :
    renormWordActionPathWeight
        M ρ lam ε ω hξ β (d :: word) 0 =
      renormWordWeightContinuousMap
        M ρ lam ε ω hξ d := by
  rfl

@[simp]
theorem renormWordActionPathWeight_cons_succ
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (d : ℕ) (word : List ℕ)
    (i : Fin (word.length + 1)) :
    renormWordActionPathWeight
        M ρ lam ε ω hξ β (d :: word) i.succ =
      renormWordActionPathWeight
        M ρ lam ε ω hξ β word i := by
  rfl

theorem weightedGreenPath_renormWord_cons
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (d : ℕ) (word : List ℕ)
    (x z : T4) (v : Fin (word.length + 1) → T4) :
    weightedGreenPath
        (renormWordActionPathWeight
          M ρ lam ε ω hξ β (d :: word))
        x (Fin.cons z v) =
      (greenFn (x - z) : ℂ) *
        renormWordWeightContinuousMap
          M ρ lam ε ω hξ d z *
        weightedGreenPath
          (renormWordActionPathWeight
            M ρ lam ε ω hξ β word)
          z v := by
  rw [weightedGreenPath_succ]
  simp

/-- Every recursive word action is its flat weighted Green path for
almost every left endpoint. -/
theorem renormWordContinuousAction_eq_weightedGreenPath_ae
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (word : List ℕ) :
    ∀ᵐ x ∂paperMeasure,
      renormWordContinuousAction
          M ρ lam ε ω hξ β word x =
        ∫ v : Fin (word.length + 1) → T4,
          weightedGreenPath
            (renormWordActionPathWeight
              M ρ lam ε ω hξ β word)
            x v
          ∂(Measure.pi fun _ => paperMeasure) := by
  induction word with
  | nil =>
      filter_upwards
        [ae_integrable_weightedGreenPath
          (renormWordActionPathWeight
            M ρ lam ε ω hξ β [])] with x hpath
      rw [renormWordContinuousAction,
        greenPhysicalConvolution_apply]
      simp only [List.length_nil]
      rw [integral_pathHeadTail 0 _ hpath]
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_unique]
      have hmass :
          (Measure.pi fun _ : Fin 0 =>
            paperMeasure).real Set.univ = 1 := by
        rw [measureReal_def, Measure.pi_empty_univ]
        simp
      rw [hmass, one_smul]
      simp [weightedGreenPath,
        renormWordActionPathWeight]
  | cons d word ih =>
      filter_upwards
        [ae_integrable_weightedGreenPath
          (renormWordActionPathWeight
            M ρ lam ε ω hξ β (d :: word))] with
          x hpath
      rw [renormWordContinuousAction,
        greenPhysicalConvolution_apply]
      simp only [List.length_cons]
      rw [integral_pathHeadTail
        (word.length + 1) _ hpath]
      apply integral_congr_ae
      filter_upwards [ih] with z hz
      simp only [ContinuousMap.mul_apply]
      rw [hz]
      calc
        (greenFn (x - z) : ℂ) *
              ((renormWordWeightContinuousMap
                  M ρ lam ε ω hξ d) z *
                ∫ v : Fin (word.length + 1) → T4,
                  weightedGreenPath
                    (renormWordActionPathWeight
                      M ρ lam ε ω hξ β word)
                    z v
                  ∂(Measure.pi fun _ => paperMeasure)) =
            ((greenFn (x - z) : ℂ) *
              (renormWordWeightContinuousMap
                M ρ lam ε ω hξ d) z) *
              ∫ v : Fin (word.length + 1) → T4,
                weightedGreenPath
                  (renormWordActionPathWeight
                    M ρ lam ε ω hξ β word)
                  z v
                ∂(Measure.pi fun _ => paperMeasure) := by ring
        _ =
            ∫ v : Fin (word.length + 1) → T4,
              ((greenFn (x - z) : ℂ) *
                (renormWordWeightContinuousMap
                  M ρ lam ε ω hξ d) z) *
                weightedGreenPath
                  (renormWordActionPathWeight
                    M ρ lam ε ω hξ β word)
                  z v
              ∂(Measure.pi fun _ => paperMeasure) := by
                rw [integral_const_mul]
        _ =
            ∫ v : Fin (word.length + 1) → T4,
              weightedGreenPath
                (renormWordActionPathWeight
                  M ρ lam ε ω hξ β (d :: word))
                x (Fin.cons z v)
              ∂(Measure.pi fun _ => paperMeasure) := by
                apply integral_congr_ae
                filter_upwards with v
                exact
                  (weightedGreenPath_renormWord_cons
                    M ρ lam ε ω hξ β d word x z v).symm

/-! ## Identification with the graded-word kernels -/

/-- Complex form of a graded-word kernel.  This is definitionally the
same integral as `renormWordKernel`, with the real integrand embedded in
`ℂ`. -/
def renormWordKernelC
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (word : List ℕ)
    (x y : T4) (ω : M.Ω) : ℂ :=
  ∫ v : Fin word.length → T4,
    (renormWordIntegrandOnTuple
      M ρ lam ε word (assemble x y v) ω : ℂ)
    ∂(Measure.pi fun _ => paperMeasure)

theorem renormWordKernelC_eq_ofReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (word : List ℕ)
    (x y : T4) (ω : M.Ω) :
    renormWordKernelC M ρ lam ε word x y ω =
      (renormWordKernel M ρ lam ε word x y ω : ℂ) := by
  unfold renormWordKernelC renormWordKernel
  exact integral_complex_ofReal

/-- Complex kernel of the order-`n` graded parametrix. -/
def gradedParametrixKernelC
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℂ :=
  ∑ c : Composition n,
    renormWordKernelC M ρ lam ε c.blocks x y ω

theorem gradedParametrixKernelC_eq_ofReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) :
    gradedParametrixKernelC M ρ lam ε n x y ω =
      (gradedParametrix M ρ lam ε n x y ω : ℂ) := by
  unfold gradedParametrixKernelC gradedParametrix
  simp_rw [renormWordKernelC_eq_ofReal]
  push_cast
  rfl

/-- Flat complex integrand of one word acting on a Fourier character. -/
def renormWordFlatActionIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω) (β : Z4) (word : List ℕ)
    (x y : T4) (v : Fin word.length → T4) : ℂ :=
  (renormWordIntegrandOnTuple
      M ρ lam ε word (assemble x y v) ω : ℂ) *
    charT4 β y

private theorem snoc_cons_word
    {n : ℕ}
    (z : T4) (v : Fin n → T4) (y : T4) :
    (Fin.snoc
        (Fin.cons z v : Fin (n + 1) → T4) y :
      Fin (n + 2) → T4) =
      Fin.cons z
        (Fin.snoc v y : Fin (n + 1) → T4) :=
  (Fin.cons_snoc_eq_snoc_cons z v y).symm

/-- Separating the terminal path vertex produces exactly the word
kernel integrand times the input character. -/
theorem weightedGreenPath_renormWord_snoc
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (word : List ℕ)
    (x y : T4) (v : Fin word.length → T4) :
    weightedGreenPath
        (renormWordActionPathWeight
          M ρ lam ε ω hξ β word)
        x (Fin.snoc v y) =
      renormWordFlatActionIntegrand
        M ρ lam ε ω β word x y v := by
  induction word generalizing x with
  | nil =>
      have hv :
          v = fun i : Fin 0 => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      subst v
      rw [Fin.snoc_zero]
      simp [renormWordFlatActionIntegrand,
        renormWordIntegrandOnTuple,
        weightedGreenPath,
        renormWordActionPathWeight,
        assemble]
  | cons d word ih =>
      rw [← Fin.cons_self_tail v]
      rw [snoc_cons_word]
      rw [weightedGreenPath_renormWord_cons]
      rw [ih]
      unfold renormWordFlatActionIntegrand
      rw [renormWordIntegrandOnTuple_cons]
      push_cast
      rw [renormWordWeightContinuousMap_apply]
      ring

/-- A.e. kernel form of a bounded graded-word factor followed by the
final Green operator. -/
theorem renormWordL2Factor_mul_green_apply_char_ae
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (word : List ℕ) :
    (renormWordL2Factor M ρ lam ε ω hξ word *
        greenL2Op) (charT4Lp 2 β) =ᵐ[haarT4]
      fun x =>
        ∫ y : T4,
          renormWordKernelC
              M ρ lam ε word x y ω *
            charT4 β y
          ∂paperMeasure := by
  rw [renormWordL2Factor_mul_green_apply_char]
  have hhaarPaper : haarT4 ≪ paperMeasure := by
    unfold paperMeasure
    exact Measure.absolutelyContinuous_smul
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := 2) (μ := haarT4) (𝕜 := ℂ)
      (renormWordContinuousAction
        M ρ lam ε ω hξ β word),
    hhaarPaper.ae_le
      (renormWordContinuousAction_eq_weightedGreenPath_ae
        M ρ lam ε ω hξ β word),
    hhaarPaper.ae_le
      (ae_integrable_weightedGreenPath
        (renormWordActionPathWeight
          M ρ lam ε ω hξ β word))] with
      x hcoe haction hpath
  rw [hcoe, haction]
  rw [integral_pathLast word.length _ hpath]
  apply integral_congr_ae
  filter_upwards with y
  unfold renormWordKernelC
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with v
  exact
    weightedGreenPath_renormWord_snoc
      M ρ lam ε ω hξ β word x y v

/-- For almost every left endpoint, the word kernel acting on one
Fourier character is integrable in the right endpoint. -/
theorem ae_integrable_renormWordKernelC_mul_char
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (word : List ℕ) :
    ∀ᵐ x ∂paperMeasure,
      Integrable
        (fun y : T4 =>
          renormWordKernelC
              M ρ lam ε word x y ω *
            charT4 β y)
        paperMeasure := by
  have hjoint :=
    integrable_renormWordIntegrandOnTuple_global
      M ρ lam ε ω hξ word
  filter_upwards [hjoint.prod_right_ae] with x hx
  have houter :
      Integrable
        (fun y : T4 =>
          ∫ v : Fin word.length → T4,
            (renormWordIntegrandOnTuple
              M ρ lam ε word
                (assemble x y v) ω : ℂ)
            ∂(Measure.pi fun _ => paperMeasure))
        paperMeasure :=
    hx.integral_prod_left
  unfold renormWordKernelC
  exact houter.mul_bdd
    (charT4Continuous β).continuous.aestronglyMeasurable
    (ae_of_all paperMeasure fun y => by
      rw [norm_charT4])

/-- A.e. kernel action of one complete graded order. -/
theorem gradedParametrixL2FactorOrder_mul_green_apply_char_ae
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (β : Z4) (n : ℕ) :
    (gradedParametrixL2FactorOrder
          M ρ lam ε ω hξ n *
        greenL2Op) (charT4Lp 2 β) =ᵐ[haarT4]
      fun x =>
        ∫ y : T4,
          gradedParametrixKernelC
              M ρ lam ε n x y ω *
            charT4 β y
          ∂paperMeasure := by
  classical
  unfold gradedParametrixL2FactorOrder
  rw [Finset.sum_mul]
  have hhaarPaper : haarT4 ≪ paperMeasure := by
    unfold paperMeasure
    exact Measure.absolutelyContinuous_smul
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  filter_upwards
    [ae_coe_finsetSum_torusL2
      (Finset.univ : Finset (Composition n))
      (fun c =>
        (renormWordL2Factor
            M ρ lam ε ω hξ c.blocks *
          greenL2Op) (charT4Lp 2 β)),
    Filter.eventually_all_finset
      (Finset.univ : Finset (Composition n)) |>.2
        (fun c _ =>
          renormWordL2Factor_mul_green_apply_char_ae
            M ρ lam ε ω hξ β c.blocks),
    Filter.eventually_all_finset
      (Finset.univ : Finset (Composition n)) |>.2
        (fun c _ =>
          hhaarPaper.ae_le
            (ae_integrable_renormWordKernelC_mul_char
              M ρ lam ε ω hξ β c.blocks))] with
      x hcoe hx hint
  calc
    ((((∑ c : Composition n,
            renormWordL2Factor M ρ lam ε ω hξ c.blocks *
              greenL2Op) (charT4Lp 2 β) : TorusL2) :
          T4 → ℂ) x) =
        ∑ c : Composition n,
          ((((renormWordL2Factor
                  M ρ lam ε ω hξ c.blocks *
                greenL2Op) (charT4Lp 2 β) : TorusL2) :
            T4 → ℂ) x) := by
      rw [_root_.sum_apply]
      exact hcoe
    _ =
        ∑ c : Composition n,
          ∫ y : T4,
            renormWordKernelC
                M ρ lam ε c.blocks x y ω *
              charT4 β y
            ∂paperMeasure := by
      exact Finset.sum_congr rfl fun c _ =>
        hx c (Finset.mem_univ c)
    _ =
        ∫ y : T4,
          ∑ c : Composition n,
            renormWordKernelC
                M ρ lam ε c.blocks x y ω *
              charT4 β y
          ∂paperMeasure := by
      symm
      exact integral_finsetSum Finset.univ
        (fun c _ => hint c (Finset.mem_univ c))
    _ =
        ∫ y : T4,
          gradedParametrixKernelC
              M ρ lam ε n x y ω *
            charT4 β y
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      unfold gradedParametrixKernelC
      rw [Finset.sum_mul]

/-! ## Fourier coefficients and the physical operator -/

/-- Bounded operators on `TorusL2` are determined by all their Fourier
matrix coefficients. -/
theorem torusL2Operator_ext_of_matrixCoeff
    {A B : TorusL2 →L[ℂ] TorusL2}
    (hcoeff :
      ∀ α β,
        torusFourierMatrixCoeff A α β =
          torusFourierMatrixCoeff B α β) :
    A = B := by
  have hbasis :
      ∀ β : Z4,
        A (torusFourierBasis β) =
          B (torusFourierBasis β) := by
    intro β
    apply torusFourierBasis.repr.injective
    ext k
    simpa only [torusFourierBasis.repr_apply_apply,
      torusFourierMatrixCoeff, neg_neg] using
      hcoeff (-k) β
  let S : Submodule ℂ TorusL2 :=
    Submodule.span ℂ (Set.range torusFourierBasis)
  have heqOn : Set.EqOn A B (S : Set TorusL2) := by
    intro f hf
    change f ∈ Submodule.span ℂ
      (Set.range torusFourierBasis) at hf
    refine Submodule.span_induction
      (p := fun f _ => A f = B f) ?_ ?_ ?_ ?_ hf
    · intro f hfRange
      rcases hfRange with ⟨k, rfl⟩
      exact hbasis k
    · simp
    · intro f g _hf _hg hfEq hgEq
      simp only [map_add, hfEq, hgEq]
    · intro c f _hf hfEq
      simp only [map_smul, hfEq]
  have hclosure :
      S.topologicalClosure = ⊤ := by
    exact torusFourierBasis.dense_span
  have hdense : Dense (S : Set TorusL2) := by
    rw [dense_iff_closure_eq]
    exact congrArg SetLike.coe hclosure
  exact ContinuousLinearMap.ext fun f =>
    congrFun
      (Continuous.ext_on hdense
        A.continuous B.continuous heqOn) f

/-- Fourier coefficient of one bounded graded order after restoring the
final Green edge. -/
theorem torusFourierMatrixCoeff_gradedParametrixL2FactorOrder_mul_green
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (n : ℕ) (α β : Z4) :
    torusFourierMatrixCoeff
        (gradedParametrixL2FactorOrder
            M ρ lam ε ω hξ n *
          greenL2Op) α β =
      (paperTorusVolume : ℂ)⁻¹ *
        paperKernelCoeff
          (fun x y =>
            gradedParametrixKernelC
              M ρ lam ε n x y ω)
          α β := by
  have hinner :=
    inner_eq_volume_inv_mul_paperKernelCoeff_of_action
      (gradedParametrixL2FactorOrder
          M ρ lam ε ω hξ n *
        greenL2Op)
      (fun x y =>
        gradedParametrixKernelC
          M ρ lam ε n x y ω)
      α β
      (gradedParametrixL2FactorOrder_mul_green_apply_char_ae
        M ρ lam ε ω hξ β n)
  have hchar (k : Z4) :
      torusFourierBasis k = charT4Lp 2 k :=
    congrFun coe_torusFourierBasis k
  unfold torusFourierMatrixCoeff
  rw [hchar (-α), hchar β]
  exact hinner

/-- The sole coefficient-level analytic bridge between the pairing
parametrix used by P-3.5b and the graded word expansion used by the
bounded operator algebra.  It asks only for the integrated coefficients,
not for a false all-endpoint kernel identity. -/
def ParametrixGradedCoefficientAgreement
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω) : Prop :=
  ∀ n, n ≤ A → ∀ α β,
    paperKernelCoeff
        (fun x y =>
          gradedParametrixKernelC
            M ρ lam ε n x y ω)
        α β =
      pmCoeff M ρ lam ε n α β ω

/-- At a sample where the integrated pairing/graded comparison holds,
the bounded graded construction equals the canonical coefficient
operator at each positive order. -/
theorem gradedParametrixL2FactorOrder_mul_green_eq_canonical
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A n : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (hn : n ≤ A)
    (hagree :
      ParametrixGradedCoefficientAgreement
        M ρ lam ε A ω)
    (hcanonical :
      ∀ α β,
        torusFourierMatrixCoeff
            (canonicalParametrixOrderL2Operator
              M ρ lam ε n ω) α β =
          (paperTorusVolume : ℂ)⁻¹ *
            pmCoeff M ρ lam ε n α β ω) :
    gradedParametrixL2FactorOrder
          M ρ lam ε ω hξ n *
        greenL2Op =
      canonicalParametrixOrderL2Operator
        M ρ lam ε n ω := by
  apply torusL2Operator_ext_of_matrixCoeff
  intro α β
  rw [
    torusFourierMatrixCoeff_gradedParametrixL2FactorOrder_mul_green,
    hagree n hn α β,
    hcanonical α β]

/-- The zeroth graded factor is the identity operator. -/
theorem gradedParametrixL2FactorOrder_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω)) :
    gradedParametrixL2FactorOrder
        M ρ lam ε ω hξ 0 = 1 := by
  unfold gradedParametrixL2FactorOrder
  have hblocks :
      ∀ c : Composition 0, c.blocks = [] :=
    fun c => (Composition.blocks_eq_nil c).mpr rfl
  calc
    (∑ c : Composition 0,
        renormWordL2Factor
          M ρ lam ε ω hξ c.blocks) =
        ∑ _c : Composition 0,
          (1 : TorusL2 →L[ℂ] TorusL2) := by
      apply Fintype.sum_congr
      intro c
      rw [hblocks c]
      rfl
    _ = 1 := by simp [composition_card]

/-- The `Fin`-indexed physical truncation is the Green operator plus
its positive canonical orders. -/
theorem canonicalPhysicalTruncatedParametrixL2Operator_eq
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω) :
    canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω =
      greenL2Op +
        ∑ n ∈ Finset.range A,
          canonicalParametrixOrderL2Operator
            M ρ lam ε (n + 1) ω := by
  unfold canonicalPhysicalTruncatedParametrixL2Operator
  rw [Fin.sum_univ_succ]
  unfold canonicalPhysicalParametrixL2Piece
  simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ,
    Nat.succ_ne_zero]
  rw [Fin.sum_univ_eq_sum_range
    (fun n =>
      canonicalParametrixOrderL2Operator
        M ρ lam ε (n + 1) ω) A]

/-- **Actual physical bridge.**  The finite graded factor followed by
`G` is exactly the canonical bounded operator built from the P-3.5b
Fourier coefficients.  The hypotheses are samplewise versions of the
two honest a.e. coefficient facts; no arbitrary realization operator is
quantified. -/
theorem gradedTruncatedParametrixL2Factor_mul_green_eq_canonical
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω)
    (hξ : Continuous (M.xiEps ρ ε ω))
    (hagree :
      ParametrixGradedCoefficientAgreement
        M ρ lam ε A ω)
    (hcanonical :
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        torusFourierMatrixCoeff
            (canonicalParametrixOrderL2Operator
              M ρ lam ε n ω) α β =
          (paperTorusVolume : ℂ)⁻¹ *
            pmCoeff M ρ lam ε n α β ω) :
    gradedTruncatedParametrixL2Factor
          M ρ lam ε ω hξ A *
        greenL2Op =
      canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω := by
  unfold gradedTruncatedParametrixL2Factor
  rw [Finset.sum_mul]
  rw [canonicalPhysicalTruncatedParametrixL2Operator_eq]
  rw [Finset.sum_range_succ']
  rw [gradedParametrixL2FactorOrder_zero]
  rw [one_mul, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnlt : n < A := Finset.mem_range.mp hn
  exact
    gradedParametrixL2FactorOrder_mul_green_eq_canonical
      M ρ lam ε A (n + 1) ω hξ (by omega)
      hagree
      (hcanonical (n + 1) (by omega) (by omega))

/-! ## Canonical random factor and concrete P-err residuals -/

/-- Proof-independent totalization of the graded bounded factor.
Continuity of the mollified noise holds almost surely at positive
scale; the zero branch is used only on the exceptional set. -/
def canonicalGradedTruncatedParametrixL2Factor
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 := by
  classical
  exact fun ω =>
    if hξ : Continuous (M.xiEps ρ ε ω) then
      gradedTruncatedParametrixL2Factor
        M ρ lam ε ω hξ A
    else 0

/-- The concrete right P-err residual for the bounded factorized
Anderson operator. -/
def canonicalPerrRightRemainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  fun ω =>
    (1 - Kop greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)) *
      canonicalGradedTruncatedParametrixL2Factor
        M ρ lam ε A ω -
      1

/-- The concrete left P-err residual. -/
def canonicalPerrLeftRemainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  fun ω =>
    canonicalGradedTruncatedParametrixL2Factor
        M ρ lam ε A ω *
      (1 - Kop greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)) -
      1

/-- Physical form of the right factor residual after restoring the
final Green operator. -/
def canonicalPerrRightPhysicalRemainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  fun ω =>
    (1 - Kop greenL2Op
        (mollifiedPotentialL2Op M ρ lam ε ω)) *
      canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω -
      greenL2Op

/-- Physical form of the left factor residual.  The right
preconditioner is `1 - M G`, as forced by associativity from
`Q (1 - G M) G`. -/
def canonicalPerrLeftPhysicalRemainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) :
    M.Ω → TorusL2 →L[ℂ] TorusL2 :=
  fun ω =>
    canonicalPhysicalTruncatedParametrixL2Operator
        M ρ lam ε A ω *
      (1 -
        mollifiedPotentialL2Op M ρ lam ε ω *
          greenL2Op) -
      greenL2Op

/-- Restoring the final Green edge turns the factor right residual into
the corresponding physical preconditioned residual. -/
theorem canonicalPerrRightRemainder_mul_green_eq_physical
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω)
    (hbridge :
      canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε A ω *
          greenL2Op =
        canonicalPhysicalTruncatedParametrixL2Operator
          M ρ lam ε A ω) :
    canonicalPerrRightRemainder
          M ρ lam ε A ω *
        greenL2Op =
      canonicalPerrRightPhysicalRemainder
        M ρ lam ε A ω := by
  unfold canonicalPerrRightRemainder
  unfold canonicalPerrRightPhysicalRemainder
  rw [sub_mul, one_mul, mul_assoc, hbridge]

/-- Restoring the final Green edge turns the factor left residual into
the physical right-preconditioned residual. -/
theorem canonicalPerrLeftRemainder_mul_green_eq_physical
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω)
    (hbridge :
      canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε A ω *
          greenL2Op =
        canonicalPhysicalTruncatedParametrixL2Operator
          M ρ lam ε A ω) :
    canonicalPerrLeftRemainder
          M ρ lam ε A ω *
        greenL2Op =
      canonicalPerrLeftPhysicalRemainder
        M ρ lam ε A ω := by
  unfold canonicalPerrLeftRemainder
  unfold canonicalPerrLeftPhysicalRemainder
  unfold Kop
  calc
    (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε A ω *
          (1 -
            greenL2Op *
              mollifiedPotentialL2Op
                M ρ lam ε ω) -
        1) * greenL2Op =
        canonicalGradedTruncatedParametrixL2Factor
              M ρ lam ε A ω *
            greenL2Op -
          (canonicalGradedTruncatedParametrixL2Factor
                M ρ lam ε A ω *
              greenL2Op) *
            mollifiedPotentialL2Op
              M ρ lam ε ω *
            greenL2Op -
          greenL2Op := by noncomm_ring
    _ =
        canonicalPhysicalTruncatedParametrixL2Operator
              M ρ lam ε A ω -
          canonicalPhysicalTruncatedParametrixL2Operator
              M ρ lam ε A ω *
            mollifiedPotentialL2Op
              M ρ lam ε ω *
            greenL2Op -
          greenL2Op := by rw [hbridge]
    _ =
        canonicalPhysicalTruncatedParametrixL2Operator
              M ρ lam ε A ω *
            (1 -
              mollifiedPotentialL2Op
                  M ρ lam ε ω *
                greenL2Op) -
          greenL2Op := by noncomm_ring

/-- The two factorized P-err identities hold for the canonical
construction at every sample.  This theorem contains no norm estimate:
identifying and estimating the displayed residuals is the remaining
analytic P-err task. -/
theorem canonicalPerr_andersonParametrixData
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (ω : M.Ω) :
    AndersonParametrixData
      greenL2Op
      (mollifiedPotentialL2Op M ρ lam ε ω)
      (canonicalGradedTruncatedParametrixL2Factor
        M ρ lam ε A ω)
      (canonicalPerrLeftRemainder
        M ρ lam ε A ω)
      (canonicalPerrRightRemainder
        M ρ lam ε A ω) := by
  constructor
  · unfold canonicalPerrRightRemainder
    noncomm_ring
  · unfold canonicalPerrLeftRemainder
    noncomm_ring

/-- P-3.5b supplies the canonical positive-order coefficient identities
simultaneously through every finite truncation order. -/
theorem ae_canonicalParametrixOrderL2Operator_coeff_of_momentBounds
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ A →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
        torusFourierMatrixCoeff
            (canonicalParametrixOrderL2Operator
              M ρ lam ε n ω) α β =
          (paperTorusVolume : ℂ)⁻¹ *
            pmCoeff M ρ lam ε n α β ω := by
  have hall :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ∀ n ∈ Finset.Icc 1 A, ∀ α β,
          torusFourierMatrixCoeff
              (canonicalParametrixOrderL2Operator
                M ρ lam ε n ω) α β =
            (paperTorusVolume : ℂ)⁻¹ *
              pmCoeff M ρ lam ε n α β ω :=
    (Filter.eventually_all_finset
      (Finset.Icc 1 A)).2 fun n hn =>
        canonicalParametrixOrderL2Operator_realizes
          (hfubini n (Finset.mem_Icc.mp hn).1
            (Finset.mem_Icc.mp hn).2)
          (hwick n (Finset.mem_Icc.mp hn).1
            (Finset.mem_Icc.mp hn).2)
          (hdet n (Finset.mem_Icc.mp hn).1
            (Finset.mem_Icc.mp hn).2)
          houter hpower hlam hε hεle
  filter_upwards [hall] with ω hω
  intro n hn hna
  exact hω n (Finset.mem_Icc.mpr ⟨hn, hna⟩)

/-- Almost-sure physical bridge for the proof-independent canonical
factor. -/
theorem ae_canonicalGradedTruncatedParametrixL2Factor_mul_green_eq
    {M : NoiseModel} {ρ : SmoothCutoff}
    {lam ε : ℝ} {A : ℕ}
    (hε : 0 < ε)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω)
    (hcanonical :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
          torusFourierMatrixCoeff
              (canonicalParametrixOrderL2Operator
                M ρ lam ε n ω) α β =
            (paperTorusVolume : ℂ)⁻¹ *
              pmCoeff M ρ lam ε n α β ω) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε A ω *
          greenL2Op =
        canonicalPhysicalTruncatedParametrixL2Operator
          M ρ lam ε A ω := by
  filter_upwards
    [M.ae_continuous_xiEps ρ hε,
      hagree, hcanonical] with
      ω hξ hagreeω hcanonicalω
  unfold canonicalGradedTruncatedParametrixL2Factor
  rw [dif_pos hξ]
  exact
    gradedTruncatedParametrixL2Factor_mul_green_eq_canonical
      M ρ lam ε A ω hξ hagreeω hcanonicalω

/-- Both concrete factor residuals agree almost surely with their
physical preconditioned forms.  These are the bounded-operator versions
of paper (3.20)--(3.21); identifying the physical forms with the
explicit boundary kernels is the remaining kernel-realization step. -/
theorem ae_canonicalPerrRemainders_mul_green_eq_physical
    {M : NoiseModel} {ρ : SmoothCutoff}
    {lam ε : ℝ} {A : ℕ}
    (hε : 0 < ε)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω)
    (hcanonical :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ∀ n, 1 ≤ n → n ≤ A → ∀ α β,
          torusFourierMatrixCoeff
              (canonicalParametrixOrderL2Operator
                M ρ lam ε n ω) α β =
            (paperTorusVolume : ℂ)⁻¹ *
              pmCoeff M ρ lam ε n α β ω) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      canonicalPerrRightRemainder
            M ρ lam ε A ω *
          greenL2Op =
        canonicalPerrRightPhysicalRemainder
            M ρ lam ε A ω ∧
      canonicalPerrLeftRemainder
            M ρ lam ε A ω *
          greenL2Op =
        canonicalPerrLeftPhysicalRemainder
          M ρ lam ε A ω := by
  filter_upwards
    [ae_canonicalGradedTruncatedParametrixL2Factor_mul_green_eq
      hε hagree hcanonical] with ω hbridge
  exact ⟨
    canonicalPerrRightRemainder_mul_green_eq_physical
      M ρ lam ε A ω hbridge,
    canonicalPerrLeftRemainder_mul_green_eq_physical
      M ρ lam ε A ω hbridge⟩

/-- The arbitrary `Qfactor/Rleft/Rright` validity interface is
discharged for the canonical construction.  The only analytic bridge
left is the integrated pairing/graded coefficient agreement. -/
theorem ae_canonicalFactorizedParametrixValid
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ A →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω) :
    ∀ᵐ ω ∂(volume : Measure M.Ω),
      canonicalFactorizedParametrixValid
        M ρ lam ε A
        (canonicalGradedTruncatedParametrixL2Factor
          M ρ lam ε A)
        (canonicalPerrLeftRemainder
          M ρ lam ε A)
        (canonicalPerrRightRemainder
          M ρ lam ε A)
        ω := by
  have hcanonical :=
    ae_canonicalParametrixOrderL2Operator_coeff_of_momentBounds
      hfubini hwick hdet
      houter hpower hlam hε hεle
  have hbridge :=
    ae_canonicalGradedTruncatedParametrixL2Factor_mul_green_eq
      hε hagree hcanonical
  filter_upwards [hbridge] with ω hbridgeω
  exact ⟨
    canonicalPerr_andersonParametrixData
      M ρ lam ε A ω,
    hbridgeω⟩

/-- Exceptional-set estimate with the canonical factor and P-err
residuals, eliminating the former arbitrary validity hypothesis. -/
theorem measureReal_compl_canonicalConstructedL2ParametrixGoodEvent_le
    {M : NoiseModel} {ρ : SmoothCutoff}
    {outerConstant powerConstant lam ε : ℝ}
    {A : ℕ}
    (hfubini :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        PmCoeffMomentFubiniOutput
          M ρ lam ε m α β)
    (hwick :
      ∀ m, 1 ≤ m → m ≤ A →
        WickAtSecondMomentLaw M ρ ε m)
    (hdet :
      ∀ m, 1 ≤ m → m ≤ A → ∀ α β,
        ‖deterministicMomentPairingSum
            ρ lam ε m α β‖ ≤
          deterministicMomentRHS
            outerConstant powerConstant lam ε m α β)
    (houter : 0 ≤ outerConstant)
    (hpower : 0 ≤ powerConstant)
    (hlam : 0 ≤ lam)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hagree :
      ∀ᵐ ω ∂(volume : Measure M.Ω),
        ParametrixGradedCoefficientAgreement
          M ρ lam ε A ω)
    (hintR :
      Integrable
        (fun ω =>
          ‖canonicalPerrLeftRemainder
              M ρ lam ε A ω‖ +
            ‖canonicalPerrRightRemainder
              M ρ lam ε A ω‖)
        (volume : Measure M.Ω))
    (δR : ℝ)
    (hfirstR :
      (∫ ω,
          ‖canonicalPerrLeftRemainder
              M ρ lam ε A ω‖ +
            ‖canonicalPerrRightRemainder
              M ρ lam ε A ω‖
        ∂(volume : Measure M.Ω)) ≤ δR) :
    (volume : Measure M.Ω).real
        (canonicalL2ParametrixGoodEvent
          M ρ lam ε A
          (canonicalGradedTruncatedParametrixL2Factor
            M ρ lam ε A)
          (canonicalPerrLeftRemainder
            M ρ lam ε A)
          (canonicalPerrRightRemainder
            M ρ lam ε A))ᶜ ≤
      canonicalPhysicalTruncatedParametrixL2SecondMomentBudget
          outerConstant powerConstant lam ε A /
        (ε ^ (-14 : ℤ)) ^ 2 +
      δR / ε ^ 28 := by
  exact
    measureReal_compl_canonicalL2ParametrixGoodEvent_le
      (canonicalGradedTruncatedParametrixL2Factor
        M ρ lam ε A)
      (canonicalPerrLeftRemainder
        M ρ lam ε A)
      (canonicalPerrRightRemainder
        M ρ lam ε A)
      hfubini hwick hdet
      houter hpower hlam hε hεle
      hintR δR hfirstR
      (ae_canonicalFactorizedParametrixValid
        hfubini hwick hdet
        houter hpower hlam hε hεle hagree)

end PartialPairing

end

end Anderson4D
