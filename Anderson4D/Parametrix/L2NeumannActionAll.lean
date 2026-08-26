import Anderson4D.Parametrix.ChainIntegrability
import Anderson4D.Parametrix.L2NeumannAction

/-!
# All-order flat realization of the physical Neumann action

`L2NeumannAction.lean` constructs every operator power by recursive Green
convolution and checks the first nontrivial flat chain.  Here the reusable
weighted-path integrability theorem closes the Fubini induction at every
order.  The equality is correctly stated almost everywhere in the left
endpoint: a fixed-endpoint flat chain may fail to be integrable on a
diagonal, while its joint integrand is integrable and therefore has
integrable sections almost everywhere.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- The vertex weights of the order-`n` physical Neumann action: the
first `n` vertices carry the continuous multiplier and the last vertex
carries the input Fourier character. -/
def neumannActionPathWeight
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    Fin (n + 1) → C(T4, ℂ) :=
  Fin.lastCases (charT4Continuous β) (fun _ => m)

@[simp]
theorem neumannActionPathWeight_last
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    neumannActionPathWeight m β n (Fin.last n) =
      charT4Continuous β := by
  simp [neumannActionPathWeight]

@[simp]
theorem neumannActionPathWeight_castSucc
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ)
    (i : Fin n) :
    neumannActionPathWeight m β n i.castSucc = m := by
  simp [neumannActionPathWeight]

@[simp]
theorem neumannActionPathWeight_zero_succ
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    neumannActionPathWeight m β (n + 1) 0 = m := by
  change
    neumannActionPathWeight m β (n + 1)
      (0 : Fin (n + 1)).castSucc = m
  exact neumannActionPathWeight_castSucc m β (n + 1) 0

@[simp]
theorem neumannActionPathWeight_succ
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ)
    (i : Fin (n + 1)) :
    neumannActionPathWeight m β (n + 1) i.succ =
      neumannActionPathWeight m β n i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [show j.castSucc.succ = j.succ.castSucc by
      apply Fin.ext
      rfl]
    rw [
      neumannActionPathWeight_castSucc
        m β (n + 1) j.succ,
      neumannActionPathWeight_castSucc
        m β n j]

/-- Removing the first vertex of the order-`n+1` path leaves exactly the
order-`n` path. -/
theorem weightedGreenPath_neumann_succ_cons
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ)
    (x z : T4) (v : Fin (n + 1) → T4) :
    weightedGreenPath
        (neumannActionPathWeight m β (n + 1))
        x (Fin.cons z v) =
      (greenFn (x - z) : ℂ) * m z *
        weightedGreenPath
          (neumannActionPathWeight m β n) z v := by
  rw [weightedGreenPath_succ]
  simp only [Fin.cons_zero, Fin.tail_cons,
    neumannActionPathWeight_zero_succ,
    neumannActionPathWeight_succ]

/-- Every recursive physical Neumann action is the corresponding flat
Green-path integral for almost every left endpoint. -/
theorem continuousNeumannAction_eq_weightedGreenPath_ae
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    ∀ᵐ x ∂paperMeasure,
      continuousNeumannAction m β n x =
        ∫ v : Fin (n + 1) → T4,
          weightedGreenPath
            (neumannActionPathWeight m β n) x v
          ∂(Measure.pi fun _ => paperMeasure) := by
  induction n with
  | zero =>
      filter_upwards
        [ae_integrable_weightedGreenPath
          (neumannActionPathWeight m β 0)] with
        x hpath
      rw [continuousNeumannAction_zero_apply]
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
      have hw :
          neumannActionPathWeight m β 0 0 =
            charT4Continuous β := by
        rw [show (0 : Fin 1) = Fin.last 0 by
          apply Fin.ext
          rfl]
        exact neumannActionPathWeight_last m β 0
      rw [weightedGreenPath_succ, hw]
      simp
  | succ n ih =>
      filter_upwards
        [ae_integrable_weightedGreenPath
          (neumannActionPathWeight m β (n + 1))] with
        x hpath
      rw [continuousNeumannAction_succ_apply]
      rw [integral_pathHeadTail (n + 1) _ hpath]
      apply integral_congr_ae
      filter_upwards [ih] with z hz
      rw [hz]
      calc
        (greenFn (x - z) : ℂ) *
              (m z *
                ∫ v : Fin (n + 1) → T4,
                  weightedGreenPath
                    (neumannActionPathWeight m β n)
                    z v
                  ∂(Measure.pi fun _ => paperMeasure)) =
            ((greenFn (x - z) : ℂ) * m z) *
              ∫ v : Fin (n + 1) → T4,
                weightedGreenPath
                  (neumannActionPathWeight m β n)
                  z v
                ∂(Measure.pi fun _ => paperMeasure) := by
                  ring
        _ =
            ∫ v : Fin (n + 1) → T4,
              ((greenFn (x - z) : ℂ) * m z) *
                weightedGreenPath
                  (neumannActionPathWeight m β n)
                  z v
              ∂(Measure.pi fun _ => paperMeasure) := by
                rw [integral_const_mul]
        _ =
            ∫ v : Fin (n + 1) → T4,
              weightedGreenPath
                (neumannActionPathWeight m β (n + 1))
                x (Fin.cons z v)
              ∂(Measure.pi fun _ => paperMeasure) := by
                apply integral_congr_ae
                filter_upwards with v
                exact
                  (weightedGreenPath_neumann_succ_cons
                    m β n x z v).symm

/-! ## Identification with the paper's flat product -/

/-- Flat complex Green-chain integrand with a continuous multiplier.
The final character is included as the last vertex weight. -/
def continuousNeumannFlatIntegrand
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ)
    (x y : T4) (v : Fin n → T4) : ℂ :=
  (∏ e : Fin (n + 1),
      (greenFn
        ((assemble x y v) e.castSucc -
          (assemble x y v) e.succ) : ℂ)) *
    (∏ i : Fin n, m (v i)) *
      charT4 β y

/-- Dropping the first internal point from an assembled nonempty chain
turns that point into the new left endpoint. -/
theorem assemble_cons_succ_path
    (n : ℕ) (x y z : T4)
    (v : Fin n → T4)
    (i : Fin (n + 2)) :
    assemble x y (Fin.cons z v) i.succ =
      assemble z y v i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [assemble]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [assemble]
    · simp only [assemble, Fin.val_succ,
        Fin.val_castSucc]
      rw [dif_neg (by omega), dif_neg (by omega),
        dif_neg (by omega), dif_neg (by omega)]
      have hleft :
          (⟨k.val + 1 + 1 - 1, by omega⟩ :
            Fin (n + 1)) =
            k.succ := by
        apply Fin.ext
        simp
      have hright :
          (⟨k.val + 1 - 1, by omega⟩ :
            Fin n) =
            k := by
        apply Fin.ext
        simp
      rw [hleft, hright, Fin.cons_succ]

/-- A nonempty flat product separates into its first Green edge and
multiplier followed by the shorter flat product. -/
theorem continuousNeumannFlatIntegrand_succ_cons
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ)
    (x z y : T4) (v : Fin n → T4) :
    continuousNeumannFlatIntegrand
        m β (n + 1) x y (Fin.cons z v) =
      (greenFn (x - z) : ℂ) * m z *
        continuousNeumannFlatIntegrand
          m β n z y v := by
  have hchain :
      (∏ e : Fin (n + 2),
          (greenFn
            (assemble x y (Fin.cons z v) e.castSucc -
              assemble x y (Fin.cons z v) e.succ) : ℂ)) =
        (greenFn (x - z) : ℂ) *
          ∏ e : Fin (n + 1),
            (greenFn
              (assemble z y v e.castSucc -
                assemble z y v e.succ) : ℂ) := by
    calc
      _ =
          (greenFn
            (assemble x y (Fin.cons z v)
                (0 : Fin (n + 2)).castSucc -
              assemble x y (Fin.cons z v)
                (0 : Fin (n + 2)).succ) : ℂ) *
            ∏ e : Fin (n + 1),
              (greenFn
                (assemble x y (Fin.cons z v)
                    e.succ.castSucc -
                  assemble x y (Fin.cons z v)
                    e.succ.succ) : ℂ) :=
        Fin.prod_univ_succ _
      _ = _ := by
        congr 1
        apply Finset.prod_congr rfl
        intro e _
        have hleft :
            e.succ.castSucc =
              e.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hleft]
        rw [assemble_cons_succ_path n x y z v
          e.castSucc]
        rw [assemble_cons_succ_path n x y z v
          e.succ]
  have hweight :
      (∏ i : Fin (n + 1),
          m ((Fin.cons z v :
            Fin (n + 1) → T4) i)) =
        m z * ∏ i : Fin n, m (v i) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  unfold continuousNeumannFlatIntegrand
  rw [hchain, hweight]
  ring

private theorem snoc_cons
    {n : ℕ}
    (z : T4) (v : Fin n → T4) (y : T4) :
    (Fin.snoc
        (Fin.cons z v : Fin (n + 1) → T4) y :
      Fin (n + 2) → T4) =
      Fin.cons z
        (Fin.snoc v y : Fin (n + 1) → T4) :=
  (Fin.cons_snoc_eq_snoc_cons z v y).symm

/-- The recursive weighted path is exactly the assembled flat product
after the terminal vertex is separated. -/
theorem weightedGreenPath_neumann_snoc
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ)
    (x y : T4) (v : Fin n → T4) :
    weightedGreenPath
        (neumannActionPathWeight m β n)
        x (Fin.snoc v y) =
      continuousNeumannFlatIntegrand
        m β n x y v := by
  induction n generalizing x with
  | zero =>
      have hv :
          v = fun i : Fin 0 => Fin.elim0 i := by
        funext i
        exact Fin.elim0 i
      subst v
      rw [Fin.snoc_zero]
      simp [continuousNeumannFlatIntegrand,
        weightedGreenPath, neumannActionPathWeight,
        assemble]
      apply Or.inl
      rfl
  | succ n ih =>
      rw [← Fin.cons_self_tail v]
      rw [snoc_cons]
      rw [weightedGreenPath_neumann_succ_cons]
      rw [ih]
      exact
        (continuousNeumannFlatIntegrand_succ_cons
          m β n x (v 0) y (Fin.tail v)).symm

/-- A.e. flat-product form of the recursive physical action. -/
theorem continuousNeumannAction_eq_flatIntegral_ae
    (m : C(T4, ℂ)) (β : Z4) (n : ℕ) :
    ∀ᵐ x ∂paperMeasure,
      continuousNeumannAction m β n x =
        ∫ y : T4, ∫ v : Fin n → T4,
          continuousNeumannFlatIntegrand
            m β n x y v
          ∂(Measure.pi fun _ => paperMeasure)
          ∂paperMeasure := by
  filter_upwards
    [continuousNeumannAction_eq_weightedGreenPath_ae
      m β n,
    ae_integrable_weightedGreenPath
      (neumannActionPathWeight m β n)] with
      x haction hpath
  rw [haction, integral_pathLast n _ hpath]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with v
  exact weightedGreenPath_neumann_snoc
    m β n x y v

/-- On an absolutely summable noise sample, the continuous flat product
is exactly the integrand used in the paper's `neumannTermKernel`. -/
theorem continuousNeumannFlatIntegrand_eq_physical_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) (n : ℕ)
    (x y : T4) (v : Fin n → T4) :
    continuousNeumannFlatIntegrand
        (measurableMollifiedPotential
          M ρ lam ε ω) β n x y v =
      ((((∏ e : Fin (n + 1),
            greenFn
              ((assemble x y v) e.castSucc -
                (assemble x y v) e.succ)) *
          ∏ i : Fin n,
            multFun M ρ lam ε (v i) ω : ℝ) : ℂ) *
        charT4 β y) := by
  have hweight :
      (∏ i : Fin n,
          measurableMollifiedPotential
            M ρ lam ε ω (v i)) =
        ∏ i : Fin n,
          (multFun M ρ lam ε (v i) ω : ℂ) := by
    apply Finset.prod_congr rfl
    intro i _
    exact
      measurableMollifiedPotential_apply_eq_multFun_of_summable
        M ρ lam ε ω hω (v i)
  unfold continuousNeumannFlatIntegrand
  rw [hweight]
  push_cast
  ring

/-- A.e. kernel form of every recursive physical Neumann action. -/
theorem continuousNeumannAction_eq_neumannTermKernel_ae_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) (n : ℕ) :
    ∀ᵐ x ∂paperMeasure,
      continuousNeumannAction
          (measurableMollifiedPotential
            M ρ lam ε ω) β n x =
        ∫ y : T4,
          neumannTermKernel
              M ρ lam ε n x y ω *
            charT4 β y
          ∂paperMeasure := by
  filter_upwards
    [continuousNeumannAction_eq_flatIntegral_ae
      (measurableMollifiedPotential
        M ρ lam ε ω) β n] with
      x hflat
  rw [hflat]
  apply integral_congr_ae
  filter_upwards with y
  unfold neumannTermKernel
  calc
    (∫ v : Fin n → T4,
        continuousNeumannFlatIntegrand
          (measurableMollifiedPotential M ρ lam ε ω)
          β n x y v
        ∂(Measure.pi fun _ => paperMeasure)) =
        ∫ v : Fin n → T4,
          ((((∏ e : Fin (n + 1),
                greenFn
                  ((assemble x y v) e.castSucc -
                    (assemble x y v) e.succ)) *
              ∏ i : Fin n,
                multFun M ρ lam ε (v i) ω : ℝ) : ℂ) *
            charT4 β y)
          ∂(Measure.pi fun _ => paperMeasure) := by
      apply integral_congr_ae
      filter_upwards with v
      exact
        continuousNeumannFlatIntegrand_eq_physical_of_summable
          M ρ lam ε ω hω β n x y v
    _ =
        (∫ v : Fin n → T4,
          (((∏ e : Fin (n + 1),
                greenFn
                  ((assemble x y v) e.castSucc -
                    (assemble x y v) e.succ)) *
              ∏ i : Fin n,
                multFun M ρ lam ε (v i) ω : ℝ) : ℂ)
          ∂(Measure.pi fun _ => paperMeasure)) *
          charT4 β y := by
      rw [integral_mul_const]

/-- **All-order physical/operator bridge.**  Absolute Fourier
summability of the mollified sample implies the exact
`NeumannTermKernelAction` at every order. -/
theorem neumannTermKernelAction_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) (n : ℕ) :
    NeumannTermKernelAction
      M ρ lam ε n β ω := by
  have hscale :
      ENNReal.ofReal ((2 * Real.pi) ^ (dim : ℕ)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hhaarPaper : haarT4 ≪ paperMeasure := by
    unfold paperMeasure
    exact Measure.absolutelyContinuous_smul hscale
  have hkernel :
      ∀ᵐ x ∂haarT4,
        continuousNeumannAction
            (measurableMollifiedPotential
              M ρ lam ε ω) β n x =
          ∫ y : T4,
            neumannTermKernel
                M ρ lam ε n x y ω *
              charT4 β y
            ∂paperMeasure :=
    hhaarPaper.ae_le
      (continuousNeumannAction_eq_neumannTermKernel_ae_of_summable
        M ρ lam ε ω hω β n)
  unfold NeumannTermKernelAction
  filter_upwards
    [pow_andersonK_apply_char_ae_of_summable
      M ρ lam ε ω hω β n,
    hkernel] with x hop hphysical
  exact hop.trans hphysical

/-- Absolute Fourier summability discharges every kernel-action
hypothesis in the Neumann-tail coefficient bridge. -/
theorem torusOperatorModeCoeffH_eq_neumannCoeff_tail_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (hK : ‖andersonK M ρ lam ε ω‖ < 1) :
    torusOperatorModeCoeffH M ρ lam ε α β ω =
      (paperTorusVolume : ℂ)⁻¹ *
        ∑' n : ℕ,
          neumannCoeff M ρ lam ε (n + 1) α β ω := by
  exact torusOperatorModeCoeffH_eq_neumannCoeff_tail
    M ρ lam ε α β ω hK
      (fun n =>
        neumannTermKernelAction_of_summable
          M ρ lam ε ω hω β (n + 1))

/-- On an absolutely summable sample, the operator and coefficient
routes to the recentered inverse agree with the exact normalization
from the paper. -/
theorem torusOperatorModeCoeffH_eq_scaled_modeHcoeff_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (α β : Z4) (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (hK : ‖andersonK M ρ lam ε ω‖ < 1)
    (hLam : lamEps lam ε ≠ 0) :
    torusOperatorModeCoeffH M ρ lam ε α β ω =
      (lamEps lam ε / paperTorusVolume) •
        modeHcoeff M ρ lam ε α β ω := by
  exact torusOperatorModeCoeffH_eq_scaled_modeHcoeff
    M ρ lam ε α β ω hK hLam
      (fun n =>
        neumannTermKernelAction_of_summable
          M ρ lam ε ω hω β (n + 1))

/-- The all-order flat path is the a.e. representative of the
operator-valued Neumann power. -/
theorem pow_andersonK_apply_char_ae_eq_weightedGreenPath_of_summable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (ω : M.Ω)
    (hω : Summable fun k : Z4 =>
      ‖M.mollifiedRandomCoeff ρ ε k ω‖)
    (β : Z4) (n : ℕ) :
    ((andersonK M ρ lam ε ω) ^ n *
        greenL2Op) (charT4Lp 2 β) =ᵐ[haarT4]
      fun x =>
        ∫ v : Fin (n + 1) → T4,
          weightedGreenPath
            (neumannActionPathWeight
              (measurableMollifiedPotential
                M ρ lam ε ω) β n)
            x v
          ∂(Measure.pi fun _ => paperMeasure) := by
  have hscale :
      ENNReal.ofReal ((2 * Real.pi) ^ (dim : ℕ)) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hhaarPaper : haarT4 ≪ paperMeasure := by
    unfold paperMeasure
    exact Measure.absolutelyContinuous_smul hscale
  have hflat :
      ∀ᵐ x ∂haarT4,
        continuousNeumannAction
            (measurableMollifiedPotential
              M ρ lam ε ω) β n x =
          ∫ v : Fin (n + 1) → T4,
            weightedGreenPath
              (neumannActionPathWeight
                (measurableMollifiedPotential
                  M ρ lam ε ω) β n)
              x v
            ∂(Measure.pi fun _ => paperMeasure) :=
    hhaarPaper.ae_le
      (continuousNeumannAction_eq_weightedGreenPath_ae
        (measurableMollifiedPotential
          M ρ lam ε ω) β n)
  filter_upwards
    [pow_andersonK_apply_char_ae_of_summable
      M ρ lam ε ω hω β n,
      hflat] with
      x hop hflat
  exact hop.trans hflat

end

end Anderson4D
