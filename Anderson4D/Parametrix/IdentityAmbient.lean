import Anderson4D.Parametrix.IdentityIntegration

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

private def caseThreeInsertInternal
    (q r : ℕ) (z w : T4)
    (t : Fin (2 * q + r) → T4) :
    Fin (2 * (q + 1) + r) → T4 :=
  fun j =>
    Fin.insertNth (α := fun _ => T4)
      (0 : Fin (2 * q + r + 1 + 1)) z
      (Fin.insertNth (α := fun _ => T4)
        (⟨2 * q, by omega⟩ : Fin (2 * q + r + 1)) w t)
      (Fin.cast (by omega) j)

private theorem caseThreeInsertInternal_eq
    (q r : ℕ) (z w : T4)
    (t : Fin (2 * q + r) → T4) :
    caseThreeInsertInternal q r z w t =
      caseThreeAmbientInternal q r z w t := by
  funext j
  unfold caseThreeInsertInternal
  let j' : Fin (2 * q + r + 1 + 1) :=
    Fin.cast (by omega) j
  change
    Fin.insertNth (α := fun _ => T4)
        (0 : Fin (2 * q + r + 1 + 1)) z
        (Fin.insertNth (α := fun _ => T4)
          (⟨2 * q, by omega⟩ : Fin (2 * q + r + 1)) w t)
        j' =
      caseThreeAmbientInternal q r z w t
        (Fin.cast (by omega) j')
  rw [Fin.insertNth_zero']
  refine Fin.cases ?_ (fun k => ?_) j'
  · simp only [Fin.cons_zero]
    rw [show
        (Fin.cast (by omega) (0 :
          Fin (2 * q + r + 1 + 1))) =
          Fin.castAdd r
            (0 : Fin (2 * (q + 1))) by
        apply Fin.ext
        rfl]
    rw [caseThreeAmbientInternal_prefix,
      detJTupleSucc_zero]
  · rw [Fin.cons_succ]
    by_cases hk : k.val < 2 * q
    · let i :
          Fin (2 * q + r + 1) :=
          ⟨2 * q, by omega⟩
      let uAll : Fin (2 * q + r) :=
        ⟨k.val, by omega⟩
      let uPre : Fin (2 * q) :=
        ⟨k.val, hk⟩
      have hkrep : i.succAbove uAll = k := by
        rw [Fin.succAbove_of_castSucc_lt]
        · apply Fin.ext
          rfl
        · exact Fin.mk_lt_mk.mpr hk
      rw [← hkrep, Fin.insertNth_apply_succAbove]
      rw [hkrep]
      rw [show
          Fin.cast (by omega) k.succ =
            Fin.castAdd r (varIdx uPre) by
        apply Fin.ext
        rfl]
      rw [caseThreeAmbientInternal_prefix]
      unfold detJTupleSucc
      rw [show
          Fin.cast (by omega :
            2 * (q + 1) = 2 * q + 2)
            (varIdx uPre) =
          varIdx uPre by
        apply Fin.ext
        rfl]
      rw [assemble_varIdx]
      congr 1
    · by_cases heq : k.val = 2 * q
      · have hkfin :
            k =
              (⟨2 * q, by omega⟩ :
                Fin (2 * q + r + 1)) := by
          apply Fin.ext
          exact heq
        rw [hkfin, Fin.insertNth_apply_same]
        rw [← hkfin]
        let oldLast :
            Fin (2 * (q + 1) + r) :=
          ⟨2 * q + 1, by omega⟩
        have hcoord :
            Fin.cast (by omega) k.succ =
              oldLast := by
          apply Fin.ext
          change k.val + 1 = 2 * q + 1
          omega
        rw [hcoord]
        let iLast : Fin (2 * (q + 1)) :=
          ⟨2 * q + 1, by omega⟩
        have hold :
            oldLast =
              Fin.castLE (by omega) iLast := by
          apply Fin.ext
          rfl
        rw [hold]
        unfold caseThreeAmbientInternal
        rw [Fin.append_left']
        unfold detJTupleSucc
        rw [show
            Fin.cast (by omega :
              2 * (q + 1) = 2 * q + 2) iLast =
              Fin.last (2 * q + 1) by
          apply Fin.ext
          rfl]
        rw [assemble_last]
      · have hgt : 2 * q < k.val := by omega
        have hr : k.val - (2 * q + 1) < r := by
          have hklt := k.isLt
          omega
        let a : Fin r := ⟨k.val - (2 * q + 1), hr⟩
        let i :
            Fin (2 * q + r + 1) :=
          ⟨2 * q, by omega⟩
        let uAll : Fin (2 * q + r) :=
          ⟨k.val - 1, by omega⟩
        have hkrep : i.succAbove uAll = k := by
          rw [Fin.succAbove_of_le_castSucc]
          · apply Fin.ext
            dsimp [uAll]
            omega
          · exact Fin.mk_le_mk.mpr (by
              dsimp [i, uAll]
              omega)
        rw [← hkrep, Fin.insertNth_apply_succAbove]
        have htidx :
            uAll =
              Fin.natAdd (2 * q) a := by
          apply Fin.ext
          dsimp [a, uAll]
          omega
        rw [htidx]
        rw [← htidx, hkrep]
        rw [show
            Fin.cast (by omega) k.succ =
            Fin.natAdd (2 * (q + 1)) a by
          apply Fin.ext
          dsimp [a]
          omega]
        rw [caseThreeAmbientInternal_suffix]
        congr 1

private theorem fin_equivCast_symm_val
    {m n : ℕ} (h : m = n) (j : Fin n) :
    ((Equiv.cast (congrArg Fin h)).symm j).val =
      j.val := by
  subst n
  rfl

private def caseThreeIndexCast
    (q r : ℕ) :
    Fin ((2 * q + r) + 2) ≃
      Fin (2 * (q + 1) + r) :=
  Equiv.cast (congrArg Fin (by omega))

private def caseThreeFullCastEquiv
    (q r : ℕ) :
    (Fin (2 * (q + 1) + r) → T4) ≃ᵐ
      (Fin ((2 * q + r) + 2) → T4) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : Fin (2 * (q + 1) + r) => T4)
    (caseThreeIndexCast q r)).symm

private def caseThreeFirstEquiv
    (q r : ℕ) :
    (Fin ((2 * q + r) + 2) → T4) ≃ᵐ
      T4 × (Fin ((2 * q + r) + 1) → T4) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin ((2 * q + r + 1) + 1) => T4) 0

private def caseThreeSecondEquiv
    (q r : ℕ) :
    (Fin ((2 * q + r) + 1) → T4) ≃ᵐ
      T4 × (Fin (2 * q + r) → T4) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin ((2 * q + r) + 1) => T4)
    (⟨2 * q, by omega⟩ :
      Fin ((2 * q + r) + 1))

/-- The measurable coordinate permutation taking paper order
`(z,u,w,v)` to the Fubini order `(z,w,(u,v))`. -/
def caseThreeVariablesEquiv
    (q r : ℕ) :
    (Fin (2 * (q + 1) + r) → T4) ≃ᵐ
      T4 × (T4 × (Fin (2 * q + r) → T4)) :=
  (caseThreeFullCastEquiv q r).trans <|
    (caseThreeFirstEquiv q r).trans <|
      MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (caseThreeSecondEquiv q r)

/-- The inverse coordinate permutation reconstructs the paper-order
case-(3) internal tuple. -/
theorem caseThreeVariablesEquiv_symm_apply
    (q r : ℕ) (z w : T4)
    (t : Fin (2 * q + r) → T4) :
    (caseThreeVariablesEquiv q r).symm
        (z, (w, t)) =
      caseThreeAmbientInternal q r z w t := by
  rw [← caseThreeInsertInternal_eq]
  funext j
  simp only [caseThreeVariablesEquiv,
    MeasurableEquiv.trans_symm,
    MeasurableEquiv.trans_apply]
  have hprod :
      (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (caseThreeSecondEquiv q r)).symm
          (z, (w, t)) =
        (z, (caseThreeSecondEquiv q r).symm
          (w, t)) := by
    rfl
  rw [hprod]
  simp only [caseThreeFirstEquiv,
    caseThreeSecondEquiv,
    MeasurableEquiv.piFinSuccAbove_symm_apply,
    caseThreeFullCastEquiv,
    MeasurableEquiv.symm_symm,
    caseThreeInsertInternal]
  rw [MeasurableEquiv.coe_piCongrLeft]
  simp only [Equiv.piCongrLeft_apply_eq_cast]
  change
    Fin.insertNth (α := fun _ => T4)
        (0 : Fin (2 * q + r + 1 + 1)) z
        (Fin.insertNth (α := fun _ => T4)
          (⟨2 * q, by omega⟩ :
            Fin (2 * q + r + 1)) w t)
        ((caseThreeIndexCast q r).symm j) =
      Fin.insertNth (α := fun _ => T4)
        (0 : Fin (2 * q + r + 1 + 1)) z
        (Fin.insertNth (α := fun _ => T4)
          (⟨2 * q, by omega⟩ :
            Fin (2 * q + r + 1)) w t)
        (Fin.cast (by omega) j)
  congr 1
  apply Fin.ext
  unfold caseThreeIndexCast
  exact fin_equivCast_symm_val (by omega) j

/-- The case-(3) coordinate permutation preserves the product of
paper-normalized Haar measures. -/
theorem measurePreserving_caseThreeVariablesEquiv
    (q r : ℕ) :
    MeasurePreserving
      (caseThreeVariablesEquiv q r)
      (Measure.pi fun _ :
        Fin (2 * (q + 1) + r) => paperMeasure)
      (paperMeasure.prod
        (paperMeasure.prod
          (Measure.pi fun _ :
            Fin (2 * q + r) => paperMeasure))) := by
  let μold :=
    Measure.pi fun _ :
      Fin (2 * (q + 1) + r) => paperMeasure
  let μnew :=
    Measure.pi fun _ :
      Fin ((2 * q + r) + 2) => paperMeasure
  let μtail :=
    Measure.pi fun _ :
      Fin ((2 * q + r) + 1) => paperMeasure
  let μt :=
    Measure.pi fun _ :
      Fin (2 * q + r) => paperMeasure
  have hcastForward :
      MeasurePreserving
        (MeasurableEquiv.piCongrLeft
          (fun _ :
            Fin (2 * (q + 1) + r) => T4)
          (caseThreeIndexCast q r))
        μnew μold := by
    simpa only [μnew, μold] using
      (measurePreserving_piCongrLeft
        (fun _ :
          Fin (2 * (q + 1) + r) =>
            paperMeasure)
        (caseThreeIndexCast q r))
  have hcast :
      MeasurePreserving
        (caseThreeFullCastEquiv q r)
        μold μnew := by
    simpa only [caseThreeFullCastEquiv] using
      hcastForward.symm
  have hfirst :
      MeasurePreserving
        (caseThreeFirstEquiv q r)
        μnew (paperMeasure.prod μtail) := by
    simpa only [caseThreeFirstEquiv,
      μnew, μtail] using
      (measurePreserving_piFinSuccAbove
        (fun _ :
          Fin ((2 * q + r + 1) + 1) =>
            paperMeasure)
        (0 : Fin ((2 * q + r + 1) + 1)))
  have hsecond :
      MeasurePreserving
        (caseThreeSecondEquiv q r)
        μtail (paperMeasure.prod μt) := by
    simpa only [caseThreeSecondEquiv,
      μtail, μt] using
      (measurePreserving_piFinSuccAbove
        (fun _ :
          Fin ((2 * q + r) + 1) =>
            paperMeasure)
        (⟨2 * q, by omega⟩ :
          Fin ((2 * q + r) + 1)))
  have hprod :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl T4)
          (caseThreeSecondEquiv q r))
        (paperMeasure.prod μtail)
        (paperMeasure.prod
          (paperMeasure.prod μt)) := by
    let hbase :=
      (MeasurePreserving.id paperMeasure).prod
        hsecond
    exact hbase.congr
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.refl T4)
        (caseThreeSecondEquiv q r)).measurable
      (Filter.Eventually.of_forall fun p => by
        rfl)
  let hcomp := hprod.comp (hfirst.comp hcast)
  exact hcomp.congr
    (caseThreeVariablesEquiv q r).measurable
    (Filter.Eventually.of_forall fun v => by
      rfl)

/-- Fubini after the case-(3) coordinate permutation
`(z,u,w,v) ↔ (z,w,(u,v))`. -/
theorem integral_caseThreeVariables
    (q r : ℕ)
    (f :
      (Fin (2 * (q + 1) + r) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ :
          Fin (2 * (q + 1) + r) =>
            paperMeasure)) :
    (∫ v : Fin (2 * (q + 1) + r) → T4,
        f v
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ z : T4, ∫ w : T4,
        ∫ t : Fin (2 * q + r) → T4,
          f (caseThreeAmbientInternal
            q r z w t)
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure := by
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
      measurePreserving_caseThreeVariablesEquiv
        q r
  have hf' :
      Integrable
        (fun p => f (e.symm p)) μtarget := by
    have hiff :=
      hp.integrable_comp_emb
        e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    have hcomp :
        Integrable
          (((fun p => f (e.symm p)) ∘ e))
          μold := by
      convert hf using 1
      funext v
      simp only [Function.comp_apply,
        e.symm_apply_apply]
    exact hcomp
  calc
    (∫ v, f v ∂μold) =
        ∫ p, f (e.symm p) ∂μtarget := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp'
          (fun p => f (e.symm p))
    _ =
        ∫ z : T4,
          ∫ wt :
              T4 ×
                (Fin (2 * q + r) → T4),
            f (e.symm (z, wt))
            ∂(paperMeasure.prod μt)
          ∂paperMeasure :=
      integral_prod _ hf'
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf'.prod_right_ae] with
        z hz
      rw [integral_prod _ hz]
      simp_rw [e,
        caseThreeVariablesEquiv_symm_apply]
      rfl

/-- The ambient case-(3) term is the existing random kernel for the
appended prefix/tail pairing. -/
theorem caseThreeAmbientContribution_eq_randRI
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (q r : ℕ)
    (σ :
      PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω)
    (hint :
      Integrable
        (fun v :
          Fin (2 * (q + 1) + r) → T4 =>
          randIntegrand M ρ ε
            (appendPairing σ τ)
            (assemble x y v) ω)
        (Measure.pi fun _ => paperMeasure)) :
    caseThreeAmbientContribution
        M ρ lam ε q r σ τ x y ω =
      randRI M ρ lam ε
        (2 * (q + 1) + r)
        (appendPairing σ τ) x y ω := by
  unfold caseThreeAmbientContribution
  unfold caseThreeAmbientCore
  unfold randRI
  rw [← integral_caseThreeVariables
    q r
    (fun v =>
      randIntegrand M ρ ε
        (appendPairing σ τ)
        (assemble x y v) ω)
    hint]

/-- **Fixed-pairing case-(3) identity.**  A non-split fully
paired prefix contributes the ambient appended-pairing kernel plus
the collapsed delta term. -/
theorem caseThreeJointContribution_eq_randRI_add_delta
    (M : NoiseModel) (ρ : SmoothCutoff)
    (lam ε : ℝ) (q r : ℕ)
    (σ :
      PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (hσ : IsNonSplit σ)
    (x y : T4) (ω : M.Ω)
    (hsplit :
      NestedIntegrablePair3
        paperMeasure paperMeasure
        (Measure.pi fun _ :
          Fin (2 * q + r) =>
            paperMeasure)
        (fun z w t =>
          caseThreeAmbientCore
            M ρ ε q r σ τ x z w y ω t)
        (fun z w t =>
          caseThreeDiagonalCore
            M ρ ε q r σ τ x z w y ω t))
    (hambient :
      Integrable
        (fun v :
          Fin (2 * (q + 1) + r) → T4 =>
          randIntegrand M ρ ε
            (appendPairing σ τ)
            (assemble x y v) ω)
        (Measure.pi fun _ => paperMeasure)) :
    caseThreeJointContribution
        M ρ lam ε q r σ τ x y ω =
      randRI M ρ lam ε
          (2 * (q + 1) + r)
          (appendPairing σ τ) x y ω +
        caseThreeDeltaContribution
          M ρ lam ε (q + 1) r
          σ τ x y ω := by
  rw [caseThreeJointContribution_eq_ambient_add_delta
    M ρ lam ε q r σ τ hσ x y ω hsplit]
  rw [caseThreeAmbientContribution_eq_randRI
    M ρ lam ε q r σ τ x y ω hambient]

end PartialPairing

end

end Anderson4D
