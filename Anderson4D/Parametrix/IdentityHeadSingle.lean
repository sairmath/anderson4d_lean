import Anderson4D.Parametrix.IdentityExtraction

/-!
# The head-single branch of the parametrix identity

This file identifies Wick creation with case (1) in the proof of
Proposition 3.4.  Adjoining the new noise variable is the same as
prepending one fixed point to the old partial pairing.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

namespace PartialPairing

@[simp]
theorem wickHeadEquiv_creation_zero
    (n : ℕ) (κ : PartialPairing (Fin n)) :
    wickHeadEquiv n (Sum.inl κ) 0 = 0 := by
  unfold wickHeadEquiv finHeadEquiv
  simp [optionHeadEquiv, optionHeadAssemble]
  change
    PartialPairing.congr (finSuccEquiv n).symm
        (optionFixed κ) 0 = 0
  rw [PartialPairing.congr_apply_apply]
  rfl

@[simp]
theorem wickHeadEquiv_creation_succ
    (n : ℕ) (κ : PartialPairing (Fin n)) (i : Fin n) :
    wickHeadEquiv n (Sum.inl κ) i.succ = (κ i).succ := by
  unfold wickHeadEquiv finHeadEquiv
  simp [optionHeadEquiv, optionHeadAssemble]
  change
    PartialPairing.congr (finSuccEquiv n).symm
        (optionFixed κ) i.succ = (κ i).succ
  rw [PartialPairing.congr_apply_apply]
  rfl

/-- The creation pairing is the consecutive append of a singleton fixed
head and the old pairing. -/
theorem wickHeadEquiv_creation_eq_append
    (n : ℕ) (κ : PartialPairing (Fin n)) :
    wickHeadEquiv n (Sum.inl κ) =
      appendPairingTo (N := n + 1) (a := 1) (by omega)
        PartialPairing.id κ := by
  apply PartialPairing.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [wickHeadEquiv_creation_zero]
    have hzero :
        (0 : Fin (n + 1)) =
          Fin.castLE (by omega : 1 ≤ n + 1) (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hzero, appendPairingTo_apply_prefix]
    rfl
  · rw [wickHeadEquiv_creation_succ]
    have hsucc :
        j.succ =
          suffixFin (by omega : 1 ≤ n + 1) j := by
      apply Fin.ext
      simp only [Fin.val_succ, suffixFin_val]
      omega
    rw [hsucc, appendPairingTo_apply_suffix]
    apply Fin.ext
    simp only [Fin.val_succ, suffixFin_val]
    omega

@[simp]
theorem extract_id_fin_one :
    extract (PartialPairing.id : PartialPairing (Fin 1)) = [] := by
  decide

/-- Prepending a fixed point only adds the new first Green edge to the
chain product. -/
theorem chainProduct_wickHeadEquiv_creation
    (n : ℕ) (κ : PartialPairing (Fin n))
    (xt : Fin (n + 3) → T4) :
    (∏ e : Fin (n + 2),
        if e.val ∈
            (extract (wickHeadEquiv n (Sum.inl κ))).map
              (fun p => p.2.val + 1) then 1
        else greenFn (xt e.castSucc - xt e.succ)) =
      greenFn (xt 0 - xt 1) *
        ∏ e : Fin (n + 1),
          if e.val ∈
              (extract κ).map (fun p => p.2.val + 1) then 1
          else greenFn
            (ambientTailTuple
                (by omega : 1 ≤ n + 1) xt e.castSucc -
              ambientTailTuple
                (by omega : 1 ≤ n + 1) xt e.succ) := by
  let ha : 1 ≤ n + 1 := by omega
  let K :=
    appendPairingTo ha
      (PartialPairing.id : PartialPairing (Fin 1)) κ
  let rvK :=
    (extract K).map (fun p => p.2.val + 1)
  let rvκ :=
    (extract κ).map (fun p => p.2.val + 1)
  have hperm :
      rvK.Perm
        ((extract (PartialPairing.id :
              PartialPairing (Fin 1))).map
            (fun p => p.2.val + 1) ++
          (extract κ).map
            (fun p => 1 + p.2.val + 1)) := by
    exact extractedRightValues_appendPairingTo_perm
      ha (PartialPairing.id : PartialPairing (Fin 1)) κ
  have hmem (k : ℕ) :
      k ∈ rvK ↔
        k ∈ (extract κ).map
          (fun p => 1 + p.2.val + 1) := by
    rw [hperm.mem_iff]
    simp only [extract_id_fin_one, List.map_nil,
      List.nil_append]
  have hzero : 0 ∉ rvK := by
    intro h
    have hz := (hmem 0).mp h
    obtain ⟨p, _hp, heq⟩ := List.mem_map.mp hz
    omega
  have hsucc (e : Fin (n + 1)) :
      e.succ.val ∈ rvK ↔ e.val ∈ rvκ := by
    rw [hmem]
    constructor
    · intro h
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨p, hp, by
        simp only [Fin.val_succ] at heq
        omega⟩
    · intro h
      obtain ⟨p, hp, heq⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨p, hp, by
        simp only [Fin.val_succ]
        omega⟩
  rw [wickHeadEquiv_creation_eq_append]
  change
    (∏ e : Fin (n + 2),
        if e.val ∈ rvK then 1
        else greenFn (xt e.castSucc - xt e.succ)) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, if_neg hzero]
  apply congrArg (greenFn (xt 0 - xt 1) * ·)
  apply Finset.prod_congr rfl
  intro e _he
  by_cases h : e.val ∈ rvκ
  · rw [if_pos h, if_pos ((hsucc e).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((hsucc e).mp h'))]
    apply congrArg greenFn
    apply congrArg₂ (· - ·)
    · apply congrArg xt
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · apply congrArg xt
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

/-- The deterministic closed form for a created pairing is the old
closed form preceded by the new free Green edge. -/
theorem detIntegrand_wickHeadEquiv_creation
    (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (xt : Fin (n + 3) → T4) :
    detIntegrand ρ ε (n + 1)
        (wickHeadEquiv n (Sum.inl κ)) xt =
      greenFn (xt 0 - xt 1) *
        detIntegrand ρ ε n κ
          (ambientTailTuple
            (by omega : 1 ≤ n + 1) xt) := by
  unfold detIntegrand
  rw [chainProduct_wickHeadEquiv_creation]
  rw [wickHeadEquiv_creation_eq_append]
  rw [differenceProduct_appendPairingTo
    (by omega : 1 ≤ n + 1)
    (PartialPairing.id : PartialPairing (Fin 1)) κ xt]
  rw [covarianceProduct_appendPairingTo
    ρ ε (by omega : 1 ≤ n + 1)
    (PartialPairing.id : PartialPairing (Fin 1)) κ xt]
  simp only [extract_id_fin_one, List.map_nil, List.prod_nil,
    one_mul]
  have hpair :
      (PartialPairing.id :
        PartialPairing (Fin 1)).pairSupport = ∅ := by
    ext i
    simp [PartialPairing.pairSupport]
  rw [hpair]
  simp only [Finset.filter_empty, Finset.prod_empty, one_mul]
  simp only [mul_assoc]
  rfl

/-- The singles of a creation pairing are the new zero followed by the
shifted old singles. -/
theorem singles_wickHeadEquiv_creation
    (n : ℕ) (κ : PartialPairing (Fin n)) :
    (wickHeadEquiv n (Sum.inl κ)).singles =
      insert 0 (κ.singles.map (Fin.succEmb n)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [PartialPairing.mem_singles,
      wickHeadEquiv_creation_zero]
    simp
  · rw [PartialPairing.mem_singles,
      wickHeadEquiv_creation_succ]
    simp [PartialPairing.mem_singles]

/-- The ordered list of values attached to the singles is the sorted
singles finset mapped through the ambient tuple. -/
theorem wickAtSingleLabels_eq_sort_map
    {m : ℕ} (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    wickAtSingleLabels κ xt =
      κ.singles.sort.map (fun i => xt (varIdx i)) := by
  unfold wickAtSingleLabels
  simp only [Finset.orderEmbOfFin_apply]
  convert
    (List.ofFn_getElem_eq_map κ.singles.sort
      (fun i => xt (varIdx i))) using 1
  all_goals simp

/-- Creation prepends the new head value to the old ordered list of
single labels. -/
theorem wickAtSingleLabels_wickHeadEquiv_creation
    (n : ℕ) (κ : PartialPairing (Fin n))
    (xt : Fin (n + 3) → T4) :
    wickAtSingleLabels
        (wickHeadEquiv n (Sum.inl κ)) xt =
      xt 1 ::
        wickAtSingleLabels κ
          (ambientTailTuple
            (by omega : 1 ≤ n + 1) xt) := by
  rw [wickAtSingleLabels_eq_sort_map,
    singles_wickHeadEquiv_creation]
  have hzero :
      (0 : Fin (n + 1)) ∉
        κ.singles.map (Fin.succEmb n) := by
    simp
  rw [Finset.sort_insert (r := (· ≤ ·))
    (by simp) hzero]
  rw [List.map_cons]
  have hsort :
      κ.singles.sort.map Fin.succ =
        (κ.singles.map (Fin.succEmb n)).sort := by
    exact StrictMonoOn.map_finsetSort
      (Fin.succEmb n) κ.singles
      (Fin.strictMono_succ.strictMonoOn
        (↑κ.singles : Set (Fin n)))
  rw [← hsort]
  rw [List.map_map, wickAtSingleLabels_eq_sort_map]
  apply congrArg₂ List.cons
  · apply congrArg xt
    apply Fin.ext
    rfl
  · apply List.map_congr_left
    intro i hi
    apply congrArg xt
    apply Fin.ext
    simp only [varIdx_val, Fin.val_succ]
    omega

/-- The Wick factor of the created pairing is exactly the creation term
in the head recursion. -/
theorem wickAt_wickHeadEquiv_creation
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (xt : Fin (n + 3) → T4) (ω : M.Ω) :
    wickAt M ρ ε
        (wickHeadEquiv n (Sum.inl κ)) xt ω =
      wickPolynomial
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
        (fun x ω' => M.xiEps ρ ε ω' x)
        (xt 1 ::
          wickAtSingleLabels κ
            (ambientTailTuple
              (by omega : 1 ≤ n + 1) xt)) ω := by
  rw [wickAt_eq_wickPolynomial,
    wickAtSingleLabels_wickHeadEquiv_creation]

/-- Pointwise case (1) of Proposition 3.4: the Wick-creation source term
is the random integrand indexed by the corresponding head-single
pairing. -/
theorem headSingleCreationTerm_eq_randIntegrand
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (xt : Fin (n + 3) → T4) (ω : M.Ω) :
    greenFn (xt 0 - xt 1) *
        (detIntegrand ρ ε n κ
          (ambientTailTuple
            (by omega : 1 ≤ n + 1) xt) *
          wickPolynomial
            (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
            (fun x ω' => M.xiEps ρ ε ω' x)
            (xt 1 ::
              wickAtSingleLabels κ
                (ambientTailTuple
                  (by omega : 1 ≤ n + 1) xt)) ω) =
      randIntegrand M ρ ε
        (wickHeadEquiv n (Sum.inl κ)) xt ω := by
  unfold randIntegrand
  rw [detIntegrand_wickHeadEquiv_creation,
    wickAt_wickHeadEquiv_creation]
  ring

/-! ## Splitting the new integration variable -/

/-- Measurable separation of the first coordinate from a tuple of
`n+1` internal variables. -/
def headTailVariablesEquiv (n : ℕ) :
    (Fin (n + 1) → T4) ≃ᵐ
      T4 × (Fin n → T4) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => T4) 0

@[simp]
theorem headTailVariablesEquiv_symm_apply
    (n : ℕ) (z : T4) (v : Fin n → T4) :
    (headTailVariablesEquiv n).symm (z, v) =
      Fin.cons z v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [headTailVariablesEquiv]
  · simp [headTailVariablesEquiv]

/-- Fubini after separating the new head variable from the old internal
variables. -/
theorem integral_headTailVariables
    (n : ℕ) (f : (Fin (n + 1) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure)) :
    (∫ u : Fin (n + 1) → T4,
        f u ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ z : T4, ∫ v : Fin n → T4,
        f (Fin.cons z v)
        ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure := by
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
      funext u
      simp only [Function.comp_apply,
        e.symm_apply_apply]
    exact hcomp
  calc
    (∫ u, f u ∂μold) =
        ∫ p, f (e.symm p) ∂μtarget := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp'
          (fun p => f (e.symm p))
    _ =
        ∫ z : T4, ∫ v : Fin n → T4,
          f (e.symm (z, v))
          ∂μtail ∂paperMeasure :=
      integral_prod _ hf'
    _ = _ := by
      simp_rw [e, headTailVariablesEquiv_symm_apply]
      rfl

@[simp]
theorem assemble_cons_first_internal
    (n : ℕ) (x z y : T4) (v : Fin n → T4) :
    assemble x y (Fin.cons z v) 1 = z := by
  have hidx :
      (1 : Fin (n + 3)) =
        varIdx (0 : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [hidx, assemble_varIdx]
  simp

/-- Removing the first internal variable from an assembled ambient tuple
leaves the old assembled tuple. -/
theorem ambientTailTuple_assemble_cons
    (n : ℕ) (x z y : T4) (v : Fin n → T4) :
    ambientTailTuple
        (by omega : 1 ≤ n + 1)
        (assemble x y (Fin.cons z v)) =
      assemble z y v := by
  funext i
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    subst i
    unfold ambientTailTuple
    change
      assemble x y (Fin.cons z v)
          (1 : Fin (n + 3)) =
        assemble z y v (0 : Fin (n + 2))
    rw [assemble_cons_first_internal, assemble_zero]
  · by_cases hilast : i.val = n + 1
    · have hi : i = Fin.last (n + 1) := by
        apply Fin.ext
        simpa only [Fin.val_last] using hilast
      subst i
      unfold ambientTailTuple
      rw [assemble_last]
      have hidx :
          (⟨1 + (Fin.last (n + 1)).val, by omega⟩ :
              Fin (n + 3)) =
            Fin.last (n + 2) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [hidx, assemble_last]
    · let j : Fin n := ⟨i.val - 1, by
        have hiLt := i.isLt
        omega⟩
      have hiVar : i = varIdx j := by
        apply Fin.ext
        dsimp [j]
        omega
      rw [hiVar]
      unfold ambientTailTuple
      rw [assemble_varIdx]
      have hidx :
          (⟨1 + (varIdx j).val, by omega⟩ :
              Fin (n + 3)) =
            varIdx j.succ := by
        apply Fin.ext
        simp only [varIdx_val, Fin.val_succ]
        omega
      rw [hidx, assemble_varIdx]
      simp

/-- The integrated Wick-creation source attached to one old pairing. -/
def headSingleCreationContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (n + 1) *
    (∫ z : T4, ∫ v : Fin n → T4,
      greenFn (x - z) *
        (detIntegrand ρ ε n κ
            (assemble z y v) *
          wickPolynomial
            (fun a b : T4 =>
              ρ.etaEpsT4 ε (a - b))
            (fun a ω' =>
              M.xiEps ρ ε ω' a)
            (z ::
              wickAtSingleLabels κ
                (assemble z y v)) ω)
      ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure)

/-- Integrated case (1) of Proposition 3.4.  Under exactly the
integrability needed for Fubini, the creation source is the random
kernel indexed by the head-single pairing. -/
theorem headSingleCreationContribution_eq_randRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (κ : PartialPairing (Fin n))
    (x y : T4) (ω : M.Ω)
    (hint :
      Integrable
        (fun u : Fin (n + 1) → T4 =>
          randIntegrand M ρ ε
            (wickHeadEquiv n (Sum.inl κ))
            (assemble x y u) ω)
        (Measure.pi fun _ => paperMeasure)) :
    headSingleCreationContribution
        M ρ lam ε n κ x y ω =
      randRI M ρ lam ε (n + 1)
        (wickHeadEquiv n (Sum.inl κ))
        x y ω := by
  unfold headSingleCreationContribution
  unfold randRI
  rw [integral_headTailVariables n _ hint]
  apply congrArg (lamEps lam ε ^ (n + 1) * ·)
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with v
  have hpoint :=
    headSingleCreationTerm_eq_randIntegrand
      M ρ ε n κ (assemble x y (Fin.cons z v)) ω
  rw [ambientTailTuple_assemble_cons,
    assemble_cons_first_internal, assemble_zero] at hpoint
  exact hpoint

/-- Summed case (1) of Proposition 3.4.  Wick creation enumerates the
head-single class with multiplicity one. -/
theorem sum_headSingleCreationContribution_eq_headSingleRandRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      ∀ κ : PartialPairing (Fin n),
        Integrable
          (fun u : Fin (n + 1) → T4 =>
            randIntegrand M ρ ε
              (wickHeadEquiv n (Sum.inl κ))
              (assemble x y u) ω)
          (Measure.pi fun _ => paperMeasure)) :
    (∑ κ : PartialPairing (Fin n),
        headSingleCreationContribution
          M ρ lam ε n κ x y ω) =
      ∑ κ :
          {κ : PartialPairing (Fin (n + 1)) //
            HeadIsSingle κ},
        randRI M ρ lam ε (n + 1) κ.1 x y ω := by
  calc
    _ =
        ∑ κ : PartialPairing (Fin n),
          randRI M ρ lam ε (n + 1)
            (creationHeadEquiv n κ).1 x y ω := by
      apply Fintype.sum_congr
      intro κ
      rw [creationHeadEquiv_apply_val]
      exact headSingleCreationContribution_eq_randRI
        M ρ lam ε n κ x y ω (hint κ)
    _ = _ :=
      sum_creation_headCase n
        (fun κ =>
          randRI M ρ lam ε (n + 1) κ x y ω)

end PartialPairing

end

end Anderson4D
