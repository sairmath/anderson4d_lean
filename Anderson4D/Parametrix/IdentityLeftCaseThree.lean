import Anderson4D.Parametrix.IdentityHeadPrefix
import Anderson4D.Parametrix.IdentityLeftAssembly

/-!
# Closing the with-prefix branch of the left parametrix identity

This module reindexes the actual marked-single contraction sum by the
paper's minimal non-split head prefix and applies the fixed-data
case-(3) bridge.  Every reindexing is an equivalence, so no
multiplicity factor is introduced.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-- Marked old singles whose new head has a fully paired prefix are in
bijection with the paper's case-(3) ambient pairings. -/
def withPrefixMarkedEquiv (n : ℕ) :
    {d : MarkedSingle (Fin n) //
      markedHasHeadPrefix d} ≃
      {κ : PartialPairing (Fin (n + 1)) //
        HeadPairedWithPrefix κ} where
  toFun d :=
    ⟨wickHeadEquiv n (Sum.inr d.1),
      ⟨wickHeadEquiv_contraction_not_isSingle
          n d.1,
        d.2⟩⟩
  invFun κ := by
    let d :=
      headDeletionData κ.1 κ.2.1
    refine ⟨d, ?_⟩
    have heq :
        (contractionHeadEquiv n d).1 = κ.1 :=
      contractionHeadEquiv_headDeletionData
        κ.1 κ.2.1
    change
      HasFullyPairedHeadPrefix
        (wickHeadEquiv n (Sum.inr d))
    rw [← contractionHeadEquiv_apply_val,
      heq]
    exact κ.2.2
  left_inv d := by
    apply Subtype.ext
    exact headDeletionData_wickHeadEquiv
      d.1
      (wickHeadEquiv_contraction_not_isSingle
        n d.1)
  right_inv κ := by
    apply Subtype.ext
    exact contractionHeadEquiv_headDeletionData
      κ.1 κ.2.1

/-- Reindex the still-unreduced with-prefix contraction sum by its
ambient case-(3) pairing. -/
theorem leftWithPrefixContractionSum_eq_headDeletionSum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) :
    leftWithPrefixContractionSum
        M ρ lam ε n x y ω =
      ∑ κ :
          {κ : PartialPairing (Fin (n + 1)) //
            HeadPairedWithPrefix κ},
        headPairedContractionContribution
          M ρ lam ε n
          (headDeletionData κ.1 κ.2.1)
          x y ω := by
  unfold leftWithPrefixContractionSum
  let e := withPrefixMarkedEquiv n
  calc
    _ =
        ∑ κ :
            {κ : PartialPairing (Fin (n + 1)) //
              HeadPairedWithPrefix κ},
          headPairedContractionContribution
            M ρ lam ε n (e.symm κ).1 x y ω :=
      ((e.symm.sum_comp
        (fun d =>
          headPairedContractionContribution
            M ρ lam ε n d.1 x y ω)).symm)
    _ = _ := by
      apply Fintype.sum_congr
      intro κ
      rfl

/-! ## Exact-cardinality specialization of a fixed `q` fibre -/

/-- Cast the tail type produced by `assembleCaseThree` at the exact
old order `2p+1+r` back to the paper tail type `Fin r`. -/
def caseThreeExactTailPairing
    (p r : ℕ)
    (τ :
      PartialPairing
        (Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1)))) :
    PartialPairing (Fin r) :=
  arithmeticCastPairing
    (by omega :
      (2 * p + 1 + r) + 1 -
          2 * (p + 1) =
        r)
    τ

/-- The tail cast above is an actual equivalence of pairing types, used
to reindex the finite tail sum without multiplicity. -/
def caseThreeExactTailPairingEquiv
    (p r : ℕ) :
    PartialPairing
        (Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1))) ≃
      PartialPairing (Fin r) :=
  PartialPairing.congr
    (Fin.castOrderIso
      (by omega :
        (2 * p + 1 + r) + 1 -
            2 * (p + 1) =
          r)).toEquiv

@[simp]
theorem caseThreeExactTailPairingEquiv_apply
    (p r : ℕ)
    (τ :
      PartialPairing
        (Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1)))) :
    caseThreeExactTailPairingEquiv p r τ =
      caseThreeExactTailPairing p r τ := by
  rfl

@[simp]
theorem caseThreeExactTailPairing_apply_val
    (p r : ℕ)
    (τ :
      PartialPairing
        (Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1))))
    (j :
      Fin
        ((2 * p + 1 + r) + 1 -
          2 * (p + 1))) :
    (caseThreeExactTailPairing p r τ
      (Fin.cast (by omega) j)).val =
      (τ j).val := by
  rfl

/-- At an exact old order, the canonical ambient assembly is literally
the arithmetic successor presentation used by the fixed-data
head-deletion bridge. -/
theorem assembleCaseThree_exact_eq_caseThreeHeadPairing
    (p r : ℕ)
    (σ : PartialPairing (Fin (2 * (p + 1))))
    (τ :
      PartialPairing
        (Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1)))) :
    assembleCaseThree
        (m := 2 * p + 1 + r)
        (q := p + 1) (by omega)
        σ τ =
      caseThreeHeadPairing p r σ
        (caseThreeExactTailPairing p r τ) := by
  apply PartialPairing.ext
  intro i
  apply Fin.ext
  by_cases hi :
      i.val < 2 * (p + 1)
  · let j : Fin (2 * (p + 1)) :=
      ⟨i.val, hi⟩
    have hij :
        i =
          Fin.castLE
            (by omega :
              2 * (p + 1) ≤
                (2 * p + 1 + r) + 1)
            j := by
      apply Fin.ext
      rfl
    calc
      (assembleCaseThree
          (m := 2 * p + 1 + r)
          (q := p + 1) (by omega)
          σ τ i).val =
          (assembleCaseThree
            (m := 2 * p + 1 + r)
            (q := p + 1) (by omega)
            σ τ
            (Fin.castLE
              (by omega :
                2 * (p + 1) ≤
                  (2 * p + 1 + r) + 1)
              j)).val := by
        exact congrArg
          (fun k =>
            (assembleCaseThree
              (m := 2 * p + 1 + r)
              (q := p + 1) (by omega)
              σ τ k).val)
          hij
      _ = (σ j).val := by
        unfold assembleCaseThree
        rw [appendPairingTo_apply_prefix]
        rfl
      _ =
          (appendPairing σ
            (caseThreeExactTailPairing p r τ)
            (Fin.castAdd r j)).val := by
        simp only [appendPairing_apply_castAdd]
        rfl
      _ =
          (caseThreeHeadPairing p r σ
            (caseThreeExactTailPairing p r τ)
            i).val := by
        rw [caseThreeHeadPairing_apply_val]
        apply congrArg Fin.val
        apply congrArg
          (appendPairing σ
            (caseThreeExactTailPairing p r τ))
        apply Fin.ext
        rfl
  · have hge :
        2 * (p + 1) ≤ i.val := by
      omega
    let j :
        Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1)) :=
      ⟨i.val - 2 * (p + 1), by
        have := i.isLt
        omega⟩
    let jr : Fin r :=
      Fin.cast (by omega) j
    have hij :
        i =
          suffixFin
            (by omega :
              2 * (p + 1) ≤
                (2 * p + 1 + r) + 1)
            j := by
      apply Fin.ext
      simp only [suffixFin_val]
      dsimp only [j]
      omega
    calc
      (assembleCaseThree
          (m := 2 * p + 1 + r)
          (q := p + 1) (by omega)
          σ τ i).val =
          (assembleCaseThree
            (m := 2 * p + 1 + r)
            (q := p + 1) (by omega)
            σ τ
            (suffixFin
              (by omega :
                2 * (p + 1) ≤
                  (2 * p + 1 + r) + 1)
              j)).val := by
        exact congrArg
          (fun k =>
            (assembleCaseThree
              (m := 2 * p + 1 + r)
              (q := p + 1) (by omega)
              σ τ k).val)
          hij
      _ =
          2 * (p + 1) + (τ j).val := by
        unfold assembleCaseThree
        rw [appendPairingTo_apply_suffix]
        rfl
      _ =
          2 * (p + 1) +
            (caseThreeExactTailPairing
              p r τ jr).val := by
        apply congrArg (2 * (p + 1) + ·)
        symm
        exact
          caseThreeExactTailPairing_apply_val
            p r τ j
      _ =
          (appendPairing σ
            (caseThreeExactTailPairing p r τ)
            (Fin.natAdd (2 * (p + 1)) jr)).val := by
        simp only [appendPairing_apply_natAdd]
        rfl
      _ =
          (caseThreeHeadPairing p r σ
            (caseThreeExactTailPairing p r τ)
            i).val := by
        rw [caseThreeHeadPairing_apply_val]
        apply congrArg Fin.val
        apply congrArg
          (appendPairing σ
            (caseThreeExactTailPairing p r τ))
        apply Fin.ext
        dsimp only [jr, j]
        change
          2 * (p + 1) +
              (i.val - 2 * (p + 1)) =
            i.val
        omega

/-- Head deletion respects the exact canonical case-(3) assembly. -/
theorem headDeletionData_assembleCaseThree_exact
    (p r : ℕ)
    (σ : PartialPairing (Fin (2 * (p + 1))))
    (τ :
      PartialPairing
        (Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1))))
    (hσ : IsNonSplit σ) :
    headDeletionData
        (assembleCaseThree
          (m := 2 * p + 1 + r)
          (q := p + 1) (by omega)
          σ τ)
        (assembleCaseThree_headPairedWithPrefix
          (m := 2 * p + 1 + r)
          (q := p + 1)
          (by omega) (by omega)
          σ τ hσ).1 =
      caseThreeHeadDeletionData p r σ
        (caseThreeExactTailPairing p r τ) hσ := by
  unfold caseThreeHeadDeletionData
  apply
    (contractionHeadEquiv
      (2 * p + 1 + r)).injective
  apply Subtype.ext
  rw [contractionHeadEquiv_headDeletionData,
    contractionHeadEquiv_headDeletionData]
  exact
    assembleCaseThree_exact_eq_caseThreeHeadPairing
      p r σ τ

/-- `randRI` is invariant under the canonical transport between
propositionally equal finite cardinalities. -/
theorem randRI_arithmeticCast
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {m n : ℕ} (h : m = n)
    (κ : PartialPairing (Fin m))
    (x y : T4) (ω : M.Ω) :
    randRI M ρ lam ε n
        (arithmeticCastPairing h κ) x y ω =
      randRI M ρ lam ε m κ x y ω := by
  subst n
  rfl

/-- The ambient random kernel of an exact canonical assembly is the
paper-facing appended-pairing kernel. -/
theorem randRI_assembleCaseThree_exact
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (p r : ℕ)
    (σ : PartialPairing (Fin (2 * (p + 1))))
    (τ :
      PartialPairing
        (Fin
          ((2 * p + 1 + r) + 1 -
            2 * (p + 1))))
    (x y : T4) (ω : M.Ω) :
    randRI M ρ lam ε ((2 * p + 1 + r) + 1)
        (assembleCaseThree
          (m := 2 * p + 1 + r)
          (q := p + 1) (by omega)
          σ τ)
        x y ω =
      randRI M ρ lam ε (2 * (p + 1) + r)
        (appendPairing σ
          (caseThreeExactTailPairing p r τ))
        x y ω := by
  rw [assembleCaseThree_exact_eq_caseThreeHeadPairing
    p r σ τ]
  exact
    randRI_arithmeticCast
      M ρ lam ε
      (by omega :
        2 * (p + 1) + r =
          (2 * p + 1 + r) + 1)
      (appendPairing σ
        (caseThreeExactTailPairing p r τ))
      x y ω

/-! ## Fixed fibre collapse -/

/-- A complete fixed minimal-prefix fibre: after canonical
multiplicity-one reindexing, its actual head-deletion contractions are
the corresponding ambient random kernels plus the paper counterterm
block. -/
theorem
    sum_caseThreeExactFiber_headDeletion_eq_randRI_add_counterterm
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (p r : ℕ) (x y : T4) (ω : M.Ω)
    (hhead :
      CaseThreeHeadContractionIntegrability
        M ρ ε p r x y ω)
    (hsum :
      CaseThreeSummationIntegrability
        M ρ lam ε p r x y ω) :
    (∑ K ∈ Finset.univ.filter
          (fun K :
            {κ :
                PartialPairing
                  (Fin ((2 * p + 1 + r) + 1)) //
              HeadPairedWithPrefix κ} =>
            caseThreeQ K = p + 1),
        headPairedContractionContribution
          M ρ lam ε (2 * p + 1 + r)
          (headDeletionData K.1 K.2.1)
          x y ω) =
      (∑ K ∈ Finset.univ.filter
            (fun K :
              {κ :
                  PartialPairing
                    (Fin ((2 * p + 1 + r) + 1)) //
                HeadPairedWithPrefix κ} =>
              caseThreeQ K = p + 1),
          randRI M ρ lam ε
            ((2 * p + 1 + r) + 1)
            K.1 x y ω) +
        caseThreeCountertermBlock
          M ρ lam ε (p + 1) r x y ω := by
  classical
  let E :=
    caseThreeExactTailPairingEquiv p r
  have hleft :=
    sum_caseThree_filter_equiv
      (m := 2 * p + 1 + r)
      (q := p + 1)
      (by omega) (by omega)
      (fun K :
        {κ :
            PartialPairing
              (Fin ((2 * p + 1 + r) + 1)) //
          HeadPairedWithPrefix κ} =>
        headPairedContractionContribution
          M ρ lam ε (2 * p + 1 + r)
          (headDeletionData K.1 K.2.1)
          x y ω)
  have hright :=
    sum_caseThree_filter_equiv
      (m := 2 * p + 1 + r)
      (q := p + 1)
      (by omega) (by omega)
      (fun K :
        {κ :
            PartialPairing
              (Fin ((2 * p + 1 + r) + 1)) //
          HeadPairedWithPrefix κ} =>
        randRI M ρ lam ε
          ((2 * p + 1 + r) + 1)
          K.1 x y ω)
  have hactual :
      (∑ K ∈ Finset.univ.filter
            (fun K :
              {κ :
                  PartialPairing
                    (Fin ((2 * p + 1 + r) + 1)) //
                HeadPairedWithPrefix κ} =>
              caseThreeQ K = p + 1),
          headPairedContractionContribution
            M ρ lam ε (2 * p + 1 + r)
            (headDeletionData K.1 K.2.1)
            x y ω) =
        ∑ σ :
            {σ :
                PartialPairing (Fin (2 * (p + 1))) //
              IsNonSplit σ},
          ∑ τ : PartialPairing (Fin r),
            headPairedContractionContribution
              M ρ lam ε (2 * p + 1 + r)
              (caseThreeHeadDeletionData
                p r σ.1 τ σ.2)
              x y ω := by
    calc
      _ =
          ∑ σ :
              {σ :
                  PartialPairing
                    (Fin (2 * (p + 1))) //
                IsNonSplit σ},
            ∑ τ :
                PartialPairing
                  (Fin
                    ((2 * p + 1 + r) + 1 -
                      2 * (p + 1))),
              headPairedContractionContribution
                M ρ lam ε (2 * p + 1 + r)
                (headDeletionData
                  (assembleCaseThree
                    (m := 2 * p + 1 + r)
                    (q := p + 1) (by omega)
                    σ.1 τ)
                  (assembleCaseThree_headPairedWithPrefix
                    (m := 2 * p + 1 + r)
                    (q := p + 1)
                    (by omega) (by omega)
                    σ.1 τ σ.2).1)
                x y ω := hleft
      _ =
          ∑ σ :
              {σ :
                  PartialPairing
                    (Fin (2 * (p + 1))) //
                IsNonSplit σ},
            ∑ τ :
                PartialPairing
                  (Fin
                    ((2 * p + 1 + r) + 1 -
                      2 * (p + 1))),
              headPairedContractionContribution
                M ρ lam ε (2 * p + 1 + r)
                (caseThreeHeadDeletionData p r σ.1
                  (E τ) σ.2)
                x y ω := by
        apply Fintype.sum_congr
        intro σ
        apply Fintype.sum_congr
        intro τ
        apply congrArg
          (fun d =>
            headPairedContractionContribution
              M ρ lam ε (2 * p + 1 + r)
              d x y ω)
        simpa only [E,
          caseThreeExactTailPairingEquiv_apply] using
          headDeletionData_assembleCaseThree_exact
            p r σ.1 τ σ.2
      _ = _ := by
        apply Fintype.sum_congr
        intro σ
        exact
          E.sum_comp
            (fun τ =>
              headPairedContractionContribution
                M ρ lam ε (2 * p + 1 + r)
                (caseThreeHeadDeletionData
                  p r σ.1 τ σ.2)
                x y ω)
  have hrandom :
      (∑ σ ∈ Finset.univ.filter
            (fun σ :
              PartialPairing (Fin (2 * (p + 1))) =>
              IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            randRI M ρ lam ε
              (2 * (p + 1) + r)
              (appendPairing σ τ) x y ω) =
        ∑ K ∈ Finset.univ.filter
            (fun K :
              {κ :
                  PartialPairing
                    (Fin ((2 * p + 1 + r) + 1)) //
                HeadPairedWithPrefix κ} =>
              caseThreeQ K = p + 1),
          randRI M ρ lam ε
            ((2 * p + 1 + r) + 1)
            K.1 x y ω := by
    calc
      _ =
          ∑ σ :
              {σ :
                  PartialPairing
                    (Fin (2 * (p + 1))) //
                IsNonSplit σ},
            ∑ τ : PartialPairing (Fin r),
              randRI M ρ lam ε
                (2 * (p + 1) + r)
                (appendPairing σ.1 τ) x y ω := by
        apply Finset.sum_subtype
        intro σ
        simp only [Finset.mem_filter,
          Finset.mem_univ, true_and]
      _ =
          ∑ σ :
              {σ :
                  PartialPairing
                    (Fin (2 * (p + 1))) //
                IsNonSplit σ},
            ∑ τ :
                PartialPairing
                  (Fin
                    ((2 * p + 1 + r) + 1 -
                      2 * (p + 1))),
              randRI M ρ lam ε
                ((2 * p + 1 + r) + 1)
                (assembleCaseThree
                  (m := 2 * p + 1 + r)
                  (q := p + 1) (by omega)
                  σ.1 τ)
                x y ω := by
        apply Fintype.sum_congr
        intro σ
        calc
          _ =
              ∑ τ :
                  PartialPairing
                    (Fin
                      ((2 * p + 1 + r) + 1 -
                        2 * (p + 1))),
                randRI M ρ lam ε
                  (2 * (p + 1) + r)
                  (appendPairing σ.1 (E τ))
                  x y ω := by
            exact
              (E.sum_comp
                (fun τ =>
                  randRI M ρ lam ε
                    (2 * (p + 1) + r)
                    (appendPairing σ.1 τ)
                    x y ω)).symm
          _ = _ := by
            apply Fintype.sum_congr
            intro τ
            symm
            simpa only [E,
              caseThreeExactTailPairingEquiv_apply] using
              randRI_assembleCaseThree_exact
                M ρ lam ε p r σ.1 τ x y ω
      _ = _ := hright.symm
  calc
    _ =
        ∑ σ :
            {σ :
                PartialPairing (Fin (2 * (p + 1))) //
              IsNonSplit σ},
          ∑ τ : PartialPairing (Fin r),
            headPairedContractionContribution
              M ρ lam ε (2 * p + 1 + r)
              (caseThreeHeadDeletionData
                p r σ.1 τ σ.2)
              x y ω := hactual
    _ =
        (∑ σ ∈ Finset.univ.filter
              (fun σ :
                PartialPairing (Fin (2 * (p + 1))) =>
                IsNonSplit σ),
            ∑ τ : PartialPairing (Fin r),
              randRI M ρ lam ε
                (2 * (p + 1) + r)
                (appendPairing σ τ) x y ω) +
          caseThreeCountertermBlock
            M ρ lam ε (p + 1) r x y ω :=
      sum_headPairedCaseThreeContribution_eq_randRI_add_counterterm
        M ρ lam ε p r x y ω hhead hsum
    _ = _ := by
      rw [hrandom]

/-! ## All minimal prefixes at a fixed old order -/

/-- Analytic ledger for every paper minimal-prefix order
`q ∈ [1, ⌊(n+1)/2⌋]`.  The fixed-data bridge uses zero-based
`q-1`, while the counterterm and the paper use the positive order
`q`. -/
structure LeftWithPrefixCaseThreeIntegrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : Prop where
  contraction :
    ∀ q ∈ Finset.Icc 1 ((n + 1) / 2),
      CaseThreeHeadContractionIntegrability
        M ρ ε (q - 1) (n + 1 - 2 * q)
        x y ω
  summation :
    ∀ q ∈ Finset.Icc 1 ((n + 1) / 2),
      CaseThreeSummationIntegrability
        M ρ lam ε (q - 1) (n + 1 - 2 * q)
        x y ω

/-- **Closed case-(3) branch of Proposition 3.4.**

At fixed old order `n`, summing every actual with-prefix Wick
contraction over the unique minimal prefix
`q ∈ Icc 1 ((n+1)/2)` gives every ambient with-prefix random kernel
once, plus the full fixed-order counterterm sum. -/
theorem
    leftWithPrefixContractionSum_eq_randRISum_add_countertermSum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hint :
      LeftWithPrefixCaseThreeIntegrability
        M ρ lam ε n x y ω) :
    leftWithPrefixContractionSum
        M ρ lam ε n x y ω =
      leftWithPrefixRandRISum
          M ρ lam ε n x y ω +
        leftOrderCountertermSum
          M ρ lam ε n x y ω := by
  rw [leftWithPrefixContractionSum_eq_headDeletionSum]
  unfold leftWithPrefixRandRISum
  unfold leftOrderCountertermSum
  rw [sum_caseThree_by_q]
  rw [sum_caseThree_by_q]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hqmem
  have hqbounds := Finset.mem_Icc.mp hqmem
  have hqne : q ≠ 0 := by
    omega
  obtain ⟨p, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero hqne
  have htwo :
      2 * (p + 1) ≤ n + 1 := by
    have hmul :=
      (Nat.le_div_iff_mul_le
        (by omega : 0 < 2)).mp hqbounds.2
    omega
  obtain ⟨r, hr⟩ :=
    Nat.exists_eq_add_of_le htwo
  have hn :
      n = 2 * p + 1 + r := by
    omega
  subst n
  have hhead :
      CaseThreeHeadContractionIntegrability
        M ρ ε p r x y ω := by
    convert
      hint.contraction (p + 1) hqmem using 1 <;>
      omega
  have hsum :
      CaseThreeSummationIntegrability
        M ρ lam ε p r x y ω := by
    convert
      hint.summation (p + 1) hqmem using 1 <;>
      omega
  have htail :
      (2 * p + 1 + r) + 1 -
          2 * (p + 1) =
        r := by
    omega
  simp only [Nat.succ_eq_add_one, htail]
  exact
    sum_caseThreeExactFiber_headDeletion_eq_randRI_add_counterterm
      M ρ lam ε p r x y ω hhead hsum

/-! ## Direct assembly into the left parametrix identity -/

/-- The complete left preconditioned remainder identity with the
case-(3) equality discharged by the explicit all-prefix integrability
ledger above.  No branch identity remains as a hypothesis. -/
theorem
    leftPreconditionedParametrixAction_eq_green_add_remainder_of_integrability
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω)
    (hsource :
      ∀ n ∈ Finset.range A,
        LeftOrderSourceIntegrability
          M ρ lam ε n x y ω)
    (hsplit :
      ∀ n ∈ Finset.range A,
        ∀ κ : PartialPairing (Fin n),
          LeftPairingSplitIntegrability
            M ρ ε n κ x y ω)
    (hcreation :
      ∀ n ∈ Finset.range A,
        ∀ κ : PartialPairing (Fin n),
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              randIntegrand M ρ ε
                (wickHeadEquiv n (Sum.inl κ))
                (assemble x y u) ω)
            (Measure.pi fun _ => paperMeasure))
    (hnoPrefix :
      ∀ n ∈ Finset.range A,
        ∀ d :
            {d : MarkedSingle (Fin n) //
              ¬markedHasHeadPrefix d},
          Integrable
            (fun u : Fin (n + 1) → T4 =>
              randIntegrand M ρ ε
                (wickHeadEquiv n
                  (Sum.inr d.1))
                (assemble x y u) ω)
            (Measure.pi fun _ => paperMeasure))
    (hcaseThree :
      ∀ n ∈ Finset.range A,
        LeftWithPrefixCaseThreeIntegrability
          M ρ lam ε n x y ω) :
    leftPreconditionedParametrixAction
        M ρ lam ε A x y ω =
      greenFn (x - y) +
        leftPreconditionedRemainder
          M ρ lam ε A x y ω := by
  apply
    leftPreconditionedParametrixAction_eq_green_add_remainder_of_headCases
      M ρ lam ε A x y ω
      hsource hsplit hcreation hnoPrefix
  intro n hn
  exact
    leftWithPrefixContractionSum_eq_randRISum_add_countertermSum
      M ρ lam ε n x y ω
      (hcaseThree n hn)

end PartialPairing

end

end Anderson4D
