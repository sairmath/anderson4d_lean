import Anderson4D.PermSum.SingleScaleCommonProduct
import Anderson4D.PermSum.SingleScaleOccurrenceLedger
import Anderson4D.PermSum.SingleScalePayoffLedger
import Anderson4D.PermSum.SingleScalePowerReverse

set_option warningAsError true
set_option autoImplicit false

/-!
# Completing the common product at the anchor

The common target ledger omits the distinguished anchor.  Completing its
occurrence and parent-scale factors costs the reciprocal of the anchor
base factor.  Since the occurrence atom `X * sqrt Y` is at least one, this
is bounded by the printed occurrence factor times the full word
parent-scale product and `N_anchor^2`.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Parent-scale factor attached to every position of an active word. -/
def nxWordBaseScaleFactor
    {t : PlaneTree} {Nm : HeppMarking t}
    {mu : Multiplicities t} {m : ℕ}
    (x : Fin m → ActiveNXClass Nm mu) : ℝ :=
  ∏ i : Fin m, ((x i).1.1 : ℝ)⁻¹ ^ 2

/-- The local common target is the occurrence atom, the parent-scale
factor, and the optional skipped-edge atom. -/
theorem paperDyadicLocalTarget_eq_occurrence_mul_scale_mul_skip
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t) (a : NXClass) (skipped : Bool) :
    paperDyadicLocalTarget Nm mu a skipped =
      paper588OccurrenceAtom Nm mu a * (a.1 : ℝ)⁻¹ ^ 2 *
        (if skipped then paper588SkippedAtom Nm mu a else 1) := by
  cases skipped <;>
    simp [paperDyadicLocalTarget, paperDyadicBase,
      paperDyadicSkipXi, paper588OccurrenceAtom,
      paper588SkippedAtom, paperDyadicY, Nat.cast_mul]

/-- Every active occurrence atom satisfies `X * sqrt Y ≥ 1`. -/
theorem one_le_paper588OccurrenceAtom
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (a : ActiveNXClass Nm mu) :
    1 ≤ paper588OccurrenceAtom Nm mu a.1 := by
  have hXnat : 1 ≤ a.1.2 :=
    one_le_nxClass_X Nm mu a.2
  have hX : (1 : ℝ) ≤ (a.1.2 : ℝ) := by
    exact_mod_cast hXnat
  have hYnat : 1 ≤ (singleScaleSigma2 Nm mu a.1).2 := by
    unfold singleScaleSigma2 dyadicFloor
    exact Nat.one_le_pow _ _ (by norm_num)
  have hY : (1 : ℝ) ≤
      ((singleScaleSigma2 Nm mu a.1).2 : ℝ) := by
    exact_mod_cast hYnat
  unfold paper588OccurrenceAtom
  have hsqrt :
      1 ≤ Real.sqrt
        ((singleScaleSigma2 Nm mu a.1).2 : ℝ) := by
    exact Real.one_le_sqrt.mpr hY
  simpa using
    mul_le_mul hX hsqrt zero_le_one (zero_le_one.trans hX)

/-- Active parent scales are strictly positive. -/
theorem activeNXClass_parentScale_pos
    {t : PlaneTree} (Nm : HeppMarking t)
    (mu : Multiplicities t)
    (a : ActiveNXClass Nm mu) :
    0 < a.1.1 := by
  obtain ⟨l, _hl, hclass⟩ := Finset.mem_image.mp a.2
  have hfirst := congrArg Prod.fst hclass
  simpa [singleScaleSigma1] using
    (hfirst ▸ scaleN_pos Nm (parentV l.1))

private theorem prod_word_eq_anchor_mul_outward
    {m : ℕ}
    (anchor : Fin m) (f : Fin m → ℝ) :
    (∏ i : Fin m, f i) =
      f anchor *
        ∏ edge : AdjacentIndex m,
          f (outwardEdgeTargetPosition anchor edge) := by
  rw [← prod_nonanchor_eq_prod_outwardEdgeTarget]
  exact
    (Finset.mul_prod_erase
      (Finset.univ : Finset (Fin m)) f
      (Finset.mem_univ anchor)).symm

private theorem prod_ite_decide_mem
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → ℝ) :
    (∏ i : α, if decide (i ∈ s) then f i else 1) =
      ∏ i ∈ s, f i := by
  classical
  simpa only [decide_eq_true_eq] using
    Fintype.prod_ite_mem s f

/-- Exact factorization of the phase-independent common product into
non-anchor occurrence atoms, non-anchor parent scales, and skipped atoms. -/
theorem locatedLedgerCommonProduct_finAnchor_eq_occurrence_scale_skip
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor x O) =
      (∏ edge : AdjacentIndex m,
        paper588OccurrenceAtom Nm mu
          (x (outwardEdgeTargetPosition anchor edge)).1) *
      (∏ edge : AdjacentIndex m,
        ((x (outwardEdgeTargetPosition anchor edge)).1.1 : ℝ)⁻¹ ^ 2) *
      (∏ edge ∈ O,
        paper588SkippedAtom Nm mu
          (x (outwardEdgeTargetPosition anchor edge)).1) := by
  rw [locatedLedgerCommonProduct_finAnchor_eq_edgeProduct]
  simp_rw [
    paperDyadicLocalTarget_eq_occurrence_mul_scale_mul_skip]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [prod_ite_decide_mem]

/--
Completing the missing anchor gives an exact identity.  The only extra
factor is the anchor occurrence atom; the anchor parent-scale inverse
cancels against `N_anchor^2`.
-/
theorem outward588_mul_wordBaseScale_mul_anchorScale_sq
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    outward588WordOccurrenceFactor Nm mu anchor O x *
          nxWordBaseScaleFactor x *
          ((x anchor).1.1 : ℝ) ^ 2 =
      locatedLedgerCommonProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor x O) *
        paper588OccurrenceAtom Nm mu (x anchor).1 := by
  have hN :
      ((x anchor).1.1 : ℝ) ≠ 0 := by
    exact_mod_cast
      (activeNXClass_parentScale_pos Nm mu (x anchor)).ne'
  rw [locatedLedgerCommonProduct_finAnchor_eq_occurrence_scale_skip]
  unfold outward588WordOccurrenceFactor
    assigned588WordOccurrenceFactor nxWordBaseScaleFactor
  rw [prod_word_eq_anchor_mul_outward
      anchor (fun i => paper588OccurrenceAtom Nm mu (x i).1),
    prod_word_eq_anchor_mul_outward
      anchor (fun i => ((x i).1.1 : ℝ)⁻¹ ^ 2)]
  field_simp [hN]

/--
Paper-facing anchor completion: the phase-independent common factor is
bounded by the outward occurrence factor, the full word parent-scale
factor, and the explicit `N_anchor^2` cost.
-/
theorem locatedLedgerCommonProduct_finAnchor_le_completed
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedLedgerCommonProduct Nm mu
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor x O) ≤
      outward588WordOccurrenceFactor Nm mu anchor O x *
        nxWordBaseScaleFactor x *
        ((x anchor).1.1 : ℝ) ^ 2 := by
  rw [outward588_mul_wordBaseScale_mul_anchorScale_sq
    Nm mu leftPhase rightPhase anchor x O]
  exact le_mul_of_one_le_right
    (locatedLedgerCommonProduct_nonneg Nm mu _)
    (one_le_paper588OccurrenceAtom Nm mu (x anchor))

/-! ## Rewriting the full word parent-scale product by original leaves -/

/-- A valid active class word contains exactly the leaf-multiplicity power
of every original parent scale. -/
theorem nxWordBaseScaleFactor_eq_leafProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu)) :
    nxWordBaseScaleFactor x =
      ∏ l : HeppLeaf t,
        (((scaleN Nm (parentV l.1) : ℝ)⁻¹ ^ 2) ^
          leafMultiplicity mu l) := by
  rw [nxWordBaseScaleFactor,
    prod_word_eq_prod_pow_occurrenceCount
      Nm mu x (fun a => (a.1 : ℝ)⁻¹ ^ 2)]
  have hocc :
      (∏ a ∈ nxCarrier Nm mu,
          ((a.1 : ℝ)⁻¹ ^ 2) ^ nxWordOccurrenceCount x a) =
        ∏ a ∈ nxCarrier Nm mu,
          ((a.1 : ℝ)⁻¹ ^ 2) ^ multiplicityNX Nm mu a := by
    apply Finset.prod_congr rfl
    intro a ha
    rw [nxWordOccurrenceCount_eq_multiplicityNX Nm mu x hx a ha]
  rw [hocc]
  calc
    (∏ a ∈ nxCarrier Nm mu,
        ((a.1 : ℝ)⁻¹ ^ 2) ^ multiplicityNX Nm mu a) =
        ∏ a ∈ nxCarrier Nm mu,
          ∏ l ∈ leavesAtNX Nm mu a,
            (((a.1 : ℝ)⁻¹ ^ 2) ^
              leafMultiplicity mu l) := by
          apply Finset.prod_congr rfl
          intro a ha
          rw [multiplicityNX, ← Finset.prod_pow_eq_pow_sum]
    _ = ∏ a ∈ nxCarrier Nm mu,
          ∏ l ∈ leavesAtNX Nm mu a,
            (((scaleN Nm (parentV l.1) : ℝ)⁻¹ ^ 2) ^
              leafMultiplicity mu l) := by
          apply Finset.prod_congr rfl
          intro a ha
          apply Finset.prod_congr rfl
          intro l hl
          have hclass :
              singleScaleSigma1 Nm mu l = a :=
            (Finset.mem_filter.mp hl).2
          have hfirst := congrArg Prod.fst hclass
          simp only [singleScaleSigma1] at hfirst
          rw [hfirst]
    _ = ∏ l : HeppLeaf t,
          (((scaleN Nm (parentV l.1) : ℝ)⁻¹ ^ 2) ^
            leafMultiplicity mu l) := by
          unfold leavesAtNX nxCarrier
          exact
            Finset.prod_fiberwise_of_maps_to
              (s := (Finset.univ : Finset (HeppLeaf t)))
              (t := Finset.univ.image (singleScaleSigma1 Nm mu))
              (g := singleScaleSigma1 Nm mu)
              (fun l hl => Finset.mem_image_of_mem _ hl)
              (fun l =>
                (((scaleN Nm (parentV l.1) : ℝ)⁻¹ ^ 2) ^
                  leafMultiplicity mu l))

/-- The natural inverse-square power carried by a class word is the
integer-power notation used by the paper-facing payoff ledger. -/
private theorem inv_sq_pow_eq_zpow_neg_two_mul
    (a : ℝ) (m : ℕ) :
    (a⁻¹ ^ 2) ^ m =
      a ^ ((-2 : ℤ) * (m : ℤ)) := by
  rw [← pow_mul, ← zpow_natCast, inv_zpow, ← zpow_neg]
  congr 1

/-- A valid active word supplies exactly the global inverse-square
leaf-scale product that occurs on the left of (5.89). -/
theorem nxWordBaseScaleFactor_eq_leafZpowProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu)) :
    nxWordBaseScaleFactor x =
      ∏ l : HeppLeaf t,
        (scaleN Nm (parentV l.1) : ℝ) ^
          ((-2 : ℤ) * (leafMultiplicity mu l : ℤ)) := by
  rw [nxWordBaseScaleFactor_eq_leafProduct Nm mu x hx]
  apply Fintype.prod_congr
  intro l
  exact inv_sq_pow_eq_zpow_neg_two_mul
    (scaleN Nm (parentV l.1) : ℝ)
    (leafMultiplicity mu l)

/--
Exact end-of-(5.88) ledger after choosing an original leaf in the
distinguished anchor class.  The anchor-scale square completes the
distinguished-parent factor in `singleScaleLeafPower`.
-/
theorem wordBaseFactorialOuterPayoff_mul_anchorScale_sq_eq_leafPower
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu))
    (l₀ : HeppLeaf t)
    (hl₀ : l₀ ∈ leavesAtNX Nm mu (x anchor).1) :
    nxWordBaseScaleFactor x *
          (∏ l : HeppLeaf t,
            sqrtFactorial (leafMultiplicity mu l) *
              originalOuterLeafPayoff Nm mu compound l) *
          ((x anchor).1.1 : ℝ) ^ 2 =
      (∏ l ∈ simpleLeaves t compound,
          sqrtFactorial (mu.m l)) *
        (∏ l ∈ compoundLeaves t compound,
          factorialThreeQuarters (mu.m l)) *
        singleScaleLeafPower Nm mu compound l₀ := by
  have hclass :
      singleScaleSigma1 Nm mu l₀ = (x anchor).1 :=
    (Finset.mem_filter.mp hl₀).2
  have hparent :
      scaleN Nm (parentV l₀.1) = (x anchor).1.1 := by
    simpa only [singleScaleSigma1] using congrArg Prod.fst hclass
  rw [nxWordBaseScaleFactor_eq_leafZpowProduct Nm mu x hx,
    globalBaseScaleFactorialOuterPayoff_eq]
  unfold singleScaleLeafPower
  rw [hparent]
  ac_rfl

/-- Every valid active word admits an original anchor leaf realizing the
exact completed payoff ledger. -/
theorem exists_anchorLeaf_wordBaseFactorialOuterPayoff_eq_leafPower
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) (anchor : Fin m)
    (x : Fin m → ActiveNXClass Nm mu)
    (hx : x ∈ validWords (M := m) (activeNXMultiplicity Nm mu)) :
    ∃ l₀ : HeppLeaf t,
      l₀ ∈ leavesAtNX Nm mu (x anchor).1 ∧
        nxWordBaseScaleFactor x *
              (∏ l : HeppLeaf t,
                sqrtFactorial (leafMultiplicity mu l) *
                  originalOuterLeafPayoff Nm mu compound l) *
              ((x anchor).1.1 : ℝ) ^ 2 =
          (∏ l ∈ simpleLeaves t compound,
              sqrtFactorial (mu.m l)) *
            (∏ l ∈ compoundLeaves t compound,
              factorialThreeQuarters (mu.m l)) *
            singleScaleLeafPower Nm mu compound l₀ := by
  obtain ⟨l₀, hl₀⟩ :=
    leavesAtNX_nonempty Nm mu (x anchor).2
  exact ⟨l₀, hl₀,
    wordBaseFactorialOuterPayoff_mul_anchorScale_sq_eq_leafPower
      Nm mu compound anchor x hx l₀ hl₀⟩

end XYCluster

end

end Anderson4D
