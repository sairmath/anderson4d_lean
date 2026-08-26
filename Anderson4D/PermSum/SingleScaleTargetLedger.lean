import Anderson4D.PermSum.SingleScalePosition

/-!
# Occurrence-level target ledger for the one-parity estimate

The mixed eliminator produces one target for every scheduled block.  This
file expands those targets without turning repeated scalar losses into a
set: the loss ledger is a `List`, so every occurrence is retained.

For each located block the target is split into four factors:

* the common local factors of (5.87);
* the scalar losses `sqrt Y` and `Xi⁻¹`;
* the explicit rough `(N/R)²` factors;
* the precise-pair dyadic gain.

The resulting identity is exact.  In particular, no gain is attached to a
single or rough-pair block, and no scalar loss is attached to a precise pair.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-- Common (5.87) local factors contributed by one located block. -/
noncomputable def locatedBlockCommonTarget
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    LocatedNXParityBlock (m := m) Nm mu → ℝ
  | .single _ a skipped =>
      paperDyadicLocalTarget Nm mu a.1 skipped
  | .pair _ _ p =>
      paperDyadicLocalTarget Nm mu p.left.1 p.skipLeft *
        paperDyadicLocalTarget Nm mu p.right.1 p.skipRight
  | .roughPair _ _ p =>
      paperDyadicLocalTarget Nm mu p.left.1 p.skipLeft *
        paperDyadicLocalTarget Nm mu p.right.1 p.skipRight

/--
Occurrence ledger of scalar losses.  A singleton contributes two entries
and a rough pair contributes four; a precise pair contributes none.
-/
noncomputable def locatedBlockLossAtoms
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    LocatedNXParityBlock (m := m) Nm mu → List ℝ
  | .single _ a skipped =>
      [Real.sqrt (paperDyadicY Nm mu a.1),
        paperDyadicXiInv Nm mu a.1 skipped]
  | .pair _ _ _ => []
  | .roughPair _ _ p =>
      [Real.sqrt (paperDyadicY Nm mu p.left.1),
        paperDyadicXiInv Nm mu p.left.1 p.skipLeft,
        Real.sqrt (paperDyadicY Nm mu p.right.1),
        paperDyadicXiInv Nm mu p.right.1 p.skipRight]

/-- Explicit rough scale payoff contributed by one block. -/
noncomputable def locatedBlockRoughScale
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (R : ℝ) :
    LocatedNXParityBlock (m := m) Nm mu → ℝ
  | .single _ a skipped =>
      paperDyadicRoughScaleGain R a.1 skipped
  | .pair _ _ _ => 1
  | .roughPair _ _ p =>
      paperDyadicRoughScaleGain R p.left.1 p.skipLeft *
        paperDyadicRoughScaleGain R p.right.1 p.skipRight

/-- The precise-pair gain; exceptional blocks deliberately contribute `1`. -/
noncomputable def locatedBlockPreciseGain
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    LocatedNXParityBlock (m := m) Nm mu → ℝ
  | .single _ _ _ => 1
  | .pair _ _ p =>
      dyadicForwardGain
        (singleScaleSigma2 Nm mu p.left.1)
        (singleScaleSigma2 Nm mu p.right.1)
  | .roughPair _ _ _ => 1

theorem locatedBlockCommonTarget_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (b : LocatedNXParityBlock (m := m) Nm mu) :
    0 ≤ locatedBlockCommonTarget Nm mu b := by
  cases b with
  | single _ a skipped =>
      exact paperDyadicLocalTarget_nonneg Nm mu a.1 skipped
  | pair _ _ p | roughPair _ _ p =>
      exact mul_nonneg
        (paperDyadicLocalTarget_nonneg Nm mu p.left.1 p.skipLeft)
        (paperDyadicLocalTarget_nonneg Nm mu p.right.1 p.skipRight)

theorem locatedBlockRoughScale_nonneg
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (R : ℝ) (b : LocatedNXParityBlock (m := m) Nm mu) :
    0 ≤ locatedBlockRoughScale R b := by
  cases b with
  | single _ a skipped =>
      exact paperDyadicRoughScaleGain_nonneg R a.1 skipped
  | pair _ _ _ =>
      exact zero_le_one
  | roughPair _ _ p =>
      exact mul_nonneg
        (paperDyadicRoughScaleGain_nonneg R p.left.1 p.skipLeft)
        (paperDyadicRoughScaleGain_nonneg R p.right.1 p.skipRight)

theorem locatedBlockPreciseGain_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (b : LocatedNXParityBlock (m := m) Nm mu) :
    0 ≤ locatedBlockPreciseGain Nm mu b := by
  cases b with
  | single _ _ _ | roughPair _ _ _ =>
      exact zero_le_one
  | pair _ _ p =>
      exact dyadicForwardGain_nonneg _ _

/-- Exact target split for a single scheduled occurrence. -/
theorem nxParityBlockTarget_analyticBlock_eq_ledgers
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (hR : 0 < R)
    (b : LocatedNXParityBlock (m := m) Nm mu) :
    nxParityBlockTarget Nm mu R b.analyticBlock =
      locatedBlockCommonTarget Nm mu b *
        (locatedBlockLossAtoms Nm mu b).prod *
        locatedBlockRoughScale R b *
        locatedBlockPreciseGain Nm mu b := by
  cases b with
  | single i a skipped =>
      rw [LocatedNXParityBlock.analyticBlock, nxParityBlockTarget,
        paperDyadicSingleRoughTarget_eq_common_mul_losses
          Nm mu R hR a.2 skipped]
      simp only [locatedBlockCommonTarget, locatedBlockLossAtoms,
        locatedBlockRoughScale, locatedBlockPreciseGain,
        List.prod_cons, List.prod_nil, mul_one]
      ring
  | pair i j p =>
      simp only [LocatedNXParityBlock.analyticBlock, nxParityBlockTarget,
        locatedBlockCommonTarget, locatedBlockLossAtoms,
        locatedBlockRoughScale, locatedBlockPreciseGain,
        List.prod_nil, mul_one]
      rfl
  | roughPair i j p =>
      rw [LocatedNXParityBlock.analyticBlock, nxParityBlockTarget,
        paperDyadicPairRoughTarget_eq_common_mul_losses
          Nm mu R hR p.left.2 p.right.2 p.skipLeft p.skipRight]
      simp only [locatedBlockCommonTarget, locatedBlockLossAtoms,
        locatedBlockRoughScale, locatedBlockPreciseGain,
        List.prod_cons, List.prod_nil, mul_one]
      ring

/-- All scalar-loss occurrences in a located schedule. -/
noncomputable def locatedLedgerLossAtoms
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) : List ℝ :=
  bs.flatMap (locatedBlockLossAtoms Nm mu)

/-- Product of all common local factors in a located schedule. -/
noncomputable def locatedLedgerCommonProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) : ℝ :=
  (bs.map (locatedBlockCommonTarget Nm mu)).prod

/-- Product of all explicit rough scale factors in a located schedule. -/
noncomputable def locatedLedgerRoughScaleProduct
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (R : ℝ)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) : ℝ :=
  (bs.map (locatedBlockRoughScale R)).prod

/-- Product of all retained precise-pair gains in a located schedule. -/
noncomputable def locatedLedgerPreciseGainProduct
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) : ℝ :=
  (bs.map (locatedBlockPreciseGain Nm mu)).prod

/-- Exact product normal form, retaining multiplicities of scalar losses. -/
theorem nxParityBlockTarget_product_eq_ledgers
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (hR : 0 < R)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (bs.map fun b =>
        nxParityBlockTarget Nm mu R b.analyticBlock).prod =
      locatedLedgerCommonProduct Nm mu bs *
        (locatedLedgerLossAtoms Nm mu bs).prod *
        locatedLedgerRoughScaleProduct R bs *
        locatedLedgerPreciseGainProduct Nm mu bs := by
  induction bs with
  | nil =>
      simp [locatedLedgerCommonProduct, locatedLedgerLossAtoms,
        locatedLedgerRoughScaleProduct, locatedLedgerPreciseGainProduct]
  | cons b bs ih =>
      rw [List.map_cons, List.prod_cons,
        nxParityBlockTarget_analyticBlock_eq_ledgers Nm mu R hR b, ih]
      simp only [locatedLedgerCommonProduct, locatedLedgerLossAtoms,
        locatedLedgerRoughScaleProduct, locatedLedgerPreciseGainProduct,
        List.flatMap_cons, List.prod_append, List.map_cons, List.prod_cons]
      ring

/-- The length of the occurrence ledger is exactly `2·single + 4·rough`. -/
theorem length_locatedLedgerLossAtoms
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (locatedLedgerLossAtoms Nm mu bs).length =
      positionLossAtomBudget
        (nxParitySingleCount
          (bs.map LocatedNXParityBlock.analyticBlock))
        (nxParityRoughPairCount
          (bs.map LocatedNXParityBlock.analyticBlock)) := by
  induction bs with
  | nil =>
      simp [locatedLedgerLossAtoms, positionLossAtomBudget,
        nxParitySingleCount, nxParityRoughPairCount]
  | cons b bs ih =>
      unfold locatedLedgerLossAtoms at ih ⊢
      simp only [List.flatMap_cons, List.length_append, List.map_cons]
      rw [ih]
      cases b <;>
        simp [locatedBlockLossAtoms,
          LocatedNXParityBlock.analyticBlock, positionLossAtomBudget] <;>
        omega

theorem mem_locatedLedgerLossAtoms_nonneg
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    {x : ℝ} (hx : x ∈ locatedLedgerLossAtoms Nm mu bs) :
    0 ≤ x := by
  rw [locatedLedgerLossAtoms, List.mem_flatMap] at hx
  obtain ⟨b, _hb, hxb⟩ := hx
  cases b with
  | single i a skipped =>
      simp [locatedBlockLossAtoms] at hxb
      rcases hxb with rfl | rfl
      · exact Real.sqrt_nonneg _
      · exact paperDyadicXiInv_nonneg Nm mu a.1 skipped
  | pair i j p =>
      simp [locatedBlockLossAtoms] at hxb
  | roughPair i j p =>
      simp [locatedBlockLossAtoms] at hxb
      rcases hxb with rfl | rfl | rfl | rfl
      · exact Real.sqrt_nonneg _
      · exact paperDyadicXiInv_nonneg Nm mu p.left.1 p.skipLeft
      · exact Real.sqrt_nonneg _
      · exact paperDyadicXiInv_nonneg Nm mu p.right.1 p.skipRight

theorem mem_locatedLedgerLossAtoms_le_totalMultiplicity
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    {x : ℝ} (hx : x ∈ locatedLedgerLossAtoms Nm mu bs) :
    x ≤ totalMultiplicity mu := by
  rw [locatedLedgerLossAtoms, List.mem_flatMap] at hx
  obtain ⟨b, _hb, hxb⟩ := hx
  cases b with
  | single i a skipped =>
      simp [locatedBlockLossAtoms] at hxb
      rcases hxb with rfl | rfl
      · exact paperDyadicSqrtY_le_totalMultiplicity Nm mu a.2
      · exact paperDyadicXiInv_le_totalMultiplicity Nm mu a.2 skipped
  | pair i j p =>
      simp [locatedBlockLossAtoms] at hxb
  | roughPair i j p =>
      simp [locatedBlockLossAtoms] at hxb
      rcases hxb with rfl | rfl | rfl | rfl
      · exact paperDyadicSqrtY_le_totalMultiplicity Nm mu p.left.2
      · exact paperDyadicXiInv_le_totalMultiplicity
          Nm mu p.left.2 p.skipLeft
      · exact paperDyadicSqrtY_le_totalMultiplicity Nm mu p.right.2
      · exact paperDyadicXiInv_le_totalMultiplicity
          Nm mu p.right.2 p.skipRight

private theorem list_prod_le_const_pow_length
    (xs : List ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (hle : ∀ x ∈ xs, x ≤ M) :
    xs.prod ≤ M ^ xs.length := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.prod_cons, List.length_cons]
      calc
        x * xs.prod ≤ M * M ^ xs.length :=
          mul_le_mul
            (hle x (by simp))
            (ih (fun y hy => hnonneg y (by simp [hy]))
              (fun y hy => hle y (by simp [hy])))
            (List.prod_nonneg fun y hy => hnonneg y (by simp [hy]))
            hM
        _ = M ^ (xs.length + 1) := by
          rw [pow_succ]
          ring

/--
At most twenty scalar-loss occurrences are absorbed by the explicit
universal exponential.  This is a list theorem, so repeated equal atoms are
counted with their true multiplicity.
-/
theorem locatedLedgerLossAtoms_prod_le_positionLossBase_pow
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (hcard : (locatedLedgerLossAtoms Nm mu bs).length ≤ 20) :
    (locatedLedgerLossAtoms Nm mu bs).prod ≤
      (positionLossBase : ℝ) ^ totalMultiplicity mu := by
  have hM : (1 : ℝ) ≤ totalMultiplicity mu := by
    exact_mod_cast (le_trans (by omega) (two_le_totalMultiplicity mu))
  have hprod :
      (locatedLedgerLossAtoms Nm mu bs).prod ≤
        (totalMultiplicity mu : ℝ) ^
          (locatedLedgerLossAtoms Nm mu bs).length :=
    list_prod_le_const_pow_length
      (locatedLedgerLossAtoms Nm mu bs) (totalMultiplicity mu : ℝ)
      (by linarith)
      (fun x hx => mem_locatedLedgerLossAtoms_nonneg Nm mu bs hx)
      (fun x hx => mem_locatedLedgerLossAtoms_le_totalMultiplicity
        Nm mu bs hx)
  calc
    (locatedLedgerLossAtoms Nm mu bs).prod ≤
        (totalMultiplicity mu : ℝ) ^
          (locatedLedgerLossAtoms Nm mu bs).length := hprod
    _ ≤ (totalMultiplicity mu : ℝ) ^ 20 :=
      pow_le_pow_right₀ hM hcard
    _ ≤ (positionLossBase : ℝ) ^ totalMultiplicity mu := by
      exact_mod_cast
        pow_twenty_le_positionLossBase_pow (totalMultiplicity mu)

/-- Concrete loss absorption for the marked anchored schedule. -/
theorem finAnchorNXCoarse_lossAtoms_prod_le
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (locatedLedgerLossAtoms Nm mu
      (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O)).prod ≤
      (positionLossBase : ℝ) ^ totalMultiplicity mu := by
  apply locatedLedgerLossAtoms_prod_le_positionLossBase_pow
  rw [length_locatedLedgerLossAtoms]
  rw [map_analyticBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
  exact finAnchorNXCoarseLedgerWithPhases_lossAtomBudget_le_twenty
    Nm mu leftPhase rightPhase anchor cls O

/-- Exact normal form for the concrete marked anchored schedule. -/
theorem finAnchorNXCoarse_targetProduct_eq_ledgers
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (hR : 0 < R)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    ((finAnchorNXCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O).map fun b =>
      nxParityBlockTarget Nm mu R b).prod =
      locatedLedgerCommonProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O) *
        (locatedLedgerLossAtoms Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O)).prod *
        locatedLedgerRoughScaleProduct R
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O) *
        locatedLedgerPreciseGainProduct Nm mu
          (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O) := by
  rw [← map_analyticBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
  simpa only [List.map_map, Function.comp_def] using
    nxParityBlockTarget_product_eq_ledgers Nm mu R hR
      (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O)

end XYCluster

end

end Anderson4D
