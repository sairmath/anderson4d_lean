import Anderson4D.PermSum.SingleScaleInnerAssembly
import Anderson4D.PermSum.SingleScaleAnchoredSequence

/-!
# Position bookkeeping for the fixed-class inner estimate

This file isolates the part of paper (5.87) which depends on the position of
the distinguished (minimal parent-scale) leaf in the permutation.

There are two independent issues.

* Cutting the chain at the distinguished position produces a left run and a
  right run.  Pairing consecutive positions in either parity leaves at most
  two singletons on each run, hence at most four altogether.  Choosing at
  most three rough pair blocks then creates at most
  `2 * 4 + 4 * 3 = 20` scalar losses.
* A rough block is not literally the common target in (5.87).  The exact
  comparison loses `sqrt Y` and, for a skipped incoming edge, `Xi⁻¹`.
  Both atoms are bounded by the total multiplicity.  The resulting
  polynomial `m^20` is bounded here by the explicit exponential
  `(2^20)^m`.

The last section records the orientation issue on the left of the cut.  Its
gain is the forward gain of the reversed class pair, and the concrete
retained-edge interface preserves that orientation.  The exact reindexing
to the bidirectional sequence product is proved in `SingleScaleAnchorGlue`;
no pointwise forward/reverse comparison is assumed here.
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

namespace XYCluster

/-! ## The two scalar losses in a rough local target -/

/-- The inverse of the paper factor `Xi`.  We keep it as a separate atom so
that the `20`-loss ledger counts `sqrt Y` and `Xi⁻¹` separately. -/
noncomputable def paperDyadicXiInv {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) (skipped : Bool) : ℝ :=
  if skipped then
    Real.sqrt ((a.2 : ℝ) * paperDyadicY Nm mu a)
  else 1

/-- The explicit `(N/R)²` supplied by a rough estimate when the incoming
edge is skipped. -/
noncomputable def paperDyadicRoughScaleGain
    (R : ℝ) (a : NXClass) (skipped : Bool) : ℝ :=
  if skipped then ((a.1 : ℝ) / R) ^ 2 else 1

theorem paperDyadicXiInv_nonneg {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (a : NXClass) (skipped : Bool) :
    0 ≤ paperDyadicXiInv Nm mu a skipped := by
  unfold paperDyadicXiInv
  split_ifs <;> positivity

theorem paperDyadicRoughScaleGain_nonneg
    (R : ℝ) (a : NXClass) (skipped : Bool) :
    0 ≤ paperDyadicRoughScaleGain R a skipped := by
  unfold paperDyadicRoughScaleGain
  split_ifs <;> positivity

private theorem active_paperDyadicY_pos {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (_ha : a ∈ nxCarrier Nm mu) :
    0 < paperDyadicY Nm mu a := by
  unfold paperDyadicY singleScaleSigma2 dyadicFloor
  positivity

private theorem active_nxClass_scale_pos {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    0 < a.1 := by
  obtain ⟨l, _hl, rfl⟩ := Finset.mem_image.mp ha
  exact scaleN_pos Nm (parentV l.1)

/-- On an active class, `Xi * Xi⁻¹ = 1`. -/
theorem paperDyadicSkipXi_mul_XiInv {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) (skipped : Bool) :
    paperDyadicSkipXi Nm mu a skipped *
        paperDyadicXiInv Nm mu a skipped = 1 := by
  cases skipped with
  | false =>
      simp [paperDyadicSkipXi, paperDyadicXiInv]
  | true =>
      have hX : 0 < (a.2 : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one
          (one_le_nxClass_X Nm mu ha)
      have hY : 0 < paperDyadicY Nm mu a :=
        active_paperDyadicY_pos Nm mu ha
      have hsqrt :
          Real.sqrt ((a.2 : ℝ) * paperDyadicY Nm mu a) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (mul_pos hX hY))
      unfold paperDyadicSkipXi paperDyadicXiInv
      simp only [if_true]
      exact inv_mul_cancel₀ hsqrt

/-- Exact comparison of a one-variable rough target with the common local
factor of (5.87).  No `Y` or `Xi` loss is hidden in a constant. -/
theorem paperDyadicSingleRoughTarget_eq_common_mul_losses
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (hR : 0 < R) {a : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (skipped : Bool) :
    paperDyadicSingleRoughTarget Nm mu R a skipped =
      paperDyadicLocalTarget Nm mu a skipped *
        Real.sqrt (paperDyadicY Nm mu a) *
        paperDyadicXiInv Nm mu a skipped *
        paperDyadicRoughScaleGain R a skipped := by
  have hN : (a.1 : ℝ) ≠ 0 := by
    exact_mod_cast (active_nxClass_scale_pos Nm mu ha).ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hY : 0 ≤ paperDyadicY Nm mu a :=
    (active_paperDyadicY_pos Nm mu ha).le
  have hsqrtY :
      Real.sqrt (paperDyadicY Nm mu a) *
          Real.sqrt (paperDyadicY Nm mu a) =
        paperDyadicY Nm mu a :=
    Real.mul_self_sqrt hY
  cases skipped with
  | false =>
      simp only [paperDyadicSingleRoughTarget, Bool.false_eq_true,
        if_false, paperDyadicLocalTarget, paperDyadicSkipXi,
        paperDyadicXiInv, paperDyadicRoughScaleGain, mul_one]
      unfold paperDyadicBase
      symm
      calc
        (a.2 : ℝ) * Real.sqrt (paperDyadicY Nm mu a) *
              (a.1 : ℝ)⁻¹ ^ 2 *
            Real.sqrt (paperDyadicY Nm mu a) =
            (a.2 : ℝ) *
              (Real.sqrt (paperDyadicY Nm mu a) *
                Real.sqrt (paperDyadicY Nm mu a)) *
              (a.1 : ℝ)⁻¹ ^ 2 := by ring
        _ = (a.2 : ℝ) * paperDyadicY Nm mu a *
              (a.1 : ℝ)⁻¹ ^ 2 := by rw [hsqrtY]
  | true =>
      have hXi :=
        paperDyadicSkipXi_mul_XiInv Nm mu ha true
      simp only [paperDyadicSingleRoughTarget, if_true,
        paperDyadicLocalTarget, paperDyadicRoughScaleGain]
      symm
      calc
        paperDyadicBase Nm mu a *
              paperDyadicSkipXi Nm mu a true *
            Real.sqrt (paperDyadicY Nm mu a) *
          paperDyadicXiInv Nm mu a true *
            ((a.1 : ℝ) / R) ^ 2 =
            paperDyadicBase Nm mu a *
              Real.sqrt (paperDyadicY Nm mu a) *
              (paperDyadicSkipXi Nm mu a true *
                paperDyadicXiInv Nm mu a true) *
              ((a.1 : ℝ) / R) ^ 2 := by ring
        _ = paperDyadicBase Nm mu a *
              Real.sqrt (paperDyadicY Nm mu a) *
              ((a.1 : ℝ) / R) ^ 2 := by rw [hXi, mul_one]
        _ = (a.2 : ℝ) *
              (Real.sqrt (paperDyadicY Nm mu a) *
                Real.sqrt (paperDyadicY Nm mu a)) *
              (a.1 : ℝ)⁻¹ ^ 2 *
              ((a.1 : ℝ) / R) ^ 2 := by
            unfold paperDyadicBase
            ring
        _ = (a.2 : ℝ) * paperDyadicY Nm mu a *
              (a.1 : ℝ)⁻¹ ^ 2 *
              ((a.1 : ℝ) / R) ^ 2 := by rw [hsqrtY]
        _ = (a.2 : ℝ) * paperDyadicY Nm mu a * R⁻¹ ^ 2 := by
            field_simp [hN, hR0]

/-- Exact rough-pair conversion.  It exposes four possible scalar loss atoms
(`sqrt Y` and `Xi⁻¹` for each endpoint) and the two scale gains. -/
theorem paperDyadicPairRoughTarget_eq_common_mul_losses
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (R : ℝ) (hR : 0 < R) {a b : NXClass}
    (ha : a ∈ nxCarrier Nm mu) (hb : b ∈ nxCarrier Nm mu)
    (skipA skipB : Bool) :
    paperDyadicPairRoughTarget Nm mu R a b skipA skipB =
      (paperDyadicLocalTarget Nm mu a skipA *
          paperDyadicLocalTarget Nm mu b skipB) *
        (Real.sqrt (paperDyadicY Nm mu a) *
          paperDyadicXiInv Nm mu a skipA) *
        (Real.sqrt (paperDyadicY Nm mu b) *
          paperDyadicXiInv Nm mu b skipB) *
        (paperDyadicRoughScaleGain R a skipA *
          paperDyadicRoughScaleGain R b skipB) := by
  rw [paperDyadicPairRoughTarget,
    paperDyadicSingleRoughTarget_eq_common_mul_losses
      Nm mu R hR ha skipA,
    paperDyadicSingleRoughTarget_eq_common_mul_losses
      Nm mu R hR hb skipB]
  ring

/-! ## Every scalar loss is at most the total multiplicity -/

private theorem multiplicityNX_le_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    multiplicityNX Nm mu a ≤ totalMultiplicity mu := by
  rw [← sum_multiplicityNX Nm mu]
  exact Finset.single_le_sum
    (fun q _hq => Nat.zero_le (multiplicityNX Nm mu q)) ha

private theorem active_X_mul_Y_le_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    a.2 * (singleScaleSigma2 Nm mu a).2 ≤ totalMultiplicity mu :=
  (multiplicityNX_bounds Nm mu ha).1.trans
    (multiplicityNX_le_totalMultiplicity Nm mu ha)

theorem paperDyadicY_le_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    paperDyadicY Nm mu a ≤ totalMultiplicity mu := by
  have hX := one_le_nxClass_X Nm mu ha
  have hXY := active_X_mul_Y_le_totalMultiplicity Nm mu ha
  unfold paperDyadicY
  have hnat : (singleScaleSigma2 Nm mu a).2 ≤
      totalMultiplicity mu := by
    calc
      (singleScaleSigma2 Nm mu a).2 =
        1 * (singleScaleSigma2 Nm mu a).2 := by simp
      _ ≤ a.2 * (singleScaleSigma2 Nm mu a).2 :=
        Nat.mul_le_mul_right _ hX
      _ ≤ totalMultiplicity mu := hXY
  exact_mod_cast hnat

theorem paperDyadicXY_le_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    a.2 * (singleScaleSigma2 Nm mu a).2 ≤ totalMultiplicity mu :=
  active_X_mul_Y_le_totalMultiplicity Nm mu ha

theorem paperDyadicSqrtY_le_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) :
    Real.sqrt (paperDyadicY Nm mu a) ≤ totalMultiplicity mu := by
  have hY1 : 1 ≤ paperDyadicY Nm mu a := by
    unfold paperDyadicY singleScaleSigma2 dyadicFloor
    exact_mod_cast Nat.one_le_pow
      (Nat.log 2 (leavesAtNX Nm mu a).card) 2 (by norm_num)
  calc
    Real.sqrt (paperDyadicY Nm mu a) ≤
        paperDyadicY Nm mu a :=
      Real.sqrt_le_self_iff.mpr (Or.inr hY1)
    _ ≤ totalMultiplicity mu := by
      exact_mod_cast paperDyadicY_le_totalMultiplicity Nm mu ha

theorem paperDyadicXiInv_le_totalMultiplicity {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    {a : NXClass} (ha : a ∈ nxCarrier Nm mu) (skipped : Bool) :
    paperDyadicXiInv Nm mu a skipped ≤ totalMultiplicity mu := by
  have hm1 : 1 ≤ totalMultiplicity mu := by
    have hxy := active_X_mul_Y_le_totalMultiplicity Nm mu ha
    have hx := one_le_nxClass_X Nm mu ha
    have hy : 1 ≤ (singleScaleSigma2 Nm mu a).2 := by
      unfold singleScaleSigma2 dyadicFloor
      exact Nat.one_le_pow _ _ (by norm_num)
    have honeXY :
        1 ≤ a.2 * (singleScaleSigma2 Nm mu a).2 := by
      have := Nat.mul_le_mul hx hy
      simpa using this
    exact honeXY.trans hxy
  cases skipped with
  | false =>
      simp [paperDyadicXiInv]
      exact_mod_cast hm1
  | true =>
      have hXY1 :
          (1 : ℝ) ≤
            (a.2 : ℝ) * paperDyadicY Nm mu a := by
        have hx := one_le_nxClass_X Nm mu ha
        have hy : 1 ≤ (singleScaleSigma2 Nm mu a).2 := by
          unfold singleScaleSigma2 dyadicFloor
          exact Nat.one_le_pow _ _ (by norm_num)
        unfold paperDyadicY
        exact_mod_cast (by
          have := Nat.mul_le_mul hx hy
          simpa using this)
      have hsqrt :
          Real.sqrt ((a.2 : ℝ) * paperDyadicY Nm mu a) ≤
            (a.2 : ℝ) * paperDyadicY Nm mu a :=
        Real.sqrt_le_self_iff.mpr (Or.inr hXY1)
      have hXY :
          (a.2 : ℝ) * paperDyadicY Nm mu a ≤
            totalMultiplicity mu := by
        unfold paperDyadicY
        exact_mod_cast active_X_mul_Y_le_totalMultiplicity Nm mu ha
      simpa [paperDyadicXiInv] using hsqrt.trans hXY

/-! ## The explicit `m^20 <= C^m` absorption -/

/-- The concrete universal base used to absorb the twenty polynomial
losses. -/
def positionLossBase : ℕ := 2 ^ 20

theorem pow_twenty_le_positionLossBase_pow (m : ℕ) :
    m ^ 20 ≤ positionLossBase ^ m := by
  have hm : m ≤ 2 ^ m := Nat.lt_two_pow_self.le
  calc
    m ^ 20 ≤ (2 ^ m) ^ 20 := Nat.pow_le_pow_left hm 20
    _ = (2 ^ 20) ^ m := by
      simp only [← pow_mul]
      congr 1
      omega
    _ = positionLossBase ^ m := rfl

/-- A product of at most twenty nonnegative atoms, each at most `m`, is
absorbed by the same universal exponential. -/
theorem prod_lossAtoms_le_positionLossBase_pow
    {ι : Type*} (s : Finset ι) (loss : ι → ℝ) (m : ℕ)
    (hcard : s.card ≤ 20)
    (hnonneg : ∀ i ∈ s, 0 ≤ loss i)
    (hle : ∀ i ∈ s, loss i ≤ m) :
    (∏ i ∈ s, loss i) ≤ (positionLossBase : ℝ) ^ m := by
  by_cases hm : m = 0
  · subst m
    by_cases hs : s = ∅
    · subst s
      simp
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have hzero : loss i = 0 := by
        have hlo := hnonneg i hi
        have hup := hle i hi
        norm_num at hup
        linarith
      rw [Finset.prod_eq_zero hi hzero]
      positivity
  calc
    (∏ i ∈ s, loss i) ≤ ∏ _i ∈ s, (m : ℝ) :=
      Finset.prod_le_prod hnonneg hle
    _ = (m : ℝ) ^ s.card := by simp
    _ ≤ (m : ℝ) ^ 20 := by
      exact pow_le_pow_right₀ (by exact_mod_cast Nat.pos_of_ne_zero hm)
        hcard
    _ ≤ (positionLossBase : ℝ) ^ m := by
      exact_mod_cast pow_twenty_le_positionLossBase_pow m

/-! ## Pairing the two runs cut at the distinguished position -/

/-- A purely positional single or consecutive-pair block. -/
inductive PositionBlock (α : Type*)
  | single (x : α)
  | pair (x y : α)
deriving DecidableEq

/-- Pair consecutive entries of a run.  In the shifted phase the first
entry is left single before ordinary pairing starts. -/
def pairPositionRun {α : Type*} : Bool → List α → List (PositionBlock α)
  | false, [] => []
  | false, [x] => [.single x]
  | false, x :: y :: xs => .pair x y :: pairPositionRun false xs
  | true, [] => []
  | true, x :: xs => .single x :: pairPositionRun false xs

/-- Positions contained in a block, in traversal order. -/
def PositionBlock.entries {α : Type*} : PositionBlock α → List α
  | .single x => [x]
  | .pair x y => [x, y]

def PositionBlock.map {α β : Type*} (f : α → β) :
    PositionBlock α → PositionBlock β
  | .single x => .single (f x)
  | .pair x y => .pair (f x) (f y)

@[simp] theorem pairPositionRun_map {α β : Type*}
    (phase : Bool) (f : α → β) (xs : List α) :
    (pairPositionRun phase xs).map (PositionBlock.map f) =
      pairPositionRun phase (xs.map f) := by
  cases phase with
  | false =>
      induction xs using List.twoStepInduction with
      | nil => rfl
      | singleton x => rfl
      | cons_cons x y xs ih =>
          simp [pairPositionRun, PositionBlock.map, ih]
  | true =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          simp [pairPositionRun, PositionBlock.map,
            pairPositionRun_map false f xs]

@[simp] theorem flatten_pairPositionRun {α : Type*}
    (phase : Bool) (xs : List α) :
    (pairPositionRun phase xs).flatMap PositionBlock.entries = xs := by
  cases phase with
  | false =>
      induction xs using List.twoStepInduction with
      | nil => rfl
      | singleton x => rfl
      | cons_cons x y xs ih =>
          simp [pairPositionRun, PositionBlock.entries, ih]
  | true =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          simp [pairPositionRun, PositionBlock.entries,
            flatten_pairPositionRun false xs]

/-- Both endpoints of a pair block really occur in the run it was built
from.  This small interface avoids reopening the recursive pairing
definition in later geometric arguments. -/
theorem pairPositionRun_pair_endpoints_mem {α : Type*}
    (phase : Bool) (xs : List α) (x y : α)
    (h : PositionBlock.pair x y ∈ pairPositionRun phase xs) :
    x ∈ xs ∧ y ∈ xs := by
  constructor
  · rw [← flatten_pairPositionRun phase xs, List.mem_flatMap]
    exact ⟨.pair x y, h, by simp [PositionBlock.entries]⟩
  · rw [← flatten_pairPositionRun phase xs, List.mem_flatMap]
    exact ⟨.pair x y, h, by simp [PositionBlock.entries]⟩

/-- Pairs in an arithmetic run join successive values and have the parity
dictated by the unshifted phase. -/
private theorem pair_mem_pairPositionRun_false_range'
    (start len x y : ℕ)
    (h : PositionBlock.pair x y ∈
      pairPositionRun false (List.range' start len)) :
    y = x + 1 ∧ x % 2 = start % 2 := by
  induction len using Nat.twoStepInduction generalizing start x y with
  | zero =>
      simp [pairPositionRun] at h
  | one =>
      simp [List.range'_succ, pairPositionRun] at h
  | more n ih0 _ih1 =>
      have hrange :
          List.range' start (n + 2) =
            start :: (start + 1) :: List.range' (start + 2) n := by
        rw [show n + 2 = (n + 1) + 1 by omega,
          List.range'_succ, List.range'_succ]
      rw [hrange] at h
      simp only [pairPositionRun, List.mem_cons] at h
      rcases h with hhead | htail
      · cases hhead
        constructor <;> omega
      · have ht := ih0 (start + 2) x y htail
        constructor
        · exact ht.1
        · omega

private theorem pair_mem_pairPositionRun_range'
    (phase : Bool) (start len x y : ℕ)
    (h : PositionBlock.pair x y ∈
      pairPositionRun phase (List.range' start len)) :
    y = x + 1 ∧
      x % 2 = (start + if phase then 1 else 0) % 2 := by
  cases phase with
  | false =>
      simpa using
        pair_mem_pairPositionRun_false_range' start len x y h
  | true =>
      cases len with
      | zero =>
          simp [pairPositionRun] at h
      | succ len =>
          rw [List.range'_succ] at h
          simp only [pairPositionRun, List.mem_cons] at h
          rcases h with hbad | htail
          · cases hbad
          have ht :=
            pair_mem_pairPositionRun_false_range'
              (start + 1) len x y htail
          simpa only [if_true] using ht

/-- Converse to `pair_mem_pairPositionRun_false_range'`: every adjacent
pair with the required parity and lying in the arithmetic run is selected
by the unshifted pairing schedule. -/
private theorem pair_mem_pairPositionRun_false_range'_of_bounds
    (start len x : ℕ)
    (hx : start ≤ x) (hy : x + 1 < start + len)
    (hparity : x % 2 = start % 2) :
    PositionBlock.pair x (x + 1) ∈
      pairPositionRun false (List.range' start len) := by
  induction len using Nat.twoStepInduction generalizing start x with
  | zero => omega
  | one => omega
  | more n ih0 _ih1 =>
      have hrange :
          List.range' start (n + 2) =
            start :: (start + 1) :: List.range' (start + 2) n := by
        rw [show n + 2 = (n + 1) + 1 by omega,
          List.range'_succ, List.range'_succ]
      rw [hrange]
      simp only [pairPositionRun, List.mem_cons]
      by_cases hxs : x = start
      · left
        subst x
        rfl
      · right
        apply ih0 (start + 2) x
        · omega
        · omega
        · omega

/-- Every adjacent pair with the phase-selected parity and lying in an
arithmetic run occurs in that phase's pairing schedule. -/
private theorem pair_mem_pairPositionRun_range'_of_bounds
    (phase : Bool) (start len x : ℕ)
    (hx : start ≤ x) (hy : x + 1 < start + len)
    (hparity :
      x % 2 = (start + if phase then 1 else 0) % 2) :
    PositionBlock.pair x (x + 1) ∈
      pairPositionRun phase (List.range' start len) := by
  cases phase with
  | false =>
      exact pair_mem_pairPositionRun_false_range'_of_bounds
        start len x hx hy (by simpa using hparity)
  | true =>
      cases len with
      | zero => omega
      | succ len =>
          have hparity' : x % 2 = (start + 1) % 2 := by
            simpa only [if_true] using hparity
          rw [List.range'_succ]
          simp only [pairPositionRun, List.mem_cons]
          right
          apply pair_mem_pairPositionRun_false_range'_of_bounds
            (start + 1) len x
          · omega
          · omega
          · exact hparity'

/-- Number of one-variable estimates in a schedule. -/
def positionSingleCount {α : Type*}
    (bs : List (PositionBlock α)) : ℕ :=
  (bs.filter fun b => match b with
    | .single _ => true
    | .pair _ _ => false).length

@[simp] theorem positionSingleCount_single_cons {α : Type*}
    (x : α) (bs : List (PositionBlock α)) :
    positionSingleCount (.single x :: bs) =
      positionSingleCount bs + 1 := by
  simp [positionSingleCount]

@[simp] theorem positionSingleCount_pair_cons {α : Type*}
    (x y : α) (bs : List (PositionBlock α)) :
    positionSingleCount (.pair x y :: bs) =
      positionSingleCount bs := by
  simp [positionSingleCount]

theorem positionSingleCount_pairPositionRun_le_two
    {α : Type*} (phase : Bool) (xs : List α) :
    positionSingleCount (pairPositionRun phase xs) ≤ 2 := by
  let rec falseLeOne (ys : List α) :
      positionSingleCount (pairPositionRun false ys) ≤ 1 := by
    match ys with
    | [] => simp [positionSingleCount, pairPositionRun]
    | [x] => simp [positionSingleCount, pairPositionRun]
    | x :: y :: zs =>
        simpa [positionSingleCount, pairPositionRun] using
          falseLeOne zs
  cases phase with
  | false =>
      exact (falseLeOne xs).trans (by omega)
  | true =>
      cases xs with
      | nil => simp [positionSingleCount, pairPositionRun]
      | cons x xs =>
          have h := falseLeOne xs
          simpa [positionSingleCount, pairPositionRun] using h

theorem positionSingleCount_append {α : Type*}
    (xs ys : List (PositionBlock α)) :
    positionSingleCount (xs ++ ys) =
      positionSingleCount xs + positionSingleCount ys := by
  simp [positionSingleCount, List.filter_append]

/-- Pair both sides of a cut.  The lists are ordered away from the anchor;
the left list is therefore the mirrored traversal. -/
def anchorPositionSchedule {α : Type*}
    (phase : Bool) (left right : List α) : List (PositionBlock α) :=
  pairPositionRun phase left ++ pairPositionRun phase right

/-- Independent phases are required after reversing the left run. -/
def anchorPositionScheduleWithPhases {α : Type*}
    (leftPhase rightPhase : Bool) (left right : List α) :
    List (PositionBlock α) :=
  pairPositionRun leftPhase left ++ pairPositionRun rightPhase right

/-- The promised at-most-four one-variable blocks. -/
theorem anchorPositionSchedule_singleCount_le_four
    {α : Type*} (phase : Bool) (left right : List α) :
    positionSingleCount (anchorPositionSchedule phase left right) ≤ 4 := by
  rw [anchorPositionSchedule, positionSingleCount_append]
  have hl := positionSingleCount_pairPositionRun_le_two phase left
  have hr := positionSingleCount_pairPositionRun_le_two phase right
  omega

theorem anchorPositionScheduleWithPhases_singleCount_le_four
    {α : Type*} (leftPhase rightPhase : Bool)
    (left right : List α) :
    positionSingleCount
        (anchorPositionScheduleWithPhases
          leftPhase rightPhase left right) ≤ 4 := by
  rw [anchorPositionScheduleWithPhases, positionSingleCount_append]
  have hl := positionSingleCount_pairPositionRun_le_two leftPhase left
  have hr := positionSingleCount_pairPositionRun_le_two rightPhase right
  omega

@[simp] theorem flatten_anchorPositionSchedule {α : Type*}
    (phase : Bool) (left right : List α) :
    (anchorPositionSchedule phase left right).flatMap
        PositionBlock.entries =
      left ++ right := by
  simp [anchorPositionSchedule, flatten_pairPositionRun]

@[simp] theorem flatten_anchorPositionScheduleWithPhases {α : Type*}
    (leftPhase rightPhase : Bool) (left right : List α) :
    (anchorPositionScheduleWithPhases
      leftPhase rightPhase left right).flatMap PositionBlock.entries =
        left ++ right := by
  simp [anchorPositionScheduleWithPhases, flatten_pairPositionRun]

/-- A schedule whose blocks remember the active `(N,X)` class at every
position. -/
def positionBlockToNXParityBlock {α : Type*} {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : α → ActiveNXClass Nm mu) (incomingSkipped : α → Bool) :
    PositionBlock α → NXParityBlock Nm mu
  | .single x => .single (cls x) (incomingSkipped x)
  | .pair x y =>
      .pair
        { left := cls x
          right := cls y
          skipLeft := incomingSkipped x
          skipRight := incomingSkipped y }

/-- Number of one-variable blocks after classes have been attached. -/
def nxParitySingleCount {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (NXParityBlock Nm mu)) : ℕ :=
  (bs.filter fun b => match b with
    | .single _ _ => true
    | .pair _ => false
    | .roughPair _ => false).length

/-- Number of pair blocks deliberately assigned the rough estimate (5.90). -/
def nxParityRoughPairCount {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (NXParityBlock Nm mu)) : ℕ :=
  (bs.filter fun b => match b with
    | .roughPair _ => true
    | .single _ _ => false
    | .pair _ => false).length

@[simp] theorem nxParitySingleCount_single_cons {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (a : ActiveNXClass Nm mu) (skipped : Bool)
    (bs : List (NXParityBlock Nm mu)) :
    nxParitySingleCount (.single a skipped :: bs) =
      nxParitySingleCount bs + 1 := by
  simp [nxParitySingleCount]

@[simp] theorem nxParitySingleCount_pair_cons {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (p : NXPairBlock Nm mu) (bs : List (NXParityBlock Nm mu)) :
    nxParitySingleCount (.pair p :: bs) =
      nxParitySingleCount bs := by
  simp [nxParitySingleCount]

@[simp] theorem nxParitySingleCount_roughPair_cons {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (p : NXPairBlock Nm mu) (bs : List (NXParityBlock Nm mu)) :
    nxParitySingleCount (.roughPair p :: bs) =
      nxParitySingleCount bs := by
  simp [nxParitySingleCount]

@[simp] theorem nxParityRoughPairCount_single_cons {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (a : ActiveNXClass Nm mu) (skipped : Bool)
    (bs : List (NXParityBlock Nm mu)) :
    nxParityRoughPairCount (.single a skipped :: bs) =
      nxParityRoughPairCount bs := by
  simp [nxParityRoughPairCount]

@[simp] theorem nxParityRoughPairCount_pair_cons {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (p : NXPairBlock Nm mu) (bs : List (NXParityBlock Nm mu)) :
    nxParityRoughPairCount (.pair p :: bs) =
      nxParityRoughPairCount bs := by
  simp [nxParityRoughPairCount]

@[simp] theorem nxParityRoughPairCount_roughPair_cons {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (p : NXPairBlock Nm mu) (bs : List (NXParityBlock Nm mu)) :
    nxParityRoughPairCount (.roughPair p :: bs) =
      nxParityRoughPairCount bs + 1 := by
  simp [nxParityRoughPairCount]

theorem nxParitySingleCount_append {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (xs ys : List (NXParityBlock Nm mu)) :
    nxParitySingleCount (xs ++ ys) =
      nxParitySingleCount xs + nxParitySingleCount ys := by
  simp [nxParitySingleCount, List.filter_append]

theorem nxParityRoughPairCount_append {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (xs ys : List (NXParityBlock Nm mu)) :
    nxParityRoughPairCount (xs ++ ys) =
      nxParityRoughPairCount xs + nxParityRoughPairCount ys := by
  simp [nxParityRoughPairCount, List.filter_append]

theorem nxParitySingleCount_map_positionBlockToNXParityBlock
    {α : Type*} {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : α → ActiveNXClass Nm mu) (incomingSkipped : α → Bool)
    (bs : List (PositionBlock α)) :
    nxParitySingleCount
        (bs.map (positionBlockToNXParityBlock Nm mu cls incomingSkipped)) =
      positionSingleCount bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | single x =>
          simpa only [List.map_cons, positionBlockToNXParityBlock,
            nxParitySingleCount_single_cons,
            positionSingleCount_single_cons] using
            congrArg (fun n => n + 1) ih
      | pair x y =>
          simpa only [List.map_cons, positionBlockToNXParityBlock,
            nxParitySingleCount_pair_cons,
            positionSingleCount_pair_cons] using ih

theorem nxParityRoughPairCount_map_positionBlockToNXParityBlock
    {α : Type*} {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : α → ActiveNXClass Nm mu) (incomingSkipped : α → Bool)
    (bs : List (PositionBlock α)) :
    nxParityRoughPairCount
        (bs.map (positionBlockToNXParityBlock Nm mu cls incomingSkipped)) =
      0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | single x =>
          simpa only [List.map_cons, positionBlockToNXParityBlock,
            nxParityRoughPairCount_single_cons] using ih
      | pair x y =>
          simpa only [List.map_cons, positionBlockToNXParityBlock,
            nxParityRoughPairCount_pair_cons] using ih

/-- Whether a refined pair touches a skipped edge and is therefore eligible
for one of the paper's at-most-three rough estimates. -/
def nxPairBlockTouchesSkip {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (p : NXPairBlock Nm mu) : Bool :=
  p.skipLeft || p.skipRight

/-- Mark the first `fuel` eligible refined pairs as rough.  This is the
literal "choose three (or all if fewer)" operation following (5.92). -/
def markFirstSkippedPairsRough {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    ℕ → List (NXParityBlock Nm mu) → List (NXParityBlock Nm mu)
  | _, [] => []
  | 0, bs => bs
  | fuel + 1, b :: bs =>
      match b with
      | .pair p =>
          if nxPairBlockTouchesSkip p then
            .roughPair p :: markFirstSkippedPairsRough fuel bs
          else
            .pair p :: markFirstSkippedPairsRough (fuel + 1) bs
      | .single a skipped =>
          .single a skipped :: markFirstSkippedPairsRough (fuel + 1) bs
      | .roughPair p =>
          .roughPair p :: markFirstSkippedPairsRough (fuel + 1) bs

@[simp] theorem length_markFirstSkippedPairsRough {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (bs : List (NXParityBlock Nm mu)) :
    (markFirstSkippedPairsRough fuel bs).length = bs.length := by
  induction bs generalizing fuel with
  | nil => simp [markFirstSkippedPairsRough]
  | cons b bs ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases b with
          | single a skipped =>
              simp [markFirstSkippedPairsRough, ih]
          | pair p =>
              by_cases h : nxPairBlockTouchesSkip p
              · simp [markFirstSkippedPairsRough, h, ih]
              · simp [markFirstSkippedPairsRough, h, ih]
          | roughPair p =>
              simp [markFirstSkippedPairsRough, ih]

theorem nxParitySingleCount_markFirstSkippedPairsRough {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (bs : List (NXParityBlock Nm mu)) :
    nxParitySingleCount (markFirstSkippedPairsRough fuel bs) =
      nxParitySingleCount bs := by
  induction bs generalizing fuel with
  | nil => simp [markFirstSkippedPairsRough, nxParitySingleCount]
  | cons b bs ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases b with
          | single a skipped =>
              simpa only [markFirstSkippedPairsRough,
                nxParitySingleCount_single_cons] using
                congrArg (fun n => n + 1) (ih (fuel + 1))
          | pair p =>
              by_cases h : nxPairBlockTouchesSkip p
              · simpa only [markFirstSkippedPairsRough, h, if_true,
                  nxParitySingleCount_roughPair_cons,
                  nxParitySingleCount_pair_cons] using ih fuel
              · have hb : nxPairBlockTouchesSkip p = false :=
                  Bool.eq_false_of_not_eq_true h
                simpa [markFirstSkippedPairsRough, hb] using ih (fuel + 1)
          | roughPair p =>
              simpa only [markFirstSkippedPairsRough,
                nxParitySingleCount_roughPair_cons] using ih (fuel + 1)

/-- Rough marking creates at most `fuel` new rough pairs. -/
theorem nxParityRoughPairCount_markFirstSkippedPairsRough_le {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (bs : List (NXParityBlock Nm mu)) :
    nxParityRoughPairCount (markFirstSkippedPairsRough fuel bs) ≤
      nxParityRoughPairCount bs + fuel := by
  induction bs generalizing fuel with
  | nil => simp [markFirstSkippedPairsRough, nxParityRoughPairCount]
  | cons b bs ih =>
      cases fuel with
      | zero =>
          simp [markFirstSkippedPairsRough]
      | succ fuel =>
          cases b with
          | single a skipped =>
              simpa only [markFirstSkippedPairsRough,
                nxParityRoughPairCount_single_cons] using ih (fuel + 1)
          | pair p =>
              by_cases h : nxPairBlockTouchesSkip p
              · have htail := ih fuel
                simpa only [markFirstSkippedPairsRough, h, if_true,
                  nxParityRoughPairCount_roughPair_cons,
                  nxParityRoughPairCount_pair_cons, Nat.add_assoc,
                  Nat.add_comm, Nat.add_left_comm] using
                  Nat.add_le_add_right htail 1
              · have hb : nxPairBlockTouchesSkip p = false :=
                  Bool.eq_false_of_not_eq_true h
                simpa [markFirstSkippedPairsRough, hb] using ih (fuel + 1)
          | roughPair p =>
              simpa only [markFirstSkippedPairsRough,
                nxParityRoughPairCount_roughPair_cons, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using
                Nat.add_le_add_right (ih (fuel + 1)) 1

/-- The scalar-loss ledger has two atoms for each single block and four for
each rough pair. -/
def positionLossAtomBudget (singleBlocks roughPairs : ℕ) : ℕ :=
  2 * singleBlocks + 4 * roughPairs

theorem positionLossAtomBudget_le_twenty
    {singleBlocks roughPairs : ℕ}
    (hsingle : singleBlocks ≤ 4) (hrough : roughPairs ≤ 3) :
    positionLossAtomBudget singleBlocks roughPairs ≤ 20 := by
  unfold positionLossAtomBudget
  omega

/-! ### The concrete cut of `Fin m` at an anchor -/

/-- Positions strictly to the left of the anchor, ordered away from the
anchor.  Thus this list is decreasing in the original word order. -/
def leftAnchorPositions {m : ℕ} (anchor : Fin m) : List (Fin m) :=
  (List.finRange anchor.1).reverse.map fun i =>
    ⟨i.1, lt_trans i.2 anchor.2⟩

/-- Positions strictly to the right of the anchor, ordered away from the
anchor (increasing in the original word order). -/
def rightAnchorPositions {m : ℕ} (anchor : Fin m) : List (Fin m) :=
  (List.finRange (m - (anchor.1 + 1))).map fun i =>
    ⟨anchor.1 + 1 + i.1, by omega⟩

/-- Zero-based position inside the outward run on the position's side. -/
def anchorPositionOutwardOffset {m : ℕ}
    (anchor i : Fin m) : ℕ :=
  if i.1 < anchor.1 then
    anchor.1 - 1 - i.1
  else
    i.1 - (anchor.1 + 1)

@[simp] theorem length_leftAnchorPositions {m : ℕ} (anchor : Fin m) :
    (leftAnchorPositions anchor).length = anchor.1 := by
  simp [leftAnchorPositions]

@[simp] theorem length_rightAnchorPositions {m : ℕ} (anchor : Fin m) :
    (rightAnchorPositions anchor).length = m - (anchor.1 + 1) := by
  simp [rightAnchorPositions]

theorem leftAnchorPositions_nodup {m : ℕ} (anchor : Fin m) :
    (leftAnchorPositions anchor).Nodup := by
  unfold leftAnchorPositions
  apply List.Nodup.map
  · intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.1) hij
  · exact List.nodup_reverse.mpr (List.nodup_finRange anchor.1)

theorem rightAnchorPositions_nodup {m : ℕ} (anchor : Fin m) :
    (rightAnchorPositions anchor).Nodup := by
  unfold rightAnchorPositions
  apply List.Nodup.map
  · intro i j hij
    apply Fin.ext
    have hval :
        anchor.1 + 1 + i.1 = anchor.1 + 1 + j.1 :=
      congrArg (fun x : Fin m => x.1) hij
    omega
  · exact List.nodup_finRange _

theorem map_anchorPositionOutwardOffset_left {m : ℕ}
    (anchor : Fin m) :
    (leftAnchorPositions anchor).map
        (anchorPositionOutwardOffset anchor) =
      List.range anchor.1 := by
  let complement := fun x : ℕ => anchor.1 - 1 - x
  have hfirst :
      (leftAnchorPositions anchor).map
          (anchorPositionOutwardOffset anchor) =
        (List.finRange anchor.1).reverse.map
          (fun i => complement i.1) := by
    unfold leftAnchorPositions
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply, anchorPositionOutwardOffset,
      complement]
    rw [if_pos]
    exact i.2
  have hvalues :
      (List.finRange anchor.1).reverse.map (fun i => i.1) =
        (List.range anchor.1).reverse := by
    simp only [List.map_reverse, List.map_coe_finRange_eq_range]
  have hreverse :
      (List.range anchor.1).reverse =
        (List.range anchor.1).map complement := by
    calc
      (List.range anchor.1).reverse =
          (List.range' 0 anchor.1).reverse := by
            rw [List.range_eq_range']
      _ = (List.range anchor.1).map
          (fun x => 0 + anchor.1 - 1 - x) :=
        List.reverse_range'
      _ = (List.range anchor.1).map complement := by
        apply List.map_congr_left
        intro x hx
        simp only [complement]
        omega
  rw [hfirst]
  calc
    (List.finRange anchor.1).reverse.map
        (fun i => complement i.1) =
      ((List.finRange anchor.1).reverse.map
        (fun i => i.1)).map complement := by
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          rfl
    _ = (List.range anchor.1).reverse.map complement := by
      rw [hvalues]
    _ = ((List.range anchor.1).map complement).map complement := by
      rw [hreverse]
    _ = List.range anchor.1 := by
      rw [List.map_map]
      calc
        (List.range anchor.1).map (complement ∘ complement) =
            (List.range anchor.1).map id := by
          apply List.map_congr_left
          intro x hx
          have hxlt : x < anchor.1 := List.mem_range.mp hx
          simp only [Function.comp_apply, complement, id_eq]
          omega
        _ = List.range anchor.1 := List.map_id _

theorem map_anchorPositionOutwardOffset_right {m : ℕ}
    (anchor : Fin m) :
    (rightAnchorPositions anchor).map
        (anchorPositionOutwardOffset anchor) =
      List.range (m - (anchor.1 + 1)) := by
  unfold rightAnchorPositions
  rw [List.map_map]
  calc
    (List.finRange (m - (anchor.1 + 1))).map
        (anchorPositionOutwardOffset anchor ∘
          fun i => (⟨anchor.1 + 1 + i.1, by omega⟩ : Fin m)) =
      (List.finRange (m - (anchor.1 + 1))).map
        (fun i => i.1) := by
          apply List.map_congr_left
          intro i hi
          simp only [Function.comp_apply, anchorPositionOutwardOffset]
          rw [if_neg]
          · omega
          · omega
    _ = List.range (m - (anchor.1 + 1)) :=
      List.map_coe_finRange_eq_range

theorem mem_leftAnchorPositions_iff {m : ℕ}
    (anchor i : Fin m) :
    i ∈ leftAnchorPositions anchor ↔ i.1 < anchor.1 := by
  constructor
  · intro hi
    simp only [leftAnchorPositions, List.mem_map, List.mem_reverse] at hi
    obtain ⟨j, _hj, hji⟩ := hi
    have hval : j.1 = i.1 := congrArg Fin.val hji
    simpa [hval] using j.2
  · intro hi
    let j : Fin anchor.1 := ⟨i.1, hi⟩
    simp only [leftAnchorPositions, List.mem_map, List.mem_reverse]
    refine ⟨j, List.mem_finRange j, ?_⟩
    apply Fin.ext
    rfl

theorem mem_rightAnchorPositions_iff {m : ℕ}
    (anchor i : Fin m) :
    i ∈ rightAnchorPositions anchor ↔ anchor.1 < i.1 := by
  constructor
  · intro hi
    simp only [rightAnchorPositions, List.mem_map] at hi
    obtain ⟨j, _hj, hji⟩ := hi
    have hval : anchor.1 + 1 + j.1 = i.1 :=
      congrArg Fin.val hji
    omega
  · intro hi
    have hdiff : i.1 - (anchor.1 + 1) <
        m - (anchor.1 + 1) := by omega
    let j : Fin (m - (anchor.1 + 1)) :=
      ⟨i.1 - (anchor.1 + 1), hdiff⟩
    simp only [rightAnchorPositions, List.mem_map]
    refine ⟨j, List.mem_finRange j, ?_⟩
    apply Fin.ext
    dsimp [j]
    omega

/-- The two concrete runs contain every position except the anchor, exactly
as a set. -/
theorem mem_left_or_right_anchor_iff {m : ℕ}
    (anchor i : Fin m) :
    i ∈ leftAnchorPositions anchor ∨
        i ∈ rightAnchorPositions anchor ↔
      i ≠ anchor := by
  rw [mem_leftAnchorPositions_iff, mem_rightAnchorPositions_iff]
  constructor
  · intro h hEq
    subst i
    omega
  · intro hne
    have hval : i.1 ≠ anchor.1 := fun h =>
      hne (Fin.ext h)
    omega

theorem leftAnchorPositions_disjoint_right {m : ℕ} (anchor : Fin m) :
    (leftAnchorPositions anchor).Disjoint
      (rightAnchorPositions anchor) := by
  rw [List.disjoint_left]
  intro i hi hright
  have hil := (mem_leftAnchorPositions_iff anchor i).mp hi
  have hir := (mem_rightAnchorPositions_iff anchor i).mp hright
  omega

theorem left_append_rightAnchorPositions_nodup {m : ℕ}
    (anchor : Fin m) :
    (leftAnchorPositions anchor ++ rightAnchorPositions anchor).Nodup :=
  (leftAnchorPositions_nodup anchor).append
    (rightAnchorPositions_nodup anchor)
    (leftAnchorPositions_disjoint_right anchor)

/-- The concrete schedule obtained by cutting `Fin m` at `anchor`. -/
def finAnchorPositionSchedule {m : ℕ}
    (phase : Bool) (anchor : Fin m) : List (PositionBlock (Fin m)) :=
  anchorPositionSchedule phase
    (leftAnchorPositions anchor) (rightAnchorPositions anchor)

/-- Concrete anchor schedule with the independently selectable phases used
on the reversed left and forward right runs. -/
def finAnchorPositionScheduleWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    List (PositionBlock (Fin m)) :=
  anchorPositionScheduleWithPhases leftPhase rightPhase
    (leftAnchorPositions anchor) (rightAnchorPositions anchor)

theorem finAnchorPositionSchedule_singleCount_le_four {m : ℕ}
    (phase : Bool) (anchor : Fin m) :
    positionSingleCount (finAnchorPositionSchedule phase anchor) ≤ 4 :=
  anchorPositionSchedule_singleCount_le_four _ _ _

theorem finAnchorPositionScheduleWithPhases_singleCount_le_four {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    positionSingleCount
        (finAnchorPositionScheduleWithPhases
          leftPhase rightPhase anchor) ≤ 4 :=
  anchorPositionScheduleWithPhases_singleCount_le_four _ _ _ _

/-- Counting entries after the cut gives exactly `m-1`; the anchor is the
single omitted position. -/
theorem length_flatten_finAnchorPositionSchedule {m : ℕ}
    (phase : Bool) (anchor : Fin m) :
    ((finAnchorPositionSchedule phase anchor).flatMap
      PositionBlock.entries).length = m - 1 := by
  rw [finAnchorPositionSchedule, flatten_anchorPositionSchedule,
    List.length_append, length_leftAnchorPositions,
    length_rightAnchorPositions]
  omega

theorem flatten_finAnchorPositionScheduleWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    (finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor).flatMap PositionBlock.entries =
        leftAnchorPositions anchor ++ rightAnchorPositions anchor := by
  simp [finAnchorPositionScheduleWithPhases]

theorem mem_flatten_finAnchorPositionScheduleWithPhases_iff {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor i : Fin m) :
    i ∈ (finAnchorPositionScheduleWithPhases
        leftPhase rightPhase anchor).flatMap PositionBlock.entries ↔
      i ≠ anchor := by
  rw [flatten_finAnchorPositionScheduleWithPhases, List.mem_append,
    mem_left_or_right_anchor_iff]

theorem length_flatten_finAnchorPositionScheduleWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    ((finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor).flatMap
        PositionBlock.entries).length = m - 1 := by
  rw [flatten_finAnchorPositionScheduleWithPhases,
    List.length_append, length_leftAnchorPositions,
    length_rightAnchorPositions]
  omega

theorem nodup_flatten_finAnchorPositionScheduleWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    ((finAnchorPositionScheduleWithPhases
      leftPhase rightPhase anchor).flatMap
        PositionBlock.entries).Nodup := by
  rw [flatten_finAnchorPositionScheduleWithPhases]
  exact left_append_rightAnchorPositions_nodup anchor

/-- Direction of traversal away from the anchor. -/
inductive PositionDirection
  | forward
  | reverse
deriving DecidableEq

/-- Incoming adjacency in the original left-to-right orientation. -/
def forwardIncomingEdge {m : ℕ} (i : Fin m) :
    Option (AdjacentIndex m) :=
  if h : 0 < i.1 then
    some ⟨⟨i.1 - 1, (Nat.sub_le i.1 1).trans_lt i.2⟩, by
      change i.1 - 1 + 1 < m
      omega⟩
  else none

/-- Incoming adjacency when traversing the word from right to left. -/
def reverseIncomingEdge {m : ℕ} (i : Fin m) :
    Option (AdjacentIndex m) :=
  if h : i.1 + 1 < m then
    some ⟨i, h⟩
  else none

/-- Whether the edge entering a position in the chosen traversal direction
belongs to the skipped set `O`. -/
def positionIncomingSkipped {m : ℕ}
    (O : Finset (AdjacentIndex m)) (dir : PositionDirection)
    (i : Fin m) : Bool :=
  match dir with
  | .forward => (forwardIncomingEdge i).any fun j => decide (j ∈ O)
  | .reverse => (reverseIncomingEdge i).any fun j => decide (j ∈ O)

/-! ### Position-preserving exceptional-gain ledger -/

/-- The original chain edges incident to a position.  These are the only
ratio gains whose local argument can use that position. -/
def positionIncidentEdges {m : ℕ} (i : Fin m) :
    Finset (AdjacentIndex m) :=
  (forwardIncomingEdge i).toFinset ∪
    (reverseIncomingEdge i).toFinset

/-- The original ratio-gain edges touched by a one- or two-variable local
operation.  This definition is geometric: an edge is recorded only when one
of its endpoints is actually eliminated by the block. -/
def PositionBlock.affectedEdges {m : ℕ} :
    PositionBlock (Fin m) → Finset (AdjacentIndex m)
  | .single i => positionIncidentEdges i
  | .pair i j => positionIncidentEdges i ∪ positionIncidentEdges j

/-! ### The genuine even/odd carrier in original edge coordinates -/

/--
Distance of an original adjacency edge from the anchor, measured outward
on its own side.  Both boundary edges adjacent to the anchor have distance
zero.
-/
def anchorEdgeOutwardDistance {m : ℕ}
    (anchor : Fin m) (j : AdjacentIndex m) : ℕ :=
  if j.1.1 < anchor.1 then
    anchor.1 - 1 - j.1.1
  else
    j.1.1 - anchor.1

/-- The phase selected on the side containing an original adjacency edge. -/
def anchorEdgeSelectedPhase {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (j : AdjacentIndex m) : Bool :=
  if j.1.1 < anchor.1 then leftPhase else rightPhase

@[simp] theorem anchorEdgeSelectedPhase_flip {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (j : AdjacentIndex m) :
    anchorEdgeSelectedPhase (!leftPhase) (!rightPhase) anchor j =
      !(anchorEdgeSelectedPhase leftPhase rightPhase anchor j) := by
  unfold anchorEdgeSelectedPhase
  split <;> rfl

/--
The original edges matched by one parity schedule.  Shifted phase `true`
selects even outward distances (including the anchor boundary), while
ordinary phase `false` selects odd outward distances.
-/
def finAnchorPositionPhaseCarrierWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    Finset (AdjacentIndex m) :=
  Finset.univ.filter fun j =>
    decide (anchorEdgeOutwardDistance anchor j % 2 = 0) =
      anchorEdgeSelectedPhase leftPhase rightPhase anchor j

@[simp] theorem mem_finAnchorPositionPhaseCarrierWithPhases
    {m : ℕ} (leftPhase rightPhase : Bool) (anchor : Fin m)
    (j : AdjacentIndex m) :
    j ∈ finAnchorPositionPhaseCarrierWithPhases
        leftPhase rightPhase anchor ↔
      decide (anchorEdgeOutwardDistance anchor j % 2 = 0) =
        anchorEdgeSelectedPhase leftPhase rightPhase anchor j := by
  simp [finAnchorPositionPhaseCarrierWithPhases]

/-- Flipping both independently chosen side phases gives the complementary
carrier of original edges. -/
theorem finAnchorPositionPhaseCarrier_union_flip {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    finAnchorPositionPhaseCarrierWithPhases
        leftPhase rightPhase anchor ∪
      finAnchorPositionPhaseCarrierWithPhases
        (!leftPhase) (!rightPhase) anchor =
      Finset.univ := by
  ext j
  simp only [Finset.mem_union,
    mem_finAnchorPositionPhaseCarrierWithPhases,
    anchorEdgeSelectedPhase_flip, Finset.mem_univ, iff_true]
  cases hp : decide
      (anchorEdgeOutwardDistance anchor j % 2 = 0) <;>
    cases hs :
      anchorEdgeSelectedPhase leftPhase rightPhase anchor j <;>
    simp

theorem finAnchorPositionPhaseCarrier_disjoint_flip {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m) :
    Disjoint
      (finAnchorPositionPhaseCarrierWithPhases
        leftPhase rightPhase anchor)
      (finAnchorPositionPhaseCarrierWithPhases
        (!leftPhase) (!rightPhase) anchor) := by
  apply Finset.disjoint_left.mpr
  intro j hj hjFlip
  rw [mem_finAnchorPositionPhaseCarrierWithPhases] at hj hjFlip
  rw [anchorEdgeSelectedPhase_flip] at hjFlip
  cases hp : decide
      (anchorEdgeOutwardDistance anchor j % 2 = 0) <;>
    cases hs :
      anchorEdgeSelectedPhase leftPhase rightPhase anchor j <;>
    simp [hp, hs] at hj hjFlip

/-- On the reversed left run, every selected edge is either the boundary
edge consumed by the shifted singleton or the internal edge of a concrete
pair. -/
private theorem left_phaseCarrier_edge_pair_or_single
    {m : ℕ} (phase : Bool) (anchor : Fin m)
    (edge : AdjacentIndex m) (hleft : edge.1.1 < anchor.1)
    (hphase :
      decide ((anchor.1 - 1 - edge.1.1) % 2 = 0) = phase) :
    (∃ i : Fin m,
        PositionBlock.single i ∈
          pairPositionRun phase (leftAnchorPositions anchor) ∧
        edge ∈ (PositionBlock.single i).affectedEdges) ∨
      ∃ i j : Fin m,
        PositionBlock.pair i j ∈
          pairPositionRun phase (leftAnchorPositions anchor) ∧
        edge.1 = j ∧ j.1 + 1 = i.1 := by
  let d := anchor.1 - 1 - edge.1.1
  have hdlt : d < anchor.1 := by
    dsimp [d]
    omega
  cases phase with
  | false =>
      have hodd : d % 2 ≠ 0 := by
        change decide (d % 2 = 0) = false at hphase
        simpa using hphase
      have hdne : d ≠ 0 := by
        intro hd
        apply hodd
        simp [hd]
      have hparity : (d - 1) % 2 = 0 := by
        omega
      have hoffset :
          PositionBlock.pair (d - 1) d ∈
            pairPositionRun false (List.range anchor.1) := by
        rw [List.range_eq_range']
        have h :=
          pair_mem_pairPositionRun_range'_of_bounds
            false 0 anchor.1 (d - 1) (by omega) (by omega)
              (by simpa using hparity)
        simpa only [Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hdne)] using h
      have hmapped :
          PositionBlock.pair (d - 1) d ∈
            (pairPositionRun false
              (leftAnchorPositions anchor)).map
                (PositionBlock.map
                  (anchorPositionOutwardOffset anchor)) := by
        rw [pairPositionRun_map,
          map_anchorPositionOutwardOffset_left]
        exact hoffset
      obtain ⟨b, hb, hbmap⟩ := List.mem_map.mp hmapped
      cases b with
      | single x =>
          simp [PositionBlock.map] at hbmap
      | pair i j =>
          have hendpoints :=
            pairPositionRun_pair_endpoints_mem
              false (leftAnchorPositions anchor) i j hb
          have hi : i.1 < anchor.1 :=
            (mem_leftAnchorPositions_iff anchor i).mp hendpoints.1
          have hj : j.1 < anchor.1 :=
            (mem_leftAnchorPositions_iff anchor j).mp hendpoints.2
          simp only [PositionBlock.map,
            PositionBlock.pair.injEq] at hbmap
          rcases hbmap with ⟨hiOffset, hjOffset⟩
          right
          refine ⟨i, j, hb, ?_, ?_⟩
          · apply Fin.ext
            simp only [anchorPositionOutwardOffset,
              if_pos hj] at hjOffset
            dsimp [d] at hjOffset
            omega
          · simp only [anchorPositionOutwardOffset,
              if_pos hi, if_pos hj] at hiOffset hjOffset
            omega
  | true =>
      have hdeven : d % 2 = 0 := by
        change decide (d % 2 = 0) = true at hphase
        simpa using hphase
      by_cases hd : d = 0
      · have hanchor : 0 < anchor.1 := by omega
        have hoffset :
            PositionBlock.single 0 ∈
              pairPositionRun true (List.range anchor.1) := by
          rw [List.range_eq_range']
          cases ha : anchor.1 with
          | zero => omega
          | succ n =>
              rw [List.range'_succ]
              simp [pairPositionRun]
        have hmapped :
            PositionBlock.single 0 ∈
              (pairPositionRun true
                (leftAnchorPositions anchor)).map
                  (PositionBlock.map
                    (anchorPositionOutwardOffset anchor)) := by
          rw [pairPositionRun_map,
            map_anchorPositionOutwardOffset_left]
          exact hoffset
        obtain ⟨b, hb, hbmap⟩ := List.mem_map.mp hmapped
        cases b with
        | pair i j =>
            simp [PositionBlock.map] at hbmap
        | single i =>
            have hi : i.1 < anchor.1 := by
              apply (mem_leftAnchorPositions_iff anchor i).mp
              rw [← flatten_pairPositionRun true
                (leftAnchorPositions anchor), List.mem_flatMap]
              exact ⟨PositionBlock.single i, hb,
                by simp [PositionBlock.entries]⟩
            simp only [PositionBlock.map,
              PositionBlock.single.injEq] at hbmap
            have hieq : i = edge.1 := by
              apply Fin.ext
              simp only [anchorPositionOutwardOffset,
                if_pos hi] at hbmap
              dsimp [d] at hd
              omega
            left
            refine ⟨i, hb, ?_⟩
            subst i
            simp [PositionBlock.affectedEdges,
              positionIncidentEdges, reverseIncomingEdge, edge.2]
      · have hparity : (d - 1) % 2 = 1 := by omega
        have hoffset :
            PositionBlock.pair (d - 1) d ∈
              pairPositionRun true (List.range anchor.1) := by
          rw [List.range_eq_range']
          have h :=
            pair_mem_pairPositionRun_range'_of_bounds
              true 0 anchor.1 (d - 1) (by omega) (by omega)
                (by simpa using hparity)
          simpa only [Nat.sub_add_cancel
            (Nat.one_le_iff_ne_zero.mpr hd)] using h
        have hmapped :
            PositionBlock.pair (d - 1) d ∈
              (pairPositionRun true
                (leftAnchorPositions anchor)).map
                  (PositionBlock.map
                    (anchorPositionOutwardOffset anchor)) := by
          rw [pairPositionRun_map,
            map_anchorPositionOutwardOffset_left]
          exact hoffset
        obtain ⟨b, hb, hbmap⟩ := List.mem_map.mp hmapped
        cases b with
        | single x =>
            simp [PositionBlock.map] at hbmap
        | pair i j =>
            have hendpoints :=
              pairPositionRun_pair_endpoints_mem
                true (leftAnchorPositions anchor) i j hb
            have hi : i.1 < anchor.1 :=
              (mem_leftAnchorPositions_iff anchor i).mp hendpoints.1
            have hj : j.1 < anchor.1 :=
              (mem_leftAnchorPositions_iff anchor j).mp hendpoints.2
            simp only [PositionBlock.map,
              PositionBlock.pair.injEq] at hbmap
            rcases hbmap with ⟨hiOffset, hjOffset⟩
            right
            refine ⟨i, j, hb, ?_, ?_⟩
            · apply Fin.ext
              simp only [anchorPositionOutwardOffset,
                if_pos hj] at hjOffset
              dsimp [d] at hjOffset
              omega
            · simp only [anchorPositionOutwardOffset,
                if_pos hi, if_pos hj] at hiOffset hjOffset
              omega

/-- On the forward right run, every selected edge is either the boundary
edge consumed by the shifted singleton or the internal edge of a concrete
pair. -/
private theorem right_phaseCarrier_edge_pair_or_single
    {m : ℕ} (phase : Bool) (anchor : Fin m)
    (edge : AdjacentIndex m) (hright : anchor.1 ≤ edge.1.1)
    (hphase :
      decide ((edge.1.1 - anchor.1) % 2 = 0) = phase) :
    (∃ i : Fin m,
        PositionBlock.single i ∈
          pairPositionRun phase (rightAnchorPositions anchor) ∧
        edge ∈ (PositionBlock.single i).affectedEdges) ∨
      ∃ i j : Fin m,
        PositionBlock.pair i j ∈
          pairPositionRun phase (rightAnchorPositions anchor) ∧
        edge.1 = i ∧ i.1 + 1 = j.1 := by
  let d := edge.1.1 - anchor.1
  have hdlt : d < m - (anchor.1 + 1) := by
    dsimp [d]
    omega
  cases phase with
  | false =>
      have hodd : d % 2 ≠ 0 := by
        change decide (d % 2 = 0) = false at hphase
        simpa using hphase
      have hdne : d ≠ 0 := by
        intro hd
        apply hodd
        simp [hd]
      have hparity : (d - 1) % 2 = 0 := by
        omega
      have hoffset :
          PositionBlock.pair (d - 1) d ∈
            pairPositionRun false
              (List.range (m - (anchor.1 + 1))) := by
        rw [List.range_eq_range']
        have h :=
          pair_mem_pairPositionRun_range'_of_bounds
            false 0 (m - (anchor.1 + 1)) (d - 1)
              (by omega) (by omega) (by simpa using hparity)
        simpa only [Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hdne)] using h
      have hmapped :
          PositionBlock.pair (d - 1) d ∈
            (pairPositionRun false
              (rightAnchorPositions anchor)).map
                (PositionBlock.map
                  (anchorPositionOutwardOffset anchor)) := by
        rw [pairPositionRun_map,
          map_anchorPositionOutwardOffset_right]
        exact hoffset
      obtain ⟨b, hb, hbmap⟩ := List.mem_map.mp hmapped
      cases b with
      | single x =>
          simp [PositionBlock.map] at hbmap
      | pair i j =>
          have hendpoints :=
            pairPositionRun_pair_endpoints_mem
              false (rightAnchorPositions anchor) i j hb
          have hi : anchor.1 < i.1 :=
            (mem_rightAnchorPositions_iff anchor i).mp hendpoints.1
          have hj : anchor.1 < j.1 :=
            (mem_rightAnchorPositions_iff anchor j).mp hendpoints.2
          simp only [PositionBlock.map,
            PositionBlock.pair.injEq] at hbmap
          rcases hbmap with ⟨hiOffset, hjOffset⟩
          right
          refine ⟨i, j, hb, ?_, ?_⟩
          · apply Fin.ext
            simp only [anchorPositionOutwardOffset,
              if_neg (not_lt_of_ge (Nat.le_of_lt hi))] at hiOffset
            dsimp [d] at hiOffset
            omega
          · simp only [anchorPositionOutwardOffset,
              if_neg (not_lt_of_ge (Nat.le_of_lt hi)),
              if_neg (not_lt_of_ge (Nat.le_of_lt hj))] at hiOffset hjOffset
            omega
  | true =>
      have hdeven : d % 2 = 0 := by
        change decide (d % 2 = 0) = true at hphase
        simpa using hphase
      by_cases hd : d = 0
      · have hlen : 0 < m - (anchor.1 + 1) := by omega
        have hoffset :
            PositionBlock.single 0 ∈
              pairPositionRun true
                (List.range (m - (anchor.1 + 1))) := by
          rw [List.range_eq_range']
          cases hn : m - (anchor.1 + 1) with
          | zero => omega
          | succ n =>
              rw [List.range'_succ]
              simp [pairPositionRun]
        have hmapped :
            PositionBlock.single 0 ∈
              (pairPositionRun true
                (rightAnchorPositions anchor)).map
                  (PositionBlock.map
                    (anchorPositionOutwardOffset anchor)) := by
          rw [pairPositionRun_map,
            map_anchorPositionOutwardOffset_right]
          exact hoffset
        obtain ⟨b, hb, hbmap⟩ := List.mem_map.mp hmapped
        cases b with
        | pair i j =>
            simp [PositionBlock.map] at hbmap
        | single i =>
            have hi : anchor.1 < i.1 := by
              apply (mem_rightAnchorPositions_iff anchor i).mp
              rw [← flatten_pairPositionRun true
                (rightAnchorPositions anchor), List.mem_flatMap]
              exact ⟨PositionBlock.single i, hb,
                by simp [PositionBlock.entries]⟩
            simp only [PositionBlock.map,
              PositionBlock.single.injEq] at hbmap
            have hieq : i.1 = edge.1.1 + 1 := by
              simp only [anchorPositionOutwardOffset,
                if_neg (not_lt_of_ge (Nat.le_of_lt hi))] at hbmap
              dsimp [d] at hd
              omega
            left
            refine ⟨i, hb, ?_⟩
            unfold PositionBlock.affectedEdges positionIncidentEdges
            apply Finset.mem_union.mpr
            left
            have hforward : forwardIncomingEdge i = some edge := by
              unfold forwardIncomingEdge
              rw [dif_pos (by omega)]
              congr 2
              apply Fin.ext
              simp only
              omega
            rw [hforward]
            simp
      · have hparity : (d - 1) % 2 = 1 := by omega
        have hoffset :
            PositionBlock.pair (d - 1) d ∈
              pairPositionRun true
                (List.range (m - (anchor.1 + 1))) := by
          rw [List.range_eq_range']
          have h :=
            pair_mem_pairPositionRun_range'_of_bounds
              true 0 (m - (anchor.1 + 1)) (d - 1)
                (by omega) (by omega) (by simpa using hparity)
          simpa only [Nat.sub_add_cancel
            (Nat.one_le_iff_ne_zero.mpr hd)] using h
        have hmapped :
            PositionBlock.pair (d - 1) d ∈
              (pairPositionRun true
                (rightAnchorPositions anchor)).map
                  (PositionBlock.map
                    (anchorPositionOutwardOffset anchor)) := by
          rw [pairPositionRun_map,
            map_anchorPositionOutwardOffset_right]
          exact hoffset
        obtain ⟨b, hb, hbmap⟩ := List.mem_map.mp hmapped
        cases b with
        | single x =>
            simp [PositionBlock.map] at hbmap
        | pair i j =>
            have hendpoints :=
              pairPositionRun_pair_endpoints_mem
                true (rightAnchorPositions anchor) i j hb
            have hi : anchor.1 < i.1 :=
              (mem_rightAnchorPositions_iff anchor i).mp hendpoints.1
            have hj : anchor.1 < j.1 :=
              (mem_rightAnchorPositions_iff anchor j).mp hendpoints.2
            simp only [PositionBlock.map,
              PositionBlock.pair.injEq] at hbmap
            rcases hbmap with ⟨hiOffset, hjOffset⟩
            right
            refine ⟨i, j, hb, ?_, ?_⟩
            · apply Fin.ext
              simp only [anchorPositionOutwardOffset,
                if_neg (not_lt_of_ge (Nat.le_of_lt hi))] at hiOffset
              dsimp [d] at hiOffset
              omega
            · simp only [anchorPositionOutwardOffset,
                if_neg (not_lt_of_ge (Nat.le_of_lt hi)),
                if_neg (not_lt_of_ge (Nat.le_of_lt hj))] at hiOffset hjOffset
              omega

/-- Every edge selected by a phase schedule is accounted for by a concrete
block: either it is incident to a singleton, or it is the internal edge of
a pair.  This is the converse coverage statement missing from the earlier
pair-to-carrier interface. -/
theorem finAnchorPositionPhaseCarrier_pair_or_single
    {m : ℕ} (leftPhase rightPhase : Bool) (anchor : Fin m)
    (edge : AdjacentIndex m)
    (hedge : edge ∈
      finAnchorPositionPhaseCarrierWithPhases
        leftPhase rightPhase anchor) :
    (∃ i : Fin m,
        PositionBlock.single i ∈
          finAnchorPositionScheduleWithPhases
            leftPhase rightPhase anchor ∧
        edge ∈ (PositionBlock.single i).affectedEdges) ∨
      ∃ i j : Fin m,
        PositionBlock.pair i j ∈
          finAnchorPositionScheduleWithPhases
            leftPhase rightPhase anchor ∧
        ((edge.1 = i ∧ i.1 + 1 = j.1) ∨
          (edge.1 = j ∧ j.1 + 1 = i.1)) := by
  rw [mem_finAnchorPositionPhaseCarrierWithPhases] at hedge
  by_cases hleft : edge.1.1 < anchor.1
  · have hphase :
        decide ((anchor.1 - 1 - edge.1.1) % 2 = 0) =
          leftPhase := by
      simpa [anchorEdgeOutwardDistance,
        anchorEdgeSelectedPhase, hleft] using hedge
    rcases left_phaseCarrier_edge_pair_or_single
        leftPhase anchor edge hleft hphase with hsingle | hpair
    · left
      obtain ⟨i, hi, hedgei⟩ := hsingle
      exact ⟨i, by
        simpa [finAnchorPositionScheduleWithPhases,
          anchorPositionScheduleWithPhases] using
            (List.mem_append_left _ hi), hedgei⟩
    · right
      obtain ⟨i, j, hp, heq, hadj⟩ := hpair
      refine ⟨i, j, ?_, Or.inr ⟨heq, hadj⟩⟩
      simpa [finAnchorPositionScheduleWithPhases,
        anchorPositionScheduleWithPhases] using
          (List.mem_append_left _ hp)
  · have hright : anchor.1 ≤ edge.1.1 := Nat.le_of_not_gt hleft
    have hphase :
        decide ((edge.1.1 - anchor.1) % 2 = 0) =
          rightPhase := by
      simpa [anchorEdgeOutwardDistance,
        anchorEdgeSelectedPhase, hleft] using hedge
    rcases right_phaseCarrier_edge_pair_or_single
        rightPhase anchor edge hright hphase with hsingle | hpair
    · left
      obtain ⟨i, hi, hedgei⟩ := hsingle
      exact ⟨i, by
        simpa [finAnchorPositionScheduleWithPhases,
          anchorPositionScheduleWithPhases] using
            (List.mem_append_right _ hi), hedgei⟩
    · right
      obtain ⟨i, j, hp, heq, hadj⟩ := hpair
      refine ⟨i, j, ?_, Or.inl ⟨heq, hadj⟩⟩
      simpa [finAnchorPositionScheduleWithPhases,
        anchorPositionScheduleWithPhases] using
          (List.mem_append_right _ hp)

/--
Every concrete pair block contributes its internal original-word edge to
the phase carrier selected for that side of the anchor.  The disjunction
records the reversal of the left run: right-run pairs are `(i,i+1)`, while
left-run pairs are `(i,i-1)` in traversal order.
-/
theorem finAnchorPositionSchedule_pair_internalEdge_mem_phaseCarrier
    {m : ℕ} (leftPhase rightPhase : Bool) (anchor i j : Fin m)
    (hpair : PositionBlock.pair i j ∈
      finAnchorPositionScheduleWithPhases
        leftPhase rightPhase anchor) :
    ∃ edge : AdjacentIndex m,
      edge ∈ finAnchorPositionPhaseCarrierWithPhases
          leftPhase rightPhase anchor ∧
        ((edge.1 = i ∧ i.1 + 1 = j.1) ∨
          (edge.1 = j ∧ j.1 + 1 = i.1)) := by
  have hsides :
      PositionBlock.pair i j ∈
          pairPositionRun leftPhase (leftAnchorPositions anchor) ∨
        PositionBlock.pair i j ∈
          pairPositionRun rightPhase (rightAnchorPositions anchor) := by
    simpa [finAnchorPositionScheduleWithPhases,
      anchorPositionScheduleWithPhases] using hpair
  rcases hsides with hleft | hright
  · have hendpoints :=
      pairPositionRun_pair_endpoints_mem
        leftPhase (leftAnchorPositions anchor) i j hleft
    have hi : i.1 < anchor.1 :=
      (mem_leftAnchorPositions_iff anchor i).mp hendpoints.1
    have hj : j.1 < anchor.1 :=
      (mem_leftAnchorPositions_iff anchor j).mp hendpoints.2
    have hmapped :
        PositionBlock.pair
            (anchorPositionOutwardOffset anchor i)
            (anchorPositionOutwardOffset anchor j) ∈
          pairPositionRun leftPhase (List.range anchor.1) := by
      rw [← map_anchorPositionOutwardOffset_left,
        ← pairPositionRun_map]
      exact List.mem_map_of_mem hleft
    rw [List.range_eq_range'] at hmapped
    have hstep :=
      pair_mem_pairPositionRun_range'
        leftPhase 0 anchor.1
          (anchorPositionOutwardOffset anchor i)
          (anchorPositionOutwardOffset anchor j) hmapped
    have hadj : j.1 + 1 = i.1 := by
      simp only [anchorPositionOutwardOffset, if_pos hi, if_pos hj] at hstep
      omega
    let edge : AdjacentIndex m := ⟨j, by omega⟩
    refine ⟨edge, ?_, Or.inr ⟨rfl, hadj⟩⟩
    rw [mem_finAnchorPositionPhaseCarrierWithPhases]
    simp only [anchorEdgeOutwardDistance,
      anchorEdgeSelectedPhase, edge, if_pos hj]
    simp only [anchorPositionOutwardOffset, if_pos hi, if_pos hj] at hstep
    cases leftPhase <;> simp_all <;> omega
  · have hendpoints :=
      pairPositionRun_pair_endpoints_mem
        rightPhase (rightAnchorPositions anchor) i j hright
    have hi : anchor.1 < i.1 :=
      (mem_rightAnchorPositions_iff anchor i).mp hendpoints.1
    have hj : anchor.1 < j.1 :=
      (mem_rightAnchorPositions_iff anchor j).mp hendpoints.2
    have hmapped :
        PositionBlock.pair
            (anchorPositionOutwardOffset anchor i)
            (anchorPositionOutwardOffset anchor j) ∈
          pairPositionRun rightPhase
            (List.range (m - (anchor.1 + 1))) := by
      rw [← map_anchorPositionOutwardOffset_right,
        ← pairPositionRun_map]
      exact List.mem_map_of_mem hright
    rw [List.range_eq_range'] at hmapped
    have hstep :=
      pair_mem_pairPositionRun_range'
        rightPhase 0 (m - (anchor.1 + 1))
          (anchorPositionOutwardOffset anchor i)
          (anchorPositionOutwardOffset anchor j) hmapped
    have hadj : i.1 + 1 = j.1 := by
      simp only [anchorPositionOutwardOffset,
        if_neg (not_lt_of_ge (Nat.le_of_lt hi)),
        if_neg (not_lt_of_ge (Nat.le_of_lt hj))] at hstep
      omega
    let edge : AdjacentIndex m := ⟨i, by omega⟩
    refine ⟨edge, ?_, Or.inl ⟨rfl, hadj⟩⟩
    rw [mem_finAnchorPositionPhaseCarrierWithPhases]
    simp only [anchorEdgeOutwardDistance,
      anchorEdgeSelectedPhase, edge,
      if_neg (not_lt_of_ge (Nat.le_of_lt hi))]
    simp only [anchorPositionOutwardOffset,
      if_neg (not_lt_of_ge (Nat.le_of_lt hi)),
      if_neg (not_lt_of_ge (Nat.le_of_lt hj))] at hstep
    cases rightPhase <;> simp_all <;> omega

private theorem card_optionToFinset_le_one {α : Type*}
    [DecidableEq α] (o : Option α) :
    o.toFinset.card ≤ 1 := by
  cases o <;> simp

theorem card_positionIncidentEdges_le_two {m : ℕ} (i : Fin m) :
    (positionIncidentEdges i).card ≤ 2 := by
  calc
    (positionIncidentEdges i).card ≤
        (forwardIncomingEdge i).toFinset.card +
          (reverseIncomingEdge i).toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ 1 + 1 :=
      Nat.add_le_add
        (card_optionToFinset_le_one (forwardIncomingEdge i))
        (card_optionToFinset_le_one (reverseIncomingEdge i))
    _ = 2 := by norm_num

theorem PositionBlock.card_affectedEdges_le {m : ℕ}
    (b : PositionBlock (Fin m)) :
    b.affectedEdges.card ≤
      match b with
      | .single _ => 2
      | .pair _ _ => 4 := by
  cases b with
  | single i =>
      exact card_positionIncidentEdges_le_two i
  | pair i j =>
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add
          (card_positionIncidentEdges_le_two i)
          (card_positionIncidentEdges_le_two j))

/-- Consecutive positions share their connecting edge, so their incident
edge union has cardinality at most three. -/
theorem PositionBlock.card_affectedEdges_pair_le_three_of_adjacent
    {m : ℕ} (i j : Fin m)
    (hij : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) :
    (PositionBlock.pair i j).affectedEdges.card ≤ 3 := by
  have forwardCase (x y : Fin m) (hxy : x.1 + 1 = y.1) :
      (positionIncidentEdges x ∪ positionIncidentEdges y).card ≤ 3 := by
    let e : AdjacentIndex m := ⟨x, by omega⟩
    have hxedge : x.1 + 1 < m := by omega
    have hreverse : reverseIncomingEdge x = some e := by
      rw [reverseIncomingEdge, dif_pos hxedge]
    have hypos : 0 < y.1 := by omega
    have hforward : forwardIncomingEdge y = some e := by
      rw [forwardIncomingEdge, dif_pos hypos]
      congr 1
      apply Subtype.ext
      apply Fin.ext
      simp [e]
      omega
    have hex : e ∈ positionIncidentEdges x := by
      unfold positionIncidentEdges
      apply Finset.mem_union.mpr
      exact Or.inr (by rw [hreverse]; simp)
    have hey : e ∈ positionIncidentEdges y := by
      unfold positionIncidentEdges
      apply Finset.mem_union.mpr
      exact Or.inl (by rw [hforward]; simp)
    have hinter :
        1 ≤ (positionIncidentEdges x ∩ positionIncidentEdges y).card :=
      Finset.one_le_card.mpr ⟨e, Finset.mem_inter.mpr ⟨hex, hey⟩⟩
    have hunion :=
      Finset.card_union_add_card_inter
        (positionIncidentEdges x) (positionIncidentEdges y)
    have hx := card_positionIncidentEdges_le_two x
    have hy := card_positionIncidentEdges_le_two y
    omega
  rcases hij with hij | hji
  · exact forwardCase i j hij
  · simpa [PositionBlock.affectedEdges, Finset.union_comm] using
      forwardCase j i hji

/-- An analytic parity block together with the exact original positions it
eliminates.  Unlike `NXParityBlock`, this type retains enough information to
state which gain indices are discarded.  The constructors enforce matching
one- and two-variable arity. -/
inductive LocatedNXParityBlock {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
  | single (position : Fin m) (a : ActiveNXClass Nm mu) (skipped : Bool)
  | pair (leftPosition rightPosition : Fin m) (p : NXPairBlock Nm mu)
  | roughPair
      (leftPosition rightPosition : Fin m) (p : NXPairBlock Nm mu)

def LocatedNXParityBlock.positionBlock {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    LocatedNXParityBlock (m := m) Nm mu → PositionBlock (Fin m)
  | .single i _ _ => .single i
  | .pair i j _ => .pair i j
  | .roughPair i j _ => .pair i j

def LocatedNXParityBlock.analyticBlock {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    LocatedNXParityBlock (m := m) Nm mu → NXParityBlock Nm mu
  | .single _ a skipped => .single a skipped
  | .pair _ _ p => .pair p
  | .roughPair _ _ p => .roughPair p

def locatePositionBlock {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool) :
    PositionBlock (Fin m) → LocatedNXParityBlock (m := m) Nm mu
  | .single i => .single i (cls i) (incomingSkipped i)
  | .pair i j =>
      .pair i j
        { left := cls i
          right := cls j
          skipLeft := incomingSkipped i
          skipRight := incomingSkipped j }

@[simp] theorem analyticBlock_locatePositionBlock
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool)
    (b : PositionBlock (Fin m)) :
    (locatePositionBlock Nm mu cls incomingSkipped b).analyticBlock =
      positionBlockToNXParityBlock Nm mu cls incomingSkipped b := by
  cases b <;> rfl

@[simp] theorem positionBlock_locatePositionBlock
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool)
    (b : PositionBlock (Fin m)) :
    (locatePositionBlock Nm mu cls incomingSkipped b).positionBlock = b := by
  cases b <;> rfl

/-- Position-preserving version of `markFirstSkippedPairsRough`. -/
def markFirstSkippedLocatedPairsRough {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    ℕ → List (LocatedNXParityBlock (m := m) Nm mu) →
      List (LocatedNXParityBlock (m := m) Nm mu)
  | _, [] => []
  | 0, bs => bs
  | fuel + 1, b :: bs =>
      match b with
      | .single i a skipped =>
          .single i a skipped ::
            markFirstSkippedLocatedPairsRough (fuel + 1) bs
      | .pair i j p =>
          if nxPairBlockTouchesSkip p then
            .roughPair i j p ::
              markFirstSkippedLocatedPairsRough fuel bs
          else
            .pair i j p ::
              markFirstSkippedLocatedPairsRough (fuel + 1) bs
      | .roughPair i j p =>
          .roughPair i j p ::
            markFirstSkippedLocatedPairsRough (fuel + 1) bs

@[simp] theorem map_analyticBlock_markFirstSkippedLocatedPairsRough
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (markFirstSkippedLocatedPairsRough fuel bs).map
        LocatedNXParityBlock.analyticBlock =
      markFirstSkippedPairsRough fuel
        (bs.map LocatedNXParityBlock.analyticBlock) := by
  induction bs generalizing fuel with
  | nil =>
      simp [markFirstSkippedLocatedPairsRough,
        markFirstSkippedPairsRough]
  | cons b bs ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases b with
          | single i a skipped =>
              simp [markFirstSkippedLocatedPairsRough,
                markFirstSkippedPairsRough,
                LocatedNXParityBlock.analyticBlock, ih]
          | pair i j p =>
              by_cases h : nxPairBlockTouchesSkip p
              · simp [markFirstSkippedLocatedPairsRough,
                  markFirstSkippedPairsRough,
                  LocatedNXParityBlock.analyticBlock, h, ih]
              · have hb : nxPairBlockTouchesSkip p = false :=
                  Bool.eq_false_of_not_eq_true h
                simp [markFirstSkippedLocatedPairsRough,
                  markFirstSkippedPairsRough,
                  LocatedNXParityBlock.analyticBlock, hb, ih]
          | roughPair i j p =>
              simp [markFirstSkippedLocatedPairsRough,
                markFirstSkippedPairsRough,
                LocatedNXParityBlock.analyticBlock, ih]

@[simp] theorem map_positionBlock_markFirstSkippedLocatedPairsRough
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (markFirstSkippedLocatedPairsRough fuel bs).map
        LocatedNXParityBlock.positionBlock =
      bs.map LocatedNXParityBlock.positionBlock := by
  induction bs generalizing fuel with
  | nil =>
      simp [markFirstSkippedLocatedPairsRough]
  | cons b bs ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases b with
          | single i a skipped =>
              simp [markFirstSkippedLocatedPairsRough,
                LocatedNXParityBlock.positionBlock, ih]
          | pair i j p =>
              by_cases h : nxPairBlockTouchesSkip p
              · simp [markFirstSkippedLocatedPairsRough,
                  LocatedNXParityBlock.positionBlock, h, ih]
              · have hb : nxPairBlockTouchesSkip p = false :=
                  Bool.eq_false_of_not_eq_true h
                simp [markFirstSkippedLocatedPairsRough,
                  LocatedNXParityBlock.positionBlock, hb, ih]
          | roughPair i j p =>
              simp [markFirstSkippedLocatedPairsRough,
                LocatedNXParityBlock.positionBlock, ih]

/-- A precise pair surviving the first-skipped marking was already the
same precise pair in the raw ledger.  Marking can only replace a precise
pair by a rough pair; it never creates a new precise payload. -/
private theorem precisePair_mem_of_mem_markFirstSkippedLocatedPairsRough
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ)
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (i j : Fin m) (p : NXPairBlock Nm mu)
    (hmem :
      LocatedNXParityBlock.pair i j p ∈
        markFirstSkippedLocatedPairsRough fuel bs) :
    LocatedNXParityBlock.pair i j p ∈ bs := by
  induction bs generalizing fuel with
  | nil =>
      simp [markFirstSkippedLocatedPairsRough] at hmem
  | cons b bs ih =>
      cases fuel with
      | zero => exact hmem
      | succ fuel =>
          cases b with
          | single k a skipped =>
              rw [markFirstSkippedLocatedPairsRough] at hmem
              rcases List.mem_cons.mp hmem with hbad | htail
              · cases hbad
              · exact List.mem_cons.mpr
                  (Or.inr (ih (fuel + 1) htail))
          | pair k l q =>
              by_cases htouch : nxPairBlockTouchesSkip q
              · rw [markFirstSkippedLocatedPairsRough,
                  if_pos htouch] at hmem
                rcases List.mem_cons.mp hmem with hbad | htail
                · cases hbad
                · exact List.mem_cons.mpr
                    (Or.inr (ih fuel htail))
              · have hfalse :
                    nxPairBlockTouchesSkip q = false :=
                  Bool.eq_false_of_not_eq_true htouch
                rw [markFirstSkippedLocatedPairsRough,
                  hfalse] at hmem
                rcases List.mem_cons.mp hmem with hhead | htail
                · exact List.mem_cons.mpr (Or.inl hhead)
                · exact List.mem_cons.mpr
                    (Or.inr (ih (fuel + 1) htail))
          | roughPair k l q =>
              rw [markFirstSkippedLocatedPairsRough] at hmem
              rcases List.mem_cons.mp hmem with hbad | htail
              · cases hbad
              · exact List.mem_cons.mpr
                  (Or.inr (ih (fuel + 1) htail))

/-- Union of the *actual original chain edges* affected by single and rough
blocks.  Precise pair blocks do not discard any gain. -/
def locatedExceptionalEdges {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    List (LocatedNXParityBlock (m := m) Nm mu) →
      Finset (AdjacentIndex m)
  | [] => ∅
  | .single i _ _ :: bs =>
      (PositionBlock.single i).affectedEdges ∪ locatedExceptionalEdges bs
  | .pair _ _ _ :: bs => locatedExceptionalEdges bs
  | .roughPair i j _ :: bs =>
      (PositionBlock.pair i j).affectedEdges ∪ locatedExceptionalEdges bs

private theorem mem_locatedExceptionalEdges_of_single_mem
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (i : Fin m) (a : ActiveNXClass Nm mu) (skipped : Bool)
    (edge : AdjacentIndex m)
    (hblock : LocatedNXParityBlock.single i a skipped ∈ bs)
    (hedge : edge ∈ (PositionBlock.single i).affectedEdges) :
    edge ∈ locatedExceptionalEdges bs := by
  induction bs with
  | nil => simp at hblock
  | cons b bs ih =>
      simp only [List.mem_cons] at hblock
      rcases hblock with hhead | htail
      · subst b
        simp [locatedExceptionalEdges, hedge]
      · cases b <;>
          simp [locatedExceptionalEdges, ih htail]

private theorem mem_locatedExceptionalEdges_of_roughPair_mem
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (LocatedNXParityBlock (m := m) Nm mu))
    (i j : Fin m) (p : NXPairBlock Nm mu)
    (edge : AdjacentIndex m)
    (hblock : LocatedNXParityBlock.roughPair i j p ∈ bs)
    (hedge : edge ∈ (PositionBlock.pair i j).affectedEdges) :
    edge ∈ locatedExceptionalEdges bs := by
  induction bs with
  | nil => simp at hblock
  | cons b bs ih =>
      simp only [List.mem_cons] at hblock
      rcases hblock with hhead | htail
      · subst b
        simp [locatedExceptionalEdges, hedge]
      · cases b <;>
          simp [locatedExceptionalEdges, ih htail]

/-- The explicit edge union is bounded by exactly the same `2·single +
4·rough` budget used for the scalar losses.  The proof does not infer an
exception count from prose: every recorded edge is incident to a concrete
position in an exceptional block. -/
theorem card_locatedExceptionalEdges_le_lossAtomBudget
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (locatedExceptionalEdges bs).card ≤
      positionLossAtomBudget
        (nxParitySingleCount
          (bs.map LocatedNXParityBlock.analyticBlock))
        (nxParityRoughPairCount
          (bs.map LocatedNXParityBlock.analyticBlock)) := by
  induction bs with
  | nil =>
      simp [locatedExceptionalEdges, positionLossAtomBudget,
        nxParitySingleCount, nxParityRoughPairCount]
  | cons b bs ih =>
      cases b with
      | single i a skipped =>
          calc
            (locatedExceptionalEdges
                (.single i a skipped :: bs)).card ≤
                (PositionBlock.single i).affectedEdges.card +
                  (locatedExceptionalEdges bs).card :=
              Finset.card_union_le _ _
            _ ≤ 2 +
                positionLossAtomBudget
                  (nxParitySingleCount
                    (bs.map LocatedNXParityBlock.analyticBlock))
                  (nxParityRoughPairCount
                    (bs.map LocatedNXParityBlock.analyticBlock)) :=
              Nat.add_le_add
                (PositionBlock.card_affectedEdges_le (.single i)) ih
            _ = positionLossAtomBudget
                (nxParitySingleCount
                  ((.single i a skipped :: bs).map
                    LocatedNXParityBlock.analyticBlock))
                (nxParityRoughPairCount
              ((.single i a skipped :: bs).map
                    LocatedNXParityBlock.analyticBlock)) := by
              simp [LocatedNXParityBlock.analyticBlock,
                positionLossAtomBudget]
              omega
      | pair i j p =>
          simpa [locatedExceptionalEdges,
            LocatedNXParityBlock.analyticBlock] using ih
      | roughPair i j p =>
          calc
            (locatedExceptionalEdges
                (.roughPair i j p :: bs)).card ≤
                (PositionBlock.pair i j).affectedEdges.card +
                  (locatedExceptionalEdges bs).card :=
              Finset.card_union_le _ _
            _ ≤ 4 +
                positionLossAtomBudget
                  (nxParitySingleCount
                    (bs.map LocatedNXParityBlock.analyticBlock))
                  (nxParityRoughPairCount
                    (bs.map LocatedNXParityBlock.analyticBlock)) :=
              Nat.add_le_add
                (PositionBlock.card_affectedEdges_le (.pair i j)) ih
            _ = positionLossAtomBudget
                (nxParitySingleCount
                  ((.roughPair i j p :: bs).map
                    LocatedNXParityBlock.analyticBlock))
                (nxParityRoughPairCount
              ((.roughPair i j p :: bs).map
                    LocatedNXParityBlock.analyticBlock)) := by
              simp [LocatedNXParityBlock.analyticBlock,
                positionLossAtomBudget]
              omega

/-! ### Erasing the analytic class payload from the exception ledger -/

/-- The positional and skipped-edge data which alone controls rough marking. -/
inductive PositionExceptionControlBlock (m : ℕ)
  | single (position : Fin m) (skipped : Bool)
  | pair
      (leftPosition rightPosition : Fin m)
      (skipLeft skipRight : Bool)
  | roughPair
      (leftPosition rightPosition : Fin m)
      (skipLeft skipRight : Bool)
deriving DecidableEq

def positionBlockToExceptionControl {m : ℕ}
    (incomingSkipped : Fin m → Bool) :
    PositionBlock (Fin m) → PositionExceptionControlBlock m
  | .single i => .single i (incomingSkipped i)
  | .pair i j =>
      .pair i j (incomingSkipped i) (incomingSkipped j)

def LocatedNXParityBlock.exceptionControl
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t} :
    LocatedNXParityBlock (m := m) Nm mu →
      PositionExceptionControlBlock m
  | .single i _ skipped => .single i skipped
  | .pair i j p => .pair i j p.skipLeft p.skipRight
  | .roughPair i j p => .roughPair i j p.skipLeft p.skipRight

@[simp] theorem exceptionControl_locatePositionBlock
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (cls : Fin m → ActiveNXClass Nm mu)
    (incomingSkipped : Fin m → Bool)
    (b : PositionBlock (Fin m)) :
    (locatePositionBlock Nm mu cls incomingSkipped b).exceptionControl =
      positionBlockToExceptionControl incomingSkipped b := by
  cases b <;> rfl

/-- Pure positional copy of “mark the first three eligible pairs rough”. -/
def markFirstSkippedPositionExceptionRough {m : ℕ} :
    ℕ → List (PositionExceptionControlBlock m) →
      List (PositionExceptionControlBlock m)
  | _, [] => []
  | 0, bs => bs
  | fuel + 1, b :: bs =>
      match b with
      | .single i skipped =>
          .single i skipped ::
            markFirstSkippedPositionExceptionRough (fuel + 1) bs
      | .pair i j skipLeft skipRight =>
          if skipLeft || skipRight then
            .roughPair i j skipLeft skipRight ::
              markFirstSkippedPositionExceptionRough fuel bs
          else
            .pair i j skipLeft skipRight ::
              markFirstSkippedPositionExceptionRough (fuel + 1) bs
      | .roughPair i j skipLeft skipRight =>
          .roughPair i j skipLeft skipRight ::
            markFirstSkippedPositionExceptionRough (fuel + 1) bs

@[simp] theorem map_exceptionControl_markFirstSkippedLocatedPairsRough
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (fuel : ℕ) (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    (markFirstSkippedLocatedPairsRough fuel bs).map
        LocatedNXParityBlock.exceptionControl =
      markFirstSkippedPositionExceptionRough fuel
        (bs.map LocatedNXParityBlock.exceptionControl) := by
  induction bs generalizing fuel with
  | nil =>
      simp [markFirstSkippedLocatedPairsRough,
        markFirstSkippedPositionExceptionRough]
  | cons b bs ih =>
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases b with
          | single i a skipped =>
              simp [markFirstSkippedLocatedPairsRough,
                markFirstSkippedPositionExceptionRough,
                LocatedNXParityBlock.exceptionControl, ih]
          | pair i j p =>
              cases hleft : p.skipLeft <;>
                cases hright : p.skipRight <;>
                simp [markFirstSkippedLocatedPairsRough,
                  markFirstSkippedPositionExceptionRough,
                  LocatedNXParityBlock.exceptionControl,
                  nxPairBlockTouchesSkip, hleft, hright, ih]
          | roughPair i j p =>
              simp [markFirstSkippedLocatedPairsRough,
                markFirstSkippedPositionExceptionRough,
                LocatedNXParityBlock.exceptionControl, ih]

/-- Exceptional original edges computed with no analytic class payload. -/
def positionExceptionControlEdges {m : ℕ} :
    List (PositionExceptionControlBlock m) →
      Finset (AdjacentIndex m)
  | [] => ∅
  | .single i _ :: bs =>
      (PositionBlock.single i).affectedEdges ∪
        positionExceptionControlEdges bs
  | .pair _ _ _ _ :: bs =>
      positionExceptionControlEdges bs
  | .roughPair i j _ _ :: bs =>
      (PositionBlock.pair i j).affectedEdges ∪
        positionExceptionControlEdges bs

theorem positionExceptionControlEdges_map_exceptionControl
    {t : PlaneTree} {m : ℕ}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (bs : List (LocatedNXParityBlock (m := m) Nm mu)) :
    positionExceptionControlEdges
        (bs.map LocatedNXParityBlock.exceptionControl) =
      locatedExceptionalEdges bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;>
        simp [LocatedNXParityBlock.exceptionControl,
          positionExceptionControlEdges, locatedExceptionalEdges, ih]

/-- The two analytic runs must remain separate: concatenating them and
feeding the result to `conditionedNXParityChainSum` would invent an edge
between the two outer endpoints. -/
structure AnchoredNXParityRuns {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) where
  left : List (NXParityBlock Nm mu)
  right : List (NXParityBlock Nm mu)

/-- Flatten the two runs only for block counting.  This list is a ledger,
not an analytic chain. -/
def AnchoredNXParityRuns.ledger {t : PlaneTree}
    {Nm : HeppMarking t} {mu : Multiplicities t}
    (runs : AnchoredNXParityRuns Nm mu) :
    List (NXParityBlock Nm mu) :=
  runs.left ++ runs.right

/-- The paper class runs on the two sides of an anchored word.  The left
run uses the reverse incoming edge; the right run uses the ordinary incoming
edge. -/
def finAnchorNXParityRunsWithPhases {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    AnchoredNXParityRuns Nm mu where
  left :=
    (pairPositionRun leftPhase (leftAnchorPositions anchor)).map
      (positionBlockToNXParityBlock Nm mu cls
        (positionIncomingSkipped O .reverse))
  right :=
    (pairPositionRun rightPhase (rightAnchorPositions anchor)).map
      (positionBlockToNXParityBlock Nm mu cls
        (positionIncomingSkipped O .forward))

/-- Equal-phase convenience wrapper.  The paper-facing parity constructor
below may instead use `finAnchorNXParityRunsWithPhases`, since reversal can
change the phase on the left run. -/
def finAnchorNXParityRuns {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    AnchoredNXParityRuns Nm mu :=
  finAnchorNXParityRunsWithPhases Nm mu phase phase anchor cls O

/-- Flattened raw-run ledger, used only for the finite block counts. -/
def finAnchorNXParityLedgerWithPhases {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    List (NXParityBlock Nm mu) :=
  (finAnchorNXParityRunsWithPhases Nm mu
    leftPhase rightPhase anchor cls O).ledger

def finAnchorNXParityLedger {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    List (NXParityBlock Nm mu) :=
  (finAnchorNXParityRuns Nm mu phase anchor cls O).ledger

/-- Raw parity ledger which retains the concrete original positions.  The
two directions use their respective incoming edges before the lists are
flattened for counting. -/
def finAnchorNXLocatedParityLedgerWithPhases {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    List (LocatedNXParityBlock (m := m) Nm mu) :=
  (pairPositionRun leftPhase (leftAnchorPositions anchor)).map
      (locatePositionBlock Nm mu cls
        (positionIncomingSkipped O .reverse)) ++
    (pairPositionRun rightPhase (rightAnchorPositions anchor)).map
      (locatePositionBlock Nm mu cls
        (positionIncomingSkipped O .forward))

theorem map_analyticBlock_finAnchorNXLocatedParityLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.analyticBlock =
      finAnchorNXParityLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O := by
  simp [finAnchorNXLocatedParityLedgerWithPhases,
    finAnchorNXParityLedgerWithPhases,
    finAnchorNXParityRunsWithPhases, AnchoredNXParityRuns.ledger,
    List.map_map, Function.comp_def]

theorem map_positionBlock_finAnchorNXLocatedParityLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.positionBlock =
      finAnchorPositionScheduleWithPhases
        leftPhase rightPhase anchor := by
  simp [finAnchorNXLocatedParityLedgerWithPhases,
    finAnchorPositionScheduleWithPhases,
    anchorPositionScheduleWithPhases,
    List.map_map, Function.comp_def]

private theorem pair_mem_leftAnchorPositions_descends
    {m : ℕ} (phase : Bool) (anchor i j : Fin m)
    (hpair :
      PositionBlock.pair i j ∈
        pairPositionRun phase (leftAnchorPositions anchor)) :
    j.1 + 1 = i.1 := by
  have hendpoints :=
    pairPositionRun_pair_endpoints_mem
      phase (leftAnchorPositions anchor) i j hpair
  have hi : i.1 < anchor.1 :=
    (mem_leftAnchorPositions_iff anchor i).mp hendpoints.1
  have hj : j.1 < anchor.1 :=
    (mem_leftAnchorPositions_iff anchor j).mp hendpoints.2
  have hmapped :
      PositionBlock.pair
          (anchorPositionOutwardOffset anchor i)
          (anchorPositionOutwardOffset anchor j) ∈
        pairPositionRun phase (List.range anchor.1) := by
    rw [← map_anchorPositionOutwardOffset_left,
      ← pairPositionRun_map]
    exact List.mem_map_of_mem hpair
  rw [List.range_eq_range'] at hmapped
  have hstep :=
    pair_mem_pairPositionRun_range'
      phase 0 anchor.1
        (anchorPositionOutwardOffset anchor i)
        (anchorPositionOutwardOffset anchor j) hmapped
  simp only [anchorPositionOutwardOffset,
    if_pos hi, if_pos hj] at hstep
  omega

private theorem pair_mem_rightAnchorPositions_ascends
    {m : ℕ} (phase : Bool) (anchor i j : Fin m)
    (hpair :
      PositionBlock.pair i j ∈
        pairPositionRun phase (rightAnchorPositions anchor)) :
    i.1 + 1 = j.1 := by
  have hendpoints :=
    pairPositionRun_pair_endpoints_mem
      phase (rightAnchorPositions anchor) i j hpair
  have hi : anchor.1 < i.1 :=
    (mem_rightAnchorPositions_iff anchor i).mp hendpoints.1
  have hj : anchor.1 < j.1 :=
    (mem_rightAnchorPositions_iff anchor j).mp hendpoints.2
  have hmapped :
      PositionBlock.pair
          (anchorPositionOutwardOffset anchor i)
          (anchorPositionOutwardOffset anchor j) ∈
        pairPositionRun phase
          (List.range (m - (anchor.1 + 1))) := by
    rw [← map_anchorPositionOutwardOffset_right,
      ← pairPositionRun_map]
    exact List.mem_map_of_mem hpair
  rw [List.range_eq_range'] at hmapped
  have hstep :=
    pair_mem_pairPositionRun_range'
      phase 0 (m - (anchor.1 + 1))
        (anchorPositionOutwardOffset anchor i)
        (anchorPositionOutwardOffset anchor j) hmapped
  simp only [anchorPositionOutwardOffset,
    if_neg (not_lt_of_ge (Nat.le_of_lt hi)),
    if_neg (not_lt_of_ge (Nat.le_of_lt hj))] at hstep
  omega

/-- A precise pair in the raw located ledger retains its exact class
payload, traversal side, direction, and incoming-skip bit. -/
private theorem precisePair_mem_finAnchorNXLocatedParityLedger_metadata
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m))
    (i j : Fin m) (p : NXPairBlock Nm mu)
    (hmem :
      LocatedNXParityBlock.pair i j p ∈
        finAnchorNXLocatedParityLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) :
    p.left = cls i ∧ p.right = cls j ∧
      ((i ∈ leftAnchorPositions anchor ∧
          j ∈ leftAnchorPositions anchor ∧
          j.1 + 1 = i.1 ∧
          p.skipRight =
            positionIncomingSkipped O .reverse j) ∨
        (i ∈ rightAnchorPositions anchor ∧
          j ∈ rightAnchorPositions anchor ∧
          i.1 + 1 = j.1 ∧
          p.skipRight =
            positionIncomingSkipped O .forward j)) := by
  rw [finAnchorNXLocatedParityLedgerWithPhases,
    List.mem_append] at hmem
  rcases hmem with hleft | hright
  · obtain ⟨b, hb, hbLocated⟩ := List.mem_map.mp hleft
    cases b with
    | single k =>
        simp [locatePositionBlock] at hbLocated
    | pair k l =>
        cases hbLocated
        have hendpoints :=
          pairPositionRun_pair_endpoints_mem
            leftPhase (leftAnchorPositions anchor) i j hb
        exact ⟨rfl, rfl, Or.inl
          ⟨hendpoints.1, hendpoints.2,
            pair_mem_leftAnchorPositions_descends
              leftPhase anchor i j hb, rfl⟩⟩
  · obtain ⟨b, hb, hbLocated⟩ := List.mem_map.mp hright
    cases b with
    | single k =>
        simp [locatePositionBlock] at hbLocated
    | pair k l =>
        cases hbLocated
        have hendpoints :=
          pairPositionRun_pair_endpoints_mem
            rightPhase (rightAnchorPositions anchor) i j hb
        exact ⟨rfl, rfl, Or.inr
          ⟨hendpoints.1, hendpoints.2,
            pair_mem_rightAnchorPositions_ascends
              rightPhase anchor i j hb, rfl⟩⟩

/-- The raw anchor ledger after erasing every analytic `(N,X)` class. -/
def finAnchorPositionExceptionControlLedgerWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    List (PositionExceptionControlBlock m) :=
  (pairPositionRun leftPhase (leftAnchorPositions anchor)).map
      (positionBlockToExceptionControl
        (positionIncomingSkipped O .reverse)) ++
    (pairPositionRun rightPhase (rightAnchorPositions anchor)).map
      (positionBlockToExceptionControl
        (positionIncomingSkipped O .forward))

theorem map_exceptionControl_finAnchorNXLocatedParityLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.exceptionControl =
      finAnchorPositionExceptionControlLedgerWithPhases
        leftPhase rightPhase anchor O := by
  simp [finAnchorNXLocatedParityLedgerWithPhases,
    finAnchorPositionExceptionControlLedgerWithPhases,
    List.map_map, Function.comp_def]

/-- Pure positional coarse ledger, including the global first-three rule. -/
def finAnchorPositionExceptionControlCoarseLedgerWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    List (PositionExceptionControlBlock m) :=
  markFirstSkippedPositionExceptionRough 3
    (finAnchorPositionExceptionControlLedgerWithPhases
      leftPhase rightPhase anchor O)

/-- Raw exceptional edges before restricting them to the selected phase. -/
def finAnchorPureRawExceptionalEdgesWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    Finset (AdjacentIndex m) :=
  positionExceptionControlEdges
    (finAnchorPositionExceptionControlCoarseLedgerWithPhases
      leftPhase rightPhase anchor O)

theorem finAnchorNXParityLedgerWithPhases_singleCount_le_four
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParitySingleCount
        (finAnchorNXParityLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) ≤ 4 := by
  rw [finAnchorNXParityLedgerWithPhases,
    AnchoredNXParityRuns.ledger, finAnchorNXParityRunsWithPhases,
    nxParitySingleCount_append,
    nxParitySingleCount_map_positionBlockToNXParityBlock,
    nxParitySingleCount_map_positionBlockToNXParityBlock]
  have hl :=
    positionSingleCount_pairPositionRun_le_two
      leftPhase (leftAnchorPositions anchor)
  have hr :=
    positionSingleCount_pairPositionRun_le_two
      rightPhase (rightAnchorPositions anchor)
  omega

theorem finAnchorNXParityLedger_singleCount_le_four
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParitySingleCount
        (finAnchorNXParityLedger Nm mu phase anchor cls O) ≤ 4 := by
  simpa [finAnchorNXParityLedger, finAnchorNXParityRuns,
    finAnchorNXParityLedgerWithPhases] using
    finAnchorNXParityLedgerWithPhases_singleCount_le_four
      Nm mu phase phase anchor cls O

theorem finAnchorNXParityLedgerWithPhases_roughPairCount_eq_zero
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParityRoughPairCount
        (finAnchorNXParityLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) = 0 := by
  rw [finAnchorNXParityLedgerWithPhases, AnchoredNXParityRuns.ledger,
    finAnchorNXParityRunsWithPhases,
    nxParityRoughPairCount_append,
    nxParityRoughPairCount_map_positionBlockToNXParityBlock,
    nxParityRoughPairCount_map_positionBlockToNXParityBlock]

theorem finAnchorNXParityLedger_roughPairCount_eq_zero
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParityRoughPairCount
        (finAnchorNXParityLedger Nm mu phase anchor cls O) = 0 := by
  simpa [finAnchorNXParityLedger, finAnchorNXParityRuns,
    finAnchorNXParityLedgerWithPhases] using
    finAnchorNXParityLedgerWithPhases_roughPairCount_eq_zero
      Nm mu phase phase anchor cls O

/-- Flattened coarse ledger: select the first three eligible pair blocks
(or all of them if fewer).  As above, this is not itself an analytic chain. -/
def finAnchorNXCoarseLedgerWithPhases {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    List (NXParityBlock Nm mu) :=
  markFirstSkippedPairsRough 3
    (finAnchorNXParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O)

def finAnchorNXCoarseLedger {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    List (NXParityBlock Nm mu) :=
  finAnchorNXCoarseLedgerWithPhases Nm mu
    phase phase anchor cls O

/-- Mark the first three eligible concrete pair blocks while retaining their
positions. -/
def finAnchorNXLocatedCoarseLedgerWithPhases {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    List (LocatedNXParityBlock (m := m) Nm mu) :=
  markFirstSkippedLocatedPairsRough 3
    (finAnchorNXLocatedParityLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O)

theorem map_analyticBlock_finAnchorNXLocatedCoarseLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.analyticBlock =
      finAnchorNXCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O := by
  rw [finAnchorNXLocatedCoarseLedgerWithPhases,
    map_analyticBlock_markFirstSkippedLocatedPairsRough,
    map_analyticBlock_finAnchorNXLocatedParityLedgerWithPhases]
  rfl

theorem map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.positionBlock =
      finAnchorPositionScheduleWithPhases
        leftPhase rightPhase anchor := by
  rw [finAnchorNXLocatedCoarseLedgerWithPhases,
    map_positionBlock_markFirstSkippedLocatedPairsRough,
    map_positionBlock_finAnchorNXLocatedParityLedgerWithPhases]

theorem map_exceptionControl_finAnchorNXLocatedCoarseLedgerWithPhases
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O).map
        LocatedNXParityBlock.exceptionControl =
      finAnchorPositionExceptionControlCoarseLedgerWithPhases
        leftPhase rightPhase anchor O := by
  rw [finAnchorNXLocatedCoarseLedgerWithPhases,
    map_exceptionControl_markFirstSkippedLocatedPairsRough,
    map_exceptionControl_finAnchorNXLocatedParityLedgerWithPhases]
  rfl

theorem locatedExceptionalEdges_finAnchorNXCoarse_eq_pure
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    locatedExceptionalEdges
        (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) =
      finAnchorPureRawExceptionalEdgesWithPhases
        leftPhase rightPhase anchor O := by
  unfold finAnchorPureRawExceptionalEdgesWithPhases
  rw [← positionExceptionControlEdges_map_exceptionControl,
    map_exceptionControl_finAnchorNXLocatedCoarseLedgerWithPhases]

/-- Rough marking changes estimates but neither loses nor duplicates a
position: the concrete coarse ledger contains exactly all non-anchor
positions. -/
theorem mem_flatten_positionBlocks_finAnchorNXLocatedCoarseLedger_iff
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor i : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    i ∈ ((finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O).map
          LocatedNXParityBlock.positionBlock).flatMap
            PositionBlock.entries ↔
      i ≠ anchor := by
  rw [map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
  exact mem_flatten_finAnchorPositionScheduleWithPhases_iff
    leftPhase rightPhase anchor i

/-- Split the marked ledger back into two analytic runs at the original left
run length.  `length_markFirstSkippedPairsRough` guarantees that no block is
lost; in particular the two runs are never concatenated analytically. -/
def finAnchorNXCoarseRunsWithPhases {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    AnchoredNXParityRuns Nm mu :=
  let raw := finAnchorNXParityRunsWithPhases Nm mu
    leftPhase rightPhase anchor cls O
  let marked := finAnchorNXCoarseLedgerWithPhases Nm mu
    leftPhase rightPhase anchor cls O
  { left := marked.take raw.left.length
    right := marked.drop raw.left.length }

def finAnchorNXCoarseRuns {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    AnchoredNXParityRuns Nm mu :=
  finAnchorNXCoarseRunsWithPhases Nm mu
    phase phase anchor cls O

theorem finAnchorNXCoarseRunsWithPhases_ledger
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXCoarseRunsWithPhases Nm mu
      leftPhase rightPhase anchor cls O).ledger =
      finAnchorNXCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O := by
  simp [finAnchorNXCoarseRunsWithPhases, AnchoredNXParityRuns.ledger,
    List.take_append_drop]

theorem finAnchorNXCoarseRuns_ledger
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXCoarseRuns Nm mu phase anchor cls O).ledger =
      finAnchorNXCoarseLedger Nm mu phase anchor cls O := by
  simpa [finAnchorNXCoarseRuns, finAnchorNXCoarseLedger] using
    finAnchorNXCoarseRunsWithPhases_ledger
      Nm mu phase phase anchor cls O

theorem finAnchorNXCoarseLedgerWithPhases_singleCount_le_four
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParitySingleCount
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) ≤ 4 := by
  rw [finAnchorNXCoarseLedgerWithPhases,
    nxParitySingleCount_markFirstSkippedPairsRough]
  exact finAnchorNXParityLedgerWithPhases_singleCount_le_four
    Nm mu leftPhase rightPhase anchor cls O

theorem finAnchorNXCoarseLedger_singleCount_le_four
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParitySingleCount
        (finAnchorNXCoarseLedger Nm mu phase anchor cls O) ≤ 4 := by
  simpa [finAnchorNXCoarseLedger] using
    finAnchorNXCoarseLedgerWithPhases_singleCount_le_four
      Nm mu phase phase anchor cls O

theorem finAnchorNXCoarseLedgerWithPhases_roughPairCount_le_three
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParityRoughPairCount
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) ≤ 3 := by
  calc
    nxParityRoughPairCount
        (finAnchorNXCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O) ≤
      nxParityRoughPairCount
          (finAnchorNXParityLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O) + 3 :=
      nxParityRoughPairCount_markFirstSkippedPairsRough_le 3 _
    _ = 3 := by
      rw [finAnchorNXParityLedgerWithPhases_roughPairCount_eq_zero]

theorem finAnchorNXCoarseLedger_roughPairCount_le_three
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    nxParityRoughPairCount
        (finAnchorNXCoarseLedger Nm mu phase anchor cls O) ≤ 3 := by
  simpa [finAnchorNXCoarseLedger] using
    finAnchorNXCoarseLedgerWithPhases_roughPairCount_le_three
      Nm mu phase phase anchor cls O

theorem finAnchorNXCoarseLedgerWithPhases_lossAtomBudget_le_twenty
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    positionLossAtomBudget
        (nxParitySingleCount
          (finAnchorNXCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O))
        (nxParityRoughPairCount
          (finAnchorNXCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O)) ≤ 20 :=
  positionLossAtomBudget_le_twenty
    (finAnchorNXCoarseLedgerWithPhases_singleCount_le_four
      Nm mu leftPhase rightPhase anchor cls O)
    (finAnchorNXCoarseLedgerWithPhases_roughPairCount_le_three
      Nm mu leftPhase rightPhase anchor cls O)

theorem finAnchorNXCoarseLedger_lossAtomBudget_le_twenty
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (phase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    positionLossAtomBudget
        (nxParitySingleCount
          (finAnchorNXCoarseLedger Nm mu phase anchor cls O))
        (nxParityRoughPairCount
          (finAnchorNXCoarseLedger Nm mu phase anchor cls O)) ≤ 20 := by
  simpa [finAnchorNXCoarseLedger] using
    finAnchorNXCoarseLedgerWithPhases_lossAtomBudget_le_twenty
      Nm mu phase phase anchor cls O

/--
The phase-matched exceptional set, defined solely from positions, phases,
and `O`.  Intersecting with the genuine carrier is essential: a local block
may be incident to an edge belonging to the opposite parity.
-/
def finAnchorPureExceptionalEdgesWithPhases {m : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (O : Finset (AdjacentIndex m)) :
    Finset (AdjacentIndex m) :=
  finAnchorPureRawExceptionalEdgesWithPhases
      leftPhase rightPhase anchor O ∩
    finAnchorPositionPhaseCarrierWithPhases
      leftPhase rightPhase anchor

/-- Compatibility wrapper for analytic schedules.  The class word is
deliberately ignored, so the exception set can be moved outside its sum. -/
def finAnchorNXExceptionalEdgesWithPhases {t : PlaneTree} {m : ℕ}
    (_Nm : HeppMarking t) (_mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (_cls : Fin m → ActiveNXClass _Nm _mu)
    (O : Finset (AdjacentIndex m)) :
    Finset (AdjacentIndex m) :=
  finAnchorPureExceptionalEdgesWithPhases
    leftPhase rightPhase anchor O

theorem positionPhase_exceptionalEdges_independent_cls
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls₁ cls₂ : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₁ O =
      finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₂ O :=
  rfl

theorem finAnchorNXExceptionalEdgesWithPhases_subset_carrier
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls O ⊆
      finAnchorPositionPhaseCarrierWithPhases
        leftPhase rightPhase anchor := by
  exact Finset.inter_subset_right

private theorem internal_adjacent_edge_mem_pair_affectedEdges
    {m : ℕ} (edge : AdjacentIndex m) (i j : Fin m)
    (horientation :
      (edge.1 = i ∧ i.1 + 1 = j.1) ∨
        (edge.1 = j ∧ j.1 + 1 = i.1)) :
    edge ∈ (PositionBlock.pair i j).affectedEdges := by
  rcases horientation with hright | hleft
  · rcases hright with ⟨heq, _hadj⟩
    subst i
    simp [PositionBlock.affectedEdges, positionIncidentEdges,
      reverseIncomingEdge, edge.2]
  · rcases hleft with ⟨heq, _hadj⟩
    subst j
    simp [PositionBlock.affectedEdges, positionIncidentEdges,
      reverseIncomingEdge, edge.2]

/--
Hard retained-edge interface for the position layer.  Every carrier edge
which is not charged to the explicit exceptional set is the internal edge
of a concrete *precise* coarse-ledger pair.  The conclusion also restores
the exact endpoint classes, the outward side and orientation, and the
incoming skip bit used by the local pair estimate.

Existence with full metadata is the interface needed by the analytic glue.
Uniqueness is deliberately not asserted here; it can be derived separately
from the no-duplication schedule invariant if a later consumer needs it.
-/
theorem finAnchorNX_retained_phaseCarrier_mem_precisePair
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m))
    (edge : AdjacentIndex m)
    (hcarrier :
      edge ∈ finAnchorPositionPhaseCarrierWithPhases
        leftPhase rightPhase anchor)
    (hnotExceptional :
      edge ∉ finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls O) :
    ∃ (i j : Fin m) (p : NXPairBlock Nm mu),
      LocatedNXParityBlock.pair i j p ∈
          finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O ∧
        p.left = cls i ∧
        p.right = cls j ∧
        ((i ∈ leftAnchorPositions anchor ∧
            j ∈ leftAnchorPositions anchor ∧
            edge.1 = j ∧
            j.1 + 1 = i.1 ∧
            p.skipRight = decide (edge ∈ O)) ∨
          (i ∈ rightAnchorPositions anchor ∧
            j ∈ rightAnchorPositions anchor ∧
            edge.1 = i ∧
            i.1 + 1 = j.1 ∧
            p.skipRight = decide (edge ∈ O))) := by
  let coarse :=
    finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
      leftPhase rightPhase anchor cls O
  have hnotRaw :
      edge ∉ finAnchorPureRawExceptionalEdgesWithPhases
        leftPhase rightPhase anchor O := by
    intro hraw
    apply hnotExceptional
    exact Finset.mem_inter.mpr ⟨hraw, hcarrier⟩
  have hnotLocated :
      edge ∉ locatedExceptionalEdges coarse := by
    rw [show coarse =
      finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
        leftPhase rightPhase anchor cls O by rfl,
      locatedExceptionalEdges_finAnchorNXCoarse_eq_pure]
    exact hnotRaw
  rcases finAnchorPositionPhaseCarrier_pair_or_single
      leftPhase rightPhase anchor edge hcarrier with
    hsingle | hpair
  · obtain ⟨i, hiSchedule, hedgeSingle⟩ := hsingle
    have hiMapped :
        PositionBlock.single i ∈
          coarse.map LocatedNXParityBlock.positionBlock := by
      rw [show coarse =
        finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O by rfl,
        map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
      exact hiSchedule
    obtain ⟨b, hbCoarse, hbPosition⟩ :=
      List.mem_map.mp hiMapped
    cases b with
    | pair k l p =>
        simp [LocatedNXParityBlock.positionBlock] at hbPosition
    | roughPair k l p =>
        simp [LocatedNXParityBlock.positionBlock] at hbPosition
    | single k a skipped =>
        simp only [LocatedNXParityBlock.positionBlock,
          PositionBlock.single.injEq] at hbPosition
        subst k
        exact False.elim (hnotLocated
          (mem_locatedExceptionalEdges_of_single_mem
            coarse i a skipped edge hbCoarse hedgeSingle))
  · obtain ⟨i, j, hijSchedule, horientation⟩ := hpair
    have hedgePair :
        edge ∈ (PositionBlock.pair i j).affectedEdges :=
      internal_adjacent_edge_mem_pair_affectedEdges
        edge i j horientation
    have hijMapped :
        PositionBlock.pair i j ∈
          coarse.map LocatedNXParityBlock.positionBlock := by
      rw [show coarse =
        finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
          leftPhase rightPhase anchor cls O by rfl,
        map_positionBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
      exact hijSchedule
    obtain ⟨b, hbCoarse, hbPosition⟩ :=
      List.mem_map.mp hijMapped
    cases b with
    | single k a skipped =>
        simp [LocatedNXParityBlock.positionBlock] at hbPosition
    | roughPair k l p =>
        simp only [LocatedNXParityBlock.positionBlock,
          PositionBlock.pair.injEq] at hbPosition
        rcases hbPosition with ⟨rfl, rfl⟩
        exact False.elim (hnotLocated
          (mem_locatedExceptionalEdges_of_roughPair_mem
            coarse k l p edge hbCoarse hedgePair))
    | pair k l p =>
        simp only [LocatedNXParityBlock.positionBlock,
          PositionBlock.pair.injEq] at hbPosition
        rcases hbPosition with ⟨rfl, rfl⟩
        have hraw :
            LocatedNXParityBlock.pair k l p ∈
              finAnchorNXLocatedParityLedgerWithPhases Nm mu
                leftPhase rightPhase anchor cls O := by
          apply
            precisePair_mem_of_mem_markFirstSkippedLocatedPairsRough
              3
              (finAnchorNXLocatedParityLedgerWithPhases Nm mu
                leftPhase rightPhase anchor cls O)
              k l p
          simpa [coarse,
            finAnchorNXLocatedCoarseLedgerWithPhases] using hbCoarse
        obtain ⟨hpLeft, hpRight, hside⟩ :=
          precisePair_mem_finAnchorNXLocatedParityLedger_metadata
            Nm mu leftPhase rightPhase anchor cls O k l p hraw
        refine ⟨k, l, p, ?_, hpLeft, hpRight, ?_⟩
        · simpa [coarse] using hbCoarse
        · rcases hside with hleft | hright
          · obtain ⟨hiLeft, hjLeft, hdescend, hskip⟩ := hleft
            have hedgeLeft : edge.1 = l := by
              rcases horientation with hforward | hreverse
              · omega
              · exact hreverse.1
            left
            refine ⟨hiLeft, hjLeft, hedgeLeft,
              hdescend, ?_⟩
            rw [hskip]
            have hreverse :
                reverseIncomingEdge l = some edge := by
              unfold reverseIncomingEdge
              rw [dif_pos (by omega)]
              congr 2
              exact hedgeLeft.symm
            simp [positionIncomingSkipped, hreverse]
          · obtain ⟨hiRight, hjRight, hascend, hskip⟩ := hright
            have hedgeRight : edge.1 = k := by
              rcases horientation with hforward | hreverse
              · exact hforward.1
              · omega
            right
            refine ⟨hiRight, hjRight, hedgeRight,
              hascend, ?_⟩
            rw [hskip]
            have hforward :
                forwardIncomingEdge l = some edge := by
              unfold forwardIncomingEdge
              rw [dif_pos (by omega)]
              congr 2
              apply Fin.ext
              change l.1 - 1 = edge.1.1
              omega
            simp [positionIncomingSkipped, hforward]

/-- Fully concrete version of the paper's “at most 20 skipped gains” audit.
Each member of the finset is an original adjacency incident to a single or
rough pair block; the cardinality bound follows from `4` single blocks and
`3` rough pair blocks, with costs `2` and `4` respectively. -/
theorem card_finAnchorNXExceptionalEdgesWithPhases_le_twenty
    {t : PlaneTree} {m : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin m)
    (cls : Fin m → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex m)) :
    (finAnchorNXExceptionalEdgesWithPhases Nm mu
      leftPhase rightPhase anchor cls O).card ≤ 20 := by
  calc
    (finAnchorNXExceptionalEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls O).card ≤
      positionLossAtomBudget
        (nxParitySingleCount
          ((finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O).map
              LocatedNXParityBlock.analyticBlock))
        (nxParityRoughPairCount
          ((finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O).map
              LocatedNXParityBlock.analyticBlock)) := by
      calc
        (finAnchorNXExceptionalEdgesWithPhases Nm mu
            leftPhase rightPhase anchor cls O).card ≤
            (finAnchorPureRawExceptionalEdgesWithPhases
              leftPhase rightPhase anchor O).card := by
          exact Finset.card_le_card Finset.inter_subset_left
        _ =
            (locatedExceptionalEdges
              (finAnchorNXLocatedCoarseLedgerWithPhases Nm mu
                leftPhase rightPhase anchor cls O)).card := by
          rw [locatedExceptionalEdges_finAnchorNXCoarse_eq_pure]
        _ ≤ _ :=
          card_locatedExceptionalEdges_le_lossAtomBudget _
    _ = positionLossAtomBudget
        (nxParitySingleCount
          (finAnchorNXCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O))
        (nxParityRoughPairCount
          (finAnchorNXCoarseLedgerWithPhases Nm mu
            leftPhase rightPhase anchor cls O)) := by
      rw [map_analyticBlock_finAnchorNXLocatedCoarseLedgerWithPhases]
    _ ≤ 20 :=
      finAnchorNXCoarseLedgerWithPhases_lossAtomBudget_le_twenty
        Nm mu leftPhase rightPhase anchor cls O

/-! ### Reindexing the concrete exceptions into the anchored sequence bound -/

/-- The zero-based paper adjacency indices of a word of length `n+1` are
canonically `Fin n`. -/
def adjacentIndexSuccEquiv (n : ℕ) :
    AdjacentIndex (n + 1) ≃ Fin n where
  toFun j := ⟨j.1.1, by omega⟩
  invFun j :=
    { val := ⟨j.1, j.2.trans (Nat.lt_succ_self n)⟩
      property := Nat.add_lt_add_right j.2 1 }
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv j := by
    apply Fin.ext
    rfl

/-- Reindex an original adjacency exception set for the sequence lemmas. -/
def reindexAdjacentExceptions {n : ℕ}
    (E : Finset (AdjacentIndex (n + 1))) : Finset (Fin n) :=
  E.map (adjacentIndexSuccEquiv n).toEmbedding

@[simp] theorem card_reindexAdjacentExceptions {n : ℕ}
    (E : Finset (AdjacentIndex (n + 1))) :
    (reindexAdjacentExceptions E).card = E.card := by
  simp [reindexAdjacentExceptions]

/-- The phase carrier in the `Fin n` coordinates used by sequence bounds. -/
def finAnchorPositionPhaseFinCarrierWithPhases {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    Finset (Fin n) :=
  reindexAdjacentExceptions
    (finAnchorPositionPhaseCarrierWithPhases
      leftPhase rightPhase anchor)

theorem finAnchorPositionPhaseFinCarrier_union_flip {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    finAnchorPositionPhaseFinCarrierWithPhases
        leftPhase rightPhase anchor ∪
      finAnchorPositionPhaseFinCarrierWithPhases
        (!leftPhase) (!rightPhase) anchor =
      Finset.univ := by
  unfold finAnchorPositionPhaseFinCarrierWithPhases
    reindexAdjacentExceptions
  rw [← Finset.map_union,
    finAnchorPositionPhaseCarrier_union_flip]
  exact Finset.map_univ_equiv (adjacentIndexSuccEquiv n)

theorem finAnchorPositionPhaseFinCarrier_disjoint_flip {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1)) :
    Disjoint
      (finAnchorPositionPhaseFinCarrierWithPhases
        leftPhase rightPhase anchor)
      (finAnchorPositionPhaseFinCarrierWithPhases
        (!leftPhase) (!rightPhase) anchor) := by
  unfold finAnchorPositionPhaseFinCarrierWithPhases
    reindexAdjacentExceptions
  rw [Finset.disjoint_map]
  exact finAnchorPositionPhaseCarrier_disjoint_flip
    leftPhase rightPhase anchor

/-- The anchored sequence estimate remains uniform when the exceptional set
depends on the anchor position.  This is the form required here because the
one-variable boundary blocks move with the minimal-scale position. -/
theorem anchoredBidirectional_code_sum_le_varyingExceptions
    (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n ν : ℕ) (e : Fin ν → ℤ),
        ν ≤ n + 1 → Function.Injective e →
        ∀ E : Fin (n + 1) → Finset (Fin n),
          (∀ anchor, (E anchor).card ≤ B) →
          ∑ anchor : Fin (n + 1),
            ∑ w : Fin (n + 1) → Fin ν,
              anchoredBidirectionalCodeWeight θ e
                (E anchor) anchor w
            ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hfixed⟩ :=
    anchoredBidirectional_code_fixedAnchor_sum_le θ hθ B
  refine ⟨2 * C, by nlinarith, ?_⟩
  intro n ν e hν he E hE
  have hM :
      ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast Nat.le_of_lt (n + 1).lt_two_pow_self
  calc
    (∑ anchor : Fin (n + 1),
        ∑ w : Fin (n + 1) → Fin ν,
          anchoredBidirectionalCodeWeight θ e
            (E anchor) anchor w) ≤
        ∑ _anchor : Fin (n + 1), C ^ (n + 1) :=
      Finset.sum_le_sum fun anchor _ =>
        hfixed n ν e hν he (E anchor) (hE anchor) anchor
    _ = ((n + 1 : ℕ) : ℝ) * C ^ (n + 1) := by simp
    _ ≤ (2 : ℝ) ^ (n + 1) * C ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hM
        (pow_nonneg (le_trans zero_le_one hC) _)
    _ = (2 * C) ^ (n + 1) := by rw [mul_pow]

/-- Pure positional exception set in the sequence theorem's coordinates. -/
def finAnchorPureExceptionalFinEdgesWithPhases {n : ℕ}
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (O : Finset (AdjacentIndex (n + 1))) :
    Finset (Fin n) :=
  reindexAdjacentExceptions
    (finAnchorPureExceptionalEdgesWithPhases
      leftPhase rightPhase anchor O)

/-- Compatibility wrapper for the analytic class schedule. -/
def finAnchorNXExceptionalFinEdgesWithPhases
    {t : PlaneTree} {n : ℕ}
    (_Nm : HeppMarking t) (_mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (_cls : Fin (n + 1) → ActiveNXClass _Nm _mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    Finset (Fin n) :=
  finAnchorPureExceptionalFinEdgesWithPhases
    leftPhase rightPhase anchor O

theorem positionPhase_exceptionalFinEdges_independent_cls
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls₁ cls₂ : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXExceptionalFinEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₁ O =
      finAnchorNXExceptionalFinEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls₂ O :=
  rfl

theorem finAnchorNXExceptionalFinEdgesWithPhases_subset_carrier
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXExceptionalFinEdgesWithPhases Nm mu
        leftPhase rightPhase anchor cls O ⊆
      finAnchorPositionPhaseFinCarrierWithPhases
        leftPhase rightPhase anchor := by
  unfold finAnchorNXExceptionalFinEdgesWithPhases
    finAnchorPureExceptionalFinEdgesWithPhases
    finAnchorPositionPhaseFinCarrierWithPhases
    reindexAdjacentExceptions
  exact Finset.map_subset_map.mpr
    (finAnchorNXExceptionalEdgesWithPhases_subset_carrier
      Nm mu leftPhase rightPhase anchor cls O)

theorem card_finAnchorNXExceptionalFinEdgesWithPhases_le_twenty
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    (finAnchorNXExceptionalFinEdgesWithPhases Nm mu
      leftPhase rightPhase anchor cls O).card ≤ 20 := by
  rw [finAnchorNXExceptionalFinEdgesWithPhases,
    finAnchorPureExceptionalFinEdgesWithPhases,
    card_reindexAdjacentExceptions]
  exact card_finAnchorNXExceptionalEdgesWithPhases_le_twenty
    Nm mu leftPhase rightPhase anchor cls O

/-- Union of a phase's exceptions with those of its genuine flipped phase. -/
def finAnchorNXInterpolatedExceptionalFinEdges
    {t : PlaneTree} {n : ℕ}
    (_Nm : HeppMarking t) (_mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (_cls : Fin (n + 1) → ActiveNXClass _Nm _mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    Finset (Fin n) :=
  finAnchorPureExceptionalFinEdgesWithPhases
      leftPhase rightPhase anchor O ∪
    finAnchorPureExceptionalFinEdgesWithPhases
      (!leftPhase) (!rightPhase) anchor O

theorem positionPhase_interpolatedExceptionalFinEdges_independent_cls
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls₁ cls₂ : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    finAnchorNXInterpolatedExceptionalFinEdges Nm mu
        leftPhase rightPhase anchor cls₁ O =
      finAnchorNXInterpolatedExceptionalFinEdges Nm mu
        leftPhase rightPhase anchor cls₂ O :=
  rfl

theorem card_finAnchorNXInterpolatedExceptionalFinEdges_le_forty
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool)
    (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1))) :
    (finAnchorNXInterpolatedExceptionalFinEdges Nm mu
      leftPhase rightPhase anchor cls O).card ≤ 40 := by
  unfold finAnchorNXInterpolatedExceptionalFinEdges
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add
      (card_finAnchorNXExceptionalFinEdgesWithPhases_le_twenty
        Nm mu leftPhase rightPhase anchor cls O)
      (card_finAnchorNXExceptionalFinEdgesWithPhases_le_twenty
        Nm mu (!leftPhase) (!rightPhase) anchor cls O))

/--
Exact interpolation of the two complementary phase carriers.  This is the
concrete instantiation of `sqrt_even_mul_odd_gain_eq_sixteenth`; neither the
partition nor exception containment is left as an assumption.
-/
theorem finAnchorNX_sqrt_phase_gain_eq_sixteenth
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1)))
    (ratio : Fin n → ℝ)
    (hratio : ∀ j, 0 ≤ ratio j) :
    Real.sqrt
        ((∏ j ∈
            finAnchorPositionPhaseFinCarrierWithPhases
                leftPhase rightPhase anchor \
              finAnchorNXExceptionalFinEdgesWithPhases Nm mu
                leftPhase rightPhase anchor cls O,
            ratioGain (1 / 8 : ℝ) (ratio j)) *
          ∏ j ∈
            finAnchorPositionPhaseFinCarrierWithPhases
                (!leftPhase) (!rightPhase) anchor \
              finAnchorNXExceptionalFinEdgesWithPhases Nm mu
                (!leftPhase) (!rightPhase) anchor cls O,
            ratioGain (1 / 8 : ℝ) (ratio j)) =
      ∏ j ∈ Finset.univ \
          finAnchorNXInterpolatedExceptionalFinEdges Nm mu
            leftPhase rightPhase anchor cls O,
        ratioGain (1 / 16 : ℝ) (ratio j) := by
  exact sqrt_even_mul_odd_gain_eq_sixteenth
    Finset.univ
    (finAnchorPositionPhaseFinCarrierWithPhases
      leftPhase rightPhase anchor)
    (finAnchorPositionPhaseFinCarrierWithPhases
      (!leftPhase) (!rightPhase) anchor)
    (finAnchorNXExceptionalFinEdgesWithPhases Nm mu
      leftPhase rightPhase anchor cls O)
    (finAnchorNXExceptionalFinEdgesWithPhases Nm mu
      (!leftPhase) (!rightPhase) anchor cls O)
    (finAnchorPositionPhaseFinCarrier_union_flip
      leftPhase rightPhase anchor)
    (finAnchorPositionPhaseFinCarrier_disjoint_flip
      leftPhase rightPhase anchor)
    (finAnchorNXExceptionalFinEdgesWithPhases_subset_carrier
      Nm mu leftPhase rightPhase anchor cls O)
    (finAnchorNXExceptionalFinEdgesWithPhases_subset_carrier
      Nm mu (!leftPhase) (!rightPhase) anchor cls O)
    ratio (fun j _ => hratio j)

/--
Concrete geometric-mean bridge for the two complementary local estimates.
Once the same nonnegative quantity is bounded by each retained `1/8`
phase product, it is bounded by the common `1/16` target with the union of
their positional exceptions.
-/
theorem finAnchorNX_two_phase_gain_bounds_le_sixteenth
    {t : PlaneTree} {n : ℕ}
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (leftPhase rightPhase : Bool) (anchor : Fin (n + 1))
    (cls : Fin (n + 1) → ActiveNXClass Nm mu)
    (O : Finset (AdjacentIndex (n + 1)))
    (ratio : Fin n → ℝ)
    (hratio : ∀ j, 0 ≤ ratio j)
    (x : ℝ) (hx : 0 ≤ x)
    (hphase :
      x ≤
        ∏ j ∈
          finAnchorPositionPhaseFinCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalFinEdgesWithPhases Nm mu
              leftPhase rightPhase anchor cls O,
          ratioGain (1 / 8 : ℝ) (ratio j))
    (hflip :
      x ≤
        ∏ j ∈
          finAnchorPositionPhaseFinCarrierWithPhases
              (!leftPhase) (!rightPhase) anchor \
            finAnchorNXExceptionalFinEdgesWithPhases Nm mu
              (!leftPhase) (!rightPhase) anchor cls O,
          ratioGain (1 / 8 : ℝ) (ratio j)) :
    x ≤
      ∏ j ∈ Finset.univ \
          finAnchorNXInterpolatedExceptionalFinEdges Nm mu
            leftPhase rightPhase anchor cls O,
        ratioGain (1 / 16 : ℝ) (ratio j) := by
  have hphaseNonneg :
      0 ≤
        ∏ j ∈
          finAnchorPositionPhaseFinCarrierWithPhases
              leftPhase rightPhase anchor \
            finAnchorNXExceptionalFinEdgesWithPhases Nm mu
              leftPhase rightPhase anchor cls O,
          ratioGain (1 / 8 : ℝ) (ratio j) := by
    exact Finset.prod_nonneg fun j _ =>
      ratioGain_nonneg _ (hratio j)
  have hflipNonneg :
      0 ≤
        ∏ j ∈
          finAnchorPositionPhaseFinCarrierWithPhases
              (!leftPhase) (!rightPhase) anchor \
            finAnchorNXExceptionalFinEdgesWithPhases Nm mu
              (!leftPhase) (!rightPhase) anchor cls O,
          ratioGain (1 / 8 : ℝ) (ratio j) := by
    exact Finset.prod_nonneg fun j _ =>
      ratioGain_nonneg _ (hratio j)
  calc
    x ≤ Real.sqrt
        ((∏ j ∈
            finAnchorPositionPhaseFinCarrierWithPhases
                leftPhase rightPhase anchor \
              finAnchorNXExceptionalFinEdgesWithPhases Nm mu
                leftPhase rightPhase anchor cls O,
            ratioGain (1 / 8 : ℝ) (ratio j)) *
          ∏ j ∈
            finAnchorPositionPhaseFinCarrierWithPhases
                (!leftPhase) (!rightPhase) anchor \
              finAnchorNXExceptionalFinEdgesWithPhases Nm mu
                (!leftPhase) (!rightPhase) anchor cls O,
            ratioGain (1 / 8 : ℝ) (ratio j)) :=
      le_geometricMean_of_le_both
        hx hphaseNonneg hflipNonneg hphase hflip
    _ =
        ∏ j ∈ Finset.univ \
            finAnchorNXInterpolatedExceptionalFinEdges Nm mu
              leftPhase rightPhase anchor cls O,
          ratioGain (1 / 16 : ℝ) (ratio j) :=
      finAnchorNX_sqrt_phase_gain_eq_sixteenth
        Nm mu leftPhase rightPhase anchor cls O ratio hratio

/-- Paper-facing `1/16` gain bound after even/odd interpolation.  The
exception set is the union of the two concrete one-parity sets and therefore
has budget `40`.  This exponent is unrelated to the Step-3 outer exponent
`1/20`. -/
theorem finAnchorNX_sixteenth_positionGain_sum_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n ν : ℕ) (e : Fin ν → ℤ),
        ν ≤ n + 1 → Function.Injective e →
        ∀ {t : PlaneTree}
          (Nm : HeppMarking t) (mu : Multiplicities t)
          (leftPhase rightPhase : Fin (n + 1) → Bool)
          (cls : Fin (n + 1) → ActiveNXClass Nm mu)
          (O : Finset (AdjacentIndex (n + 1))),
          ∑ anchor : Fin (n + 1),
            ∑ w : Fin (n + 1) → Fin ν,
              anchoredBidirectionalCodeWeight (1 / 16 : ℝ) e
                (finAnchorNXInterpolatedExceptionalFinEdges Nm mu
                  (leftPhase anchor) (rightPhase anchor)
                  anchor cls O)
                anchor w
            ≤ C ^ (n + 1) := by
  obtain ⟨C, hC, hbound⟩ :=
    anchoredBidirectional_code_sum_le_varyingExceptions
      (1 / 16 : ℝ) (by norm_num) 40
  refine ⟨C, hC, ?_⟩
  intro n ν e hν he t Nm mu leftPhase rightPhase cls O
  apply hbound n ν e hν he
    (fun anchor =>
      finAnchorNXInterpolatedExceptionalFinEdges Nm mu
        (leftPhase anchor) (rightPhase anchor)
        anchor cls O)
  intro anchor
  exact card_finAnchorNXInterpolatedExceptionalFinEdges_le_forty
    Nm mu
    (leftPhase anchor) (rightPhase anchor)
    anchor cls O

/-! ## Shared anchor and used-copy state -/

/-- The used set at the moment the two sides start: it contains the single
distinguished labeled copy.  Both side eliminations must extend this same
set, rather than using two independent copies of the anchor. -/
def arrangementAnchorUsedCopies {t : PlaneTree} {mu : Multiplicities t}
    {M : ℕ} (σ : Fin M ≃ HeppLabeledCopy mu) (anchor : Fin M) :
    Finset (HeppLabeledCopy mu) :=
  arrangementUsedCopies σ {anchor}

@[simp] theorem arrangementAnchorUsedCopies_eq_singleton
    {t : PlaneTree} {mu : Multiplicities t}
    {M : ℕ} (σ : Fin M ≃ HeppLabeledCopy mu) (anchor : Fin M) :
    arrangementAnchorUsedCopies σ anchor = {σ anchor} := by
  simp [arrangementAnchorUsedCopies, arrangementUsedCopies]

/-- Every non-anchor position is an honest conditioned choice when the
shared used set initially contains the anchor. -/
theorem arrangement_nonanchor_mem_conditionedNX
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {M : ℕ}
    (σ : Fin M ≃ HeppLabeledCopy mu) (anchor j : Fin M)
    (hj : j ≠ anchor) (a : NXClass)
    (ha : singleScaleSigma1 Nm mu (σ j).1 = a) :
    σ j ∈ conditionedCopiesAtNX Nm mu
      (arrangementAnchorUsedCopies σ anchor) a := by
  apply arrangement_copy_mem_conditionedNX
    Nm mu σ {anchor} (by simp [hj]) a ha

/-- Choices on opposite sides of the cut remain distinct after the first
one is inserted into the common used set.  This is the anchor/cross-side
bookkeeping required by the global finite-Fubini step. -/
theorem arrangement_crossSide_pair_mem_conditionedNX
    {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) {M : ℕ}
    (σ : Fin M ≃ HeppLabeledCopy mu) (anchor j k : Fin M)
    (hj : j ≠ anchor) (hk : k ≠ anchor) (hjk : j ≠ k)
    (a b : NXClass)
    (ha : singleScaleSigma1 Nm mu (σ j).1 = a)
    (hb : singleScaleSigma1 Nm mu (σ k).1 = b) :
    σ j ∈ conditionedCopiesAtNX Nm mu
        (arrangementAnchorUsedCopies σ anchor) a ∧
      σ k ∈ conditionedCopiesAtNX Nm mu
        (insert (σ j) (arrangementAnchorUsedCopies σ anchor)) b := by
  exact arrangement_pair_mem_conditionedNX
    Nm mu σ {anchor} (by simp [hj]) (by simp [hk]) hjk a b ha hb

/-- Both outward analytic runs may be fed to the mixed one-parity local
estimate with the *same* anchored used-copy state and anchored lattice point.
The theorem gives separate bounds; their product is obtained through the
arrangement/Fubini lemma without duplicating the anchor or introducing an edge
between the outer endpoints. -/
theorem
    finAnchorNXCoarseRunsWithPhases_sharedAnchor_le_targetProducts :
    ∃ C : ℝ, 256 ≤ C ∧
      ∀ {t : PlaneTree} {m : ℕ}
        (ht : t.isValid = true) (hroot : rootV t ∈ BranchNodes t)
        (Nm : HeppMarking t) (mu : Multiplicities t)
        (z : HeppLeaf t → Fin 4 → ℤ) (hz : IsSeparatedEmbedding Nm z)
        (R : ℕ), accumulatedScale Nm mu (rootV t) ≤ R →
        ∀ (leftPhase rightPhase : Bool) (anchor : Fin m)
          (cls : Fin m → ActiveNXClass Nm mu)
          (O : Finset (AdjacentIndex m))
          (σ : Fin m ≃ HeppLabeledCopy mu),
          conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
              (finAnchorNXCoarseRunsWithPhases Nm mu
                leftPhase rightPhase anchor cls O).left
              (arrangementAnchorUsedCopies σ anchor)
              (labeledCopyPoint z (σ anchor)) ≤
            ((finAnchorNXCoarseRunsWithPhases Nm mu
                leftPhase rightPhase anchor cls O).left.map fun p =>
              C * nxParityBlockTarget Nm mu (R : ℝ) p).prod ∧
          conditionedNXParityChainSum ht hroot Nm mu z hz (R : ℝ)
              (finAnchorNXCoarseRunsWithPhases Nm mu
                leftPhase rightPhase anchor cls O).right
              (arrangementAnchorUsedCopies σ anchor)
              (labeledCopyPoint z (σ anchor)) ≤
            ((finAnchorNXCoarseRunsWithPhases Nm mu
                leftPhase rightPhase anchor cls O).right.map fun p =>
              C * nxParityBlockTarget Nm mu (R : ℝ) p).prod := by
  obtain ⟨C, hC, hchain⟩ :=
    conditionedNXParityChainSum_le_targetProduct
  refine ⟨C, hC, ?_⟩
  intro t m ht hroot Nm mu z hz R hR
    leftPhase rightPhase anchor cls O σ
  constructor
  · exact hchain ht hroot Nm mu z hz R hR
      (finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).left
      (arrangementAnchorUsedCopies σ anchor)
      (labeledCopyPoint z (σ anchor))
  · exact hchain ht hroot Nm mu z hz R hR
      (finAnchorNXCoarseRunsWithPhases Nm mu
        leftPhase rightPhase anchor cls O).right
      (arrangementAnchorUsedCopies σ anchor)
      (labeledCopyPoint z (σ anchor))

/-! ## Bidirectional gain interface -/

/-- One dyadic gain on an enumerated class family. -/
noncomputable def positionCodeGain {ν : ℕ}
    (e : Fin ν → ℤ) (a b : Fin ν) : ℝ :=
  min 1 (((2 : ℝ) ^ e b / (2 : ℝ) ^ e a) ^ (1 / 8 : ℝ))

theorem positionCodeGain_nonneg {ν : ℕ}
    (e : Fin ν → ℤ) (a b : Fin ν) :
    0 ≤ positionCodeGain e a b := by
  unfold positionCodeGain
  exact le_min zero_le_one
    (Real.rpow_nonneg (div_nonneg (zpow_nonneg (by norm_num) _)
      (zpow_nonneg (by norm_num) _)) _)

/-- Gain product on one side, with the side word ordered *away* from the
anchor.  For the left side this is the reverse of original word order; for
the right side it is the original order. -/
def anchoredSideCodeWord {ν k : ℕ}
    (anchor : Fin ν) (x : Fin k → Fin ν) : Fin (k + 1) → Fin ν :=
  Fin.cons anchor x

noncomputable def anchoredSideCodeGain {ν k : ℕ}
    (e : Fin ν → ℤ) (anchor : Fin ν) (x : Fin k → Fin ν) : ℝ :=
  ∏ j : Fin k,
    positionCodeGain e
      (anchoredSideCodeWord anchor x j.castSucc)
      (anchoredSideCodeWord anchor x j.succ)

theorem anchoredSideCodeGain_nonneg {ν k : ℕ}
    (e : Fin ν → ℤ) (anchor : Fin ν) (x : Fin k → Fin ν) :
    0 ≤ anchoredSideCodeGain e anchor x := by
  unfold anchoredSideCodeGain
  exact Finset.prod_nonneg fun j _ => positionCodeGain_nonneg e _ _

/-- Sum over all class words on one side of a fixed anchor class. -/
noncomputable def anchoredSideCodeSum {ν : ℕ}
    (e : Fin ν → ℤ) (k : ℕ) (anchor : Fin ν) : ℝ :=
  ∑ x : Fin k → Fin ν, anchoredSideCodeGain e anchor x

theorem anchoredSideCodeSum_nonneg {ν : ℕ}
    (e : Fin ν → ℤ) (k : ℕ) (anchor : Fin ν) :
    0 ≤ anchoredSideCodeSum e k anchor := by
  unfold anchoredSideCodeSum
  exact Finset.sum_nonneg fun x _ =>
    anchoredSideCodeGain_nonneg e anchor x

/-- The gain sum prescribed by the paper's "going left and right
separately": both words are ordered away from the common anchor.  Thus the
left product uses original-order reverse gains and the right product uses
original-order forward gains. -/
noncomputable def anchoredBidirectionalCodeSum {ν : ℕ}
    (e : Fin ν → ℤ) (leftLength rightLength : ℕ) : ℝ :=
  ∑ anchor : Fin ν,
    anchoredSideCodeSum e leftLength anchor *
      anchoredSideCodeSum e rightLength anchor

/-- Once the two padded one-sided applications of Lemma 5.13 are available,
the sum over the at-most-`M` anchor classes costs only another `2^M`.
This is the global replacement for the invalid pointwise comparison between
forward and reverse gains. -/
theorem anchoredBidirectionalCodeSum_le_of_side_bounds
    {ν : ℕ} (e : Fin ν → ℤ) (leftLength rightLength M : ℕ)
    (hν : ν ≤ M) (C : ℝ) (hC : 0 ≤ C)
    (hleft : ∀ anchor : Fin ν,
      anchoredSideCodeSum e leftLength anchor ≤ C ^ M)
    (hright : ∀ anchor : Fin ν,
      anchoredSideCodeSum e rightLength anchor ≤ C ^ M) :
    anchoredBidirectionalCodeSum e leftLength rightLength ≤
      (2 * C ^ 2) ^ M := by
  have hpow : 0 ≤ C ^ M := pow_nonneg hC M
  have hνpow : (ν : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast hν.trans Nat.lt_two_pow_self.le
  calc
    anchoredBidirectionalCodeSum e leftLength rightLength ≤
        ∑ _anchor : Fin ν, (C ^ M) * (C ^ M) := by
      unfold anchoredBidirectionalCodeSum
      exact Finset.sum_le_sum fun anchor _ =>
        mul_le_mul (hleft anchor) (hright anchor)
          (anchoredSideCodeSum_nonneg e _ anchor) hpow
    _ = (ν : ℝ) * ((C ^ M) * (C ^ M)) := by
      simp
    _ ≤ (2 : ℝ) ^ M * ((C ^ M) * (C ^ M)) :=
      mul_le_mul_of_nonneg_right hνpow
        (mul_nonneg hpow hpow)
    _ = (2 * C ^ 2) ^ M := by
      simp only [mul_pow, pow_two]

/-!
## Exact cross-module boundary

This file now closes the position layer itself:

* independent left/right phases, the concrete cut at every anchor, and exact
  coverage of all non-anchor positions;
* position-preserving rough marking, at most four single blocks and three
  rough pairs, and the exact original adjacency edges affected by them;
* at most `20` exceptional gains per parity and at most `40` after even/odd
  interpolation;
* exact conversion of heterogeneous rough targets to the common (5.87)
  baseline, with all `sqrt Y` and `Xi⁻¹` atoms exposed and the resulting
  polynomial loss absorbed exponentially;
* the shared anchored used-copy state and separate local target-product
  bounds for the two outward analytic runs;
* the padded bidirectional sequence estimate, specialized to the concrete
  anchor-dependent exception sets at exponent `1/8`, and to their even/odd
  union at exponent `1/16`.

`SingleScaleAnchorGlue` and the final P-5.10 assembly use these positional
facts to:

* identify (or nonnegatively dominate) the fixed-anchor arrangement fiber by
  the two outward conditioned eliminations while threading one genuinely
  shared `used` set through both sides;
* reindex the products of `nxParityBlockTarget` into the final common
  (5.87) product, combine the even/odd estimates by geometric mean, and
  connect the active `P` word to the code-word sequence sum;
* combine the explicit rough scale gains with `R^(2s)` and
  `(N_root/R)^(min(2s,3))`, then reinsert the finite-Fubini and factorial
  ledgers at the frozen proposition boundary.

The statement-weight-to-local-kernel inequalities in the first item
live in `SingleScaleWeightBridge`.  No pointwise comparison between original
forward and traversal-forward gains is valid or assumed; the left run is
handled globally by reversal, as in `SingleScaleAnchoredSequence`.
-/

end XYCluster
end
end Anderson4D
