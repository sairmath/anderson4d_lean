import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticBlockIndependence
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticGreenSkeleton
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticScheduleGeometry

/-!
# Factoring the first analytic R-322 block

The analytic schedule places an innermost primitive block at its head.  This
file makes the first pointwise separation needed by the collapse induction:

* later difference factors only read coordinates outside the head block;
* an unreplaced chain edge whose two vertices avoid the head block is likewise
  independent of the head variables;
* the head difference is the literal difference of the two endpoint kernels
  with their common, external successor;
* consequently the generalized signed Green skeleton factors into a local
  head part and an outer part which is constant in all head-block variables.

The chain family is kept heterogeneous.  Thus the statement remains usable
after earlier primitive blocks have already been replaced by collapsed
kernels; no free-Green specialization is hidden in the induction interface.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-! ## Generalized analytic skeleton -/

/-- Left vertex of an internal `J` chain edge. -/
def r322JChainEdgeLeft {n : ℕ}
    (e : Fin (n - 1)) : Fin n :=
  ⟨e.val, by
    have he := e.isLt
    omega⟩

/-- Right vertex of an internal `J` chain edge. -/
def r322JChainEdgeRight {n : ℕ}
    (e : Fin (n - 1)) : Fin n :=
  ⟨e.val + 1, by
    have he := e.isLt
    omega⟩

/-- A chain edge is exterior to a block when both of its coordinate reads are
outside the block. -/
def R322ChainEdgeOutside {n : ℕ}
    (B : Finset (Fin n)) (e : Fin (n - 1)) : Prop :=
  r322JChainEdgeLeft e ∉ B ∧
    r322JChainEdgeRight e ∉ B

instance {n : ℕ} (B : Finset (Fin n)) (e : Fin (n - 1)) :
    Decidable (R322ChainEdgeOutside B e) := by
  unfold R322ChainEdgeOutside
  infer_instance

/-- One generalized chain factor, with analytically scheduled right edges
removed exactly as in the closed `J` formula. -/
def r322AnalyticChainEdgeFactorWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (x : Fin n → T4) (e : Fin (n - 1)) : ℝ :=
  if e.val ∈
      ((r322AnalyticSchedule κ).map
        (fun s => s.1.2.val)) then
    1
  else
    jChainEdgeWith G x e

/-- Product of all generalized, unreplaced chain edges. -/
def r322AnalyticChainProductWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (x : Fin n → T4) : ℝ :=
  ∏ e : Fin (n - 1),
    r322AnalyticChainEdgeFactorWith G κ x e

/-- Difference-factor product for an arbitrary suffix of the analytic
schedule. -/
def r322AnalyticDiffProductWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (steps : List (R322ExtractionStep n))
    (x : Fin n → T4) : ℝ :=
  (steps.map (fun t => diffFactorJWith G x t.1)).prod

/-- The closed analytic skeleton with heterogeneous chain inputs. -/
def r322AnalyticSkeletonWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (x : Fin n → T4) : ℝ :=
  r322AnalyticChainProductWith G κ x *
    r322AnalyticDiffProductWith G
      (r322AnalyticSchedule κ) x

/-- At the constant Green family, the generalized skeleton is the frozen
analytic Green skeleton. -/
theorem r322AnalyticSkeletonWith_green_eq
    {n : ℕ} (κ : PartialPairing (Fin n))
    (x : Fin n → T4) :
    r322AnalyticSkeletonWith
        (fun _ : Fin (n - 1) => greenFn) κ x =
      r322AnalyticGreenSkeleton κ x := by
  have hchain :
      r322AnalyticChainProductWith
          (fun _ : Fin (n - 1) => greenFn) κ x =
        ∏ e : Fin (n - 1),
          if e.val ∈
              ((r322AnalyticSchedule κ).map
                (fun s => s.1.2.val)) then
            1
          else if h : e.val + 1 < n then
            greenFn
              (x ⟨e.val, by omega⟩ -
                x ⟨e.val + 1, h⟩)
          else
            1 := by
    unfold r322AnalyticChainProductWith
    apply Finset.prod_congr rfl
    intro e _he
    have hguard : e.val + 1 < n := by
      have he := e.isLt
      omega
    by_cases hm :
        e.val ∈
          ((r322AnalyticSchedule κ).map
            (fun s => s.1.2.val))
    · simp only [r322AnalyticChainEdgeFactorWith,
        hm, if_true]
    · simp only [r322AnalyticChainEdgeFactorWith,
        hm, if_false, hguard]
      unfold jChainEdgeWith
      rfl
  have hdiff :
      r322AnalyticDiffProductWith
          (fun _ : Fin (n - 1) => greenFn)
          (r322AnalyticSchedule κ) x =
        ((r322AnalyticSchedule κ).map
          (fun s => diffFactorJ x s.1)).prod := by
    unfold r322AnalyticDiffProductWith
    apply congrArg List.prod
    apply List.map_congr_left
    intro s _hs
    exact diffFactorJWith_green x s.1
  unfold r322AnalyticSkeletonWith
    r322AnalyticGreenSkeleton
  rw [hchain, hdiff]

/-! ## Coordinate independence of the two outer ingredients -/

/-- A generalized chain edge whose two vertices avoid the head block is
unchanged when only head-block coordinates move. -/
theorem jChainEdgeWith_eq_of_eq_outside_analyticHeadBlock
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (x y : Fin n → T4)
    (s : R322ExtractionStep n)
    (e : Fin (n - 1))
    (he : R322ChainEdgeOutside s.2 e)
    (hxy : ∀ i, i ∉ s.2 → x i = y i) :
    jChainEdgeWith G x e =
      jChainEdgeWith G y e := by
  unfold jChainEdgeWith
  change
    G e
        (x (r322JChainEdgeLeft e) -
          x (r322JChainEdgeRight e)) =
      G e
        (y (r322JChainEdgeLeft e) -
          y (r322JChainEdgeRight e))
  rw [hxy (r322JChainEdgeLeft e) he.1,
    hxy (r322JChainEdgeRight e) he.2]

/-- In particular, an unreplaced exterior analytic chain factor is
head-coordinate independent. -/
theorem r322AnalyticUnreplacedChainEdgeFactor_eq
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (x y : Fin n → T4)
    (s : R322ExtractionStep n)
    (e : Fin (n - 1))
    (he : R322ChainEdgeOutside s.2 e)
    (hunreplaced :
      e.val ∉
        ((r322AnalyticSchedule κ).map
          (fun t => t.1.2.val)))
    (hxy : ∀ i, i ∉ s.2 → x i = y i) :
    r322AnalyticChainEdgeFactorWith G κ x e =
      r322AnalyticChainEdgeFactorWith G κ y e := by
  simp only [r322AnalyticChainEdgeFactorWith,
    hunreplaced, if_false]
  exact
    jChainEdgeWith_eq_of_eq_outside_analyticHeadBlock
      G x y s e he hxy

/-- The whole product of later analytic differences is independent of the
head-block variables. -/
theorem r322AnalyticTailDiffProductWith_eq
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (x y : Fin n → T4)
    (s : R322ExtractionStep n)
    (tail : List (R322ExtractionStep n))
    (hschedule :
      r322AnalyticSchedule κ = s :: tail)
    (hxy : ∀ i, i ∉ s.2 → x i = y i) :
    r322AnalyticDiffProductWith G tail x =
      r322AnalyticDiffProductWith G tail y := by
  have hs :
      ExtractionPairBlockAligned s.1 s.2 := by
    apply r322AnalyticSchedule_forall_aligned κ s
    rw [hschedule]
    simp
  unfold r322AnalyticDiffProductWith
  apply congrArg List.prod
  apply List.map_congr_left
  intro t ht
  have ht' :
      ExtractionPairBlockAligned t.1 t.2 := by
    apply r322AnalyticSchedule_forall_aligned κ t
    rw [hschedule]
    simp [ht]
  have hrel :
      s.1.2 < t.1.1 ∨
        (t.1.1 < s.1.1 ∧ s.1.2 < t.1.2) :=
    r322AnalyticSchedule_head_later_right_or_contains
      κ hschedule ht
  exact
    diffFactorJWith_eq_of_eq_outside_analyticHeadBlock
      G x y s t hs ht' hrel hxy

/-! ## Local/outer chain split -/

/-- Chain factors touching the head block.  Replaced edges remain literal
ones, so this is an exact factor of the closed skeleton. -/
def r322AnalyticHeadLocalChainProductWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (s : R322ExtractionStep n)
    (x : Fin n → T4) : ℝ :=
  ∏ e : Fin (n - 1),
    if R322ChainEdgeOutside s.2 e then
      1
    else
      r322AnalyticChainEdgeFactorWith G κ x e

/-- Chain factors whose two vertices both avoid the head block. -/
def r322AnalyticHeadOuterChainProductWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (s : R322ExtractionStep n)
    (x : Fin n → T4) : ℝ :=
  ∏ e : Fin (n - 1),
    if R322ChainEdgeOutside s.2 e then
      r322AnalyticChainEdgeFactorWith G κ x e
    else
      1

/-- The full generalized chain product is the product of the touching and
exterior parts. -/
theorem r322AnalyticChainProductWith_eq_local_mul_outer
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (s : R322ExtractionStep n)
    (x : Fin n → T4) :
    r322AnalyticChainProductWith G κ x =
      r322AnalyticHeadLocalChainProductWith G κ s x *
        r322AnalyticHeadOuterChainProductWith G κ s x := by
  unfold r322AnalyticChainProductWith
    r322AnalyticHeadLocalChainProductWith
    r322AnalyticHeadOuterChainProductWith
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _he
  by_cases hout : R322ChainEdgeOutside s.2 e
  · simp only [hout, if_true, one_mul]
  · simp only [hout, if_false, mul_one]

/-- The exterior chain product is independent of all head-block
coordinates, whether an exterior edge is replaced or unreplaced. -/
theorem r322AnalyticHeadOuterChainProductWith_eq
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (x y : Fin n → T4)
    (s : R322ExtractionStep n)
    (hxy : ∀ i, i ∉ s.2 → x i = y i) :
    r322AnalyticHeadOuterChainProductWith G κ s x =
      r322AnalyticHeadOuterChainProductWith G κ s y := by
  unfold r322AnalyticHeadOuterChainProductWith
  apply Finset.prod_congr rfl
  intro e _he
  by_cases hout : R322ChainEdgeOutside s.2 e
  · simp only [hout, if_true]
    unfold r322AnalyticChainEdgeFactorWith
    split
    · rfl
    · exact
        jChainEdgeWith_eq_of_eq_outside_analyticHeadBlock
          G x y s e hout hxy
  · simp only [hout, if_false]

/-! ## The explicit head difference -/

/-- In the proper guarded case, the head difference is exactly the
difference of the two endpoint kernels evaluated against their common
successor.  The successor is outside the head block. -/
theorem r322AnalyticHead_diffFactorJWith_eq
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (x : Fin n → T4)
    (s : R322ExtractionStep n)
    (hs : ExtractionPairBlockAligned s.1 s.2)
    (hguard : s.1.2.val + 1 < n) :
    (⟨s.1.2.val + 1, hguard⟩ : Fin n) ∉ s.2 ∧
      diffFactorJWith G x s.1 =
        G ⟨s.1.2.val, by omega⟩
            (x s.1.2 -
              x ⟨s.1.2.val + 1, hguard⟩) -
          G ⟨s.1.2.val, by omega⟩
            (x s.1.1 -
              x ⟨s.1.2.val + 1, hguard⟩) := by
  constructor
  · exact
      r322AnalyticHead_rightSucc_not_mem_headBlock
        s hs hguard
  · unfold diffFactorJWith
    simp only [hguard, dite_true]

/-! ## Pointwise head factorization -/

/-- The local part: every chain edge touching the head block and the signed
head endpoint difference. -/
def r322AnalyticHeadLocalFactorWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (s : R322ExtractionStep n)
    (x : Fin n → T4) : ℝ :=
  r322AnalyticHeadLocalChainProductWith G κ s x *
    diffFactorJWith G x s.1

/-- The outer part: all fully exterior chain edges and all later analytic
differences. -/
def r322AnalyticHeadOuterFactorWith
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (s : R322ExtractionStep n)
    (tail : List (R322ExtractionStep n))
    (x : Fin n → T4) : ℝ :=
  r322AnalyticHeadOuterChainProductWith G κ s x *
    r322AnalyticDiffProductWith G tail x

/-- Exact pointwise local/outer factorization of the generalized skeleton at
the head of the analytic schedule. -/
theorem r322AnalyticSkeletonWith_eq_headLocal_mul_outer
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (s : R322ExtractionStep n)
    (tail : List (R322ExtractionStep n))
    (x : Fin n → T4)
    (hschedule :
      r322AnalyticSchedule κ = s :: tail) :
    r322AnalyticSkeletonWith G κ x =
      r322AnalyticHeadLocalFactorWith G κ s x *
        r322AnalyticHeadOuterFactorWith
          G κ s tail x := by
  unfold r322AnalyticSkeletonWith
    r322AnalyticHeadLocalFactorWith
    r322AnalyticHeadOuterFactorWith
    r322AnalyticDiffProductWith
  rw [r322AnalyticChainProductWith_eq_local_mul_outer,
    hschedule]
  simp only [List.map_cons, List.prod_cons]
  ring

/-- The outer factor in the exact split is constant in all head-block
variables. -/
theorem r322AnalyticHeadOuterFactorWith_eq
    {n : ℕ} (G : Fin (n - 1) → T4 → ℝ)
    (κ : PartialPairing (Fin n))
    (x y : Fin n → T4)
    (s : R322ExtractionStep n)
    (tail : List (R322ExtractionStep n))
    (hschedule :
      r322AnalyticSchedule κ = s :: tail)
    (hxy : ∀ i, i ∉ s.2 → x i = y i) :
    r322AnalyticHeadOuterFactorWith G κ s tail x =
      r322AnalyticHeadOuterFactorWith G κ s tail y := by
  unfold r322AnalyticHeadOuterFactorWith
  rw [r322AnalyticHeadOuterChainProductWith_eq
      G κ x y s hxy,
    r322AnalyticTailDiffProductWith_eq
      G κ x y s tail hschedule hxy]

/-- Free-Green form of the exact pointwise factorization, connected to the
public analytic skeleton. -/
theorem r322AnalyticGreenSkeleton_eq_headLocal_mul_outer
    {n : ℕ} (κ : PartialPairing (Fin n))
    (s : R322ExtractionStep n)
    (tail : List (R322ExtractionStep n))
    (x : Fin n → T4)
    (hschedule :
      r322AnalyticSchedule κ = s :: tail) :
    r322AnalyticGreenSkeleton κ x =
      r322AnalyticHeadLocalFactorWith
          (fun _ : Fin (n - 1) => greenFn)
          κ s x *
        r322AnalyticHeadOuterFactorWith
          (fun _ : Fin (n - 1) => greenFn)
          κ s tail x := by
  rw [← r322AnalyticSkeletonWith_green_eq κ x]
  exact
    r322AnalyticSkeletonWith_eq_headLocal_mul_outer
      (fun _ : Fin (n - 1) => greenFn)
      κ s tail x hschedule

end

end Anderson4D
