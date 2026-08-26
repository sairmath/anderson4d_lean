import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointAggregate
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFiber

/-!
# Endpoint-first factorization of refined R-324 fibres

This file connects the abstract four-leg Fourier calculation in
`R324EndpointAggregate` to the actual closed deterministic profiles.
The first and last chain edges are removed from each renormalized Green
skeleton, leaving a core which depends only on the internal variables.

The construction is deliberately pointwise and exact.  In particular, a
whole refined primitive-pairing/configuration fibre may be placed in the
internal core before the four external variables are integrated.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Endpoint-independent chain edges -/

private theorem assemble_eq_zeroEndpoints_of_internal
    {m : ℕ} (x y : T4) (v : Fin m → T4)
    (j : Fin (m + 2))
    (hj0 : j.val ≠ 0) (hjlast : j.val ≠ m + 1) :
    assemble x y v j = assemble 0 0 v j := by
  simp only [assemble, dif_neg hj0, dif_neg hjlast]

theorem zero_not_mem_extractedRightEdges
    {m : ℕ} (κ : PartialPairing (Fin m)) :
    (0 : Fin (m + 1)) ∉ extractedRightEdges κ := by
  intro hzero
  obtain ⟨p, _hp, hedge⟩ :=
    exists_extractedPairOfRightEdge κ 0 hzero
  have hval := congrArg Fin.val hedge
  simp only [extractedRightEdge_val, Fin.val_zero] at hval
  omega

private theorem extractedShortcutParent_pos
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) (hi : i ∈ extractedRightEdges κ) :
    0 < (extractedShortcutParent κ i hi).val := by
  unfold extractedShortcutParent
  simp only
  omega

private theorem extractedShortcutParent_cast_internal
    {m : ℕ} (κ : PartialPairing (Fin m))
    (i : Fin (m + 1)) (hi : i ∈ extractedRightEdges κ) :
    (Fin.castLE (by omega)
      (extractedShortcutParent κ i hi) :
        Fin (m + 2)).val ≠ 0 ∧
      (Fin.castLE (by omega)
        (extractedShortcutParent κ i hi) :
          Fin (m + 2)).val ≠ m + 1 := by
  constructor
  · exact Nat.ne_of_gt (extractedShortcutParent_pos κ i hi)
  · have hle :
        (extractedShortcutParent κ i hi).val ≤ i.val := by
      exact Nat.lt_succ_iff.mp
        (extractedShortcutParent κ i hi).isLt
    have hiLt := i.isLt
    simp only [Fin.castLE]
    omega

/-- A nonendpoint edge of the uniform difference product is independent
of both external variables. -/
theorem expandedGreenDifferenceFactor_eq_zeroEndpoints
    {m : ℕ} (κ : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4)
    (i : Fin (m + 1))
    (hi0 : i ≠ 0) (hilast : i ≠ Fin.last m) :
    originalGreenEdge (assemble x y v) i -
        extractedShortcutGreenEdge κ (assemble x y v) i =
      originalGreenEdge (assemble 0 0 v) i -
        extractedShortcutGreenEdge κ (assemble 0 0 v) i := by
  have hiVal0 : i.val ≠ 0 := by
    intro h
    apply hi0
    apply Fin.ext
    simpa using h
  have hiValLast : i.val ≠ m := by
    intro h
    apply hilast
    apply Fin.ext
    simpa using h
  have hparent :
      assemble x y v i.castSucc =
        assemble 0 0 v i.castSucc := by
    apply assemble_eq_zeroEndpoints_of_internal
    · simpa using hiVal0
    · change i.val ≠ m + 1
      omega
  have hchild :
      assemble x y v i.succ =
        assemble 0 0 v i.succ := by
    apply assemble_eq_zeroEndpoints_of_internal
    · change i.val + 1 ≠ 0
      omega
    · change i.val + 1 ≠ m + 1
      omega
  have horiginal :
      originalGreenEdge (assemble x y v) i =
        originalGreenEdge (assemble 0 0 v) i := by
    unfold originalGreenEdge
    rw [hparent, hchild]
  have hshortcut :
      extractedShortcutGreenEdge κ (assemble x y v) i =
        extractedShortcutGreenEdge κ (assemble 0 0 v) i := by
    unfold extractedShortcutGreenEdge
    split_ifs with hi
    · have hp :=
        extractedShortcutParent_cast_internal κ i hi
      rw [
        assemble_eq_zeroEndpoints_of_internal
          x y v _ hp.1 hp.2,
        hchild]
    · rfl
  rw [horiginal, hshortcut]

/-- Internal difference-product core after deleting the two external
chain edges. -/
def r324RenormalizedInteriorCore
    {m : ℕ} (κ : PartialPairing (Fin m))
    (v : Fin m → T4) : ℂ :=
  ∏ i ∈
      (((Finset.univ : Finset (Fin (m + 1))).erase 0).erase
        (Fin.last m)),
      (originalGreenEdge (assemble 0 0 v) i -
        extractedShortcutGreenEdge κ (assemble 0 0 v) i)

/-! ## Exact first/last edge factorization -/

/-- Internal anchor of the incoming external leg. -/
def r324IncomingAnchor
    {m : ℕ} (_hm : 0 < m) (v : Fin m → T4) : T4 :=
  assemble 0 0 v (0 : Fin (m + 1)).succ

/-- Ordinary internal anchor of the outgoing external leg. -/
def r324OutgoingAnchor
    {m : ℕ} (_hm : 0 < m) (v : Fin m → T4) : T4 :=
  assemble 0 0 v (Fin.last m).castSucc

/-- Whether the final chain edge was replaced by an extracted endpoint
difference. -/
def r324OutgoingIsShortcut
    {m : ℕ} (κ : PartialPairing (Fin m)) : Bool :=
  decide (Fin.last m ∈ extractedRightEdges κ)

/-- The subtraction anchor of the outgoing leg.  In the ordinary branch
its value is irrelevant and is set to zero. -/
def r324OutgoingShortcutAnchor
    {m : ℕ} (κ : PartialPairing (Fin m))
    (v : Fin m → T4) : T4 :=
  if h : Fin.last m ∈ extractedRightEdges κ then
    assemble 0 0 v
      (Fin.castLE (by omega)
        (extractedShortcutParent κ (Fin.last m) h))
  else 0

theorem expandedGreenDifferenceFactor_zero
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4) :
    originalGreenEdge (assemble x y v) 0 -
        extractedShortcutGreenEdge κ (assemble x y v) 0 =
      r324IncomingEndpointKernel
        (r324IncomingAnchor hm v)
        (r324IncomingAnchor hm v) false x := by
  have hchild :
      assemble x y v (0 : Fin (m + 1)).succ =
        r324IncomingAnchor hm v := by
    unfold r324IncomingAnchor
    apply assemble_eq_zeroEndpoints_of_internal
    · change (0 : ℕ) + 1 ≠ 0
      omega
    · change (0 : ℕ) + 1 ≠ m + 1
      omega
  have hparent :
      assemble x y v (0 : Fin (m + 1)).castSucc = x := by
    rw [show (0 : Fin (m + 1)).castSucc =
        (0 : Fin (m + 2)) by
      apply Fin.ext
      rfl]
    exact assemble_zero x y v
  unfold originalGreenEdge
    extractedShortcutGreenEdge
    r324IncomingEndpointKernel
  rw [dif_neg (zero_not_mem_extractedRightEdges κ),
    hparent, hchild]
  simp

theorem expandedGreenDifferenceFactor_last
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4) :
    originalGreenEdge (assemble x y v) (Fin.last m) -
        extractedShortcutGreenEdge κ
          (assemble x y v) (Fin.last m) =
      r324OutgoingEndpointKernel
        (r324OutgoingAnchor hm v)
        (r324OutgoingShortcutAnchor κ v)
        (r324OutgoingIsShortcut κ) y := by
  have hparent :
      assemble x y v (Fin.last m).castSucc =
        r324OutgoingAnchor hm v := by
    unfold r324OutgoingAnchor
    apply assemble_eq_zeroEndpoints_of_internal
    · change m ≠ 0
      omega
    · change m ≠ m + 1
      omega
  have hchild :
      assemble x y v (Fin.last m).succ = y := by
    rw [show (Fin.last m).succ = Fin.last (m + 1) by
      apply Fin.ext
      rfl]
    exact assemble_last x y v
  by_cases hlast :
      Fin.last m ∈ extractedRightEdges κ
  · have hp :=
      extractedShortcutParent_cast_internal
        κ (Fin.last m) hlast
    have hshortcut :
        assemble x y v
            (Fin.castLE (by omega)
              (extractedShortcutParent κ
                (Fin.last m) hlast)) =
          r324OutgoingShortcutAnchor κ v := by
      unfold r324OutgoingShortcutAnchor
      rw [dif_pos hlast]
      exact assemble_eq_zeroEndpoints_of_internal
        x y v _ hp.1 hp.2
    unfold originalGreenEdge
      extractedShortcutGreenEdge
      r324OutgoingEndpointKernel
      r324OutgoingIsShortcut
    rw [dif_pos hlast, if_pos (by
      simpa only [decide_eq_true_eq] using hlast),
      hparent, hchild, hshortcut]
  · unfold originalGreenEdge
      extractedShortcutGreenEdge
      r324OutgoingEndpointKernel
      r324OutgoingIsShortcut
    rw [dif_neg hlast, if_neg (by
      simpa only [decide_eq_true_eq] using hlast),
      hparent, hchild]

/-- Exact product decomposition of a renormalized profile into its two
external legs and an endpoint-independent internal core. -/
theorem renormalizedGreenSkeleton_eq_endpointKernels_mul_core
    {m : ℕ} (hm : 0 < m)
    (κ : PartialPairing (Fin m))
    (x y : T4) (v : Fin m → T4) :
    renormalizedGreenSkeleton κ (assemble x y v) =
      r324IncomingEndpointKernel
          (r324IncomingAnchor hm v)
          (r324IncomingAnchor hm v) false x *
        r324OutgoingEndpointKernel
          (r324OutgoingAnchor hm v)
          (r324OutgoingShortcutAnchor κ v)
          (r324OutgoingIsShortcut κ) y *
        r324RenormalizedInteriorCore κ v := by
  rw [renormalizedGreenSkeleton_eq_differenceProduct]
  unfold expandedGreenDifferenceProduct
  let F : Fin (m + 1) → ℂ := fun i =>
    originalGreenEdge (assemble x y v) i -
      extractedShortcutGreenEdge κ (assemble x y v) i
  have hlastNeZero : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  have hlastMem :
      Fin.last m ∈
        (Finset.univ : Finset (Fin (m + 1))).erase 0 := by
    simp [hlastNeZero]
  have hsplitZero :=
    Finset.mul_prod_erase
      (Finset.univ : Finset (Fin (m + 1))) F
      (Finset.mem_univ (0 : Fin (m + 1)))
  have hsplitLast :=
    Finset.mul_prod_erase
      ((Finset.univ : Finset (Fin (m + 1))).erase 0) F
      hlastMem
  have hmiddle :
      (∏ i ∈
          ((Finset.univ : Finset (Fin (m + 1))).erase 0).erase
            (Fin.last m), F i) =
        r324RenormalizedInteriorCore κ v := by
    unfold r324RenormalizedInteriorCore
    apply Finset.prod_congr rfl
    intro i hi
    have hi0 : i ≠ 0 := by
      exact (Finset.mem_erase.mp
        (Finset.mem_erase.mp hi).2).1
    have hilast : i ≠ Fin.last m :=
      (Finset.mem_erase.mp hi).1
    exact expandedGreenDifferenceFactor_eq_zeroEndpoints
      κ x y v i hi0 hilast
  change (∏ i : Fin (m + 1), F i) = _
  calc
    (∏ i : Fin (m + 1), F i) =
        F 0 *
          (∏ i ∈
            (Finset.univ :
              Finset (Fin (m + 1))).erase 0, F i) :=
      hsplitZero.symm
    _ = F 0 *
        (F (Fin.last m) *
          ∏ i ∈
            ((Finset.univ :
              Finset (Fin (m + 1))).erase 0).erase
                (Fin.last m), F i) := by
      rw [hsplitLast]
    _ =
      r324IncomingEndpointKernel
          (r324IncomingAnchor hm v)
          (r324IncomingAnchor hm v) false x *
        r324OutgoingEndpointKernel
          (r324OutgoingAnchor hm v)
          (r324OutgoingShortcutAnchor κ v)
          (r324OutgoingIsShortcut κ) y *
        r324RenormalizedInteriorCore κ v := by
      dsimp only [F]
      rw [expandedGreenDifferenceFactor_zero hm κ x y v,
        expandedGreenDifferenceFactor_last hm κ x y v,
        hmiddle]
      ring

/-! ## A whole refined fibre as one endpoint-separated integrand -/

/-- The four concrete pairs of endpoint anchors attached to a contraction
representative, in `(x,y,z,w)` order. -/
def r324ContractionEndpointAnchors
    {m : ℕ} (hm : 0 < m) (e : MomentContraction m)
    (v : Fin (2 * m) → T4) : R324EndpointAnchors :=
  let vl : Fin m → T4 := fun i => v (leftMomentIndex i)
  let vr : Fin m → T4 := fun i => v (rightMomentIndex i)
  ![
    (r324IncomingAnchor hm vl,
      r324IncomingAnchor hm vl),
    (r324OutgoingAnchor hm vl,
      r324OutgoingShortcutAnchor e.1 vl),
    (r324IncomingAnchor hm vr,
      r324IncomingAnchor hm vr),
    (r324OutgoingAnchor hm vr,
      r324OutgoingShortcutAnchor e.2.1 vr)
  ]

/-- Only the outgoing endpoint of either copy can be replaced by an
extracted difference. -/
def r324ContractionEndpointFlags
    {m : ℕ} (e : MomentContraction m) : R324EndpointFlags :=
  ![
    false,
    r324OutgoingIsShortcut e.1,
    false,
    r324OutgoingIsShortcut e.2.1
  ]

@[simp]
theorem r324ContractionEndpointAnchors_zero
    {m : ℕ} (hm : 0 < m) (e : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    r324ContractionEndpointAnchors hm e v 0 =
      (r324IncomingAnchor hm
          (fun i => v (leftMomentIndex i)),
        r324IncomingAnchor hm
          (fun i => v (leftMomentIndex i))) :=
  rfl

@[simp]
theorem r324ContractionEndpointAnchors_one
    {m : ℕ} (hm : 0 < m) (e : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    r324ContractionEndpointAnchors hm e v 1 =
      (r324OutgoingAnchor hm
          (fun i => v (leftMomentIndex i)),
        r324OutgoingShortcutAnchor e.1
          (fun i => v (leftMomentIndex i))) :=
  rfl

@[simp]
theorem r324ContractionEndpointAnchors_two
    {m : ℕ} (hm : 0 < m) (e : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    r324ContractionEndpointAnchors hm e v 2 =
      (r324IncomingAnchor hm
          (fun i => v (rightMomentIndex i)),
        r324IncomingAnchor hm
          (fun i => v (rightMomentIndex i))) :=
  rfl

@[simp]
theorem r324ContractionEndpointAnchors_three
    {m : ℕ} (hm : 0 < m) (e : MomentContraction m)
    (v : Fin (2 * m) → T4) :
    r324ContractionEndpointAnchors hm e v 3 =
      (r324OutgoingAnchor hm
          (fun i => v (rightMomentIndex i)),
        r324OutgoingShortcutAnchor e.2.1
          (fun i => v (rightMomentIndex i))) :=
  rfl

@[simp]
theorem r324ContractionEndpointFlags_zero
    {m : ℕ} (e : MomentContraction m) :
    r324ContractionEndpointFlags e 0 = false :=
  rfl

@[simp]
theorem r324ContractionEndpointFlags_one
    {m : ℕ} (e : MomentContraction m) :
    r324ContractionEndpointFlags e 1 =
      r324OutgoingIsShortcut e.1 :=
  rfl

@[simp]
theorem r324ContractionEndpointFlags_two
    {m : ℕ} (e : MomentContraction m) :
    r324ContractionEndpointFlags e 2 = false :=
  rfl

@[simp]
theorem r324ContractionEndpointFlags_three
    {m : ℕ} (e : MomentContraction m) :
    r324ContractionEndpointFlags e 3 =
      r324OutgoingIsShortcut e.2.1 :=
  rfl

/-- Internal core of one refined fibre.  Crucially, the complete
primitive-pairing fibre sum remains inside this core. -/
def r324RefinedEndpointCore
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (v : Fin (2 * m) → T4) : ℂ :=
  r324RenormalizedInteriorCore e₀.1
      (fun i => v (leftMomentIndex i)) *
    r324RenormalizedInteriorCore e₀.2.1
      (fun i => v (rightMomentIndex i)) *
    ∑ e ∈ momentRefinedContractionFiber m s r,
      (primitiveCovarianceProduct ρ ε m
        (momentCombinedPairing e.1 e.2.1 e.2.2) v : ℂ)

/-- Exact endpoint-separated form of an entire residual-refined physical
fibre.  The finite primitive-pairing sum is formed before any endpoint
Fourier integration or norm. -/
theorem momentRefinedPhysicalIntegrand_eq_endpointSeparated
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4)
    (s r :
      Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentContractionFiber m s)
    (x y z w : T4) (v : Fin (2 * m) → T4) :
    momentRefinedPhysicalIntegrand
        ρ ε m α β s r x y z w v =
      r324EndpointSeparatedIntegrand α β
        (r324ContractionEndpointAnchors hm e₀ v)
        (r324ContractionEndpointFlags e₀)
        (r324RefinedEndpointCore ρ ε m s r e₀ v)
        x y z w := by
  rw [
    momentRefinedPhysicalIntegrand_eq_commonSkeletons_mul_sum_covariance
      ρ ε m α β s r e₀ he₀ x y z w v,
    renormalizedGreenSkeleton_eq_endpointKernels_mul_core
      hm e₀.1 x y (fun i => v (leftMomentIndex i)),
    renormalizedGreenSkeleton_eq_endpointKernels_mul_core
      hm e₀.2.1 z w (fun i => v (rightMomentIndex i))]
  unfold momentFourierPhase
    r324EndpointSeparatedIntegrand
    r324RefinedEndpointCore
  simp only [r324ContractionEndpointAnchors_zero,
    r324ContractionEndpointAnchors_one,
    r324ContractionEndpointAnchors_two,
    r324ContractionEndpointAnchors_three,
    r324ContractionEndpointFlags_zero,
    r324ContractionEndpointFlags_one,
    r324ContractionEndpointFlags_two,
    r324ContractionEndpointFlags_three]
  ring

end

end Anderson4D
