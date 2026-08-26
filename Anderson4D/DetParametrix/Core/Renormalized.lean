import Anderson4D.DetParametrix.Core.Kernels

/-!
# Recursive deterministic renormalization and the closed formula

Paper: D-RI — Def 3.1 / Prop 3.2 — deterministic renormalization, closed formula (3.6)

The definitions in `Kernels.lean` use the closed formula (3.6), as required
by DESIGN §5.7bis.  This file supplies the converse obligation: after the
one-step identity (3.7), every application of paper Definition 3.1 replaces
one chain edge by its endpoint difference.  We implement those replacements
recursively in extraction order and prove that their result is exactly the
closed product.  Unlike a definitional alias, the recursive side carries a
shrinking active-edge set.

All definitions accept a family `[G₀, …, Gₘ]`; specializing every entry to
`greenFn` recovers `detIntegrand`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The one-step analytic identity -/

/-- The unrenormalized two-kernel insertion in the first line of paper
(3.5), with `J` between the two boundary kernels. -/
def rawRenormalizationStep
    (Gp J Gr : T4 → ℝ) (x y : T4) : ℝ :=
  ∫ z, ∫ w,
    Gp (x - z) * J (z - w) * Gr (w - y)
      ∂paperMeasure ∂paperMeasure

/-- The scalar counterterm in paper (3.5), with the formal delta already
evaluated. -/
def renormalizationCounterterm
    (Gp J Gr : T4 → ℝ) (x y : T4) : ℝ :=
  (∫ u, J u ∂paperMeasure) *
    ∫ z, Gp (x - z) * Gr (z - y) ∂paperMeasure

/-- The difference-integrand form in the second line of paper (3.7). -/
def differenceRenormalizationStep
    (Gp J Gr : T4 → ℝ) (x y : T4) : ℝ :=
  ∫ z, ∫ w,
    Gp (x - z) * J (z - w) *
      (Gr (w - y) - Gr (z - y))
      ∂paperMeasure ∂paperMeasure

/-- **Paper (3.7).**  Subtracting the scalar counterterm is equivalent to
replacing the right boundary kernel by its endpoint difference.

The hypotheses expose exactly the two uses of Bochner-integral linearity and
translation invariance needed by the paper's formal calculation; later
analytic estimates discharge them for the concrete kernels. -/
theorem raw_sub_counterterm_eq_difference
    (Gp J Gr : T4 → ℝ) (x y : T4)
    (hshift : ∀ z : T4,
      (∫ w, J (z - w) ∂paperMeasure) =
        ∫ u, J u ∂paperMeasure)
    (hrawInner : ∀ z : T4, Integrable
      (fun w => Gp (x - z) * J (z - w) * Gr (w - y))
      paperMeasure)
    (hdiagInner : ∀ z : T4, Integrable
      (fun w => Gp (x - z) * J (z - w) * Gr (z - y))
      paperMeasure)
    (hrawOuter : Integrable
      (fun z => ∫ w,
        Gp (x - z) * J (z - w) * Gr (w - y)
          ∂paperMeasure) paperMeasure)
    (hdiagOuter : Integrable
      (fun z => ∫ w,
        Gp (x - z) * J (z - w) * Gr (z - y)
          ∂paperMeasure) paperMeasure) :
    rawRenormalizationStep Gp J Gr x y -
        renormalizationCounterterm Gp J Gr x y =
      differenceRenormalizationStep Gp J Gr x y := by
  let mass : ℝ := ∫ u, J u ∂paperMeasure
  have hinner (z : T4) :
      (∫ w, Gp (x - z) * J (z - w) *
          (Gr (w - y) - Gr (z - y)) ∂paperMeasure) =
        (∫ w, Gp (x - z) * J (z - w) * Gr (w - y)
            ∂paperMeasure) -
          ∫ w, Gp (x - z) * J (z - w) * Gr (z - y)
            ∂paperMeasure := by
    rw [← integral_sub (hrawInner z) (hdiagInner z)]
    apply integral_congr_ae
    filter_upwards with w
    ring
  have hdiag (z : T4) :
      (∫ w, Gp (x - z) * J (z - w) * Gr (z - y)
          ∂paperMeasure) =
        (Gp (x - z) * Gr (z - y)) * mass := by
    calc
      (∫ w, Gp (x - z) * J (z - w) * Gr (z - y)
          ∂paperMeasure) =
          ∫ w, (Gp (x - z) * Gr (z - y)) * J (z - w)
            ∂paperMeasure := by
              apply integral_congr_ae
              filter_upwards with w
              ring
      _ = (Gp (x - z) * Gr (z - y)) *
          ∫ w, J (z - w) ∂paperMeasure := by
            rw [integral_const_mul]
      _ = (Gp (x - z) * Gr (z - y)) * mass := by
            rw [hshift z]
  have hdiagTotal :
      (∫ z, ∫ w,
          Gp (x - z) * J (z - w) * Gr (z - y)
            ∂paperMeasure ∂paperMeasure) =
        mass * ∫ z, Gp (x - z) * Gr (z - y)
          ∂paperMeasure := by
    calc
      (∫ z, ∫ w,
          Gp (x - z) * J (z - w) * Gr (z - y)
            ∂paperMeasure ∂paperMeasure) =
          ∫ z, (Gp (x - z) * Gr (z - y)) * mass
            ∂paperMeasure := by
              apply integral_congr_ae
              filter_upwards with z
              exact hdiag z
      _ = (∫ z, Gp (x - z) * Gr (z - y)
              ∂paperMeasure) * mass := by
            rw [integral_mul_const]
      _ = mass * ∫ z, Gp (x - z) * Gr (z - y)
              ∂paperMeasure := by ring
  unfold rawRenormalizationStep renormalizationCounterterm
    differenceRenormalizationStep
  rw [integral_congr_ae
    (Filter.Eventually.of_forall fun z => hinner z)]
  rw [integral_sub hrawOuter hdiagOuter, hdiagTotal]

/-! ## A generic replacement-product recursion -/

/-- Starting with the product of `base` over `active`, recursively remove the
key of each replacement and multiply by its new value.  This is the scalar
semantics of successive edge replacements, without division and hence with
no junk case when an old edge factor vanishes. -/
def replacementProduct
    {ι : Type*} [DecidableEq ι] (base : ι → ℝ) :
    List (ι × ℝ) → Finset ι → ℝ
  | [], active => ∏ i ∈ active, base i
  | u :: us, active =>
      u.2 * replacementProduct base us (active.erase u.1)

/-- A recursive sequence of replacements is the product of all replacement
values times the product of untouched base entries.  Repeated keys are
allowed: they are removed once but every explicitly requested replacement
value is retained. -/
theorem replacementProduct_eq_prod
    {ι : Type*} [DecidableEq ι] (base : ι → ℝ)
    (us : List (ι × ℝ)) (active : Finset ι) :
    replacementProduct base us active =
      (us.map Prod.snd).prod *
        ∏ i ∈ active \ (us.map Prod.fst).toFinset, base i := by
  induction us generalizing active with
  | nil =>
      simp [replacementProduct]
  | cons u us ih =>
      rw [replacementProduct, ih]
      simp only [List.map_cons, List.prod_cons, List.toFinset_cons]
      have hset :
          active.erase u.1 \ (us.map Prod.fst).toFinset =
            active \ insert u.1 (us.map Prod.fst).toFinset := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        tauto
      rw [hset]
      ring

/-! ## Generalized chain inputs -/

/-- The chain edge immediately to the right of an extracted interval
`p = (l,r)`.  Paper indices are one-based, so a zero-based right endpoint
`r` replaces edge `r+1` among the `m+1` chain edges. -/
def extractedRightEdge {m : ℕ} (p : Fin m × Fin m) : Fin (m + 1) :=
  ⟨p.2.val + 1, by have := p.2.isLt; omega⟩

@[simp]
theorem extractedRightEdge_val {m : ℕ} (p : Fin m × Fin m) :
    (extractedRightEdge p).val = p.2.val + 1 := rfl

/-- Unrenormalized value of chain edge `e` for generalized input kernels
`G₀,…,Gₘ`. -/
def chainEdgeWith {m : ℕ}
    (G : Fin (m + 1) → T4 → ℝ)
    (xt : Fin (m + 2) → T4) (e : Fin (m + 1)) : ℝ :=
  G e (xt e.castSucc - xt e.succ)

/-- The difference which replaces the edge to the right of an extracted
interval, with the correct member of the generalized kernel family. -/
def diffFactorWith {m : ℕ}
    (G : Fin (m + 1) → T4 → ℝ)
    (xt : Fin (m + 2) → T4) (p : Fin m × Fin m) : ℝ :=
  G (extractedRightEdge p)
      (xt (varIdx p.2) -
        xt ⟨p.2.val + 2, by have := p.2.isLt; omega⟩) -
    G (extractedRightEdge p)
      (xt (varIdx p.1) -
        xt ⟨p.2.val + 2, by have := p.2.isLt; omega⟩)

/-- The finite set of chain edges replaced by the extraction procedure. -/
def extractedRightEdges {m : ℕ}
    (κ : PartialPairing (Fin m)) : Finset (Fin (m + 1)) :=
  ((extract κ).map extractedRightEdge).toFinset

/-- The generalized closed integrand (paper (3.6)) before the global
coupling factor and integration. -/
def detIntegrandWith
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (G : Fin (m + 1) → T4 → ℝ)
    (xt : Fin (m + 2) → T4) : ℝ :=
  (∏ e : Fin (m + 1),
      if e ∈ extractedRightEdges κ then 1 else chainEdgeWith G xt e) *
    ((extract κ).map (diffFactorWith G xt)).prod *
    ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε (xt (varIdx i) - xt (varIdx (κ i)))

/-- **Recursive deterministic renormalization kernel (paper Def. 3.1 after
the one-step identity (3.7)).**  Each smallest-leftmost interval returned by
`extract κ` removes its right chain edge and inserts the corresponding
difference.  The covariance factors do not change during this operation. -/
def detRIkernelWith
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (G : Fin (m + 1) → T4 → ℝ)
    (xt : Fin (m + 2) → T4) : ℝ :=
  replacementProduct (chainEdgeWith G xt)
      ((extract κ).map fun p =>
        (extractedRightEdge p, diffFactorWith G xt p))
      Finset.univ *
    ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
      ρ.etaEpsT4 ε (xt (varIdx i) - xt (varIdx (κ i)))

/-- Specialization of the recursive kernel to the Green chain used in the
paper. -/
def detRIkernel
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) : ℝ :=
  detRIkernelWith ρ ε m κ (fun _ => greenFn) xt

/-- A product which replaces all entries in `s` by one is the product of the
base function over the complement of `s`. -/
theorem prod_if_mem_eq_prod_sdiff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    (∏ i : ι, if i ∈ s then 1 else f i) =
      ∏ i ∈ Finset.univ \ s, f i := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  apply Finset.prod_congr
  · ext e
    simp
  · intro e _
    rfl

/-- The untouched-edge product written with an `if` is exactly the product
over the complement of the replaced edge set. -/
theorem prod_if_not_extractedRightEdges
    {m : ℕ} (κ : PartialPairing (Fin m))
    (f : Fin (m + 1) → ℝ) :
    (∏ e : Fin (m + 1),
        if e ∈ extractedRightEdges κ then 1 else f e) =
      ∏ e ∈ Finset.univ \ extractedRightEdges κ, f e :=
  prod_if_mem_eq_prod_sdiff (extractedRightEdges κ) f

/-- **Proposition 3.2, generalized-input integrand form.**  The recursive
edge-removal semantics of Definition 3.1 equals the closed formula (3.6).
The proof is a genuine induction over the extracted endpoint list through
`replacementProduct_eq_prod`. -/
theorem detRIkernelWith_eq_prod
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (G : Fin (m + 1) → T4 → ℝ)
    (xt : Fin (m + 2) → T4) :
    detRIkernelWith ρ ε m κ G xt =
      detIntegrandWith ρ ε m κ G xt := by
  unfold detRIkernelWith detIntegrandWith
  rw [replacementProduct_eq_prod]
  have hkeys :
      (((extract κ).map fun p =>
          (extractedRightEdge p, diffFactorWith G xt p)).map
            Prod.fst).toFinset =
        extractedRightEdges κ := by
    simp [extractedRightEdges, Function.comp_def]
  have hvals :
      (((extract κ).map fun p =>
          (extractedRightEdge p, diffFactorWith G xt p)).map
            Prod.snd).prod =
        ((extract κ).map (diffFactorWith G xt)).prod := by
    simp [Function.comp_def]
  rw [hkeys, hvals, prod_if_not_extractedRightEdges]
  ring

/-- Green-kernel specialization of Proposition 3.2. -/
theorem detRIkernel_eq_prod
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    detRIkernel ρ ε m κ xt =
      detIntegrandWith ρ ε m κ (fun _ => greenFn) xt := by
  exact detRIkernelWith_eq_prod ρ ε m κ (fun _ => greenFn) xt

/-- The generalized closed formula specializes definitionally (up to the
equivalent `Fin`/value membership representation of replaced edges) to the
original frozen `detIntegrand`. -/
theorem detIntegrandWith_green_eq_detIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    detIntegrandWith ρ ε m κ (fun _ => greenFn) xt =
      detIntegrand ρ ε m κ xt := by
  have hmem : ∀ e : Fin (m + 1),
      e ∈ extractedRightEdges κ ↔
        e.val ∈ (extract κ).map (fun p => p.2.val + 1) := by
    intro e
    simp only [extractedRightEdges, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨p, hp, hep⟩
      refine ⟨p, hp, ?_⟩
      simpa [extractedRightEdge] using congrArg Fin.val hep
    · rintro ⟨p, hp, hep⟩
      refine ⟨p, hp, ?_⟩
      apply Fin.ext
      simpa [extractedRightEdge] using hep
  unfold detIntegrandWith detIntegrand chainEdgeWith diffFactorWith diffFactor
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro e _
      simp only [hmem e]
    · rfl
  · rfl

/-- Direct Green-kernel form of Proposition 3.2. -/
theorem detRIkernel_eq_detIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) :
    detRIkernel ρ ε m κ xt = detIntegrand ρ ε m κ xt :=
  (detRIkernel_eq_prod ρ ε m κ xt).trans
    (detIntegrandWith_green_eq_detIntegrand ρ ε m κ xt)

/-! ## Integrated recursive kernels -/

/-- The fully integrated kernel built from the recursive edge-replacement
semantics. -/
def detRIrecursiveFull
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m)) (x y : T4) : ℝ :=
  lamEps lam ε ^ m *
    ∫ v : Fin m → T4, detRIkernel ρ ε m κ (assemble x y v)
      ∂(MeasureTheory.Measure.pi fun _ => paperMeasure)

/-- The profile version of `detRIrecursiveFull`, integrating only paired
variables and keeping the single variables free. -/
def detRIrecursiveProfile
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m)) (x y : T4)
    (z : Fin m → T4) : ℝ :=
  lamEps lam ε ^ m *
    ∫ w : (↥κ.pairSupport → T4),
      detRIkernel ρ ε m κ (assemble x y fun i =>
        if h : i ∈ κ.pairSupport then w ⟨i, h⟩ else z i)
      ∂(MeasureTheory.Measure.pi fun _ => paperMeasure)

/-- Integrated form of Proposition 3.2. -/
theorem detRIrecursiveFull_eq_detRIfull
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m)) (x y : T4) :
    detRIrecursiveFull ρ lam ε m κ x y =
      detRIfull ρ lam ε m κ x y := by
  unfold detRIrecursiveFull detRIfull
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  exact detRIkernel_eq_detIntegrand ρ ε m κ (assemble x y v)

/-- Profile-integrated form of Proposition 3.2. -/
theorem detRIrecursiveProfile_eq_detRIprofile
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m)) (x y : T4)
    (z : Fin m → T4) :
    detRIrecursiveProfile ρ lam ε m κ x y z =
      detRIprofile ρ lam ε m κ x y z := by
  unfold detRIrecursiveProfile detRIprofile
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  exact detRIkernel_eq_detIntegrand ρ ε m κ
    (assemble x y fun i =>
      if h : i ∈ κ.pairSupport then w ⟨i, h⟩ else z i)

end

end Anderson4D
