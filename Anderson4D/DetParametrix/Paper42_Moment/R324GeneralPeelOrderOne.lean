import Anderson4D.DetParametrix.Paper42_Moment.R324ComplementScheduleCore

/-!
# The order-one contraction bound for the R-324 uniform branch

Order one has exactly one contraction entity: no within-half pair can
exist on a one-point half, so both partial pairings are trivial and the
cross bijection is unique.  Its physical integral is the two complete
one-vertex half chains joined by a single cross covariance.  All four
boundary Green edges peel at unit paper mass and the cross covariance
has mollifier mass at most one, so the term is bounded by the paper
volume alone — no logarithm and no window is spent, exactly the
`K^1 |log ε|^0` entry of the general peel ledger.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The unique order-one contraction -/

/-- Both halves unpaired, singles matched by the unique bijection. -/
def oneCrossContraction : MomentContraction 1 :=
  ⟨PartialPairing.id, PartialPairing.id, Equiv.refl _⟩

/-- A one-point half admits only the trivial pairing. -/
theorem partialPairing_finOne_eq (κ : PartialPairing (Fin 1)) :
    κ = PartialPairing.id := by
  refine PartialPairing.ext fun i => ?_
  have : Subsingleton (Fin 1) := ⟨fun a b => Fin.ext (by omega)⟩
  exact Subsingleton.elim _ _

/-- The order-one contraction entity is unique. -/
theorem momentContraction_one_eq (e : MomentContraction 1) :
    e = oneCrossContraction := by
  obtain ⟨κp, κm, π⟩ := e
  have hsub : Subsingleton (Fin 1) := ⟨fun a b => Fin.ext (by omega)⟩
  rcases partialPairing_finOne_eq κp with rfl
  rcases partialPairing_finOne_eq κm with rfl
  have hπ : π = Equiv.refl _ := by
    haveI :
        Subsingleton
          ↥((PartialPairing.id : PartialPairing (Fin 1)).singles) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim _ _
  rw [hπ]
  rfl

/-- Order one has exactly one contraction entity. -/
theorem fintype_card_momentContraction_one :
    Fintype.card (MomentContraction 1) = 1 := by decide

/-- Nothing is extracted from the trivial pairing of a one-point
half. -/
theorem extract_id_finOne :
    extract (PartialPairing.id : PartialPairing (Fin 1)) =
      ([] : List (Fin 1 × Fin 1)) := by decide

/-- **Closed form of the order-one trivial-pairing integrand**: the
plain two-edge chain. -/
theorem detIntegrand_one_id_assemble
    (ρ : SmoothCutoff) (ε : ℝ) (x y : T4) (u : Fin 1 → T4) :
    detIntegrand ρ ε 1 PartialPairing.id (assemble x y u) =
      greenFn (x - u 0) * greenFn (u 0 - y) := by
  unfold detIntegrand
  rw [extract_id_finOne]
  have hxt1 : assemble x y u (1 : Fin (1 + 2)) = u 0 := by
    have h : (1 : Fin (1 + 2)) = varIdx (0 : Fin 1) := rfl
    rw [h, assemble_varIdx]
  have hxt2 : assemble x y u (2 : Fin (1 + 2)) = y := by
    have h : (2 : Fin (1 + 2)) = Fin.last (1 + 1) := rfl
    rw [h, assemble_last]
  have hcov :
      (∏ i ∈ (PartialPairing.id :
            PartialPairing (Fin 1)).pairSupport.filter
          (fun i => i < (PartialPairing.id : PartialPairing (Fin 1)) i),
        ρ.etaEpsT4 ε
          (assemble x y u (varIdx i) -
            assemble x y u
              (varIdx ((PartialPairing.id :
                PartialPairing (Fin 1)) i)))) = 1 := by
    have hset :
        (PartialPairing.id :
            PartialPairing (Fin 1)).pairSupport.filter
          (fun i => i < (PartialPairing.id :
            PartialPairing (Fin 1)) i) =
          (∅ : Finset (Fin 1)) := by decide
    rw [hset, Finset.prod_empty]
  have hchain :
      (∏ e : Fin (1 + 1),
        if e.val ∈ ([] : List (Fin 1 × Fin 1)).map
            (fun p => p.2.val + 1) then 1
        else greenFn (assemble x y u e.castSucc -
          assemble x y u e.succ)) =
        greenFn (x - u 0) * greenFn (u 0 - y) := by
    rw [Fin.prod_univ_two]
    simp only [List.map_nil, List.not_mem_nil, if_false]
    have hc0 : (0 : Fin (1 + 1)).castSucc = (0 : Fin (1 + 2)) := rfl
    have hs0 : (0 : Fin (1 + 1)).succ = (1 : Fin (1 + 2)) := rfl
    have hc1 : (1 : Fin (1 + 1)).castSucc = (1 : Fin (1 + 2)) := rfl
    have hs1 : (1 : Fin (1 + 1)).succ = (2 : Fin (1 + 2)) := rfl
    rw [hc0, hs0, hc1, hs1, assemble_zero, hxt1, hxt2]
  rw [hchain, hcov, List.map_nil, List.prod_nil, mul_one, mul_one]

/-- **The order-one cross covariance**: exactly one factor. -/
theorem momentCrossCovarianceProduct_one
    (ρ : SmoothCutoff) (ε : ℝ)
    (π : (PartialPairing.id : PartialPairing (Fin 1)).singles ≃
      (PartialPairing.id : PartialPairing (Fin 1)).singles)
    (v : Fin (2 * 1) → T4) :
    momentCrossCovarianceProduct ρ ε 1
        PartialPairing.id PartialPairing.id π v =
      ρ.etaEpsT4 ε
        (v (leftMomentIndex 0) - v (rightMomentIndex 0)) := by
  unfold momentCrossCovarianceProduct
  have hsub : Subsingleton (Fin 1) := ⟨fun a b => Fin.ext (by omega)⟩
  haveI :
      Subsingleton
        ↥((PartialPairing.id : PartialPairing (Fin 1)).singles) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hmem :
      (0 : Fin 1) ∈
        (PartialPairing.id : PartialPairing (Fin 1)).singles := by
    decide
  haveI :
      Unique
        ↥((PartialPairing.id : PartialPairing (Fin 1)).singles) :=
    uniqueOfSubsingleton ⟨0, hmem⟩
  rw [Finset.univ_unique, Finset.prod_singleton]
  have h1 :
      ((default :
        ↥((PartialPairing.id : PartialPairing (Fin 1)).singles)) :
          Fin 1) = 0 :=
    Subsingleton.elim _ _
  have h2 :
      ((π default : ↥((PartialPairing.id :
        PartialPairing (Fin 1)).singles)) : Fin 1) = 0 :=
    Subsingleton.elim _ _
  rw [h1, h2]

/-! ## The order-one physical density -/

/-- Internal core: the single cross covariance. -/
def r324OneCoreDensity (ρ : SmoothCutoff) (ε : ℝ)
    (v : Fin (2 * 1) → T4) : ℝ :=
  ρ.etaEpsT4 ε (v (leftMomentIndex 0) - v (rightMomentIndex 0))

/-- The full order-one physical density in peel-ready nested form:
each external variable multiplies one unit-mass boundary Green edge. -/
def r324OnePhysicalDensity (ρ : SmoothCutoff) (ε : ℝ)
    (p : R324PhysicalPoint 1) : ℝ :=
  greenFn (p.1 - p.2.2.2.2 (leftMomentIndex 0)) *
    (greenFn (p.2.2.2.2 (leftMomentIndex 0) - p.2.1) *
      (greenFn (p.2.2.1 - p.2.2.2.2 (rightMomentIndex 0)) *
        (greenFn (p.2.2.2.2 (rightMomentIndex 0) - p.2.2.2.1) *
          r324OneCoreDensity ρ ε p.2.2.2.2)))

/-- The norm of the unique order-one flat integrand is the order-one
physical density. -/
theorem norm_r324Flatten_one_eq
    (ρ : SmoothCutoff) (ε : ℝ) (α β : Z4)
    (p : R324PhysicalPoint 1) :
    ‖r324Flatten
        (deterministicMomentIntegrand ρ ε 1 α β
          oneCrossContraction.1 oneCrossContraction.2.1
          oneCrossContraction.2.2) p‖ =
      r324OnePhysicalDensity ρ ε p := by
  unfold r324Flatten deterministicMomentIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_charT4,
    norm_charT4, norm_charT4, norm_charT4, mul_one, one_mul,
    one_mul, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hD :
      detIntegrand ρ ε 1 oneCrossContraction.1
          (assemble p.1 p.2.1
            (fun i => p.2.2.2.2 (leftMomentIndex i))) *
        detIntegrand ρ ε 1 oneCrossContraction.2.1
          (assemble p.2.2.1 p.2.2.2.1
            (fun i => p.2.2.2.2 (rightMomentIndex i))) *
        momentCrossCovarianceProduct ρ ε 1
          oneCrossContraction.1 oneCrossContraction.2.1
          oneCrossContraction.2.2 p.2.2.2.2 =
        r324OnePhysicalDensity ρ ε p := by
    show
      detIntegrand ρ ε 1 PartialPairing.id
          (assemble p.1 p.2.1
            (fun i => p.2.2.2.2 (leftMomentIndex i))) *
        detIntegrand ρ ε 1 PartialPairing.id
          (assemble p.2.2.1 p.2.2.2.1
            (fun i => p.2.2.2.2 (rightMomentIndex i))) *
        momentCrossCovarianceProduct ρ ε 1
          PartialPairing.id PartialPairing.id (Equiv.refl _)
          p.2.2.2.2 =
        r324OnePhysicalDensity ρ ε p
    rw [detIntegrand_one_id_assemble, detIntegrand_one_id_assemble,
      momentCrossCovarianceProduct_one]
    unfold r324OnePhysicalDensity r324OneCoreDensity
    ring
  rw [hD]
  rw [abs_of_nonneg ?_]
  unfold r324OnePhysicalDensity r324OneCoreDensity
  have h1 := greenFn_nonneg
    (p.1 - p.2.2.2.2 (leftMomentIndex 0))
  have h2 := greenFn_nonneg
    (p.2.2.2.2 (leftMomentIndex 0) - p.2.1)
  have h3 := greenFn_nonneg
    (p.2.2.1 - p.2.2.2.2 (rightMomentIndex 0))
  have h4 := greenFn_nonneg
    (p.2.2.2.2 (rightMomentIndex 0) - p.2.2.2.1)
  have h5 := ρ.etaEpsT4_nonneg ε
    (p.2.2.2.2 (leftMomentIndex 0) -
      p.2.2.2.2 (rightMomentIndex 0))
  positivity

/-- **Exact peeling of the four external variables.**  Each boundary
Green edge has unit paper mass; the flat order-one density integrates
to the internal core integral. -/
theorem integral_flat_r324OnePhysicalDensity
    (ρ : SmoothCutoff) (ε : ℝ)
    (hint :
      Integrable (r324OnePhysicalDensity ρ ε)
        (r324PhysicalMeasure 1)) :
    (∫ p, r324OnePhysicalDensity ρ ε p
        ∂(r324PhysicalMeasure 1)) =
      ∫ v : Fin (2 * 1) → T4,
        r324OneCoreDensity ρ ε v
        ∂(Measure.pi fun _ : Fin (2 * 1) => paperMeasure) := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure at hint ⊢
  unfold r324OnePhysicalDensity at hint ⊢
  rw [integral_prod_symm _ hint]
  have heval1 :
      (fun q : T4 × (T4 × (T4 × (Fin (2 * 1) → T4))) =>
        ∫ x, greenFn (x - q.2.2.2 (leftMomentIndex 0)) *
          (greenFn (q.2.2.2 (leftMomentIndex 0) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 0) - q.2.2.1) *
                r324OneCoreDensity ρ ε q.2.2.2)))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (T4 × (Fin (2 * 1) → T4))) =>
          greenFn (q.2.2.2 (leftMomentIndex 0) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 0) - q.2.2.1) *
                r324OneCoreDensity ρ ε q.2.2.2)) := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  have hint1 := hint.integral_prod_right
  rw [heval1] at hint1 ⊢
  rw [integral_prod_symm _ hint1]
  have heval2 :
      (fun q : T4 × (T4 × (Fin (2 * 1) → T4)) =>
        ∫ y, greenFn (q.2.2 (leftMomentIndex 0) - y) *
          (greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 0) - q.2.1) *
              r324OneCoreDensity ρ ε q.2.2))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (Fin (2 * 1) → T4)) =>
          greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 0) - q.2.1) *
              r324OneCoreDensity ρ ε q.2.2) := by
    funext q
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  have hint2 := hint1.integral_prod_right
  rw [heval2] at hint2 ⊢
  rw [integral_prod_symm _ hint2]
  have heval3 :
      (fun q : T4 × (Fin (2 * 1) → T4) =>
        ∫ z, greenFn (z - q.2 (rightMomentIndex 0)) *
          (greenFn (q.2 (rightMomentIndex 0) - q.1) *
            r324OneCoreDensity ρ ε q.2)
          ∂paperMeasure) =
        fun q : T4 × (Fin (2 * 1) → T4) =>
          greenFn (q.2 (rightMomentIndex 0) - q.1) *
            r324OneCoreDensity ρ ε q.2 := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  have hint3 := hint2.integral_prod_right
  rw [heval3] at hint3 ⊢
  rw [integral_prod_symm _ hint3]
  have heval4 :
      (fun v : Fin (2 * 1) → T4 =>
        ∫ w, greenFn (v (rightMomentIndex 0) - w) *
          r324OneCoreDensity ρ ε v
          ∂paperMeasure) =
        fun v : Fin (2 * 1) → T4 =>
          r324OneCoreDensity ρ ε v := by
    funext v
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  rw [heval4]

/-- The order-one core inherits integrability from the flat
density. -/
theorem integrable_r324OneCoreDensity_of_flat
    (ρ : SmoothCutoff) (ε : ℝ)
    (hint :
      Integrable (r324OnePhysicalDensity ρ ε)
        (r324PhysicalMeasure 1)) :
    Integrable (r324OneCoreDensity ρ ε)
      (Measure.pi fun _ : Fin (2 * 1) => paperMeasure) := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure at hint
  unfold r324OnePhysicalDensity at hint
  have hint1 := hint.integral_prod_right
  have heval1 :
      (fun q : T4 × (T4 × (T4 × (Fin (2 * 1) → T4))) =>
        ∫ x, greenFn (x - q.2.2.2 (leftMomentIndex 0)) *
          (greenFn (q.2.2.2 (leftMomentIndex 0) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 0) - q.2.2.1) *
                r324OneCoreDensity ρ ε q.2.2.2)))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (T4 × (Fin (2 * 1) → T4))) =>
          greenFn (q.2.2.2 (leftMomentIndex 0) - q.1) *
            (greenFn (q.2.1 - q.2.2.2 (rightMomentIndex 0)) *
              (greenFn (q.2.2.2 (rightMomentIndex 0) - q.2.2.1) *
                r324OneCoreDensity ρ ε q.2.2.2)) := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  rw [heval1] at hint1
  have hint2 := hint1.integral_prod_right
  have heval2 :
      (fun q : T4 × (T4 × (Fin (2 * 1) → T4)) =>
        ∫ y, greenFn (q.2.2 (leftMomentIndex 0) - y) *
          (greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 0) - q.2.1) *
              r324OneCoreDensity ρ ε q.2.2))
          ∂paperMeasure) =
        fun q : T4 × (T4 × (Fin (2 * 1) → T4)) =>
          greenFn (q.1 - q.2.2 (rightMomentIndex 0)) *
            (greenFn (q.2.2 (rightMomentIndex 0) - q.2.1) *
              r324OneCoreDensity ρ ε q.2.2) := by
    funext q
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  rw [heval2] at hint2
  have hint3 := hint2.integral_prod_right
  have heval3 :
      (fun q : T4 × (Fin (2 * 1) → T4) =>
        ∫ z, greenFn (z - q.2 (rightMomentIndex 0)) *
          (greenFn (q.2 (rightMomentIndex 0) - q.1) *
            r324OneCoreDensity ρ ε q.2)
          ∂paperMeasure) =
        fun q : T4 × (Fin (2 * 1) → T4) =>
          greenFn (q.2 (rightMomentIndex 0) - q.1) *
            r324OneCoreDensity ρ ε q.2 := by
    funext q
    rw [integral_mul_const, integral_greenFn_sub, one_mul]
  rw [heval3] at hint3
  have hint4 := hint3.integral_prod_right
  have heval4 :
      (fun v : Fin (2 * 1) → T4 =>
        ∫ w, greenFn (v (rightMomentIndex 0) - w) *
          r324OneCoreDensity ρ ε v
          ∂paperMeasure) =
        fun v : Fin (2 * 1) → T4 =>
          r324OneCoreDensity ρ ε v := by
    funext v
    rw [integral_mul_const, integral_greenFn_shift_left, one_mul]
  rw [heval4] at hint4
  exact hint4

/-! ## The core mass bound -/

/-- **Unit mollifier mass bound for the order-one core.**  One cross
covariance integrates to at most one over its first variable; the
remaining variable contributes the paper volume. -/
theorem integral_r324OneCoreDensity_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε)
    (hcore :
      Integrable (r324OneCoreDensity ρ ε)
        (Measure.pi fun _ : Fin (2 * 1) => paperMeasure)) :
    (∫ v : Fin (2 * 1) → T4,
        r324OneCoreDensity ρ ε v
        ∂(Measure.pi fun _ : Fin (2 * 1) => paperMeasure)) ≤
      (2 * Real.pi) ^ (dim : ℕ) := by
  set g : T4 × T4 → ℝ :=
    fun q => ρ.etaEpsT4 ε (q.1 - q.2) with hgdef
  have hmp :=
    measurePreserving_piFinTwo
      (fun _ : Fin 2 => paperMeasure)
  have hcomp :
      ∀ v : Fin (2 * 1) → T4,
        r324OneCoreDensity ρ ε v =
          g ((MeasurableEquiv.piFinTwo
            fun _ : Fin 2 => T4) v) := by
    intro v
    unfold r324OneCoreDensity
    rw [hgdef]
    have hl : leftMomentIndex (0 : Fin 1) = (0 : Fin (2 * 1)) :=
      rfl
    have hr : rightMomentIndex (0 : Fin 1) = (1 : Fin (2 * 1)) :=
      rfl
    rw [hl, hr]
    rfl
  have hgint : Integrable g (paperMeasure.prod paperMeasure) := by
    have hpi :
        Integrable
          (g ∘ (MeasurableEquiv.piFinTwo fun _ : Fin 2 => T4))
          (Measure.pi fun _ : Fin 2 => paperMeasure) :=
      hcore.congr
        (Filter.Eventually.of_forall fun v => hcomp v)
    have hmap := hmp.map_eq
    rw [← hmap]
    exact (integrable_map_equiv _ g).mpr hpi
  calc
    (∫ v : Fin (2 * 1) → T4,
        r324OneCoreDensity ρ ε v
        ∂(Measure.pi fun _ : Fin (2 * 1) => paperMeasure)) =
        ∫ v : Fin 2 → T4,
          g ((MeasurableEquiv.piFinTwo fun _ : Fin 2 => T4) v)
          ∂(Measure.pi fun _ : Fin 2 => paperMeasure) :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun v => hcomp v)
    _ = ∫ q, g q ∂(paperMeasure.prod paperMeasure) :=
      hmp.integral_comp' g
    _ = ∫ y, ∫ x, g (x, y) ∂paperMeasure ∂paperMeasure :=
      integral_prod_symm g hgint
    _ ≤ ∫ _y : T4, (1 : ℝ) ∂paperMeasure := by
      refine integral_mono_of_nonneg ?_ (integrable_const 1) ?_
      · filter_upwards with y
        exact integral_nonneg fun x =>
          ρ.etaEpsT4_nonneg ε _
      · filter_upwards with y
        exact integral_etaEpsT4_sub_le_one ρ hε y
    _ = (2 * Real.pi) ^ (dim : ℕ) := by
      rw [integral_const, measureReal_def, paperMeasure_univ,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
        mul_one]

/-! ## The order-one contraction bound -/

/-- **Every order-one contraction term is bounded by the paper
volume.**  No logarithm is spent: the four boundary Green edges peel
at unit mass and the single cross covariance has mass at most one. -/
theorem norm_deterministicMomentContractionTerm_one_le
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (α β : Z4) (e : MomentContraction 1) :
    ‖deterministicMomentContractionTerm ρ ε 1 α β e‖ ≤
      (2 * Real.pi) ^ (dim : ℕ) := by
  rcases momentContraction_one_eq e with rfl
  have hflat :=
    r324MomentIntegrable_all ρ hε hε1 α β oneCrossContraction
  have hterm :
      deterministicMomentContractionTerm ρ ε 1 α β
          oneCrossContraction =
        ∫ p, r324Flatten
          (deterministicMomentIntegrand ρ ε 1 α β
            oneCrossContraction.1 oneCrossContraction.2.1
            oneCrossContraction.2.2) p
          ∂(r324PhysicalMeasure 1) :=
    (integral_r324Flatten_deterministicMomentIntegrand
      ρ ε 1 α β oneCrossContraction hflat).symm
  have hdensityint :
      Integrable (r324OnePhysicalDensity ρ ε)
        (r324PhysicalMeasure 1) := by
    refine hflat.norm.congr ?_
    filter_upwards with p
    exact norm_r324Flatten_one_eq ρ ε α β p
  calc
    ‖deterministicMomentContractionTerm ρ ε 1 α β
        oneCrossContraction‖ =
        ‖∫ p, r324Flatten
          (deterministicMomentIntegrand ρ ε 1 α β
            oneCrossContraction.1 oneCrossContraction.2.1
            oneCrossContraction.2.2) p
          ∂(r324PhysicalMeasure 1)‖ := by rw [hterm]
    _ ≤ ∫ p, ‖r324Flatten
          (deterministicMomentIntegrand ρ ε 1 α β
            oneCrossContraction.1 oneCrossContraction.2.1
            oneCrossContraction.2.2) p‖
          ∂(r324PhysicalMeasure 1) :=
      norm_integral_le_integral_norm _
    _ = ∫ p, r324OnePhysicalDensity ρ ε p
          ∂(r324PhysicalMeasure 1) :=
      integral_congr_ae (Filter.Eventually.of_forall
        (norm_r324Flatten_one_eq ρ ε α β))
    _ = ∫ v : Fin (2 * 1) → T4,
          r324OneCoreDensity ρ ε v
          ∂(Measure.pi fun _ : Fin (2 * 1) => paperMeasure) :=
      integral_flat_r324OnePhysicalDensity ρ ε hdensityint
    _ ≤ (2 * Real.pi) ^ (dim : ℕ) :=
      integral_r324OneCoreDensity_le ρ hε
        (integrable_r324OneCoreDensity_of_flat ρ ε hdensityint)

end

end Anderson4D
