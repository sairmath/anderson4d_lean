import Anderson4D.Combinatorics.PairingRecursion
import Anderson4D.Probability.Chaos

/-!
# Explicit partial-pairing expansion of Wick polynomials

This file expands the recursive Wick polynomial as a finite sum over actual
`PartialPairing`s.  Every two-cycle is represented at its smaller endpoint;
the corresponding factor is `-C`, while fixed points contribute the field
value.  The head-classification equivalence from `PairingRecursion` then
gives the creation--contraction recursion without any symmetry assumption
on `C`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace PartialPairing

/-- Representatives selected by an explicit strict relation. -/
def representativesBy {α : Type*} [Fintype α] [DecidableEq α]
    (lt : α → α → Prop) [DecidableRel lt]
    (κ : PartialPairing α) : Finset α :=
  κ.pairSupport.filter fun i => lt i (κ i)

/-- Smaller endpoints of the two-cycles of a linearly ordered pairing. -/
def representatives {α : Type*} [Fintype α] [DecidableEq α]
    [LinearOrder α] (κ : PartialPairing α) : Finset α :=
  κ.representativesBy (· < ·)

@[simp] theorem mem_representatives
    {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    {κ : PartialPairing α} {i : α} :
    i ∈ κ.representatives ↔ κ i ≠ i ∧ i < κ i := by
  simp [representatives, representativesBy]

/-- Head-first strict order used only for the Option classification. -/
def optionHeadLT {α : Type*} [LT α] :
    Option α → Option α → Prop
  | none, some _ => True
  | some a, some b => a < b
  | _, _ => False

instance {α : Type*} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] :
    DecidableRel (optionHeadLT (α := α)) := by
  intro a b
  cases a <;> cases b <;> dsimp only [optionHeadLT] <;>
    infer_instance

theorem subtype_lt_iff_val_lt
    {α : Type*} [LT α] {p : α → Prop}
    (a b : Subtype p) :
    a < b ↔ a.1 < b.1 := by
  rfl

theorem representatives_optionFixed
    {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (κ : PartialPairing α) :
    (optionFixed κ).representativesBy optionHeadLT =
      κ.representatives.image some := by
  ext o
  cases o with
  | none =>
      simp [representatives, representativesBy, optionHeadLT,
        PartialPairing.pairSupport]
  | some i =>
      simp [representatives, representativesBy, optionHeadLT,
        PartialPairing.pairSupport]

theorem singles_optionFixed
    {α : Type*} [Fintype α] [DecidableEq α]
    (κ : PartialPairing α) :
    (optionFixed κ).singles = insert none (κ.singles.image some) := by
  ext o
  cases o with
  | none =>
      simp [PartialPairing.singles]
  | some i =>
      simp [PartialPairing.singles]

theorem representatives_optionPaired
    {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    (optionPaired j κ).representativesBy optionHeadLT =
      insert none (κ.representatives.image fun i => some i.1) := by
  ext o
  cases o with
  | none =>
      simp [representatives, representativesBy, optionHeadLT,
        PartialPairing.pairSupport]
  | some i =>
      by_cases hi : i = j
      · subst i
        simp [representatives, representativesBy, optionHeadLT,
          PartialPairing.pairSupport]
      · simp [representatives, representativesBy, optionHeadLT,
          PartialPairing.pairSupport, hi, Subtype.ext_iff]
        intro _
        rfl

theorem singles_optionPaired
    {α : Type*} [Fintype α] [DecidableEq α]
    (j : α) (κ : PartialPairing {i : α // i ≠ j}) :
    (optionPaired j κ).singles =
      κ.singles.image fun i => some i.1 := by
  ext o
  cases o with
  | none =>
      simp [PartialPairing.singles, optionPaired]
  | some i =>
      by_cases hi : i = j
      · subst i
        simp [PartialPairing.singles, optionPaired]
      · simp [PartialPairing.singles, optionPaired, hi,
          Subtype.ext_iff]

theorem singles_congr
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (κ : PartialPairing α) :
    (PartialPairing.congr e κ).singles = κ.singles.image e := by
  ext j
  simp only [PartialPairing.mem_singles, Finset.mem_image]
  constructor
  · intro h
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    apply e.injective
    simpa using h
  · rintro ⟨a, ha, rfl⟩
    simpa using congrArg e ha

theorem representativesBy_congr
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ltα : α → α → Prop) [DecidableRel ltα]
    (ltβ : β → β → Prop) [DecidableRel ltβ]
    (e : α ≃ β)
    (hlt : ∀ i j, ltβ (e i) (e j) ↔ ltα i j)
    (κ : PartialPairing α) :
    (PartialPairing.congr e κ).representativesBy ltβ =
      (κ.representativesBy ltα).image e := by
  ext j
  simp only [representativesBy, Finset.mem_image, Finset.mem_filter,
    PartialPairing.mem_pairSupport]
  constructor
  · rintro ⟨hne, horder⟩
    refine ⟨e.symm j, ⟨?_, ?_⟩, e.apply_symm_apply j⟩
    · intro hk
      apply hne
      rw [PartialPairing.congr_apply_apply, hk, e.apply_symm_apply]
    · apply (hlt (e.symm j) (κ (e.symm j))).mp
      simpa only [PartialPairing.congr_apply_apply,
        e.apply_symm_apply] using horder
  · rintro ⟨a, ⟨hne, horder⟩, rfl⟩
    simp only [PartialPairing.congr_apply_apply, e.symm_apply_apply]
    constructor
    · exact fun h => hne (e.injective h)
    · exact (hlt a (κ a)).mpr horder

/-- The increasing enumeration of all positions of a list except `p`. -/
def eraseIdxOrderIso {ι : Type*} (xs : List ι) (p : Fin xs.length) :
    Fin (xs.eraseIdx p).length ≃o {i : Fin xs.length // i ≠ p} := by
  cases xs with
  | nil => exact Fin.elim0 p
  | cons x xs =>
      exact
        (Fin.castOrderIso (by
          rw [List.length_eraseIdx_of_lt p.isLt]
          simp)).trans (finSuccAboveOrderIso p)

theorem get_eraseIdxOrderIso {ι : Type*} (xs : List ι)
    (p : Fin xs.length) (i : Fin (xs.eraseIdx p).length) :
    xs.get (eraseIdxOrderIso xs p i).1 = (xs.eraseIdx p).get i := by
  cases xs with
  | nil => exact Fin.elim0 p
  | cons x xs =>
      simp only [eraseIdxOrderIso, OrderIso.trans_apply,
        Fin.castOrderIso_apply, finSuccAboveOrderIso_apply,
        List.get_eq_getElem]
      rw [List.getElem_eraseIdx]
      unfold Fin.succAbove
      split_ifs with h
      · have hi : (i : ℕ) < (p : ℕ) := h
        rw [dif_pos hi]
        rfl
      · have hi : ¬(i : ℕ) < (p : ℕ) := h
        rw [dif_neg hi]
        rfl

theorem finSuccEquiv_symm_lt_iff (n : ℕ)
    (a b : Option (Fin n)) :
    (finSuccEquiv n).symm a < (finSuccEquiv n).symm b ↔
      optionHeadLT a b := by
  cases a <;> cases b <;> simp [optionHeadLT]

end PartialPairing

/-- One summand of the explicit Wick expansion, with the endpoint of each
two-cycle selected by an explicit strict relation. -/
def partialPairingWickWeightBy
    {α ι Ω : Type*} [Fintype α] [DecidableEq α]
    (lt : α → α → Prop) [DecidableRel lt]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : α → ι) (κ : PartialPairing α) (ω : Ω) : ℝ :=
  (∏ i ∈ κ.representativesBy lt, -C (v i) (v (κ i))) *
    ∏ i ∈ κ.singles, X (v i) ω

/-- One summand of the explicit Wick expansion on a linearly ordered
carrier. -/
def partialPairingWickWeight
    {α ι Ω : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : α → ι) (κ : PartialPairing α) (ω : Ω) : ℝ :=
  partialPairingWickWeightBy (· < ·) C X v κ ω

/-- Finite sum over every partial pairing, with representatives selected
by an explicit strict relation. -/
def explicitPartialPairingWickBy
    {α ι Ω : Type*} [Fintype α] [DecidableEq α]
    (lt : α → α → Prop) [DecidableRel lt]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : α → ι) (ω : Ω) : ℝ :=
  ∑ κ : PartialPairing α,
    partialPairingWickWeightBy lt C X v κ ω

/-- Finite sum over every partial pairing of the labelled carrier. -/
def explicitPartialPairingWick
    {α ι Ω : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : α → ι) (ω : Ω) : ℝ :=
  explicitPartialPairingWickBy (· < ·) C X v ω

theorem partialPairingWickWeightBy_congr
    {α β ι Ω : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ltα : α → α → Prop) [DecidableRel ltα]
    (ltβ : β → β → Prop) [DecidableRel ltβ]
    (e : α ≃ β)
    (hlt : ∀ i j, ltβ (e i) (e j) ↔ ltα i j)
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : β → ι) (κ : PartialPairing α) (ω : Ω) :
    partialPairingWickWeightBy ltβ C X v
        (PartialPairing.congr e κ) ω =
      partialPairingWickWeightBy ltα C X (v ∘ e) κ ω := by
  classical
  rw [partialPairingWickWeightBy, partialPairingWickWeightBy,
    PartialPairing.representativesBy_congr ltα ltβ e hlt κ,
    PartialPairing.singles_congr e κ,
    Finset.prod_image e.injective.injOn,
    Finset.prod_image e.injective.injOn]
  simp only [PartialPairing.congr_apply_apply, e.symm_apply_apply,
    Function.comp_apply]

theorem explicitPartialPairingWickBy_congr
    {α β ι Ω : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (ltα : α → α → Prop) [DecidableRel ltα]
    (ltβ : β → β → Prop) [DecidableRel ltβ]
    (e : α ≃ β)
    (hlt : ∀ i j, ltβ (e i) (e j) ↔ ltα i j)
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : β → ι) (ω : Ω) :
    explicitPartialPairingWickBy ltβ C X v ω =
      explicitPartialPairingWickBy ltα C X (v ∘ e) ω := by
  classical
  unfold explicitPartialPairingWickBy
  rw [← (PartialPairing.congr e).sum_comp
    (fun κ => partialPairingWickWeightBy ltβ C X v κ ω)]
  simp_rw [partialPairingWickWeightBy_congr ltα ltβ e hlt]

@[simp]
theorem partialPairingWickWeightBy_optionFixed
    {α ι Ω : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (x : ι) (v : α → ι) (κ : PartialPairing α) (ω : Ω) :
    partialPairingWickWeightBy PartialPairing.optionHeadLT C X
        (fun o => o.elim x v) (PartialPairing.optionFixed κ) ω =
      X x ω * partialPairingWickWeight C X v κ ω := by
  classical
  simp [partialPairingWickWeight, partialPairingWickWeightBy,
    PartialPairing.representatives,
    PartialPairing.representatives_optionFixed,
    PartialPairing.singles_optionFixed, Finset.prod_image]
  ring

@[simp]
theorem partialPairingWickWeightBy_optionPaired
    {α ι Ω : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (x : ι) (v : α → ι) (j : α)
    (κ : PartialPairing {i : α // i ≠ j}) (ω : Ω) :
    partialPairingWickWeightBy PartialPairing.optionHeadLT C X
        (fun o => o.elim x v) (PartialPairing.optionPaired j κ) ω =
      -C x (v j) *
        partialPairingWickWeight C X (fun i => v i.1) κ ω := by
  classical
  have hpair : ∀ i : {i : α // i ≠ j},
      ((PartialPairing.optionPaired j κ) (some i.1)).elim x v =
        v (κ i).1 := by
    intro i
    rw [PartialPairing.optionPaired_some_ne j κ i.1 i.2]
    rfl
  simp [partialPairingWickWeight, partialPairingWickWeightBy,
    PartialPairing.representatives,
    PartialPairing.representatives_optionPaired,
    PartialPairing.singles_optionPaired, Finset.prod_image, hpair]
  ring

/-- Splitting according to the partner of the distinguished `none`
index gives the creation--contraction recursion on `Option α`. -/
theorem explicitPartialPairingWickBy_option_recursion
    {α ι Ω : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (x : ι) (v : α → ι) (ω : Ω) :
    explicitPartialPairingWickBy PartialPairing.optionHeadLT C X
        (fun o => o.elim x v) ω =
      X x ω * explicitPartialPairingWick C X v ω -
        ∑ j : α, C x (v j) *
          explicitPartialPairingWick C X
            (fun i : {i : α // i ≠ j} => v i.1) ω := by
  classical
  unfold explicitPartialPairingWickBy
  rw [← (PartialPairing.optionHeadEquiv (α := α)).symm.sum_comp
    (fun κ =>
      partialPairingWickWeightBy PartialPairing.optionHeadLT C X
        (fun o => o.elim x v) κ ω)]
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [PartialPairing.optionHeadEquiv_symm_inl,
    PartialPairing.optionHeadEquiv_symm_inr]
  simp_rw [partialPairingWickWeightBy_optionFixed,
    partialPairingWickWeightBy_optionPaired]
  simp only [explicitPartialPairingWick, explicitPartialPairingWickBy]
  simp only [partialPairingWickWeight]
  simp_rw [← Finset.mul_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem explicitPartialPairingWick_compl_eq_eraseIdx
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (xs : List ι) (p : Fin xs.length) (ω : Ω) :
    explicitPartialPairingWick C X
        (fun i : {i : Fin xs.length // i ≠ p} => xs.get i.1) ω =
    explicitPartialPairingWick C X
        (fun i : Fin (xs.eraseIdx p).length =>
          (xs.eraseIdx p).get i) ω := by
  let e := PartialPairing.eraseIdxOrderIso xs p
  let ee : Fin (xs.eraseIdx p).length ≃
      {i : Fin xs.length // i ≠ p} := EquivLike.toEquiv e
  have horder : ∀ i j, ee i < ee j ↔ i < j :=
    fun _ _ => e.lt_iff_lt
  have hlabel :
      ((fun i : {i : Fin xs.length // i ≠ p} => xs.get i.1) ∘ ee) =
        fun i : Fin (xs.eraseIdx p).length =>
          (xs.eraseIdx p).get i := by
    funext i
    exact PartialPairing.get_eraseIdxOrderIso xs p i
  unfold explicitPartialPairingWick
  rw [explicitPartialPairingWickBy_congr (· < ·) (· < ·)
    ee horder C X]
  rw [hlabel]

/-- The standard finite-index version of the explicit partial-pairing
expansion for a labelled list. -/
def explicitPartialPairingWickList
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (xs : List ι) (ω : Ω) : ℝ :=
  explicitPartialPairingWick C X
    (fun i : Fin xs.length => xs.get i) ω

@[simp]
theorem explicitPartialPairingWickList_nil
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (ω : Ω) :
    explicitPartialPairingWickList C X [] ω = 1 := by
  letI : Unique (PartialPairing (Fin 0)) :=
    { default := PartialPairing.id
      uniq := fun κ => by
        apply PartialPairing.ext
        exact fun i => Fin.elim0 i }
  simp [explicitPartialPairingWickList, explicitPartialPairingWick,
    explicitPartialPairingWickBy, partialPairingWickWeightBy,
    PartialPairing.representativesBy, PartialPairing.pairSupport,
    PartialPairing.singles]

@[simp]
theorem explicitPartialPairingWickList_cons
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (x : ι) (xs : List ι) (ω : Ω) :
    explicitPartialPairingWickList C X (x :: xs) ω =
      X x ω * explicitPartialPairingWickList C X xs ω -
        ∑ j : Fin xs.length,
          C x (xs.get j) *
            explicitPartialPairingWickList C X (xs.eraseIdx j) ω := by
  let vFin : Fin (xs.length + 1) → ι :=
    fun i => (x :: xs).get i
  let vOpt : Option (Fin xs.length) → ι :=
    fun o => o.elim x (fun i => xs.get i)
  have hlabel : vFin ∘ (finSuccEquiv xs.length).symm = vOpt := by
    funext o
    cases o <;> simp [vFin, vOpt, Function.comp_apply]
  change explicitPartialPairingWick C X vFin ω = _
  unfold explicitPartialPairingWick
  rw [explicitPartialPairingWickBy_congr
    PartialPairing.optionHeadLT (· < ·)
    (finSuccEquiv xs.length).symm
    (PartialPairing.finSuccEquiv_symm_lt_iff xs.length) C X]
  rw [hlabel]
  rw [explicitPartialPairingWickBy_option_recursion]
  unfold explicitPartialPairingWickList
  simp_rw [explicitPartialPairingWick_compl_eq_eraseIdx]

/-- The explicit partial-pairing expansion satisfies the abstract
creation--contraction specification. -/
theorem explicitPartialPairingWickList_recursionLaw
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ) :
    WickRecursionLaw C X (explicitPartialPairingWickList C X) where
  empty := fun ω => explicitPartialPairingWickList_nil C X ω
  create_contract := by
    intro x xs ω
    rw [explicitPartialPairingWickList_cons]
    ring

/-- Generic Wick formula: the finite sum over partial pairings is exactly
the recursively normal-ordered polynomial. -/
theorem explicitPartialPairingWickList_eq_wickPolynomial
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (xs : List ι) :
    explicitPartialPairingWickList C X xs =
      wickPolynomial C X xs :=
  (explicitPartialPairingWickList_recursionLaw C X).eq_wickPolynomial xs

@[simp]
theorem explicitPartialPairingWickList_apply_eq_wickPolynomial
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (xs : List ι) (ω : Ω) :
    explicitPartialPairingWickList C X xs ω =
      wickPolynomial C X xs ω :=
  congrFun (explicitPartialPairingWickList_eq_wickPolynomial C X xs) ω

/-- The Wick formula with the explicit summation and weight visible in
the statement. -/
theorem sum_partialPairingWickWeight_eq_wickPolynomial
    {ι Ω : Type*} (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (xs : List ι) (ω : Ω) :
    (∑ κ : PartialPairing (Fin xs.length),
      partialPairingWickWeight C X
        (fun i : Fin xs.length => xs.get i) κ ω) =
      wickPolynomial C X xs ω := by
  simpa [explicitPartialPairingWickList, explicitPartialPairingWick,
    explicitPartialPairingWickBy, partialPairingWickWeight] using
      explicitPartialPairingWickList_apply_eq_wickPolynomial C X xs ω

end

end Anderson4D
