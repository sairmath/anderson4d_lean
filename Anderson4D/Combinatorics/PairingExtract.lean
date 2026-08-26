import Mathlib
import Anderson4D.Combinatorics.Pairing

/-!
# L0 combinatorics: iterated extraction of fully paired subintervals

Endpoint-extraction layer for Def 3.1 of Deng–Shen (arXiv:2607.10105), node
**D-RI** (DESIGN §5.7bis): the renormalization iteratively removes the
smallest-then-leftmost fully paired subinterval, where after removals a
"subinterval" is contiguous **in the remaining index order**.

## Design

* We never change the index type: the remaining indices are a shrinking
  `active : Finset (Fin m)`.  The trace of `[a, b]` on `active` is `relIcc`;
  `IsRelFullyPaired κ active a b` is the relative variant of
  `IsFullyPairedOn κ (Finset.Icc a b)`.
* The Def 3.1(2) selector on the relative structure, `selectRel`, picks the
  candidate `(a, b)` minimizing the lexicographic triple
  `((relIcc active a b).card, a, b)`, encoded into `ℕ` by the mixed-radix key
  `candKey active a b = card * ((m+1) * (m+1)) + (a * (m+1) + b)` and selected
  via `Finset.min'` on the key image (`minCandKey`) plus `Finset.choose`
  (the key is injective, `candKey_inj`).
* The extraction recursion `extractAux` runs on fuel; each step removes the
  selected trace from `active`, which shrinks `active` by at least `2`
  (`IsRelFullyPaired.two_le_card`), so fuel `m` always reaches the
  no-candidate state (`extract_fuel_sufficient`, via the stateful variant
  `extractAuxS`).
-/

namespace Anderson4D

variable {m : ℕ}

/-! ## Relative intervals -/

/-- The trace of the interval `[a, b]` on the set `active` of remaining
indices: for the Def 3.1 iteration, "subinterval" means contiguous in the
remaining index order, i.e. a set of this form. -/
def relIcc (active : Finset (Fin m)) (a b : Fin m) : Finset (Fin m) :=
  active.filter fun i => a ≤ i ∧ i ≤ b

@[simp]
theorem mem_relIcc {active : Finset (Fin m)} {a b i : Fin m} :
    i ∈ relIcc active a b ↔ i ∈ active ∧ a ≤ i ∧ i ≤ b := by
  simp [relIcc]

theorem relIcc_subset_active (active : Finset (Fin m)) (a b : Fin m) :
    relIcc active a b ⊆ active :=
  Finset.filter_subset _ _

/-- Monotonicity of the trace in the active set. -/
theorem relIcc_mono {active active' : Finset (Fin m)} (h : active ⊆ active')
    (a b : Fin m) : relIcc active a b ⊆ relIcc active' a b :=
  Finset.filter_subset_filter _ h

/-- **Relative form of paper Def 2.3 / Def 3.1(2).**  The trace of `[a, b]` on
`active` is a fully paired subinterval of the remaining index order: both
endpoints are still active, `a ≤ b`, and the trace is fully paired. -/
def IsRelFullyPaired (κ : PartialPairing (Fin m)) (active : Finset (Fin m))
    (a b : Fin m) : Prop :=
  a ∈ active ∧ b ∈ active ∧ a ≤ b ∧ IsFullyPairedOn κ (relIcc active a b)

instance (κ : PartialPairing (Fin m)) (active : Finset (Fin m)) (a b : Fin m) :
    Decidable (IsRelFullyPaired κ active a b) :=
  decidable_of_iff
    (a ∈ active ∧ b ∈ active ∧ a ≤ b ∧ IsFullyPairedOn κ (relIcc active a b))
    Iff.rfl

namespace IsRelFullyPaired

variable {κ : PartialPairing (Fin m)} {active : Finset (Fin m)} {a b : Fin m}

theorem left_mem (h : IsRelFullyPaired κ active a b) : a ∈ active := h.1

theorem right_mem (h : IsRelFullyPaired κ active a b) : b ∈ active := h.2.1

theorem le (h : IsRelFullyPaired κ active a b) : a ≤ b := h.2.2.1

theorem isFullyPairedOn (h : IsRelFullyPaired κ active a b) :
    IsFullyPairedOn κ (relIcc active a b) := h.2.2.2

theorem left_mem_relIcc (h : IsRelFullyPaired κ active a b) :
    a ∈ relIcc active a b :=
  mem_relIcc.mpr ⟨h.left_mem, le_refl a, h.le⟩

theorem right_mem_relIcc (h : IsRelFullyPaired κ active a b) :
    b ∈ relIcc active a b :=
  mem_relIcc.mpr ⟨h.right_mem, h.le, le_refl b⟩

/-- A relative fully paired interval contains at least one whole pair:
its trace has at least two elements.  This is the engine of the fuel bound
for the extraction recursion. -/
theorem two_le_card (h : IsRelFullyPaired κ active a b) :
    2 ≤ (relIcc active a b).card := by
  have ha := h.left_mem_relIcc
  have hka : κ a ∈ relIcc active a b := h.isFullyPairedOn.apply_mem ha
  have hne : κ a ≠ a := h.isFullyPairedOn.ne_of_mem ha
  calc 2 = ({a, κ a} : Finset (Fin m)).card := (Finset.card_pair hne.symm).symm
    _ ≤ (relIcc active a b).card :=
        Finset.card_le_card
          (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hka))

end IsRelFullyPaired

/-! ## The relative selector

Among all `(a, b)` with `IsRelFullyPaired κ active a b`, select the one with
lexicographically minimal `((relIcc active a b).card, a, b)`, via the
mixed-radix embedding `candKey` into `ℕ` and `Finset.min'`. -/

section RadixArithmetic

/-- Mixed-radix comparison, leading digit: if `r₁, r₂ < N` then
`c₁ * N + r₁ ≤ c₂ * N + r₂` forces `c₁ ≤ c₂`. -/
theorem radix_le_left {N c₁ c₂ r₁ r₂ : ℕ} (hr₂ : r₂ < N)
    (h : c₁ * N + r₁ ≤ c₂ * N + r₂) : c₁ ≤ c₂ := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : c₂ * N + N ≤ c₁ * N := by
    have h2 := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hlt)
    rwa [Nat.succ_mul] at h2
  have h3 : c₂ * N + r₂ < c₂ * N + N := Nat.add_lt_add_left hr₂ _
  exact absurd ((h3.trans_le h1).trans_le ((Nat.le_add_right _ r₁).trans h))
    (lt_irrefl _)

/-- Mixed-radix decomposition is unique: equal keys with in-range remainders
have equal digits. -/
theorem radix_eq {N c₁ c₂ r₁ r₂ : ℕ} (hr₁ : r₁ < N) (hr₂ : r₂ < N)
    (h : c₁ * N + r₁ = c₂ * N + r₂) : c₁ = c₂ ∧ r₁ = r₂ := by
  have hc : c₁ = c₂ := le_antisymm (radix_le_left hr₂ h.le) (radix_le_left hr₁ h.ge)
  subst hc
  exact ⟨rfl, Nat.add_left_cancel h⟩

end RadixArithmetic

/-- The mixed-radix selection key of a candidate `(a, b)`:
`(relIcc active a b).card * ((m+1) * (m+1)) + (a * (m+1) + b)`, i.e. the
lexicographic triple `(card, a, b)` in base `m + 1`. -/
def candKey (active : Finset (Fin m)) (a b : Fin m) : ℕ :=
  (relIcc active a b).card * ((m + 1) * (m + 1)) + ((a : ℕ) * (m + 1) + (b : ℕ))

/-- The inner two digits of `candKey` stay below the outer radix. -/
theorem candKey_inner_lt (a b : Fin m) :
    (a : ℕ) * (m + 1) + (b : ℕ) < (m + 1) * (m + 1) :=
  calc (a : ℕ) * (m + 1) + (b : ℕ)
      < (a : ℕ) * (m + 1) + (m + 1) :=
        Nat.add_lt_add_left (Nat.lt_succ_of_lt b.isLt) _
    _ = ((a : ℕ) + 1) * (m + 1) := by ring
    _ ≤ (m + 1) * (m + 1) :=
        mul_le_mul_left (Nat.succ_le_of_lt (Nat.lt_succ_of_lt a.isLt)) _

/-- The key determines the candidate. -/
theorem candKey_inj {active : Finset (Fin m)} {a₁ b₁ a₂ b₂ : Fin m}
    (h : candKey active a₁ b₁ = candKey active a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  unfold candKey at h
  obtain ⟨-, hinner⟩ := radix_eq (candKey_inner_lt a₁ b₁) (candKey_inner_lt a₂ b₂) h
  obtain ⟨ha, hb⟩ := radix_eq (Nat.lt_succ_of_lt b₁.isLt)
    (Nat.lt_succ_of_lt b₂.isLt) hinner
  exact ⟨Fin.ext ha, Fin.ext hb⟩

/-- The candidates of the relative selector: endpoint pairs of relative fully
paired intervals of `active`. -/
def relCands (κ : PartialPairing (Fin m)) (active : Finset (Fin m)) :
    Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => IsRelFullyPaired κ active p.1 p.2

@[simp]
theorem mem_relCands {κ : PartialPairing (Fin m)} {active : Finset (Fin m)}
    {p : Fin m × Fin m} :
    p ∈ relCands κ active ↔ IsRelFullyPaired κ active p.1 p.2 := by
  simp [relCands]

theorem relCands_nonempty_iff {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} :
    (relCands κ active).Nonempty ↔ ∃ a b, IsRelFullyPaired κ active a b := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, mem_relCands.mp hp⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨(a, b), mem_relCands.mpr hab⟩

/-- The minimal selection key over all candidates. -/
def minCandKey (κ : PartialPairing (Fin m)) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) : ℕ :=
  ((relCands κ active).image fun p => candKey active p.1 p.2).min'
    ((relCands_nonempty_iff.mpr h).image _)

theorem exists_unique_minKey_cand (κ : PartialPairing (Fin m))
    (active : Finset (Fin m)) (h : ∃ a b, IsRelFullyPaired κ active a b) :
    ∃! p, p ∈ relCands κ active ∧
      candKey active p.1 p.2 = minCandKey κ active h := by
  obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp
    (Finset.min'_mem ((relCands κ active).image fun p => candKey active p.1 p.2)
      ((relCands_nonempty_iff.mpr h).image _))
  refine ⟨p, ⟨hp, hpk⟩, ?_⟩
  rintro q ⟨-, hqk⟩
  obtain ⟨h1, h2⟩ := candKey_inj (hqk.trans hpk.symm)
  exact Prod.ext h1 h2

/-- **Relative Def 3.1(2) selector.**  The candidate `(a, b)` with
lexicographically minimal `((relIcc active a b).card, a, b)`. -/
def selectRel (κ : PartialPairing (Fin m)) (active : Finset (Fin m))
    (h : ∃ a b, IsRelFullyPaired κ active a b) : Fin m × Fin m :=
  Finset.choose _ _ (exists_unique_minKey_cand κ active h)

theorem selectRel_mem_relCands (κ : PartialPairing (Fin m))
    (active : Finset (Fin m)) (h : ∃ a b, IsRelFullyPaired κ active a b) :
    selectRel κ active h ∈ relCands κ active :=
  Finset.choose_mem _ _ _

/-- The selected pair is a genuine candidate. -/
theorem selectRel_isRelFullyPaired (κ : PartialPairing (Fin m))
    (active : Finset (Fin m)) (h : ∃ a b, IsRelFullyPaired κ active a b) :
    IsRelFullyPaired κ active (selectRel κ active h).1 (selectRel κ active h).2 :=
  mem_relCands.mp (selectRel_mem_relCands κ active h)

theorem candKey_selectRel (κ : PartialPairing (Fin m))
    (active : Finset (Fin m)) (h : ∃ a b, IsRelFullyPaired κ active a b) :
    candKey active (selectRel κ active h).1 (selectRel κ active h).2 =
      minCandKey κ active h :=
  Finset.choose_property
    (fun p : Fin m × Fin m => candKey active p.1 p.2 = minCandKey κ active h)
    (relCands κ active) (exists_unique_minKey_cand κ active h)

/-- Key minimality of the selected pair over all candidates. -/
theorem candKey_selectRel_le {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (h : ∃ a b, IsRelFullyPaired κ active a b)
    {a b : Fin m} (hab : IsRelFullyPaired κ active a b) :
    candKey active (selectRel κ active h).1 (selectRel κ active h).2 ≤
      candKey active a b := by
  rw [candKey_selectRel]
  exact Finset.min'_le _ _
    (Finset.mem_image_of_mem _ ((mem_relCands (p := (a, b))).mpr hab))

/-- Selector spec, first component of the lexicographic order: the selected
trace has minimal cardinality among all candidates. -/
theorem selectRel_card_le {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (h : ∃ a b, IsRelFullyPaired κ active a b)
    {a b : Fin m} (hab : IsRelFullyPaired κ active a b) :
    (relIcc active (selectRel κ active h).1 (selectRel κ active h).2).card ≤
      (relIcc active a b).card := by
  have hle := candKey_selectRel_le h hab
  unfold candKey at hle
  exact radix_le_left (candKey_inner_lt a b) hle

/-- Selector spec, second component: among candidates of the minimal trace
cardinality, the selected left endpoint is leftmost. -/
theorem selectRel_fst_le {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (h : ∃ a b, IsRelFullyPaired κ active a b)
    {a b : Fin m} (hab : IsRelFullyPaired κ active a b)
    (hcard : (relIcc active (selectRel κ active h).1
        (selectRel κ active h).2).card = (relIcc active a b).card) :
    (selectRel κ active h).1 ≤ a := by
  have hle := candKey_selectRel_le h hab
  unfold candKey at hle
  rw [hcard] at hle
  have hinner := le_of_add_le_add_left hle
  exact Fin.le_def.mpr
    (radix_le_left (Nat.lt_succ_of_lt b.isLt) hinner)

/-- Selector spec, third component: among candidates of minimal trace
cardinality and minimal left endpoint, the selected right endpoint is
minimal. -/
theorem selectRel_snd_le {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (h : ∃ a b, IsRelFullyPaired κ active a b)
    {a b : Fin m} (hab : IsRelFullyPaired κ active a b)
    (hcard : (relIcc active (selectRel κ active h).1
        (selectRel κ active h).2).card = (relIcc active a b).card)
    (hfst : (selectRel κ active h).1 = a) :
    (selectRel κ active h).2 ≤ b := by
  have hle := candKey_selectRel_le h hab
  unfold candKey at hle
  rw [hcard, hfst] at hle
  have hinner := le_of_add_le_add_left hle
  exact Fin.le_def.mpr (le_of_add_le_add_left hinner)

/-! ## The extraction recursion (paper Def 3.1, node D-RI) -/

/-- Fuel recursion implementing the Def 3.1 iteration: while a relative fully
paired interval exists in `active`, extract the selected endpoint pair and
remove its trace from `active`. -/
def extractAux (κ : PartialPairing (Fin m)) :
    ℕ → Finset (Fin m) → List (Fin m × Fin m)
  | 0, _ => []
  | fuel + 1, active =>
    if h : ∃ a b, IsRelFullyPaired κ active a b then
      selectRel κ active h ::
        extractAux κ fuel
          (active \ relIcc active (selectRel κ active h).1 (selectRel κ active h).2)
    else []

@[simp]
theorem extractAux_zero (κ : PartialPairing (Fin m)) (active : Finset (Fin m)) :
    extractAux κ 0 active = [] := rfl

/-- Raw recursion equation at successor fuel. -/
theorem extractAux_succ (κ : PartialPairing (Fin m)) (fuel : ℕ)
    (active : Finset (Fin m)) :
    extractAux κ (fuel + 1) active =
      if h : ∃ a b, IsRelFullyPaired κ active a b then
        selectRel κ active h ::
          extractAux κ fuel
            (active \ relIcc active (selectRel κ active h).1 (selectRel κ active h).2)
      else [] := rfl

/-- Recursion equation, candidate case. -/
@[simp]
theorem extractAux_succ_pos {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (fuel : ℕ)
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    extractAux κ (fuel + 1) active =
      selectRel κ active h ::
        extractAux κ fuel
          (active \ relIcc active (selectRel κ active h).1 (selectRel κ active h).2) := by
  rw [extractAux_succ, dif_pos h]

/-- Recursion equation, no-candidate case. -/
@[simp]
theorem extractAux_succ_neg {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (fuel : ℕ)
    (h : ¬∃ a b, IsRelFullyPaired κ active a b) :
    extractAux κ (fuel + 1) active = [] := by
  rw [extractAux_succ, dif_neg h]

theorem extractAux_nil_of_no_candidate {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (fuel : ℕ)
    (h : ¬∃ a b, IsRelFullyPaired κ active a b) :
    extractAux κ fuel active = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => exact extractAux_succ_neg fuel h

/-- **Paper Def 3.1 (node D-RI).**  The list of endpoint pairs of the
successively removed fully paired subintervals, starting from all of `Fin m`;
fuel `m` always suffices (`extract_fuel_sufficient`). -/
def extract (κ : PartialPairing (Fin m)) : List (Fin m × Fin m) :=
  extractAux κ m Finset.univ

/-- Step invariant: every extracted pair has both endpoints in the active set
of its step (hence in the initial one), and is ordered. -/
theorem extractAux_mem (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m), ∀ p ∈ extractAux κ fuel active,
      p.1 ∈ active ∧ p.2 ∈ active ∧ p.1 ≤ p.2 := by
  induction fuel with
  | zero => intro active p hp; simp at hp
  | succ fuel ih =>
    intro active p hp
    by_cases h : ∃ a b, IsRelFullyPaired κ active a b
    · rw [extractAux_succ_pos fuel h] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have hs := selectRel_isRelFullyPaired κ active h
        exact ⟨hs.left_mem, hs.right_mem, hs.le⟩
      · obtain ⟨h1, h2, h3⟩ := ih _ p hp
        exact ⟨Finset.sdiff_subset h1, Finset.sdiff_subset h2, h3⟩
    · rw [extractAux_succ_neg fuel h] at hp
      simp at hp

/-- Weak extraction spec: every extracted pair is ordered. -/
theorem extract_spec (κ : PartialPairing (Fin m)) :
    ∀ p ∈ extract κ, p.1 ≤ p.2 :=
  fun p hp => (extractAux_mem κ m Finset.univ p hp).2.2

/-- Each extraction step shrinks the active set by at least two elements. -/
theorem card_sdiff_relIcc_add_two_le {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} {a b : Fin m}
    (h : IsRelFullyPaired κ active a b) :
    (active \ relIcc active a b).card + 2 ≤ active.card := by
  have h1 : (active \ relIcc active a b).card + (relIcc active a b).card =
      active.card :=
    Finset.card_sdiff_add_card_eq_card (relIcc_subset_active active a b)
  have h2 := h.two_le_card
  omega

/-! ## The stateful recursion and fuel adequacy -/

/-- Stateful variant of `extractAux`, additionally returning the final active
set; used to state fuel adequacy (`extract_fuel_sufficient`). -/
def extractAuxS (κ : PartialPairing (Fin m)) :
    ℕ → Finset (Fin m) → List (Fin m × Fin m) × Finset (Fin m)
  | 0, active => ([], active)
  | fuel + 1, active =>
    if h : ∃ a b, IsRelFullyPaired κ active a b then
      let r := extractAuxS κ fuel
        (active \ relIcc active (selectRel κ active h).1 (selectRel κ active h).2)
      (selectRel κ active h :: r.1, r.2)
    else ([], active)

@[simp]
theorem extractAuxS_zero (κ : PartialPairing (Fin m))
    (active : Finset (Fin m)) : extractAuxS κ 0 active = ([], active) := rfl

/-- Recursion equation for `extractAuxS`, candidate case. -/
@[simp]
theorem extractAuxS_succ_pos {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (fuel : ℕ)
    (h : ∃ a b, IsRelFullyPaired κ active a b) :
    extractAuxS κ (fuel + 1) active =
      (selectRel κ active h ::
          (extractAuxS κ fuel (active \ relIcc active (selectRel κ active h).1
            (selectRel κ active h).2)).1,
        (extractAuxS κ fuel (active \ relIcc active (selectRel κ active h).1
          (selectRel κ active h).2)).2) := by
  rw [extractAuxS]
  rw [dif_pos h]

/-- Recursion equation for `extractAuxS`, no-candidate case. -/
@[simp]
theorem extractAuxS_succ_neg {κ : PartialPairing (Fin m)}
    {active : Finset (Fin m)} (fuel : ℕ)
    (h : ¬∃ a b, IsRelFullyPaired κ active a b) :
    extractAuxS κ (fuel + 1) active = ([], active) := by
  rw [extractAuxS]
  rw [dif_neg h]

/-- The extracted list of the stateful recursion is `extractAux`. -/
theorem extractAuxS_fst (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      (extractAuxS κ fuel active).1 = extractAux κ fuel active := by
  induction fuel with
  | zero => intro active; rfl
  | succ fuel ih =>
    intro active
    by_cases h : ∃ a b, IsRelFullyPaired κ active a b
    · rw [extractAuxS_succ_pos fuel h, extractAux_succ_pos fuel h]
      dsimp only
      rw [ih]
    · rw [extractAuxS_succ_neg fuel h, extractAux_succ_neg fuel h]

/-- Fuel adequacy, general form: if `active.card ≤ 2 * fuel + 1` then the
recursion reaches the no-candidate state (each step removes at least two
elements, `card_sdiff_relIcc_add_two_le`). -/
theorem extractAuxS_no_candidate (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m), active.card ≤ 2 * fuel + 1 →
      ¬∃ a b, IsRelFullyPaired κ (extractAuxS κ fuel active).2 a b := by
  induction fuel with
  | zero =>
    rintro active hcard ⟨a, b, hab⟩
    have h4 : (extractAuxS κ 0 active).2 = active := rfl
    rw [h4] at hab
    have h2 := hab.two_le_card
    have h3 := Finset.card_le_card (relIcc_subset_active active a b)
    omega
  | succ fuel ih =>
    intro active hcard
    by_cases h : ∃ a b, IsRelFullyPaired κ active a b
    · rw [extractAuxS_succ_pos fuel h]
      have hshrink := card_sdiff_relIcc_add_two_le
        (selectRel_isRelFullyPaired κ active h)
      exact ih _ (by omega)
    · rw [extractAuxS_succ_neg fuel h]
      exact h

/-- The active set remaining after the extraction loop (fuel `m`,
initial state `Finset.univ`). -/
def finalActive (κ : PartialPairing (Fin m)) : Finset (Fin m) :=
  (extractAuxS κ m Finset.univ).2

theorem extract_eq_extractAuxS_fst (κ : PartialPairing (Fin m)) :
    extract κ = (extractAuxS κ m Finset.univ).1 :=
  (extractAuxS_fst κ m Finset.univ).symm

/-- **Fuel adequacy.**  Fuel `m` reaches the terminal state of the Def 3.1
iteration: no relative fully paired interval survives in `finalActive`. -/
theorem extract_fuel_sufficient (κ : PartialPairing (Fin m)) :
    ¬∃ a b, IsRelFullyPaired κ (finalActive κ) a b := by
  apply extractAuxS_no_candidate
  rw [Finset.card_univ, Fintype.card_fin]
  omega

/-! ## Endpoint sets for the closed formulas -/

/-- The selected right endpoint lies in the removed trace, so it never
reappears: the extracted right endpoints are pairwise distinct. -/
theorem extractAux_map_snd_nodup (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      ((extractAux κ fuel active).map Prod.snd).Nodup := by
  induction fuel with
  | zero => intro active; simp
  | succ fuel ih =>
    intro active
    by_cases h : ∃ a b, IsRelFullyPaired κ active a b
    · rw [extractAux_succ_pos fuel h, List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih _⟩
      obtain ⟨q, hq, hq2⟩ := List.mem_map.mp hmem
      have hmemq := (extractAux_mem κ fuel _ q hq).2.1
      rw [Finset.mem_sdiff] at hmemq
      refine hmemq.2 ?_
      rw [show q.2 = (selectRel κ active h).2 from hq2]
      exact (selectRel_isRelFullyPaired κ active h).right_mem_relIcc
    · rw [extractAux_succ_neg fuel h]
      simp

/-- Left analogue: the extracted left endpoints are pairwise distinct. -/
theorem extractAux_map_fst_nodup (κ : PartialPairing (Fin m)) (fuel : ℕ) :
    ∀ active : Finset (Fin m),
      ((extractAux κ fuel active).map Prod.fst).Nodup := by
  induction fuel with
  | zero => intro active; simp
  | succ fuel ih =>
    intro active
    by_cases h : ∃ a b, IsRelFullyPaired κ active a b
    · rw [extractAux_succ_pos fuel h, List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, ih _⟩
      obtain ⟨q, hq, hq2⟩ := List.mem_map.mp hmem
      have hmemq := (extractAux_mem κ fuel _ q hq).1
      rw [Finset.mem_sdiff] at hmemq
      refine hmemq.2 ?_
      rw [show q.1 = (selectRel κ active h).1 from hq2]
      exact (selectRel_isRelFullyPaired κ active h).left_mem_relIcc
    · rw [extractAux_succ_neg fuel h]
      simp

theorem extract_map_snd_nodup (κ : PartialPairing (Fin m)) :
    ((extract κ).map Prod.snd).Nodup :=
  extractAux_map_snd_nodup κ m Finset.univ

theorem extract_map_fst_nodup (κ : PartialPairing (Fin m)) :
    ((extract κ).map Prod.fst).Nodup :=
  extractAux_map_fst_nodup κ m Finset.univ

/-- The right endpoints `b_i` of the extracted intervals (input to the closed
formulas of §4.1). -/
def rightEndpoints (κ : PartialPairing (Fin m)) : Finset (Fin m) :=
  ((extract κ).map Prod.snd).toFinset

/-- The left endpoints `a_i` of the extracted intervals. -/
def leftEndpoints (κ : PartialPairing (Fin m)) : Finset (Fin m) :=
  ((extract κ).map Prod.fst).toFinset

theorem rightEndpoints_card_eq_length (κ : PartialPairing (Fin m)) :
    (rightEndpoints κ).card = (extract κ).length := by
  rw [rightEndpoints, List.toFinset_card_of_nodup (extract_map_snd_nodup κ),
    List.length_map]

theorem leftEndpoints_card_eq_length (κ : PartialPairing (Fin m)) :
    (leftEndpoints κ).card = (extract κ).length := by
  rw [leftEndpoints, List.toFinset_card_of_nodup (extract_map_fst_nodup κ),
    List.length_map]

/-! ## Sanity checks on small cases -/

-- The swap pairing of `Fin 2` (`Fin.rev`): one extraction step removing the
-- whole interval.
#guard extract (⟨Fin.rev, Fin.rev_involutive⟩ : PartialPairing (Fin 2)) = [(0, 1)]

-- The identity pairing (all singles): nothing to extract.
#guard extract (PartialPairing.id : PartialPairing (Fin 2)) = []
#guard extract (PartialPairing.id : PartialPairing (Fin 3)) = []

-- The nested pairing 0↔3, 1↔2 of `Fin 4`: first the inner pair (1,2) is
-- removed, then {0, 3} is contiguous *in the remaining index order* and is
-- removed as the relative interval (0,3).
#guard extract (⟨Fin.rev, Fin.rev_involutive⟩ : PartialPairing (Fin 4)) =
  [(1, 2), (0, 3)]
#guard (rightEndpoints (⟨Fin.rev, Fin.rev_involutive⟩ : PartialPairing (Fin 4))) =
  {2, 3}

-- Kernel-checked versions (`decide`, no `native_decide`).
example :
    extract (⟨Fin.rev, Fin.rev_involutive⟩ : PartialPairing (Fin 2)) = [(0, 1)] := by
  decide
example : extract (PartialPairing.id : PartialPairing (Fin 2)) = [] := by decide

end Anderson4D
