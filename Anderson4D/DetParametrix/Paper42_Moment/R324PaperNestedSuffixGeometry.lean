import Anderson4D.DetParametrix.Paper42_Moment.R324PaperTraceExteriorParts
import Anderson4D.DetParametrix.Paper42_Moment.R324NestedCrossResidualState

/-!
# Geometry of a nested residual suffix

Once an interval trace has been processed, all later shells together with
the final exterior cover exactly the exterior of that trace.  This is the
moving-carrier identity behind the inside-to-outside Step 3 induction.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- One shell followed by the exterior of its outer interval is exactly the
exterior of the inner interval. -/
theorem residualIntervalShell_union_exterior
    {n : ℕ} (active : Finset (Fin n))
    (previous next : Fin n × Fin n)
    (hcontains : LaterCrossCutIntervalContains previous next) :
    residualIntervalShell active previous next ∪
        residualIntervalExterior active next =
      residualIntervalExterior active previous := by
  classical
  have hsubset :
      residualIntervalTrace active previous ⊆
        residualIntervalTrace active next :=
    residualIntervalTrace_subset hcontains
  ext x
  simp only [residualIntervalShell, residualIntervalExterior,
    Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (⟨hxNext, hxNotPrevious⟩ | ⟨hxActive, hxNotNext⟩)
    · exact
        ⟨(relIcc_subset_active active next.1 next.2) hxNext,
          hxNotPrevious⟩
    · exact ⟨hxActive, fun hxPrevious => hxNotNext (hsubset hxPrevious)⟩
  · rintro ⟨hxActive, hxNotPrevious⟩
    by_cases hxNext : x ∈ residualIntervalTrace active next
    · exact Or.inl ⟨hxNext, hxNotPrevious⟩
    · exact Or.inr ⟨hxActive, hxNext⟩

/-- **Nested suffix carrier identity.**  Starting immediately outside
`previous`, the union of all later shells and the final exterior is exactly
the exterior of `previous`. -/
theorem finsetUnionList_nestedResidualShells_eq_exterior
    {n : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise
        LaterCrossCutIntervalContains) :
    finsetUnionList (nestedResidualShells active previous rest) =
      residualIntervalExterior active previous := by
  induction rest generalizing previous with
  | nil =>
      simp [nestedResidualShells, finsetUnionList]
  | cons next rest ih =>
      have hcons := List.pairwise_cons.mp hpair
      have hnext : LaterCrossCutIntervalContains previous next :=
        hcons.1 next (by simp)
      have htail :
          (next :: rest).Pairwise LaterCrossCutIntervalContains :=
        hcons.2
      simp only [nestedResidualShells, finsetUnionList]
      rw [ih next htail,
        residualIntervalShell_union_exterior active previous next hnext]

/-- Canonical-chain specialization for any literal suffix beginning at
`previous`.  This avoids exposing the later attach/filter enrichment of the
proof-relevant block schedule. -/
theorem finsetUnionList_nestedResidualShells_momentResidual_eq_exterior
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (pre : List (Fin (2 * m) × Fin (2 * m)))
    (previous : Fin (2 * m) × Fin (2 * m))
    (rest : List (Fin (2 * m) × Fin (2 * m)))
    (hchain :
      momentResidualIntervalChain κp κm π =
        pre ++ previous :: rest) :
    finsetUnionList
        (nestedResidualShells
          (momentResidualActive κp κm) previous rest) =
      residualIntervalExterior
        (momentResidualActive κp κm) previous := by
  have hfull :=
    momentResidualIntervalChain_pairwise_laterContains κp κm π
  rw [hchain] at hfull
  have hsuffix := hfull.drop (i := pre.length)
  have hpair :
      (previous :: rest).Pairwise
        LaterCrossCutIntervalContains := by
    simpa only [List.drop_left] using hsuffix
  exact finsetUnionList_nestedResidualShells_eq_exterior
    (momentResidualActive κp κm) previous rest hpair

/-! ## Half-carrier formulas and contiguity -/

/-- The left half of a genuine nested suffix is the active initial interval
strictly before the previous left endpoint. -/
theorem finsetUnionList_nestedResidualShells_filter_lt
    {n cut : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise LaterCrossCutIntervalContains)
    (hp1 : (previous.1 : ℕ) < cut)
    (hcutp2 : cut ≤ (previous.2 : ℕ)) :
    (finsetUnionList
        (nestedResidualShells active previous rest)).filter
          (fun i : Fin n => (i : ℕ) < cut) =
      active.filter fun i : Fin n => i < previous.1 := by
  rw [finsetUnionList_nestedResidualShells_eq_exterior
      active previous rest hpair,
    residualIntervalExterior_filter_lt active previous hp1 hcutp2]

/-- The right half is the active terminal interval strictly after the
previous right endpoint. -/
theorem finsetUnionList_nestedResidualShells_filter_ge
    {n cut : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise LaterCrossCutIntervalContains)
    (hp1 : (previous.1 : ℕ) < cut)
    (hcutp2 : cut ≤ (previous.2 : ℕ)) :
    (finsetUnionList
        (nestedResidualShells active previous rest)).filter
          (fun i : Fin n => cut ≤ (i : ℕ)) =
      active.filter fun i : Fin n => previous.2 < i := by
  rw [finsetUnionList_nestedResidualShells_eq_exterior
      active previous rest hpair,
    residualIntervalExterior_filter_ge active previous hp1 hcutp2]

/-- The left half of the nested suffix is order-connected relative to the
original active carrier. -/
theorem finsetUnionList_nestedResidualShells_filter_lt_ordConnectedWithin
    {n cut : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise LaterCrossCutIntervalContains)
    (hp1 : (previous.1 : ℕ) < cut)
    (hcutp2 : cut ≤ (previous.2 : ℕ)) :
    FinsetOrdConnectedWithin active
      ((finsetUnionList
        (nestedResidualShells active previous rest)).filter
          (fun i : Fin n => (i : ℕ) < cut)) := by
  rw [finsetUnionList_nestedResidualShells_eq_exterior
    active previous rest hpair]
  exact residualIntervalExterior_filter_lt_ordConnectedWithin
    active previous hp1 hcutp2

/-- Right-half relative order-connectedness. -/
theorem finsetUnionList_nestedResidualShells_filter_ge_ordConnectedWithin
    {n cut : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise LaterCrossCutIntervalContains)
    (hp1 : (previous.1 : ℕ) < cut)
    (hcutp2 : cut ≤ (previous.2 : ℕ)) :
    FinsetOrdConnectedWithin active
      ((finsetUnionList
        (nestedResidualShells active previous rest)).filter
          (fun i : Fin n => cut ≤ (i : ℕ))) := by
  rw [finsetUnionList_nestedResidualShells_eq_exterior
    active previous rest hpair]
  exact residualIntervalExterior_filter_ge_ordConnectedWithin
    active previous hp1 hcutp2

end Anderson4D
