import Anderson4D.DetParametrix.Core.CrossCutIntervals

/-!
# The residual interval chain in the doubled moment reduction

This file packages the fully paired proper subintervals which remain
after the two within-half extraction loops in paper §4.2 Step 2.
`CrossCutIntervals.lean` proves that distinct residual intervals are
strictly nested.  Here they are collected into a finite set and a
canonical inside-to-outside list, preparing the successive collapse in
Step 3.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- All relative fully paired intervals of the doubled residual carrier. -/
def momentResidualFullyPairedIntervals
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Finset (Fin (2 * m) × Fin (2 * m)) :=
  Finset.univ.filter fun p =>
    IsRelFullyPaired (momentCombinedPairing κp κm π)
      (momentResidualActive κp κm) p.1 p.2

@[simp]
theorem mem_momentResidualFullyPairedIntervals
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p : Fin (2 * m) × Fin (2 * m)} :
    p ∈ momentResidualFullyPairedIntervals κp κm π ↔
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) p.1 p.2 := by
  simp [momentResidualFullyPairedIntervals]

/-- The proper residual intervals reduced before the final primitive
block.  Properness is relative to the sparse active carrier, before the
paper renames its elements consecutively. -/
def momentResidualProperIntervals
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Finset (Fin (2 * m) × Fin (2 * m)) :=
  (momentResidualFullyPairedIntervals κp κm π).filter fun p =>
    relIcc (momentResidualActive κp κm) p.1 p.2 ≠
      momentResidualActive κp κm

@[simp]
theorem mem_momentResidualProperIntervals
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p : Fin (2 * m) × Fin (2 * m)} :
    p ∈ momentResidualProperIntervals κp κm π ↔
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) p.1 p.2 ∧
      relIcc (momentResidualActive κp κm) p.1 p.2 ≠
        momentResidualActive κp κm := by
  simp [momentResidualProperIntervals]

/-- Every proper residual interval straddles the central cut. -/
theorem momentResidualProperInterval_straddlesCut
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p : Fin (2 * m) × Fin (2 * m)}
    (hp : p ∈ momentResidualProperIntervals κp κm π) :
    IntervalStraddlesCut m p :=
  (mem_momentResidualProperIntervals.mp hp).1
    |>.momentResidualActive_straddlesCut

/-- Distinct proper residual intervals are strictly nested at both
endpoints. -/
theorem momentResidualProperIntervals_strictlyNested
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p q : Fin (2 * m) × Fin (2 * m)}
    (hp : p ∈ momentResidualProperIntervals κp κm π)
    (hq : q ∈ momentResidualProperIntervals κp κm π)
    (hpq : p ≠ q) :
    (p.1 < q.1 ∧ q.2 < p.2) ∨
      (q.1 < p.1 ∧ p.2 < q.2) :=
  (mem_momentResidualProperIntervals.mp hp).1
    |>.momentResidualActive_strictlyNested
      (mem_momentResidualProperIntervals.mp hq).1 hpq

/-- Canonical inside-to-outside ordering.  The ordinary lexicographic
sort lists the strictly nested intervals outside-to-inside because left
endpoints increase inward, so the list is reversed. -/
def momentResidualIntervalChain
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    List (Fin (2 * m) × Fin (2 * m)) :=
  ((momentResidualProperIntervals κp κm π).sort
    (Prod.Lex (· < ·) (· ≤ ·))).reverse

@[simp]
theorem mem_momentResidualIntervalChain
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p : Fin (2 * m) × Fin (2 * m)} :
    p ∈ momentResidualIntervalChain κp κm π ↔
      p ∈ momentResidualProperIntervals κp κm π := by
  rw [momentResidualIntervalChain, List.mem_reverse,
    Finset.mem_sort (Prod.Lex (· < ·) (· ≤ ·))]

theorem momentResidualIntervalChain_nodup
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentResidualIntervalChain κp κm π).Nodup := by
  unfold momentResidualIntervalChain
  rw [List.nodup_reverse]
  exact Finset.sort_nodup
    (momentResidualProperIntervals κp κm π)
      (Prod.Lex (· < ·) (· ≤ ·))

private theorem List.Pairwise.imp_of_mem_of_nodup
    {α : Type*} {R S : α → α → Prop} {l : List α}
    (hR : l.Pairwise R)
    (hnodup : l.Nodup)
    (himp :
      ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b → S a b) :
    l.Pairwise S := by
  induction l with
  | nil =>
      exact List.Pairwise.nil
  | cons a l ih =>
      rw [List.pairwise_cons] at hR ⊢
      rw [List.nodup_cons] at hnodup
      constructor
      · intro b hb
        exact himp a (by simp) b (by simp [hb])
          (fun hab => hnodup.1 (hab ▸ hb))
          (hR.1 b hb)
      · exact ih hR.2 hnodup.2 fun b hb c hc hbc hbcR =>
          himp b (by simp [hb]) c (by simp [hc]) hbc hbcR

/-- The canonical chain is ordered exactly as the successive Step 3
collapses: every later interval strictly contains every earlier one. -/
theorem momentResidualIntervalChain_pairwise_laterContains
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentResidualIntervalChain κp κm π).Pairwise
      LaterCrossCutIntervalContains := by
  let s := momentResidualProperIntervals κp κm π
  have hlex :
      (momentResidualIntervalChain κp κm π).Pairwise
        (fun p q =>
          Prod.Lex (· < ·) (· ≤ ·) q p) := by
    unfold momentResidualIntervalChain
    exact
      (Finset.pairwise_sort s
        (Prod.Lex (· < ·) (· ≤ ·))).reverse
  apply List.Pairwise.imp_of_mem_of_nodup hlex
    (momentResidualIntervalChain_nodup κp κm π)
  intro p hp q hq hpq hpqLex
  have hp' :
      p ∈ momentResidualProperIntervals κp κm π :=
    mem_momentResidualIntervalChain.mp hp
  have hq' :
      q ∈ momentResidualProperIntervals κp κm π :=
    mem_momentResidualIntervalChain.mp hq
  rcases
      momentResidualProperIntervals_strictlyNested
        hp' hq' hpq with houter | hinner
  · exfalso
    rcases Prod.lex_iff.mp hpqLex with hqp | ⟨heq, _⟩
    · exact (not_lt_of_ge houter.1.le) hqp
    · exact (ne_of_lt houter.1) heq.symm
  · exact hinner

/-! ## Closed shells between successive residual intervals -/

/-- The active trace of an endpoint interval. -/
def residualIntervalTrace
    {n : ℕ} (active : Finset (Fin n))
    (p : Fin n × Fin n) : Finset (Fin n) :=
  relIcc active p.1 p.2

theorem residualIntervalTrace_subset
    {n : ℕ} {active : Finset (Fin n)}
    {p q : Fin n × Fin n}
    (h : LaterCrossCutIntervalContains p q) :
    residualIntervalTrace active p ⊆
      residualIntervalTrace active q := by
  intro x hx
  have hx' := mem_relIcc.mp hx
  exact mem_relIcc.mpr
    ⟨hx'.1, h.1.le.trans hx'.2.1,
      hx'.2.2.trans h.2.le⟩

/-- The new closed shell exposed when the collapse expands from an inner
interval `p` to the next outer interval `q`. -/
def residualIntervalShell
    {n : ℕ} (active : Finset (Fin n))
    (p q : Fin n × Fin n) : Finset (Fin n) :=
  residualIntervalTrace active q \
    residualIntervalTrace active p

/-- A shell between two fully paired intervals is again fully paired. -/
theorem residualIntervalShell_isFullyPairedOn
    {n : ℕ} {κ : PartialPairing (Fin n)}
    {active : Finset (Fin n)}
    {p q : Fin n × Fin n}
    (hp : IsRelFullyPaired κ active p.1 p.2)
    (hq : IsRelFullyPaired κ active q.1 q.2) :
    IsFullyPairedOn κ
      (residualIntervalShell active p q) :=
  hq.isFullyPairedOn.sdiff hp.isFullyPairedOn

/-- Strict containment makes every successive shell nonempty. -/
theorem residualIntervalShell_nonempty
    {n : ℕ} {κ : PartialPairing (Fin n)}
    {active : Finset (Fin n)}
    {p q : Fin n × Fin n}
    (_hp : IsRelFullyPaired κ active p.1 p.2)
    (hq : IsRelFullyPaired κ active q.1 q.2)
    (h : LaterCrossCutIntervalContains p q) :
    (residualIntervalShell active p q).Nonempty := by
  refine ⟨q.1, Finset.mem_sdiff.mpr
    ⟨hq.left_mem_relIcc, ?_⟩⟩
  intro hqInner
  exact (not_le_of_gt h.1)
    (mem_relIcc.mp hqInner).2.1

/-- An inner trace together with its next shell is exactly the outer
trace. -/
theorem residualIntervalTrace_union_shell
    {n : ℕ} {active : Finset (Fin n)}
    {p q : Fin n × Fin n}
    (h : LaterCrossCutIntervalContains p q) :
    residualIntervalTrace active p ∪
        residualIntervalShell active p q =
      residualIntervalTrace active q := by
  exact Finset.union_sdiff_of_subset
    (residualIntervalTrace_subset h)

/-- The exterior remaining after the outermost proper interval. -/
def residualIntervalExterior
    {n : ℕ} (active : Finset (Fin n))
    (p : Fin n × Fin n) : Finset (Fin n) :=
  active \ residualIntervalTrace active p

/-- The exterior of a fully paired residual interval is closed and has
no singles because the whole residual carrier is fully paired. -/
theorem momentResidualIntervalExterior_isFullyPairedOn
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p : Fin (2 * m) × Fin (2 * m)}
    (hp :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) p.1 p.2) :
    IsFullyPairedOn (momentCombinedPairing κp κm π)
      (residualIntervalExterior
        (momentResidualActive κp κm) p) :=
  (momentResidualActive_isFullyPairedOn κp κm π).sdiff
    hp.isFullyPairedOn

/-- An interval trace and its exterior exactly partition the residual
carrier. -/
theorem residualIntervalTrace_union_exterior
    {n : ℕ} (active : Finset (Fin n))
    (p : Fin n × Fin n) :
    residualIntervalTrace active p ∪
        residualIntervalExterior active p =
      active := by
  exact Finset.union_sdiff_of_subset
    (relIcc_subset_active active p.1 p.2)

end Anderson4D
