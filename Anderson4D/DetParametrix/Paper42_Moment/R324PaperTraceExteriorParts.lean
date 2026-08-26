import Anderson4D.DetParametrix.Paper42_Moment.R324PaperShellParts

/-!
# Cross-cut trace and exterior parts

The shell calculation has two endpoint analogues.  A cross-cut trace is a
terminal interval in each half of the active order, while the exterior is
the complementary initial or terminal interval.  These identities provide
the first and last blocks in the paper's Step 3 chain decomposition.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- Below the cut, a straddling trace is the relative interval starting at
its left endpoint and ending just before the cut. -/
theorem residualIntervalTrace_filter_lt
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hmp2 : m ≤ (p.2 : ℕ)) :
    (residualIntervalTrace active p).filter
        (fun i : Fin n => (i : ℕ) < m) =
      active.filter fun i : Fin n => p.1 ≤ i ∧ (i : ℕ) < m := by
  classical
  ext i
  simp only [residualIntervalTrace, Finset.mem_filter, mem_relIcc]
  constructor
  · rintro ⟨⟨hact, hp1, _hp2⟩, him⟩
    exact ⟨hact, hp1, him⟩
  · rintro ⟨hact, hp1, him⟩
    refine ⟨⟨hact, hp1, ?_⟩, him⟩
    rw [Fin.le_def]
    omega

/-- Above the cut, a straddling trace is the relative interval from the cut
through its right endpoint. -/
theorem residualIntervalTrace_filter_ge
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hp1 : (p.1 : ℕ) < m) :
    (residualIntervalTrace active p).filter
        (fun i : Fin n => m ≤ (i : ℕ)) =
      active.filter fun i : Fin n => m ≤ (i : ℕ) ∧ i ≤ p.2 := by
  classical
  ext i
  simp only [residualIntervalTrace, Finset.mem_filter, mem_relIcc]
  constructor
  · rintro ⟨⟨hact, _hp1, hp2⟩, him⟩
    exact ⟨hact, him, hp2⟩
  · rintro ⟨hact, him, hp2⟩
    refine ⟨⟨hact, ?_, hp2⟩, him⟩
    rw [Fin.le_def]
    omega

/-- Below the cut, the exterior of a straddling interval is exactly the
active initial interval strictly before its left endpoint. -/
theorem residualIntervalExterior_filter_lt
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hp1 : (p.1 : ℕ) < m) (hmp2 : m ≤ (p.2 : ℕ)) :
    (residualIntervalExterior active p).filter
        (fun i : Fin n => (i : ℕ) < m) =
      active.filter fun i : Fin n => i < p.1 := by
  classical
  ext i
  simp only [residualIntervalExterior, residualIntervalTrace,
    Finset.mem_filter, Finset.mem_sdiff, mem_relIcc]
  constructor
  · rintro ⟨⟨hact, hnotTrace⟩, him⟩
    refine ⟨hact, ?_⟩
    rw [Fin.lt_def]
    by_contra hge
    apply hnotTrace
    refine ⟨hact, ?_, ?_⟩
    · rw [Fin.le_def]
      omega
    · rw [Fin.le_def]
      omega
  · rintro ⟨hact, hlt⟩
    have him : (i : ℕ) < m := by
      have := Fin.lt_def.mp hlt
      omega
    refine ⟨⟨hact, ?_⟩, him⟩
    rintro ⟨_, hp1le, _⟩
    exact (not_le_of_gt hlt) hp1le

/-- Above the cut, the exterior is exactly the active terminal interval
strictly after the right endpoint. -/
theorem residualIntervalExterior_filter_ge
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hp1 : (p.1 : ℕ) < m) (hmp2 : m ≤ (p.2 : ℕ)) :
    (residualIntervalExterior active p).filter
        (fun i : Fin n => m ≤ (i : ℕ)) =
      active.filter fun i : Fin n => p.2 < i := by
  classical
  ext i
  simp only [residualIntervalExterior, residualIntervalTrace,
    Finset.mem_filter, Finset.mem_sdiff, mem_relIcc]
  constructor
  · rintro ⟨⟨hact, hnotTrace⟩, him⟩
    refine ⟨hact, ?_⟩
    rw [Fin.lt_def]
    by_contra hge
    apply hnotTrace
    refine ⟨hact, ?_, ?_⟩
    · rw [Fin.le_def]
      omega
    · rw [Fin.le_def]
      omega
  · rintro ⟨hact, hlt⟩
    have him : m ≤ (i : ℕ) := by
      have := Fin.lt_def.mp hlt
      omega
    refine ⟨⟨hact, ?_⟩, him⟩
    rintro ⟨_, _, hp2le⟩
    exact (not_le_of_gt hlt) hp2le

/-! ## Contiguity in the relative active order -/

/-- A finite part is contiguous relative to `active` when its pullback to
the linearly ordered subtype of active vertices is order-connected.  This is
the standard `Set.OrdConnected` predicate, applied to the relative carrier
rather than to the ambient `Fin n` (where gaps in `active` are intentional). -/
def FinsetOrdConnectedWithin
    {n : ℕ} (active part : Finset (Fin n)) : Prop :=
  Set.OrdConnected
    {i : {i : Fin n // i ∈ active} | i.1 ∈ part}

/-- The below-cut trace is contiguous in the active order. -/
theorem residualIntervalTrace_filter_lt_ordConnectedWithin
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hmp2 : m ≤ (p.2 : ℕ)) :
    FinsetOrdConnectedWithin active
      ((residualIntervalTrace active p).filter
        (fun i : Fin n => (i : ℕ) < m)) := by
  rw [residualIntervalTrace_filter_lt active p hmp2]
  rw [FinsetOrdConnectedWithin, Set.ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq, Finset.mem_filter] at hx hy ⊢
  have hxyz : x ≤ z ∧ z ≤ y := hz
  refine ⟨z.2, ?_, ?_⟩
  · exact hx.2.1.trans hxyz.1
  · have hylt := hy.2.2
    change (z.1 : ℕ) < m
    change (y.1 : ℕ) < m at hylt
    exact lt_of_le_of_lt hxyz.2 hylt

/-- The above-cut trace is contiguous in the active order. -/
theorem residualIntervalTrace_filter_ge_ordConnectedWithin
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hp1 : (p.1 : ℕ) < m) :
    FinsetOrdConnectedWithin active
      ((residualIntervalTrace active p).filter
        (fun i : Fin n => m ≤ (i : ℕ))) := by
  rw [residualIntervalTrace_filter_ge active p hp1]
  rw [FinsetOrdConnectedWithin, Set.ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq, Finset.mem_filter] at hx hy ⊢
  have hxyz : x ≤ z ∧ z ≤ y := hz
  refine ⟨z.2, ?_, ?_⟩
  · have hxge := hx.2.1
    change m ≤ (z.1 : ℕ)
    change m ≤ (x.1 : ℕ) at hxge
    exact hxge.trans hxyz.1
  · have hzy : z.1 ≤ y.1 := hxyz.2
    exact hzy.trans hy.2.2

/-- The below-cut exterior is contiguous in the active order. -/
theorem residualIntervalExterior_filter_lt_ordConnectedWithin
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hp1 : (p.1 : ℕ) < m) (hmp2 : m ≤ (p.2 : ℕ)) :
    FinsetOrdConnectedWithin active
      ((residualIntervalExterior active p).filter
        (fun i : Fin n => (i : ℕ) < m)) := by
  rw [residualIntervalExterior_filter_lt active p hp1 hmp2]
  rw [FinsetOrdConnectedWithin, Set.ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq, Finset.mem_filter] at hx hy ⊢
  have hxyz : x ≤ z ∧ z ≤ y := hz
  have hzy : z.1 ≤ y.1 := hxyz.2
  exact ⟨z.2, hzy.trans_lt hy.2⟩

/-- The above-cut exterior is contiguous in the active order. -/
theorem residualIntervalExterior_filter_ge_ordConnectedWithin
    {n m : ℕ} (active : Finset (Fin n)) (p : Fin n × Fin n)
    (hp1 : (p.1 : ℕ) < m) (hmp2 : m ≤ (p.2 : ℕ)) :
    FinsetOrdConnectedWithin active
      ((residualIntervalExterior active p).filter
        (fun i : Fin n => m ≤ (i : ℕ))) := by
  rw [residualIntervalExterior_filter_ge active p hp1 hmp2]
  rw [FinsetOrdConnectedWithin, Set.ordConnected_def]
  intro x hx y hy z hz
  simp only [Set.mem_setOf_eq, Finset.mem_filter] at hx hy ⊢
  have hxyz : x ≤ z ∧ z ≤ y := hz
  have hxz : x.1 ≤ z.1 := hxyz.1
  exact ⟨z.2, hx.2.trans_le hxz⟩

end Anderson4D
