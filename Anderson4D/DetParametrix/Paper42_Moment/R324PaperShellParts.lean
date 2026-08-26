import Anderson4D.DetParametrix.Core.ResidualIntervalChain

/-!
# A cross-cut shell is contiguous in each half

Paper: R-324 — §4.2 Step 3, the shells of the nested chain

The blocks of the nested schedule are the *shells* between consecutive
intervals of paper Step 3(b)'s nested chain
`[a_t,b_t] ⊂ … ⊂ [a_1,b_1]`:

```lean
residualIntervalShell active p q = relIcc active q.1 q.2 \ relIcc active p.1 p.2
```

with `p` the inner interval and `q` the outer one.  Both straddle the cut
(Step 3(b)), so on the left of the cut `i ≤ p.2` and `i ≤ q.2` hold
automatically, and the shell's left part collapses to the relative
half-open interval

```
{ i ∈ active | q.1 ≤ i < p.1 }
```

— contiguous in the active order *by construction*, which is what makes
"the chain edges interior to the shell" a well-defined complement.  The
right part is the mirror image.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- **The part of a cross-cut shell below the cut is a relative half-open
interval.**

Both bounding intervals straddle the cut, so below it the constraints
`i ≤ p.2` and `i ≤ q.2` are vacuous and only `q.1 ≤ i < p.1` survives. -/
theorem residualIntervalShell_filter_lt
    {n m : ℕ} (active : Finset (Fin n)) (p q : Fin n × Fin n)
    (hp1 : (p.1 : ℕ) < m) (hmp2 : m ≤ (p.2 : ℕ)) (hmq2 : m ≤ (q.2 : ℕ)) :
    (residualIntervalShell active p q).filter (fun i : Fin n => (i : ℕ) < m) =
      active.filter fun i : Fin n => q.1 ≤ i ∧ i < p.1 := by
  classical
  ext i
  simp only [residualIntervalShell, residualIntervalTrace,
    Finset.mem_filter, Finset.mem_sdiff, mem_relIcc]
  constructor
  · rintro ⟨⟨⟨hact, hq1, _hq2⟩, hnp⟩, him⟩
    refine ⟨hact, hq1, ?_⟩
    rw [Fin.lt_def]
    by_contra hge
    exact hnp ⟨hact, by rw [Fin.le_def]; omega, by rw [Fin.le_def]; omega⟩
  · rintro ⟨hact, hq1, hlt⟩
    have hilt : (i : ℕ) < m := by
      have := Fin.lt_def.mp hlt
      omega
    refine ⟨⟨⟨hact, hq1, by rw [Fin.le_def]; omega⟩, ?_⟩, hilt⟩
    rintro ⟨_, hp1le, _⟩
    have := Fin.le_def.mp hp1le
    have := Fin.lt_def.mp hlt
    omega

/-- **The part of a cross-cut shell above the cut is a relative half-open
interval.**  Mirror image of the previous lemma. -/
theorem residualIntervalShell_filter_ge
    {n m : ℕ} (active : Finset (Fin n)) (p q : Fin n × Fin n)
    (hp2 : m ≤ (p.2 : ℕ)) (hq1 : (q.1 : ℕ) < m) (hp1 : (p.1 : ℕ) < m) :
    (residualIntervalShell active p q).filter (fun i : Fin n => m ≤ (i : ℕ)) =
      active.filter fun i : Fin n => p.2 < i ∧ i ≤ q.2 := by
  classical
  ext i
  simp only [residualIntervalShell, residualIntervalTrace,
    Finset.mem_filter, Finset.mem_sdiff, mem_relIcc]
  constructor
  · rintro ⟨⟨⟨hact, _hq1, hq2⟩, hnp⟩, him⟩
    refine ⟨hact, ?_, hq2⟩
    rw [Fin.lt_def]
    by_contra hge
    exact hnp ⟨hact, by rw [Fin.le_def]; omega, by rw [Fin.le_def]; omega⟩
  · rintro ⟨hact, hgt, hq2⟩
    have hige : m ≤ (i : ℕ) := by
      have := Fin.lt_def.mp hgt
      omega
    refine ⟨⟨⟨hact, by rw [Fin.le_def]; omega, hq2⟩, ?_⟩, hige⟩
    rintro ⟨_, _, hp2le⟩
    have := Fin.le_def.mp hp2le
    have := Fin.lt_def.mp hgt
    omega

end Anderson4D
