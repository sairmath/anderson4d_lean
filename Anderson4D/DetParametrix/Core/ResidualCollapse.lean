import Anderson4D.DetParametrix.Core.ResidualIntervalChain

/-!
# Exact block decomposition for the residual R-324 collapse

For a nested inside-to-outside interval chain, the collapse blocks are:

* the innermost interval trace;
* the closed shell between every two successive traces;
* the exterior of the outermost trace.

If the chain is empty, the whole residual carrier is the sole block.
This file proves that these blocks cover the residual carrier exactly
and that every block is fully paired by the combined contraction
pairing.  It is the finite-carrier decomposition used before applying
the primitive analytic estimate successively in paper §4.2 Step 3.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- Shells after a current inner trace, ending with the exterior of the
last outer trace. -/
def nestedResidualShells
    {n : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n) :
    List (Fin n × Fin n) → List (Finset (Fin n))
  | [] => [residualIntervalExterior active previous]
  | next :: rest =>
      residualIntervalShell active previous next ::
        nestedResidualShells active next rest

/-- Complete block list associated with an inside-to-outside chain. -/
def residualCollapseBlocks
    {n : ℕ} (active : Finset (Fin n)) :
    List (Fin n × Fin n) → List (Finset (Fin n))
  | [] => [active]
  | first :: rest =>
      residualIntervalTrace active first ::
        nestedResidualShells active first rest

/-- Union of a finite list of finite carriers. -/
def finsetUnionList {α : Type*} [DecidableEq α] :
    List (Finset α) → Finset α
  | [] => ∅
  | s :: ss => s ∪ finsetUnionList ss

/-- Relative primitivity on a sparse carrier: every relative fully
paired interval is the whole carrier.  After order-preserving renaming
this is exactly paper Definition 2.3. -/
def IsRelPrimitiveOn
    {n : ℕ} (κ : PartialPairing (Fin n))
    (active : Finset (Fin n)) : Prop :=
  ∀ a b, IsRelFullyPaired κ active a b →
    relIcc active a b = active

/-- Restricting twice to nested endpoint bounds does not change a
relative interval whose endpoints already belong to the outer trace. -/
theorem relIcc_residualIntervalTrace
    {n : ℕ} {active : Finset (Fin n)}
    {p : Fin n × Fin n} {a b : Fin n}
    (ha : a ∈ residualIntervalTrace active p)
    (hb : b ∈ residualIntervalTrace active p) :
    relIcc (residualIntervalTrace active p) a b =
      relIcc active a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxtrace, hax, hxb⟩ := mem_relIcc.mp hx
    have hxactive := (mem_relIcc.mp hxtrace).1
    exact mem_relIcc.mpr
      ⟨hxactive, hax, hxb⟩
  · intro hx
    obtain ⟨hxactive, hax, hxb⟩ := mem_relIcc.mp hx
    obtain ⟨_, hp1a, _⟩ := mem_relIcc.mp ha
    obtain ⟨_, _, hbp2⟩ := mem_relIcc.mp hb
    exact mem_relIcc.mpr
      ⟨mem_relIcc.mpr
        ⟨hxactive, hp1a.trans hax, hxb.trans hbp2⟩,
        hax, hxb⟩

/-- If the canonical residual chain is empty, the whole residual
carrier is already primitive. -/
theorem momentResidualActive_isRelPrimitiveOn_of_chain_eq_nil
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hchain : momentResidualIntervalChain κp κm π = []) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π)
      (momentResidualActive κp κm) := by
  intro a b hab
  by_contra hproper
  have hp :
      (a, b) ∈ momentResidualIntervalChain κp κm π :=
    mem_momentResidualIntervalChain.mpr
      (mem_momentResidualProperIntervals.mpr
        ⟨hab, hproper⟩)
  rw [hchain] at hp
  simp at hp

/-- The first trace of the canonical inside-to-outside residual chain
is primitive.  Any proper subinterval would itself occur in the chain
before the head, contradicting the chosen order. -/
theorem residualIntervalTrace_head_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (first : Fin (2 * m) × Fin (2 * m))
    (rest : List (Fin (2 * m) × Fin (2 * m)))
    (hchain :
      momentResidualIntervalChain κp κm π =
        first :: rest) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π)
      (residualIntervalTrace
        (momentResidualActive κp κm) first) := by
  intro a b hab
  have hfirstMem :
      first ∈ momentResidualIntervalChain κp κm π := by
    rw [hchain]
    simp
  have hfirst :=
    mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp hfirstMem)
  have haActive :
      a ∈ momentResidualActive κp κm :=
    (mem_relIcc.mp hab.left_mem).1
  have hbActive :
      b ∈ momentResidualActive κp κm :=
    (mem_relIcc.mp hab.right_mem).1
  have habActive :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) a b := by
    refine ⟨haActive, hbActive, hab.le, ?_⟩
    rw [← relIcc_residualIntervalTrace
      hab.left_mem hab.right_mem]
    exact hab.isFullyPairedOn
  have habProper :
      relIcc (momentResidualActive κp κm) a b ≠
        momentResidualActive κp κm := by
    intro hall
    apply hfirst.2
    apply Finset.Subset.antisymm
    · exact relIcc_subset_active _ _ _
    · intro x hx
      have hxAB : x ∈ relIcc
          (momentResidualActive κp κm) a b := by
        rw [hall]
        exact hx
      rw [← relIcc_residualIntervalTrace
        hab.left_mem hab.right_mem] at hxAB
      exact (mem_relIcc.mp hxAB).1
  have habChain :
      (a, b) ∈ momentResidualIntervalChain κp κm π :=
    mem_momentResidualIntervalChain.mpr
      (mem_momentResidualProperIntervals.mpr
        ⟨habActive, habProper⟩)
  have habChain' : (a, b) ∈ first :: rest := by
    rw [← hchain]
    exact habChain
  rcases List.mem_cons.mp habChain' with heq | hrest
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    ext x
    simp [residualIntervalTrace, relIcc]
  · have hpair :
        (first :: rest).Pairwise
          LaterCrossCutIntervalContains := by
      rw [← hchain]
      exact momentResidualIntervalChain_pairwise_laterContains
        κp κm π
    have hcontains :
        LaterCrossCutIntervalContains first (a, b) :=
      (List.pairwise_cons.mp hpair).1 (a, b) hrest
    have hfirstLeA :
        first.1 ≤ a :=
      (mem_relIcc.mp hab.left_mem).2.1
    exact False.elim ((not_lt_of_ge hfirstLeA) hcontains.1)

/-- Membership in the shell between two nested traces, expressed as
the two open side pieces around the inner trace. -/
theorem mem_residualIntervalShell_iff
    {n : ℕ} {active : Finset (Fin n)}
    {p q : Fin n × Fin n}
    (_h : LaterCrossCutIntervalContains p q)
    {x : Fin n} :
    x ∈ residualIntervalShell active p q ↔
      x ∈ active ∧ q.1 ≤ x ∧ x ≤ q.2 ∧
        (x < p.1 ∨ p.2 < x) := by
  simp only [residualIntervalShell, residualIntervalTrace,
    Finset.mem_sdiff, mem_relIcc]
  constructor
  · rintro ⟨⟨hx, hq1x, hxq2⟩, hxnot⟩
    refine ⟨hx, hq1x, hxq2, ?_⟩
    by_cases hp1x : p.1 ≤ x
    · right
      exact lt_of_not_ge fun hxp2 =>
        hxnot ⟨hx, hp1x, hxp2⟩
    · left
      exact lt_of_not_ge hp1x
  · rintro ⟨hx, hq1x, hxq2, hxside⟩
    refine ⟨⟨hx, hq1x, hxq2⟩, ?_⟩
    rintro ⟨_, hp1x, hxp2⟩
    rcases hxside with hleft | hright
    · exact (not_lt_of_ge hp1x) hleft
    · exact (not_lt_of_ge hxp2) hright

/-- On the left component of a shell, its relative intervals are the
same as relative intervals of the full active carrier. -/
theorem relIcc_residualIntervalShell_eq_active_of_left
    {n : ℕ} {active : Finset (Fin n)}
    {p q : Fin n × Fin n} {a b : Fin n}
    (h : LaterCrossCutIntervalContains p q)
    (ha : a ∈ residualIntervalShell active p q)
    (hb : b ∈ residualIntervalShell active p q)
    (hbLeft : b < p.1) :
    relIcc (residualIntervalShell active p q) a b =
      relIcc active a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxshell, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨(mem_residualIntervalShell_iff h).mp hxshell |>.1,
        hax, hxb⟩
  · intro hx
    obtain ⟨hxactive, hax, hxb⟩ := mem_relIcc.mp hx
    have ha' := (mem_residualIntervalShell_iff h).mp ha
    have hb' := (mem_residualIntervalShell_iff h).mp hb
    exact mem_relIcc.mpr
      ⟨(mem_residualIntervalShell_iff h).mpr
        ⟨hxactive, ha'.2.1.trans hax,
          hxb.trans hb'.2.2.1,
          Or.inl (hxb.trans_lt hbLeft)⟩,
        hax, hxb⟩

/-- Right-component counterpart of
`relIcc_residualIntervalShell_eq_active_of_left`. -/
theorem relIcc_residualIntervalShell_eq_active_of_right
    {n : ℕ} {active : Finset (Fin n)}
    {p q : Fin n × Fin n} {a b : Fin n}
    (h : LaterCrossCutIntervalContains p q)
    (ha : a ∈ residualIntervalShell active p q)
    (hb : b ∈ residualIntervalShell active p q)
    (haRight : p.2 < a) :
    relIcc (residualIntervalShell active p q) a b =
      relIcc active a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxshell, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨(mem_residualIntervalShell_iff h).mp hxshell |>.1,
        hax, hxb⟩
  · intro hx
    obtain ⟨hxactive, hax, hxb⟩ := mem_relIcc.mp hx
    have ha' := (mem_residualIntervalShell_iff h).mp ha
    have hb' := (mem_residualIntervalShell_iff h).mp hb
    exact mem_relIcc.mpr
      ⟨(mem_residualIntervalShell_iff h).mpr
        ⟨hxactive, ha'.2.1.trans hax,
          hxb.trans hb'.2.2.1,
          Or.inr (haRight.trans_le hax)⟩,
        hax, hxb⟩

/-- A fully paired interval inside a residual shell must meet both side
components of that shell.  Otherwise it would lift to a residual
fully-paired interval lying wholly on one side of the central cut. -/
theorem IsRelFullyPaired.momentResidualShell_straddlesInner
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p q : Fin (2 * m) × Fin (2 * m)}
    (hp :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) p.1 p.2)
    (hpq : LaterCrossCutIntervalContains p q)
    {a b : Fin (2 * m)}
    (hab :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (residualIntervalShell
          (momentResidualActive κp κm) p q) a b) :
    a < p.1 ∧ p.2 < b := by
  have haSide :=
    (mem_residualIntervalShell_iff hpq).mp hab.left_mem |>.2.2.2
  have hbSide :=
    (mem_residualIntervalShell_iff hpq).mp hab.right_mem |>.2.2.2
  constructor
  · rcases haSide with haLeft | haRight
    · exact haLeft
    · have habActive :
          IsRelFullyPaired (momentCombinedPairing κp κm π)
            (momentResidualActive κp κm) a b := by
        refine
          ⟨(mem_residualIntervalShell_iff hpq).mp
              hab.left_mem |>.1,
            (mem_residualIntervalShell_iff hpq).mp
              hab.right_mem |>.1,
            hab.le, ?_⟩
        rw [← relIcc_residualIntervalShell_eq_active_of_right
          hpq hab.left_mem hab.right_mem haRight]
        exact hab.isFullyPairedOn
      have hcut := habActive.momentResidualActive_straddlesCut
      have hpCut := hp.momentResidualActive_straddlesCut
      have haGe : m ≤ a.val :=
        hpCut.2.trans
          (Nat.le_of_lt (Fin.mk_lt_mk.mp haRight))
      exact False.elim ((not_lt_of_ge haGe) hcut.1)
  · rcases hbSide with hbLeft | hbRight
    · have habActive :
          IsRelFullyPaired (momentCombinedPairing κp κm π)
            (momentResidualActive κp κm) a b := by
        refine
          ⟨(mem_residualIntervalShell_iff hpq).mp
              hab.left_mem |>.1,
            (mem_residualIntervalShell_iff hpq).mp
              hab.right_mem |>.1,
            hab.le, ?_⟩
        rw [← relIcc_residualIntervalShell_eq_active_of_left
          hpq hab.left_mem hab.right_mem hbLeft]
        exact hab.isFullyPairedOn
      have hcut := habActive.momentResidualActive_straddlesCut
      have hpCut := hp.momentResidualActive_straddlesCut
      have hbLt : b.val < m :=
        (Fin.mk_lt_mk.mp hbLeft).trans hpCut.1
      exact False.elim ((not_lt_of_ge hcut.2) hbLt)
    · exact hbRight

/-- A shell interval which crosses its inner trace lifts to the union
of that inner trace and the shell interval on the original carrier. -/
theorem residualIntervalTrace_union_relIcc_shell
    {n : ℕ} {active : Finset (Fin n)}
    {p q : Fin n × Fin n} {a b : Fin n}
    (hpq : LaterCrossCutIntervalContains p q)
    (ha : a ∈ residualIntervalShell active p q)
    (hb : b ∈ residualIntervalShell active p q)
    (haLeft : a < p.1) (hbRight : p.2 < b) :
    residualIntervalTrace active p ∪
        relIcc (residualIntervalShell active p q) a b =
      relIcc active a b := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxInner | hxShell
    · obtain ⟨hxactive, hp1x, hxp2⟩ := mem_relIcc.mp hxInner
      exact mem_relIcc.mpr
        ⟨hxactive, haLeft.le.trans hp1x,
          hxp2.trans hbRight.le⟩
    · obtain ⟨hxS, hax, hxb⟩ := mem_relIcc.mp hxShell
      exact mem_relIcc.mpr
        ⟨(mem_residualIntervalShell_iff hpq).mp hxS |>.1,
          hax, hxb⟩
  · intro hx
    obtain ⟨hxactive, hax, hxb⟩ := mem_relIcc.mp hx
    by_cases hp1x : p.1 ≤ x
    · by_cases hxp2 : x ≤ p.2
      · exact Finset.mem_union_left _
          (mem_relIcc.mpr ⟨hxactive, hp1x, hxp2⟩)
      · apply Finset.mem_union_right
        exact mem_relIcc.mpr
          ⟨(mem_residualIntervalShell_iff hpq).mpr
            ⟨hxactive,
              ((mem_residualIntervalShell_iff hpq).mp ha).2.1.trans hax,
              hxb.trans
                ((mem_residualIntervalShell_iff hpq).mp hb).2.2.1,
              Or.inr (lt_of_not_ge hxp2)⟩,
            hax, hxb⟩
    · apply Finset.mem_union_right
      exact mem_relIcc.mpr
        ⟨(mem_residualIntervalShell_iff hpq).mpr
          ⟨hxactive,
            ((mem_residualIntervalShell_iff hpq).mp ha).2.1.trans hax,
            hxb.trans
              ((mem_residualIntervalShell_iff hpq).mp hb).2.2.1,
            Or.inl (lt_of_not_ge hp1x)⟩,
          hax, hxb⟩

/-- The first shell of a canonical residual chain is primitive.  A
proper shell interval would lift to an extra residual interval strictly
between the first two adjacent chain entries. -/
theorem first_residualIntervalShell_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (first next : Fin (2 * m) × Fin (2 * m))
    (rest : List (Fin (2 * m) × Fin (2 * m)))
    (hchain :
      momentResidualIntervalChain κp κm π =
        first :: next :: rest) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π)
      (residualIntervalShell
        (momentResidualActive κp κm) first next) := by
  let κ := momentCombinedPairing κp κm π
  let active := momentResidualActive κp κm
  have hpair :
      (first :: next :: rest).Pairwise
        LaterCrossCutIntervalContains := by
    rw [← hchain]
    exact momentResidualIntervalChain_pairwise_laterContains
      κp κm π
  have hnextPair :
      LaterCrossCutIntervalContains first next :=
    (List.pairwise_cons.mp hpair).1 next (by simp)
  have hfirst :
      IsRelFullyPaired κ active first.1 first.2 :=
    (mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp
        (hchain ▸ (by simp : first ∈ first :: next :: rest)))).1
  have hnext :
      IsRelFullyPaired κ active next.1 next.2 :=
    (mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp
        (hchain ▸ (by simp : next ∈ first :: next :: rest)))).1
  intro a b hab
  have habSides :=
    IsRelFullyPaired.momentResidualShell_straddlesInner
      hfirst hnextPair hab
  have habActive :
      IsRelFullyPaired κ active a b := by
    refine
      ⟨(mem_residualIntervalShell_iff hnextPair).mp
          hab.left_mem |>.1,
        (mem_residualIntervalShell_iff hnextPair).mp
          hab.right_mem |>.1,
        hab.le, ?_⟩
    rw [← residualIntervalTrace_union_relIcc_shell
      hnextPair hab.left_mem hab.right_mem
      habSides.1 habSides.2]
    exact hfirst.isFullyPairedOn.union hab.isFullyPairedOn
  have habProper :
      relIcc active a b ≠ active := by
    intro hall
    have hnextProper :=
      (mem_momentResidualProperIntervals.mp
        (mem_momentResidualIntervalChain.mp
          (hchain ▸
            (by simp : next ∈ first :: next :: rest)))).2
    apply hnextProper
    apply Finset.Subset.antisymm
    · exact relIcc_subset_active _ _ _
    · intro x hx
      have hxAB : x ∈ relIcc active a b := by
        rw [hall]
        exact hx
      obtain ⟨_, hax, hxb⟩ := mem_relIcc.mp hxAB
      have haOuter :=
        (mem_residualIntervalShell_iff hnextPair).mp
          hab.left_mem
      have hbOuter :=
        (mem_residualIntervalShell_iff hnextPair).mp
          hab.right_mem
      exact mem_relIcc.mpr
        ⟨hx, haOuter.2.1.trans hax,
          hxb.trans hbOuter.2.2.1⟩
  have habChain :
      (a, b) ∈ first :: next :: rest := by
    rw [← hchain]
    exact mem_momentResidualIntervalChain.mpr
      (mem_momentResidualProperIntervals.mpr
        ⟨habActive, habProper⟩)
  rcases List.mem_cons.mp habChain with hEqFirst | habTail
  · have hlt : a < first.1 := habSides.1
    have haeq : a = first.1 :=
      congrArg Prod.fst hEqFirst
    exact False.elim ((ne_of_lt hlt) haeq)
  · rcases List.mem_cons.mp habTail with hEqNext | habRest
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hEqNext
      ext x
      simp only [mem_relIcc]
      constructor
      · intro hx
        exact hx.1
      · intro hx
        have hx' :=
          (mem_residualIntervalShell_iff hnextPair).mp hx
        exact ⟨hx, hx'.2.1, hx'.2.2.1⟩
    · have hlater :
          LaterCrossCutIntervalContains next (a, b) :=
        (List.pairwise_cons.mp
          (List.pairwise_cons.mp hpair).2).1 (a, b) habRest
      have hnextLeA :
          next.1 ≤ a :=
        (mem_residualIntervalShell_iff hnextPair).mp
          hab.left_mem |>.2.1
      exact False.elim ((not_lt_of_ge hnextLeA) hlater.1)

/-- Every shell between adjacent entries of the canonical residual
chain is primitive, including shells after a nonempty prefix. -/
theorem adjacent_residualIntervalShell_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (pre : List (Fin (2 * m) × Fin (2 * m)))
    (first next : Fin (2 * m) × Fin (2 * m))
    (rest : List (Fin (2 * m) × Fin (2 * m)))
    (hchain :
      momentResidualIntervalChain κp κm π =
        pre ++ first :: next :: rest) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π)
      (residualIntervalShell
        (momentResidualActive κp κm) first next) := by
  let κ := momentCombinedPairing κp κm π
  let active := momentResidualActive κp κm
  have hpairFull :
      (pre ++ first :: next :: rest).Pairwise
        LaterCrossCutIntervalContains := by
    rw [← hchain]
    exact momentResidualIntervalChain_pairwise_laterContains
      κp κm π
  have hpair :
      (first :: next :: rest).Pairwise
        LaterCrossCutIntervalContains := by
    have hdrop := hpairFull.drop (i := pre.length)
    simpa only [List.drop_left] using hdrop
  have hnextPair :
      LaterCrossCutIntervalContains first next :=
    (List.pairwise_cons.mp hpair).1 next (by simp)
  have hfirst :
      IsRelFullyPaired κ active first.1 first.2 :=
    (mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp
        (hchain ▸
          (by simp : first ∈ pre ++ first :: next :: rest)))).1
  intro a b hab
  have habSides :=
    IsRelFullyPaired.momentResidualShell_straddlesInner
      hfirst hnextPair hab
  have habActive :
      IsRelFullyPaired κ active a b := by
    refine
      ⟨(mem_residualIntervalShell_iff hnextPair).mp
          hab.left_mem |>.1,
        (mem_residualIntervalShell_iff hnextPair).mp
          hab.right_mem |>.1,
        hab.le, ?_⟩
    rw [← residualIntervalTrace_union_relIcc_shell
      hnextPair hab.left_mem hab.right_mem
      habSides.1 habSides.2]
    exact hfirst.isFullyPairedOn.union hab.isFullyPairedOn
  have habProper :
      relIcc active a b ≠ active := by
    intro hall
    have hnextProper :=
      (mem_momentResidualProperIntervals.mp
        (mem_momentResidualIntervalChain.mp
          (hchain ▸
            (by simp :
              next ∈ pre ++ first :: next :: rest)))).2
    apply hnextProper
    apply Finset.Subset.antisymm
    · exact relIcc_subset_active _ _ _
    · intro x hx
      have hxAB : x ∈ relIcc active a b := by
        rw [hall]
        exact hx
      obtain ⟨_, hax, hxb⟩ := mem_relIcc.mp hxAB
      have haOuter :=
        (mem_residualIntervalShell_iff hnextPair).mp
          hab.left_mem
      have hbOuter :=
        (mem_residualIntervalShell_iff hnextPair).mp
          hab.right_mem
      exact mem_relIcc.mpr
        ⟨hx, haOuter.2.1.trans hax,
          hxb.trans hbOuter.2.2.1⟩
  have habChain :
      (a, b) ∈ pre ++ first :: next :: rest := by
    rw [← hchain]
    exact mem_momentResidualIntervalChain.mpr
      (mem_momentResidualProperIntervals.mpr
        ⟨habActive, habProper⟩)
  rcases List.mem_append.mp habChain with habPre | habTail
  · have hcross :
        LaterCrossCutIntervalContains (a, b) first :=
      (List.pairwise_append.mp hpairFull).2.2
        (a, b) habPre first (by simp)
    exact False.elim
      ((not_lt_of_ge hcross.1.le) habSides.1)
  · rcases List.mem_cons.mp habTail with hEqFirst | habTail'
    · have hlt : a < first.1 := habSides.1
      have haeq : a = first.1 :=
        congrArg Prod.fst hEqFirst
      exact False.elim ((ne_of_lt hlt) haeq)
    · rcases List.mem_cons.mp habTail' with hEqNext | habRest
      · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hEqNext
        ext x
        simp only [mem_relIcc]
        constructor
        · intro hx
          exact hx.1
        · intro hx
          have hx' :=
            (mem_residualIntervalShell_iff hnextPair).mp hx
          exact ⟨hx, hx'.2.1, hx'.2.2.1⟩
      · have hlater :
            LaterCrossCutIntervalContains next (a, b) :=
          (List.pairwise_cons.mp
            (List.pairwise_cons.mp hpair).2).1 (a, b) habRest
        have hnextLeA :
            next.1 ≤ a :=
          (mem_residualIntervalShell_iff hnextPair).mp
            hab.left_mem |>.2.1
        exact False.elim ((not_lt_of_ge hnextLeA) hlater.1)

/-- Membership in the exterior of a residual trace, expressed as the
two open side pieces outside the trace. -/
theorem mem_residualIntervalExterior_iff
    {n : ℕ} {active : Finset (Fin n)}
    {p : Fin n × Fin n} {x : Fin n} :
    x ∈ residualIntervalExterior active p ↔
      x ∈ active ∧ (x < p.1 ∨ p.2 < x) := by
  simp only [residualIntervalExterior, residualIntervalTrace,
    Finset.mem_sdiff, mem_relIcc]
  constructor
  · rintro ⟨hx, hxnot⟩
    refine ⟨hx, ?_⟩
    by_cases hp1x : p.1 ≤ x
    · right
      exact lt_of_not_ge fun hxp2 =>
        hxnot ⟨hx, hp1x, hxp2⟩
    · left
      exact lt_of_not_ge hp1x
  · rintro ⟨hx, hxside⟩
    refine ⟨hx, ?_⟩
    rintro ⟨_, hp1x, hxp2⟩
    rcases hxside with hleft | hright
    · exact (not_lt_of_ge hp1x) hleft
    · exact (not_lt_of_ge hxp2) hright

/-- On the left component of an exterior, its relative intervals are
the same as relative intervals of the full active carrier. -/
theorem relIcc_residualIntervalExterior_eq_active_of_left
    {n : ℕ} {active : Finset (Fin n)}
    {p : Fin n × Fin n} {a b : Fin n}
    (_ha : a ∈ residualIntervalExterior active p)
    (_hb : b ∈ residualIntervalExterior active p)
    (hbLeft : b < p.1) :
    relIcc (residualIntervalExterior active p) a b =
      relIcc active a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxexterior, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨(mem_residualIntervalExterior_iff.mp hxexterior).1,
        hax, hxb⟩
  · intro hx
    obtain ⟨hxactive, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨mem_residualIntervalExterior_iff.mpr
        ⟨hxactive, Or.inl (hxb.trans_lt hbLeft)⟩,
        hax, hxb⟩

/-- Right-component counterpart of
`relIcc_residualIntervalExterior_eq_active_of_left`. -/
theorem relIcc_residualIntervalExterior_eq_active_of_right
    {n : ℕ} {active : Finset (Fin n)}
    {p : Fin n × Fin n} {a b : Fin n}
    (_ha : a ∈ residualIntervalExterior active p)
    (_hb : b ∈ residualIntervalExterior active p)
    (haRight : p.2 < a) :
    relIcc (residualIntervalExterior active p) a b =
      relIcc active a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxexterior, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨(mem_residualIntervalExterior_iff.mp hxexterior).1,
        hax, hxb⟩
  · intro hx
    obtain ⟨hxactive, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨mem_residualIntervalExterior_iff.mpr
        ⟨hxactive, Or.inr (haRight.trans_le hax)⟩,
        hax, hxb⟩

/-- A fully paired interval inside the final exterior must meet both
side components.  A one-sided interval would contradict residual
cross-cut geometry. -/
theorem IsRelFullyPaired.momentResidualExterior_straddlesInner
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {p : Fin (2 * m) × Fin (2 * m)}
    (hp :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) p.1 p.2)
    {a b : Fin (2 * m)}
    (hab :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (residualIntervalExterior
          (momentResidualActive κp κm) p) a b) :
    a < p.1 ∧ p.2 < b := by
  have haSide :=
    (mem_residualIntervalExterior_iff.mp hab.left_mem).2
  have hbSide :=
    (mem_residualIntervalExterior_iff.mp hab.right_mem).2
  constructor
  · rcases haSide with haLeft | haRight
    · exact haLeft
    · have habActive :
          IsRelFullyPaired (momentCombinedPairing κp κm π)
            (momentResidualActive κp κm) a b := by
        refine
          ⟨(mem_residualIntervalExterior_iff.mp
              hab.left_mem).1,
            (mem_residualIntervalExterior_iff.mp
              hab.right_mem).1,
            hab.le, ?_⟩
        rw [← relIcc_residualIntervalExterior_eq_active_of_right
          hab.left_mem hab.right_mem haRight]
        exact hab.isFullyPairedOn
      have hcut := habActive.momentResidualActive_straddlesCut
      have hpCut := hp.momentResidualActive_straddlesCut
      have haGe : m ≤ a.val :=
        hpCut.2.trans
          (Nat.le_of_lt (Fin.mk_lt_mk.mp haRight))
      exact False.elim ((not_lt_of_ge haGe) hcut.1)
  · rcases hbSide with hbLeft | hbRight
    · have habActive :
          IsRelFullyPaired (momentCombinedPairing κp κm π)
            (momentResidualActive κp κm) a b := by
        refine
          ⟨(mem_residualIntervalExterior_iff.mp
              hab.left_mem).1,
            (mem_residualIntervalExterior_iff.mp
              hab.right_mem).1,
            hab.le, ?_⟩
        rw [← relIcc_residualIntervalExterior_eq_active_of_left
          hab.left_mem hab.right_mem hbLeft]
        exact hab.isFullyPairedOn
      have hcut := habActive.momentResidualActive_straddlesCut
      have hpCut := hp.momentResidualActive_straddlesCut
      have hbLt : b.val < m :=
        (Fin.mk_lt_mk.mp hbLeft).trans hpCut.1
      exact False.elim ((not_lt_of_ge hcut.2) hbLt)
    · exact hbRight

/-- An exterior interval which crosses its inner trace lifts to the
union of that trace and the exterior interval on the original carrier. -/
theorem residualIntervalTrace_union_relIcc_exterior
    {n : ℕ} {active : Finset (Fin n)}
    {p : Fin n × Fin n} {a b : Fin n}
    (_ha : a ∈ residualIntervalExterior active p)
    (_hb : b ∈ residualIntervalExterior active p)
    (haLeft : a < p.1) (hbRight : p.2 < b) :
    residualIntervalTrace active p ∪
        relIcc (residualIntervalExterior active p) a b =
      relIcc active a b := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxInner | hxExterior
    · obtain ⟨hxactive, hp1x, hxp2⟩ := mem_relIcc.mp hxInner
      exact mem_relIcc.mpr
        ⟨hxactive, haLeft.le.trans hp1x,
          hxp2.trans hbRight.le⟩
    · obtain ⟨hxE, hax, hxb⟩ := mem_relIcc.mp hxExterior
      exact mem_relIcc.mpr
        ⟨(mem_residualIntervalExterior_iff.mp hxE).1,
          hax, hxb⟩
  · intro hx
    obtain ⟨hxactive, hax, hxb⟩ := mem_relIcc.mp hx
    by_cases hp1x : p.1 ≤ x
    · by_cases hxp2 : x ≤ p.2
      · exact Finset.mem_union_left _
          (mem_relIcc.mpr ⟨hxactive, hp1x, hxp2⟩)
      · apply Finset.mem_union_right
        exact mem_relIcc.mpr
          ⟨mem_residualIntervalExterior_iff.mpr
            ⟨hxactive, Or.inr (lt_of_not_ge hxp2)⟩,
            hax, hxb⟩
    · apply Finset.mem_union_right
      exact mem_relIcc.mpr
        ⟨mem_residualIntervalExterior_iff.mpr
          ⟨hxactive, Or.inl (lt_of_not_ge hp1x)⟩,
          hax, hxb⟩

/-- The exterior after the outermost residual interval is primitive.
Any proper exterior interval would lift to a residual interval outside
the last entry of the canonical chain. -/
theorem last_residualIntervalExterior_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (pre : List (Fin (2 * m) × Fin (2 * m)))
    (last : Fin (2 * m) × Fin (2 * m))
    (hchain :
      momentResidualIntervalChain κp κm π =
        pre ++ [last]) :
    IsRelPrimitiveOn (momentCombinedPairing κp κm π)
      (residualIntervalExterior
        (momentResidualActive κp κm) last) := by
  let κ := momentCombinedPairing κp κm π
  let active := momentResidualActive κp κm
  have hpair :
      (pre ++ [last]).Pairwise
        LaterCrossCutIntervalContains := by
    rw [← hchain]
    exact momentResidualIntervalChain_pairwise_laterContains
      κp κm π
  have hlast :
      IsRelFullyPaired κ active last.1 last.2 :=
    (mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp
        (hchain ▸
          (by simp : last ∈ pre ++ [last])))).1
  intro a b hab
  have habSides :=
    IsRelFullyPaired.momentResidualExterior_straddlesInner
      hlast hab
  have habActive :
      IsRelFullyPaired κ active a b := by
    refine
      ⟨(mem_residualIntervalExterior_iff.mp
          hab.left_mem).1,
        (mem_residualIntervalExterior_iff.mp
          hab.right_mem).1,
        hab.le, ?_⟩
    rw [← residualIntervalTrace_union_relIcc_exterior
      hab.left_mem hab.right_mem habSides.1 habSides.2]
    exact hlast.isFullyPairedOn.union hab.isFullyPairedOn
  by_cases hall : relIcc active a b = active
  · apply Finset.Subset.antisymm
    · exact relIcc_subset_active _ _ _
    · intro x hx
      have hxActive :
          x ∈ relIcc active a b := by
        rw [hall]
        exact (mem_residualIntervalExterior_iff.mp hx).1
      exact mem_relIcc.mpr
        ⟨hx, (mem_relIcc.mp hxActive).2.1,
          (mem_relIcc.mp hxActive).2.2⟩
  · have habChain :
        (a, b) ∈ pre ++ [last] := by
      rw [← hchain]
      exact mem_momentResidualIntervalChain.mpr
        (mem_momentResidualProperIntervals.mpr
          ⟨habActive, hall⟩)
    rcases List.mem_append.mp habChain with habPre | habLast
    · have hcross :
          LaterCrossCutIntervalContains (a, b) last :=
        (List.pairwise_append.mp hpair).2.2
          (a, b) habPre last (by simp)
      exact False.elim
        ((not_lt_of_ge hcross.1.le) habSides.1)
    · have hEqLast : (a, b) = last := by
        simpa using habLast
      have haeq : a = last.1 :=
        congrArg Prod.fst hEqLast
      exact False.elim ((ne_of_lt habSides.1) haeq)

/-- All successive shells and the final exterior after a given chain
entry are primitive. -/
theorem nestedResidualShells_forall_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (pre : List (Fin (2 * m) × Fin (2 * m)))
    (previous : Fin (2 * m) × Fin (2 * m))
    (rest : List (Fin (2 * m) × Fin (2 * m)))
    (hchain :
      momentResidualIntervalChain κp κm π =
        pre ++ previous :: rest) :
    (nestedResidualShells
      (momentResidualActive κp κm) previous rest).Forall
        (IsRelPrimitiveOn
          (momentCombinedPairing κp κm π)) := by
  induction rest generalizing pre previous with
  | nil =>
      rw [nestedResidualShells, List.forall_cons]
      exact
        ⟨last_residualIntervalExterior_isRelPrimitiveOn
            κp κm π pre previous (by simpa using hchain),
          by trivial⟩
  | cons next rest ih =>
      simp only [nestedResidualShells, List.forall_cons]
      constructor
      · exact adjacent_residualIntervalShell_isRelPrimitiveOn
          κp κm π pre previous next rest hchain
      · apply ih (pre := pre ++ [previous]) (previous := next)
        simpa only [List.append_assoc, List.singleton_append]
          using hchain

/-- Starting from any trace in a nested chain, its later shells and final
exterior complete it to the whole active carrier. -/
theorem residualIntervalTrace_union_nestedResidualShells
    {n : ℕ} (active : Finset (Fin n))
    (previous : Fin n × Fin n)
    (rest : List (Fin n × Fin n))
    (hpair :
      (previous :: rest).Pairwise
        LaterCrossCutIntervalContains) :
    residualIntervalTrace active previous ∪
        finsetUnionList
          (nestedResidualShells active previous rest) =
      active := by
  induction rest generalizing previous with
  | nil =>
      simp only [nestedResidualShells, finsetUnionList,
        Finset.union_empty]
      exact residualIntervalTrace_union_exterior active previous
  | cons next rest ih =>
      have hcons := List.pairwise_cons.mp hpair
      have hnext :
          LaterCrossCutIntervalContains previous next :=
        hcons.1 next (by simp)
      have htail :
          (next :: rest).Pairwise
            LaterCrossCutIntervalContains :=
        hcons.2
      simp only [nestedResidualShells, finsetUnionList]
      rw [← Finset.union_assoc,
        residualIntervalTrace_union_shell hnext]
      exact ih next htail

/-- The block list of any nested chain covers the active carrier exactly. -/
theorem finsetUnionList_residualCollapseBlocks
    {n : ℕ} (active : Finset (Fin n))
    (chain : List (Fin n × Fin n))
    (hpair :
      chain.Pairwise LaterCrossCutIntervalContains) :
    finsetUnionList (residualCollapseBlocks active chain) =
      active := by
  cases chain with
  | nil =>
      simp [residualCollapseBlocks, finsetUnionList]
  | cons first rest =>
      simp only [residualCollapseBlocks, finsetUnionList]
      exact residualIntervalTrace_union_nestedResidualShells
        active first rest hpair

/-- Every later shell and the final exterior are fully paired, provided
the active carrier and all interval traces are fully paired. -/
theorem nestedResidualShells_forall_isFullyPairedOn
    {n : ℕ} {κ : PartialPairing (Fin n)}
    {active : Finset (Fin n)}
    (hactive : IsFullyPairedOn κ active)
    (previous : Fin n × Fin n)
    (hprevious :
      IsRelFullyPaired κ active previous.1 previous.2)
    (rest : List (Fin n × Fin n))
    (hrest :
      ∀ p ∈ rest,
        IsRelFullyPaired κ active p.1 p.2) :
    (nestedResidualShells active previous rest).Forall
      (IsFullyPairedOn κ) := by
  induction rest generalizing previous with
  | nil =>
      rw [nestedResidualShells]
      rw [List.forall_cons]
      exact ⟨hactive.sdiff hprevious.isFullyPairedOn,
        by trivial⟩
  | cons next rest ih =>
      have hnext :
          IsRelFullyPaired κ active next.1 next.2 :=
        hrest next (by simp)
      simp only [nestedResidualShells, List.forall_cons]
      constructor
      · exact hnext.isFullyPairedOn.sdiff
          hprevious.isFullyPairedOn
      · exact ih next hnext fun p hp =>
          hrest p (by simp [hp])

/-- Every block in a collapse decomposition is fully paired. -/
theorem residualCollapseBlocks_forall_isFullyPairedOn
    {n : ℕ} {κ : PartialPairing (Fin n)}
    {active : Finset (Fin n)}
    (hactive : IsFullyPairedOn κ active)
    (chain : List (Fin n × Fin n))
    (hchain :
      ∀ p ∈ chain,
        IsRelFullyPaired κ active p.1 p.2) :
    (residualCollapseBlocks active chain).Forall
      (IsFullyPairedOn κ) := by
  cases chain with
  | nil =>
      simp [residualCollapseBlocks, hactive]
  | cons first rest =>
      have hfirst :
          IsRelFullyPaired κ active first.1 first.2 :=
        hchain first (by simp)
      simp only [residualCollapseBlocks, List.forall_cons]
      exact ⟨hfirst.isFullyPairedOn,
        nestedResidualShells_forall_isFullyPairedOn
          hactive first hfirst rest
          (fun p hp => hchain p (by simp [hp]))⟩

/-- Concrete collapse blocks for one R-324 contraction entity. -/
def momentResidualCollapseBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    List (Finset (Fin (2 * m))) :=
  residualCollapseBlocks (momentResidualActive κp κm)
    (momentResidualIntervalChain κp κm π)

/-- The concrete R-324 collapse blocks cover the doubled residual
carrier exactly. -/
theorem finsetUnionList_momentResidualCollapseBlocks
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    finsetUnionList
        (momentResidualCollapseBlocks κp κm π) =
      momentResidualActive κp κm := by
  exact finsetUnionList_residualCollapseBlocks
    (momentResidualActive κp κm)
    (momentResidualIntervalChain κp κm π)
    (momentResidualIntervalChain_pairwise_laterContains
      κp κm π)

/-- Every concrete R-324 collapse block is closed and contains no single
of the combined pairing. -/
theorem momentResidualCollapseBlocks_forall_isFullyPairedOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentResidualCollapseBlocks κp κm π).Forall
      (IsFullyPairedOn
        (momentCombinedPairing κp κm π)) := by
  apply residualCollapseBlocks_forall_isFullyPairedOn
    (momentResidualActive_isFullyPairedOn κp κm π)
  intro p hp
  exact
    (mem_momentResidualProperIntervals.mp
      (mem_momentResidualIntervalChain.mp hp)).1

/-- Every concrete block used by the successive R-324 residual collapse
is primitive on its sparse carrier. -/
theorem momentResidualCollapseBlocks_forall_isRelPrimitiveOn
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    (momentResidualCollapseBlocks κp κm π).Forall
      (IsRelPrimitiveOn
        (momentCombinedPairing κp κm π)) := by
  unfold momentResidualCollapseBlocks
  cases hchain :
      momentResidualIntervalChain κp κm π with
  | nil =>
      rw [residualCollapseBlocks, List.forall_cons]
      exact
        ⟨momentResidualActive_isRelPrimitiveOn_of_chain_eq_nil
            κp κm π hchain,
          by trivial⟩
  | cons first rest =>
      simp only [residualCollapseBlocks, List.forall_cons]
      constructor
      · exact residualIntervalTrace_head_isRelPrimitiveOn
          κp κm π first rest hchain
      · exact nestedResidualShells_forall_isRelPrimitiveOn
          κp κm π [] first rest (by simpa using hchain)

end Anderson4D
