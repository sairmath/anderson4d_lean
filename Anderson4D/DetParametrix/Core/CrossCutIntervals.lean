import Anderson4D.DetParametrix.Core.MomentPairing

/-!
# Cross-cut interval geometry for the doubled moment reduction

After the within-half intervals have been removed in paper §4.2 Step 2,
every proper fully paired interval of the residual doubled pairing
straddles the central cut.  This file isolates the order-theoretic part
of Step 3: laminar intervals which straddle one cut cannot be disjoint,
and the extraction order therefore lists them from inside to outside.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

/-- An interval on `Fin n` straddles the cut immediately before `cut`
when its left endpoint lies below `cut` and its right endpoint does not. -/
def IntervalStraddlesCut
    {n : ℕ} (cut : ℕ) (p : Fin n × Fin n) : Prop :=
  p.1.val < cut ∧ cut ≤ p.2.val

/-- For two cross-cut intervals, the second one strictly contains the
first.  This is the direction forced by the paper's extraction order. -/
def LaterCrossCutIntervalContains
    {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  q.1 < p.1 ∧ p.2 < q.2

/-! ## Geometry of the doubled residual carrier -/

@[simp]
theorem leftMomentIndex_mem_momentResidualActive_iff
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (i : Fin m) :
    leftMomentIndex i ∈ momentResidualActive κp κm ↔
      i ∈ finalActive κp := by
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have hji' : j = i :=
        leftMomentIndex_injective hji
      simpa only [hji'] using hj
    · obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hi
      have hval := congrArg Fin.val hji
      simp only [leftMomentIndex, rightMomentIndex] at hval
      have hiLt := i.isLt
      omega
  · intro hi
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

@[simp]
theorem rightMomentIndex_mem_momentResidualActive_iff
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (j : Fin m) :
    rightMomentIndex j ∈ momentResidualActive κp κm ↔
      j ∈ finalActive κm := by
  constructor
  · intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, _, hij⟩ := Finset.mem_image.mp hj
      have hval := congrArg Fin.val hij
      simp only [leftMomentIndex, rightMomentIndex] at hval
      have hiLt := i.isLt
      omega
    · obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
      have hij' : i = j :=
        rightMomentIndex_injective hij
      simpa only [hij'] using hi
  · intro hj
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

/-- A residual index below the central cut comes uniquely from the left
copy. -/
theorem exists_leftMomentIndex_of_mem_momentResidualActive
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {x : Fin (2 * m)}
    (hx : x ∈ momentResidualActive κp κm)
    (hxLeft : x.val < m) :
    ∃ i : Fin m,
      i ∈ finalActive κp ∧ x = leftMomentIndex i := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi, hix.symm⟩
  · obtain ⟨j, _, hjx⟩ := Finset.mem_image.mp hx
    have hval := congrArg Fin.val hjx
    simp only [rightMomentIndex] at hval
    omega

/-- A residual index at or above the central cut comes uniquely from the
right copy. -/
theorem exists_rightMomentIndex_of_mem_momentResidualActive
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {x : Fin (2 * m)}
    (hx : x ∈ momentResidualActive κp κm)
    (hxRight : m ≤ x.val) :
    ∃ j : Fin m,
      j ∈ finalActive κm ∧ x = rightMomentIndex j := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hx
    have hval := congrArg Fin.val hix
    simp only [leftMomentIndex] at hval
    have hiLt := i.isLt
    omega
  · obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
    exact ⟨j, hj, hjx.symm⟩

/-- If both endpoints lie below the cut, the relative interval in the
doubled residual carrier is exactly the corresponding left-image
relative interval. -/
theorem relIcc_momentResidualActive_left
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (a b : Fin m) :
    relIcc (momentResidualActive κp κm)
        (leftMomentIndex a) (leftMomentIndex b) =
      relIcc ((finalActive κp).image leftMomentIndex)
        (leftMomentIndex a) (leftMomentIndex b) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxActive, hax, hxb⟩ := mem_relIcc.mp hx
    refine mem_relIcc.mpr ⟨?_, hax, hxb⟩
    rcases Finset.mem_union.mp hxActive with hxLeft | hxRight
    · exact hxLeft
    · obtain ⟨j, _, hjx⟩ := Finset.mem_image.mp hxRight
      rw [← hjx] at hxb
      change m + j.val ≤ b.val at hxb
      have hbLt := b.isLt
      omega
  · intro hx
    obtain ⟨hxActive, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨Finset.mem_union_left _ hxActive, hax, hxb⟩

/-- Right-copy counterpart of
`relIcc_momentResidualActive_left`. -/
theorem relIcc_momentResidualActive_right
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (a b : Fin m) :
    relIcc (momentResidualActive κp κm)
        (rightMomentIndex a) (rightMomentIndex b) =
      relIcc ((finalActive κm).image rightMomentIndex)
        (rightMomentIndex a) (rightMomentIndex b) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxActive, hax, hxb⟩ := mem_relIcc.mp hx
    refine mem_relIcc.mpr ⟨?_, hax, hxb⟩
    rcases Finset.mem_union.mp hxActive with hxLeft | hxRight
    · obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hxLeft
      rw [← hix] at hax
      change m + a.val ≤ i.val at hax
      have hiLt := i.isLt
      omega
    · exact hxRight
  · intro hx
    obtain ⟨hxActive, hax, hxb⟩ := mem_relIcc.mp hx
    exact mem_relIcc.mpr
      ⟨Finset.mem_union_right _ hxActive, hax, hxb⟩

/-! ## Every residual fully paired interval crosses the cut -/

/-- No relative fully paired interval of the doubled residual carrier
can have both endpoints in the left copy: reflection would contradict
terminality of `finalActive κp`. -/
theorem not_isRelFullyPaired_momentResidualActive_left
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) (a b : Fin m) :
    ¬IsRelFullyPaired (momentCombinedPairing κp κm π)
      (momentResidualActive κp κm)
      (leftMomentIndex a) (leftMomentIndex b) := by
  intro h
  have hleft :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        ((finalActive κp).image leftMomentIndex)
        (leftMomentIndex a) (leftMomentIndex b) := by
    have ha :
        a ∈ finalActive κp :=
      (leftMomentIndex_mem_momentResidualActive_iff
        κp κm a).mp h.left_mem
    have hb :
        b ∈ finalActive κp :=
      (leftMomentIndex_mem_momentResidualActive_iff
        κp κm b).mp h.right_mem
    refine ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      h.le, ?_⟩
    rw [← relIcc_momentResidualActive_left κp κm a b]
    exact h.isFullyPairedOn
  have horiginal :
      IsRelFullyPaired κp (finalActive κp) a b :=
    isRelFullyPaired_image_leftMomentIndex_iff.mp hleft
  exact extract_fuel_sufficient κp
    ⟨a, b, horiginal⟩

/-- Right-copy counterpart of
`not_isRelFullyPaired_momentResidualActive_left`. -/
theorem not_isRelFullyPaired_momentResidualActive_right
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) (a b : Fin m) :
    ¬IsRelFullyPaired (momentCombinedPairing κp κm π)
      (momentResidualActive κp κm)
      (rightMomentIndex a) (rightMomentIndex b) := by
  intro h
  have hright :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        ((finalActive κm).image rightMomentIndex)
        (rightMomentIndex a) (rightMomentIndex b) := by
    have ha :
        a ∈ finalActive κm :=
      (rightMomentIndex_mem_momentResidualActive_iff
        κp κm a).mp h.left_mem
    have hb :
        b ∈ finalActive κm :=
      (rightMomentIndex_mem_momentResidualActive_iff
        κp κm b).mp h.right_mem
    refine ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      h.le, ?_⟩
    rw [← relIcc_momentResidualActive_right κp κm a b]
    exact h.isFullyPairedOn
  have horiginal :
      IsRelFullyPaired κm (finalActive κm) a b :=
    isRelFullyPaired_image_rightMomentIndex_iff.mp hright
  exact extract_fuel_sufficient κm
    ⟨a, b, horiginal⟩

/-- Every relative fully paired interval of the residual doubled carrier
straddles its central cut.  This is the precise combinatorial assertion
at the start of paper §4.2 Step 3. -/
theorem IsRelFullyPaired.momentResidualActive_straddlesCut
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {a b : Fin (2 * m)}
    (h :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) a b) :
    IntervalStraddlesCut m (a, b) := by
  constructor
  · by_contra haLeft
    have haRight : m ≤ a.val :=
      Nat.le_of_not_gt haLeft
    have habVal : a.val ≤ b.val := h.le
    have hbRight : m ≤ b.val := haRight.trans habVal
    obtain ⟨i, _, hai⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive
        h.left_mem haRight
    obtain ⟨j, _, hbj⟩ :=
      exists_rightMomentIndex_of_mem_momentResidualActive
        h.right_mem hbRight
    rw [hai, hbj] at h
    exact
      (not_isRelFullyPaired_momentResidualActive_right
        κp κm π i j) h
  · by_contra hbRight
    have hbLeft : b.val < m :=
      Nat.lt_of_not_ge hbRight
    have habVal : a.val ≤ b.val := h.le
    have haLeft : a.val < m := habVal.trans_lt hbLeft
    obtain ⟨i, _, hai⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive
        h.left_mem haLeft
    obtain ⟨j, _, hbj⟩ :=
      exists_leftMomentIndex_of_mem_momentResidualActive
        h.right_mem hbLeft
    rw [hai, hbj] at h
    exact
      (not_isRelFullyPaired_momentResidualActive_left
        κp κm π i j) h

/-! ## Nesting of residual fully paired intervals -/

/-- When two fully paired relative intervals cross as
`a < c ≤ b < d`, their left difference is a nonempty fully paired
relative interval ending strictly before `c`. -/
theorem exists_left_fullyPairedInterval_of_crossing
    {n : ℕ} {κ : PartialPairing (Fin n)}
    {active : Finset (Fin n)} {a b c d : Fin n}
    (hI : IsRelFullyPaired κ active a b)
    (hJ : IsRelFullyPaired κ active c d)
    (hac : a < c) (_hcb : c ≤ b) (hbd : b ≤ d) :
    ∃ e : Fin n,
      IsRelFullyPaired κ active a e ∧ e < c := by
  let B :=
    relIcc active a b \ relIcc active c d
  have haNotJ :
      a ∉ relIcc active c d := by
    intro haJ
    exact (not_le_of_gt hac) (mem_relIcc.mp haJ).2.1
  have haB : a ∈ B :=
    Finset.mem_sdiff.mpr
      ⟨hI.left_mem_relIcc, haNotJ⟩
  have hBne : B.Nonempty := ⟨a, haB⟩
  let e : Fin n := B.max' hBne
  have heB : e ∈ B :=
    Finset.max'_mem B hBne
  have heParts := Finset.mem_sdiff.mp heB
  have heI := mem_relIcc.mp heParts.1
  have heLtC : e < c := by
    by_contra hnot
    have hce : c ≤ e := le_of_not_gt hnot
    apply heParts.2
    exact mem_relIcc.mpr
      ⟨heI.1, hce, heI.2.2.trans hbd⟩
  have haLeE : a ≤ e :=
    Finset.le_max' B a haB
  have hBeq :
      B = relIcc active a e := by
    ext x
    constructor
    · intro hx
      have hxParts := Finset.mem_sdiff.mp hx
      have hxI := mem_relIcc.mp hxParts.1
      exact mem_relIcc.mpr
        ⟨hxI.1, hxI.2.1,
          Finset.le_max' B x hx⟩
    · intro hx
      have hxRel := mem_relIcc.mp hx
      apply Finset.mem_sdiff.mpr
      constructor
      · exact mem_relIcc.mpr
          ⟨hxRel.1, hxRel.2.1,
            hxRel.2.2.trans heI.2.2⟩
      · intro hxJ
        have hcx : c ≤ x :=
          (mem_relIcc.mp hxJ).2.1
        exact (not_le_of_gt
          (hxRel.2.2.trans_lt heLtC)) hcx
  have hBfull :
      IsFullyPairedOn κ B :=
    hI.isFullyPairedOn.sdiff hJ.isFullyPairedOn
  have hrel :
      IsRelFullyPaired κ active a e := by
    refine ⟨hI.left_mem, heI.1, haLeE, ?_⟩
    rw [← hBeq]
    exact hBfull
  exact ⟨e, hrel, heLtC⟩

/-- Weak nesting relation, allowing equality of one endpoint. -/
def ResidualIntervalsWeaklyNested
    {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  (p.1 ≤ q.1 ∧ q.2 ≤ p.2) ∨
    (q.1 ≤ p.1 ∧ p.2 ≤ q.2)

/-- Any two fully paired intervals of the doubled residual carrier are
weakly nested.  A crossing would produce, by set difference, a fully
paired interval wholly to the left of the central cut. -/
theorem IsRelFullyPaired.momentResidualActive_weaklyNested
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {a b c d : Fin (2 * m)}
    (hI :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) a b)
    (hJ :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) c d) :
    ResidualIntervalsWeaklyNested (a, b) (c, d) := by
  have hIcut := hI.momentResidualActive_straddlesCut
  have hJcut := hJ.momentResidualActive_straddlesCut
  by_cases hac : a ≤ c
  · by_cases hdb : d ≤ b
    · exact Or.inl ⟨hac, hdb⟩
    · have hbd : b < d := lt_of_not_ge hdb
      by_cases hacEq : a = c
      · exact Or.inr ⟨hacEq.ge, hbd.le⟩
      · have hacLt : a < c :=
          lt_of_le_of_ne hac hacEq
        obtain ⟨e, he, hec⟩ :=
          exists_left_fullyPairedInterval_of_crossing
            hI hJ hacLt
              (hJcut.1.le.trans hIcut.2)
              hbd.le
        have heCut :=
          he.momentResidualActive_straddlesCut
        have heValLt : e.val < m := by
          have hecVal : e.val < c.val := hec
          exact hecVal.trans hJcut.1
        exact False.elim
          (not_lt_of_ge heCut.2 heValLt)
  · have hca : c < a := lt_of_not_ge hac
    by_cases hbd : b ≤ d
    · exact Or.inr ⟨hca.le, hbd⟩
    · have hdb : d < b := lt_of_not_ge hbd
      obtain ⟨e, he, hea⟩ :=
        exists_left_fullyPairedInterval_of_crossing
          hJ hI hca
            (hIcut.1.le.trans hJcut.2)
            hdb.le
      have heCut :=
        he.momentResidualActive_straddlesCut
      have heValLt : e.val < m := by
        have heaVal : e.val < a.val := hea
        exact heaVal.trans hIcut.1
      exact False.elim
        (not_lt_of_ge heCut.2 heValLt)

/-- If two fully paired relative intervals share their left endpoint and
the second extends farther right, their right difference is a nonempty
fully paired relative interval starting strictly after the first one. -/
theorem exists_right_fullyPairedInterval_of_same_left
    {n : ℕ} {κ : PartialPairing (Fin n)}
    {active : Finset (Fin n)} {a b d : Fin n}
    (hI : IsRelFullyPaired κ active a b)
    (hJ : IsRelFullyPaired κ active a d)
    (hbd : b < d) :
    ∃ e : Fin n,
      IsRelFullyPaired κ active e d ∧ b < e := by
  let B :=
    relIcc active a d \ relIcc active a b
  have hdNotI :
      d ∉ relIcc active a b := by
    intro hdI
    exact (not_le_of_gt hbd) (mem_relIcc.mp hdI).2.2
  have hdB : d ∈ B :=
    Finset.mem_sdiff.mpr
      ⟨hJ.right_mem_relIcc, hdNotI⟩
  have hBne : B.Nonempty := ⟨d, hdB⟩
  let e : Fin n := B.min' hBne
  have heB : e ∈ B :=
    Finset.min'_mem B hBne
  have heParts := Finset.mem_sdiff.mp heB
  have heJ := mem_relIcc.mp heParts.1
  have hbLtE : b < e := by
    by_contra hnot
    have heb : e ≤ b := le_of_not_gt hnot
    apply heParts.2
    exact mem_relIcc.mpr
      ⟨heJ.1, heJ.2.1, heb⟩
  have heLeD : e ≤ d :=
    Finset.min'_le B d hdB
  have hBeq :
      B = relIcc active e d := by
    ext x
    constructor
    · intro hx
      have hxParts := Finset.mem_sdiff.mp hx
      have hxJ := mem_relIcc.mp hxParts.1
      exact mem_relIcc.mpr
        ⟨hxJ.1, Finset.min'_le B x hx, hxJ.2.2⟩
    · intro hx
      have hxRel := mem_relIcc.mp hx
      apply Finset.mem_sdiff.mpr
      constructor
      · exact mem_relIcc.mpr
          ⟨hxRel.1, heJ.2.1.trans hxRel.2.1,
            hxRel.2.2⟩
      · intro hxI
        have hxb : x ≤ b :=
          (mem_relIcc.mp hxI).2.2
        exact (not_le_of_gt
          (hbLtE.trans_le hxRel.2.1)) hxb
  have hBfull :
      IsFullyPairedOn κ B :=
    hJ.isFullyPairedOn.sdiff hI.isFullyPairedOn
  have hrel :
      IsRelFullyPaired κ active e d := by
    refine ⟨heJ.1, hJ.right_mem, heLeD, ?_⟩
    rw [← hBeq]
    exact hBfull
  exact ⟨e, hrel, hbLtE⟩

/-- Distinct fully paired intervals of the doubled residual carrier are
strictly nested at both endpoints, exactly the chain
`aₜ < ⋯ < a₁ ≤ cut < b₁ < ⋯ < bₜ` in paper §4.2 Step 3. -/
theorem IsRelFullyPaired.momentResidualActive_strictlyNested
    {m : ℕ} {κp κm : PartialPairing (Fin m)}
    {π : κp.singles ≃ κm.singles}
    {a b c d : Fin (2 * m)}
    (hI :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) a b)
    (hJ :
      IsRelFullyPaired (momentCombinedPairing κp κm π)
        (momentResidualActive κp κm) c d)
    (hne : (a, b) ≠ (c, d)) :
    (a < c ∧ d < b) ∨ (c < a ∧ b < d) := by
  rcases hI.momentResidualActive_weaklyNested hJ with hnest | hnest
  · have hac : a < c := by
      rcases hnest with ⟨hac, hdb⟩
      by_cases heq : a = c
      · have hdbLt : d < b := by
          apply lt_of_le_of_ne hdb
          intro hEq
          apply hne
          exact Prod.ext heq hEq.symm
        obtain ⟨e, he, hde⟩ :=
          exists_right_fullyPairedInterval_of_same_left
            hJ (heq ▸ hI) hdbLt
        have heCut := he.momentResidualActive_straddlesCut
        have heRight : m ≤ e.val := by
          have hdCut := hJ.momentResidualActive_straddlesCut
          have hdeVal : d.val < e.val := hde
          exact hdCut.2.trans hdeVal.le
        exact False.elim
          ((not_lt_of_ge heRight) heCut.1)
      · exact lt_of_le_of_ne hac heq
    have hdb : d < b := by
      rcases hnest with ⟨_, hdb⟩
      by_cases heq : d = b
      · obtain ⟨e, he, hec⟩ :=
          exists_left_fullyPairedInterval_of_crossing
            hI hJ hac
              (by simpa only [heq] using hJ.le)
              heq.ge
        have heCut := he.momentResidualActive_straddlesCut
        have heLeft : e.val < m := by
          have hecVal : e.val < c.val := hec
          exact hecVal.trans
            hJ.momentResidualActive_straddlesCut.1
        exact False.elim
          ((not_lt_of_ge heCut.2) heLeft)
      · exact lt_of_le_of_ne hdb heq
    exact Or.inl ⟨hac, hdb⟩
  · have hca : c < a := by
      rcases hnest with ⟨hca, hbd⟩
      by_cases heq : c = a
      · have hbdLt : b < d := by
          apply lt_of_le_of_ne hbd
          intro hEq
          apply hne
          exact Prod.ext heq.symm hEq
        obtain ⟨e, he, hbe⟩ :=
          exists_right_fullyPairedInterval_of_same_left
            hI (heq ▸ hJ) hbdLt
        have heCut := he.momentResidualActive_straddlesCut
        have heRight : m ≤ e.val := by
          have hbCut := hI.momentResidualActive_straddlesCut
          have hbeVal : b.val < e.val := hbe
          exact hbCut.2.trans hbeVal.le
        exact False.elim
          ((not_lt_of_ge heRight) heCut.1)
      · exact lt_of_le_of_ne hca heq
    have hbd : b < d := by
      rcases hnest with ⟨_, hbd⟩
      by_cases heq : b = d
      · obtain ⟨e, he, hea⟩ :=
          exists_left_fullyPairedInterval_of_crossing
            hJ hI hca
              (by simpa only [heq] using hI.le)
              heq.ge
        have heCut := he.momentResidualActive_straddlesCut
        have heLeft : e.val < m := by
          have heaVal : e.val < a.val := hea
          exact heaVal.trans
            hI.momentResidualActive_straddlesCut.1
        exact False.elim
          ((not_lt_of_ge heCut.2) heLeft)
      · exact lt_of_le_of_ne hbd heq
    exact Or.inr ⟨hca, hbd⟩

/-- Two laminar intervals which straddle the same cut are nested. -/
theorem ReductionIntervalsLaminar.nested_of_straddlesCut
    {n cut : ℕ} {p q : Fin n × Fin n}
    (hlam : ReductionIntervalsLaminar p q)
    (hp : IntervalStraddlesCut cut p)
    (hq : IntervalStraddlesCut cut q) :
    (p.1 < q.1 ∧ q.2 < p.2) ∨
      (q.1 < p.1 ∧ p.2 < q.2) := by
  rcases hp with ⟨hpLeft, hpRight⟩
  rcases hq with ⟨hqLeft, hqRight⟩
  rcases hlam with h | h | h | h
  · exfalso
    exact (by omega)
  · exfalso
    exact (by omega)
  · exact Or.inl h
  · exact Or.inr h

/-- Directional extraction compatibility becomes strict containment
once both intervals straddle the same cut. -/
theorem EarlierReductionIntervalCompatible.laterContains_of_straddlesCut
    {n cut : ℕ} {p q : Fin n × Fin n}
    (hcompat : EarlierReductionIntervalCompatible p q)
    (hp : IntervalStraddlesCut cut p)
    (hq : IntervalStraddlesCut cut q) :
    LaterCrossCutIntervalContains p q := by
  rcases hp with ⟨hpLeft, hpRight⟩
  rcases hq with ⟨hqLeft, hqRight⟩
  rcases hcompat with h | h | h
  · exfalso
    exact (by omega)
  · exfalso
    exact (by omega)
  · exact h

/-- A list whose intervals are compatible in extraction order and all
straddle one cut is ordered by strict containment from inside to outside. -/
theorem List.Pairwise.laterCrossCutIntervalContains
    {n cut : ℕ} {l : List (Fin n × Fin n)}
    (hcompat : l.Pairwise EarlierReductionIntervalCompatible)
    (hcut : ∀ p ∈ l, IntervalStraddlesCut cut p) :
    l.Pairwise LaterCrossCutIntervalContains := by
  induction l with
  | nil =>
      exact List.Pairwise.nil
  | cons p l ih =>
      rw [List.pairwise_cons] at hcompat ⊢
      constructor
      · intro q hq
        exact
          (hcompat.1 q hq).laterContains_of_straddlesCut
            (hcut p (by simp))
            (hcut q (by simp [hq]))
      · exact ih hcompat.2 (fun q hq => hcut q (by simp [hq]))

/-- If all intervals selected from a pairing straddle a fixed cut, then
the actual Definition 3.1 extraction order is strictly inside-to-outside.
This is the order pattern `a₁ > ⋯ > aₙ` and `b₁ < ⋯ < bₙ` used in
paper §4.2 Step 3. -/
theorem extract_pairwise_laterCrossCutIntervalContains
    {n cut : ℕ} (κ : PartialPairing (Fin n))
    (hcut :
      ∀ p ∈ extract κ, IntervalStraddlesCut cut p) :
    (extract κ).Pairwise LaterCrossCutIntervalContains :=
  List.Pairwise.laterCrossCutIntervalContains
    (extractAux_pairwise_earlierCompatible κ n Finset.univ)
    hcut

end Anderson4D
