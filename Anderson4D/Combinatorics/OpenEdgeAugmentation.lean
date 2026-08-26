import Anderson4D.Combinatorics.PrimitiveWord

/-!
# Closing one open covariance edge

After a marked covariance is replaced by one Fourier character, its two
endpoints no longer have to carry the same spatial cell label.  The
remaining covariance edges still form a pairing.  This file closes that
one open edge by adjoining two final positions: the old marked endpoints
are paired with copies carrying their respective labels.

The construction is deliberately made before any word or pairing sum is
estimated.  It is the combinatorial bridge from the genuine one-open-edge
R-324 fibre to the existing permutation-sum machine.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- The involution on `Fin m ⊕ Fin 2` obtained by cutting the edge
`a ↔ b` and pairing its endpoints with the two new positions. -/
def openEdgeAugmentedSumPairing
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b) :
    PartialPairing (Fin m ⊕ Fin 2) := by
  let f : Fin m ⊕ Fin 2 → Fin m ⊕ Fin 2
    | Sum.inl i =>
        if i = a then Sum.inr 0
        else if i = b then Sum.inr 1
        else Sum.inl (κ i)
    | Sum.inr j =>
        if j = 0 then Sum.inl a else Sum.inl b
  refine ⟨f, ?_⟩
  intro i
  rcases i with i | j
  · by_cases hia : i = a
    · subst i
      simp [f]
    · by_cases hib : i = b
      · subst i
        simp [f, hia]
      · have hκba : κ b = a := by
          rw [← hκab]
          exact κ.apply_apply a
        have hκia : κ i ≠ a := by
          intro h
          have : i = b := by
            simpa [hκab] using congrArg κ h
          exact hib this
        have hκib : κ i ≠ b := by
          intro h
          have : i = a := by
            simpa [hκba] using congrArg κ h
          exact hia this
        simp [f, hia, hib, hκia, hκib]
  · fin_cases j
    · simp [f]
    · simp [f, Ne.symm hab]

/-- The same augmented pairing on the ordered carrier `Fin (m + 2)`. -/
def openEdgeAugmentedPairing
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b) :
    PartialPairing (Fin (m + 2)) :=
  PartialPairing.congr finSumFinEquiv
    (openEdgeAugmentedSumPairing κ a b hκab hab)

/-- The first new position, immediately after the old carrier. -/
def openEdgeFirstNew (m : ℕ) : Fin (m + 2) :=
  Fin.natAdd m 0

/-- The final new position. -/
def openEdgeSecondNew (m : ℕ) : Fin (m + 2) :=
  Fin.natAdd m 1

@[simp]
theorem openEdgeFirstNew_val (m : ℕ) :
    (openEdgeFirstNew m).val = m := rfl

@[simp]
theorem openEdgeSecondNew_val (m : ℕ) :
    (openEdgeSecondNew m).val = m + 1 := rfl

@[simp]
theorem openEdgeAugmentedPairing_old_left
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b) :
    openEdgeAugmentedPairing κ a b hκab hab
        (Fin.castAdd 2 a) =
      openEdgeFirstNew m := by
  simp [openEdgeAugmentedPairing,
    openEdgeAugmentedSumPairing, openEdgeFirstNew]

@[simp]
theorem openEdgeAugmentedPairing_old_right
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b) :
    openEdgeAugmentedPairing κ a b hκab hab
        (Fin.castAdd 2 b) =
      openEdgeSecondNew m := by
  simp [openEdgeAugmentedPairing,
    openEdgeAugmentedSumPairing, openEdgeSecondNew,
    Ne.symm hab]

@[simp]
theorem openEdgeAugmentedPairing_firstNew
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b) :
    openEdgeAugmentedPairing κ a b hκab hab
        (openEdgeFirstNew m) =
      Fin.castAdd 2 a := by
  simp [openEdgeAugmentedPairing,
    openEdgeAugmentedSumPairing, openEdgeFirstNew]

@[simp]
theorem openEdgeAugmentedPairing_secondNew
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b) :
    openEdgeAugmentedPairing κ a b hκab hab
        (openEdgeSecondNew m) =
      Fin.castAdd 2 b := by
  simp [openEdgeAugmentedPairing,
    openEdgeAugmentedSumPairing, openEdgeSecondNew]

@[simp]
theorem openEdgeAugmentedPairing_old_other
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b i : Fin m) (hκab : κ a = b)
    (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b) :
    openEdgeAugmentedPairing κ a b hκab
        hab
        (Fin.castAdd 2 i) =
      Fin.castAdd 2 (κ i) := by
  simp [openEdgeAugmentedPairing,
    openEdgeAugmentedSumPairing, hia, hib]

/-! ## The corresponding word -/

/-- Copy the labels at the two opened endpoints onto the two new
positions. -/
def openEdgeAugmentedSumWord
    {α : Type*} {m : ℕ} (w : Fin m → α)
    (a b : Fin m) : Fin m ⊕ Fin 2 → α
  | Sum.inl i => w i
  | Sum.inr j => if j = 0 then w a else w b

/-- The augmented word on the ordered carrier `Fin (m + 2)`. -/
def openEdgeAugmentedWord
    {α : Type*} {m : ℕ} (w : Fin m → α)
    (a b : Fin m) : Fin (m + 2) → α :=
  fun i =>
    openEdgeAugmentedSumWord w a b
      (finSumFinEquiv.symm i)

@[simp]
theorem openEdgeAugmentedWord_old
    {α : Type*} {m : ℕ} (w : Fin m → α)
    (a b i : Fin m) :
    openEdgeAugmentedWord w a b (Fin.castAdd 2 i) =
      w i := by
  simp [openEdgeAugmentedWord, openEdgeAugmentedSumWord]

@[simp]
theorem openEdgeAugmentedWord_firstNew
    {α : Type*} {m : ℕ} (w : Fin m → α)
    (a b : Fin m) :
    openEdgeAugmentedWord w a b (openEdgeFirstNew m) =
      w a := by
  simp [openEdgeAugmentedWord, openEdgeAugmentedSumWord,
    openEdgeFirstNew]

@[simp]
theorem openEdgeAugmentedWord_secondNew
    {α : Type*} {m : ℕ} (w : Fin m → α)
    (a b : Fin m) :
    openEdgeAugmentedWord w a b (openEdgeSecondNew m) =
      w b := by
  simp [openEdgeAugmentedWord, openEdgeAugmentedSumWord,
    openEdgeSecondNew]

/-- If every unmarked old edge respects the original word, the closed
augmented pairing respects the augmented word. -/
theorem openEdgeAugmentedPairing_respectsWord
    {α : Type*} {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (w : Fin m → α)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    (openEdgeAugmentedPairing κ a b hκab hab).RespectsWord
      (openEdgeAugmentedWord w a b) := by
  intro i
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  rcases s with i | j
  · by_cases hia : i = a
    · subst i
      simp [openEdgeAugmentedPairing,
        openEdgeAugmentedSumPairing,
        openEdgeAugmentedWord, openEdgeAugmentedSumWord]
    · by_cases hib : i = b
      · subst i
        simp [openEdgeAugmentedPairing,
          openEdgeAugmentedSumPairing,
          openEdgeAugmentedWord, openEdgeAugmentedSumWord,
          hia]
      · simpa [openEdgeAugmentedPairing,
          openEdgeAugmentedSumPairing,
          openEdgeAugmentedWord, openEdgeAugmentedSumWord,
          hia, hib] using hrespect i hia hib
  · fin_cases j <;>
      simp [openEdgeAugmentedPairing,
        openEdgeAugmentedSumPairing,
        openEdgeAugmentedWord, openEdgeAugmentedSumWord]

/-- Closing the marked edge preserves fullness. -/
theorem openEdgeAugmentedPairing_isFull
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a ≠ b)
    (hfull : κ.IsFull) :
    (openEdgeAugmentedPairing κ a b hκab hab).IsFull := by
  intro i
  by_cases hiold : i.val < m
  · let i₀ : Fin m := ⟨i.val, hiold⟩
    have hcast : Fin.castAdd 2 i₀ = i := Fin.ext rfl
    by_cases hia : i₀ = a
    · rw [hia] at hcast
      rw [← hcast,
        openEdgeAugmentedPairing_old_left
          κ a b hκab hab]
      intro h
      have := congrArg Fin.val h
      simp [openEdgeFirstNew] at this
      omega
    · by_cases hib : i₀ = b
      · rw [hib] at hcast
        rw [← hcast,
          openEdgeAugmentedPairing_old_right
            κ a b hκab hab]
        intro h
        have := congrArg Fin.val h
        simp [openEdgeSecondNew] at this
        omega
      · rw [← hcast,
          openEdgeAugmentedPairing_old_other
            κ a b i₀ hκab hab hia hib]
        intro h
        apply hfull i₀
        exact Fin.castAdd_inj.mp h
  · have hi_cases :
        i = openEdgeFirstNew m ∨
          i = openEdgeSecondNew m := by
      have him : m ≤ i.val := Nat.le_of_not_gt hiold
      rcases (show i.val = m ∨ i.val = m + 1 by omega) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hi_cases with hi | hi
    · subst i
      rw [openEdgeAugmentedPairing_firstNew
        κ a b hκab hab]
      intro h
      have := congrArg Fin.val h
      simp [openEdgeFirstNew] at this
      omega
    · subst i
      rw [openEdgeAugmentedPairing_secondNew
        κ a b hκab hab]
      intro h
      have := congrArg Fin.val h
      simp [openEdgeSecondNew] at this
      omega

/-- The dummy closure of a lower marked edge in a primitive full pairing
is again primitive.  Appending the copies in lower/upper order is
essential: a fully paired interval reaching the first copy must also
contain the old upper endpoint, hence must reach the final copy. -/
theorem openEdgeAugmentedPairing_isPrimitive
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a < b)
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    IsPrimitive (openEdgeAugmentedPairing κ a b hκab
      (ne_of_lt hab)) := by
  let κ' := openEdgeAugmentedPairing κ a b hκab
    (ne_of_lt hab)
  intro c d hcd hpaired
  have habne : a ≠ b := ne_of_lt hab
  by_cases hdold : d.val < m
  · have hcold : c.val < m := lt_of_le_of_lt hcd hdold
    let c₀ : Fin m := ⟨c.val, hcold⟩
    let d₀ : Fin m := ⟨d.val, hdold⟩
    have hcastc : Fin.castAdd 2 c₀ = c := Fin.ext rfl
    have hcastd : Fin.castAdd 2 d₀ = d := Fin.ext rfl
    have ha_not : a ∉ Finset.Icc c₀ d₀ := by
      intro ha
      have hacast :
          Fin.castAdd 2 a ∈ Finset.Icc c d := by
        rw [Finset.mem_Icc] at ha ⊢
        change c₀.val ≤ a.val ∧ a.val ≤ d₀.val at ha
        change c.val ≤ a.val ∧ a.val ≤ d.val
        simpa [c₀, d₀] using ha
      have hnew :=
        hpaired.apply_mem hacast
      rw [show κ' (Fin.castAdd 2 a) =
          openEdgeFirstNew m by
        exact openEdgeAugmentedPairing_old_left
          κ a b hκab habne] at hnew
      have := (Finset.mem_Icc.mp hnew).2
      change m ≤ d.val at this
      omega
    have hb_not : b ∉ Finset.Icc c₀ d₀ := by
      intro hb
      have hbcast :
          Fin.castAdd 2 b ∈ Finset.Icc c d := by
        rw [Finset.mem_Icc] at hb ⊢
        change c₀.val ≤ b.val ∧ b.val ≤ d₀.val at hb
        change c.val ≤ b.val ∧ b.val ≤ d.val
        simpa [c₀, d₀] using hb
      have hnew :=
        hpaired.apply_mem hbcast
      rw [show κ' (Fin.castAdd 2 b) =
          openEdgeSecondNew m by
        exact openEdgeAugmentedPairing_old_right
          κ a b hκab habne] at hnew
      have := (Finset.mem_Icc.mp hnew).2
      change m + 1 ≤ d.val at this
      omega
    have holdPaired :
        IsFullyPairedOn κ (Finset.Icc c₀ d₀) := by
      constructor
      · intro i _hi
        exact hfull i
      · intro i hi
        have hia : i ≠ a := by
          intro h
          exact ha_not (h ▸ hi)
        have hib : i ≠ b := by
          intro h
          exact hb_not (h ▸ hi)
        have hicast :
            Fin.castAdd 2 i ∈ Finset.Icc c d := by
          rw [Finset.mem_Icc] at hi ⊢
          change c₀.val ≤ i.val ∧ i.val ≤ d₀.val at hi
          change c.val ≤ i.val ∧ i.val ≤ d.val
          simpa [c₀, d₀] using hi
        have hκicast :=
          hpaired.apply_mem hicast
        rw [show κ' (Fin.castAdd 2 i) =
            Fin.castAdd 2 (κ i) by
          exact openEdgeAugmentedPairing_old_other
            κ a b i hκab habne hia hib] at hκicast
        rw [Finset.mem_Icc] at hκicast ⊢
        change c.val ≤ (κ i).val ∧ (κ i).val ≤ d.val at hκicast
        change c₀.val ≤ (κ i).val ∧ (κ i).val ≤ d₀.val
        simpa [c₀, d₀] using hκicast
    have hall :=
      hprimitive c₀ d₀ (by exact_mod_cast hcd) holdPaired
    exact (ha_not (by rw [hall]; simp)).elim
  · have hmd : m ≤ d.val := Nat.le_of_not_gt hdold
    have hd_cases : d.val = m ∨ d.val = m + 1 := by
      omega
    rcases hd_cases with hd | hd
    · have hdnew : d = openEdgeFirstNew m := Fin.ext hd
      have hfirst_mem :
          openEdgeFirstNew m ∈ Finset.Icc c d := by
        rw [← hdnew]
        exact Finset.mem_Icc.mpr ⟨hcd, le_rfl⟩
      have ha_mem :=
        hpaired.apply_mem hfirst_mem
      rw [show κ' (openEdgeFirstNew m) =
          Fin.castAdd 2 a by
        exact openEdgeAugmentedPairing_firstNew
          κ a b hκab habne] at ha_mem
      have hca :
          c.val ≤ a.val :=
        (Finset.mem_Icc.mp ha_mem).1
      have hb_mem :
          Fin.castAdd 2 b ∈ Finset.Icc c d := by
        apply Finset.mem_Icc.mpr
        constructor
        · exact_mod_cast hca.trans hab.le
        · change b.val ≤ d.val
          rw [hd]
          exact Nat.le_of_lt b.isLt
      have hsecond :=
        hpaired.apply_mem hb_mem
      rw [show κ' (Fin.castAdd 2 b) =
          openEdgeSecondNew m by
        exact openEdgeAugmentedPairing_old_right
          κ a b hκab habne] at hsecond
      have := (Finset.mem_Icc.mp hsecond).2
      simp [hdnew, openEdgeFirstNew,
        openEdgeSecondNew] at this
    · have hdlast : d = Fin.last (m + 1) := Fin.ext hd
      have hsecond_mem :
          openEdgeSecondNew m ∈ Finset.Icc c d := by
        rw [hdlast]
        exact Finset.mem_Icc.mpr
          ⟨Fin.le_last _, le_rfl⟩
      have hb_mem :=
        hpaired.apply_mem hsecond_mem
      rw [show κ' (openEdgeSecondNew m) =
          Fin.castAdd 2 b by
        exact openEdgeAugmentedPairing_secondNew
          κ a b hκab habne] at hb_mem
      have hcb :
          c.val ≤ b.val :=
        (Finset.mem_Icc.mp hb_mem).1
      have hfirst_mem :
          openEdgeFirstNew m ∈ Finset.Icc c d := by
        apply Finset.mem_Icc.mpr
        constructor
        · exact_mod_cast hcb.trans (by omega : b.val ≤ m)
        · rw [hdlast]
          exact Fin.le_last _
      have ha_mem :=
        hpaired.apply_mem hfirst_mem
      rw [show κ' (openEdgeFirstNew m) =
          Fin.castAdd 2 a by
        exact openEdgeAugmentedPairing_firstNew
          κ a b hκab habne] at ha_mem
      have hca :
          c.val ≤ a.val :=
        (Finset.mem_Icc.mp ha_mem).1
      have hmpos : 0 < m := Nat.zero_lt_of_lt a.isLt
      let c₀ : Fin m := ⟨c.val, lt_of_le_of_lt hca a.isLt⟩
      let d₀ : Fin m := ⟨m - 1, by omega⟩
      have hcastc : Fin.castAdd 2 c₀ = c := Fin.ext rfl
      have holdPaired :
          IsFullyPairedOn κ (Finset.Icc c₀ d₀) := by
        constructor
        · intro i _hi
          exact hfull i
        · intro i hi
          have hicast :
              Fin.castAdd 2 i ∈ Finset.Icc c d := by
            apply Finset.mem_Icc.mpr
            constructor
            · exact_mod_cast (Finset.mem_Icc.mp hi).1
            · rw [hdlast]
              exact Fin.le_last _
          have hκicast :=
            hpaired.apply_mem hicast
          by_cases hia : i = a
          · subst i
            simpa [hκab, Finset.mem_Icc] using
              (show c₀ ≤ b ∧ b ≤ d₀ by
                constructor
                · exact hca.trans hab.le
                · change b.val ≤ m - 1
                  omega)
          · by_cases hib : i = b
            · subst i
              have hκba : κ b = a := by
                rw [← hκab]
                exact κ.apply_apply a
              simpa [hκba, Finset.mem_Icc] using
                (show c₀ ≤ a ∧ a ≤ d₀ by
                  constructor
                  · exact hca
                  · change a.val ≤ m - 1
                    omega)
            · rw [show κ' (Fin.castAdd 2 i) =
                  Fin.castAdd 2 (κ i) by
                exact openEdgeAugmentedPairing_old_other
                  κ a b i hκab habne hia hib] at hκicast
              exact Finset.mem_Icc.mpr
                ⟨by exact_mod_cast
                    (Finset.mem_Icc.mp hκicast).1,
                  by
                    change (κ i).val ≤ m - 1
                    omega⟩
      have hall :=
        hprimitive c₀ d₀ (by
          change c.val ≤ m - 1
          omega) holdPaired
      let zero : Fin m := ⟨0, hmpos⟩
      have hzero_mem : zero ∈ Finset.Icc c₀ d₀ := by
        rw [hall]
        simp
      have hcval : c.val = 0 := by
        have := (Finset.mem_Icc.mp hzero_mem).1
        change c.val ≤ 0 at this
        exact Nat.eq_zero_of_le_zero this
      have hc : c = 0 := Fin.ext hcval
      rw [hc, hdlast]
      exact Icc_zero_last_eq_univ

/-- Consequently, a spatial word respected by every unmarked edge becomes
a genuine primitive word after the two dummy copies are appended. -/
theorem noProperLeafBlock_openEdgeAugmentedWord
    {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (κ : PartialPairing (Fin m))
    (a b : Fin m) (hκab : κ a = b) (hab : a < b)
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ)
    (w : Fin m → α)
    (hrespect :
      ∀ i : Fin m, i ≠ a → i ≠ b →
        w i = w (κ i)) :
    NoProperLeafBlock
      (openEdgeAugmentedWord w a b) := by
  let habne : a ≠ b := ne_of_lt hab
  exact
    noProperLeafBlock_of_primitive_full_respectsWord
      (openEdgeAugmentedPairing_isPrimitive
        κ a b hκab hab hfull hprimitive)
      (openEdgeAugmentedPairing_isFull
        κ a b hκab habne hfull)
      (openEdgeAugmentedPairing_respectsWord
        κ a b hκab habne w hrespect)

end

end Anderson4D
