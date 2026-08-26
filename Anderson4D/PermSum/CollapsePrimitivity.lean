import Anderson4D.PermSum.CollapseLeafExistence
import Anderson4D.PermSum.CollapsePredicates

/-!
# Primitivity transport through the Proposition 5.9 collapse

This file transports paper condition (5.11)(c), represented by
`NoProperLeafBlock`, through the inside-subtree word collapse.
-/

namespace Anderson4D

set_option warningAsError true
set_option autoImplicit false

variable {A B : Type*}

/-- Canonical finite word associated with a list. -/
def listWord {α : Type*} (l : List α) : Fin l.length → α :=
  List.Vector.get (⟨l, rfl⟩ : List.Vector α l.length)

@[simp]
theorem ofFn_listWord {α : Type*} (l : List α) :
    List.ofFn (listWord l) = l := by
  exact List.ofFn_get _

namespace RawCollapseData

/-- The finite word represented by the expanded list. -/
def expandedWord (d : RawCollapseData A B) :
    Fin d.expandedLength → A ⊕ B :=
  List.Vector.get (⟨d.expandWord, rfl⟩ :
    List.Vector (A ⊕ B) d.expandedLength)

@[simp]
theorem ofFn_expandedWord (d : RawCollapseData A B) :
    List.ofFn d.expandedWord = d.expandWord := by
  exact List.ofFn_get _

theorem expandedWord_eq_listWord (d : RawCollapseData A B) :
    d.expandedWord = listWord d.expandWord :=
  rfl

theorem collapsedWord_eq_listWord (d : RawCollapseData A B) :
    d.collapsedWord = listWord d.collapsed :=
  rfl

end RawCollapseData

/-! ## Pulling a collapsed alphabet subset back before collapse -/

/-- A collapsed subset pulls back by replacing the marker with the whole
inside alphabet and leaving outside letters unchanged. -/
def collapseAlphabetMap (x : A ⊕ B) : Unit ⊕ B :=
  match x with
  | .inl _ => .inl ()
  | .inr b => .inr b

def liftCollapsedAlphabet
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : Finset (Unit ⊕ B)) : Finset (A ⊕ B) :=
  Finset.univ.filter fun x => collapseAlphabetMap x ∈ S

@[simp]
theorem inl_mem_liftCollapsedAlphabet
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : Finset (Unit ⊕ B)) (a : A) :
    (Sum.inl a : A ⊕ B) ∈ liftCollapsedAlphabet S ↔
      (Sum.inl () : Unit ⊕ B) ∈ S := by
  simp [liftCollapsedAlphabet, collapseAlphabetMap]

@[simp]
theorem inr_mem_liftCollapsedAlphabet
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : Finset (Unit ⊕ B)) (b : B) :
    (Sum.inr b : A ⊕ B) ∈ liftCollapsedAlphabet S ↔
      (Sum.inr b : Unit ⊕ B) ∈ S := by
  simp [liftCollapsedAlphabet, collapseAlphabetMap]

theorem liftCollapsedAlphabet_nonempty
    [Fintype A] [Fintype B] [Nonempty A]
    [DecidableEq A] [DecidableEq B]
    {S : Finset (Unit ⊕ B)} (hS : S.Nonempty) :
    (liftCollapsedAlphabet S : Finset (A ⊕ B)).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  cases x with
  | inl u =>
      let a : A := Classical.choice inferInstance
      exact ⟨.inl a, by simpa using hx⟩
  | inr b =>
      exact ⟨.inr b, by simpa using hx⟩

theorem liftCollapsedAlphabet_ssubset_univ
    [Fintype A] [Fintype B] [Nonempty A]
    [DecidableEq A] [DecidableEq B]
    {S : Finset (Unit ⊕ B)} (hS : S ⊂ Finset.univ) :
    liftCollapsedAlphabet S ⊂ (Finset.univ : Finset (A ⊕ B)) := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
  obtain ⟨x, -, hx⟩ :=
    (Finset.ssubset_iff_of_subset hS.le).mp hS
  intro heq
  cases x with
  | inl u =>
      let a : A := Classical.choice inferInstance
      apply hx
      have ha : (Sum.inl a : A ⊕ B) ∈ liftCollapsedAlphabet S := by
        rw [heq]
        exact Finset.mem_univ _
      simpa using ha
  | inr b =>
      apply hx
      have hb : (Sum.inr b : A ⊕ B) ∈ liftCollapsedAlphabet S := by
        rw [heq]
        exact Finset.mem_univ _
      simpa using hb

/-! ## Expansion respects synchronized concatenation -/

/-- Expansion distributes over concatenation when the first collapsed
segment consumes exactly the first block segment. -/
theorem expand_append_of_markerCount
    (bs₁ bs₂ : List (List A)) (s₁ s₂ : List (Unit ⊕ B))
    (hcount : markerCount s₁ = bs₁.length) :
    expand (bs₁ ++ bs₂) (s₁ ++ s₂) =
      expand bs₁ s₁ ++ expand bs₂ s₂ := by
  induction s₁ generalizing bs₁ with
  | nil =>
      have hnil : bs₁ = [] := by
        simpa [markerCount] using
          List.length_eq_zero_iff.mp hcount.symm
      subst bs₁
      simp [expand]
  | cons x s₁ ih =>
      cases x with
      | inr b =>
          have htail : markerCount s₁ = bs₁.length := by
            simpa [markerCount] using hcount
          simp only [List.cons_append, expand, ih bs₁ htail,
            List.cons_append]
      | inl u =>
          cases bs₁ with
          | nil =>
              simp [markerCount] at hcount
          | cons blk bs₁ =>
              have htail : markerCount s₁ = bs₁.length := by
                simpa [markerCount] using hcount
              simp only [List.cons_append, expand, ih bs₁ htail,
                List.append_assoc]

/-- Every expanded letter is selected by the lifted alphabet if all source
tokens in the collapsed segment are selected. -/
theorem all_mem_expand_liftCollapsedAlphabet
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : Finset (Unit ⊕ B)) (bs : List (List A))
    (s : List (Unit ⊕ B))
    (hs : ∀ y ∈ s, y ∈ S) :
    ∀ x ∈ expand bs s,
      x ∈ liftCollapsedAlphabet (A := A) S := by
  induction s generalizing bs with
  | nil => simp [expand]
  | cons y s ih =>
      cases y with
      | inr b =>
          intro x hx
          simp only [expand, List.mem_cons] at hx
          rcases hx with rfl | hx
          · simpa using hs (.inr b) (List.mem_cons_self)
          · exact ih bs (fun y hy => hs y (List.mem_cons_of_mem _ hy)) x hx
      | inl u =>
          cases bs with
          | nil =>
              exact ih [] (fun y hy => hs y (List.mem_cons_of_mem _ hy))
          | cons blk bs =>
              intro x hx
              simp only [expand, List.mem_append, List.mem_map] at hx
              rcases hx with ⟨a, ha, rfl⟩ | hx
              · simpa using hs (.inl u) (List.mem_cons_self)
              · exact ih bs (fun y hy => hs y (List.mem_cons_of_mem _ hy)) x hx

/-- Every expanded letter is unselected by the lifted alphabet if all source
tokens in the collapsed segment are unselected. -/
theorem all_not_mem_expand_liftCollapsedAlphabet
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : Finset (Unit ⊕ B)) (bs : List (List A))
    (s : List (Unit ⊕ B))
    (hs : ∀ y ∈ s, y ∉ S) :
    ∀ x ∈ expand bs s,
      x ∉ liftCollapsedAlphabet (A := A) S := by
  induction s generalizing bs with
  | nil => simp [expand]
  | cons y s ih =>
      cases y with
      | inr b =>
          intro x hx
          simp only [expand, List.mem_cons] at hx
          rcases hx with rfl | hx
          · simpa using hs (.inr b) (List.mem_cons_self)
          · exact ih bs (fun y hy => hs y (List.mem_cons_of_mem _ hy)) x hx
      | inl u =>
          cases bs with
          | nil =>
              exact ih [] (fun y hy => hs y (List.mem_cons_of_mem _ hy))
          | cons blk bs =>
              intro x hx
              simp only [expand, List.mem_append, List.mem_map] at hx
              rcases hx with ⟨a, ha, rfl⟩ | hx
              · simpa using hs (.inl u) (List.mem_cons_self)
              · exact ih bs (fun y hy => hs y (List.mem_cons_of_mem _ hy)) x hx

/-- Under the raw-collapse nonempty-block invariant, a nonempty collapsed
segment has a nonempty expansion. -/
theorem expand_ne_nil_of_ne_nil
    (bs : List (List A)) (s : List (Unit ⊕ B))
    (hbs : ∀ blk ∈ bs, blk ≠ [])
    (hcount : markerCount s = bs.length) (hs : s ≠ []) :
    expand bs s ≠ [] := by
  cases s with
  | nil => exact (hs rfl).elim
  | cons y s =>
      cases y with
      | inr b =>
          simp [expand]
      | inl u =>
          cases bs with
          | nil =>
              simp [markerCount] at hcount
          | cons blk bs =>
              have hblk : blk ≠ [] :=
                hbs blk (List.mem_cons_self)
              have hmap : blk.map (Sum.inl : A → A ⊕ B) ≠ [] := by
                simpa using hblk
              intro hnil
              exact hmap (List.append_eq_nil_iff.mp hnil).1

/-- If every position of the canonical finite word is selected, every list
entry is selected. -/
theorem all_mem_of_letterPositions_eq_univ
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (l : List α)
    (hpositions :
      letterPositions (listWord l) T =
        (Finset.univ : Finset (Fin l.length))) :
    ∀ x ∈ l, x ∈ T := by
  rw [List.forall_mem_iff_getElem]
  intro i hi
  let j : Fin l.length := ⟨i, hi⟩
  have hj : j ∈ letterPositions (listWord l) T := by
    rw [hpositions]
    exact Finset.mem_univ _
  rw [mem_letterPositions] at hj
  change l.get j ∈ T at hj
  simpa [j] using hj

/-! ## A single middle block is an index interval -/

/-- In an outside/inside/outside list, membership in the inside alphabet is
exactly membership in the middle numerical range.  Keeping the ambient list
as a variable lets dependent elimination transport its `Fin` index cleanly. -/
theorem get_mem_insideAlphabet_iff_middle_range
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (l : List (A ⊕ B)) (pre : List B) (blk : List A) (post : List B)
    (hl :
      l = pre.map Sum.inr ++ blk.map Sum.inl ++ post.map Sum.inr)
    (i : Fin l.length) :
    l.get i ∈ (insideAlphabet : Finset (A ⊕ B)) ↔
      pre.length ≤ i.1 ∧ i.1 < pre.length + blk.length := by
  subst l
  by_cases hpre : i.1 < pre.length
  · rw [List.get_eq_getElem,
      List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simpa)]
    simp [insideAlphabet]
    omega
  · by_cases hmiddle : i.1 < pre.length + blk.length
    · rw [List.get_eq_getElem,
        List.getElem_append_left (by simp; omega),
        List.getElem_append_right (by simp; omega)]
      simp [insideAlphabet]
      omega
    · rw [List.get_eq_getElem,
        List.getElem_append_right (by simp; omega)]
      simp [insideAlphabet]
      omega

/-- Generic form of the middle-range lemma for an arbitrary finite alphabet
subset and lists already known to be respectively outside/inside/outside. -/
theorem get_mem_iff_middle_range_of_forall
    {α : Type*} [DecidableEq α] (T : Finset α)
    (l pre mid post : List α) (hl : l = pre ++ mid ++ post)
    (hpre : ∀ x ∈ pre, x ∉ T) (hmid : ∀ x ∈ mid, x ∈ T)
    (hpost : ∀ x ∈ post, x ∉ T) (i : Fin l.length) :
    l.get i ∈ T ↔
      pre.length ≤ i.1 ∧ i.1 < pre.length + mid.length := by
  subst l
  by_cases hp : i.1 < pre.length
  · rw [List.get_eq_getElem,
      List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simpa)]
    constructor
    · intro hi
      exact (hpre (pre[i.1]'hp) (List.getElem_mem hp) hi).elim
    · intro hi
      omega
  · by_cases hm : i.1 < pre.length + mid.length
    · have hmi : i.1 - pre.length < mid.length := by omega
      rw [List.get_eq_getElem,
        List.getElem_append_left (by simp; omega),
        List.getElem_append_right (Nat.le_of_not_gt hp)]
      constructor
      · intro _
        exact ⟨by omega, hm⟩
      · intro _
        exact hmid (mid[i.1 - pre.length]'hmi) (List.getElem_mem hmi)
    · have hposti :
          i.1 - (pre ++ mid).length < post.length := by
        simp only [List.length_append]
        have hi := i.2
        simp only [List.length_append] at hi
        omega
      rw [List.get_eq_getElem,
        List.getElem_append_right (by simp; omega)]
      constructor
      · intro hi
        exact
          (hpost (post[i.1 - (pre ++ mid).length]'hposti)
            (List.getElem_mem hposti) hi).elim
      · intro hi
        omega

/-- An outside/inside/outside list decomposition gives the corresponding
closed interval of selected finite-word positions. -/
theorem letterPositions_eq_Icc_of_decompose
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (l pre mid post : List α)
    (hl : l = pre ++ mid ++ post)
    (hpre : ∀ x ∈ pre, x ∉ T) (hmid : ∀ x ∈ mid, x ∈ T)
    (hpost : ∀ x ∈ post, x ∉ T) (hmidNonempty : mid ≠ []) :
    let w : Fin l.length → α :=
      List.Vector.get (⟨l, rfl⟩ : List.Vector α l.length)
    ∃ a b : Fin l.length,
      a ≤ b ∧ letterPositions w T = Finset.Icc a b := by
  dsimp only
  have hmidPos : 0 < mid.length := List.length_pos_iff.mpr hmidNonempty
  have hlength := congrArg List.length hl
  simp only [List.length_append] at hlength
  let a : Fin l.length := ⟨pre.length, by omega⟩
  let b : Fin l.length := ⟨pre.length + mid.length - 1, by omega⟩
  refine ⟨a, b, ?_, ?_⟩
  · apply Fin.mk_le_mk.mpr
    omega
  · ext i
    rw [mem_letterPositions]
    change l.get i ∈ T ↔ i ∈ Finset.Icc a b
    rw [get_mem_iff_middle_range_of_forall
      T l pre mid post hl hpre hmid hpost]
    simp only [Finset.mem_Icc]
    change
      (pre.length ≤ i.1 ∧ i.1 < pre.length + mid.length) ↔
        pre.length ≤ i.1 ∧ i.1 ≤ pre.length + mid.length - 1
    omega

/-- Conversely, a closed interval of selected finite-word positions yields
an outside/inside/outside list decomposition. -/
theorem decompose_of_letterPositions_eq_Icc
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (l : List α) (a b : Fin l.length)
    (hab : a ≤ b)
    (hpositions : letterPositions (listWord l) T = Finset.Icc a b) :
    ∃ pre mid post : List α,
      l = pre ++ mid ++ post ∧ mid ≠ [] ∧
        (∀ x ∈ pre, x ∉ T) ∧
        (∀ x ∈ mid, x ∈ T) ∧
        ∀ x ∈ post, x ∉ T := by
  let pre := l.take a.1
  let middleLength := b.1 - a.1 + 1
  let mid := (l.drop a.1).take middleLength
  let post := l.drop (b.1 + 1)
  have habVal : a.1 ≤ b.1 := hab
  have hmiddleLength : middleLength = b.1 + 1 - a.1 := by
    dsimp [middleLength]
    omega
  have hdecomp : l = pre ++ mid ++ post := by
    have hsum : a.1 + middleLength = b.1 + 1 := by
      dsimp [middleLength]
      omega
    calc
      l = l.take a.1 ++ l.drop a.1 := (List.take_append_drop _ _).symm
      _ = pre ++
          ((l.drop a.1).take middleLength ++
            (l.drop a.1).drop middleLength) := by
            dsimp only [pre]
            apply congrArg (l.take a.1 ++ ·)
            exact (List.take_append_drop middleLength (l.drop a.1)).symm
      _ = pre ++ mid ++ post := by
            simp only [mid, post, List.drop_drop, List.append_assoc]
            rw [hsum]
  have hmidLength : mid.length = middleLength := by
    simp only [mid, List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    dsimp [middleLength]
    omega
  have hmidNonempty : mid ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hmidLength]
    dsimp [middleLength]
    omega
  have hpre : ∀ x ∈ pre, x ∉ T := by
    rw [List.forall_mem_iff_getElem]
    intro i hi
    have hiA : i < a.1 := by
      have hpreLength : pre.length ≤ a.1 := by simp [pre]
      omega
    let j : Fin l.length := ⟨i, lt_trans hiA a.2⟩
    have hjNot : listWord l j ∉ T := by
      intro hj
      have hjpos : j ∈ letterPositions (listWord l) T :=
        mem_letterPositions.mpr hj
      rw [hpositions] at hjpos
      simp only [Finset.mem_Icc] at hjpos
      have hjval : j.1 = i := rfl
      omega
    change l.get j ∉ T at hjNot
    simpa [pre, listWord, j] using hjNot
  have hmid : ∀ x ∈ mid, x ∈ T := by
    rw [List.forall_mem_iff_getElem]
    intro i hi
    have hiBound : i < middleLength := by
      rw [← hmidLength]
      exact hi
    have hai : a.1 + i ≤ b.1 := by
      dsimp [middleLength] at hiBound
      omega
    let j : Fin l.length :=
      ⟨a.1 + i, lt_of_le_of_lt hai b.2⟩
    have hjpos : j ∈ Finset.Icc a b := by
      simp only [Finset.mem_Icc]
      constructor
      · apply Fin.mk_le_mk.mpr
        omega
      · apply Fin.mk_le_mk.mpr
        exact hai
    have hjmem : listWord l j ∈ T := by
      rw [← mem_letterPositions, hpositions]
      exact hjpos
    change l.get j ∈ T at hjmem
    simpa [mid, j] using hjmem
  have hpost : ∀ x ∈ post, x ∉ T := by
    rw [List.forall_mem_iff_getElem]
    intro i hi
    let j : Fin l.length := ⟨b.1 + 1 + i, by
      have hpostLength : post.length = l.length - (b.1 + 1) := by
        simp [post]
      omega⟩
    have hjNot : listWord l j ∉ T := by
      intro hj
      have hjpos : j ∈ letterPositions (listWord l) T :=
        mem_letterPositions.mpr hj
      rw [hpositions] at hjpos
      simp only [Finset.mem_Icc] at hjpos
      have hjval : j.1 = b.1 + 1 + i := rfl
      omega
    change l.get j ∉ T at hjNot
    change l.get ⟨b.1 + 1 + i, j.2⟩ ∉ T at hjNot
    simpa [post, Nat.add_assoc] using hjNot
  exact ⟨pre, mid, post, hdecomp, hmidNonempty, hpre, hmid, hpost⟩

/-- The middle numerical range is the closed `Fin` interval from its first
to its last position. -/
theorem middle_range_eq_Icc
    (preLength blockLength totalLength : ℕ)
    (hblock : 0 < blockLength)
    (hfit : preLength + blockLength ≤ totalLength) :
    (Finset.univ.filter fun i : Fin totalLength =>
      preLength ≤ i.1 ∧ i.1 < preLength + blockLength) =
      Finset.Icc
        ⟨preLength, by omega⟩
        ⟨preLength + blockLength - 1, by omega⟩ := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_Icc]
  change
    (preLength ≤ i.1 ∧ i.1 < preLength + blockLength) ↔
      preLength ≤ i.1 ∧ i.1 ≤ preLength + blockLength - 1
  omega

namespace RawCollapseData

/-- With one inside block, the positions occupied by inside letters form one
closed interval. -/
theorem letterPositions_insideAlphabet_eq_Icc_of_blocks_length_one
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B) (hblocks : d.blocks.length = 1) :
    ∃ a b : Fin d.expandedLength,
      a ≤ b ∧
        letterPositions d.expandedWord insideAlphabet = Finset.Icc a b := by
  obtain ⟨blk, pre, post, hblk, -, hdecomp⟩ :=
    expand_single_block_decompose d hblocks
  have hblkPos : 0 < blk.length := List.length_pos_iff.mpr hblk
  have hlength := congrArg List.length hdecomp
  simp only [List.length_append, List.length_map] at hlength
  have hfit : pre.length + blk.length ≤ d.expandedLength := by
    change pre.length + blk.length ≤ d.expandWord.length
    omega
  let a : Fin d.expandedLength := ⟨pre.length, by omega⟩
  let b : Fin d.expandedLength :=
    ⟨pre.length + blk.length - 1, by omega⟩
  refine ⟨a, b, ?_, ?_⟩
  · apply Fin.mk_le_mk.mpr
    omega
  · ext i
    rw [mem_letterPositions]
    change d.expandWord.get i ∈ insideAlphabet ↔ i ∈ Finset.Icc a b
    rw [get_mem_insideAlphabet_iff_middle_range
      d.expandWord pre blk post hdecomp]
    simp only [Finset.mem_Icc]
    change
      (pre.length ≤ i.1 ∧ i.1 < pre.length + blk.length) ↔
        pre.length ≤ i.1 ∧
          i.1 ≤ pre.length + blk.length - 1
    omega

end RawCollapseData

/-! ## Excluding the one-block and zero-block degenerations -/

private theorem mem_expand_nil_is_inr (s : List (Unit ⊕ B))
    {x : A ⊕ B} (hx : x ∈ expand ([] : List (List A)) s) :
    ∃ b : B, x = .inr b := by
  induction s with
  | nil => simp [expand] at hx
  | cons y s ih =>
      cases y with
      | inl u =>
          exact ih (by simpa [expand] using hx)
      | inr b =>
          simp only [expand, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact ⟨b, rfl⟩
          · exact ih hx

namespace RawCollapseData

/-- An actually occurring inside letter forces at least one collapse block. -/
theorem blocks_nonempty_of_inside_occurs
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B)
    (hinside : ∃ i, d.expandedWord i ∈
      (insideAlphabet : Finset (A ⊕ B))) :
    d.blocks ≠ [] := by
  intro hzero
  obtain ⟨i, hi⟩ := hinside
  have himem : d.expandedWord i ∈ d.expandWord := by
    change d.expandWord.get i ∈ d.expandWord
    exact List.get_mem _ _
  change d.expandWord.get i ∈ expand d.blocks d.collapsed at himem
  rw [hzero] at himem
  obtain ⟨b, hb⟩ := mem_expand_nil_is_inr d.collapsed himem
  change d.expandWord.get i ∈ insideAlphabet at hi
  rw [hb] at hi
  exact inr_not_mem_insideAlphabet b hi

/-- **The primitivity source of `s ≥ 1`.**  If both sides of the alphabet
actually occur, condition (5.11)(c) rules out a single maximal inside block.
Consequently there are at least two blocks and hence at least one proper
composition cut. -/
theorem two_le_blocks_of_noProperLeafBlock
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B)
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hinside : ∃ i, d.expandedWord i ∈
      (insideAlphabet : Finset (A ⊕ B)))
    (houtside : ∃ i, d.expandedWord i ∉
      (insideAlphabet : Finset (A ⊕ B))) :
    2 ≤ d.blocks.length := by
  have hnonempty : d.blocks ≠ [] :=
    d.blocks_nonempty_of_inside_occurs hinside
  have hlengthPos : 0 < d.blocks.length :=
    List.length_pos_iff.mpr hnonempty
  by_contra hnot
  have hone : d.blocks.length = 1 := by omega
  obtain ⟨a, b, hab, hpositions⟩ :=
    d.letterPositions_insideAlphabet_eq_Icc_of_blocks_length_one hone
  have hfull :
      Finset.Icc a b = (Finset.univ : Finset (Fin d.expandedLength)) :=
    hprimitive insideAlphabet insideAlphabet_nonempty
      insideAlphabet_ssubset_univ a b hab hpositions
  obtain ⟨i, hi⟩ := houtside
  apply hi
  rw [← mem_letterPositions, hpositions, hfull]
  exact Finset.mem_univ i

/-- Valid positive multiplicities discharge the two occurrence hypotheses in
`two_le_blocks_of_noProperLeafBlock`. -/
theorem two_le_blocks_of_noProperLeafBlock_of_mem_validWords_of_pos
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (d : RawCollapseData A B)
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hvalid : d.expandedWord ∈ validWords mult)
    (hpos : ∀ x, 0 < mult x) :
    2 ≤ d.blocks.length := by
  let a : A := Classical.choice inferInstance
  let b : B := Classical.choice inferInstance
  obtain ⟨ia, hia⟩ :=
    exists_eq_of_mem_validWords_of_pos mult d.expandedWord
      hvalid (.inl a) (hpos (.inl a))
  obtain ⟨ib, hib⟩ :=
    exists_eq_of_mem_validWords_of_pos mult d.expandedWord
      hvalid (.inr b) (hpos (.inr b))
  apply d.two_le_blocks_of_noProperLeafBlock hprimitive
  · exact ⟨ia, by rw [hia]; exact inl_mem_insideAlphabet a⟩
  · exact ⟨ib, by rw [hib]; exact inr_not_mem_insideAlphabet b⟩

/-- Positive valid multiplicities give the paper's nondegenerate cut ledger
`1 ≤ s = |O|`. -/
theorem one_le_card_adjacentCutIndices_of_mem_validWords_of_pos
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B]
    (mult : A ⊕ B → ℕ) (d : RawCollapseData A B)
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hvalid : d.expandedWord ∈ validWords mult)
    (hpos : ∀ x, 0 < mult x) :
    1 ≤ d.adjacentCutIndices.card :=
  d.one_le_card_adjacentCutIndices
    (d.two_le_blocks_of_noProperLeafBlock_of_mem_validWords_of_pos
      mult hprimitive hvalid hpos)

/-- Primitivity descends to the word on the contracted alphabet.  A collapsed
alphabet subset is pulled back by replacing the marker with the whole inside
alphabet; a collapsed interval expands to an interval before collapse. -/
theorem collapsedWord_noProperLeafBlock
    [Fintype A] [Fintype B] [Nonempty A]
    [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B)
    (hprimitive : NoProperLeafBlock d.expandedWord) :
    NoProperLeafBlock d.collapsedWord := by
  intro S hSNonempty hSProper a b hab hpositions
  have hpositionsList :
      letterPositions (listWord d.collapsed) S = Finset.Icc a b := by
    simpa only [← d.collapsedWord_eq_listWord] using hpositions
  obtain ⟨pre, mid, post, hsource, hmidNonempty,
      hpre, hmid, hpost⟩ :=
    decompose_of_letterPositions_eq_Icc
      S d.collapsed a b hab hpositionsList
  let kp := markerCount pre
  let km := markerCount mid
  let bsPre := d.blocks.take kp
  let bsRest := d.blocks.drop kp
  let bsMid := bsRest.take km
  let bsPost := bsRest.drop km
  have htotal :
      kp + km + markerCount post = d.blocks.length := by
    calc
      kp + km + markerCount post =
          markerCount (pre ++ mid ++ post) := by
            simp [kp, km, markerCount, Nat.add_assoc]
      _ = markerCount d.collapsed := by rw [hsource]
      _ = d.blocks.length := d.2.2.1
  have hkp : kp ≤ d.blocks.length := by omega
  have hkm : km ≤ bsRest.length := by
    dsimp only [bsRest]
    rw [List.length_drop]
    omega
  have hcountPre : markerCount pre = bsPre.length := by
    dsimp only [bsPre, kp]
    rw [List.length_take, Nat.min_eq_left hkp]
  have hcountMid : markerCount mid = bsMid.length := by
    dsimp only [bsMid, km]
    rw [List.length_take, Nat.min_eq_left hkm]
  have hblocks :
      d.blocks = bsPre ++ (bsMid ++ bsPost) := by
    calc
      d.blocks =
          d.blocks.take kp ++ d.blocks.drop kp :=
        (List.take_append_drop kp d.blocks).symm
      _ = bsPre ++
          (bsRest.take km ++ bsRest.drop km) := by
            dsimp only [bsPre, bsRest]
            apply congrArg (d.blocks.take kp ++ ·)
            exact
              (List.take_append_drop km (d.blocks.drop kp)).symm
      _ = bsPre ++ (bsMid ++ bsPost) := by
            rfl
  have hsourceRight :
      d.collapsed = pre ++ (mid ++ post) := by
    simpa only [List.append_assoc] using hsource
  let expPre := expand bsPre pre
  let expMid := expand bsMid mid
  let expPost := expand bsPost post
  have hexpandRight :
      d.expandWord = expPre ++ (expMid ++ expPost) := by
    change expand d.blocks d.collapsed =
      expand bsPre pre ++
        (expand bsMid mid ++ expand bsPost post)
    rw [hblocks, hsourceRight,
      expand_append_of_markerCount bsPre (bsMid ++ bsPost)
        pre (mid ++ post) hcountPre,
      expand_append_of_markerCount bsMid bsPost mid post hcountMid]
  have hexpand :
      d.expandWord = expPre ++ expMid ++ expPost := by
    simpa only [List.append_assoc] using hexpandRight
  have hbsPre : ∀ blk ∈ bsPre, blk ≠ [] := by
    intro blk hblk
    apply d.2.1 blk
    exact List.mem_of_mem_take hblk
  have hbsMid : ∀ blk ∈ bsMid, blk ≠ [] := by
    intro blk hblk
    apply d.2.1 blk
    exact List.mem_of_mem_drop (List.mem_of_mem_take hblk)
  have hbsPost : ∀ blk ∈ bsPost, blk ≠ [] := by
    intro blk hblk
    apply d.2.1 blk
    exact List.mem_of_mem_drop (List.mem_of_mem_drop hblk)
  let liftS : Finset (A ⊕ B) := liftCollapsedAlphabet S
  have hpreExpanded : ∀ x ∈ expPre, x ∉ liftS := by
    exact all_not_mem_expand_liftCollapsedAlphabet
      S bsPre pre hpre
  have hmidExpanded : ∀ x ∈ expMid, x ∈ liftS := by
    exact all_mem_expand_liftCollapsedAlphabet S bsMid mid hmid
  have hpostExpanded : ∀ x ∈ expPost, x ∉ liftS := by
    exact all_not_mem_expand_liftCollapsedAlphabet
      S bsPost post hpost
  have hExpMidNonempty : expMid ≠ [] :=
    expand_ne_nil_of_ne_nil bsMid mid hbsMid hcountMid hmidNonempty
  obtain ⟨ea, eb, heab, hpositionsExpanded⟩ :=
    letterPositions_eq_Icc_of_decompose
      liftS d.expandWord expPre expMid expPost hexpand
        hpreExpanded hmidExpanded hpostExpanded hExpMidNonempty
  have hpositionsExpanded' :
      letterPositions d.expandedWord liftS = Finset.Icc ea eb := by
    change
      letterPositions (listWord d.expandWord) liftS =
        Finset.Icc ea eb
    exact hpositionsExpanded
  have hfullExpanded :
      Finset.Icc ea eb =
        (Finset.univ : Finset (Fin d.expandedLength)) :=
    hprimitive liftS
      (liftCollapsedAlphabet_nonempty hSNonempty)
      (liftCollapsedAlphabet_ssubset_univ hSProper)
      ea eb heab hpositionsExpanded'
  have hallPositions :
      letterPositions (listWord d.expandWord) liftS =
        (Finset.univ : Finset (Fin d.expandWord.length)) := by
    calc
      letterPositions (listWord d.expandWord) liftS =
          Finset.Icc ea eb := hpositionsExpanded
      _ = Finset.univ := hfullExpanded
  have hallExpanded : ∀ x ∈ d.expandWord, x ∈ liftS :=
    all_mem_of_letterPositions_eq_univ liftS d.expandWord hallPositions
  have hExpPreNil : expPre = [] := by
    by_contra hne
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil expPre hne
    have hxWhole : x ∈ d.expandWord := by
      rw [hexpandRight]
      exact List.mem_append_left _ hx
    exact hpreExpanded x hx (hallExpanded x hxWhole)
  have hExpPostNil : expPost = [] := by
    by_contra hne
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil expPost hne
    have hxWhole : x ∈ d.expandWord := by
      rw [hexpandRight]
      exact List.mem_append_right _ (List.mem_append_right _ hx)
    exact hpostExpanded x hx (hallExpanded x hxWhole)
  have hpreNil : pre = [] := by
    by_contra hne
    exact
      (expand_ne_nil_of_ne_nil bsPre pre hbsPre hcountPre hne)
        hExpPreNil
  have hpostNil : post = [] := by
    by_contra hne
    exact
      (expand_ne_nil_of_ne_nil bsPost post hbsPost
        (by
          have hcountPost :
              markerCount post = bsPost.length := by
            dsimp only [bsPost, bsRest]
            rw [List.length_drop, List.length_drop]
            omega
          exact hcountPost)
        hne) hExpPostNil
  have hallCollapsed : ∀ x ∈ d.collapsed, x ∈ S := by
    intro x hx
    rw [hsource, hpreNil, hpostNil] at hx
    simp only [List.nil_append, List.append_nil] at hx
    exact hmid x hx
  have hpositionsFull :
      letterPositions d.collapsedWord S =
        (Finset.univ : Finset (Fin d.collapsed.length)) := by
    ext i
    rw [mem_letterPositions]
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      exact hallCollapsed _ (by
        change d.collapsed.get i ∈ d.collapsed
        exact List.get_mem _ _)
  calc
    Finset.Icc a b = letterPositions d.collapsedWord S :=
      hpositions.symm
    _ = Finset.univ := hpositionsFull

/-- Equivalent cut-cardinality form used in the paper's notation `s = |O|`. -/
theorem one_le_card_adjacentCutIndices_of_noProperLeafBlock
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [DecidableEq A] [DecidableEq B]
    (d : RawCollapseData A B)
    (hprimitive : NoProperLeafBlock d.expandedWord)
    (hinside : ∃ i, d.expandedWord i ∈
      (insideAlphabet : Finset (A ⊕ B)))
    (houtside : ∃ i, d.expandedWord i ∉
      (insideAlphabet : Finset (A ⊕ B))) :
    1 ≤ d.adjacentCutIndices.card :=
  d.one_le_card_adjacentCutIndices
    (d.two_le_blocks_of_noProperLeafBlock hprimitive hinside houtside)

end RawCollapseData

end Anderson4D
