import Anderson4D.PermSum.CollapseWords

/-!
# Typed coordinates for the Proposition 5.9 collapse

This module records the length and multiplicity ledgers carried by the
finite-word collapse, and exposes the change of variables

`raw collapse data ≃ (inside list, positive composition, collapsed list)`.

The last item is an actual `Equiv`: the block list is recovered by splitting
the inside list at the composition boundaries.  In particular, none of the
coordinate projections is used as though it were injective.
-/

namespace Anderson4D

variable {A B : Type*}

namespace RawCollapseData

private theorem length_expand_add_markerCount (bs : List (List A))
    (s : List (Unit ⊕ B)) (hcount : markerCount s = bs.length) :
    (expand bs s).length + markerCount s =
      (bs.map List.length).sum + s.length := by
  induction s generalizing bs with
  | nil =>
      have hbs : bs = [] := by
        simpa [markerCount] using hcount.symm
      subst bs
      simp [expand, markerCount]
  | cons x s ih =>
      cases x with
      | inr b =>
          have htail : markerCount s = bs.length := by
            simpa [markerCount] using hcount
          have hih := ih bs htail
          simp only [markerCount] at hih
          simp [expand, markerCount]
          omega
      | inl u =>
          cases bs with
          | nil =>
              simp [markerCount] at hcount
          | cons blk bs =>
              have htail : markerCount s = bs.length := by
                simpa [markerCount] using hcount
              have hih := ih bs htail
              simp only [markerCount] at hih
              simp [expand, markerCount]
              omega

/-- Exact additive length ledger before solving for the collapsed length. -/
theorem expandedLength_add_blocks_length (d : RawCollapseData A B) :
    d.expandedLength + d.blocks.length =
      d.insideLength + d.collapsed.length := by
  have h := length_expand_add_markerCount d.blocks d.collapsed d.2.2.1
  calc
    d.expandedLength + d.blocks.length =
        d.expandedLength + markerCount d.collapsed :=
      congrArg (fun k => d.expandedLength + k) d.2.2.1.symm
    _ = d.insideLength + d.collapsed.length := by
      simpa [expandedLength, expandWord, insideLength, insideList] using h

/-- Every inside letter survives expansion. -/
theorem insideLength_le_expandedLength (d : RawCollapseData A B) :
    d.insideLength ≤ d.expandedLength := by
  have hmarker : d.blocks.length ≤ d.collapsed.length := by
    calc
      d.blocks.length = markerCount d.collapsed := d.2.2.1.symm
      _ ≤ d.collapsed.length := List.countP_le_length
  have hledger := d.expandedLength_add_blocks_length
  omega

/-- The collapsed word has the paper's length
`expanded length - inside length + number of blocks`. -/
theorem collapsed_length (d : RawCollapseData A B) :
    d.collapsed.length =
      d.expandedLength - d.insideLength + d.blocks.length := by
  have hledger := d.expandedLength_add_blocks_length
  have hle := d.insideLength_le_expandedLength
  omega

/-- Fixed-original-length form of `collapsed_length`. -/
theorem collapsed_length_fixed {n : ℕ} (d : FixedRawCollapseData A B n) :
    d.1.collapsed.length = n - d.1.insideLength + d.1.blocks.length := by
  rw [d.1.collapsed_length, d.2]

end RawCollapseData

/-! ## Multiplicity transport to the two coordinate words -/

/-- Multiplicity of an inside letter in `π₁`. -/
def insideMultiplicity (mult : A ⊕ B → ℕ) : A → ℕ :=
  fun a => mult (.inl a)

/-- Multiplicity in `π₂`: the new marker occurs once for each inside block,
while every outside multiplicity is unchanged. -/
def collapsedMultiplicity (mult : A ⊕ B → ℕ)
    (d : RawCollapseData A B) : Unit ⊕ B → ℕ
  | .inl _ => d.blocks.length
  | .inr b => mult (.inr b)

private theorem coordinate_count_ofFn {α : Type*}
    [BEq α] [LawfulBEq α] [DecidableEq α] :
    ∀ {n : ℕ} (w : Fin n → α) (a : α),
      (List.ofFn w).count a =
        (Finset.univ.filter fun i => w i = a).card
  | 0, w, a => by simp
  | n + 1, w, a => by
      rw [List.ofFn_succ, List.count_cons,
        coordinate_count_ofFn (fun i => w i.succ) a,
        Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
      simp only [beq_iff_eq]
      omega

namespace RawCollapseData

/-- `π₁` has exactly the inside multiplicities prescribed by the original
word. -/
theorem insideWord_mem_validWords [Fintype A] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {d : RawCollapseData A B}
    (h : CollapseMultiplicitySpec mult d) :
    d.insideWord ∈ validWords (insideMultiplicity mult) := by
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun a => ?_⟩
  calc
    (Finset.univ.filter fun i => d.insideWord i = a).card =
        (List.ofFn d.insideWord).count a :=
      (coordinate_count_ofFn d.insideWord a).symm
    _ = d.insideList.count a := by
      rw [show List.ofFn d.insideWord = d.insideList by
        exact List.ofFn_get d.insideList]
    _ = (d.blocks.map fun blk => blk.count a).sum := by
      simpa [insideList] using
        (List.count_flatten (a := a) (l := d.blocks))
    _ = insideMultiplicity mult a := h.1 a

/-- `π₂` has one marker per inside block and preserves every outside
multiplicity. -/
theorem collapsedWord_mem_validWords [Fintype B] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {d : RawCollapseData A B}
    (h : CollapseMultiplicitySpec mult d) :
    d.collapsedWord ∈ validWords (collapsedMultiplicity mult d) := by
  rw [validWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro x
  cases x with
  | inl u =>
      cases u
      calc
        (Finset.univ.filter fun i => d.collapsedWord i = .inl ()).card =
            (List.ofFn d.collapsedWord).count (.inl ()) :=
          (count_inl_ofFn_eq_fiberCard d.collapsedWord ()).symm
        _ = d.collapsed.count (.inl ()) := by
          rw [show List.ofFn d.collapsedWord = d.collapsed by
            exact List.ofFn_get d.collapsed]
        _ = collapsedMultiplicity mult d (.inl ()) := by
          rw [← markerCount_eq_count d.collapsed]
          exact d.2.2.1
  | inr b =>
      calc
        (Finset.univ.filter fun i => d.collapsedWord i = .inr b).card =
            (List.ofFn d.collapsedWord).count (.inr b) :=
          (count_inr_ofFn_eq_fiberCard d.collapsedWord b).symm
        _ = d.collapsed.count (.inr b) := by
          rw [show List.ofFn d.collapsedWord = d.collapsed by
            exact List.ofFn_get d.collapsed]
        _ = collapsedMultiplicity mult d (.inr b) := h.2 b

private theorem sum_multiplicity_eq_length_of_mem_validWords
    {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} {mult : α → ℕ} {w : Fin n → α}
    (hw : w ∈ validWords mult) :
    ∑ a : α, mult a = n := by
  rw [validWords, Finset.mem_filter] at hw
  calc
    ∑ a : α, mult a =
        ∑ a : α, (Finset.univ.filter fun i => w i = a).card := by
      exact Finset.sum_congr rfl fun a _ => (hw.2 a).symm
    _ = n := by
      simpa using
        (Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset (Fin n)) (Finset.univ : Finset α) w)

/-- Total inside multiplicity is the length of `π₁`. -/
theorem sum_insideMultiplicity_eq_insideLength
    [Fintype A] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {d : RawCollapseData A B}
    (h : CollapseMultiplicitySpec mult d) :
    ∑ a : A, insideMultiplicity mult a = d.insideLength := by
  exact sum_multiplicity_eq_length_of_mem_validWords
    (d.insideWord_mem_validWords h)

/-- Total collapsed multiplicity is the length of `π₂`. -/
theorem sum_collapsedMultiplicity_eq_collapsed_length
    [Fintype B] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {d : RawCollapseData A B}
    (h : CollapseMultiplicitySpec mult d) :
    ∑ x : Unit ⊕ B, collapsedMultiplicity mult d x =
      d.collapsed.length := by
  exact sum_multiplicity_eq_length_of_mem_validWords
    (d.collapsedWord_mem_validWords h)

/-- The total `π₂` multiplicity in original-length coordinates. -/
theorem sum_collapsedMultiplicity_eq_length_ledger
    [Fintype B] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {d : RawCollapseData A B}
    (h : CollapseMultiplicitySpec mult d) :
    ∑ x : Unit ⊕ B, collapsedMultiplicity mult d x =
      d.expandedLength - d.insideLength + d.blocks.length := by
  rw [d.sum_collapsedMultiplicity_eq_collapsed_length h, d.collapsed_length]

/-- Fixed-original-length form of the total `π₂` multiplicity ledger. -/
theorem sum_collapsedMultiplicity_eq_fixed_length_ledger
    [Fintype B] [DecidableEq A] [DecidableEq B]
    {mult : A ⊕ B → ℕ} {n : ℕ} {d : FixedRawCollapseData A B n}
    (h : CollapseMultiplicitySpec mult d.1) :
    ∑ x : Unit ⊕ B, collapsedMultiplicity mult d.1 x =
      n - d.1.insideLength + d.1.blocks.length := by
  rw [d.1.sum_collapsedMultiplicity_eq_collapsed_length h,
    RawCollapseData.collapsed_length_fixed d]

end RawCollapseData

/-! ## Genuine `(π₁, composition, π₂)` coordinates -/

/-- Typed collapse coordinates.  `compositionBlocks` together with its two
certificates is exactly a positive composition of `inside.length`; keeping
its data fields exposed makes equality of coordinates proof-irrelevant. -/
@[ext]
structure CollapseCoordinates (A B : Type*) where
  /-- The flattened inside word `π₁`. -/
  inside : List A
  /-- Positive block lengths, i.e. the composition between `π₁` and `π₂`. -/
  compositionBlocks : List ℕ
  compositionBlocks_pos :
    ∀ {k : ℕ}, k ∈ compositionBlocks → 0 < k
  compositionBlocks_sum : compositionBlocks.sum = inside.length
  /-- The collapsed outside word `π₂`. -/
  collapsed : List (Unit ⊕ B)
  marker_count : markerCount collapsed = compositionBlocks.length
  noTwoAdjacentMarkers : NoTwoAdjacentMarkers collapsed

namespace CollapseCoordinates

/-- The genuine mathlib `Composition` carried by the coordinate block
lengths. -/
def composition (q : CollapseCoordinates A B) :
    Composition q.inside.length where
  blocks := q.compositionBlocks
  blocks_pos := q.compositionBlocks_pos
  blocks_sum := q.compositionBlocks_sum

@[simp] theorem composition_blocks (q : CollapseCoordinates A B) :
    q.composition.blocks = q.compositionBlocks :=
  rfl

@[simp] theorem composition_length (q : CollapseCoordinates A B) :
    q.composition.length = q.compositionBlocks.length :=
  rfl

end CollapseCoordinates

/-- Forget the explicit coordinates by splitting `π₁` at the composition
boundaries. -/
def collapseCoordinatesToRaw (q : CollapseCoordinates A B) :
    RawCollapseData A B :=
  ⟨(q.inside.splitWrtComposition q.composition, q.collapsed), by
    refine ⟨?_, ?_, q.noTwoAdjacentMarkers⟩
    · intro block hblock
      exact List.ne_nil_of_length_pos
        (List.length_pos_of_mem_splitWrtComposition hblock)
    · simpa using q.marker_count⟩

/-- Read the flattened inside word, its block composition, and the collapsed
word from raw collapse data. -/
def rawToCollapseCoordinates (d : RawCollapseData A B) :
    CollapseCoordinates A B :=
  { inside := d.insideList
    compositionBlocks := d.blocks.map List.length
    compositionBlocks_pos := by
      intro k hk
      obtain ⟨block, hblock, rfl⟩ := List.mem_map.1 hk
      exact List.length_pos_iff.2 (d.2.1 block hblock)
    compositionBlocks_sum := by
      simp [RawCollapseData.insideList, List.length_flatten]
    collapsed := d.collapsed
    marker_count := by
      calc
        markerCount d.collapsed = d.blocks.length := d.2.2.1
        _ = (d.blocks.map List.length).length := by simp
    noTwoAdjacentMarkers := d.2.2.2 }

/-- Raw block/collapsed data are equivalent to the explicit
`(π₁, composition, π₂)` coordinates. -/
def rawCollapseCoordinatesEquiv (A B : Type*) :
    RawCollapseData A B ≃ CollapseCoordinates A B where
  toFun := rawToCollapseCoordinates
  invFun := collapseCoordinatesToRaw
  left_inv d := by
    apply Subtype.ext
    apply Prod.ext
    · exact d.split_insideList_blockComposition
    · rfl
  right_inv q := by
    apply CollapseCoordinates.ext
    · exact List.flatten_splitWrtComposition q.inside q.composition
    · exact List.map_length_splitWrtComposition q.inside q.composition
    · rfl

end Anderson4D
