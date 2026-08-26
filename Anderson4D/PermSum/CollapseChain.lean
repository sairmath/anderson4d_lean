import Anderson4D.PermSum.CollapseGeometry
import Anderson4D.PermSum.CollapseWords
import Anderson4D.PermSum.MergeRuns

/-!
# Chain-product decomposition for the Proposition 5.9 collapse

This file proves the list-level core of paper (5.43).  An expanded word is
split into nonempty tagged segments: a singleton for every outside letter
and one inside block for every marker.  Its chain product factors exactly
into internal segment products and boundary products.  Only boundaries
incident to a marker may change under collapse.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open scoped BigOperators

noncomputable section

variable {X Y R : Type*}

/-! ## Generic nonempty-segment calculus -/

/-- A nonempty chain segment carrying the letter used to represent it after
collapse. -/
structure ChainSegment (X Y : Type*) where
  tag : Y
  letters : List X
  nonempty : letters ≠ []

namespace ChainSegment

/-- First letter of a nonempty segment. -/
def first (s : ChainSegment X Y) : X :=
  s.letters.head s.nonempty

/-- Final letter of a nonempty segment. -/
def last (s : ChainSegment X Y) : X :=
  s.letters.getLast s.nonempty

@[simp] theorem first_mk (tag : Y) (x : X) (xs : List X) :
    (⟨tag, x :: xs, by simp⟩ : ChainSegment X Y).first = x :=
  rfl

end ChainSegment

/-- Chain product across the boundary between two nonempty segments. -/
def segmentBoundaryEdge (edge : X → X → R)
    (p q : ChainSegment X Y) : R :=
  edge p.last q.first

/-- Flatten the letters of a list of nonempty segments. -/
def flattenSegments (segments : List (ChainSegment X Y)) : List X :=
  (segments.map ChainSegment.letters).flatten

/-- Product of the chain products internal to each segment. -/
def internalSegmentProduct [Monoid R] (edge : X → X → R)
    (segments : List (ChainSegment X Y)) : R :=
  (segments.map fun s => listChainProduct edge s.letters).prod

private theorem listChainProduct_append_of_nonempty [Monoid R]
    (edge : X → X → R) :
    ∀ (xs ys : List X) (hxs : xs ≠ []) (hys : ys ≠ []),
      listChainProduct edge (xs ++ ys) =
        listChainProduct edge xs *
          edge (xs.getLast hxs) (ys.head hys) *
          listChainProduct edge ys
  | [], _, hxs, _ => (hxs rfl).elim
  | [x], [], _, hys => (hys rfl).elim
  | [x], y :: ys, _, _ => by
      simp [listChainProduct]
  | x :: y :: xs, ys, hwhole, hys => by
      have htail : y :: xs ≠ [] := by simp
      rw [show (x :: y :: xs) ++ ys = x :: ((y :: xs) ++ ys) by rfl]
      change edge x y * listChainProduct edge ((y :: xs) ++ ys) =
        (edge x y * listChainProduct edge (y :: xs)) *
          edge ((x :: y :: xs).getLast hwhole) (ys.head hys) *
            listChainProduct edge ys
      rw [listChainProduct_append_of_nonempty edge (y :: xs) ys htail hys]
      have hlast :
          (x :: y :: xs).getLast hwhole =
            (y :: xs).getLast htail := by
        simp
      rw [hlast]
      ac_rfl

/-- Exact factorization of a flattened segmented chain into all internal
segment chains and the chain of segment-boundary edges. -/
theorem listChainProduct_flattenSegments [CommMonoid R]
    (edge : X → X → R) (segments : List (ChainSegment X Y)) :
    listChainProduct edge (flattenSegments segments) =
      internalSegmentProduct edge segments *
        listChainProduct (segmentBoundaryEdge edge) segments := by
  induction segments with
  | nil =>
      simp [flattenSegments, internalSegmentProduct, listChainProduct]
  | cons p ps ih =>
      cases ps with
      | nil =>
          simp [flattenSegments, internalSegmentProduct, listChainProduct]
      | cons q qs =>
          have htail :
              flattenSegments (q :: qs) ≠ [] := by
            simp [flattenSegments, q.nonempty]
          rw [show flattenSegments (p :: q :: qs) =
            p.letters ++ flattenSegments (q :: qs) by
              simp [flattenSegments]]
          rw [listChainProduct_append_of_nonempty edge
            p.letters (flattenSegments (q :: qs)) p.nonempty htail]
          rw [ih]
          simp only [internalSegmentProduct, List.map_cons, List.prod_cons,
            listChainProduct]
          have hfirst :
              (flattenSegments (q :: qs)).head htail = q.first := by
            simp [flattenSegments, ChainSegment.first, q.nonempty]
          rw [hfirst]
          unfold segmentBoundaryEdge
          ac_rfl

/-- Nonnegativity of a real-valued list chain product. -/
theorem listChainProduct_nonneg {α : Type*} (edge : α → α → ℝ)
    (hedge : ∀ x y, 0 ≤ edge x y) :
    ∀ l : List α, 0 ≤ listChainProduct edge l
  | [] => by simp [listChainProduct]
  | [_] => by simp [listChainProduct]
  | x :: y :: rest => by
      simp only [listChainProduct]
      exact mul_nonneg (hedge x y)
        (listChainProduct_nonneg edge hedge (y :: rest))

/-- Pointwise comparison on adjacent pairs compares the two chain products. -/
theorem listChainProduct_le_of_isChain {α : Type*}
    (f g : α → α → ℝ)
    (hf : ∀ x y, 0 ≤ f x y) (hg : ∀ x y, 0 ≤ g x y) :
    ∀ l : List α, l.IsChain (fun x y => f x y ≤ g x y) →
      listChainProduct f l ≤ listChainProduct g l
  | [], _ => by simp [listChainProduct]
  | [_], _ => by simp [listChainProduct]
  | x :: y :: rest, hchain => by
      have hpair := (List.isChain_cons_cons.mp hchain).1
      have htail := (List.isChain_cons_cons.mp hchain).2
      simp only [listChainProduct]
      exact mul_le_mul hpair
        (listChainProduct_le_of_isChain f g hf hg (y :: rest) htail)
        (listChainProduct_nonneg f hf (y :: rest)) (hg x y)

/-! ## Marker-boundary ledger -/

/-- Natural indicator that a collapsed letter is the marker. -/
def markerIndicator {B : Type*} : Unit ⊕ B → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Natural indicator that a collapsed edge is incident to a marker. -/
def markerBoundaryIndicator {B : Type*}
    (x y : Unit ⊕ B) : ℕ :=
  if x.isLeft = true ∨ y.isLeft = true then 1 else 0

/-- Number of changed boundaries in a collapsed word. -/
def markerBoundaryCount {B : Type*} : List (Unit ⊕ B) → ℕ
  | [] | [_] => 0
  | x :: y :: rest =>
      markerBoundaryIndicator x y + markerBoundaryCount (y :: rest)

/-- A path has at most two marker-incident boundaries per marker.  The
endpoint-inclusive convention used here gives the bound `2(s+1)`. -/
theorem markerBoundaryCount_le_two_mul_markerCount {B : Type*}
    (s : List (Unit ⊕ B)) :
    markerBoundaryCount s ≤ 2 * markerCount s := by
  have strong :
      ∀ s : List (Unit ⊕ B),
        markerBoundaryCount s +
            (match s with
            | [] => 0
            | x :: _ => markerIndicator x) ≤
          2 * markerCount s := by
    intro xs
    induction xs with
    | nil =>
        simp [markerBoundaryCount]
    | cons x xs ih =>
      cases xs with
      | nil =>
        cases x with
        | inl u =>
            cases u
            simp [markerBoundaryCount, markerIndicator, markerCount]
        | inr b =>
            simp [markerBoundaryCount, markerIndicator, markerCount]
      | cons y rest =>
        cases x with
        | inl u =>
            cases u
            cases y with
            | inl u' =>
                cases u'
                simp [markerBoundaryCount, markerBoundaryIndicator,
                  markerIndicator, markerCount] at ih ⊢
                omega
            | inr b =>
                simp [markerBoundaryCount, markerBoundaryIndicator,
                  markerIndicator, markerCount] at ih ⊢
                omega
        | inr b =>
            cases y with
            | inl u =>
                cases u
                simp [markerBoundaryCount, markerBoundaryIndicator,
                  markerIndicator, markerCount] at ih ⊢
                omega
            | inr b' =>
                simp [markerBoundaryCount, markerBoundaryIndicator,
                  markerIndicator, markerCount] at ih ⊢
                omega
  have h := strong s
  split at h <;> omega

/-- Replacing every marker-incident edge factor by twice its collapsed
counterpart extracts exactly one factor `2` per changed boundary. -/
theorem listChainProduct_markerBoundaryCost {B : Type*}
    (edge : (Unit ⊕ B) → (Unit ⊕ B) → ℝ)
    (s : List (Unit ⊕ B)) :
    listChainProduct
        (fun x y =>
          (2 : ℝ) ^ markerBoundaryIndicator x y * edge x y) s =
      (2 : ℝ) ^ markerBoundaryCount s *
        listChainProduct edge s := by
  induction s with
  | nil =>
      simp [markerBoundaryCount, listChainProduct]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [markerBoundaryCount, listChainProduct]
    | cons y rest =>
      simp only [markerBoundaryCount, listChainProduct, pow_add]
      rw [ih]
      ring

/-- Generic boundary comparison for tagged segments. -/
theorem segmentBoundaryProduct_le_markerCost
    {B : Type*} (edge : X → X → ℝ)
    (collapsedEdge : (Unit ⊕ B) → (Unit ⊕ B) → ℝ)
    (segments : List (ChainSegment X (Unit ⊕ B)))
    (hedge : ∀ x y, 0 ≤ edge x y)
    (hcollapsed : ∀ x y, 0 ≤ collapsedEdge x y)
    (hcompare :
      segments.IsChain fun p q =>
        segmentBoundaryEdge edge p q ≤
          (2 : ℝ) ^ markerBoundaryIndicator p.tag q.tag *
            collapsedEdge p.tag q.tag) :
    listChainProduct (segmentBoundaryEdge edge) segments ≤
      (2 : ℝ) ^ markerBoundaryCount (segments.map ChainSegment.tag) *
        listChainProduct collapsedEdge
          (segments.map ChainSegment.tag) := by
  let costEdge : ChainSegment X (Unit ⊕ B) →
      ChainSegment X (Unit ⊕ B) → ℝ :=
    fun p q =>
      (2 : ℝ) ^ markerBoundaryIndicator p.tag q.tag *
        collapsedEdge p.tag q.tag
  have hboundaryNonneg :
      ∀ p q, 0 ≤ segmentBoundaryEdge edge p q :=
    fun (p q : ChainSegment X (Unit ⊕ B)) => hedge p.last q.first
  have hcostNonneg : ∀ p q, 0 ≤ costEdge p q := by
    intro p q
    exact mul_nonneg (by positivity) (hcollapsed p.tag q.tag)
  calc
    listChainProduct (segmentBoundaryEdge edge) segments ≤
        listChainProduct costEdge segments :=
      listChainProduct_le_of_isChain _ _ hboundaryNonneg
        hcostNonneg segments hcompare
    _ = listChainProduct
        (fun x y =>
          (2 : ℝ) ^ markerBoundaryIndicator x y *
            collapsedEdge x y)
        (segments.map ChainSegment.tag) := by
      rw [listChainProduct_map]
    _ = (2 : ℝ) ^
          markerBoundaryCount (segments.map ChainSegment.tag) *
        listChainProduct collapsedEdge
          (segments.map ChainSegment.tag) :=
      listChainProduct_markerBoundaryCost collapsedEdge _

theorem internalSegmentProduct_nonneg
    (edge : X → X → ℝ) (hedge : ∀ x y, 0 ≤ edge x y)
    (segments : List (ChainSegment X Y)) :
    0 ≤ internalSegmentProduct edge segments := by
  unfold internalSegmentProduct
  induction segments with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (listChainProduct_nonneg edge hedge p.letters) ih

/-- Segmented-chain estimate with the corrected `4^(number of markers)`
loss. -/
theorem listChainProduct_flattenSegments_le_four_pow
    {B : Type*} (edge : X → X → ℝ)
    (collapsedEdge : (Unit ⊕ B) → (Unit ⊕ B) → ℝ)
    (segments : List (ChainSegment X (Unit ⊕ B)))
    (hedge : ∀ x y, 0 ≤ edge x y)
    (hcollapsed : ∀ x y, 0 ≤ collapsedEdge x y)
    (hcompare :
      segments.IsChain fun p q =>
        segmentBoundaryEdge edge p q ≤
          (2 : ℝ) ^ markerBoundaryIndicator p.tag q.tag *
            collapsedEdge p.tag q.tag) :
    listChainProduct edge (flattenSegments segments) ≤
      (4 : ℝ) ^ markerCount (segments.map ChainSegment.tag) *
        internalSegmentProduct edge segments *
        listChainProduct collapsedEdge
          (segments.map ChainSegment.tag) := by
  have hboundary :=
    segmentBoundaryProduct_le_markerCost edge collapsedEdge segments
      hedge hcollapsed hcompare
  have hcount :
      markerBoundaryCount (segments.map ChainSegment.tag) ≤
        2 * markerCount (segments.map ChainSegment.tag) :=
    markerBoundaryCount_le_two_mul_markerCount _
  have hpowers :
      (2 : ℝ) ^ markerBoundaryCount (segments.map ChainSegment.tag) ≤
        (4 : ℝ) ^ markerCount (segments.map ChainSegment.tag) := by
    calc
      (2 : ℝ) ^ markerBoundaryCount (segments.map ChainSegment.tag) ≤
          (2 : ℝ) ^ (2 * markerCount
            (segments.map ChainSegment.tag)) :=
        pow_le_pow_right₀ (by norm_num) hcount
      _ = (4 : ℝ) ^ markerCount (segments.map ChainSegment.tag) := by
        rw [pow_mul]
        norm_num
  have hinternal :=
    internalSegmentProduct_nonneg edge hedge segments
  have hcollapsedChain :=
    listChainProduct_nonneg collapsedEdge hcollapsed
      (segments.map ChainSegment.tag)
  rw [listChainProduct_flattenSegments]
  calc
    internalSegmentProduct edge segments *
        listChainProduct (segmentBoundaryEdge edge) segments ≤
      internalSegmentProduct edge segments *
        ((2 : ℝ) ^ markerBoundaryCount
            (segments.map ChainSegment.tag) *
          listChainProduct collapsedEdge
            (segments.map ChainSegment.tag)) :=
      mul_le_mul_of_nonneg_left hboundary hinternal
    _ ≤ internalSegmentProduct edge segments *
        ((4 : ℝ) ^ markerCount (segments.map ChainSegment.tag) *
          listChainProduct collapsedEdge
            (segments.map ChainSegment.tag)) := by
      gcongr
    _ = (4 : ℝ) ^ markerCount (segments.map ChainSegment.tag) *
        internalSegmentProduct edge segments *
        listChainProduct collapsedEdge
          (segments.map ChainSegment.tag) := by ring

/-! ## Segments canonically attached to raw collapse data -/

variable {A B : Type*}

/-- Turn `expand bs collapsed` into nonempty tagged segments.  A marker with
no remaining block is silently dropped, matching `expand`; raw collapse data
exclude that degeneration by their marker-count invariant. -/
def collapseSegmentsAux :
    (bs : List (List A)) → (collapsed : List (Unit ⊕ B)) →
      (∀ block ∈ bs, block ≠ []) →
      List (ChainSegment (A ⊕ B) (Unit ⊕ B))
  | _, [], _ => []
  | bs, .inr b :: collapsed, hbs =>
      ⟨.inr b, [.inr b], by simp⟩ ::
        collapseSegmentsAux bs collapsed hbs
  | [], .inl _ :: collapsed, _ =>
      collapseSegmentsAux [] collapsed (by simp)
  | block :: bs, .inl _ :: collapsed, hbs =>
      let hblock : block ≠ [] :=
        hbs block (List.mem_cons_self)
      let htail : ∀ b ∈ bs, b ≠ [] :=
        fun b hb => hbs b (List.mem_cons_of_mem block hb)
      let hmap : block.map Sum.inl ≠ [] := by
        intro hnil
        have hlength := congrArg List.length hnil
        simp only [List.length_map, List.length_nil] at hlength
        exact hblock (List.length_eq_zero_iff.mp hlength)
      ⟨.inl (), block.map Sum.inl, hmap⟩ ::
        collapseSegmentsAux bs collapsed htail

/-- The segment letters flatten to the definition of `expand`. -/
theorem flattenSegments_collapseSegmentsAux :
    ∀ (bs : List (List A)) (collapsed : List (Unit ⊕ B))
      (hbs : ∀ block ∈ bs, block ≠ []),
      flattenSegments (collapseSegmentsAux bs collapsed hbs) =
        expand bs collapsed
  | bs, [], hbs => by
      simp [collapseSegmentsAux, flattenSegments, expand]
  | bs, .inr b :: collapsed, hbs => by
      change [Sum.inr b] ++
          flattenSegments (collapseSegmentsAux bs collapsed _) =
        Sum.inr b :: expand bs collapsed
      rw [flattenSegments_collapseSegmentsAux bs collapsed hbs]
      rfl
  | [], .inl u :: collapsed, hbs => by
      change flattenSegments (collapseSegmentsAux [] collapsed _) =
        expand [] collapsed
      apply flattenSegments_collapseSegmentsAux
  | block :: bs, .inl u :: collapsed, hbs => by
      have htail : ∀ b ∈ bs, b ≠ [] :=
        fun b hb => hbs b (List.mem_cons_of_mem block hb)
      change block.map Sum.inl ++
          flattenSegments (collapseSegmentsAux bs collapsed _) =
        block.map Sum.inl ++ expand bs collapsed
      rw [flattenSegments_collapseSegmentsAux bs collapsed htail]

/-- With exact marker bookkeeping, segment tags recover the collapsed word. -/
theorem map_tag_collapseSegmentsAux :
    ∀ (bs : List (List A)) (collapsed : List (Unit ⊕ B))
      (hbs : ∀ block ∈ bs, block ≠ []),
      markerCount collapsed = bs.length →
      (collapseSegmentsAux bs collapsed hbs).map ChainSegment.tag =
        collapsed
  | bs, [], hbs, hcount => by
      have hnil : bs = [] := by
        simpa [markerCount] using hcount.symm
      subst bs
      simp [collapseSegmentsAux]
  | bs, .inr b :: collapsed, hbs, hcount => by
      have htail : markerCount collapsed = bs.length := by
        simpa [markerCount] using hcount
      change Sum.inr b ::
          (collapseSegmentsAux bs collapsed _).map ChainSegment.tag =
        Sum.inr b :: collapsed
      rw [map_tag_collapseSegmentsAux bs collapsed hbs htail]
  | [], .inl u :: collapsed, hbs, hcount => by
      simp [markerCount] at hcount
  | block :: bs, .inl u :: collapsed, hbs, hcount => by
      have htailBlocks : ∀ b ∈ bs, b ≠ [] :=
        fun b hb => hbs b (List.mem_cons_of_mem block hb)
      have htail : markerCount collapsed = bs.length := by
        simpa [markerCount] using hcount
      change Sum.inl () ::
          (collapseSegmentsAux bs collapsed _).map ChainSegment.tag =
        Sum.inl u :: collapsed
      cases u
      rw [map_tag_collapseSegmentsAux bs collapsed htailBlocks htail]

/-- Internal segment factors are exactly the products internal to the inside
blocks; outside singleton segments contribute one. -/
theorem internalProduct_collapseSegmentsAux
    (edge : (A ⊕ B) → (A ⊕ B) → ℝ) :
    ∀ (bs : List (List A)) (collapsed : List (Unit ⊕ B))
      (hbs : ∀ block ∈ bs, block ≠ []),
      markerCount collapsed = bs.length →
      internalSegmentProduct edge
          (collapseSegmentsAux bs collapsed hbs) =
        (bs.map fun block =>
          listChainProduct edge (block.map Sum.inl)).prod
  | bs, [], hbs, hcount => by
      have hnil : bs = [] := by
        simpa [markerCount] using hcount.symm
      subst bs
      simp [collapseSegmentsAux, internalSegmentProduct]
  | bs, .inr b :: collapsed, hbs, hcount => by
      have htail : markerCount collapsed = bs.length := by
        simpa [markerCount] using hcount
      change 1 *
          internalSegmentProduct edge
            (collapseSegmentsAux bs collapsed _) =
        (bs.map fun block =>
          listChainProduct edge (block.map Sum.inl)).prod
      rw [one_mul]
      exact internalProduct_collapseSegmentsAux edge bs collapsed hbs htail
  | [], .inl u :: collapsed, hbs, hcount => by
      simp [markerCount] at hcount
  | block :: bs, .inl u :: collapsed, hbs, hcount => by
      have htailBlocks : ∀ b ∈ bs, b ≠ [] :=
        fun b hb => hbs b (List.mem_cons_of_mem block hb)
      have htail : markerCount collapsed = bs.length := by
        simpa [markerCount] using hcount
      change listChainProduct edge (block.map Sum.inl) *
          internalSegmentProduct edge
            (collapseSegmentsAux bs collapsed _) =
        listChainProduct edge (block.map Sum.inl) *
          (bs.map fun b =>
            listChainProduct edge (b.map Sum.inl)).prod
      rw [internalProduct_collapseSegmentsAux edge bs collapsed
        htailBlocks htail]

namespace RawCollapseData

/-- Canonical nonempty segments of raw collapse data. -/
def chainSegments (d : RawCollapseData A B) :
    List (ChainSegment (A ⊕ B) (Unit ⊕ B)) :=
  collapseSegmentsAux d.blocks d.collapsed d.2.1

@[simp] theorem flatten_chainSegments (d : RawCollapseData A B) :
    flattenSegments d.chainSegments = d.expandWord := by
  exact flattenSegments_collapseSegmentsAux d.blocks d.collapsed d.2.1

@[simp] theorem map_tag_chainSegments (d : RawCollapseData A B) :
    d.chainSegments.map ChainSegment.tag = d.collapsed := by
  exact map_tag_collapseSegmentsAux d.blocks d.collapsed d.2.1 d.2.2.1

/-- Product of the chain weights internal to all inside blocks. -/
def insideBlockChainProduct
    (edge : (A ⊕ B) → (A ⊕ B) → ℝ)
    (d : RawCollapseData A B) : ℝ :=
  (d.blocks.map fun block =>
    listChainProduct edge (block.map Sum.inl)).prod

@[simp] theorem internalProduct_chainSegments
    (edge : (A ⊕ B) → (A ⊕ B) → ℝ)
    (d : RawCollapseData A B) :
    internalSegmentProduct edge d.chainSegments =
      d.insideBlockChainProduct edge := by
  exact internalProduct_collapseSegmentsAux edge d.blocks d.collapsed
    d.2.1 d.2.2.1

/-- Raw-coordinate form of (5.43), with the local changed-boundary
comparison exposed as an `IsChain` hypothesis. -/
theorem expandWord_chain_le_four_pow_blocks
    (edge : (A ⊕ B) → (A ⊕ B) → ℝ)
    (collapsedEdge : (Unit ⊕ B) → (Unit ⊕ B) → ℝ)
    (d : RawCollapseData A B)
    (hedge : ∀ x y, 0 ≤ edge x y)
    (hcollapsed : ∀ x y, 0 ≤ collapsedEdge x y)
    (hcompare :
      d.chainSegments.IsChain fun p q =>
        segmentBoundaryEdge edge p q ≤
          (2 : ℝ) ^ markerBoundaryIndicator p.tag q.tag *
            collapsedEdge p.tag q.tag) :
    listChainProduct edge d.expandWord ≤
      (4 : ℝ) ^ d.blocks.length *
        d.insideBlockChainProduct edge *
        listChainProduct collapsedEdge d.collapsed := by
  have h :=
    listChainProduct_flattenSegments_le_four_pow
      edge collapsedEdge d.chainSegments hedge hcollapsed hcompare
  rw [flatten_chainSegments, map_tag_chainSegments,
    internalProduct_chainSegments] at h
  calc
    listChainProduct edge d.expandWord ≤
        (4 : ℝ) ^ markerCount d.collapsed *
          d.insideBlockChainProduct edge *
          listChainProduct collapsedEdge d.collapsed := h
    _ = (4 : ℝ) ^ d.blocks.length *
          d.insideBlockChainProduct edge *
          listChainProduct collapsedEdge d.collapsed := by
      have hmarker : markerCount d.collapsed = d.blocks.length := d.2.2.1
      rw [hmarker]

/-- Paper's coarser `4^n` form, where `n` is the total inside length. -/
theorem expandWord_chain_le_four_pow_insideLength
    (edge : (A ⊕ B) → (A ⊕ B) → ℝ)
    (collapsedEdge : (Unit ⊕ B) → (Unit ⊕ B) → ℝ)
    (d : RawCollapseData A B)
    (hedge : ∀ x y, 0 ≤ edge x y)
    (hcollapsed : ∀ x y, 0 ≤ collapsedEdge x y)
    (hcompare :
      d.chainSegments.IsChain fun p q =>
        segmentBoundaryEdge edge p q ≤
          (2 : ℝ) ^ markerBoundaryIndicator p.tag q.tag *
            collapsedEdge p.tag q.tag) :
    listChainProduct edge d.expandWord ≤
      (4 : ℝ) ^ d.insideLength *
        d.insideBlockChainProduct edge *
        listChainProduct collapsedEdge d.collapsed := by
  have hraw :=
    d.expandWord_chain_le_four_pow_blocks edge collapsedEdge
      hedge hcollapsed hcompare
  have hblocks : d.blocks.length ≤ d.insideLength := by
    simpa using d.blockComposition.length_le
  have hpow : (4 : ℝ) ^ d.blocks.length ≤ 4 ^ d.insideLength :=
    pow_le_pow_right₀ (by norm_num) hblocks
  have hrest :
      0 ≤ d.insideBlockChainProduct edge *
        listChainProduct collapsedEdge d.collapsed := by
    exact mul_nonneg
      (by
        unfold insideBlockChainProduct
        induction d.blocks with
        | nil => simp
        | cons block blocks ih =>
            simp only [List.map_cons, List.prod_cons]
            exact mul_nonneg
              (listChainProduct_nonneg edge hedge (block.map Sum.inl)) ih)
      (listChainProduct_nonneg collapsedEdge hcollapsed d.collapsed)
  calc
    listChainProduct edge d.expandWord ≤
        (4 : ℝ) ^ d.blocks.length *
          d.insideBlockChainProduct edge *
          listChainProduct collapsedEdge d.collapsed := hraw
    _ = (4 : ℝ) ^ d.blocks.length *
        (d.insideBlockChainProduct edge *
          listChainProduct collapsedEdge d.collapsed) := by ring
    _ ≤ (4 : ℝ) ^ d.insideLength *
        (d.insideBlockChainProduct edge *
          listChainProduct collapsedEdge d.collapsed) :=
      mul_le_mul_of_nonneg_right hpow hrest
    _ = (4 : ℝ) ^ d.insideLength *
        d.insideBlockChainProduct edge *
        listChainProduct collapsedEdge d.collapsed := by ring

end RawCollapseData

end

end Anderson4D
