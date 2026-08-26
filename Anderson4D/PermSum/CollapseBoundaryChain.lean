import Anderson4D.PermSum.CollapseChain
import Anderson4D.PermSum.CollapseEmbedding

/-!
# Tree-geometric boundary comparison for the collapse chain

This file connects the raw segmented-chain estimate of `CollapseChain` to
the actual inside/outside leaf carriers and lattice edge weights used in
paper (5.43).
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Tree-facing edge functions -/

/-- Position of an original split letter. -/
def originalCollapsePoint {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) {r : VPos t} :
    InsideLeaf r ⊕ OutsideLeaf r → Fin 4 → ℤ
  | .inl l => z l.1
  | .inr y => z y.1

/-- Position of a collapsed letter: the marker is represented by `lstar`,
and outside leaves keep their original positions. -/
def collapsedCollapsePoint {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) :
    Unit ⊕ OutsideLeaf r → Fin 4 → ℤ
  | .inl _ => contractEmbedding z r lstar (contractMarkerLeaf r)
  | .inr y => contractEmbedding z r lstar (contractOutsideLeaf r y)

/-- Original lattice edge on the inside/outside split alphabet. -/
def originalCollapseEdge {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) {r : VPos t}
    (x y : InsideLeaf r ⊕ OutsideLeaf r) : ℝ :=
  latticeEdgeWeight (originalCollapsePoint z x)
    (originalCollapsePoint z y)

/-- Collapsed lattice edge on the marker/outside alphabet. -/
def collapsedCollapseEdge {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r)
    (x y : Unit ⊕ OutsideLeaf r) : ℝ :=
  latticeEdgeWeight (collapsedCollapsePoint z r lstar x)
    (collapsedCollapsePoint z r lstar y)

theorem originalCollapseEdge_nonneg {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) {r : VPos t}
    (x y : InsideLeaf r ⊕ OutsideLeaf r) :
    0 ≤ originalCollapseEdge z x y := by
  unfold originalCollapseEdge latticeEdgeWeight
  positivity

theorem collapsedCollapseEdge_nonneg {t : PlaneTree}
    (z : HeppLeaf t → Fin 4 → ℤ) (r : VPos t)
    (lstar : InsideLeaf r) (x y : Unit ⊕ OutsideLeaf r) :
    0 ≤ collapsedCollapseEdge z r lstar x y := by
  unfold collapsedCollapseEdge latticeEdgeWeight
  positivity

/-! ## Structural shape of canonical collapse segments -/

/-- Every canonical collapse segment is either an outside singleton or a
nonempty block consisting entirely of inside letters. -/
def IsCanonicalCollapseSegment {A B : Type*}
    (p : ChainSegment (A ⊕ B) (Unit ⊕ B)) : Prop :=
  (∃ b : B, p.tag = .inr b ∧ p.letters = [.inr b]) ∨
    ∃ block : List A, block ≠ [] ∧
      p.tag = .inl () ∧ p.letters = block.map Sum.inl

theorem canonical_of_mem_collapseSegmentsAux {A B : Type*} :
    ∀ (blocks : List (List A)) (collapsed : List (Unit ⊕ B))
      (hblocks : ∀ block ∈ blocks, block ≠ [])
      (p : ChainSegment (A ⊕ B) (Unit ⊕ B)),
      p ∈ collapseSegmentsAux blocks collapsed hblocks →
        IsCanonicalCollapseSegment p
  | _, [], _, p, hp => by
      simp [collapseSegmentsAux] at hp
  | blocks, .inr b :: collapsed, hblocks, p, hp => by
      simp only [collapseSegmentsAux, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inl ⟨b, rfl, rfl⟩
      · exact canonical_of_mem_collapseSegmentsAux
          blocks collapsed hblocks p hp
  | [], .inl u :: collapsed, hblocks, p, hp => by
      exact canonical_of_mem_collapseSegmentsAux
        [] collapsed (by simp) p (by
          simpa only [collapseSegmentsAux] using hp)
  | block :: blocks, .inl u :: collapsed, hblocks, p, hp => by
      have hblock : block ≠ [] :=
        hblocks block (List.mem_cons_self)
      have htail : ∀ b ∈ blocks, b ≠ [] :=
        fun b hb => hblocks b (List.mem_cons_of_mem block hb)
      simp only [collapseSegmentsAux, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact Or.inr ⟨block, hblock, rfl, rfl⟩
      · exact canonical_of_mem_collapseSegmentsAux
          blocks collapsed htail p hp

theorem RawCollapseData.canonical_chainSegment {A B : Type*}
    (d : RawCollapseData A B)
    (p : ChainSegment (A ⊕ B) (Unit ⊕ B))
    (hp : p ∈ d.chainSegments) :
    IsCanonicalCollapseSegment p :=
  canonical_of_mem_collapseSegmentsAux d.blocks d.collapsed d.2.1 p hp

/-! ## Local changed-boundary comparison -/

/-- The geometric comparison for a single adjacent pair of canonical
segments.  The impossible marker-marker case is ruled out by the tag-chain
hypothesis inherited from `NoTwoAdjacentMarkers`. -/
theorem canonical_segmentBoundary_le {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    (p q : ChainSegment
      (InsideLeaf r ⊕ OutsideLeaf r) (Unit ⊕ OutsideLeaf r))
    (hp : IsCanonicalCollapseSegment p)
    (hq : IsCanonicalCollapseSegment q)
    (htags : p.tag.isLeft = false ∨ q.tag.isLeft = false) :
    segmentBoundaryEdge (originalCollapseEdge z) p q ≤
      (2 : ℝ) ^ markerBoundaryIndicator p.tag q.tag *
        collapsedCollapseEdge z r lstar p.tag q.tag := by
  rcases p with ⟨ptag, pletters, pne⟩
  rcases q with ⟨qtag, qletters, qne⟩
  rcases hp with hpOutside | hpInside
  · obtain ⟨y, hpTag, hpLetters⟩ := hpOutside
    rcases hq with hqOutside | hqInside
    · obtain ⟨y', hqTag, hqLetters⟩ := hqOutside
      change ptag = Sum.inr y at hpTag
      change pletters = [Sum.inr y] at hpLetters
      change qtag = Sum.inr y' at hqTag
      change qletters = [Sum.inr y'] at hqLetters
      subst ptag
      subst qtag
      subst pletters
      subst qletters
      simp [segmentBoundaryEdge, ChainSegment.last, ChainSegment.first,
        originalCollapseEdge, originalCollapsePoint,
        collapsedCollapseEdge, collapsedCollapsePoint,
        markerBoundaryIndicator, contractEmbedding_apply_outside]
    · obtain ⟨block, hblock, hqTag, hqLetters⟩ := hqInside
      obtain ⟨l, rest, rfl⟩ := List.exists_cons_of_ne_nil hblock
      change ptag = Sum.inr y at hpTag
      change pletters = [Sum.inr y] at hpLetters
      change qtag = Sum.inl () at hqTag
      change qletters = (l :: rest).map Sum.inl at hqLetters
      subst ptag
      subst qtag
      subst pletters
      subst qletters
      have hquarter :=
        contractEmbedding_boundary_quarter ht Nm mu z hsep hdiam hr
          l lstar y
      simpa [segmentBoundaryEdge, ChainSegment.last, ChainSegment.first,
        originalCollapseEdge, originalCollapsePoint,
        collapsedCollapseEdge, collapsedCollapsePoint,
        markerBoundaryIndicator, contractEmbedding_apply_outside] using
        latticeEdgeWeight_le_two_mul_of_quarter_replacement
          (contractEmbedding z r lstar (contractOutsideLeaf r y))
          (z l.1)
          (contractEmbedding z r lstar (contractMarkerLeaf r))
          hquarter
  · obtain ⟨block, hblock, hpTag, hpLetters⟩ := hpInside
    rcases hq with hqOutside | hqInside
    · obtain ⟨y, hqTag, hqLetters⟩ := hqOutside
      change ptag = Sum.inl () at hpTag
      change pletters = block.map Sum.inl at hpLetters
      change qtag = Sum.inr y at hqTag
      change qletters = [Sum.inr y] at hqLetters
      subst ptag
      subst qtag
      subst pletters
      subst qletters
      let l : InsideLeaf r :=
        block.getLast hblock
      have hquarter :=
        contractEmbedding_boundary_quarter ht Nm mu z hsep hdiam hr
          l lstar y
      simpa [l, segmentBoundaryEdge, ChainSegment.last, ChainSegment.first,
        originalCollapseEdge, originalCollapsePoint,
        collapsedCollapseEdge, collapsedCollapsePoint,
        markerBoundaryIndicator, contractEmbedding_apply_outside] using
        latticeEdgeWeight_le_two_mul_of_quarter_replacement_left
          (contractEmbedding z r lstar (contractOutsideLeaf r y))
          (z l.1)
          (contractEmbedding z r lstar (contractMarkerLeaf r))
          hquarter
    · obtain ⟨block', hblock', hqTag, hqLetters⟩ := hqInside
      change ptag = Sum.inl () at hpTag
      change qtag = Sum.inl () at hqTag
      subst ptag
      subst qtag
      simp at htags

/-- Canonical segments of raw collapse data satisfy the local comparison
required by the raw chain theorem. -/
theorem RawCollapseData.chainSegments_isChain_boundaryComparison
    {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    d.chainSegments.IsChain fun p q =>
      segmentBoundaryEdge (originalCollapseEdge z) p q ≤
        (2 : ℝ) ^ markerBoundaryIndicator p.tag q.tag *
          collapsedCollapseEdge z r lstar p.tag q.tag := by
  have htags :
      d.chainSegments.IsChain fun p q =>
        p.tag.isLeft = false ∨ q.tag.isLeft = false := by
    have hcollapsed :
        (d.chainSegments.map ChainSegment.tag).IsChain
          (fun x y => x.isLeft = false ∨ y.isLeft = false) := by
      rw [d.map_tag_chainSegments]
      exact d.2.2.2
    exact (List.isChain_map ChainSegment.tag).mp hcollapsed
  exact htags.imp_of_mem_imp fun p q hp hq hpq =>
    canonical_segmentBoundary_le ht Nm mu z hsep hdiam hr lstar
      p q (d.canonical_chainSegment p hp)
      (d.canonical_chainSegment q hq) hpq

/-! ## Tree-facing (5.43) -/

/-- Tree-geometric form of paper (5.43): the expanded original chain is
bounded by the internal inside-block chains times the collapsed chain, with
the corrected loss `4^(total inside length)`. -/
theorem RawCollapseData.expandWord_latticeChain_le_four_pow
    {t : PlaneTree}
    (ht : t.isValid = true)
    (Nm : HeppMarking t) (mu : Multiplicities t)
    (z : HeppLeaf t → Fin 4 → ℤ)
    (hsep : IsSeparatedEmbedding Nm z)
    (hdiam : SatisfiesSubtreeDiameter Nm mu z)
    {r : VPos t} (hr : CollapseEligible Nm mu r)
    (lstar : InsideLeaf r)
    (d : RawCollapseData (InsideLeaf r) (OutsideLeaf r)) :
    listChainProduct (originalCollapseEdge z) d.expandWord ≤
      (4 : ℝ) ^ d.insideLength *
        d.insideBlockChainProduct (originalCollapseEdge z) *
        listChainProduct (collapsedCollapseEdge z r lstar) d.collapsed := by
  exact d.expandWord_chain_le_four_pow_insideLength
    (originalCollapseEdge z) (collapsedCollapseEdge z r lstar)
    (originalCollapseEdge_nonneg z)
    (collapsedCollapseEdge_nonneg z r lstar)
    (d.chainSegments_isChain_boundaryComparison
      ht Nm mu z hsep hdiam hr lstar)

/-!
## Coordinate-product identity

The geometric (5.43) estimate combines with the exact identity

`d.insideBlockChainProduct (originalCollapseEdge z) =
  heppChainWeightExcept (restrictEmbedding z r)
    d.adjacentCutIndices (restrictedInsideWord r d)`.

This is the finite-product reindexing statement that deleting the
`blockComposition` proper partial-sum gaps from the flattened inside word
leaves exactly the product of the internal block chains; it is independent of
the boundary geometry proved here.
-/

end

end Anderson4D
