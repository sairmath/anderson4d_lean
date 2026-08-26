import Anderson4D.DetParametrix.Paper42_Moment.R324PaperNestedSuffixGeometry
import Anderson4D.DetParametrix.Paper42_Moment.R324EndpointIntegratedGroupedMajorant

/-!
# Ordered half-chain partitions for the paper's nested Step 3

The endpoint-erased chain of a completed half has one slot for every
surviving vertex except the last one. If a current carrier is split into
two nonempty consecutive pieces, those slots split into the internal slots
of the first piece, the unique slot at its last vertex, and the internal
slots of the second piece. The middle slot is the flanking connector used
by the nested-cross induction.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace R324WithinHalfResidualPrefix

variable {ρ : SmoothCutoff} {lam ε : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}

/-- Production slots of a nonempty sparse half-carrier, with its terminal
source vertex erased. -/
def halfChainEdgeSlots
    (_res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (carrier : Finset (Fin m)) (hne : carrier.Nonempty) :
    Finset (Fin (m + 1)) :=
  (carrier.erase (carrier.max' hne)).image
    r324InternalVertexEdgeSlot

private theorem r324InternalVertexEdgeSlot_injective_local :
    Function.Injective
      (r324InternalVertexEdgeSlot : Fin m → Fin (m + 1)) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [r324InternalVertexEdgeSlot] at hval
  omega

/-- The endpoint-erased active slots are exactly the nonterminal source
slots of the full surviving half-carrier. -/
theorem endpointErasedActiveEdgeSlots_eq_halfChainEdgeSlots
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) :
    res.endpointErasedActiveEdgeSlots hactive =
      res.halfChainEdgeSlots res.state.active hactive := by
  unfold endpointErasedActiveEdgeSlots halfChainEdgeSlots
    terminalOutgoingEdgeSlot activeEdgeSlots
  rw [Finset.image_erase
    (r324InternalVertexEdgeSlot_injective_local (m := m))]
  ext edge
  simp only [Finset.mem_erase, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro ⟨hneMax, hneZero, hzero | himage⟩
    · exact (hneZero hzero).elim
    · exact ⟨hneMax, himage⟩
  · rintro ⟨hneMax, i, hi, rfl⟩
    refine ⟨hneMax, ?_, Or.inr ⟨i, hi, rfl⟩⟩
    intro hzero
    have hval := congrArg Fin.val hzero
    simp only [r324InternalVertexEdgeSlot, Fin.val_zero] at hval
    omega

/-- Strict separation of two finite half-carriers. -/
def HalfCarrierBefore
    (first second : Finset (Fin m)) : Prop :=
  ∀ i ∈ first, ∀ j ∈ second, i < j

private theorem max'_union_eq_right_of_before
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second) :
    (first ∪ second).max' (hfirst.mono Finset.subset_union_left) =
      second.max' hsecond := by
  apply le_antisymm
  · have hmem :=
      Finset.max'_mem (first ∪ second)
        (hfirst.mono Finset.subset_union_left)
    rcases Finset.mem_union.mp hmem with hmemFirst | hmemSecond
    · exact (hbefore _ hmemFirst _
        (Finset.max'_mem second hsecond)).le
    · exact Finset.le_max' second _ hmemSecond
  · exact Finset.le_max' (first ∪ second) _
      (Finset.mem_union_right first
        (Finset.max'_mem second hsecond))

private theorem erase_max'_union_eq_of_before
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second) :
    (first ∪ second).erase
        ((first ∪ second).max'
          (hfirst.mono Finset.subset_union_left)) =
      (first.erase (first.max' hfirst) ∪
          {first.max' hfirst}) ∪
        second.erase (second.max' hsecond) := by
  have hmax := max'_union_eq_right_of_before
    first second hfirst hsecond hbefore
  rw [hmax]
  ext i
  simp only [Finset.mem_erase, Finset.mem_union,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hine, hiFirst | hiSecond⟩
    · by_cases hieq : i = first.max' hfirst
      · exact Or.inl (Or.inr hieq)
      · exact Or.inl (Or.inl ⟨hieq, hiFirst⟩)
    · exact Or.inr ⟨hine, hiSecond⟩
  · rintro (⟨⟨_hineFirstMax, hiFirst⟩ | hieq⟩ |
      ⟨hineSecondMax, hiSecond⟩)
    · refine ⟨?_, Or.inl hiFirst⟩
      intro hisec
      have hlt := hbefore i hiFirst (second.max' hsecond)
        (Finset.max'_mem second hsecond)
      exact (ne_of_lt hlt) hisec
    · subst i
      refine ⟨?_, Or.inl (Finset.max'_mem first hfirst)⟩
      intro hisec
      have hlt := hbefore (first.max' hfirst)
        (Finset.max'_mem first hfirst) (second.max' hsecond)
        (Finset.max'_mem second hsecond)
      exact (ne_of_lt hlt) hisec
    · exact ⟨hineSecondMax, Or.inr hiSecond⟩

/-- **Three-way ordered slot partition.** For consecutive nonempty
carriers `first < second`, the only slot between their two internal paths
is the slot sourced at `max first`. -/
theorem halfChainEdgeSlots_union_eq_threeWay_of_before
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second) :
    res.halfChainEdgeSlots (first ∪ second)
        (hfirst.mono Finset.subset_union_left) =
      (res.halfChainEdgeSlots first hfirst ∪
          {r324InternalVertexEdgeSlot (first.max' hfirst)}) ∪
        res.halfChainEdgeSlots second hsecond := by
  unfold halfChainEdgeSlots
  rw [erase_max'_union_eq_of_before
      first second hfirst hsecond hbefore,
    Finset.image_union, Finset.image_union,
    Finset.image_singleton]

/-- The first internal slot family is disjoint from its outgoing
connector. -/
theorem halfChainEdgeSlots_disjoint_connector
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (carrier : Finset (Fin m)) (hne : carrier.Nonempty) :
    Disjoint (res.halfChainEdgeSlots carrier hne)
      {r324InternalVertexEdgeSlot (carrier.max' hne)} := by
  rw [Finset.disjoint_left]
  intro edge hedge hconnector
  obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hedge
  have heq : i = carrier.max' hne :=
    r324InternalVertexEdgeSlot_injective_local
      (hieq.trans (Finset.mem_singleton.mp hconnector))
  exact (Finset.mem_erase.mp hi).1 heq

/-- All slots belonging to strictly separated carriers are disjoint. -/
theorem halfChainEdgeSlots_disjoint_of_before
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second) :
    Disjoint (res.halfChainEdgeSlots first hfirst)
      (res.halfChainEdgeSlots second hsecond) := by
  rw [halfChainEdgeSlots, halfChainEdgeSlots,
    Finset.disjoint_image
      (r324InternalVertexEdgeSlot_injective_local (m := m)),
    Finset.disjoint_left]
  intro i hiFirst hiSecond
  have hlt := hbefore i (Finset.mem_erase.mp hiFirst).2 i
    (Finset.mem_erase.mp hiSecond).2
  exact (lt_irrefl i) hlt

/-- The connector slot is disjoint from every slot in the later carrier. -/
theorem connector_disjoint_halfChainEdgeSlots_of_before
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second) :
    Disjoint {r324InternalVertexEdgeSlot (first.max' hfirst)}
      (res.halfChainEdgeSlots second hsecond) := by
  rw [Finset.disjoint_left]
  intro edge hconnector hedge
  obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hedge
  have heq : first.max' hfirst = j :=
    r324InternalVertexEdgeSlot_injective_local
      ((Finset.mem_singleton.mp hconnector).symm.trans hjeq.symm)
  have hlt := hbefore (first.max' hfirst)
    (Finset.max'_mem first hfirst) j (Finset.mem_erase.mp hj).2
  exact (ne_of_lt hlt) heq

/-- When the two consecutive pieces exhaust the active carrier, the
successor of the unique connector source is the first vertex of the later
piece. This identifies the singleton slot above with the literal sparse
chain leg, not merely with a counting placeholder. -/
theorem edgeSuccessor_connector_eq_varIdx_min'
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second)
    (hactive : res.state.active = first ∪ second) :
    res.edgeSuccessor
        (r324InternalVertexEdgeSlot (first.max' hfirst)) =
      varIdx (second.min' hsecond) := by
  unfold edgeSuccessor
  rw [Finset.min'_eq_iff]
  constructor
  · rw [edgeSuccessorCandidates]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨second.min' hsecond, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [hactive]
      exact Finset.mem_union_right first
        (Finset.min'_mem second hsecond)
    · simp only [r324InternalVertexEdgeSlot, varIdx_val]
      exact Nat.add_lt_add_right
        (hbefore (first.max' hfirst)
          (Finset.max'_mem first hfirst) (second.min' hsecond)
          (Finset.min'_mem second hsecond)) 1
  · intro candidate hcandidate
    rw [edgeSuccessorCandidates] at hcandidate
    rcases Finset.mem_union.mp hcandidate with hlast | hinter
    · have hc : candidate = Fin.last (m + 1) := by
        simpa only [Finset.mem_singleton] using hlast
      rw [hc]
      exact Fin.le_last _
    · obtain ⟨k, hk, hkcandidate⟩ := Finset.mem_image.mp hinter
      have hkActive := (Finset.mem_filter.mp hk).1
      have hkAfter := (Finset.mem_filter.mp hk).2
      rw [hactive] at hkActive
      rcases Finset.mem_union.mp hkActive with hkFirst | hkSecond
      · have hkLe := Finset.le_max' first k hkFirst
        simp only [r324InternalVertexEdgeSlot, varIdx_val] at hkAfter
        omega
      · rw [← hkcandidate]
        exact Fin.mk_le_mk.mpr
          (Nat.succ_le_succ
            (Finset.min'_le second k hkSecond))

/-- Coordinate form of the connector leg. -/
theorem edgeDisplacement_connector_eq
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second)
    (hactive : res.state.active = first ∪ second)
    (v : res.SurvivingCoordinate → T4) :
    res.edgeDisplacement 0 0 (res.reconstruct v)
        (r324InternalVertexEdgeSlot (first.max' hfirst)) =
      v ⟨first.max' hfirst, by
          rw [hactive]
          exact Finset.mem_union_left second
            (Finset.max'_mem first hfirst)⟩ -
        v ⟨second.min' hsecond, by
          rw [hactive]
          exact Finset.mem_union_right first
            (Finset.min'_mem second hsecond)⟩ := by
  let source : res.SurvivingCoordinate :=
    ⟨first.max' hfirst, by
      rw [hactive]
      exact Finset.mem_union_left second
        (Finset.max'_mem first hfirst)⟩
  let target : res.SurvivingCoordinate :=
    ⟨second.min' hsecond, by
      rw [hactive]
      exact Finset.mem_union_right first
        (Finset.min'_mem second hsecond)⟩
  have hsource :
      (r324InternalVertexEdgeSlot
        (first.max' hfirst)).castSucc =
          varIdx (first.max' hfirst) := by
    apply Fin.ext
    rfl
  unfold edgeDisplacement
  rw [hsource,
    res.edgeSuccessor_connector_eq_varIdx_min'
      first second hfirst hsecond hbefore hactive,
    assemble_varIdx, assemble_varIdx]
  change res.reconstruct v source.1 - res.reconstruct v target.1 = _
  rw [res.reconstruct_surviving v source,
    res.reconstruct_surviving v target]

/-- Inverse-square product restricted to one nonempty half-carrier. -/
def halfInvSqChainProduct
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (carrier : Finset (Fin m)) (hne : carrier.Nonempty)
    (v : res.SurvivingCoordinate → T4) : ℝ :=
  ∏ edge ∈ res.halfChainEdgeSlots carrier hne,
    invSqKer
      (res.edgeDisplacement 0 0 (res.reconstruct v) edge)

/-- The full endpoint-erased inverse-square chain is the restricted
product on the complete active carrier. -/
theorem endpointErasedInvSqChainProduct_eq_halfInvSqChainProduct
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty)
    (v : res.SurvivingCoordinate → T4) :
    res.endpointErasedInvSqChainProduct hactive v =
      res.halfInvSqChainProduct res.state.active hactive v := by
  unfold endpointErasedInvSqChainProduct halfInvSqChainProduct
  rw [res.endpointErasedActiveEdgeSlots_eq_halfChainEdgeSlots hactive]

/-- Product form of the three-way ordered slot partition. -/
theorem halfInvSqChainProduct_union_eq_threeWay_of_before
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (first second : Finset (Fin m))
    (hfirst : first.Nonempty) (hsecond : second.Nonempty)
    (hbefore : HalfCarrierBefore first second)
    (v : res.SurvivingCoordinate → T4) :
    res.halfInvSqChainProduct (first ∪ second)
        (hfirst.mono Finset.subset_union_left) v =
      res.halfInvSqChainProduct first hfirst v *
        invSqKer
          (res.edgeDisplacement 0 0 (res.reconstruct v)
            (r324InternalVertexEdgeSlot (first.max' hfirst))) *
        res.halfInvSqChainProduct second hsecond v := by
  let f : Fin (m + 1) → ℝ := fun edge =>
    invSqKer
      (res.edgeDisplacement 0 0 (res.reconstruct v) edge)
  have hfirstConnector :=
    res.halfChainEdgeSlots_disjoint_connector first hfirst
  have hfirstSecond :=
    res.halfChainEdgeSlots_disjoint_of_before
      first second hfirst hsecond hbefore
  have hconnectorSecond :=
    res.connector_disjoint_halfChainEdgeSlots_of_before
      first second hfirst hsecond hbefore
  unfold halfInvSqChainProduct
  rw [res.halfChainEdgeSlots_union_eq_threeWay_of_before
      first second hfirst hsecond hbefore,
    Finset.prod_union]
  · rw [Finset.prod_union hfirstConnector]
    simp only [Finset.prod_singleton]
  · rw [Finset.disjoint_union_left]
    exact ⟨hfirstSecond, hconnectorSecond⟩

/-! ## Canonical initial/terminal interval specializations -/

/-- The part of a half-carrier strictly before a cut vertex. -/
def halfCarrierBeforeCut
    (carrier : Finset (Fin m)) (cut : Fin m) : Finset (Fin m) :=
  carrier.filter fun i => i < cut

/-- The part of a half-carrier at or after a cut vertex. -/
def halfCarrierFromCut
    (carrier : Finset (Fin m)) (cut : Fin m) : Finset (Fin m) :=
  carrier.filter fun i => cut ≤ i

theorem halfCarrierBeforeCut_union_fromCut
    (carrier : Finset (Fin m)) (cut : Fin m) :
    halfCarrierBeforeCut carrier cut ∪
        halfCarrierFromCut carrier cut = carrier := by
  ext i
  simp only [halfCarrierBeforeCut, halfCarrierFromCut,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  · intro hi
    exact (lt_or_ge i cut).imp (fun h => ⟨hi, h⟩)
      (fun h => ⟨hi, h⟩)

theorem halfCarrierBefore_before_fromCut
    (carrier : Finset (Fin m)) (cut : Fin m) :
    HalfCarrierBefore
      (halfCarrierBeforeCut carrier cut)
      (halfCarrierFromCut carrier cut) := by
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact hi'.trans_le hj'

/-- Left-half orientation: the post-carrier is before the current head.
Its greatest source slot is the unique connector into the head. -/
theorem halfInvSqChainProduct_eq_post_connector_head
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (carrier : Finset (Fin m)) (cut : Fin m)
    (hpost : (halfCarrierBeforeCut carrier cut).Nonempty)
    (hhead : (halfCarrierFromCut carrier cut).Nonempty)
    (v : res.SurvivingCoordinate → T4) :
    res.halfInvSqChainProduct carrier
        ((halfCarrierBeforeCut_union_fromCut carrier cut).symm ▸
          hpost.mono Finset.subset_union_left) v =
      res.halfInvSqChainProduct
          (halfCarrierBeforeCut carrier cut) hpost v *
        invSqKer
          (res.edgeDisplacement 0 0 (res.reconstruct v)
            (r324InternalVertexEdgeSlot
              ((halfCarrierBeforeCut carrier cut).max' hpost))) *
        res.halfInvSqChainProduct
          (halfCarrierFromCut carrier cut) hhead v := by
  simpa only [halfCarrierBeforeCut_union_fromCut carrier cut] using
    res.halfInvSqChainProduct_union_eq_threeWay_of_before
      (halfCarrierBeforeCut carrier cut)
      (halfCarrierFromCut carrier cut) hpost hhead
      (halfCarrierBefore_before_fromCut carrier cut) v

/-- The part of a half-carrier through a terminal cut vertex. -/
def halfCarrierThroughCut
    (carrier : Finset (Fin m)) (cut : Fin m) : Finset (Fin m) :=
  carrier.filter fun i => i ≤ cut

/-- The part strictly after a terminal cut vertex. -/
def halfCarrierAfterCut
    (carrier : Finset (Fin m)) (cut : Fin m) : Finset (Fin m) :=
  carrier.filter fun i => cut < i

theorem halfCarrierThroughCut_union_afterCut
    (carrier : Finset (Fin m)) (cut : Fin m) :
    halfCarrierThroughCut carrier cut ∪
        halfCarrierAfterCut carrier cut = carrier := by
  ext i
  simp only [halfCarrierThroughCut, halfCarrierAfterCut,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
  · intro hi
    exact (le_or_gt i cut).imp (fun h => ⟨hi, h⟩)
      (fun h => ⟨hi, h⟩)

theorem halfCarrierThrough_before_afterCut
    (carrier : Finset (Fin m)) (cut : Fin m) :
    HalfCarrierBefore
      (halfCarrierThroughCut carrier cut)
      (halfCarrierAfterCut carrier cut) := by
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact hi'.trans_lt hj'

/-- Right-half orientation: the current head precedes the post-carrier.
The slot at the head maximum is the unique connector into the post path. -/
theorem halfInvSqChainProduct_eq_head_connector_post
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (carrier : Finset (Fin m)) (cut : Fin m)
    (hhead : (halfCarrierThroughCut carrier cut).Nonempty)
    (hpost : (halfCarrierAfterCut carrier cut).Nonempty)
    (v : res.SurvivingCoordinate → T4) :
    res.halfInvSqChainProduct carrier
        ((halfCarrierThroughCut_union_afterCut carrier cut).symm ▸
          hhead.mono Finset.subset_union_left) v =
      res.halfInvSqChainProduct
          (halfCarrierThroughCut carrier cut) hhead v *
        invSqKer
          (res.edgeDisplacement 0 0 (res.reconstruct v)
            (r324InternalVertexEdgeSlot
              ((halfCarrierThroughCut carrier cut).max' hhead))) *
        res.halfInvSqChainProduct
          (halfCarrierAfterCut carrier cut) hpost v := by
  simpa only [halfCarrierThroughCut_union_afterCut carrier cut] using
    res.halfInvSqChainProduct_union_eq_threeWay_of_before
      (halfCarrierThroughCut carrier cut)
      (halfCarrierAfterCut carrier cut) hhead hpost
      (halfCarrierThrough_before_afterCut carrier cut) v

/-- Full terminal left-half specialization, stated directly for the
paper's endpoint-erased chain. -/
theorem endpointErasedInvSqChainProduct_eq_post_connector_head
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) (cut : Fin m)
    (hpost :
      (halfCarrierBeforeCut res.state.active cut).Nonempty)
    (hhead :
      (halfCarrierFromCut res.state.active cut).Nonempty)
    (v : res.SurvivingCoordinate → T4) :
    res.endpointErasedInvSqChainProduct hactive v =
      res.halfInvSqChainProduct
          (halfCarrierBeforeCut res.state.active cut) hpost v *
        invSqKer
          (res.edgeDisplacement 0 0 (res.reconstruct v)
            (r324InternalVertexEdgeSlot
              ((halfCarrierBeforeCut res.state.active cut).max' hpost))) *
        res.halfInvSqChainProduct
          (halfCarrierFromCut res.state.active cut) hhead v := by
  rw [res.endpointErasedInvSqChainProduct_eq_halfInvSqChainProduct
    hactive v]
  exact res.halfInvSqChainProduct_eq_post_connector_head
    res.state.active cut hpost hhead v

/-- Full terminal right-half specialization. -/
theorem endpointErasedInvSqChainProduct_eq_head_connector_post
    (res : R324WithinHalfResidualPrefix ρ lam ε pairing)
    (hactive : res.state.active.Nonempty) (cut : Fin m)
    (hhead :
      (halfCarrierThroughCut res.state.active cut).Nonempty)
    (hpost :
      (halfCarrierAfterCut res.state.active cut).Nonempty)
    (v : res.SurvivingCoordinate → T4) :
    res.endpointErasedInvSqChainProduct hactive v =
      res.halfInvSqChainProduct
          (halfCarrierThroughCut res.state.active cut) hhead v *
        invSqKer
          (res.edgeDisplacement 0 0 (res.reconstruct v)
            (r324InternalVertexEdgeSlot
              ((halfCarrierThroughCut res.state.active cut).max' hhead))) *
        res.halfInvSqChainProduct
          (halfCarrierAfterCut res.state.active cut) hpost v := by
  rw [res.endpointErasedInvSqChainProduct_eq_halfInvSqChainProduct
    hactive v]
  exact res.halfInvSqChainProduct_eq_head_connector_post
    res.state.active cut hhead hpost v

end R324WithinHalfResidualPrefix

end

end Anderson4D
