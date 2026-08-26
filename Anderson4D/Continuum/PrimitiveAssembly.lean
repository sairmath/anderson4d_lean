import Anderson4D.Continuum.Discretization
import Anderson4D.HeppTree.PairedIncidence
import Anderson4D.HeppTree.VolumeEstimate
import Anderson4D.PermSum.Assembly

/-!
# Primitive-pairing assembly at lattice level

This file joins the exact finite objects which occur between paper
(5.5) and (5.17).

The first part is a genuine master bridge.  For a fixed cut `A`, the
primitive across-pairing lattice sum is covered by valid Hepp trees and then
reindexed by the *paired* finite incidence denominator from (5.6).  No
realization or positivity hypothesis is hidden in that statement.

The remaining lemmas expose three independent estimates used after this
reindexing:

* Proposition 5.6 cancels the paired incidence denominator against the
  marked-tree orbit factor;
* Proposition 5.7 controls the primitive compatible word sum;
* the root cluster diameter pays for the maximum in (5.5), and the numerical
  powerset lemma closes (5.17).

There are exactly two reindexing steps not supplied by the current library:

1. grouping a fixed paired incidence fiber by its unlabelled realized set and
   the induced multiplicity word (the paper's passage (5.8)--(5.11));
2. reindexing valid increasing branch markings by independent dyadic gaps
   before applying `sum_dyadicAssignmentWeight_le`.

They are not replaced here by assumptions equivalent to the desired bound.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

/-! ## Primitive across pairings and the actual lattice statistic -/

/-- Primitive pairings crossing the fixed paper cut `A | Aᶜ`. -/
def primitiveAcrossPairingFinset {m : ℕ} (A : Finset (Fin m)) :
    Finset (AcrossPairing A) :=
  Finset.univ.filter (IsPrimitiveAcross A)

@[simp]
theorem mem_primitiveAcrossPairingFinset
    {m : ℕ} {A : Finset (Fin m)} {κ : AcrossPairing A} :
    κ ∈ primitiveAcrossPairingFinset A ↔ IsPrimitiveAcross A κ := by
  simp [primitiveAcrossPairingFinset]

/-- The (5.5) lattice weight restricted to assignments copied along one
across pairing. -/
def pairedReductionStatistic (q : ℕ) (A : Finset (Fin (q + 1)))
    (κ : AcrossPairing A) (y : Fin (q + 1) → Z4) : ℝ :=
  if RespectsWord A y κ then reductionWeight q y else 0

theorem pairedReductionStatistic_nonneg
    (q : ℕ) (A : Finset (Fin (q + 1))) (κ : AcrossPairing A)
    (y : Fin (q + 1) → Z4) :
    0 ≤ pairedReductionStatistic q A κ y := by
  unfold pairedReductionStatistic
  split_ifs
  · exact reductionWeight_nonneg q y
  · exact le_rfl

/-- The copied-cell predicate produced by `Discretization` is exactly the
across-word predicate used by the pairing and incidence layers.  The two
definitions write the same equality in opposite orientations. -/
theorem respectsPairing_acrossToPartialPairing_iff
    {m : ℕ} (A : Finset (Fin m)) (κ : AcrossPairing A)
    (y : Fin m → Z4) :
    RespectsPairing (acrossToPartialPairing A κ) y ↔
      RespectsWord A y κ := by
  rw [← acrossToPartialPairing_respectsWord_iff A y κ]
  constructor
  · intro h i
    exact (h i).symm
  · intro h i
    exact (h i).symm

/-- The sum over the primitive pairings crossing a fixed cut.  This is the
finite lattice expression obtained from (5.5) before choosing a Hepp tree. -/
def primitiveAcrossLatticeSum
    (M q : ℕ) (A : Finset (Fin (q + 1))) : ℝ :=
  ∑ κ ∈ primitiveAcrossPairingFinset A,
    latticeChainSum M (q + 1) (pairedReductionStatistic q A κ)

/-- Primitive across pairings compatible with one lattice tuple.  Unlike the
generic word carrier, this definition does not impose a spurious finiteness
assumption on the lattice alphabet `Z4`. -/
def compatiblePrimitiveAcrossPairings
    {m : ℕ} (A : Finset (Fin m)) (y : Fin m → Z4) :
    Finset (AcrossPairing A) :=
  (primitiveAcrossPairingFinset A).filter fun κ =>
    RespectsWord A y κ

@[simp]
theorem mem_compatiblePrimitiveAcrossPairings
    {m : ℕ} {A : Finset (Fin m)} {y : Fin m → Z4}
    {κ : AcrossPairing A} :
    κ ∈ compatiblePrimitiveAcrossPairings A y ↔
      IsPrimitiveAcross A κ ∧ RespectsWord A y κ := by
  simp [compatiblePrimitiveAcrossPairings]

/-- Finite Fubini form of the primitive lattice sum: at each tuple the
pairing multiplicity is exactly the number of compatible primitive across
pairings. -/
theorem primitiveAcrossLatticeSum_eq_pairingCount
    (M q : ℕ) (A : Finset (Fin (q + 1))) :
    primitiveAcrossLatticeSum M q A =
      latticeChainSum M (q + 1) fun y =>
        ((compatiblePrimitiveAcrossPairings A y).card : ℝ) *
          reductionWeight q y := by
  unfold primitiveAcrossLatticeSum latticeChainSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  unfold pairedReductionStatistic compatiblePrimitiveAcrossPairings
  rw [← Finset.sum_filter]
  simp

private theorem two_le_valueFiber_of_respectsAcross
    {m : ℕ} (A : Finset (Fin m)) (y : Fin m → Z4)
    (κ : AcrossPairing A) (hκ : RespectsWord A y κ) (j : Fin m) :
    2 ≤ (Finset.univ.filter fun k => y k = y j).card := by
  classical
  by_cases hj : j ∈ A
  · let jA : ↥A := ⟨j, hj⟩
    let k : Fin m := (κ jA).1
    have hkAc : k ∈ Aᶜ := (κ jA).2
    have hk : k ∉ A := Finset.mem_compl.mp hkAc
    have hjk : j ≠ k := fun h => hk (h ▸ hj)
    have hyk : y k = y j := (hκ jA).symm
    apply Finset.one_lt_card.mpr
    exact ⟨j, by simp, k, by simp [hyk], hjk⟩
  · have hjAc : j ∈ Aᶜ := Finset.mem_compl.mpr hj
    let jAc : ↥(Aᶜ) := ⟨j, hjAc⟩
    let kA : ↥A := κ.symm jAc
    let k : Fin m := kA.1
    have hk : k ∈ A := kA.2
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    have hyk : y k = y j := by
      simpa [k, kA, jAc] using hκ kA
    apply Finset.one_lt_card.mpr
    exact ⟨j, by simp, k, by simp [hyk], hjk⟩

/-- A copied assignment lies in the repeated-value locus required by the
weak tree cover. -/
theorem mem_repeatedTuples_of_respectsAcross
    (M q : ℕ) (A : Finset (Fin (q + 1)))
    (κ : AcrossPairing A) (y : Fin (q + 1) → Z4)
    (hy : y ∈ rdec_boundedTuples M (q + 1))
    (hκ : RespectsWord A y κ) :
    y ∈ rdec_repeatedTuples M (q + 1) := by
  rw [rdec_mem_repeatedTuples]
  exact ⟨hy, two_le_valueFiber_of_respectsAcross A y κ hκ⟩

/-! ## A fixed tree slice has paired finite incidence data -/

/-- The fixed-tree assignments compatible with one across pairing. -/
def pairedTreeSlice
    (t : PlaneTree) (M q : ℕ) (A : Finset (Fin (q + 1)))
    (κ : AcrossPairing A) : Finset (Fin (q + 1) → Z4) :=
  (rdec_treeRealized t M (q + 1)).filter fun y =>
    RespectsWord A y κ

@[simp]
theorem mem_pairedTreeSlice
    {t : PlaneTree} {M q : ℕ} {A : Finset (Fin (q + 1))}
    {κ : AcrossPairing A} {y : Fin (q + 1) → Z4} :
    y ∈ pairedTreeSlice t M q A κ ↔
      y ∈ rdec_treeRealized t M (q + 1) ∧
        RespectsWord A y κ := by
  simp [pairedTreeSlice]

/-- A realization of a copied assignment by a fixed valid tree determines
an element of that tree's paired finite denominator carrier. -/
theorem exists_pairedData_realizes_of_mem_pairedTreeSlice
    {t : PlaneTree} (ht : t.isValid = true)
    {M q : ℕ} {A : Finset (Fin (q + 1))}
    {κ : AcrossPairing A} {y : Fin (q + 1) → Z4}
    (hy : y ∈ pairedTreeSlice t M q A κ) :
    ∃ d : PairedValidRealizationData t M (q + 1),
      PairedDataRealizes d y := by
  obtain ⟨hytree, hκ⟩ := mem_pairedTreeSlice.mp hy
  obtain ⟨_hybounded, Nm, mu, hreal⟩ :=
    rdec_mem_treeRealized.mp hytree
  obtain ⟨z, w, hadm, hw, hyz⟩ := hreal
  have hscale :
      ∀ v ∈ BranchNodes t,
        (scaleN Nm v : ℝ) ≤ 4 * (M : ℝ) :=
    fun _v hv => scaleN_le_four_mul_of_isAdmissible hadm hv
  have htotal :
      ∑ l : {v // v ∈ Leaves t}, mu.m l.1 = q + 1 :=
    multiplicities_total_of_realizesTuple
      ⟨z, w, hadm, hw, hyz⟩
  have hwκ : RespectsWord A w κ := by
    intro j
    apply hadm.inj
    rw [← hyz j.1, ← hyz (κ j).1]
    exact hκ j
  have heven :
      ∀ l : {v // v ∈ Leaves t}, Even (mu.m l.1) :=
    even_mult_of_compatibleAcrossPairing A
      (fun l : {v // v ∈ Leaves t} => mu.m l.1) hw κ hwκ
  let d₀ : RealizationData t M (q + 1) :=
    realizationDataOfBundles Nm mu hscale htotal
  have hd₀ : d₀.IsPairedValid :=
    realizationDataOfBundles_isPairedValid_of_treeValid
      ht Nm mu hscale htotal heven
  let d : PairedValidRealizationData t M (q + 1) := ⟨d₀, hd₀⟩
  refine ⟨d, ?_⟩
  have hNm :
      HeppMarking.EqOnBranch
        (d₀.toHeppMarking hd₀.1) Nm := by
    intro v hv
    change (branchDataOfScaleBound Nm hscale).raw v = Nm.Nexp v
    rw [BranchExponentData.raw_apply_of_mem _ hv]
    exact branchDataOfScaleBound_apply Nm hscale ⟨v, hv⟩
  have hmu :
      Multiplicities.EqOnLeaves
        (d₀.toMultiplicities hd₀.1) mu := by
    intro v hv
    change (leafDataOfTotal mu htotal).raw v = mu.m v
    rw [LeafMultiplicityData.raw_apply_of_mem _ hv]
    exact LeafMultiplicityData.ofMultiplicities_apply mu _ ⟨v, hv⟩
  exact (realizesTuple_congr_restricted hNm hmu).mpr
    ⟨z, w, hadm, hw, hyz⟩

/-- Exact fixed-tree form of paper (5.6), now on the actual (5.5) weight and
the even-multiplicity denominator. -/
theorem sum_pairedTreeSlice_eq_paired_incidence
    {t : PlaneTree} (ht : t.isValid = true)
    (M q : ℕ) (A : Finset (Fin (q + 1)))
    (κ : AcrossPairing A) :
    ∑ y ∈ rdec_treeRealized t M (q + 1),
        pairedReductionStatistic q A κ y =
      ∑ d ∈ pairedValidRealizationDataFinset t M (q + 1),
        ∑ y ∈ (pairedTreeSlice t M q A κ).filter
            (fun y => PairedDataRealizes d y),
          reductionWeight q y /
            pairedTreeSymDenom t M (q + 1) y := by
  have hleft :
      (∑ y ∈ rdec_treeRealized t M (q + 1),
          pairedReductionStatistic q A κ y) =
        ∑ y ∈ pairedTreeSlice t M q A κ,
          reductionWeight q y := by
    unfold pairedReductionStatistic pairedTreeSlice
    rw [Finset.sum_filter]
  rw [hleft]
  exact sum_eq_sum_paired_tree_incidence_div
    t M (q + 1) (pairedTreeSlice t M q A κ)
      (reductionWeight q)
      (fun y hy =>
        exists_pairedData_realizes_of_mem_pairedTreeSlice ht hy)

/-- The exact tree-and-incidence expression on the right of the master
bridge. -/
def primitiveTreeIncidenceSum
    (M q : ℕ) (A : Finset (Fin (q + 1))) : ℝ :=
  ∑ κ ∈ primitiveAcrossPairingFinset A,
    ∑ t ∈ rdec_treeEnum (q + 1),
      ∑ d ∈ pairedValidRealizationDataFinset t M (q + 1),
        ∑ y ∈ (pairedTreeSlice t M q A κ).filter
            (fun y => PairedDataRealizes d y),
          reductionWeight q y /
            pairedTreeSymDenom t M (q + 1) y

/-- **Master lattice/incidence bridge for (5.5)--(5.6).**

The proof uses the Hepp-tree cover only after showing from the fixed across
pairing that every contributing tuple has repeated values.  Each valid tree
slice is then reindexed by the exact paired denominator. -/
theorem primitiveAcrossLatticeSum_le_treeIncidence
    (M q : ℕ) (A : Finset (Fin (q + 1))) :
    primitiveAcrossLatticeSum M q A ≤
      primitiveTreeIncidenceSum M q A := by
  unfold primitiveAcrossLatticeSum primitiveTreeIncidenceSum
  apply Finset.sum_le_sum
  intro κ hκ
  have hcover :
      latticeChainSum M (q + 1) (pairedReductionStatistic q A κ) ≤
        ∑ t ∈ rdec_treeEnum (q + 1),
          ∑ y ∈ rdec_treeRealized t M (q + 1),
            pairedReductionStatistic q A κ y := by
    apply latticeChainSum_le_treeSum M (q + 1) (by omega)
    · exact pairedReductionStatistic_nonneg q A κ
    · intro y hybounded hynot
      unfold pairedReductionStatistic
      split_ifs with hrespects
      · exact False.elim
          (hynot
            (mem_repeatedTuples_of_respectsAcross
              M q A κ y hybounded hrespects))
      · rfl
  refine hcover.trans ?_
  apply Finset.sum_le_sum
  intro t htmem
  rw [sum_pairedTreeSlice_eq_paired_incidence
    (rdec_mem_treeEnum.mp htmem).1 M q A κ]

/-! ## Exact pointwise bridge from (5.5) to the Proposition 5.7 weight -/

/-- The maximum factor in the lattice summand (5.5). -/
def latticeTupleDiameterBracketSq
    {m : ℕ} (y : Fin (m + 1) → Z4) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (m + 1) =>
    Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (m + 1) =>
      latticeBracketSq (y i) (y j)))

theorem reductionWeight_eq_diameter_mul_heppChainWeight
    {t : PlaneTree} {m M : ℕ} {Nm : HeppMarking t}
    {mu : Multiplicities t} {y : Fin (m + 1) → Z4}
    (hreal : RealizesTuple t Nm mu M y) :
    ∃ (z : HeppLeaf t → Z4) (w : Fin (m + 1) → HeppLeaf t),
      IsAdmissible Nm M z ∧
      w ∈ validWords (leafMultiplicity mu) ∧
      reductionWeight m y =
        latticeTupleDiameterBracketSq y * heppChainWeight z w := by
  obtain ⟨z, w, hadm, hw, hy⟩ := hreal
  refine ⟨z, w, hadm, hw, ?_⟩
  unfold reductionWeight latticeTupleDiameterBracketSq heppChainWeight
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  · exact hy j.1
  · exact hy (adjacentSucc j)

/-- The root cluster diameter controls the maximum bracket factor in (5.5).
The displayed constant is polynomial in the leaf count and is subsequently
absorbed into the paper's exponential base. -/
theorem latticeTupleDiameterBracketSq_le_rootScale
    {t : PlaneTree} (ht : t.isValid = true)
    {m M : ℕ} {Nm : HeppMarking t} {mu : Multiplicities t}
    {y : Fin (m + 1) → Z4}
    (hreal : RealizesTuple t Nm mu M y) :
    latticeTupleDiameterBracketSq y ≤
      (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
        (scaleN Nm (rootV t) : ℝ) ^ 2 := by
  obtain ⟨z, w, hadm, _hw, hy⟩ := hreal
  rw [latticeTupleDiameterBracketSq]
  apply Finset.sup'_le
  intro i hi
  apply Finset.sup'_le
  intro j hj
  have hwi : w i ∈ leavesUnder (rootV t) := by
    rw [mem_leavesUnder]
    exact List.nil_prefix
  have hwj : w j ∈ leavesUnder (rootV t) := by
    rw [mem_leavesUnder]
    exact List.nil_prefix
  have hdist :
      znorm (z (w i) - z (w j)) ≤
        2 * (t.leafCount : ℝ) *
          (scaleN Nm (rootV t) : ℝ) := by
    exact
      (clusterDiameter_le_tildeScale hadm (rootV t) hwi hwj).trans
        (tildeScale_le_two_mul_leafCount_mul_scaleN ht Nm (rootV t))
  have hscale :
      (1 : ℝ) ≤ scaleN Nm (rootV t) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (scaleN_pos Nm (rootV t)))
  have hdist0 : 0 ≤ znorm (z (w i) - z (w j)) :=
    norm_nonneg _
  have hupper0 :
      0 ≤ 2 * (t.leafCount : ℝ) *
        (scaleN Nm (rootV t) : ℝ) := by
    positivity
  have hsq :
      znorm (z (w i) - z (w j)) ^ 2 ≤
        (2 * (t.leafCount : ℝ) *
          (scaleN Nm (rootV t) : ℝ)) ^ 2 := by
    nlinarith
  rw [hy i, hy j]
  unfold latticeBracketSq
  calc
    1 + znorm (z (w i) - z (w j)) ^ 2
        ≤ (scaleN Nm (rootV t) : ℝ) ^ 2 +
          (2 * (t.leafCount : ℝ) *
            (scaleN Nm (rootV t) : ℝ)) ^ 2 := by
      have hsquare :
          (1 : ℝ) ≤ (scaleN Nm (rootV t) : ℝ) ^ 2 := by
        nlinarith
      gcongr
    _ = (1 + (2 * (t.leafCount : ℝ)) ^ 2) *
          (scaleN Nm (rootV t) : ℝ) ^ 2 := by ring
    _ ≤ (1 + 2 * (t.leafCount : ℝ)) ^ 2 *
          (scaleN Nm (rootV t) : ℝ) ^ 2 := by
      have hr : 0 ≤ (t.leafCount : ℝ) := by positivity
      gcongr
      nlinarith

/-! ## P-5.7 and P-5.6 after the exact finite reindexing -/

/-- Proposition 5.7 bounds the primitive compatible across-pairing word sum
with the exact factorial quotient from (5.10). -/
theorem primitivePairedChainSum_le_permSumRHS
    {C : ℝ} (hC : PermSumEstimate C)
    (n M : ℕ) (t : PlaneTree) (Nm : HeppMarking t)
    (mu : Multiplicities t) (z : HeppLeaf t → Z4)
    (A : Finset (Fin (2 * n)))
    (hn : 2 ≤ n) (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (htotal : totalMultiplicity mu = 2 * n)
    (heven : ∀ l : HeppLeaf t, Even (leafMultiplicity mu l))
    (hadm : IsAdmissible Nm M z) :
    primitivePairedWordSum (leafMultiplicity mu) A
        (heppChainWeight z) ≤
      (∏ l : HeppLeaf t,
          (((leafMultiplicity mu l / 2).factorial : ℝ) /
            ((leafMultiplicity mu l).factorial : ℝ))) *
        permSumRHS C n t Nm mu := by
  let Q : ℝ :=
    ∏ l : HeppLeaf t,
      (((leafMultiplicity mu l / 2).factorial : ℝ) /
        ((leafMultiplicity mu l).factorial : ℝ))
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  calc
    primitivePairedWordSum (leafMultiplicity mu) A
          (heppChainWeight z) ≤
        Q *
          paperSumFiltered (leafMultiplicity mu)
            NoProperLeafBlock (heppChainWeight z) :=
      primitivePairedWordSum_le_paperSumFiltered
        (leafMultiplicity mu) A (heppChainWeight z)
        (heppChainWeight_nonneg z)
    _ = Q *
          paperSum (M := 2 * n) (leafMultiplicity mu)
            (primitiveChainWeight (m := 2 * n) z) := by
      rw [paperSum_primitiveChainWeight]
    _ ≤ Q * permSumRHS C n t Nm mu :=
      mul_le_mul_of_nonneg_left
        (hC.2 n M t Nm mu z hn ht hroot htotal heven hadm) hQ

/-- Proposition 5.6 cancels the paired incidence denominator and the marked
automorphism factor.  This is the precise algebra used between (5.12),
(5.14), and (5.16). -/
theorem realizedSetsPair_div_pairedDenom_le_volume
    {t : PlaneTree} (ht : t.isValid = true)
    {M m : ℕ} (N : BranchExponentData t (4 * M))
    (hN : N.IsValid) (mu : Multiplicities t)
    (y : Fin m → Z4)
    (hreal :
      RealizesTuple t (N.toHeppMarking hN) mu M y)
    (A : Finset (Fin m)) (κ : AcrossPairing A)
    (hκ : RespectsWord A y κ) (x₀ x₁ : Z4) :
    ((realizedSetsContainingPair N hN x₀ x₁).card : ℝ) /
        pairedTreeSymDenom t M m y ≤
      volumeEstimateFinalConstant ^ t.leafCount *
        branchScaleProduct (N.toHeppMarking hN) *
        latticeBracketInvFourth x₀ x₁ := by
  let p : ℝ :=
    Fintype.card
      (AutHeppMarked t (N.toHeppMarking hN))
  let a : ℝ := Fintype.card (Aut t)
  let d : ℝ := pairedTreeSymDenom t M m y
  let s : ℝ := (realizedSetsContainingPair N hN x₀ x₁).card
  let R : ℝ :=
    volumeEstimateFinalConstant ^ t.leafCount *
      branchScaleProduct (N.toHeppMarking hN) *
      latticeBracketInvFourth x₀ x₁
  have hp : 0 < p := by
    dsimp only [p]
    exact_mod_cast Fintype.card_pos
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast Fintype.card_pos
  have hdNat :
      0 < pairedTreeSymDenom t M m y := by
    apply pairedTreeSymDenom_pos_of_general A κ hκ
    exact treeSymDenom_pos_of_realizesTuple_autoTotal
      ht (N.toHeppMarking hN) mu
      (fun v hv => by
        obtain ⟨z, _w, hadm, _hw, _hy⟩ := hreal
        exact scaleN_le_four_mul_of_isAdmissible hadm hv)
      hreal
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast hdNat
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact mul_nonneg
      (mul_nonneg (by
        unfold volumeEstimateFinalConstant
        positivity)
        (branchScaleProduct_nonneg (N.toHeppMarking hN)))
      (latticeBracketInvFourth_nonneg x₀ x₁)
  have hdenNat :
      Fintype.card (Aut t) ≤
        pairedTreeSymDenom t M m y *
          Fintype.card
            (AutHeppMarked t (N.toHeppMarking hN)) :=
    card_aut_le_pairedTreeSymDenom_mul_card_autHeppMarked
      ht (N.toHeppMarking hN) mu hreal A κ hκ
  have hden : a ≤ d * p := by
    dsimp only [a, d, p]
    exact_mod_cast hdenNat
  have hvolumeRaw :=
    (volume_estimate ht N hN).2.2 x₀ x₁
  have hvolume : p * s ≤ R * a := by
    dsimp only [p, s]
    rw [← Nat.cast_mul]
    calc
      ((Fintype.card
          (AutHeppMarked t (N.toHeppMarking hN)) *
        (realizedSetsContainingPair N hN x₀ x₁).card : ℕ) : ℝ)
          ≤ volumeEstimateFinalConstant ^ t.leafCount *
              (t.autCard : ℝ) *
              branchScaleProduct (N.toHeppMarking hN) *
              latticeBracketInvFourth x₀ x₁ :=
        hvolumeRaw
      _ = R * a := by
        dsimp only [R, a]
        rw [card_aut_eq_autCard]
        ring
  have hcancel : s ≤ R * d := by
    have hcombined : p * s ≤ p * (R * d) := by
      calc
        p * s ≤ R * a := hvolume
        _ ≤ R * (d * p) :=
          mul_le_mul_of_nonneg_left hden hR
        _ = p * (R * d) := by ring
    exact le_of_mul_le_mul_left hcombined hp
  exact (div_le_iff₀ hd).2 hcancel

/-! ## The final (5.17) numerical ledger on an actual tree -/

/-- Actual non-root branch carrier used when independent dyadic gaps are
summed after the marking reindexing. -/
abbrev NonrootBranch (t : PlaneTree) :=
  {v // v ∈ nonrootBranches t}

/-- Tree-carrier specialization of the factorized dyadic summation.  Once a
valid increasing marking has been injected into independent gap data, every
free branch costs `L` and every other branch costs at most `2`. -/
theorem sum_nonrootBranch_dyadicAssignmentWeight_le
    (t : PlaneTree) (L : ℕ)
    (free : Finset (NonrootBranch t)) :
    (∑ a : NonrootBranch t → Fin L,
        dyadicAssignmentWeight L free a) ≤
      (L : ℝ) ^ free.card *
        2 ^ ((nonrootBranches t).card - free.card) := by
  simpa only [Fintype.card_coe] using
    sum_dyadicAssignmentWeight_le L free

/-- A valid tree with total multiplicity `2n` has at most `n-2` non-root
branch nodes. -/
theorem card_nonrootBranches_le_order_sub_two
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (n : ℕ)
    (htotal : totalMultiplicity mu = 2 * n) :
    (nonrootBranches t).card ≤ n - 2 := by
  have hbranch :
      (BranchNodes t).card ≤ t.leafCount - 1 := by
    calc
      (BranchNodes t).card ≤ branchExcess t := by
        rw [← sum_branchNodes_childCount_sub_one_eq_branchExcess,
          Finset.card_eq_sum_ones]
        exact Finset.sum_le_sum fun v hv => by
          have htwo : 2 ≤ childCount t v.1 := by
            simpa [BranchNodes] using hv
          omega
      _ = t.leafCount - 1 :=
        branchExcess_eq_leafCount_sub_one t ht
  have hnonroot :
      (nonrootBranches t).card + 1 =
        (BranchNodes t).card := by
    simpa [nonrootBranches] using
      Finset.card_erase_add_one hroot
  have hleaf :
      2 * t.leafCount ≤ totalMultiplicity mu := by
    rw [totalMultiplicity]
    calc
      2 * t.leafCount =
          ∑ _l : HeppLeaf t, 2 := by
        simp [card_Leaves_eq_leafCount, Nat.mul_comm]
      _ ≤ ∑ l : HeppLeaf t, leafMultiplicity mu l :=
        Finset.sum_le_sum fun l _ => mu.two_le l.1 l.2
  omega

/-- Tree-indexed form of the factorial/logarithm summation after (5.17). -/
theorem tree_sum_factorial_log_balance
    {t : PlaneTree} (ht : t.isValid = true)
    (hroot : rootV t ∈ BranchNodes t)
    (mu : Multiplicities t) (n L K : ℕ)
    (hn : 2 ≤ n)
    (htotal : totalMultiplicity mu = 2 * n)
    (hnL : n ≤ K * L) :
    (∑ W ∈ (nonrootBranches t).powerset,
        ((n - W.card).factorial : ℝ) *
          (L : ℝ) ^ min (W.card + 1) (n - 2)) ≤
      (16 * (K + 1) : ℝ) ^ n *
        (L : ℝ) ^ (n - 2) :=
  sum_factorial_log_balance (nonrootBranches t) n L K hn
    (card_nonrootBranches_le_order_sub_two
      ht hroot mu n htotal)
    hnL

end

end Anderson4D
