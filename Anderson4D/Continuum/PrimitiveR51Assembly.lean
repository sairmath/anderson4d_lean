import Anderson4D.Continuum.CellChainComplete
import Anderson4D.Continuum.PrimitiveSymmetry
import Anderson4D.Continuum.PrimitiveFinalAssembly

/-!
# Primitive §5.1 assembly on period-compatible cells

Paper: R-51 — §5.1 (5.1)–(5.5) — reduction of Prop 4.1 to the lattice bound

This file closes the geometric part of paper §5.1 which is specific to the
primitive kernel.  Canonical torus cells cannot be used directly in (5.3):
two neighbouring torus points may have floor labels on opposite sides of the
fundamental cube.  We therefore use `compatibleMeshSize` and unwrap the whole
linear chain by period-block translations.  The translations preserve the
torus centres and give the exact no-wrap hypotheses consumed by
`terminalCellLIntegral_exhaustive_order`.

The final finite reindexing from these unwrapped, endpoint-fixed paths to the
bounded-box sum consumed by `primitive_lattice_estimate` is intentionally not
asserted here.  In particular, this file contains no hypothesis equivalent to
Proposition 4.1 and does not declare `Proposition41`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-! ## Counting the smaller endpoints exactly once -/

/-- In a finite linear order, selecting the smaller endpoint of every
nontrivial two-cycle is in bijection with the unordered-pair carrier. -/
theorem card_pairSupport_filter_lt_eq_pairs
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (κ : PartialPairing ι) :
    (κ.pairSupport.filter fun i => i < κ i).card = κ.pairs.card := by
  classical
  refine Finset.card_bij (fun i _hi => s(i, κ i)) ?_ ?_ ?_
  · intro i hi
    exact PartialPairing.mem_pairs.mpr
      ⟨i, PartialPairing.mem_pairSupport.mp
        (Finset.mem_filter.mp hi).1, rfl⟩
  · intro i hi j hj hij
    rcases Sym2.eq_iff.mp hij with hsame | hswap
    · exact hsame.1
    · have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hback : κ i < i := by
        calc
          κ i = j := hswap.2
          _ < κ j := hj'
          _ = i := hswap.1.symm
      exact False.elim (lt_asymm hi' hback)
  · intro p hp
    obtain ⟨a, ha, hap⟩ := PartialPairing.mem_pairs.mp hp
    by_cases hlt : a < κ a
    · refine ⟨a, Finset.mem_filter.mpr
        ⟨PartialPairing.mem_pairSupport.mpr ha, hlt⟩, hap⟩
    · have hback : κ a < a := by
        have hle : κ a ≤ a := le_of_not_gt hlt
        exact lt_of_le_of_ne hle ha
      refine ⟨κ a, Finset.mem_filter.mpr
        ⟨κ.apply_mem_pairSupport
          (PartialPairing.mem_pairSupport.mpr ha), ?_⟩, ?_⟩
      · simpa only [κ.apply_apply] using hback
      · rw [κ.apply_apply, Sym2.eq_swap]
        exact hap

/-- A full pairing of `2n` positions has exactly `n` selected covariance
factors in the smaller-endpoint convention of `primitiveCovarianceProduct`.
-/
theorem card_primitiveCovarianceRepresentatives
    {n : ℕ} (κ : PartialPairing (Fin (2 * n)))
    (hfull : κ.IsFull) :
    (κ.pairSupport.filter fun i => i < κ i).card = n := by
  rw [card_pairSupport_filter_lt_eq_pairs]
  have hcard := κ.card_pairSupport
  rw [PartialPairing.isFull_iff_pairSupport_eq_univ.mp hfull] at hcard
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-! ## The exact covariance power ledger -/

/-- The uniform pointwise covariance bound has exactly `n` factors for a
full pairing on `2n` slots. -/
theorem exists_primitiveCovarianceProduct_uniform_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (κ : PartialPairing (Fin (2 * n))),
        κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
          ∀ x : Fin (2 * n) → T4,
            primitiveCovarianceProduct ρ ε n κ x ≤
              (ε⁻¹ ^ (dim : ℕ) * C) ^ n := by
  obtain ⟨C, hC, hη⟩ :=
    ρ.exists_pos_etaEpsT4_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro n κ hfull ε hε hε1 x
  unfold primitiveCovarianceProduct
  let s := κ.pairSupport.filter fun i => i < κ i
  calc
    (∏ i ∈ s, ρ.etaEpsT4 ε (x i - x (κ i))) ≤
        ∏ _i ∈ s, (ε⁻¹ ^ (dim : ℕ) * C) := by
      refine Finset.prod_le_prod
        (fun i _hi => SmoothCutoff.etaEpsT4_nonneg
          ρ ε (x i - x (κ i)))
        (fun i _hi => hη hε hε1 (x i - x (κ i)))
    _ = (ε⁻¹ ^ (dim : ℕ) * C) ^ s.card := by
      simp
    _ = (ε⁻¹ ^ (dim : ℕ) * C) ^ n := by
      rw [show s.card = n by
        exact card_primitiveCovarianceRepresentatives κ hfull]

/-! ## The inserted diameter is the lattice maximum in (5.5) -/

/-- Periodization can only decrease the distance between Euclidean cell
representatives. -/
theorem dist_latticeTorusCenter_le
    {δ : ℝ} (hδ : 0 ≤ δ) (a b : Z4) :
    dist (latticeTorusCenter δ a) (latticeTorusCenter δ b) ≤
      δ * znorm (a - b) := by
  calc
    dist (latticeTorusCenter δ a) (latticeTorusCenter δ b) ≤
        ‖cellRepresentative δ a - cellRepresentative δ b‖ := by
      exact dist_periodizeR4_le_norm_sub _ _
    _ = |δ| * znorm (a - b) :=
      norm_cellRepresentative_sub δ a b
    _ = δ * znorm (a - b) := by rw [abs_of_nonneg hδ]

/-- Every pairwise lattice bracket is below the tuple maximum used by the
fixed-data lattice assembly. -/
theorem latticeBracketSq_le_primitiveTupleDiameterBracketSq
    {m : ℕ} (hm : 0 < m) (y : Fin m → Z4) (i j : Fin m) :
    latticeBracketSq (y i) (y j) ≤
      primitiveTupleDiameterBracketSq hm y := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold primitiveTupleDiameterBracketSq
  exact
    (Finset.le_sup'
      (f := fun k : Fin m => latticeBracketSq (y i) (y k))
      (by simp : j ∈ (Finset.univ : Finset (Fin m)))).trans
      (Finset.le_sup'
        (f := fun k : Fin m =>
          Finset.univ.sup'
            ⟨⟨0, hm⟩, Finset.mem_univ _⟩
            (fun l : Fin m => latticeBracketSq (y k) (y l)))
        (by simp : i ∈ (Finset.univ : Finset (Fin m))))

/-- If every torus point lies in the radius-`Rδ` neighbourhood of its
lattice centre, its squared tuple diameter is controlled by the genuine
lattice maximum. -/
theorem torusTupleDiameterSq_le_compatibleCellMaximum
    {m : ℕ} [Nonempty (Fin m)] (hm : 0 < m) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R)
    (y : Fin m → Z4) (x : Fin m → T4)
    (hx : ∀ i, x i ∈ latticeCellNeighborhood δ R (y i)) :
    torusTupleDiameterSq x ≤
      8 * δ ^ 2 *
        (4 * R ^ 2 + primitiveTupleDiameterBracketSq hm y) := by
  unfold torusTupleDiameterSq
  apply Finset.sup'_le
  intro i _hi
  apply Finset.sup'_le
  intro j _hj
  let d : ℝ := znorm (y i - y j)
  let D : ℝ := primitiveTupleDiameterBracketSq hm y
  have hxi :
      dist (x i) (latticeTorusCenter δ (y i)) ≤ R * δ := by
    exact (show dist (x i) (latticeTorusCenter δ (y i)) < R * δ from
      hx i).le
  have hxj :
      dist (latticeTorusCenter δ (y j)) (x j) ≤ R * δ := by
    rw [dist_comm]
    exact (show dist (x j) (latticeTorusCenter δ (y j)) < R * δ from
      hx j).le
  have hc :
      dist (latticeTorusCenter δ (y i))
          (latticeTorusCenter δ (y j)) ≤ δ * d :=
    dist_latticeTorusCenter_le hδ.le (y i) (y j)
  have hdist :
      dist (x i) (x j) ≤ δ * (2 * R + d) := by
    calc
      dist (x i) (x j) ≤
          dist (x i) (latticeTorusCenter δ (y i)) +
            dist (latticeTorusCenter δ (y i))
              (latticeTorusCenter δ (y j)) +
            dist (latticeTorusCenter δ (y j)) (x j) :=
        dist_triangle4 _ _ _ _
      _ ≤ R * δ + δ * d + R * δ := by gcongr
      _ = δ * (2 * R + d) := by ring
  have hdist0 : 0 ≤ dist (x i) (x j) := dist_nonneg
  have hright0 : 0 ≤ δ * (2 * R + d) := by
    apply mul_nonneg hδ.le
    exact add_nonneg (by positivity) (znorm_nonneg _)
  have hsq :
      dist (x i) (x j) ^ 2 ≤
        (δ * (2 * R + d)) ^ 2 :=
    pow_le_pow_left₀ hdist0 hdist 2
  have htorus :
      torusDistSq (x i - x j) ≤
        4 * dist (x i) (x j) ^ 2 := by
    simpa only [dist_eq_norm] using
      torusDistSq_le_four_mul_sq_norm (x i - x j)
  have hd0 : 0 ≤ d := znorm_nonneg _
  have hD :
      1 + d ^ 2 ≤ D := by
    exact latticeBracketSq_le_primitiveTupleDiameterBracketSq
      hm y i j
  calc
    torusDistSq (x i - x j) ≤
        4 * dist (x i) (x j) ^ 2 := htorus
    _ ≤ 4 * (δ * (2 * R + d)) ^ 2 := by gcongr
    _ ≤ 8 * δ ^ 2 * (4 * R ^ 2 + D) := by
      nlinarith [sq_nonneg (2 * R - d), sq_nonneg δ]

/-- The paper insertion `ε² + max |xᵢ-xⱼ|²` is bounded by `δ²` times the
same tuple maximum appearing in `reductionWeight`.  The compatible-mesh
comparison `ε < 2δ` supplies the otherwise missing `ε²` term. -/
theorem primitiveInsertedFactor_le_cellMaximum
    {m : ℕ} [Nonempty (Fin m)] (hm : 0 < m) {ε R : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (y : Fin m → Z4) (x : Fin m → T4)
    (hx : ∀ i, x i ∈
      latticeCellNeighborhood (compatibleMeshSize ε) R (y i)) :
    ε ^ 2 + torusTupleDiameterSq x ≤
      (12 + 32 * R ^ 2) * compatibleMeshSize ε ^ 2 *
        primitiveTupleDiameterBracketSq hm y := by
  let δ := compatibleMeshSize ε
  let D := primitiveTupleDiameterBracketSq hm y
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hεδ : ε < 2 * δ :=
    lt_two_mul_compatibleMeshSize hε hε1
  have hεsq : ε ^ 2 ≤ 4 * δ ^ 2 := by
    nlinarith [sq_nonneg ε, sq_nonneg δ]
  have hdiam :
      torusTupleDiameterSq x ≤
        8 * δ ^ 2 * (4 * R ^ 2 + D) :=
    torusTupleDiameterSq_le_compatibleCellMaximum
      hm hδ hR y x hx
  have hDone :
      1 ≤ D := by
    have hpair :=
      latticeBracketSq_le_primitiveTupleDiameterBracketSq
        hm y (⟨0, hm⟩ : Fin m) ⟨0, hm⟩
    simpa [D, latticeBracketSq, znorm] using hpair
  have hD0 : 0 ≤ D := le_trans zero_le_one hDone
  dsimp only [δ, D] at *
  nlinarith [sq_nonneg (compatibleMeshSize ε),
    sq_nonneg R,
    mul_nonneg (sq_nonneg R) hD0,
    mul_nonneg (sq_nonneg (compatibleMeshSize ε)) hD0,
    mul_nonneg (sq_nonneg (compatibleMeshSize ε))
      (mul_nonneg (sq_nonneg R) hD0)]

/-! ## Pointwise identification of the primitive integrand -/

/-- The nonnegative inverse-square chain which dominates the arbitrary
admissible input functions in the primitive integrand. -/
def primitiveSingularChainProduct (n : ℕ) (hn : 1 ≤ n)
    (x : Fin (2 * n) → T4) : ℝ :=
  ∏ j : Fin (2 * n - 1),
    invSqKer
      (x (primitiveEdgeLeft n hn j) -
        x (primitiveEdgeRight n hn j))

theorem primitiveSingularChainProduct_nonneg
    (n : ℕ) (hn : 1 ≤ n) (x : Fin (2 * n) → T4) :
    0 ≤ primitiveSingularChainProduct n hn x := by
  unfold primitiveSingularChainProduct
  exact Finset.prod_nonneg fun j _ =>
    invSqKer_nonneg
      (x (primitiveEdgeLeft n hn j) -
        x (primitiveEdgeRight n hn j))

/-- The finite-index primitive chain is exactly the consecutive-edge product
on the complete ordered tuple.  This is the pointwise identification needed
before turning the product-cell integral into `terminalCellLIntegral`. -/
theorem primitiveSingularChainProduct_eq_listChainProduct
    (n : ℕ) (hn : 1 ≤ n) (x : Fin (2 * n) → T4) :
    primitiveSingularChainProduct n hn x =
      listChainProduct (fun a b : T4 => invSqKer (a - b))
        (List.ofFn x) := by
  let edge : T4 → T4 → ℝ := fun a b => invSqKer (a - b)
  let e : Fin (2 * n - 1) ≃ Fin (2 * n).pred :=
    Equiv.cast (by simp [Nat.pred_eq_sub_one])
  let g : Fin (2 * n).pred → ℝ := fun i =>
    edge (x (chainLeftIndex i)) (x (chainRightIndex i))
  calc
    primitiveSingularChainProduct n hn x =
        ∏ j : Fin (2 * n - 1), g (e j) := by
      unfold primitiveSingularChainProduct
      apply Finset.prod_congr rfl
      intro j _hj
      rfl
    _ = ∏ i : Fin (2 * n).pred, g i :=
      Equiv.prod_comp e g
    _ = indexedChainProduct edge x := by
      rfl
    _ = listChainProduct edge (List.ofFn x) :=
      (listChainProduct_ofFn edge x).symm

/-- The chain part of every admissible primitive input is pointwise dominated
by the exact nonnegative singular chain. -/
theorem abs_primitiveChainProduct_le_singular
    (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : IsAdmissiblePrimitiveInput n G)
    (x : Fin (2 * n) → T4) :
    |primitiveChainProduct n hn G x| ≤
      primitiveSingularChainProduct n hn x := by
  unfold primitiveChainProduct primitiveSingularChainProduct
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod
    (fun j _hj => abs_nonneg
      (G j (x (primitiveEdgeLeft n hn j) -
        x (primitiveEdgeRight n hn j))))
    (fun j _hj => hG.2 j
      (x (primitiveEdgeLeft n hn j) -
        x (primitiveEdgeRight n hn j)))

/-- Pointwise absolute-value reduction of the actual primitive integrand.
The covariance product stays in the statement (rather than being replaced by
a support predicate), and its sign is discharged from cutoff positivity. -/
theorem abs_primitiveIntegrand_le_singular_mul_covariance
    (ρ : SmoothCutoff) {ε : ℝ} (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ)
    (hG : IsAdmissiblePrimitiveInput n G)
    (κ : PartialPairing (Fin (2 * n)))
    (x : Fin (2 * n) → T4) :
    |primitiveIntegrand ρ ε n hn G κ x| ≤
      primitiveSingularChainProduct n hn x *
        primitiveCovarianceProduct ρ ε n κ x := by
  unfold primitiveIntegrand
  rw [abs_mul, abs_of_nonneg
    (primitiveCovarianceProduct_nonneg ρ ε n κ x)]
  exact mul_le_mul_of_nonneg_right
    (abs_primitiveChainProduct_le_singular n hn G hG x)
    (primitiveCovarianceProduct_nonneg ρ ε n κ x)

/-- Uniform version of the preceding pointwise reduction, with the exact
`n`-factor covariance power exposed. -/
theorem exists_abs_primitiveIntegrand_uniform_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))), κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ x : Fin (2 * n) → T4,
          |primitiveIntegrand ρ ε n hn G κ x| ≤
            (ε⁻¹ ^ (dim : ℕ) * C) ^ n *
              primitiveSingularChainProduct n hn x := by
  obtain ⟨C, hC, hcov⟩ :=
    exists_primitiveCovarianceProduct_uniform_bound ρ
  refine ⟨C, hC, ?_⟩
  intro n hn G hG κ hfull ε hε hε1 x
  calc
    |primitiveIntegrand ρ ε n hn G κ x| ≤
        primitiveSingularChainProduct n hn x *
          primitiveCovarianceProduct ρ ε n κ x :=
      abs_primitiveIntegrand_le_singular_mul_covariance
        ρ n hn G hG κ x
    _ ≤ primitiveSingularChainProduct n hn x *
          (ε⁻¹ ^ (dim : ℕ) * C) ^ n :=
      mul_le_mul_of_nonneg_left
        (hcov n κ hfull hε hε1 x)
        (primitiveSingularChainProduct_nonneg n hn x)
    _ = (ε⁻¹ ^ (dim : ℕ) * C) ^ n *
          primitiveSingularChainProduct n hn x := by ring

/-! ## The actual endpoint-fixed finite cell partition -/

/-- A finite measurable partition decomposes every nonnegative Lebesgue
integral exactly, without an integrability premise. -/
theorem FiniteMeasurableCells.lintegral_eq_sum
    {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]
    (P : FiniteMeasurableCells X ι) (μ : Measure X)
    (f : X → ENNReal) :
    (∫⁻ x, f x ∂μ) =
      ∑ i ∈ P.indices,
        ∫⁻ x in P.index ⁻¹' {i}, f x ∂μ := by
  calc
    (∫⁻ x, f x ∂μ) =
        ∫⁻ x in Set.univ, f x ∂μ := by simp
    _ = ∫⁻ x in ⋃ i ∈ P.indices,
          P.index ⁻¹' {i}, f x ∂μ := by
      rw [P.iUnion_fibers]
    _ = ∑ i ∈ P.indices,
          ∫⁻ x in P.index ⁻¹' {i}, f x ∂μ :=
      lintegral_biUnion_finset P.pairwiseDisjoint
        (fun i _hi => P.measurable_fiber i) f

/-- Endpoint assembly is measurable in all internal variables. -/
theorem measurable_primitiveAssemble
    (n : ℕ) (hn : 1 ≤ n) (z w : T4) :
    Measurable fun v : Fin (2 * n - 2) → T4 =>
      primitiveAssemble n hn z w v := by
  apply measurable_pi_lambda
  intro j
  let j' : Fin ((2 * n - 2) + 2) :=
    Fin.cast (by omega) j
  change Measurable fun v : Fin (2 * n - 2) → T4 =>
    assemble z w v j'
  unfold assemble
  by_cases h0 : j'.val = 0
  · simp only [h0, dite_true]
    exact measurable_const
  · simp only [h0, dite_false]
    by_cases hlast : j'.val = (2 * n - 2) + 1
    · simp only [hlast, dite_true]
      exact measurable_const
    · simp only [hlast, dite_false]
      exact measurable_pi_apply _

/-- The genuine finite partition of the `2n-2` integration variables:
assemble the fixed endpoints first, then floor only the chosen endpoint of
each pair and copy its label to its mate. -/
def primitivePairedInternalCells
    (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    (δ : ℝ) (hδ : 0 < δ) (z w : T4) :
    FiniteMeasurableCells
      (Fin (2 * n - 2) → T4) (Fin (2 * n) → Z4) where
  indices := Fintype.piFinset fun _ : Fin (2 * n) => torusGrid δ
  index := fun v =>
    pairedCellAssignment κ δ (primitiveAssemble n hn z w v)
  range_subset := fun v =>
    pairedCellAssignment_mem_piFinset κ hδ
      (primitiveAssemble n hn z w v)
  measurable_fiber := fun y =>
    ((measurable_pairedCellAssignment κ δ).comp
      (measurable_primitiveAssemble n hn z w))
      (measurableSet_singleton y)

/-- Exact finite cell decomposition of the actual endpoint-fixed primitive
integration domain. -/
theorem primitive_lintegral_eq_sum_pairedInternalCells
    (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n)))
    {δ : ℝ} (hδ : 0 < δ) (z w : T4)
    (f : (Fin (2 * n - 2) → T4) → ENNReal) :
    (∫⁻ v, f v
        ∂(Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure)) =
      ∑ y ∈ Fintype.piFinset
          (fun _ : Fin (2 * n) => torusGrid δ),
        ∫⁻ v in
            (fun u =>
              pairedCellAssignment κ δ
                (primitiveAssemble n hn z w u)) ⁻¹' {y},
          f v
          ∂(Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) := by
  exact (primitivePairedInternalCells n hn κ δ hδ z w).lintegral_eq_sum
    (Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) f

/-! ## Covariance support puts every variable in its copied cell -/

/-- For a full pairing, nonvanishing of every selected covariance factor
puts both members of every pair in the common compatible-mesh neighbourhood
indexed by the smaller endpoint.  The conclusion is stated for every slot,
not merely for the selected half of the pairs. -/
theorem primitiveCoordinates_mem_pairedCompatibleCells
    {m : ℕ} (ρ : SmoothCutoff) (κ : PartialPairing (Fin m))
    (hfull : κ.IsFull) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : Fin m → T4)
    (hη : ∀ i, i < κ i →
      ρ.etaEpsT4 ε (x i - x (κ i)) ≠ 0) :
    ∀ i,
      x i ∈ latticeCellNeighborhood (compatibleMeshSize ε)
        (1 + 4 * ρ.radius)
        (pairedCellAssignment κ (compatibleMeshSize ε) x i) := by
  intro i
  by_cases hi : i ≤ κ i
  · have hne : i ≠ κ i := (hfull i).symm
    have hilt : i < κ i := lt_of_le_of_ne hi hne
    have hp :=
      ρ.etaEpsT4_pair_mem_compatibleCellNeighborhood
        hε hε1 (x i) (x (κ i)) (hη i hilt)
    have hanchor : pairingAnchor κ i = i := by
      simp [pairingAnchor, hi]
    simpa only [pairedCellAssignment, hanchor] using hp.1
  · have hki : κ i < i := lt_of_not_ge hi
    have hηki :
        ρ.etaEpsT4 ε (x (κ i) - x i) ≠ 0 := by
      simpa only [κ.apply_apply] using hη (κ i) (by
        simpa only [κ.apply_apply] using hki)
    have hp :=
      ρ.etaEpsT4_pair_mem_compatibleCellNeighborhood
        hε hε1 (x (κ i)) (x i) hηki
    have hanchor : pairingAnchor κ i = κ i := by
      simp [pairingAnchor, hi]
    simpa only [pairedCellAssignment, hanchor] using hp.2

/-- Nonvanishing of the actual covariance product supplies the hypotheses of
`primitiveCoordinates_mem_pairedCompatibleCells`. -/
theorem primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
    {n : ℕ} (ρ : SmoothCutoff)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : Fin (2 * n) → T4)
    (hcov : primitiveCovarianceProduct ρ ε n κ x ≠ 0) :
    ∀ i,
      x i ∈ latticeCellNeighborhood (compatibleMeshSize ε)
        (1 + 4 * ρ.radius)
        (pairedCellAssignment κ (compatibleMeshSize ε) x i) := by
  apply primitiveCoordinates_mem_pairedCompatibleCells
    ρ κ hfull hε hε1 x
  intro i hi
  unfold primitiveCovarianceProduct at hcov
  exact Finset.prod_ne_zero_iff.mp hcov i (by
    simp only [Finset.mem_filter]
    exact ⟨PartialPairing.mem_pairSupport.mpr (hfull i), hi⟩)

/-! ## The primitive linear cell path -/

/-- Cell labels of the `2n-2` integrated vertices, in paper order. -/
def primitiveInternalCellLabels (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : List Z4 :=
  List.ofFn fun i : Fin (2 * n - 2) =>
    y (primitiveInternalIdx n hn i)

@[simp] theorem primitiveInternalCellLabels_length
    (n : ℕ) (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    (primitiveInternalCellLabels n hn y).length = 2 * n - 2 := by
  simp [primitiveInternalCellLabels]

/-- The first cell label in the primitive chain. -/
def primitiveFirstCell (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : Z4 :=
  y ⟨0, by omega⟩

/-- The last cell label in the primitive chain. -/
def primitiveLastCell (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : Z4 :=
  y (primitiveLast n hn)

/-- Original ordered cell-label list before period-block unwrapping. -/
def primitiveOriginalCellList (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : List Z4 :=
  primitiveFirstCell n hn y ::
    (primitiveInternalCellLabels n hn y ++
      [primitiveLastCell n hn y])

@[simp] theorem primitiveOriginalCellList_eq_ofFn
    (n : ℕ) (hn : 1 ≤ n) (y : Fin (2 * n) → Z4) :
    primitiveOriginalCellList n hn y = List.ofFn y := by
  let y' : Fin ((2 * n - 1) + 1) → Z4 := fun i =>
    y (Fin.cast (by omega) i)
  have hy : List.ofFn y' = List.ofFn y := by
    apply List.ext_getElem
    · simp
      omega
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn]
      dsimp only [y']
      congr
  rw [← hy]
  unfold primitiveOriginalCellList primitiveFirstCell
  rw [List.ofFn_succ]
  congr 1
  let t' : Fin ((2 * n - 2) + 1) → Z4 := fun i =>
    y' (Fin.cast (by omega) i).succ
  have ht :
      List.ofFn (fun i => y' i.succ) = List.ofFn t' := by
    apply List.ext_getElem
    · simp
      omega
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn]
      dsimp only [t']
      congr
  rw [ht, List.ofFn_succ', List.concat_eq_append]
  have hint :
      primitiveInternalCellLabels n hn y =
        List.ofFn (fun i => t' i.castSucc) := by
    unfold primitiveInternalCellLabels
    apply congrArg List.ofFn
    funext i
    unfold primitiveInternalIdx
    dsimp only [t', y']
    apply congrArg y
    apply Fin.ext
    rfl
  have hlast :
      primitiveLastCell n hn y = t' (Fin.last (2 * n - 2)) := by
    unfold primitiveLastCell primitiveLast
    dsimp only [t', y']
    apply congrArg y
    apply Fin.ext
    simp
    omega
  rw [hint, hlast]

/-- Centre-preserving no-wrap representatives of all internal labels. -/
def primitiveUnwrappedInternal (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : List Z4 :=
  unwrapLatticePath (compatibleCellCount ε)
    (primitiveFirstCell n hn y) (primitiveInternalCellLabels n hn y)

/-- A centre-preserving no-wrap representative of the fixed terminal label,
chosen relative to the end of the already unwrapped internal path. -/
def primitiveUnwrappedLast (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : Z4 :=
  nearestPeriodTranslate (compatibleCellCount ε)
    (walkEnd (primitiveFirstCell n hn y)
      (primitiveUnwrappedInternal ε n hn y))
    (primitiveLastCell n hn y)

/-- Complete list of centre-preserving representatives, including both fixed
endpoints. -/
def primitiveUnwrappedCellList (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : List Z4 :=
  primitiveFirstCell n hn y ::
    (primitiveUnwrappedInternal ε n hn y ++
      [primitiveUnwrappedLast ε n hn y])

@[simp] theorem primitiveUnwrappedCellList_length
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    (primitiveUnwrappedCellList ε n hn y).length = 2 * n := by
  simp [primitiveUnwrappedCellList, primitiveUnwrappedInternal,
    primitiveInternalCellLabels]
  omega

/-- Finite-tuple form of `primitiveUnwrappedCellList`, used to feed the
existing `reductionWeight`/Hepp-tree interfaces. -/
def primitiveUnwrappedCellTuple (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : Fin (2 * n) → Z4 :=
  fun i =>
    (primitiveUnwrappedCellList ε n hn y).get
      (Fin.cast (primitiveUnwrappedCellList_length ε n hn y).symm i)

@[simp] theorem primitiveUnwrappedCellTuple_ofFn
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    List.ofFn (primitiveUnwrappedCellTuple ε n hn y) =
      primitiveUnwrappedCellList ε n hn y := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn]
    unfold primitiveUnwrappedCellTuple
    congr

/-- Arithmetic cast of the complete unwrapped tuple to the literal
`Fin ((2n-1)+1)` carrier expected by `reductionWeight (2n-1)`. -/
def primitiveUnwrappedReductionTuple (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) : Fin ((2 * n - 1) + 1) → Z4 :=
  fun i =>
    primitiveUnwrappedCellTuple ε n hn y
      (Fin.cast (by omega) i)

@[simp] theorem primitiveUnwrappedReductionTuple_ofFn
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    List.ofFn (primitiveUnwrappedReductionTuple ε n hn y) =
      primitiveUnwrappedCellList ε n hn y := by
  rw [← primitiveUnwrappedCellTuple_ofFn ε n hn y]
  apply List.ext_getElem
  · simp
    omega
  · intro i hi₁ hi₂
    simp only [List.getElem_ofFn]
    unfold primitiveUnwrappedReductionTuple
    congr

@[simp] theorem primitiveUnwrappedInternal_length
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    (primitiveUnwrappedInternal ε n hn y).length = 2 * n - 2 := by
  simp [primitiveUnwrappedInternal]

/-- Unwrapping does not change any internal torus centre. -/
theorem primitiveUnwrappedInternal_map_centers
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    (primitiveUnwrappedInternal ε n hn y).map
        (latticeTorusCenter (compatibleMeshSize ε)) =
      (primitiveInternalCellLabels n hn y).map
        (latticeTorusCenter (compatibleMeshSize ε)) := by
  exact unwrapLatticePath_map_centers
    (compatibleMesh_isPeriodCompatible hε)
    (primitiveFirstCell n hn y) (primitiveInternalCellLabels n hn y)

/-- Unwrapping does not change the terminal torus centre. -/
theorem primitiveUnwrappedLast_center
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    latticeTorusCenter (compatibleMeshSize ε)
        (primitiveUnwrappedLast ε n hn y) =
      latticeTorusCenter (compatibleMeshSize ε)
        (primitiveLastCell n hn y) := by
  exact latticeTorusCenter_nearestPeriodTranslate
    (compatibleMesh_isPeriodCompatible hε)
    (walkEnd (primitiveFirstCell n hn y)
      (primitiveUnwrappedInternal ε n hn y))
    (primitiveLastCell n hn y)

/-- All centres of the complete unwrapped list agree, position by position,
with the original canonical labels. -/
theorem primitiveUnwrappedCellList_map_centers
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    (primitiveUnwrappedCellList ε n hn y).map
        (latticeTorusCenter (compatibleMeshSize ε)) =
      (primitiveOriginalCellList n hn y).map
        (latticeTorusCenter (compatibleMeshSize ε)) := by
  unfold primitiveUnwrappedCellList primitiveOriginalCellList
  simp only [List.map_cons, List.map_append]
  rw [primitiveUnwrappedInternal_map_centers hε n hn y,
    primitiveUnwrappedLast_center hε n hn y]

/-- Function-indexed centre preservation, suitable for transporting a whole
tuple of cell-membership hypotheses to the unwrapped realization. -/
theorem primitiveUnwrappedCellTuple_center
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) (i : Fin (2 * n)) :
    latticeTorusCenter (compatibleMeshSize ε)
        (primitiveUnwrappedCellTuple ε n hn y i) =
      latticeTorusCenter (compatibleMeshSize ε) (y i) := by
  let c := latticeTorusCenter (compatibleMeshSize ε)
  have hlist :
      List.ofFn (fun j : Fin (2 * n) =>
        c (primitiveUnwrappedCellTuple ε n hn y j)) =
        List.ofFn (fun j : Fin (2 * n) => c (y j)) := by
    calc
      List.ofFn (fun j : Fin (2 * n) =>
          c (primitiveUnwrappedCellTuple ε n hn y j)) =
          (List.ofFn
            (primitiveUnwrappedCellTuple ε n hn y)).map c := by
        exact List.ofFn_comp' _ _
      _ = (primitiveUnwrappedCellList ε n hn y).map c := by
        rw [primitiveUnwrappedCellTuple_ofFn]
      _ = (primitiveOriginalCellList n hn y).map c :=
        primitiveUnwrappedCellList_map_centers hε n hn y
      _ = (List.ofFn y).map c := by
        rw [primitiveOriginalCellList_eq_ofFn]
      _ = List.ofFn (fun j : Fin (2 * n) => c (y j)) := by
        exact (List.ofFn_comp' y c).symm
  exact congrFun (List.ofFn_injective hlist) i

/-- Whole-tuple transport of compatible-cell membership to the unwrapped
labels. -/
theorem primitiveCoordinates_mem_unwrappedCells
    {ε R : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) (x : Fin (2 * n) → T4)
    (hx : ∀ i, x i ∈
      latticeCellNeighborhood (compatibleMeshSize ε) R (y i)) :
    ∀ i, x i ∈
      latticeCellNeighborhood (compatibleMeshSize ε) R
        (primitiveUnwrappedCellTuple ε n hn y i) := by
  intro i
  unfold latticeCellNeighborhood at hx ⊢
  rw [primitiveUnwrappedCellTuple_center hε n hn y i]
  exact hx i

/-- Inserted-factor specialization to the centre-preserving unwrapped tuple.
This is the exact `δ² · max⟨uᵢ-uⱼ⟩²` factor which multiplies the terminal
chain estimate before the covariance ledger is applied. -/
theorem primitiveInsertedFactor_le_unwrappedCellMaximum
    {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) (x : Fin (2 * n) → T4)
    (hx : ∀ i, x i ∈
      latticeCellNeighborhood (compatibleMeshSize ε) R (y i)) :
    letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
    ε ^ 2 + torusTupleDiameterSq x ≤
      (12 + 32 * R ^ 2) * compatibleMeshSize ε ^ 2 *
        primitiveTupleDiameterBracketSq (by omega)
          (primitiveUnwrappedCellTuple ε n hn y) := by
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  exact primitiveInsertedFactor_le_cellMaximum
    (by omega) hε hε1 hR
    (primitiveUnwrappedCellTuple ε n hn y) x
    (primitiveCoordinates_mem_unwrappedCells
      hε n hn y x hx)

/-- The complete unwrapped primitive path satisfies the exact no-wrap
predicate, including its final edge. -/
theorem primitiveUnwrappedPath_noWrap
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    LatticeCellPathNoWrap (compatibleMeshSize ε)
      (primitiveFirstCell n hn y)
      (primitiveUnwrappedInternal ε n hn y ++
        [primitiveUnwrappedLast ε n hn y]) := by
  rw [latticeCellPathNoWrap_append_iff]
  constructor
  · exact unwrapLatticePath_noWrap
      (compatibleMesh_isPeriodCompatible hε)
      (primitiveFirstCell n hn y) (primitiveInternalCellLabels n hn y)
  · simpa only [unwrapLatticePath, primitiveUnwrappedLast] using
      unwrapLatticePath_noWrap
        (compatibleMesh_isPeriodCompatible hε)
        (walkEnd (primitiveFirstCell n hn y)
          (primitiveUnwrappedInternal ε n hn y))
        [primitiveLastCell n hn y]

/-! ## Exact identification with the existing lattice weight -/

/-- Generic list form of the paper's `AdjacentIndex` product. -/
theorem adjacentProduct_eq_listChainProduct
    {α R : Type*} [CommMonoid R] {m : ℕ}
    (edge : α → α → R) (w : Fin m → α) :
    (∏ j : AdjacentIndex m,
        edge (w j.1) (w (adjacentSucc j))) =
      listChainProduct edge (List.ofFn w) := by
  let e := adjacentIndexEquiv m
  let g : Fin m.pred → R := fun i =>
    edge (w (chainLeftIndex i)) (w (chainRightIndex i))
  calc
    (∏ j : AdjacentIndex m,
        edge (w j.1) (w (adjacentSucc j))) =
        ∏ j : AdjacentIndex m, g (e j) := by
      apply Finset.prod_congr rfl
      intro j _hj
      rfl
    _ = ∏ i : Fin m.pred, g i := Equiv.prod_comp e g
    _ = indexedChainProduct edge w := by rfl
    _ = listChainProduct edge (List.ofFn w) :=
      (listChainProduct_ofFn edge w).symm

/-- A complete list with fixed endpoints carries exactly the terminal lattice
path weight used by the exhaustive cell estimate. -/
theorem listChainProduct_lattice_eq_terminal
    (y e : Z4) (ys : List Z4) :
    listChainProduct latticeEdgeWeight (y :: (ys ++ [e])) =
      latticeTerminalPathWeight y e ys := by
  induction ys generalizing y with
  | nil =>
      simp [listChainProduct, latticeTerminalPathWeight]
  | cons a as ih =>
      simp only [List.cons_append, listChainProduct,
        latticeTerminalPathWeight]
      rw [ih]

/-- **Pointwise (5.5) identification.**

The lattice weight produced by the actual compatible-mesh, no-wrap primitive
cell path is literally `reductionWeight`: its adjacent product is the same
`latticeTerminalPathWeight` that occurs in
`primitiveTerminalCellLIntegral_exhaustive_order`, and its maximum is the
existing `primitiveTupleDiameterBracketSq`. -/
theorem primitiveUnwrappedReductionWeight_eq
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    reductionWeight (2 * n - 1)
        (primitiveUnwrappedReductionTuple ε n hn y) =
      primitiveTupleDiameterBracketSq (by omega)
          (primitiveUnwrappedReductionTuple ε n hn y) *
        latticeTerminalPathWeight
          (primitiveFirstCell n hn y)
          (primitiveUnwrappedLast ε n hn y)
          (primitiveUnwrappedInternal ε n hn y) := by
  unfold reductionWeight primitiveTupleDiameterBracketSq
  congr 1
  rw [adjacentProduct_eq_listChainProduct,
    primitiveUnwrappedReductionTuple_ofFn]
  exact listChainProduct_lattice_eq_terminal
    (primitiveFirstCell n hn y)
    (primitiveUnwrappedLast ε n hn y)
    (primitiveUnwrappedInternal ε n hn y)

/-! ## The exhaustive per-cell estimate on the actual primitive path -/

/-- Membership in a lattice-cell neighbourhood depends only on its torus
centre.  This is the small but essential boundary-safe transport used for the
last unwrapped label. -/
theorem mem_latticeCellNeighborhood_iff_of_center_eq
    {δ R : ℝ} {a b : Z4} (h :
      latticeTorusCenter δ a = latticeTorusCenter δ b)
    (x : T4) :
    x ∈ latticeCellNeighborhood δ R a ↔
      x ∈ latticeCellNeighborhood δ R b := by
  unfold latticeCellNeighborhood
  rw [h]

/-- **Primitive-cell form of paper (5.3)--(5.4).**

For `n ≥ 2`, the genuine internal primitive chain, with the two prescribed
endpoints left unintegrated, is bounded on every compatible-mesh cell by the
paper scale `δ^(4n-6)` and the linear lattice weight of centre-preserving
no-wrap representatives.  No integrability hypothesis and no periodic
boundary assumption is present: the left side is the actual Tonelli
`terminalCellLIntegral`, and unwrapping proves the latter internally. -/
theorem primitiveTerminalCellLIntegral_exhaustive_order :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (_hε : 0 < ε)
        (R : ℝ) (_hR : 0 < R)
        (y : Fin (2 * n) → Z4) (x z : T4),
        x ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
          (primitiveFirstCell n (by omega) y) →
        z ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
          (primitiveLastCell n (by omega) y) →
        terminalCellLIntegral
            (R * compatibleMeshSize ε) x z
            ((primitiveInternalCellLabels n (by omega) y).map
              (latticeTorusCenter (compatibleMeshSize ε))) ≤
          ENNReal.ofReal
              ((C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R *
                compatibleMeshSize ε ^ (4 * n - 6) *
                latticeTerminalPathWeight
                  (primitiveFirstCell n (by omega) y)
                  (primitiveUnwrappedLast ε n (by omega) y)
                  (primitiveUnwrappedInternal ε n (by omega) y)) +
            ENNReal.ofReal
              ((C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                compatibleMeshSize ε ^ (4 * n - 6) *
                latticeTerminalPathWeight
                  (primitiveFirstCell n (by omega) y)
                  (primitiveUnwrappedLast ε n (by omega) y)
                  (primitiveUnwrappedInternal ε n (by omega) y)) := by
  obtain ⟨C, hC, hchain⟩ :=
    terminalCellLIntegral_exhaustive_order
  refine ⟨C, hC, ?_⟩
  intro n hn ε hε R hR y x z hx hz
  let hn1 : 1 ≤ n := by omega
  let δ := compatibleMeshSize ε
  let ys := primitiveUnwrappedInternal ε n hn1 y
  let e := primitiveUnwrappedLast ε n hn1 y
  have hδ : 0 < δ := compatibleMeshSize_pos hε
  have hlen : ys.length = 2 * n - 2 := by
    simp [ys]
  have hz' :
      z ∈ latticeCellNeighborhood δ R e := by
    exact
      (mem_latticeCellNeighborhood_iff_of_center_eq
        (primitiveUnwrappedLast_center hε n hn1 y).symm z).mp hz
  have hbound :=
    hchain n hn δ R hδ hR
      (primitiveFirstCell n hn1 y) e ys x z hlen hx hz'
      (primitiveUnwrappedPath_noWrap hε n hn1 y)
  rw [primitiveUnwrappedInternal_map_centers hε n hn1 y] at hbound
  exact hbound

/-- Exact exponent cancellation in the inserted per-cell ledger. -/
theorem compatibleCell_inserted_power_ledger
    (δ : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    δ ^ 2 * δ ^ (4 * n - 6) = δ ^ (4 * n - 4) := by
  rw [← pow_add]
  congr 1
  omega

/-- **Inserted primitive-cell form of (5.2)--(5.5).**

This theorem multiplies the exhaustive `2n-2`-variable terminal-chain
integral by the actual insertion
`ε² + max |xᵢ-xⱼ|²`.  Centre preservation transports all cell memberships
to the unwrapped tuple; the insertion is absorbed by its actual maximum;
and the scale ledger closes to `δ^(4n-4)`.  The remaining linear product
together with that maximum is identified with `reductionWeight` by
`primitiveUnwrappedReductionWeight_eq`. -/
theorem primitiveInsertedTerminalCellLIntegral_exhaustive_order :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) {ε : ℝ}
        (_hε : 0 < ε) (_hε1 : ε ≤ 1)
        (R : ℝ) (_hR : 0 < R)
        (y : Fin (2 * n) → Z4) (x : Fin (2 * n) → T4),
        (∀ i, x i ∈
          latticeCellNeighborhood (compatibleMeshSize ε) R (y i)) →
        letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
        let δ := compatibleMeshSize ε
        let u := primitiveUnwrappedCellTuple ε n (by omega) y
        let D := primitiveTupleDiameterBracketSq (by omega) u
        let W := latticeTerminalPathWeight
          (primitiveFirstCell n (by omega) y)
          (primitiveUnwrappedLast ε n (by omega) y)
          (primitiveUnwrappedInternal ε n (by omega) y)
        ENNReal.ofReal (ε ^ 2 + torusTupleDiameterSq x) *
            terminalCellLIntegral (R * δ)
              (x ⟨0, by omega⟩) (x (primitiveLast n (by omega)))
              ((primitiveInternalCellLabels n (by omega) y).map
                (latticeTorusCenter δ)) ≤
          ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
            ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                δ ^ (4 * n - 4) * W) := by
  obtain ⟨C, hC, hcell⟩ :=
    primitiveTerminalCellLIntegral_exhaustive_order
  refine ⟨C, hC, ?_⟩
  intro n hn ε hε hε1 R hR y x hx
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let hn1 : 1 ≤ n := by omega
  let δ := compatibleMeshSize ε
  let u := primitiveUnwrappedCellTuple ε n hn1 y
  let D := primitiveTupleDiameterBracketSq (by omega) u
  let W := latticeTerminalPathWeight
    (primitiveFirstCell n hn1 y)
    (primitiveUnwrappedLast ε n hn1 y)
    (primitiveUnwrappedInternal ε n hn1 y)
  let F := ε ^ 2 + torusTupleDiameterSq x
  let A :=
    (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 6) * W
  let B :=
    (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 6) * W
  have hx0 :
      x ⟨0, by omega⟩ ∈
        latticeCellNeighborhood δ R
          (primitiveFirstCell n hn1 y) := by
    simpa only [δ, primitiveFirstCell] using
      hx (⟨0, by omega⟩ : Fin (2 * n))
  have hxlast :
      x (primitiveLast n hn1) ∈
        latticeCellNeighborhood δ R
          (primitiveLastCell n hn1 y) := by
    simpa only [δ, primitiveLastCell] using
      hx (primitiveLast n hn1)
  have hchain :=
    hcell n hn hε R hR y
      (x ⟨0, by omega⟩) (x (primitiveLast n hn1))
      hx0 hxlast
  change terminalCellLIntegral (R * δ)
      (x ⟨0, by omega⟩) (x (primitiveLast n hn1))
      ((primitiveInternalCellLabels n hn1 y).map
        (latticeTorusCenter δ)) ≤
      ENNReal.ofReal A + ENNReal.ofReal B at hchain
  have hF :
      F ≤ (12 + 32 * R ^ 2) * δ ^ 2 * D := by
    exact primitiveInsertedFactor_le_unwrappedCellMaximum
      hε hε1 hR n hn1 y x hx
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact add_nonneg (sq_nonneg ε) (torusTupleDiameterSq_nonneg x)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) u
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact latticeTerminalPathWeight_nonneg _ _ _
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    exact (compatibleMeshSize_pos hε).le
  have hfarBase : 0 ≤ C * (R ^ 2 + R ^ 4) :=
    mul_nonneg hC.le
      (add_nonneg (sq_nonneg R) (by positivity))
  have hnearBase : 0 ≤ C * cellChainRadiusFactor R :=
    mul_nonneg hC.le (cellChainRadiusFactor_pos R).le
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hfarBase _)
          (terminalRadiusFactor_pos hR).le)
        (pow_nonneg hδ0 _))
      hW0
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hnearBase _) (pow_nonneg hδ0 _))
      hW0
  have hFA :
      F * A ≤
        (12 + 32 * R ^ 2) * D *
          (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) * W := by
    calc
      F * A ≤ ((12 + 32 * R ^ 2) * δ ^ 2 * D) * A :=
        mul_le_mul_of_nonneg_right hF hA0
      _ = (12 + 32 * R ^ 2) * D *
          (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) * W := by
        dsimp only [A]
        rw [← compatibleCell_inserted_power_ledger δ n hn]
        ring
  have hFB :
      F * B ≤
        (12 + 32 * R ^ 2) * D *
          (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) * W := by
    calc
      F * B ≤ ((12 + 32 * R ^ 2) * δ ^ 2 * D) * B :=
        mul_le_mul_of_nonneg_right hF hB0
      _ = (12 + 32 * R ^ 2) * D *
          (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) * W := by
        dsimp only [B]
        rw [← compatibleCell_inserted_power_ledger δ n hn]
        ring
  calc
    ENNReal.ofReal F *
        terminalCellLIntegral (R * δ)
          (x ⟨0, by omega⟩) (x (primitiveLast n hn1))
          ((primitiveInternalCellLabels n hn1 y).map
            (latticeTorusCenter δ)) ≤
        ENNReal.ofReal F *
          (ENNReal.ofReal A + ENNReal.ofReal B) :=
      by
        simpa only [mul_comm] using
          mul_le_mul_right hchain (ENNReal.ofReal F)
    _ = ENNReal.ofReal (F * A) + ENNReal.ofReal (F * B) := by
      rw [mul_add, ENNReal.ofReal_mul hF0,
        ENNReal.ofReal_mul hF0]
    _ ≤
        ENNReal.ofReal
            ((12 + 32 * R ^ 2) * D *
              (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
          ENNReal.ofReal
            ((12 + 32 * R ^ 2) * D *
              (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4) * W) :=
      add_le_add (ENNReal.ofReal_le_ofReal hFA)
        (ENNReal.ofReal_le_ofReal hFB)

/-- Covariance-supported specialization of
`primitiveTerminalCellLIntegral_exhaustive_order`.

Here the cell tuple is not arbitrary: it is exactly
`pairedCellAssignment κ δ x` for a primitive full pairing and an actual
tuple on which the covariance product is nonzero.  Thus the endpoint-cell
hypotheses of the analytic estimate are discharged from `ηε` support. -/
theorem primitiveCovarianceSupportedCellChain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : SmoothCutoff) (n : ℕ) (hn : 2 ≤ n)
        {ε : ℝ} (_hε : 0 < ε) (_hε1 : ε ≤ 1)
        (κ : PartialPairing (Fin (2 * n)))
        (_hκ : κ ∈ primitiveFullPairings n)
        (x : Fin (2 * n) → T4),
        primitiveCovarianceProduct ρ ε n κ x ≠ 0 →
        let δ := compatibleMeshSize ε
        let R := 1 + 4 * ρ.radius
        let y := pairedCellAssignment κ δ x
        terminalCellLIntegral (R * δ)
            (x ⟨0, by omega⟩) (x (primitiveLast n (by omega)))
            ((primitiveInternalCellLabels n (by omega) y).map
              (latticeTorusCenter δ)) ≤
          ENNReal.ofReal
              ((C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R * δ ^ (4 * n - 6) *
                latticeTerminalPathWeight
                  (primitiveFirstCell n (by omega) y)
                  (primitiveUnwrappedLast ε n (by omega) y)
                  (primitiveUnwrappedInternal ε n (by omega) y)) +
            ENNReal.ofReal
              ((C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                δ ^ (4 * n - 6) *
                latticeTerminalPathWeight
                  (primitiveFirstCell n (by omega) y)
                  (primitiveUnwrappedLast ε n (by omega) y)
                  (primitiveUnwrappedInternal ε n (by omega) y)) := by
  obtain ⟨C, hC, hcell⟩ :=
    primitiveTerminalCellLIntegral_exhaustive_order
  refine ⟨C, hC, ?_⟩
  intro ρ n hn ε hε hε1 κ hκ x hcov
  let hn1 : 1 ≤ n := by omega
  let δ := compatibleMeshSize ε
  let R := 1 + 4 * ρ.radius
  let y := pairedCellAssignment κ δ x
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  have hmem :=
    primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
      ρ κ hfull hε hε1 x hcov
  have hx0 :
      x ⟨0, by omega⟩ ∈
        latticeCellNeighborhood δ R
          (primitiveFirstCell n hn1 y) := by
    simpa only [δ, R, y, primitiveFirstCell] using
      hmem (⟨0, by omega⟩ : Fin (2 * n))
  have hxlast :
      x (primitiveLast n hn1) ∈
        latticeCellNeighborhood δ R
          (primitiveLastCell n hn1 y) := by
    simpa only [δ, R, y, primitiveLastCell] using
      hmem (primitiveLast n hn1)
  exact hcell n hn hε R (by
      dsimp only [R]
      nlinarith [ρ.radius_pos]) y
    (x ⟨0, by omega⟩) (x (primitiveLast n hn1)) hx0 hxlast

/-- Fully support-discharged inserted cell estimate.  This is the final
continuous statement before summing compatible cell fibers and applying the
finite lattice/Hepp-tree estimate. -/
theorem primitiveCovarianceSupportedInsertedCellChain :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : SmoothCutoff) (n : ℕ) (hn : 2 ≤ n)
        {ε : ℝ} (_hε : 0 < ε) (_hε1 : ε ≤ 1)
        (κ : PartialPairing (Fin (2 * n)))
        (_hκ : κ ∈ primitiveFullPairings n)
        (x : Fin (2 * n) → T4),
        primitiveCovarianceProduct ρ ε n κ x ≠ 0 →
        letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
        let δ := compatibleMeshSize ε
        let R := 1 + 4 * ρ.radius
        let y := pairedCellAssignment κ δ x
        let u := primitiveUnwrappedCellTuple ε n (by omega) y
        let D := primitiveTupleDiameterBracketSq (by omega) u
        let W := latticeTerminalPathWeight
          (primitiveFirstCell n (by omega) y)
          (primitiveUnwrappedLast ε n (by omega) y)
          (primitiveUnwrappedInternal ε n (by omega) y)
        ENNReal.ofReal (ε ^ 2 + torusTupleDiameterSq x) *
            terminalCellLIntegral (R * δ)
              (x ⟨0, by omega⟩) (x (primitiveLast n (by omega)))
              ((primitiveInternalCellLabels n (by omega) y).map
                (latticeTorusCenter δ)) ≤
          ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
            ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                δ ^ (4 * n - 4) * W) := by
  obtain ⟨C, hC, hinsert⟩ :=
    primitiveInsertedTerminalCellLIntegral_exhaustive_order
  refine ⟨C, hC, ?_⟩
  intro ρ n hn ε hε hε1 κ hκ x hcov
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let δ := compatibleMeshSize ε
  let R := 1 + 4 * ρ.radius
  let y := pairedCellAssignment κ δ x
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  have hmem :=
    primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
      ρ κ hfull hε hε1 x hcov
  have hmem' :
      ∀ i, x i ∈ latticeCellNeighborhood δ R (y i) := by
    simpa only [δ, R, y] using hmem
  exact hinsert n hn hε hε1 R (by
      dsimp only [R]
      nlinarith [ρ.radius_pos]) y x hmem'

/-! ## Exact Tonelli identification on a product cell -/

/-- The `ℝ≥0∞` chain density with fixed endpoints.  Keeping this recursive
form separate from `terminalCellLIntegral` makes the finite-product Tonelli
identity transparent: the latter is precisely the iterated integral of this
density. -/
def terminalSingularProduct (x z : T4) : List T4 → ℝ≥0∞
  | [] => ENNReal.ofReal (invSqKer (x - z))
  | u :: us =>
      ENNReal.ofReal (invSqKer (x - u)) *
        terminalSingularProduct u z us

theorem terminalSingularProduct_eq_ofReal_listChainProduct
    (x z : T4) (us : List T4) :
    terminalSingularProduct x z us =
      ENNReal.ofReal
        (listChainProduct (fun a b : T4 => invSqKer (a - b))
          (x :: (us ++ [z]))) := by
  induction us generalizing x with
  | nil =>
      simp only [List.nil_append, terminalSingularProduct,
        listChainProduct, mul_one]
  | cons u us ih =>
      simp only [List.cons_append, terminalSingularProduct,
        listChainProduct, ih]
      rw [ENNReal.ofReal_mul (invSqKer_nonneg (x - u))]

/-- Joint measurability of the terminal chain density in its left endpoint
and all integrated vertices. -/
theorem measurable_terminalSingularProduct_ofFn (m : ℕ) (z : T4) :
    Measurable fun p : T4 × (Fin m → T4) =>
      terminalSingularProduct p.1 z (List.ofFn p.2) := by
  induction m with
  | zero =>
      simp only [List.ofFn_zero, terminalSingularProduct]
      have h : Measurable fun p : T4 × (Fin 0 → T4) =>
          ENNReal.ofReal (invSqKer (p.1 - z)) :=
        (measurable_invSqKer.comp
          (measurable_fst.sub measurable_const)).ennreal_ofReal
      exact h
  | succ m ih =>
      have hhead : Measurable fun p : T4 × (Fin (m + 1) → T4) =>
          ENNReal.ofReal (invSqKer (p.1 - p.2 0)) :=
        (measurable_invSqKer.comp
          (measurable_fst.sub
            ((measurable_pi_apply 0).comp measurable_snd))).ennreal_ofReal
      have htail : Measurable fun p : T4 × (Fin (m + 1) → T4) =>
          terminalSingularProduct (p.2 0) z
            (List.ofFn fun i : Fin m => p.2 i.succ) :=
        by
          have hmap : Measurable fun p : T4 × (Fin (m + 1) → T4) =>
              (p.2 0, fun i : Fin m => p.2 i.succ) :=
            ((measurable_pi_apply 0).comp measurable_snd).prodMk
              (measurable_pi_lambda _ fun (i : Fin m) =>
                (measurable_pi_apply i.succ).comp measurable_snd)
          convert ih.comp hmap using 1
          ext p
          rfl
      simp only [List.ofFn_succ, terminalSingularProduct]
      convert hhead.mul htail using 1
      ext p
      rfl

/-- Integrating the exact chain density against the product of the restricted
cell measures is definitionally the recursive `terminalCellLIntegral`.
This is the missing Tonelli bridge between the endpoint-fixed product-cell
partition and the exhaustive cell-chain theorem. -/
theorem terminalSingularProduct_lintegral_pi_restrict
    (r : ℝ) (x z : T4) (m : ℕ) (c : Fin m → T4) :
    (∫⁻ v : Fin m → T4,
        terminalSingularProduct x z (List.ofFn v)
      ∂Measure.pi fun i =>
        paperMeasure.restrict (Metric.ball (c i) r)) =
      terminalCellLIntegral r x z (List.ofFn c) := by
  induction m generalizing x with
  | zero =>
      simp only [List.ofFn_zero, terminalSingularProduct,
        terminalCellLIntegral]
      rw [Measure.pi_of_empty _ 0, lintegral_dirac]
  | succ m ih =>
      let μ : Fin (m + 1) → Measure T4 :=
        fun i => paperMeasure.restrict (Metric.ball (c i) r)
      let e :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => T4) 0
      have hmp := measurePreserving_piFinSuccAbove μ 0
      have hkernel : Measurable fun u : T4 =>
          ENNReal.ofReal (invSqKer (x - u)) :=
        (measurable_invSqKer.comp
          (measurable_const.sub measurable_id)).ennreal_ofReal
      have htail : Measurable fun p : T4 × (Fin m → T4) =>
          terminalSingularProduct p.1 z (List.ofFn p.2) :=
        measurable_terminalSingularProduct_ofFn m z
      have hprod : Measurable fun p : T4 × (Fin m → T4) =>
          ENNReal.ofReal (invSqKer (x - p.1)) *
            terminalSingularProduct p.1 z (List.ofFn p.2) :=
        (hkernel.comp measurable_fst).mul htail
      calc
        (∫⁻ v : Fin (m + 1) → T4,
            terminalSingularProduct x z (List.ofFn v)
          ∂Measure.pi fun i =>
            paperMeasure.restrict (Metric.ball (c i) r)) =
            ∫⁻ p : T4 × (Fin m → T4),
              ENNReal.ofReal (invSqKer (x - p.1)) *
                terminalSingularProduct p.1 z (List.ofFn p.2)
              ∂((paperMeasure.restrict (Metric.ball (c 0) r)).prod
                (Measure.pi fun i : Fin m =>
                  paperMeasure.restrict (Metric.ball (c i.succ) r))) := by
          change (∫⁻ v : Fin (m + 1) → T4,
              terminalSingularProduct x z (List.ofFn v) ∂Measure.pi μ) = _
          rw [← hmp.symm.lintegral_comp_emb
            e.symm.measurableEmbedding
            (fun v : Fin (m + 1) → T4 =>
              terminalSingularProduct x z (List.ofFn v))]
          simp only [μ,
            MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.insertNth_zero,
            Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq,
            List.ofFn_cons, terminalSingularProduct]
        _ = ∫⁻ u in Metric.ball (c 0) r,
              ∫⁻ v : Fin m → T4,
                ENNReal.ofReal (invSqKer (x - u)) *
                  terminalSingularProduct u z (List.ofFn v)
                ∂Measure.pi fun i : Fin m =>
                  paperMeasure.restrict (Metric.ball (c i.succ) r)
              ∂paperMeasure := by
          rw [lintegral_prod _ hprod.aemeasurable]
        _ = ∫⁻ u in Metric.ball (c 0) r,
              ENNReal.ofReal (invSqKer (x - u)) *
                terminalCellLIntegral r u z
                  (List.ofFn fun i : Fin m => c i.succ)
              ∂paperMeasure := by
          apply lintegral_congr
          intro u
          have ht : Measurable fun v : Fin m → T4 =>
              terminalSingularProduct u z (List.ofFn v) := by
            convert (measurable_terminalSingularProduct_ofFn m z).comp
              (measurable_const.prodMk measurable_id) using 1
            ext v
            rfl
          rw [lintegral_const_mul
            (ENNReal.ofReal (invSqKer (x - u))) ht]
          rw [ih u (fun i : Fin m => c i.succ)]
        _ = terminalCellLIntegral r x z (List.ofFn c) := by
          rw [List.ofFn_succ, terminalCellLIntegral.eq_def]

/-- Set-integral form of
`terminalSingularProduct_lintegral_pi_restrict`. -/
theorem terminalSingularProduct_setLIntegral_productCell
    (r : ℝ) (x z : T4) (m : ℕ) (c : Fin m → T4) :
    (∫⁻ v : Fin m → T4 in
        Set.univ.pi (fun i => Metric.ball (c i) r),
        terminalSingularProduct x z (List.ofFn v)
      ∂Measure.pi fun _ : Fin m => paperMeasure) =
      terminalCellLIntegral r x z (List.ofFn c) := by
  rw [Measure.restrict_pi_pi]
  exact terminalSingularProduct_lintegral_pi_restrict r x z m c

/-- Generic finite-list decomposition into first endpoint, internal slots,
and last endpoint, using the same slot maps as `primitiveAssemble`. -/
theorem list_ofFn_eq_primitive_endpoints
    {α : Type*} (n : ℕ) (hn : 1 ≤ n)
    (x : Fin (2 * n) → α) :
    List.ofFn x =
      x ⟨0, by omega⟩ ::
        (List.ofFn (fun i : Fin (2 * n - 2) =>
          x (primitiveInternalIdx n hn i)) ++
        [x (primitiveLast n hn)]) := by
  let x' : Fin ((2 * n - 1) + 1) → α := fun i =>
    x (Fin.cast (by omega) i)
  have hx : List.ofFn x' = List.ofFn x := by
    apply List.ext_getElem
    · simp
      omega
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn]
      dsimp only [x']
      congr
  rw [← hx, List.ofFn_succ]
  congr 1
  let t' : Fin ((2 * n - 2) + 1) → α := fun i =>
    x' (Fin.cast (by omega) i).succ
  have ht :
      List.ofFn (fun i => x' i.succ) = List.ofFn t' := by
    apply List.ext_getElem
    · simp
      omega
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn]
      dsimp only [t']
      congr
  rw [ht, List.ofFn_succ', List.concat_eq_append]
  have hint :
      (fun i : Fin (2 * n - 2) =>
          x (primitiveInternalIdx n hn i)) =
        fun i => t' i.castSucc := by
    funext i
    unfold primitiveInternalIdx
    dsimp only [t', x']
    apply congrArg x
    apply Fin.ext
    rfl
  have hlast :
      x (primitiveLast n hn) = t' (Fin.last (2 * n - 2)) := by
    unfold primitiveLast
    dsimp only [t', x']
    apply congrArg x
    apply Fin.ext
    simp
    omega
  rw [hint, hlast]

/-- The complete ordered tuple assembled from fixed endpoints has exactly the
paper list `z, v₁, …, v_{2n-2}, w`. -/
theorem list_ofFn_primitiveAssemble
    (n : ℕ) (hn : 1 ≤ n) (z w : T4)
    (v : Fin (2 * n - 2) → T4) :
    List.ofFn (primitiveAssemble n hn z w v) =
      z :: (List.ofFn v ++ [w]) := by
  rw [list_ofFn_eq_primitive_endpoints n hn]
  simp only [primitiveAssemble_zero, primitiveAssemble_internal,
    primitiveAssemble_last]

/-- Pointwise, the actual primitive singular product after endpoint assembly
is the fixed-endpoint chain density integrated by
`terminalCellLIntegral`. -/
theorem primitiveSingularChainProduct_assemble_eq_terminal
    (n : ℕ) (hn : 1 ≤ n) (z w : T4)
    (v : Fin (2 * n - 2) → T4) :
    ENNReal.ofReal
        (primitiveSingularChainProduct n hn
          (primitiveAssemble n hn z w v)) =
      terminalSingularProduct z w (List.ofFn v) := by
  rw [primitiveSingularChainProduct_eq_listChainProduct,
    list_ofFn_primitiveAssemble,
    terminalSingularProduct_eq_ofReal_listChainProduct]

/-- Exact product-cell integral of the singular majorant after endpoint
assembly. -/
theorem primitiveSingularChainProduct_setLIntegral_productCell
    (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (z w : T4)
    (c : Fin (2 * n - 2) → T4) :
    (∫⁻ v : Fin (2 * n - 2) → T4 in
        Set.univ.pi (fun i => Metric.ball (c i) r),
        ENNReal.ofReal
          (primitiveSingularChainProduct n hn
            (primitiveAssemble n hn z w v))
      ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) =
      terminalCellLIntegral r z w (List.ofFn c) := by
  calc
    _ = ∫⁻ v : Fin (2 * n - 2) → T4 in
          Set.univ.pi (fun i => Metric.ball (c i) r),
          terminalSingularProduct z w (List.ofFn v)
        ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure := by
      apply lintegral_congr
      intro v
      exact primitiveSingularChainProduct_assemble_eq_terminal
        n hn z w v
    _ = terminalCellLIntegral r z w (List.ofFn c) :=
      terminalSingularProduct_setLIntegral_productCell
        r z w (2 * n - 2) c

/-- On a genuine paired-assignment fiber, nonvanishing covariance places
every internal integration variable in the corresponding enlarged product
cell. -/
theorem primitiveInternal_mem_productCell_of_fiber_covariance_ne_zero
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) (hfull : κ.IsFull)
    (z w : T4) (y : Fin (2 * n) → Z4)
    (v : Fin (2 * n - 2) → T4)
    (hfiber :
      pairedCellAssignment κ (compatibleMeshSize ε)
        (primitiveAssemble n hn z w v) = y)
    (hcov :
      primitiveCovarianceProduct ρ ε n κ
        (primitiveAssemble n hn z w v) ≠ 0) :
    v ∈ Set.univ.pi (fun i =>
      Metric.ball
        (latticeTorusCenter (compatibleMeshSize ε)
          (y (primitiveInternalIdx n hn i)))
        ((1 + 4 * ρ.radius) * compatibleMeshSize ε)) := by
  intro i _hi
  have hmem :=
    primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
      ρ κ hfull hε hε1 (primitiveAssemble n hn z w v) hcov
      (primitiveInternalIdx n hn i)
  rw [hfiber] at hmem
  simpa only [latticeCellNeighborhood,
    primitiveAssemble_internal] using hmem

/-- Pointwise majorization on a genuine paired cell fiber.  The actual
covariance product supplies support, the actual insertion is absorbed by the
unwrapped lattice maximum, and the only remaining variable-dependent factor
is the exact terminal singular chain density. -/
theorem exists_primitiveInsertedIntegrand_fiber_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))), κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4)
          (v : Fin (2 * n - 2) → T4),
          pairedCellAssignment κ (compatibleMeshSize ε)
              (primitiveAssemble n hn z w v) = y →
          primitiveCovarianceProduct ρ ε n κ
              (primitiveAssemble n hn z w v) ≠ 0 →
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let u := primitiveUnwrappedCellTuple ε n hn y
          let D := primitiveTupleDiameterBracketSq (by omega) u
          ENNReal.ofReal
              |primitiveInsertedIntegrand ρ ε n hn G κ
                (primitiveAssemble n hn z w v)| ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * C) ^ n *
                  ((12 + 32 * R ^ 2) * δ ^ 2 * D)) *
              terminalSingularProduct z w (List.ofFn v) := by
  obtain ⟨C, hC, hub⟩ :=
    exists_abs_primitiveIntegrand_uniform_bound ρ
  refine ⟨C, hC, ?_⟩
  intro n hn G hG κ hfull ε hε hε1 z w y v hfiber hcov
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let x := primitiveAssemble n hn z w v
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let u := primitiveUnwrappedCellTuple ε n hn y
  let D := primitiveTupleDiameterBracketSq (by omega) u
  let Q := (ε⁻¹ ^ (dim : ℕ) * C) ^ n
  let B := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let F := ε ^ 2 + torusTupleDiameterSq x
  let S := primitiveSingularChainProduct n hn x
  have hmem :=
    primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
      ρ κ hfull hε hε1 x hcov
  have hx : ∀ i, x i ∈ latticeCellNeighborhood δ R (y i) := by
    rw [hfiber] at hmem
    simpa only [x, δ, R] using hmem
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact add_nonneg (sq_nonneg ε) (torusTupleDiameterSq_nonneg x)
  have hF : F ≤ B := by
    dsimp only [F, B, D, u, δ, R]
    exact primitiveInsertedFactor_le_unwrappedCellMaximum
      hε hε1 hR n hn y x hx
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact pow_nonneg
      (mul_nonneg
        (pow_nonneg (inv_nonneg.mpr hε.le) _)
        hC.le) _
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) u
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg
        (by positivity : 0 ≤ 12 + 32 * R ^ 2)
        (sq_nonneg δ))
      hD0
  have hS0 : 0 ≤ S := by
    exact primitiveSingularChainProduct_nonneg n hn x
  have hint :
      |primitiveIntegrand ρ ε n hn G κ x| ≤ Q * S := by
    simpa only [Q, S] using
      hub n hn G hG κ hfull hε hε1 x
  have hreal :
      |primitiveInsertedIntegrand ρ ε n hn G κ x| ≤
        (Q * B) * S := by
    calc
      |primitiveInsertedIntegrand ρ ε n hn G κ x| =
          F * |primitiveIntegrand ρ ε n hn G κ x| := by
        unfold primitiveInsertedIntegrand
        rw [abs_mul, abs_of_nonneg hF0]
      _ ≤ F * (Q * S) :=
        mul_le_mul_of_nonneg_left hint hF0
      _ ≤ B * (Q * S) :=
        mul_le_mul_of_nonneg_right hF
          (mul_nonneg hQ0 hS0)
      _ = (Q * B) * S := by ring
  calc
    ENNReal.ofReal
        |primitiveInsertedIntegrand ρ ε n hn G κ x| ≤
        ENNReal.ofReal ((Q * B) * S) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Q * B) *
          terminalSingularProduct z w (List.ofFn v) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hQ0 hB0)]
      change ENNReal.ofReal (Q * B) *
          ENNReal.ofReal
            (primitiveSingularChainProduct n hn
              (primitiveAssemble n hn z w v)) =
        ENNReal.ofReal (Q * B) *
          terminalSingularProduct z w (List.ofFn v)
      rw [primitiveSingularChainProduct_assemble_eq_terminal]

/-- Integrated form of the genuine fiber bound.  The domain on the left is
the actual fiber of `pairedCellAssignment`; the product cell on the right is
not assumed but follows pointwise from nonvanishing of the covariance.
Tonelli then turns its singular-chain integral into
`terminalCellLIntegral`. -/
theorem exists_primitiveInsertedIntegrand_fiber_lintegral_bound
    (ρ : SmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 1 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))), κ.IsFull →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4),
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let u := primitiveUnwrappedCellTuple ε n hn y
          let D := primitiveTupleDiameterBracketSq (by omega) u
          let c : Fin (2 * n - 2) → T4 := fun i =>
            latticeTorusCenter δ (y (primitiveInternalIdx n hn i))
          (∫⁻ v in
              (fun q =>
                pairedCellAssignment κ δ
                  (primitiveAssemble n hn z w q)) ⁻¹' {y},
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n hn G κ
                  (primitiveAssemble n hn z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * C) ^ n *
                  ((12 + 32 * R ^ 2) * δ ^ 2 * D)) *
              terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
  obtain ⟨C, hC, hpointwise⟩ :=
    exists_primitiveInsertedIntegrand_fiber_bound ρ
  refine ⟨C, hC, ?_⟩
  intro n hn G hG κ hfull ε hε hε1 z w y
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let u := primitiveUnwrappedCellTuple ε n hn y
  let D := primitiveTupleDiameterBracketSq (by omega) u
  let c : Fin (2 * n - 2) → T4 := fun i =>
    latticeTorusCenter δ (y (primitiveInternalIdx n hn i))
  let fiber : Set (Fin (2 * n - 2) → T4) :=
    (fun q =>
      pairedCellAssignment κ δ
        (primitiveAssemble n hn z w q)) ⁻¹' {y}
  let box : Set (Fin (2 * n - 2) → T4) :=
    Set.univ.pi fun i => Metric.ball (c i) (R * δ)
  let lhs : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn G κ
        (primitiveAssemble n hn z w v)|
  let K :=
    (ε⁻¹ ^ (dim : ℕ) * C) ^ n *
      ((12 + 32 * R ^ 2) * δ ^ 2 * D)
  let rhs : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal K * terminalSingularProduct z w (List.ofFn v)
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  have hδ : 0 < δ := by
    exact compatibleMeshSize_pos hε
  have hfiberMeas : MeasurableSet fiber := by
    dsimp only [fiber, δ]
    exact
      (primitivePairedInternalCells n hn κ
        (compatibleMeshSize ε)
        (compatibleMeshSize_pos hε) z w).measurable_fiber y
  have hboxMeas : MeasurableSet box := by
    dsimp only [box]
    exact MeasurableSet.univ_pi fun i =>
      measurableSet_ball
  have hterm : Measurable fun v : Fin (2 * n - 2) → T4 =>
      terminalSingularProduct z w (List.ofFn v) := by
    convert (measurable_terminalSingularProduct_ofFn
      (2 * n - 2) w).comp
        (measurable_const.prodMk measurable_id) using 1
    ext v
    rfl
  have hindicator :
      fiber.indicator lhs ≤ box.indicator rhs := by
    intro v
    by_cases hv : v ∈ fiber
    · rw [Set.indicator_of_mem hv]
      have hvfiber :
          pairedCellAssignment κ δ
              (primitiveAssemble n hn z w v) = y := by
        simpa only [fiber, Set.mem_preimage, Set.mem_singleton_iff] using hv
      by_cases hcov :
          primitiveCovarianceProduct ρ ε n κ
              (primitiveAssemble n hn z w v) = 0
      · have hz :
            primitiveInsertedIntegrand ρ ε n hn G κ
                (primitiveAssemble n hn z w v) = 0 := by
          unfold primitiveInsertedIntegrand primitiveIntegrand
          rw [hcov, mul_zero, mul_zero]
        simp only [lhs, hz, abs_zero, ENNReal.ofReal_zero, zero_le]
      · have hvbox : v ∈ box := by
          have hm :=
            primitiveInternal_mem_productCell_of_fiber_covariance_ne_zero
              ρ hε hε1 n hn κ hfull z w y v hvfiber hcov
          simpa only [box, c, R, δ] using hm
        rw [Set.indicator_of_mem hvbox]
        simpa only [lhs, rhs, K, R, δ, u, D] using
          hpointwise n hn G hG κ hfull hε hε1
            z w y v hvfiber hcov
    · simp only [Set.indicator, hv, ↓reduceIte, zero_le]
  calc
    (∫⁻ v in fiber, lhs v ∂μ) =
        ∫⁻ v, fiber.indicator lhs v ∂μ := by
      rw [lintegral_indicator hfiberMeas]
    _ ≤ ∫⁻ v, box.indicator rhs v ∂μ :=
      lintegral_mono hindicator
    _ = ∫⁻ v in box, rhs v ∂μ :=
      lintegral_indicator hboxMeas rhs
    _ = ENNReal.ofReal K *
          ∫⁻ v in box,
            terminalSingularProduct z w (List.ofFn v) ∂μ := by
      dsimp only [rhs]
      rw [lintegral_const_mul (ENNReal.ofReal K)
        hterm]
    _ = ENNReal.ofReal K *
          terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
      congr 1
      exact terminalSingularProduct_setLIntegral_productCell
        (R * δ) z w (2 * n - 2) c

/-! ## Closing the exact per-fiber scale ledger -/

/-- The uniform cell maximum, rather than a value of the insertion at a
single tuple, multiplies the terminal-chain integral.  This is the form
needed after pulling the insertion outside a product-cell integral. -/
theorem primitiveCellMaximumTerminalLIntegral_exhaustive_order :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (hn : 2 ≤ n) {ε : ℝ}
        (_hε : 0 < ε)
        (R : ℝ) (_hR : 0 < R)
        (y : Fin (2 * n) → Z4) (z w : T4),
        z ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
            (primitiveFirstCell n (by omega) y) →
        w ∈ latticeCellNeighborhood (compatibleMeshSize ε) R
            (primitiveLastCell n (by omega) y) →
        let δ := compatibleMeshSize ε
        let u := primitiveUnwrappedCellTuple ε n (by omega) y
        let D := primitiveTupleDiameterBracketSq (by omega) u
        let W := latticeTerminalPathWeight
          (primitiveFirstCell n (by omega) y)
          (primitiveUnwrappedLast ε n (by omega) y)
          (primitiveUnwrappedInternal ε n (by omega) y)
        ENNReal.ofReal
              ((12 + 32 * R ^ 2) * δ ^ 2 * D) *
            terminalCellLIntegral (R * δ) z w
              ((primitiveInternalCellLabels n (by omega) y).map
                (latticeTorusCenter δ)) ≤
          ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
            ENNReal.ofReal
              ((12 + 32 * R ^ 2) * D *
                (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
                δ ^ (4 * n - 4) * W) := by
  obtain ⟨C, hC, hcell⟩ :=
    primitiveTerminalCellLIntegral_exhaustive_order
  refine ⟨C, hC, ?_⟩
  intro n hn ε hε R hR y z w hz hw
  let hn1 : 1 ≤ n := by omega
  let δ := compatibleMeshSize ε
  let u := primitiveUnwrappedCellTuple ε n hn1 y
  let D := primitiveTupleDiameterBracketSq (by omega) u
  let W := latticeTerminalPathWeight
    (primitiveFirstCell n hn1 y)
    (primitiveUnwrappedLast ε n hn1 y)
    (primitiveUnwrappedInternal ε n hn1 y)
  let F := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let A :=
    (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 6) * W
  let B :=
    (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 6) * W
  have hchain :=
    hcell n hn hε R hR y z w hz hw
  change terminalCellLIntegral (R * δ) z w
      ((primitiveInternalCellLabels n hn1 y).map
        (latticeTorusCenter δ)) ≤
      ENNReal.ofReal A + ENNReal.ofReal B at hchain
  have hδ0 : 0 ≤ δ := (compatibleMeshSize_pos hε).le
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact primitiveTupleDiameterBracketSq_nonneg (by omega) u
  have hF0 : 0 ≤ F := by
    dsimp only [F]
    exact mul_nonneg
      (mul_nonneg
        (by positivity : 0 ≤ 12 + 32 * R ^ 2)
        (sq_nonneg δ))
      hD0
  have hfarBase : 0 ≤ C * (R ^ 2 + R ^ 4) :=
    mul_nonneg hC.le
      (add_nonneg (sq_nonneg R) (by positivity))
  have hnearBase : 0 ≤ C * cellChainRadiusFactor R :=
    mul_nonneg hC.le (cellChainRadiusFactor_pos R).le
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hfarBase _)
          (terminalRadiusFactor_pos hR).le)
        (pow_nonneg hδ0 _))
      (latticeTerminalPathWeight_nonneg _ _ _)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hnearBase _) (pow_nonneg hδ0 _))
      (latticeTerminalPathWeight_nonneg _ _ _)
  have hFA :
      F * A =
        (12 + 32 * R ^ 2) * D *
          (C * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
          terminalRadiusFactor R * δ ^ (4 * n - 4) * W := by
    dsimp only [F, A]
    rw [← compatibleCell_inserted_power_ledger δ n hn]
    ring
  have hFB :
      F * B =
        (12 + 32 * R ^ 2) * D *
          (C * cellChainRadiusFactor R) ^ (2 * n - 3) *
          δ ^ (4 * n - 4) * W := by
    dsimp only [F, B]
    rw [← compatibleCell_inserted_power_ledger δ n hn]
    ring
  calc
    ENNReal.ofReal F *
        terminalCellLIntegral (R * δ) z w
          ((primitiveInternalCellLabels n hn1 y).map
            (latticeTorusCenter δ)) ≤
        ENNReal.ofReal F *
          (ENNReal.ofReal A + ENNReal.ofReal B) :=
      by
        simpa only [mul_comm] using
          mul_le_mul_right hchain (ENNReal.ofReal F)
    _ = ENNReal.ofReal (F * A) +
          ENNReal.ofReal (F * B) := by
      rw [mul_add, ENNReal.ofReal_mul hF0,
        ENNReal.ofReal_mul hF0]
    _ = _ := by rw [hFA, hFB]

/-- **Complete continuous estimate on one actual paired cell fiber.**

This theorem starts with the real primitive inserted integrand, not a proxy.
It performs the covariance-support reduction, product-cell enlargement,
Tonelli identification, exhaustive chain estimate, and exact
`δ^(4n-4)` ledger.  The resulting lattice weight is then handled by finite
summation and reindexing. -/
theorem primitiveInsertedIntegrand_fiber_exhaustive_order
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4) (y : Fin (2 * n) → Z4),
          letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let u := primitiveUnwrappedCellTuple ε n (by omega) y
          let D := primitiveTupleDiameterBracketSq (by omega) u
          let W := latticeTerminalPathWeight
            (primitiveFirstCell n (by omega) y)
            (primitiveUnwrappedLast ε n (by omega) y)
            (primitiveUnwrappedInternal ε n (by omega) y)
          (∫⁻ v in
              (fun q =>
                pairedCellAssignment κ δ
                  (primitiveAssemble n (by omega) z w q)) ⁻¹' {y},
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ENNReal.ofReal
                ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
              (ENNReal.ofReal
                ((12 + 32 * R ^ 2) * D *
                  (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
                  terminalRadiusFactor R * δ ^ (4 * n - 4) * W) +
               ENNReal.ofReal
                ((12 + 32 * R ^ 2) * D *
                  (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
                  δ ^ (4 * n - 4) * W)) := by
  obtain ⟨Ccov, hCcov, hfiberBound⟩ :=
    exists_primitiveInsertedIntegrand_fiber_lintegral_bound ρ
  obtain ⟨Ccell, hCcell, hcellBound⟩ :=
    primitiveCellMaximumTerminalLIntegral_exhaustive_order
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w y
  letI : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  let hn1 : 1 ≤ n := by omega
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let u := primitiveUnwrappedCellTuple ε n hn1 y
  let D := primitiveTupleDiameterBracketSq (by omega) u
  let W := latticeTerminalPathWeight
    (primitiveFirstCell n hn1 y)
    (primitiveUnwrappedLast ε n hn1 y)
    (primitiveUnwrappedInternal ε n hn1 y)
  let c : Fin (2 * n - 2) → T4 := fun i =>
    latticeTorusCenter δ (y (primitiveInternalIdx n hn1 i))
  let fiber : Set (Fin (2 * n - 2) → T4) :=
    (fun q =>
      pairedCellAssignment κ δ
        (primitiveAssemble n hn1 z w q)) ⁻¹' {y}
  let f : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn1 G κ
        (primitiveAssemble n hn1 z w v)|
  let Q := (ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n
  let F := (12 + 32 * R ^ 2) * δ ^ 2 * D
  let A :=
    (12 + 32 * R ^ 2) * D *
      (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4) * W
  let B :=
    (12 + 32 * R ^ 2) * D *
      (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4) * W
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  have hfull : κ.IsFull :=
    (mem_primitiveFullPairings.mp hκ).1
  have hR : 0 < R := by
    dsimp only [R]
    nlinarith [ρ.radius_pos]
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact pow_nonneg
      (mul_nonneg
        (pow_nonneg (inv_nonneg.mpr hε.le) _)
        hCcov.le) _
  have hc :
      List.ofFn c =
        (primitiveInternalCellLabels n hn1 y).map
          (latticeTorusCenter δ) := by
    unfold c primitiveInternalCellLabels
    exact List.ofFn_comp' _ _
  have hpre :
      (∫⁻ v in fiber, f v ∂μ) ≤
        ENNReal.ofReal (Q * F) *
          terminalCellLIntegral (R * δ) z w (List.ofFn c) := by
    simpa only [fiber, f, μ, Q, F, R, δ, u, D, hn1] using
      hfiberBound n hn1 G hG κ hfull hε hε1 z w y
  change (∫⁻ v in fiber, f v ∂μ) ≤
    ENNReal.ofReal Q *
      (ENNReal.ofReal A + ENNReal.ofReal B)
  by_cases hsupported :
      ∃ v, v ∈ fiber ∧
        primitiveCovarianceProduct ρ ε n κ
          (primitiveAssemble n hn1 z w v) ≠ 0
  · obtain ⟨v₀, hv₀, hcov₀⟩ := hsupported
    have hvfiber :
        pairedCellAssignment κ δ
            (primitiveAssemble n hn1 z w v₀) = y := by
      simpa only [fiber, Set.mem_preimage, Set.mem_singleton_iff] using hv₀
    have hmem :=
      primitiveCoordinates_mem_pairedCompatibleCells_of_covariance_ne_zero
        ρ κ hfull hε hε1
          (primitiveAssemble n hn1 z w v₀) hcov₀
    rw [hvfiber] at hmem
    have hz :
        z ∈ latticeCellNeighborhood δ R
          (primitiveFirstCell n hn1 y) := by
      simpa only [primitiveFirstCell, primitiveAssemble_zero,
        δ, R] using
        hmem (⟨0, by omega⟩ : Fin (2 * n))
    have hw :
        w ∈ latticeCellNeighborhood δ R
          (primitiveLastCell n hn1 y) := by
      simpa only [primitiveLastCell, primitiveAssemble_last,
        δ, R] using hmem (primitiveLast n hn1)
    have hcell :=
      hcellBound n hn hε R hR y z w hz hw
    change ENNReal.ofReal F *
        terminalCellLIntegral (R * δ) z w
          ((primitiveInternalCellLabels n hn1 y).map
            (latticeTorusCenter δ)) ≤
        ENNReal.ofReal A + ENNReal.ofReal B at hcell
    calc
      (∫⁻ v in fiber, f v ∂μ) ≤
          ENNReal.ofReal (Q * F) *
            terminalCellLIntegral (R * δ) z w (List.ofFn c) :=
        hpre
      _ = ENNReal.ofReal Q *
          (ENNReal.ofReal F *
            terminalCellLIntegral (R * δ) z w
              ((primitiveInternalCellLabels n hn1 y).map
                (latticeTorusCenter δ))) := by
        rw [ENNReal.ofReal_mul hQ0, hc]
        ring
      _ ≤ ENNReal.ofReal Q *
          (ENNReal.ofReal A + ENNReal.ofReal B) :=
        by
          simpa only [mul_comm] using
            mul_le_mul_right hcell (ENNReal.ofReal Q)
  · have hfiberMeas : MeasurableSet fiber := by
      dsimp only [fiber, δ]
      exact
        (primitivePairedInternalCells n hn1 κ
          (compatibleMeshSize ε)
          (compatibleMeshSize_pos hε) z w).measurable_fiber y
    have hzero : (∫⁻ v in fiber, f v ∂μ) = 0 := by
      apply le_antisymm
      · calc
          (∫⁻ v in fiber, f v ∂μ) ≤
              ∫⁻ _v in fiber, 0 ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hfiberMeas] with v hv
            have hcov :
                primitiveCovarianceProduct ρ ε n κ
                    (primitiveAssemble n hn1 z w v) = 0 := by
              exact not_ne_iff.mp fun hne =>
                hsupported ⟨v, hv, hne⟩
            have hvalue :
                primitiveInsertedIntegrand ρ ε n hn1 G κ
                    (primitiveAssemble n hn1 z w v) = 0 := by
              unfold primitiveInsertedIntegrand primitiveIntegrand
              rw [hcov, mul_zero, mul_zero]
            simp only [f, hvalue, abs_zero, ENNReal.ofReal_zero]
            exact le_rfl
          _ = 0 := by simp
      · exact bot_le
    rw [hzero]
    exact bot_le

/-! ## Exact reduction to the existing finite lattice statistic -/

/-- The tuple-diameter maximum is invariant under a bijective reindexing of
the finite slots. -/
theorem primitiveTupleDiameterBracketSq_comp_equiv
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (e : Fin m ≃ Fin k) (y : Fin k → Z4) :
    primitiveTupleDiameterBracketSq hm (fun i => y (e i)) =
      primitiveTupleDiameterBracketSq hk y := by
  apply le_antisymm
  · unfold primitiveTupleDiameterBracketSq
    apply Finset.sup'_le
    intro i _hi
    apply Finset.sup'_le
    intro j _hj
    exact latticeBracketSq_le_primitiveTupleDiameterBracketSq
      hk y (e i) (e j)
  · unfold primitiveTupleDiameterBracketSq
    apply Finset.sup'_le
    intro i _hi
    apply Finset.sup'_le
    intro j _hj
    change latticeBracketSq (y i) (y j) ≤
      primitiveTupleDiameterBracketSq hm (fun a => y (e a))
    simpa only [e.apply_symm_apply] using
      latticeBracketSq_le_primitiveTupleDiameterBracketSq
        hm (fun a => y (e a)) (e.symm i) (e.symm j)

/-- The cell-tuple maximum and the arithmetic-cast reduction-tuple maximum
are literally equal. -/
theorem primitiveUnwrappedCellDiameter_eq_reductionDiameter
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    primitiveTupleDiameterBracketSq (by omega)
        (primitiveUnwrappedCellTuple ε n hn y) =
      primitiveTupleDiameterBracketSq (by omega)
        (primitiveUnwrappedReductionTuple ε n hn y) := by
  let e : Fin ((2 * n - 1) + 1) ≃ Fin (2 * n) :=
    finCongr (Nat.sub_add_cancel (by omega : 1 ≤ 2 * n))
  have h :=
    primitiveTupleDiameterBracketSq_comp_equiv
      (by omega : 0 < (2 * n - 1) + 1)
      (by omega : 0 < 2 * n) e
      (primitiveUnwrappedCellTuple ε n hn y)
  have hu :
      (fun i =>
        primitiveUnwrappedCellTuple ε n hn y (e i)) =
        primitiveUnwrappedReductionTuple ε n hn y := by
    funext i
    unfold primitiveUnwrappedReductionTuple
    apply congrArg (primitiveUnwrappedCellTuple ε n hn y)
    apply Fin.ext
    rfl
  rw [hu] at h
  exact h.symm

/-- The two lattice factors displayed by the continuous fiber estimate are
exactly the pre-existing `reductionWeight`, with no inequality or hidden
constant. -/
theorem primitiveUnwrappedCellStatistic_eq_reductionWeight
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    primitiveTupleDiameterBracketSq (by omega)
          (primitiveUnwrappedCellTuple ε n hn y) *
        latticeTerminalPathWeight
          (primitiveFirstCell n hn y)
          (primitiveUnwrappedLast ε n hn y)
          (primitiveUnwrappedInternal ε n hn y) =
      reductionWeight (2 * n - 1)
        (primitiveUnwrappedReductionTuple ε n hn y) := by
  rw [primitiveUnwrappedCellDiameter_eq_reductionDiameter]
  exact (primitiveUnwrappedReductionWeight_eq ε n hn y).symm

/-- Scalar ledger used to rewrite either exhaustive branch directly into the
finite lattice interface. -/
theorem primitiveUnwrappedCellStatistic_scalarLedger
    (a b ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (y : Fin (2 * n) → Z4) :
    a *
        primitiveTupleDiameterBracketSq (by omega)
          (primitiveUnwrappedCellTuple ε n hn y) *
        b *
        latticeTerminalPathWeight
          (primitiveFirstCell n hn y)
          (primitiveUnwrappedLast ε n hn y)
          (primitiveUnwrappedInternal ε n hn y) =
      a * b *
        reductionWeight (2 * n - 1)
          (primitiveUnwrappedReductionTuple ε n hn y) := by
  rw [← primitiveUnwrappedCellStatistic_eq_reductionWeight ε n hn y]
  ring

/-! ## Summing the genuine endpoint-fixed cell partition -/

/-- For one primitive pairing, the complete endpoint-fixed integral is
bounded by a finite sum of the existing `reductionWeight`, evaluated at the
centre-preserving unwrapped representative.  The filter is the original
copied-pair constraint and is proved from the actual cell assignment.

This theorem closes all continuous summation.  Its right-hand side isolates
the remaining finite period-lift reindexing problem. -/
theorem primitiveInsertedIntegrand_lintegral_le_unwrappedReductionSum
    (ρ : SmoothCutoff) :
    ∃ Ccov Ccell : ℝ, 0 < Ccov ∧ 0 < Ccell ∧
      ∀ (n : ℕ) (hn : 2 ≤ n)
        (G : Fin (2 * n - 1) → T4 → ℝ),
        IsAdmissiblePrimitiveInput n G →
        ∀ (κ : PartialPairing (Fin (2 * n))),
          κ ∈ primitiveFullPairings n →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∀ (z w : T4),
          let R := 1 + 4 * ρ.radius
          let δ := compatibleMeshSize ε
          let grid :=
            Fintype.piFinset
              (fun _ : Fin (2 * n) => torusGrid δ)
          let farCoeff :=
            (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
              terminalRadiusFactor R * δ ^ (4 * n - 4)
          let nearCoeff :=
            (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
              δ ^ (4 * n - 4)
          (∫⁻ v,
              ENNReal.ofReal
                |primitiveInsertedIntegrand ρ ε n (by omega) G κ
                  (primitiveAssemble n (by omega) z w v)|
            ∂Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure) ≤
            ∑ y ∈ grid.filter (RespectsPairing κ),
              ENNReal.ofReal
                  ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
                (ENNReal.ofReal
                    ((12 + 32 * R ^ 2) * farCoeff *
                      reductionWeight (2 * n - 1)
                        (primitiveUnwrappedReductionTuple ε n
                          (by omega) y)) +
                 ENNReal.ofReal
                    ((12 + 32 * R ^ 2) * nearCoeff *
                      reductionWeight (2 * n - 1)
                        (primitiveUnwrappedReductionTuple ε n
                          (by omega) y))) := by
  obtain ⟨Ccov, Ccell, hCcov, hCcell, hfiber⟩ :=
    primitiveInsertedIntegrand_fiber_exhaustive_order ρ
  refine ⟨Ccov, Ccell, hCcov, hCcell, ?_⟩
  intro n hn G hG κ hκ ε hε hε1 z w
  let hn1 : 1 ≤ n := by omega
  let R := 1 + 4 * ρ.radius
  let δ := compatibleMeshSize ε
  let grid :=
    Fintype.piFinset
      (fun _ : Fin (2 * n) => torusGrid δ)
  let farCoeff :=
    (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
      terminalRadiusFactor R * δ ^ (4 * n - 4)
  let nearCoeff :=
    (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
      δ ^ (4 * n - 4)
  let f : (Fin (2 * n - 2) → T4) → ENNReal := fun v =>
    ENNReal.ofReal
      |primitiveInsertedIntegrand ρ ε n hn1 G κ
        (primitiveAssemble n hn1 z w v)|
  let μ := Measure.pi fun _ : Fin (2 * n - 2) => paperMeasure
  let cellBound : (Fin (2 * n) → Z4) → ENNReal := fun y =>
    ENNReal.ofReal ((ε⁻¹ ^ (dim : ℕ) * Ccov) ^ n) *
      (ENNReal.ofReal
          ((12 + 32 * R ^ 2) * farCoeff *
            reductionWeight (2 * n - 1)
              (primitiveUnwrappedReductionTuple ε n hn1 y)) +
       ENNReal.ofReal
          ((12 + 32 * R ^ 2) * nearCoeff *
            reductionWeight (2 * n - 1)
              (primitiveUnwrappedReductionTuple ε n hn1 y)))
  have hpartition :=
    primitive_lintegral_eq_sum_pairedInternalCells
      n hn1 κ (compatibleMeshSize_pos hε) z w f
  change (∫⁻ v, f v ∂μ) =
      ∑ y ∈ grid,
        ∫⁻ v in
            (fun q =>
              pairedCellAssignment κ δ
                (primitiveAssemble n hn1 z w q)) ⁻¹' {y},
          f v ∂μ at hpartition
  change (∫⁻ v, f v ∂μ) ≤
    ∑ y ∈ grid.filter (RespectsPairing κ), cellBound y
  rw [hpartition]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro y hy
  by_cases hrespect : RespectsPairing κ y
  · simp only [hrespect, ↓reduceIte]
    have hbound :=
      hfiber n hn G hG κ hκ hε hε1 z w y
    have hfar :
        (12 + 32 * R ^ 2) *
            primitiveTupleDiameterBracketSq (by omega)
              (primitiveUnwrappedCellTuple ε n hn1 y) *
            (Ccell * (R ^ 2 + R ^ 4)) ^ (2 * n - 2) *
            terminalRadiusFactor R * δ ^ (4 * n - 4) *
            latticeTerminalPathWeight
              (primitiveFirstCell n hn1 y)
              (primitiveUnwrappedLast ε n hn1 y)
              (primitiveUnwrappedInternal ε n hn1 y) =
          (12 + 32 * R ^ 2) * farCoeff *
            reductionWeight (2 * n - 1)
              (primitiveUnwrappedReductionTuple ε n hn1 y) := by
      calc
        _ = (12 + 32 * R ^ 2) *
              primitiveTupleDiameterBracketSq (by omega)
                (primitiveUnwrappedCellTuple ε n hn1 y) *
              farCoeff *
              latticeTerminalPathWeight
                (primitiveFirstCell n hn1 y)
                (primitiveUnwrappedLast ε n hn1 y)
                (primitiveUnwrappedInternal ε n hn1 y) := by
          dsimp only [farCoeff]
          ring
        _ = _ :=
          primitiveUnwrappedCellStatistic_scalarLedger
            (12 + 32 * R ^ 2) farCoeff ε n hn1 y
    have hnear :
        (12 + 32 * R ^ 2) *
            primitiveTupleDiameterBracketSq (by omega)
              (primitiveUnwrappedCellTuple ε n hn1 y) *
            (Ccell * cellChainRadiusFactor R) ^ (2 * n - 3) *
            δ ^ (4 * n - 4) *
            latticeTerminalPathWeight
              (primitiveFirstCell n hn1 y)
              (primitiveUnwrappedLast ε n hn1 y)
              (primitiveUnwrappedInternal ε n hn1 y) =
          (12 + 32 * R ^ 2) * nearCoeff *
            reductionWeight (2 * n - 1)
              (primitiveUnwrappedReductionTuple ε n hn1 y) := by
      calc
        _ = (12 + 32 * R ^ 2) *
              primitiveTupleDiameterBracketSq (by omega)
                (primitiveUnwrappedCellTuple ε n hn1 y) *
              nearCoeff *
              latticeTerminalPathWeight
                (primitiveFirstCell n hn1 y)
                (primitiveUnwrappedLast ε n hn1 y)
                (primitiveUnwrappedInternal ε n hn1 y) := by
          dsimp only [nearCoeff]
          ring
        _ = _ :=
          primitiveUnwrappedCellStatistic_scalarLedger
            (12 + 32 * R ^ 2) nearCoeff ε n hn1 y
    simpa only [f, μ, cellBound, R, δ, farCoeff, nearCoeff,
      hn1, hfar, hnear] using hbound
  · simp only [hrespect, ↓reduceIte]
    have hempty :
        (fun q =>
          pairedCellAssignment κ δ
            (primitiveAssemble n hn1 z w q)) ⁻¹' {y} = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨v, hv⟩
      have heq :
          pairedCellAssignment κ δ
              (primitiveAssemble n hn1 z w v) = y := by
        simpa only [Set.mem_preimage,
          Set.mem_singleton_iff] using hv
      apply hrespect
      rw [← heq]
      exact pairedCellAssignment_respectsPairing κ δ
        (primitiveAssemble n hn1 z w v)
    rw [hempty]
    simp

/-- Purely finite statistic left after the continuous §5.1 argument:
canonical copied-pair labels are sent to their centre-preserving unwrapped
chain representatives before evaluating `reductionWeight`. -/
def primitiveUnwrappedReductionCellSum
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) : ENNReal :=
  ∑ y ∈
      (Fintype.piFinset
        (fun _ : Fin (2 * n) =>
          torusGrid (compatibleMeshSize ε))).filter
        (RespectsPairing κ),
    ENNReal.ofReal
      (reductionWeight (2 * n - 1)
        (primitiveUnwrappedReductionTuple ε n hn y))

/-- Constant factors in either exhaustive branch pull cleanly out of the
remaining finite unwrapped reduction sum. -/
theorem primitiveUnwrappedReductionCellSum_factor
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (κ : PartialPairing (Fin (2 * n))) :
    (∑ y ∈
        (Fintype.piFinset
          (fun _ : Fin (2 * n) =>
            torusGrid (compatibleMeshSize ε))).filter
          (RespectsPairing κ),
        ENNReal.ofReal q *
          (ENNReal.ofReal
              (a * reductionWeight (2 * n - 1)
                (primitiveUnwrappedReductionTuple ε n hn y)) +
           ENNReal.ofReal
              (b * reductionWeight (2 * n - 1)
                (primitiveUnwrappedReductionTuple ε n hn y)))) =
      ENNReal.ofReal q *
        (ENNReal.ofReal a + ENNReal.ofReal b) *
          primitiveUnwrappedReductionCellSum ε n hn κ := by
  unfold primitiveUnwrappedReductionCellSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [mul_add, ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  ring

end

end Anderson4D
