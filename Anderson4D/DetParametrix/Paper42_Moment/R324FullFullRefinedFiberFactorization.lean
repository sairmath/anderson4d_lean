import Anderson4D.DetParametrix.Paper42_Moment.R324FullFullTermFactorization
import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedFiberExact
import Anderson4D.DetParametrix.Paper41_Renorm.R322EndpointFiber

/-!
# Exact full/full factorization of a refined R-324 fibre

If one representative of a residual-refined contraction fibre has full
pairings in both halves, endpoint-signature rigidity makes every pairing in
the two corresponding endpoint fibres full.  The residual carrier is then
empty, so the residual signature filter removes nothing.  Consequently the
entire refined fibre is exactly the product of the two endpoint-signature
fibres; the cross-single equivalence is the unique equivalence between two
empty single sets.

After this finite reindexing, the already established factorization of one
frozen full/full contraction turns the complete refined sum into the product
of the two complete half-fibre sums.  The only analytic assumptions are
termwise integrability of the left and right half integrands.  No grouped
residual is replaced by a fixed `detIntegrand`, and no coupling factor is
introduced.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Empty residual signatures -/

/-- Both full within-half pairings have the empty residual-chain
signature, independently of the (necessarily empty) cross-single
equivalence. -/
theorem momentResidualChainSignature_eq_empty_of_isFull
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hp : κp.IsFull) (hm : κm.IsFull) :
    momentResidualChainSignature κp κm π = (∅, ∅) := by
  have hactive :
      momentResidualActive κp κm = ∅ :=
    (momentResidualActive_eq_empty_iff_isFull
      κp κm).mpr ⟨hp, hm⟩
  have hchain :
      momentResidualIntervalChain κp κm π = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p hpMem
    have hpRel :
        IsRelFullyPaired
          (momentCombinedPairing κp κm π)
          (momentResidualActive κp κm) p.1 p.2 :=
      (mem_momentResidualProperIntervals.mp
        (mem_momentResidualIntervalChain.mp hpMem)).1
    have hpActive := hpRel.left_mem
    rw [hactive] at hpActive
    exact (Finset.notMem_empty p.1 hpActive).elim
  simp only [momentResidualChainSignature, hchain,
    List.map_nil, List.toFinset_nil]

/-- In a moment-signature fibre over a full/full reference, the residual
signature is automatically the reference residual signature. -/
theorem momentResidualChainSignature_eq_of_full_reference
    {m : ℕ} (e₀ : MomentContraction m)
    (hp : e₀.1.IsFull) (hm : e₀.2.1.IsFull)
    (e : MomentSignatureFiberAt e₀) :
    momentResidualChainSignature
        e.1.1 e.1.2.1 e.1.2.2 =
      momentResidualChainSignature
        e₀.1 e₀.2.1 e₀.2.2 := by
  obtain ⟨hleft, hright⟩ :=
    reductionEndpointSignatures_eq_of_momentContractionSignature_eq
      e.1 e₀ e.2
  have hp' : e.1.1.IsFull :=
    isFull_of_reductionEndpointSignature_eq
      e₀.1 e.1.1 hp hleft
  have hm' : e.1.2.1.IsFull :=
    isFull_of_reductionEndpointSignature_eq
      e₀.2.1 e.1.2.1 hm hright
  rw [
    momentResidualChainSignature_eq_empty_of_isFull
      e.1.1 e.1.2.1 e.1.2.2 hp' hm',
    momentResidualChainSignature_eq_empty_of_isFull
      e₀.1 e₀.2.1 e₀.2.2 hp hm]

/-! ## Exact finite fibre equivalence -/

/-- The unique cross-single equivalence between two full pairings. -/
def fullPairingSinglesEquiv
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (hp : κp.IsFull) (hm : κm.IsFull) :
    κp.singles ≃ κm.singles := by
  letI : IsEmpty κp.singles :=
    ⟨fun i => by
      have hi :
          i.1 ∈ (∅ : Finset (Fin m)) := by
        simpa only [
          PartialPairing.isFull_iff_singles_eq_empty.mp hp] using
          i.2
      exact (Finset.notMem_empty i.1 hi).elim⟩
  letI : IsEmpty κm.singles :=
    ⟨fun i => by
      have hi :
          i.1 ∈ (∅ : Finset (Fin m)) := by
        simpa only [
          PartialPairing.isFull_iff_singles_eq_empty.mp hm] using
          i.2
      exact (Finset.notMem_empty i.1 hi).elim⟩
  exact Equiv.equivOfIsEmpty κp.singles κm.singles

/-- For a full/full representative, its refined fibre is exactly its whole
moment-signature fibre: the residual signature condition is automatic. -/
def momentRefinedFullFullFiberEquivMomentSignatureFiber
    {m : ℕ}
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (hp : e₀.1.IsFull) (hm : e₀.2.1.IsFull) :
    MomentRefinedContractionFiberAt m s r ≃
      MomentSignatureFiberAt e₀ where
  toFun e := by
    have he :=
      mem_momentRefinedContractionFiber.mp e.2
    have he₀' :=
      mem_momentRefinedContractionFiber.mp he₀
    exact ⟨e.1, he.1.trans he₀'.1.symm⟩
  invFun e := by
    have he₀' :=
      mem_momentRefinedContractionFiber.mp he₀
    refine
      ⟨e.1, mem_momentRefinedContractionFiber.mpr
        ⟨e.2.trans he₀'.1, ?_⟩⟩
    exact
      (momentResidualChainSignature_eq_of_full_reference
        e₀ hp hm e).trans he₀'.2
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

/-- In full/full moment coordinates, the cross-single equivalence is
uniquely determined, leaving just the two independent endpoint fibres. -/
def momentFullFullSignatureCoordinatesEquivEndpointFibers
    {m : ℕ} (e₀ : MomentContraction m)
    (hp : e₀.1.IsFull) (hm : e₀.2.1.IsFull) :
    MomentSignatureCoordinates e₀ ≃
      ReductionEndpointFiberAt e₀.1 ×
        ReductionEndpointFiberAt e₀.2.1 where
  toFun c := (c.1, c.2.1)
  invFun p := by
    have hp' : p.1.1.IsFull :=
      isFull_of_reductionEndpointSignature_eq
        e₀.1 p.1.1 hp p.1.2
    have hm' : p.2.1.IsFull :=
      isFull_of_reductionEndpointSignature_eq
        e₀.2.1 p.2.1 hm p.2.2
    exact
      ⟨p.1, p.2,
        fullPairingSinglesEquiv p.1.1 p.2.1 hp' hm'⟩
  left_inv c := by
    rcases c with ⟨κp, κm, π⟩
    dsimp
    have hp' : κp.1.IsFull :=
      isFull_of_reductionEndpointSignature_eq
        e₀.1 κp.1 hp κp.2
    have hm' : κm.1.IsFull :=
      isFull_of_reductionEndpointSignature_eq
        e₀.2.1 κm.1 hm κm.2
    have hπ :
        fullPairingSinglesEquiv
            κp.1 κm.1 hp' hm' =
          π := by
      apply Equiv.ext
      intro i
      have hi :
          i.1 ∈ (∅ : Finset (Fin m)) := by
        simpa only [
          PartialPairing.isFull_iff_singles_eq_empty.mp hp'] using
          i.2
      exact (Finset.notMem_empty i.1 hi).elim
    exact
      Sigma.ext rfl
        (heq_of_eq
          (Sigma.ext rfl (heq_of_eq hπ)))
  right_inv p := by
    rfl

/-- Exact product coordinates for an entire full/full residual-refined
fibre.  This equivalence is the no-multiplicity statement: every
contraction occurs once and only once. -/
def momentRefinedFullFullFiberEquivEndpointFibers
    {m : ℕ}
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (hp : e₀.1.IsFull) (hm : e₀.2.1.IsFull) :
    MomentRefinedContractionFiberAt m s r ≃
      ReductionEndpointFiberAt e₀.1 ×
        ReductionEndpointFiberAt e₀.2.1 :=
  (momentRefinedFullFullFiberEquivMomentSignatureFiber
      e₀ he₀ hp hm).trans
    ((momentSignatureFiberEquivCoordinates e₀).trans
      (momentFullFullSignatureCoordinatesEquivEndpointFibers
        e₀ hp hm))

/-! ## Analytic half terms and full-fibre factorization -/

/-- One signed half integral, with the two endpoint modes kept explicit. -/
def deterministicFullHalfIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) : ℂ :=
  ∫ p : T4 × (T4 × (Fin m → T4)),
    charT4 α p.1 * charT4 β p.2.1 *
      (detIntegrand ρ ε m κ
        (assemble p.1 p.2.1 p.2.2) : ℂ)
    ∂(paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin m => paperMeasure)))

/-- The exact termwise analytic seam needed before applying the frozen
full/full contraction factorization. -/
def DeterministicFullHalfIntegrable
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (α β : Z4) (κ : PartialPairing (Fin m)) : Prop :=
  Integrable
    (fun p : T4 × (T4 × (Fin m → T4)) =>
      charT4 α p.1 * charT4 β p.2.1 *
        (detIntegrand ρ ε m κ
          (assemble p.1 p.2.1 p.2.2) : ℂ))
    (paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin m => paperMeasure)))

/-- **Full/full refined-fibre factorization.**

The complete frozen contraction sum over a residual-refined fibre is the
product of the complete left and right endpoint-signature fibre sums.  The
right modes are exactly `-α,-β`; no `lamEps` factor belongs to the frozen
contraction term. -/
theorem
    sum_momentRefinedContractionFiber_deterministicMomentContractionTerm_eq_fullHalfFiber_mul
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (e₀ : MomentContraction m)
    (he₀ : e₀ ∈ momentRefinedContractionFiber m s r)
    (hp : e₀.1.IsFull) (hm : e₀.2.1.IsFull)
    (hleft :
      ∀ κp : ReductionEndpointFiberAt e₀.1,
        DeterministicFullHalfIntegrable
          ρ ε m α β κp.1)
    (hright :
      ∀ κm : ReductionEndpointFiberAt e₀.2.1,
        DeterministicFullHalfIntegrable
          ρ ε m (-α) (-β) κm.1) :
    (∑ e ∈ momentRefinedContractionFiber m s r,
        deterministicMomentContractionTerm
          ρ ε m α β e) =
      (∑ κp : ReductionEndpointFiberAt e₀.1,
          deterministicFullHalfIntegral
            ρ ε m α β κp.1) *
        ∑ κm : ReductionEndpointFiberAt e₀.2.1,
          deterministicFullHalfIntegral
            ρ ε m (-α) (-β) κm.1 := by
  let E :=
    momentRefinedFullFullFiberEquivEndpointFibers
      e₀ he₀ hp hm
  calc
    (∑ e ∈ momentRefinedContractionFiber m s r,
        deterministicMomentContractionTerm
          ρ ε m α β e) =
        ∑ e : MomentRefinedContractionFiberAt m s r,
          deterministicMomentContractionTerm
            ρ ε m α β e.1 := by
      rw [← Finset.sum_attach, Finset.attach_eq_univ]
    _ =
        ∑ p :
            ReductionEndpointFiberAt e₀.1 ×
              ReductionEndpointFiberAt e₀.2.1,
          deterministicMomentContractionTerm
            ρ ε m α β (E.symm p).1 := by
      exact (E.symm.sum_comp fun e =>
        deterministicMomentContractionTerm
          ρ ε m α β e.1).symm
    _ =
        ∑ κp : ReductionEndpointFiberAt e₀.1,
          ∑ κm : ReductionEndpointFiberAt e₀.2.1,
            deterministicMomentContractionTerm
              ρ ε m α β (E.symm (κp, κm)).1 := by
      rw [Fintype.sum_prod_type]
    _ =
        ∑ κp : ReductionEndpointFiberAt e₀.1,
          ∑ κm : ReductionEndpointFiberAt e₀.2.1,
            deterministicFullHalfIntegral
                ρ ε m α β κp.1 *
              deterministicFullHalfIntegral
                ρ ε m (-α) (-β) κm.1 := by
      apply Finset.sum_congr rfl
      intro κp _hκp
      apply Finset.sum_congr rfl
      intro κm _hκm
      have hp' : κp.1.IsFull :=
        isFull_of_reductionEndpointSignature_eq
          e₀.1 κp.1 hp κp.2
      have hm' : κm.1.IsFull :=
        isFull_of_reductionEndpointSignature_eq
          e₀.2.1 κm.1 hm κm.2
      let π :=
        fullPairingSinglesEquiv
          κp.1 κm.1 hp' hm'
      change
        deterministicMomentContractionTerm
            ρ ε m α β ⟨κp.1, κm.1, π⟩ =
          deterministicFullHalfIntegral
              ρ ε m α β κp.1 *
            deterministicFullHalfIntegral
              ρ ε m (-α) (-β) κm.1
      exact
        deterministicMomentContractionTerm_eq_fullHalfIntegral_mul
          ρ ε m α β κp.1 κm.1 π hp' hm'
          (hleft κp) (hright κm)
    _ = _ := by
      symm
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro κp _hκp
      rw [Finset.mul_sum]

end

end Anderson4D
