import Anderson4D.DetParametrix.Paper42_Moment.R324LedgerThreeInterface

/-!
# Reduction of the pure-cross fibres to the permutation multi-window

A pure-cross refined fibre consists of entities `⟨id, id, π⟩`: both half
chains are plain (`m+1` Green edges, no extraction, no within
covariance), and the `m` covariance legs are all cross legs, indexed by
a set of bijections `π`.  This file proves, at every order `m`:

* the identity-pairing half integrand is the plain Green chain;
* the summed fibre is one physical integral of a *nonnegative* density:
  the two plain chains times the permutation-summed cross covariance —
  no triangle inequality across the fibre is used;
* the permanent bound: the permutation-summed cross covariance is
  pointwise at most the product of its `m` row sums, absorbing the
  factorial fibre cardinality into `m` diagonal-window rows.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The identity pairing has plain chains -/

/-- Nothing is extracted from the identity pairing: a relative fully
paired interval would need its left endpoint moved. -/
theorem r324LedgerThree_extract_id (m : ℕ) :
    extract (PartialPairing.id : PartialPairing (Fin m)) = [] := by
  unfold extract
  apply extractAux_nil_of_no_candidate
  rintro ⟨a, b, h⟩
  exact h.isFullyPairedOn.ne_of_mem h.left_mem_relIcc
    (PartialPairing.id_apply a)

/-- The identity pairing moves nothing. -/
theorem r324LedgerThree_pairSupport_id (m : ℕ) :
    (PartialPairing.id : PartialPairing (Fin m)).pairSupport = ∅ := by
  ext i
  simp

/-- **The identity-pairing integrand is the plain Green chain**: no
edge is excluded, no difference factor and no within covariance
appears. -/
theorem r324LedgerThree_detIntegrand_id
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (xt : Fin (m + 2) → T4) :
    detIntegrand ρ ε m PartialPairing.id xt =
      ∏ e : Fin (m + 1), greenFn (xt e.castSucc - xt e.succ) := by
  unfold detIntegrand
  rw [r324LedgerThree_extract_id, r324LedgerThree_pairSupport_id]
  simp only [List.map_nil, List.not_mem_nil, if_false,
    List.prod_nil, mul_one, Finset.filter_empty, Finset.prod_empty]

/-- The plain Green chain is nonnegative. -/
theorem r324LedgerThree_chain_nonneg
    (m : ℕ) (xt : Fin (m + 2) → T4) :
    0 ≤ ∏ e : Fin (m + 1), greenFn (xt e.castSucc - xt e.succ) :=
  Finset.prod_nonneg fun _ _ => greenFn_nonneg _

/-! ## Pure-cross entities are permutation entities -/

/-- A pure-cross entity is literally `⟨id, id, π⟩` for a bijection `π`
of the identity singles. -/
theorem R324LedgerThreeAllCrossEntity.eq_mk {m : ℕ}
    {e : MomentContraction m}
    (h : R324LedgerThreeAllCrossEntity e) :
    ∃ π : ↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
      e = ⟨PartialPairing.id, PartialPairing.id, π⟩ := by
  obtain ⟨κp, κm, π⟩ := e
  obtain ⟨h1, h2⟩ := h
  dsimp only at h1 h2
  subst h1
  subst h2
  exact ⟨π, rfl⟩

/-- The permutation entities are distinct for distinct bijections. -/
theorem r324LedgerThree_mk_injective {m : ℕ}
    {π π' : ↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
      ↥(PartialPairing.id : PartialPairing (Fin m)).singles}
    (h : (⟨PartialPairing.id, PartialPairing.id, π⟩ :
        MomentContraction m) =
      ⟨PartialPairing.id, PartialPairing.id, π'⟩) : π = π' := by
  simpa using h

/-! ## The permanent bound -/

/-- **Permanent bound by row sums.**  A sum over bijections of products
of nonnegative entries is at most the sum over *all* functions, which
factorizes into the product of the row sums.  This absorbs the
factorial cardinality of a pure-cross fibre into `m` window rows. -/
theorem r324LedgerThree_sum_equiv_prod_le_prod_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (c : ι → κ → ℝ) (hc : ∀ i j, 0 ≤ c i j) :
    (∑ π : ι ≃ κ, ∏ i, c i (π i)) ≤ ∏ i, ∑ j, c i j := by
  have hfun : ∀ f : ι → κ, 0 ≤ ∏ i, c i (f i) := fun f =>
    Finset.prod_nonneg fun i _ => hc i (f i)
  calc
    (∑ π : ι ≃ κ, ∏ i, c i (π i)) =
        ∑ f ∈ (Finset.univ : Finset (ι ≃ κ)).image
          (fun π : ι ≃ κ => (π : ι → κ)),
          ∏ i, c i (f i) := by
      rw [Finset.sum_image]
      intro π _ π' _ h
      exact Equiv.coe_fn_injective h
    _ ≤ ∑ f : ι → κ, ∏ i, c i (f i) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun f _ _ => hfun f)
    _ = ∏ i, ∑ j, c i j := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-! ## The multi-window majorant -/

/-- **The row-sum multi-window majorant**: one full covariance row per
left single.  Each row is one diagonal-window sum in the remaining
frequency estimate. -/
def r324LedgerThreeCrossMajorant
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (v : Fin (2 * m) → T4) : ℝ :=
  ∏ i : ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
    ∑ j : ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
      ρ.etaEpsT4 ε
        (v (leftMomentIndex i.val) - v (rightMomentIndex j.val))

/-- The multi-window majorant is nonnegative. -/
theorem r324LedgerThreeCrossMajorant_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (v : Fin (2 * m) → T4) :
    0 ≤ r324LedgerThreeCrossMajorant ρ ε m v :=
  Finset.prod_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => ρ.etaEpsT4_nonneg ε _

/-- The finset of all permutation entities `⟨id, id, π⟩`. -/
def r324LedgerThreePermEntities (m : ℕ) :
    Finset (MomentContraction m) :=
  (Finset.univ :
    Finset (↥(PartialPairing.id :
        PartialPairing (Fin m)).singles ≃
      ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles)).image
    fun π => ⟨PartialPairing.id, PartialPairing.id, π⟩

/-- Every set of pure-cross entities embeds into the permutation
entities. -/
theorem r324LedgerThree_subset_permEntities {m : ℕ}
    {F : Finset (MomentContraction m)}
    (hF : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e) :
    F ⊆ r324LedgerThreePermEntities m := by
  intro e he
  obtain ⟨π, rfl⟩ := (hF e he).eq_mk
  exact Finset.mem_image.mpr ⟨π, Finset.mem_univ _, rfl⟩

/-- The permutation-entity sum of any function is the bijection sum. -/
theorem r324LedgerThree_sum_permEntities {m : ℕ}
    (G : MomentContraction m → ℝ) :
    (∑ e ∈ r324LedgerThreePermEntities m, G e) =
      ∑ π : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles,
        G ⟨PartialPairing.id, PartialPairing.id, π⟩ := by
  apply Finset.sum_image
  intro π _ π' _ h
  exact r324LedgerThree_mk_injective h

/-- Bijection-sum form of the permutation-entity covariance sum. -/
theorem r324LedgerThree_sum_permEntities_cross
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (v : Fin (2 * m) → T4) :
    (∑ e ∈ r324LedgerThreePermEntities m,
        momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v) =
      ∑ π : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
        momentCrossCovarianceProduct ρ ε m
          PartialPairing.id PartialPairing.id π v :=
  r324LedgerThree_sum_permEntities
    (fun e =>
      momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v)

/-- Permanent bound for the full bijection sum. -/
theorem r324LedgerThree_sum_equiv_cross_le
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (v : Fin (2 * m) → T4) :
    (∑ π : ↥(PartialPairing.id :
          PartialPairing (Fin m)).singles ≃
        ↥(PartialPairing.id : PartialPairing (Fin m)).singles,
        momentCrossCovarianceProduct ρ ε m
          PartialPairing.id PartialPairing.id π v) ≤
      r324LedgerThreeCrossMajorant ρ ε m v := by
  have h := r324LedgerThree_sum_equiv_prod_le_prod_sum
    (fun i j : ↥(PartialPairing.id :
        PartialPairing (Fin m)).singles =>
      ρ.etaEpsT4 ε
        (v (leftMomentIndex i.val) - v (rightMomentIndex j.val)))
    (fun _ _ => ρ.etaEpsT4_nonneg ε _)
  exact h

/-- **The permutation-summed cross covariance obeys the permanent
bound**: any set of pure-cross entities sums pointwise below the
product of the `m` covariance row sums. -/
theorem r324LedgerThree_sum_crossCovariance_le
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (F : Finset (MomentContraction m))
    (hF : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e)
    (v : Fin (2 * m) → T4) :
    (∑ e ∈ F,
        momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v) ≤
      r324LedgerThreeCrossMajorant ρ ε m v := by
  have hnonneg : ∀ e : MomentContraction m,
      0 ≤ momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v :=
    fun e => Finset.prod_nonneg fun _ _ => ρ.etaEpsT4_nonneg ε _
  have h1 :
      (∑ e ∈ F,
          momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v) ≤
        ∑ e ∈ r324LedgerThreePermEntities m,
          momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 v :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (r324LedgerThree_subset_permEntities hF)
      (fun e _ _ => hnonneg e)
  exact h1.trans
    (le_of_eq (r324LedgerThree_sum_permEntities_cross ρ ε m v)
      |>.trans (r324LedgerThree_sum_equiv_cross_le ρ ε m v))

/-! ## The pure-cross physical density -/

/-- The plain left half chain of a pure-cross fibre. -/
def r324LedgerThreeLeftChain (m : ℕ)
    (p : R324PhysicalPoint m) : ℝ :=
  ∏ e : Fin (m + 1),
    greenFn
      ((assemble p.1 p.2.1
          fun i => p.2.2.2.2 (leftMomentIndex i)) e.castSucc -
        (assemble p.1 p.2.1
          fun i => p.2.2.2.2 (leftMomentIndex i)) e.succ)

/-- The plain right half chain of a pure-cross fibre. -/
def r324LedgerThreeRightChain (m : ℕ)
    (p : R324PhysicalPoint m) : ℝ :=
  ∏ e : Fin (m + 1),
    greenFn
      ((assemble p.2.2.1 p.2.2.2.1
          fun i => p.2.2.2.2 (rightMomentIndex i)) e.castSucc -
        (assemble p.2.2.1 p.2.2.2.1
          fun i => p.2.2.2.2 (rightMomentIndex i)) e.succ)

theorem r324LedgerThreeLeftChain_nonneg (m : ℕ)
    (p : R324PhysicalPoint m) :
    0 ≤ r324LedgerThreeLeftChain m p :=
  Finset.prod_nonneg fun _ _ => greenFn_nonneg _

theorem r324LedgerThreeRightChain_nonneg (m : ℕ)
    (p : R324PhysicalPoint m) :
    0 ≤ r324LedgerThreeRightChain m p :=
  Finset.prod_nonneg fun _ _ => greenFn_nonneg _

/-- **The pure-cross fibre density**: two plain Green chains times the
still-summed (cancellation-free, nonnegative) cross covariance of the
fibre. -/
def r324LedgerThreeCrossDensity
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (F : Finset (MomentContraction m))
    (p : R324PhysicalPoint m) : ℝ :=
  r324LedgerThreeLeftChain m p * r324LedgerThreeRightChain m p *
    ∑ e ∈ F,
      momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 p.2.2.2.2

theorem r324LedgerThreeCrossDensity_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (F : Finset (MomentContraction m)) (p : R324PhysicalPoint m) :
    0 ≤ r324LedgerThreeCrossDensity ρ ε m F p := by
  apply mul_nonneg
    (mul_nonneg (r324LedgerThreeLeftChain_nonneg m p)
      (r324LedgerThreeRightChain_nonneg m p))
  exact Finset.sum_nonneg fun e _ =>
    Finset.prod_nonneg fun _ _ => ρ.etaEpsT4_nonneg ε _

/-- **Pointwise multi-window domination of the pure-cross density.**
The permanent bound replaces the factorial permutation sum by the
product of the `m` covariance row sums. -/
theorem r324LedgerThreeCrossDensity_le_majorant
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    {F : Finset (MomentContraction m)}
    (hF : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e)
    (p : R324PhysicalPoint m) :
    r324LedgerThreeCrossDensity ρ ε m F p ≤
      r324LedgerThreeLeftChain m p * r324LedgerThreeRightChain m p *
        r324LedgerThreeCrossMajorant ρ ε m p.2.2.2.2 :=
  mul_le_mul_of_nonneg_left
    (r324LedgerThree_sum_crossCovariance_le ρ ε F hF p.2.2.2.2)
    (mul_nonneg (r324LedgerThreeLeftChain_nonneg m p)
      (r324LedgerThreeRightChain_nonneg m p))

/-! ## Pointwise factorization of the flat pure-cross fibre -/

/-- One pure-cross flat integrand: external phase times plain chains
times its cross covariance. -/
theorem r324LedgerThree_flatten_allCross_eq
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (α β : Z4)
    {e : MomentContraction m}
    (he : R324LedgerThreeAllCrossEntity e)
    (p : R324PhysicalPoint m) :
    r324Flatten
        (deterministicMomentIntegrand ρ ε m α β
          e.1 e.2.1 e.2.2) p =
      charT4 α p.1 * charT4 β p.2.1 * charT4 (-α) p.2.2.1 *
          charT4 (-β) p.2.2.2.1 *
        ((r324LedgerThreeLeftChain m p *
            r324LedgerThreeRightChain m p *
            momentCrossCovarianceProduct ρ ε m
              e.1 e.2.1 e.2.2 p.2.2.2.2 : ℝ) : ℂ) := by
  obtain ⟨π, rfl⟩ := he.eq_mk
  unfold r324Flatten deterministicMomentIntegrand
    r324LedgerThreeLeftChain r324LedgerThreeRightChain
  rw [r324LedgerThree_detIntegrand_id, r324LedgerThree_detIntegrand_id]

/-- **Exact norm of the summed pure-cross flat fibre**: the phase has
modulus one and everything else is nonnegative, so no cancellation and
no triangle inequality is involved. -/
theorem r324LedgerThree_norm_sum_flatten_eq
    (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (α β : Z4)
    {F : Finset (MomentContraction m)}
    (hF : ∀ e ∈ F, R324LedgerThreeAllCrossEntity e)
    (p : R324PhysicalPoint m) :
    ‖∑ e ∈ F,
        r324Flatten
          (deterministicMomentIntegrand ρ ε m α β
            e.1 e.2.1 e.2.2) p‖ =
      r324LedgerThreeCrossDensity ρ ε m F p := by
  have hsum :
      (∑ e ∈ F,
          r324Flatten
            (deterministicMomentIntegrand ρ ε m α β
              e.1 e.2.1 e.2.2) p) =
        charT4 α p.1 * charT4 β p.2.1 * charT4 (-α) p.2.2.1 *
            charT4 (-β) p.2.2.2.1 *
          ((r324LedgerThreeCrossDensity ρ ε m F p : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl
      (fun e he => r324LedgerThree_flatten_allCross_eq
        ρ ε α β (hF e he) p),
      ← Finset.mul_sum]
    congr 1
    unfold r324LedgerThreeCrossDensity
    push_cast
    rw [← Finset.mul_sum]
  rw [hsum, norm_mul, norm_mul, norm_mul, norm_mul, norm_charT4,
    norm_charT4, norm_charT4, norm_charT4, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (r324LedgerThreeCrossDensity_nonneg ρ ε m F p)]
  ring

/-! ## The summed pure-cross fibre as one nonnegative integral -/

/-- **Cancellation-free integral bound for a pure-cross fibre.**  The
summed fibre is one physical integral of the nonnegative pure-cross
density; only the unimodular phase is discarded.  Together with the
pointwise permanent bound this reduces the cross-case ledger to the
multi-window estimate for two plain chains against the row-sum
majorant. -/
theorem r324LedgerThree_norm_termSum_le_integral_crossDensity
    (ρ : SmoothCutoff) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    {s r : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    (hfib : R324LedgerThreeCrossFibre m s r) :
    ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ ≤
      ∫ p, r324LedgerThreeCrossDensity ρ ε m
          (momentRefinedContractionFiber m s r) p
        ∂(r324PhysicalMeasure m) := by
  have hint :
      ∀ e ∈ momentRefinedContractionFiber m s r,
        Integrable
          (fun p => r324Flatten
            (deterministicMomentIntegrand ρ ε m α β
              e.1 e.2.1 e.2.2) p)
          (r324PhysicalMeasure m) :=
    fun e _ => r324MomentIntegrable_all ρ hε hε1 α β e
  have hrepr :
      momentRefinedDeterministicTermSum ρ ε m α β s r =
        ∫ p, ∑ e ∈ momentRefinedContractionFiber m s r,
            r324Flatten
              (deterministicMomentIntegrand ρ ε m α β
                e.1 e.2.1 e.2.2) p
          ∂(r324PhysicalMeasure m) := by
    rw [integral_finsetSum _ hint]
    unfold momentRefinedDeterministicTermSum
    exact Finset.sum_congr rfl fun e _he =>
      (integral_r324Flatten_deterministicMomentIntegrand
        ρ ε m α β e
        (r324MomentIntegrable_all ρ hε hε1 α β e)).symm
  calc
    ‖momentRefinedDeterministicTermSum ρ ε m α β s r‖ =
        ‖∫ p, ∑ e ∈ momentRefinedContractionFiber m s r,
            r324Flatten
              (deterministicMomentIntegrand ρ ε m α β
                e.1 e.2.1 e.2.2) p
          ∂(r324PhysicalMeasure m)‖ := by rw [hrepr]
    _ ≤ ∫ p, ‖∑ e ∈ momentRefinedContractionFiber m s r,
            r324Flatten
              (deterministicMomentIntegrand ρ ε m α β
                e.1 e.2.1 e.2.2) p‖
          ∂(r324PhysicalMeasure m) :=
      norm_integral_le_integral_norm _
    _ = ∫ p, r324LedgerThreeCrossDensity ρ ε m
          (momentRefinedContractionFiber m s r) p
          ∂(r324PhysicalMeasure m) :=
      integral_congr_ae (Filter.Eventually.of_forall fun p =>
        r324LedgerThree_norm_sum_flatten_eq ρ ε α β hfib p)

end

end Anderson4D
