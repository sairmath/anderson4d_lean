import Anderson4D.DetParametrix.Paper42_Moment.R324AnchorSuffixCount
import Anderson4D.DetParametrix.Paper42_Moment.R324GradeLedger
import Anderson4D.DetParametrix.Paper42_Moment.R324LayerGlueCount

/-!
# Clause B, factored: the anchor lattice series and the composed theorem

`R324CentralAnchorLedger` factors into two named inputs:

* a **physical → lattice collapse** for the anchor-resolved harvest
  (`R324AnchorCollapseAt`), the analogue of
  `R324ColPhysicalCollapseAt` in the character-free case; and
* a **lattice budget with the central bracket**
  (`R324AnchorCentralBudget`), the analogue of
  `R324ColDoubledBudgetAt` / `R324ColGradedBudgetAt`, except that the
  target carries the extra factor
  `eighthOrderFrequencyDecay ‖freq (α+β)‖`,

and then assembles everything downstream: clause B
(`R324CentralAnchorLedger`), the quadruple bracket ledger, the strong
capped cross ledger, and `MainConditional`.

## The lattice series

The anchor-resolved harvest of one entity is a Green chain in each half
carrying one character per internal coordinate, so `r324Col_piChain_integral`
turns it into `r324AnchorLatWeight`: the proved symbol weight
`r324ColLatSym` times the two anchor-resolved propagator products
`r324AnchorLatProp`, whose brackets sit at the suffix sums computed in
`R324AnchorSuffixCount`.  With the external modes switched off it *is*
the proved `r324ColLatWeight` (`r324AnchorLatWeight_zero_modes`), and
the right half may be taken with the momenta un-negated because the
propagator product is even (`r324Anchor_latProp_neg`).

The configuration sector is **shifted**: momentum conservation now reads
`∑ᵢ qᵢ = -(α+β)` (`r324Anchor_key_sum_closed`), not `∑ᵢ qᵢ = 0`.  That
shift — and not any individual Green bracket — is where the conserved
mode survives the collapse, which is exactly the content of
`R324AnchorSuffixCount`.

## The composed theorem

`mainConditional_of_gradedBudget` composes

`R324CentralAnchorLedger → R324BetaQuadBracketLedger →
 R324CappedCrossLedgerStrong → MainConditional`

with clause A, in the form the graded lattice
budget delivers it (`R324ColGradedBudgetAt ρ D m r324LayerSplitGrade`,
via an explicit bridge hypothesis).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## The anchor-resolved lattice weight -/

/-- The propagator product of one anchor-resolved half chain: the
suffix-sum brackets of `r324AnchorKeys`. -/
def r324AnchorLatProp {m : ℕ} (α β : Z4) (a : ℕ) (q : Fin m → Z4) : ℝ :=
  r324ColPiProp m (r324AnchorKeys α β a (r324ColExtend q))

theorem r324AnchorLatProp_nonneg {m : ℕ} (α β : Z4) (a : ℕ)
    (q : Fin m → Z4) : 0 ≤ r324AnchorLatProp α β a q :=
  r324ColPiProp_nonneg _ _

theorem r324Anchor_colPartial_neg (f : ℕ → Z4) (n : ℕ) :
    r324ColPartial (fun j => -(f j)) n = -r324ColPartial f n := by
  unfold r324ColPartial
  rw [Finset.sum_neg_distrib]

theorem r324Anchor_colBrk_neg (b : Z4) : r324ColBrk (-b) = r324ColBrk b := by
  unfold r324ColBrk
  rw [paperModeNormSq_neg]

/-- **The propagator product is even.**  So the right half chain, whose
momenta and external modes are the negatives of the left ones, has the
same bracket product: the lattice weight below may be written with a
single sign convention. -/
theorem r324Anchor_piProp_neg : ∀ (n : ℕ) (f : ℕ → Z4),
    r324ColPiProp n (fun j => -(f j)) = r324ColPiProp n f := by
  intro n
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
      intro f
      rw [r324ColPiProp_succ, r324ColPiProp_succ,
        r324Anchor_colPartial_neg, r324Anchor_colBrk_neg]
      congr 1
      exact ih (fun j => f (j + 1))

theorem r324AnchorKeys_zero_modes (a : ℕ) (k : ℕ → Z4) :
    r324AnchorKeys 0 0 a k = k := by
  funext j
  unfold r324AnchorKeys
  simp

/-- **The lattice summand of one anchor-resolved entity**: the proved
symbol weight against the two anchor-resolved propagator products, the
left one in identity order and the right one in the order `τ`. -/
def r324AnchorLatWeight (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ} (α β : Z4)
    (aL aR : ℕ) (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) : ℝ :=
  r324ColLatSym ρ ε q *
    (r324AnchorLatProp α β aL q * r324AnchorLatProp α β aR (q ∘ τ))

theorem r324AnchorLatWeight_nonneg (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (α β : Z4) (aL aR : ℕ) (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) :
    0 ≤ r324AnchorLatWeight ρ ε α β aL aR τ q :=
  mul_nonneg (r324ColLatSym_nonneg ρ ε q)
    (mul_nonneg (r324AnchorLatProp_nonneg _ _ _ _)
      (r324AnchorLatProp_nonneg _ _ _ _))

theorem r324AnchorLatProp_zero_modes {m : ℕ} (a : ℕ) (q : Fin m → Z4) :
    r324AnchorLatProp 0 0 a q = r324ColLatProp q := by
  unfold r324AnchorLatProp r324ColLatProp
  rw [r324AnchorKeys_zero_modes]

/-- **Sanity: switching off the external modes returns the proved
lattice weight.**  So `r324AnchorLatWeight` really is the proved
`r324ColLatWeight` decorated with the two external insertions. -/
theorem r324AnchorLatWeight_zero_modes (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (aL aR : ℕ) (τ : Equiv.Perm (Fin m)) (q : Fin m → Z4) :
    r324AnchorLatWeight ρ ε 0 0 aL aR τ q = r324ColLatWeight ρ ε τ q := by
  unfold r324AnchorLatWeight r324ColLatWeight
  rw [r324AnchorLatProp_zero_modes, r324AnchorLatProp_zero_modes]

/-! ## The shifted configuration sector -/

/-- **The shifted momentum sector.**  With `α` at the head slot and `β`
at the anchor slot, momentum conservation on the closed chain reads
`∑ᵢ qᵢ = -(α+β)` (`r324Anchor_key_sum_closed`), not `∑ᵢ qᵢ = 0`.  At
`γ = 0` this is the proved `R324ColZeroSum`. -/
def R324AnchorSector (m : ℕ) (γ : Z4) : Type :=
  {q : Fin m → Z4 // ∑ i, q i = γ}

instance (m : ℕ) (γ : Z4) :
    CoeFun (R324AnchorSector m γ) (fun _ => Fin m → Z4) :=
  ⟨Subtype.val⟩

theorem r324AnchorSector_zero (m : ℕ) :
    R324AnchorSector m 0 = R324ColZeroSum m := rfl

/-! ## Anchor collapse inputs -/

/-- **The anchor collapse**, as a named Prop: the anchor-resolved
integrand is integrable and its harvest is dominated by the anchor
lattice series on the shifted sector.  It is the character-bearing analogue
of `R324ColPhysicalCollapseAt`: the four external characters ride along into
the suffix sums, one character per internal coordinate, in the form supported
by `r324Col_piChain_integral`.

The bound is stated with an existential pairing `τ` and existential
anchor indices, because the entity set `F` is summed inside the harvest
and the collapse machine consumes one entity at a time. -/
def R324AnchorCollapseAt (ρ : SmoothCutoff) (C : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    ∀ (α β : Z4) (hm : 0 < m) (F : Finset (MomentContraction m))
      (aL aR : MomentContraction m → Option (Fin m)),
      Integrable (r324CentralAnchorIntegrand ρ ε m α β hm F aL aR)
          (Measure.pi fun _ : Fin (2 * m) => paperMeasure) ∧
        ∃ (τ : Equiv.Perm (Fin m)) (bL bR : ℕ),
          ‖r324CentralAnchorHarvest ρ ε m α β hm F aL aR‖ ≤
            C ^ m * ∑' q : R324AnchorSector m (-(α + β)),
              r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4)

/-- **The central lattice budget**, as a named Prop: on the tail region
the anchor lattice series over the shifted sector carries the `ε`-free
eighth-order bracket at the conserved mode, on top of the usual
`D^m·|log ε|^{m-1}` window budget.

This is the analytic content of clause B.  `R324AnchorSuffixCount` shows
it cannot be read off the Green brackets alone (the unique suffix sum
carrying `α+β` freely is the head one, and conservation sets it to `0`),
that the `ε`-scaled symbols miss by `ε⁻¹⁶`
(`r324Central_epsScale_gap`), and that the endpoint trade needs
`⟨α⟩⁻⁸⟨β⟩⁻⁸` where only `⟨α⟩⁻⁴⟨β⟩⁻⁴` is available
(`r324Central_endpointTrade_sq`).  What the sector *does* give for free
is that the free keys must sum to `-(α+β)`, so a large conserved mode
forces a large key (`r324Anchor_conserved_le_prod_keyBrackets`); the
remaining orders have to come from combining that constraint with the
symbol decay uniformly in `ε`. -/
def R324AnchorCentralBudget (ρ : SmoothCutoff) (D : ℝ) : Prop :=
  ∀ {ε : ℝ} (m : ℕ) (α β : Z4),
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 2 ≤ m →
      m ≤ truncOrder ε →
        r324CMBracketWeight ε α β ≤ 1 →
          ∀ (τ : Equiv.Perm (Fin m)) (bL bR : ℕ),
            (Summable fun q : R324AnchorSector m (-(α + β)) =>
                r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4)) ∧
              (∑' q : R324AnchorSector m (-(α + β)),
                  r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4)) ≤
                D ^ m * |Real.log ε| ^ (m - 1) *
                  eighthOrderFrequencyDecay
                    ‖z4EuclideanFrequency (α + β)‖

/-! ## Clause B from the two inputs -/

/-- **Clause B, factored.**  The anchor collapse plus the central lattice
budget give `R324CentralAnchorLedger` with the product constant, exactly
as `r324Col_entityBoundAt_of_collapse` combines the proved
`R324ColPhysicalCollapseAt` with `R324ColDoubledBudgetAt`. -/
theorem R324CentralAnchorLedger_of_collapse_and_budget
    {ρ : SmoothCutoff} {C D : ℝ} (hC : 0 ≤ C)
    (hcol : ∀ m : ℕ, R324AnchorCollapseAt ρ C m)
    (hbud : R324AnchorCentralBudget ρ D) :
    R324CentralAnchorLedger ρ (C * D) := by
  intro ε m α β hε hε1 hlog hm2 hcap hW F hm aL aR
  obtain ⟨hint, τ, bL, bR, hle⟩ := hcol m hε hε1 α β hm F aL aR
  refine ⟨hint, ?_⟩
  obtain ⟨_hsum, hbound⟩ := hbud m α β hε hε1 hlog hm2 hcap hW τ bL bR
  have hCm : (0 : ℝ) ≤ C ^ m := pow_nonneg hC m
  calc
    ‖r324CentralAnchorHarvest ρ ε m α β hm F aL aR‖ ≤
        C ^ m * ∑' q : R324AnchorSector m (-(α + β)),
          r324AnchorLatWeight ρ ε α β bL bR τ (q : Fin m → Z4) := hle
    _ ≤ C ^ m * (D ^ m * |Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖) :=
      mul_le_mul_of_nonneg_left hbound hCm
    _ = (C * D) ^ m * |Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ := by
      rw [mul_pow]; ring

/-! ## Monotonicity of the two clauses in the budget constant -/

theorem R324CappedDensityLedger_mono {ρ : SmoothCutoff} {K K' : ℝ}
    (hK : 0 ≤ K) (hKK : K ≤ K') (h : R324CappedDensityLedger ρ K) :
    R324CappedDensityLedger ρ K' := by
  intro ε m hε hε1 hlog hm2 hcap F
  refine (h m hε hε1 hlog hm2 hcap F).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK hKK m)
    (pow_nonneg (abs_nonneg _) _)

theorem R324CentralAnchorLedger_mono {ρ : SmoothCutoff} {K K' : ℝ}
    (hK : 0 ≤ K) (hKK : K ≤ K') (h : R324CentralAnchorLedger ρ K) :
    R324CentralAnchorLedger ρ K' := by
  intro ε m α β hε hε1 hlog hm2 hcap hW F hm aL aR
  obtain ⟨hint, hb⟩ := h m α β hε hε1 hlog hm2 hcap hW F hm aL aR
  refine ⟨hint, hb.trans ?_⟩
  have hnn : (0 : ℝ) ≤ |Real.log ε| ^ (m - 1) *
      eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _)
      (eighthOrderFrequencyDecay_nonneg _)
  calc
    K ^ m * |Real.log ε| ^ (m - 1) *
        eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ =
        K ^ m * (|Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖) := by ring
    _ ≤ K' ^ m * (|Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK hKK m) hnn
    _ = K' ^ m * |Real.log ε| ^ (m - 1) *
          eighthOrderFrequencyDecay ‖z4EuclideanFrequency (α + β)‖ := by ring

/-! ## The strong capped ledger and `MainConditional` -/

/-- **The strong capped cross ledger from the grading and tail estimates.**  Clause A
is `R324CappedDensityLedger`; clause B, on the tail region, is
`R324CentralAnchorLedger`.  They compose through
`R324BetaQuadBracketLedger_of_centralAnchor` then
`R324CappedCrossLedgerStrong_of_quadBracket`. -/
theorem R324CappedCrossLedgerStrong_of_clauses
    {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (hA : R324CappedDensityLedger ρ K)
    (hB : R324CentralAnchorLedger ρ K) :
    R324CappedCrossLedgerStrong ρ (4 * K) := by
  have hK4 : (0 : ℝ) ≤ 4 * K := by linarith
  have hKle : K ≤ 4 * K := by linarith
  have hA4 : R324CappedDensityLedger ρ (4 * K) :=
    R324CappedDensityLedger_mono hK hKle hA
  have hquad : R324BetaQuadBracketLedger ρ (4 * K) :=
    R324BetaQuadBracketLedger_of_centralAnchor hK hB
  exact R324CappedCrossLedgerStrong_of_quadBracket hK4 hA4 hquad

/-- **The two clauses close the theorem.**  Clause A plus the
central-anchor clause B give `MainConditional` through
`mainConditional_of_cappedCrossLedgerStrong`. -/
theorem mainConditional_of_clauses
    {M : NoiseModel} {ρ : SmoothCutoff} {K : ℝ} (hK : 0 ≤ K)
    (hA : R324CappedDensityLedger ρ K)
    (hB : R324CentralAnchorLedger ρ K) :
    MainConditional M ρ :=
  mainConditional_of_cappedCrossLedgerStrong
    ⟨4 * K, by linarith, R324CappedCrossLedgerStrong_of_clauses hK hA hB⟩

/-- **Conditional assembly from the graded lattice budget and the two
anchor inputs.**

`hbridge` is clause A in the form the graded lattice budget delivers it;
`hcol` and `hbud` are the two named inputs of clause B isolated above.
Given those, `MainConditional M ρ` holds. -/
theorem mainConditional_of_gradedBudget
    {M : NoiseModel} {ρ : SmoothCutoff} {C D E K : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hgrade : ∀ m : ℕ, R324ColGradedBudgetAt ρ D m r324LayerSplitGrade)
    (hbridge : (∀ m : ℕ, R324ColGradedBudgetAt ρ D m r324LayerSplitGrade) →
      R324CappedDensityLedger ρ K)
    (hcol : ∀ m : ℕ, R324AnchorCollapseAt ρ C m)
    (hbud : R324AnchorCentralBudget ρ E) :
    MainConditional M ρ := by
  have hA : R324CappedDensityLedger ρ K := hbridge hgrade
  have hB : R324CentralAnchorLedger ρ (C * E) :=
    R324CentralAnchorLedger_of_collapse_and_budget hC hcol hbud
  have hCE : (0 : ℝ) ≤ C * E := mul_nonneg hC hE
  have hmax : (0 : ℝ) ≤ max K (C * E) := le_trans hK (le_max_left _ _)
  exact mainConditional_of_clauses hmax
    (R324CappedDensityLedger_mono hK (le_max_left _ _) hA)
    (R324CentralAnchorLedger_mono hCE (le_max_right _ _) hB)

end

end Anderson4D
