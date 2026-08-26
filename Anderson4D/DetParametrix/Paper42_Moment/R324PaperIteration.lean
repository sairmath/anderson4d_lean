import Anderson4D.DetParametrix.Paper42_Moment.R324PaperStep1
import Anderson4D.DetParametrix.Paper41_Renorm.R322OneBlockCollapse
import Anderson4D.DetParametrix.Paper42_Moment.R324IntegratedCollapseClosure
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticReachableIntegrability
import Anderson4D.DetParametrix.Paper41_Renorm.R322AnalyticPrimitiveCertificate

/-!
# Paper §4.2: the successive removal of the fully paired subintervals

Paper: R-324 — §4.1 successive removal (4.13), as used by §4.2

This file transcribes the one move that both Step 1 and Step 2 of
§4.2 of arXiv:2607.10105v1 take over verbatim from §4.1:

> we can reduce the integral (4.16) by successively removing the fully
> paired subintervals `[ℓ_i, r_i]` … Each such reduction, using
> Proposition 4.1, gains a power of `Cλ` and replaces the contribution of
> `[ℓ_i, r_i]` by a new input function `H` satisfying `|H(z)| ≲ |z|⁻²`.

(the last clause is (4.13)), until only a primitive pairing remains.

## What is proved

* `exists_r324RemovalInput_le` — the iteration itself, by induction on the
  schedule.  One removal is Proposition 4.1 on the removed subinterval
  (`proposition41_at_truncation`: `J_{2k,prim} ∈ 𝓔` and (4.3)) followed by
  the §4.1 one-block collapse (`exists_r322Collapse_le`).  Iterating gives
  `|H(x)| ≤ A (Cλ)^{#removed} |x|⁻²` with `#removed = Σ_i (r_i - ℓ_i + 1)`.
* `exists_r324ReducedInput_admissible` — (4.13) on **one chain slot**: the
  surviving input divided by the gained factor is literally an
  `IsAdmissiblePrimitiveInput` entry.  Slot-local, position-free; this is
  the form Step 2 consumes.
* `exists_r324PaperIteration` — the same for the `2p-1` slots of a
  surviving primitive pairing `κ_*` on `2p` sites, with the total gained
  factor `∏_j (Cλ)^{#removed on slot j} = (Cλ)^{#removed}`.
* `exists_r324Step1Reduction_of_removal` — discharges the single named
  residual `R324Step1Reduction` of `R324PaperStep1.lean`, and
  `exists_r324Step1_removal_bound` composes it with
  `exists_r324Step1_deterministic_bound` to give `(3.24)` with `1` on the
  right for the amplitude the removal produces.

## Relation to the closed R-322 chain

The **analytic** content transfers verbatim: `exists_r322Collapse_le`
(one collapse), `r322Collapse_memE`, `measurable_r322Collapse`,
`normalizedOffDiagonalRepresentative_{memE,le,admissible}` and
`proposition41_at_truncation` are used unchanged.  What does *not*
transfer is the R-322 **wrapper**: `exists_r322RenormFiberReductionOutputAE`
and `exists_renormC_bound_of_reduction_ae` are indexed by §4.1's
counterterm constant `renormC2q` (through `detJ`, `endpointFiberDetJSum`,
`nonSplitReductionEndpointSignatures` and the `R322ExtractionStep`
schedule), not by the order-`m` deterministic fibre of (4.16); the same is
true of `R322AnalyticStage` / `r322Iterate` / `exists_r322Iterate_le`,
whose stages are already-summed §4.1 coordinates carrying no interval data.
The iteration below is therefore proved directly by induction on
the list of removed subintervals, exactly as the paper describes, with
`R324RemovedInterval` carrying no scale, coupling, or interval position.

## How Step 2 instantiates this

Step 2 works with a full pairing `κ'` of `[1,2m]` and removes the fully
paired subintervals extracted inside `[1,m]` and inside `[m+1,2m]`.  Since
`R324RemovedInterval` records only a subinterval's half-length and its
admissible interior inputs, and `r324RemovalInput` acts on a single chain
slot, Step 2 applies `exists_r324ReducedInput_admissible` once per
surviving slot of `Ĩ₀ = [1,2m] \ ∪ I_i`, feeding it the list of
subintervals removed on that slot (from either half — Definition 3.1's
subintervals never straddle the cut, so no separate treatment is needed).
The conclusions assemble into the admissible inputs of `κ₀` at whatever
index shape (4.18)'s `2m+4`-fold integral uses, and the gained factors
multiply to `(Cλ)^{#removed}` by `Finset.prod_pow_eq_pow_sum` exactly as in
`exists_r324PaperIteration`.  Absolute values are taken only afterwards,
which is (4.19).
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory

/-! ## One fully paired subinterval -/

/-- One fully paired subinterval `I_i = [ℓ_i, r_i]` scheduled for removal.

The paper's Definition 3.1 / Proposition 3.2 extraction guarantees that
the pairing induced on `I_i` is a *primitive full* pairing; so the only
data the removal consumes is the half-length `order` (the interval has
`2 * order` sites) together with the `2 * order - 1` chain inputs carried
by its interior edges, which are admissible in the sense of
Proposition 4.1.

The structure carries no scale, coupling, or interval position: exactly
the same object is used by Step 1 (subintervals of `[1,m]`) and by Step 2
(subintervals inside `[1,m]` and inside `[m+1,2m]` of a full pairing of
`[1,2m]`). -/
structure R324RemovedInterval where
  /-- Half the number of sites of `[ℓ_i, r_i]`. -/
  order : ℕ
  one_le_order : 1 ≤ order
  /-- The chain inputs `G_j` carried by the interior of `[ℓ_i, r_i]`. -/
  inputs : Fin (2 * order - 1) → T4 → ℝ
  measurable_inputs : ∀ j, Measurable (inputs j)
  admissible : IsAdmissiblePrimitiveInput order inputs

namespace R324RemovedInterval

/-- The primitive kernel `J_{2k,prim}` of the removed subinterval: the
object Proposition 4.1 estimates. -/
def kernel (I : R324RemovedInterval) (ρ : SmoothCutoff) (lam ε : ℝ) :
    T4 → ℝ :=
  primitiveKernelDiff ρ lam ε I.order I.one_le_order I.inputs

theorem measurable_kernel (I : R324RemovedInterval) (ρ : SmoothCutoff)
    (lam ε : ℝ) : Measurable (I.kernel ρ lam ε) :=
  measurable_primitiveKernelDiff ρ lam ε I.order I.one_le_order
    I.inputs I.measurable_inputs

/-- The removed interval's primitive kernel is in `𝓔`; this is the part
of Proposition 4.1 that needs no scale regime. -/
theorem memE_kernel (I : R324RemovedInterval) (ρ : SmoothCutoff)
    (lam ε : ℝ) : MemEClassT4 (I.kernel ρ lam ε) :=
  primitiveKernelDiff_memE ρ lam ε I.order I.one_le_order I.inputs
    I.admissible.1

end R324RemovedInterval

/-- The paper's `#removed`: the number of sites deleted by the schedule
`Is`, namely `Σ_i (r_i - ℓ_i + 1) = 2 Σ_i k_i`. -/
def r324RemovedSites (Is : List R324RemovedInterval) : ℕ :=
  2 * (Is.map R324RemovedInterval.order).sum

@[simp] theorem r324RemovedSites_nil : r324RemovedSites [] = 0 := by
  simp [r324RemovedSites]

theorem r324RemovedSites_cons (I : R324RemovedInterval)
    (Is : List R324RemovedInterval) :
    r324RemovedSites (I :: Is) = 2 * I.order + r324RemovedSites Is := by
  simp only [r324RemovedSites, List.map_cons, List.sum_cons]
  ring

/-! ## The successive removal, at the level of the chain input -/

/-- **The successive removal (4.13).**

Starting from the incoming Green leg `Gp` of the chain slot, remove the
scheduled subintervals one after another.  Each removal replaces the
current input by the paper's `H`, the one-block collapse (4.8) of the
current input against the primitive kernel of the removed interval and
the outgoing Green leg.  `r324RemovalInput ρ lam ε Gp Is` is the input
function surviving on that slot after the whole schedule `Is`. -/
def r324RemovalInput (ρ : SmoothCutoff) (lam ε : ℝ) (Gp : T4 → ℝ) :
    List R324RemovedInterval → T4 → ℝ
  | [] => Gp
  | I :: Is =>
      r324RemovalInput ρ lam ε
        (r322Collapse Gp (I.kernel ρ lam ε) greenFn) Is

@[simp] theorem r324RemovalInput_nil (ρ : SmoothCutoff) (lam ε : ℝ)
    (Gp : T4 → ℝ) : r324RemovalInput ρ lam ε Gp [] = Gp := rfl

theorem r324RemovalInput_cons (ρ : SmoothCutoff) (lam ε : ℝ)
    (Gp : T4 → ℝ) (I : R324RemovedInterval)
    (Is : List R324RemovedInterval) :
    r324RemovalInput ρ lam ε Gp (I :: Is) =
      r324RemovalInput ρ lam ε
        (r322Collapse Gp (I.kernel ρ lam ε) greenFn) Is := rfl

/-- The exact Fubini licences consumed by the schedule: one per removal,
stated on the input reached at that stage. -/
def R324RemovalIntegrable (ρ : SmoothCutoff) (lam ε : ℝ) (Gp : T4 → ℝ) :
    List R324RemovedInterval → Prop
  | [] => True
  | I :: Is =>
      (∀ x, Integrable
        (r322CollapseIntegrand Gp (I.kernel ρ lam ε) greenFn x)
        (paperMeasure.prod paperMeasure)) ∧
      R324RemovalIntegrable ρ lam ε
        (r322Collapse Gp (I.kernel ρ lam ε) greenFn) Is

/-! ## Structural stability of the removal -/

/-- Every removal stays inside the symmetry class `𝓔`. -/
theorem r324RemovalInput_memE (ρ : SmoothCutoff) (lam ε : ℝ) :
    ∀ (Is : List R324RemovedInterval) {Gp : T4 → ℝ},
      MemEClassT4 Gp → MemEClassT4 (r324RemovalInput ρ lam ε Gp Is)
  | [], _, hGp => hGp
  | I :: Is, _, hGp =>
      r324RemovalInput_memE ρ lam ε Is
        (r322Collapse_memE hGp (I.memE_kernel ρ lam ε) greenFn_memE)

/-- Every removal stays measurable. -/
theorem r324RemovalInput_measurable (ρ : SmoothCutoff) (lam ε : ℝ) :
    ∀ (Is : List R324RemovedInterval) {Gp : T4 → ℝ},
      Measurable Gp → Measurable (r324RemovalInput ρ lam ε Gp Is)
  | [], _, hGp => hGp
  | I :: Is, _, hGp =>
      r324RemovalInput_measurable ρ lam ε Is
        (measurable_r322Collapse hGp (I.measurable_kernel ρ lam ε)
          measurable_greenFn)

/-! ## The quantitative iteration: `(Cλ)^{#removed}` and `|H(z)| ≲ |z|⁻²` -/

/-- The universal one-block collapse constant of §4.1 is absorbed into the
base of the paper's power `(Cλ)^{#removed}`: each removal deletes at least
two sites, so one factor `K` per removal is paid by the exponent. -/
private theorem r324RemovalStepConstant_le {C lam K : ℝ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) {k : ℕ} (hk : 1 ≤ k) :
    (C * lam) ^ (2 * k) * K ≤ ((C * max K 1) * lam) ^ (2 * k) := by
  have hK1 : (1 : ℝ) ≤ max K 1 := le_max_right _ _
  have hbase : (0 : ℝ) ≤ (C * lam) ^ (2 * k) := by positivity
  have hpow : max K 1 ≤ (max K 1) ^ (2 * k) := by
    calc max K 1 = (max K 1) ^ 1 := (pow_one _).symm
      _ ≤ (max K 1) ^ (2 * k) := pow_le_pow_right₀ hK1 (by omega)
  calc (C * lam) ^ (2 * k) * K
      ≤ (C * lam) ^ (2 * k) * (max K 1) ^ (2 * k) :=
        mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hpow) hbase
    _ = ((C * max K 1) * lam) ^ (2 * k) := by
        rw [show (C * max K 1) * lam = (C * lam) * (max K 1) by ring,
          ← mul_pow]

/-- **The successive removal, quantitatively.**

This is the paper's sentence, in Lean: removing the scheduled fully paired
subintervals *gains a power of `Cλ`* — exactly one per deleted site, i.e.
`(Cλ)^{#removed}` in total — and *replaces the removed contribution by a
new input function `H` satisfying `|H(z)| ≲ |z|⁻²`*, which is (4.13).

Each individual removal is Proposition 4.1 (`proposition41_at_truncation`,
supplying `J_{2k,prim} ∈ 𝓔` and (4.3)) followed by the §4.1 one-block
collapse estimate (`exists_r322Collapse_le`).  The single constant `Citer`
is chosen before the coupling, the scale, the schedule, and the inputs. -/
theorem exists_r324RemovalInput_le (ρ : SmoothCutoff) :
    ∃ Citer : ℝ, 0 < Citer ∧
      ∀ (lam ε A : ℝ) (Gp : T4 → ℝ) (Is : List R324RemovedInterval)
        (x : T4),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 0 ≤ A → x ≠ 0 →
        (∀ I ∈ Is, I.order ≤ truncOrder ε) →
        (∀ z, z ≠ 0 → |Gp z| ≤ A * invSqKer z) →
        R324RemovalIntegrable ρ lam ε Gp Is →
        |r324RemovalInput ρ lam ε Gp Is x| ≤
          A * (Citer * lam) ^ r324RemovedSites Is * invSqKer x := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨K, hK, hcollapse⟩ := exists_r322Collapse_le hsupport
  refine ⟨C * max K 1, by positivity, ?_⟩
  intro lam ε A Gp Is
  induction Is generalizing A Gp with
  | nil =>
      intro x _hlam _hε _hε1 _hlog _hA hx _htrunc hGp _hint
      simpa using hGp x hx
  | cons I Is ih =>
      intro x hlam hε hε1 hlog hA hx htrunc hGp hint
      have hItrunc : I.order ≤ truncOrder ε := htrunc I (by simp)
      have hbounds :=
        (hprop lam ε I.order I.one_le_order I.inputs hlam hε hε1
          hItrunc I.admissible).2.2
      have hstep :
          ∀ z, z ≠ 0 →
            |r322Collapse Gp (I.kernel ρ lam ε) greenFn z| ≤
              (A * ((C * max K 1) * lam) ^ (2 * I.order)) * invSqKer z := by
        intro z hz
        refine (hcollapse C lam ε A I.order Gp (I.kernel ρ lam ε) z
          hC.le hlam.le hA hε hε1 hlog hz (I.measurable_kernel ρ lam ε)
          (I.memE_kernel ρ lam ε) (fun u => (hbounds u).1) hGp
          (hint.1 z)).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (invSqKer_nonneg z)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (r324RemovalStepConstant_le hC.le hlam.le I.one_le_order) hA
      have htail :=
        ih (A := A * ((C * max K 1) * lam) ^ (2 * I.order))
          (Gp := r322Collapse Gp (I.kernel ρ lam ε) greenFn) x hlam hε hε1
          hlog (by positivity) hx
          (fun J hJ => htrunc J (by simp [hJ])) hstep hint.2
      rw [r324RemovalInput_cons]
      refine htail.trans (le_of_eq ?_)
      rw [r324RemovedSites_cons, pow_add]
      ring

/-! ## The surviving primitive pairing and its admissible inputs -/

/-- The factor gained on one chain slot by its removals: the paper's
`(Cλ)^{#removed}`. -/
def r324RemovalScale (Citer lam : ℝ) (Is : List R324RemovedInterval) : ℝ :=
  (Citer * lam) ^ r324RemovedSites Is

theorem r324RemovalScale_pos {Citer lam : ℝ} (hCiter : 0 < Citer)
    (hlam : 0 < lam) (Is : List R324RemovedInterval) :
    0 < r324RemovalScale Citer lam Is := by
  unfold r324RemovalScale; positivity

/-- **The new input function `H` of (4.13)**, normalized by the gained
factor so that it is literally an admissible Proposition 4.1 input. -/
def r324ReducedInput (ρ : SmoothCutoff) (lam ε Citer : ℝ) (Gp : T4 → ℝ)
    (Is : List R324RemovedInterval) : T4 → ℝ :=
  normalizedOffDiagonalRepresentative (r324RemovalScale Citer lam Is)
    (r324RemovalInput ρ lam ε Gp Is)

private theorem measurable_normalizedOffDiagonalRepresentative {c : ℝ}
    {f : T4 → ℝ} (hf : Measurable f) :
    Measurable (normalizedOffDiagonalRepresentative c f) := by
  unfold normalizedOffDiagonalRepresentative
  exact measurable_const.mul (measurable_offDiagonalRepresentative hf)

theorem measurable_r324ReducedInput (ρ : SmoothCutoff) (lam ε Citer : ℝ)
    {Gp : T4 → ℝ} (hGp : Measurable Gp) (Is : List R324RemovedInterval) :
    Measurable (r324ReducedInput ρ lam ε Citer Gp Is) :=
  measurable_normalizedOffDiagonalRepresentative
    (r324RemovalInput_measurable ρ lam ε Is hGp)

/-- **(4.13) on one chain slot: the paper's `H`.**

`Gp` is the Green leg entering the slot and `Is` the schedule of fully
paired subintervals removed on it.  The surviving input, divided by the
factor `(Cλ)^{#removed}` gained by those removals, is an admissible
Proposition 4.1 input: it lies in `𝓔` and obeys `|H(z)| ≤ |z|⁻²`.

Nothing in the statement refers to the position of the slot, to the
positions of the removed subintervals, or to the ambient pairing.  This is
therefore the form **Step 2** consumes: for a full pairing of `[1,2m]`,
apply it once per surviving chain slot, with `Is` listing the fully paired
subintervals extracted inside `[1,m]` and, independently, those extracted
inside `[m+1,2m]` — the two halves need no separate treatment because the
subintervals of Definition 3.1 never straddle the cut.  Assembling the
per-slot conclusions with `IsAdmissiblePrimitiveInput`'s definition
(`(∀ j, MemEClassT4 (G j)) ∧ ∀ j z, |G j z| ≤ invSqKer z`) gives the
admissible inputs of the surviving pairing `κ₀` on `Ĩ₀`, at whatever index
shape Step 2's `2m+4`-fold integral (4.18) uses; the total gained factor is
`∏_slots (Cλ)^{#removed on slot}`, which is `(Cλ)^{#removed}`. -/
theorem exists_r324ReducedInput_admissible (ρ : SmoothCutoff) :
    ∃ Citer : ℝ, 0 < Citer ∧
      ∀ (lam ε : ℝ) (Gp : T4 → ℝ) (Is : List R324RemovedInterval),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        MemEClassT4 Gp → Measurable Gp →
        (∀ z, |Gp z| ≤ invSqKer z) →
        (∀ I ∈ Is, I.order ≤ truncOrder ε) →
        R324RemovalIntegrable ρ lam ε Gp Is →
          MemEClassT4 (r324ReducedInput ρ lam ε Citer Gp Is) ∧
            Measurable (r324ReducedInput ρ lam ε Citer Gp Is) ∧
            (∀ z, |r324ReducedInput ρ lam ε Citer Gp Is z| ≤
              invSqKer z) := by
  obtain ⟨Citer, hCiter, hiter⟩ := exists_r324RemovalInput_le ρ
  refine ⟨Citer, hCiter, ?_⟩
  intro lam ε Gp Is hlam hε hε1 hlog hmem hmeas hGp htrunc hint
  refine ⟨normalizedOffDiagonalRepresentative_memE _
      (r324RemovalInput_memE ρ lam ε Is hmem),
    measurable_r324ReducedInput ρ lam ε Citer hmeas Is, ?_⟩
  refine normalizedOffDiagonalRepresentative_le
    (r324RemovalScale_pos hCiter hlam Is) ?_
  intro z hz
  simpa [r324RemovalScale] using
    hiter lam ε 1 Gp Is z hlam hε hε1 hlog zero_le_one hz htrunc
      (fun u _hu => by simpa using hGp u) hint

/-- **The output of the successive removal.**

After the whole schedule the surviving chain inputs are again admissible
inputs for Proposition 4.1 — this is (4.13) — and the total factor gained
is `∏_j (Cλ)^{#removed on slot j} = (Cλ)^{#removed}`.

The chain slots are indexed by `Fin (2 * p - 1)`, so the conclusion is
exactly the hypothesis under which the surviving *primitive* pairing
`κ_*` on `2p` sites may be fed back into Proposition 4.1. -/
theorem exists_r324PaperIteration (ρ : SmoothCutoff) :
    ∃ Citer : ℝ, 0 < Citer ∧
      ∀ (lam ε : ℝ) (p : ℕ) (Gp : Fin (2 * p - 1) → T4 → ℝ)
        (Is : Fin (2 * p - 1) → List R324RemovedInterval),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        IsAdmissiblePrimitiveInput p Gp →
        (∀ j, Measurable (Gp j)) →
        (∀ j, ∀ I ∈ Is j, I.order ≤ truncOrder ε) →
        (∀ j, R324RemovalIntegrable ρ lam ε (Gp j) (Is j)) →
          IsAdmissiblePrimitiveInput p
              (fun j => r324ReducedInput ρ lam ε Citer (Gp j) (Is j)) ∧
            (∀ j, Measurable
              (r324ReducedInput ρ lam ε Citer (Gp j) (Is j))) ∧
            ∏ j, r324RemovalScale Citer lam (Is j) =
              (Citer * lam) ^ ∑ j, r324RemovedSites (Is j) := by
  obtain ⟨Citer, hCiter, hslot⟩ := exists_r324ReducedInput_admissible ρ
  refine ⟨Citer, hCiter, ?_⟩
  intro lam ε p Gp Is hlam hε hε1 hlog hGp hGpmeas htrunc hint
  have hj := fun j => hslot lam ε (Gp j) (Is j) hlam hε hε1 hlog (hGp.1 j)
    (hGpmeas j) (hGp.2 j) (htrunc j) (hint j)
  refine ⟨⟨fun j => (hj j).1, fun j z => (hj j).2.2 z⟩,
    fun j => (hj j).2.1, ?_⟩
  simp only [r324RemovalScale]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-! ## Integrability of the surviving primitive kernel -/

/-- Proposition 4.1's ordinary majorant (4.3) makes the surviving
primitive kernel integrable.  Measurability is supplied by the removal. -/
theorem integrable_primitiveKernelDiff_of_bounds (ρ : SmoothCutoff)
    (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j)) (hε : 0 < ε)
    (supportConstant C : ℝ)
    (hbound : PrimitiveKernelBounds ρ lam ε n hn G supportConstant C) :
    Integrable (primitiveKernelDiff ρ lam ε n hn G) paperMeasure := by
  have hmeas := measurable_primitiveKernelDiff ρ lam ε n hn G hGmeas
  have hmajor :=
    integrable_primitiveKernelMajorant C lam ε supportConstant n hε
  refine Integrable.mono' hmajor hmeas.aestronglyMeasurable
    (.of_forall fun u => ?_)
  have hpoint := (hbound u).1
  have hnn : 0 ≤ primitiveKernelMajorant C lam ε supportConstant n u :=
    (abs_nonneg _).trans hpoint
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using hpoint

/-- The `cos - 1` weighted primitive kernel is integrable: the multiplier
has norm at most two. -/
theorem integrable_primitiveKernelDiff_mul_characterCosSubOne
    (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (G : Fin (2 * n - 1) → T4 → ℝ) (hGmeas : ∀ j, Measurable (G j))
    (hε : 0 < ε) (supportConstant C : ℝ)
    (hbound : PrimitiveKernelBounds ρ lam ε n hn G supportConstant C)
    (β : Z4) :
    Integrable
      (fun u => primitiveKernelDiff ρ lam ε n hn G u *
        (r324CharacterCos β u - 1)) paperMeasure := by
  have hkernel := integrable_primitiveKernelDiff_of_bounds ρ lam ε n hn G
    hGmeas hε supportConstant C hbound
  have hweight : Measurable fun u : T4 => r324CharacterCos β u - 1 :=
    (Complex.measurable_re.comp (continuous_charT4 β).measurable).sub
      measurable_const
  refine hkernel.mul_bdd (c := 2) hweight.aestronglyMeasurable
    (.of_forall fun u => ?_)
  have hre : ‖(charT4 β u).re‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, norm_charT4] using
      Complex.abs_re_le_norm (charT4 β u)
  unfold r324CharacterCos
  calc ‖(charT4 β u).re - 1‖ ≤ ‖(charT4 β u).re‖ + ‖(1 : ℝ)‖ :=
        norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hre (by norm_num)
    _ = 2 := by norm_num

/-- The `sin` weighted primitive kernel is integrable: the multiplier has
norm at most one.  This is the premise for the `𝓔`-symmetry cancellation
of the imaginary part. -/
theorem integrable_primitiveKernelDiff_mul_characterSin (ρ : SmoothCutoff)
    (lam ε : ℝ) (n : ℕ) (hn : 1 ≤ n) (G : Fin (2 * n - 1) → T4 → ℝ)
    (hGmeas : ∀ j, Measurable (G j)) (hε : 0 < ε)
    (supportConstant C : ℝ)
    (hbound : PrimitiveKernelBounds ρ lam ε n hn G supportConstant C)
    (β : Z4) :
    Integrable
      (fun u => primitiveKernelDiff ρ lam ε n hn G u *
        r324CharacterSin β u) paperMeasure := by
  have hkernel := integrable_primitiveKernelDiff_of_bounds ρ lam ε n hn G
    hGmeas hε supportConstant C hbound
  have hweight : Measurable (r324CharacterSin β) :=
    Complex.measurable_im.comp (continuous_charT4 β).measurable
  refine hkernel.mul_bdd (c := 1) hweight.aestronglyMeasurable
    (.of_forall fun u => ?_)
  unfold r324CharacterSin
  simpa only [Real.norm_eq_abs, norm_charT4] using
    Complex.abs_im_le_norm (charT4 β u)

/-! ## Step 1's residual `R324Step1Reduction`, discharged -/

/-- The amplitude produced by the successive removal: the paper's (4.17),
namely the gained factor `(Cλ)^{#removed}` times the four-fold integral in
`(x_a, x_m, x, y)` carrying the surviving primitive kernel `J_{2p,prim}`
built from the new inputs `H`. -/
def r324RemovalAmplitude (ρ : SmoothCutoff) (lam ε Citer : ℝ) (p : ℕ)
    (hp : 1 ≤ p) (α β : Z4) (Gp : Fin (2 * p - 1) → T4 → ℝ)
    (Is : Fin (2 * p - 1) → List R324RemovedInterval) : ℂ :=
  (((∏ j, r324RemovalScale Citer lam (Is j)) : ℝ) : ℂ) *
    r324Step1Integral (primitiveKernelDiff ρ lam ε p hp
      (fun j => r324ReducedInput ρ lam ε Citer (Gp j) (Is j))) α β

/-- `R324Step1Reduction` only constrains the *norm* of its amplitude. -/
theorem R324Step1Reduction.mono {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ}
    {α β : Z4} {Cred : ℝ} {P Q : ℂ}
    (h : R324Step1Reduction ρ lam ε m α β Cred Q) (hPQ : ‖P‖ ≤ ‖Q‖) :
    R324Step1Reduction ρ lam ε m α β Cred P := by
  obtain ⟨p, hp, G, hpm, hptrunc, hadm, hcos, hsin, hbound⟩ := h
  exact ⟨p, hp, G, hpm, hptrunc, hadm, hcos, hsin, hPQ.trans hbound⟩

/-- **The one input Step 1 takes from §4.1, proved.**

For the amplitude actually produced by the successive removal, the
hypothesis `R324Step1Reduction` of `R324PaperStep1.lean` holds: the
surviving pairing is primitive on `2p` sites, its inputs are the new
functions `H` of (4.13) — admissible for Proposition 4.1 — the two
Bochner premises of the `𝓔`-symmetry cancellation hold, and the gained
factor is exactly `(Cλ)^{m-2p}`. -/
theorem exists_r324Step1Reduction_of_removal (ρ : SmoothCutoff) :
    ∃ Citer : ℝ, 0 < Citer ∧
      ∀ (lam ε : ℝ) (m p : ℕ) (hp : 1 ≤ p) (α β : Z4)
        (Gp : Fin (2 * p - 1) → T4 → ℝ)
        (Is : Fin (2 * p - 1) → List R324RemovedInterval),
        0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
        2 * p ≤ m → p ≤ truncOrder ε →
        (∑ j, r324RemovedSites (Is j)) = m - 2 * p →
        IsAdmissiblePrimitiveInput p Gp →
        (∀ j, Measurable (Gp j)) →
        (∀ j, ∀ I ∈ Is j, I.order ≤ truncOrder ε) →
        (∀ j, R324RemovalIntegrable ρ lam ε (Gp j) (Is j)) →
          R324Step1Reduction ρ lam ε m α β Citer
            (r324RemovalAmplitude ρ lam ε Citer p hp α β Gp Is) := by
  obtain ⟨supportConstant, C, _hsupport, _hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨Citer, hCiter, hiter⟩ := exists_r324PaperIteration ρ
  refine ⟨Citer, hCiter, ?_⟩
  intro lam ε m p hp α β Gp Is hlam hε hε1 hlog hpm hptrunc hsum hGp
    hGpmeas htrunc hint
  obtain ⟨hadm, hmeas, hprod⟩ :=
    hiter lam ε p Gp Is hlam hε hε1 hlog hGp hGpmeas htrunc hint
  set G : Fin (2 * p - 1) → T4 → ℝ :=
    fun j => r324ReducedInput ρ lam ε Citer (Gp j) (Is j) with hGdef
  have hbounds := (hprop lam ε p hp G hlam hε hε1 hptrunc hadm).2.2
  refine ⟨p, hp, G, hpm, hptrunc, hadm,
    integrable_primitiveKernelDiff_mul_characterCosSubOne ρ lam ε p hp G
      hmeas hε supportConstant C hbounds β,
    integrable_primitiveKernelDiff_mul_characterSin ρ lam ε p hp G
      hmeas hε supportConstant C hbounds β, ?_⟩
  have hnn : 0 ≤ ∏ j, r324RemovalScale Citer lam (Is j) :=
    Finset.prod_nonneg fun j _ => (r324RemovalScale_pos hCiter hlam (Is j)).le
  unfold r324RemovalAmplitude
  rw [← hGdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hnn, hprod, hsum]

/-- **Step 1 of §4.2, unconditional on the removal output.**

Composing the successive removal with the five remaining moves of Step 1
(`exists_r324Step1_deterministic_bound`) gives the paper's

`|P̂_m(α,β)| ≤ (Cλ)^m |log ε|⁻¹`,

which is (3.24) with `1` on the right-hand side, for the amplitude the
removal actually produces.  Any deterministic fibre dominated in norm by
that amplitude inherits the bound through `R324Step1Reduction.mono`. -/
theorem exists_r324Step1_removal_bound (ρ : SmoothCutoff) :
    ∃ Cdet : ℝ, 0 < Cdet ∧
      ∃ Citer : ℝ, 0 < Citer ∧
        ∀ (lam ε : ℝ) (m p : ℕ) (hp : 1 ≤ p) (α β : Z4) (P : ℂ)
          (Gp : Fin (2 * p - 1) → T4 → ℝ)
          (Is : Fin (2 * p - 1) → List R324RemovedInterval),
          0 < lam → 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
          2 * p ≤ m → p ≤ truncOrder ε →
          (∑ j, r324RemovedSites (Is j)) = m - 2 * p →
          IsAdmissiblePrimitiveInput p Gp →
          (∀ j, Measurable (Gp j)) →
          (∀ j, ∀ I ∈ Is j, I.order ≤ truncOrder ε) →
          (∀ j, R324RemovalIntegrable ρ lam ε (Gp j) (Is j)) →
          ‖P‖ ≤ ‖r324RemovalAmplitude ρ lam ε Citer p hp α β Gp Is‖ →
            ‖P‖ ≤ (Cdet * lam) ^ m / |Real.log ε| := by
  obtain ⟨Citer, hCiter, hred⟩ := exists_r324Step1Reduction_of_removal ρ
  obtain ⟨Cdet, hCdet, hbound⟩ :=
    exists_r324Step1_deterministic_bound ρ hCiter
  refine ⟨Cdet, hCdet, Citer, hCiter, ?_⟩
  intro lam ε m p hp α β P Gp Is hlam hε hε1 hlog hpm hptrunc hsum hGp
    hGpmeas htrunc hint hP
  exact hbound lam ε m α β P hlam hε hε1 hlog
    ((hred lam ε m p hp α β Gp Is hlam hε hε1 hlog hpm hptrunc hsum hGp
      hGpmeas htrunc hint).mono hP)

end

end Anderson4D
