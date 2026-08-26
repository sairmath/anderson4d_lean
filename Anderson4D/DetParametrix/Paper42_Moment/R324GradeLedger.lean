import Anderson4D.DetParametrix.Paper42_Moment.R324CollapseEntity
import Anderson4D.DetParametrix.Paper42_Moment.R324GradeCount

/-!
# Clause A from a σ-graded lattice budget

This file proves the *asymptotic* grading estimate: it turns a
per-bijection graded budget on the collapsed lattice sum into the exact
proved interface `R324CappedCrossGradingBoundAt`, hence (through the
already proved `r324CappedCrossLedger_of_grading` and
`mainConditional_of_crossGrading_capped`) into `MainConditional`.

## What the file proves

`r324Grade_gradingBoundAt_of_layered` : *layered grading ⇒ clause A's
grading interface*, where "layered" means

* `grade e ≤ m-1` on the pure-cross entities,
* `I(e) ≤ A^m·L^{grade e}`, and
* `#{e : grade e = j} ≤ A^m·(m-j)!` for every `j ≤ m-1`.

The third clause is the σ-grading proper.  Its two ends are exactly
what one knows unconditionally: at `j = 0` it is the trivial entity
count `m!`, at `j = m-1` it is the sharp requirement that only `A^m`
bijections carry the full window power `L^{m-1}` (the identity entity
is one of them, and by `r324PermCross_integral_crossDensity_ge` every
entity is `≥ c^m`, so nothing weaker than a *count* can help).  The
budget `K^m·L^{m-1}` of clause A is therefore **right as stated**: no
factorial allowance is needed, because the order cap `m ≤ ⌊L⌋` makes
`m! ≤ m^{m-1} ≤ L^{m-1}` (`r324Grade_factorial_le_pow`), so the flat
grade is over budget by exactly one `L^{m-1}` and each unit of grade
must buy back one factor `m` in the count.

`r324Grade_layeredAt_of_collapse` : *assigned collapse + graded lattice
budget + permutation layer count ⇒ layered grading*.  After the
physical→lattice collapse each entity is the zero-sum lattice sum `∑_q W_τ(q)` of
`R324CollapseEntity`, and the grade lives on the bijection `τ`.

`r324Grade_mainConditional_of_gradedLattice` : the end-to-end
composition to `MainConditional`.

## Why the grade must be non-constant, and where it comes from

The arithmetic–geometric route of `R324CollapseEntity` is provably
blind to the grading: `r324Col_tsum_latWeight_le` bounds *every* `τ` by
the identity pattern because `q ↦ q∘τ` is a measure-preserving
bijection of the zero-sum sector.  The grade must therefore be read off
the *joint* structure of the two suffix-sum families.  Power counting
on the lattice sum
`∑_q ∏ᵢ‖ρ̂(εqᵢ)‖² ∏ⱼ⟨Sⱼ⟩⁻²⟨Sⱼ^τ⟩⁻²` identifies it: with `m-1` free
momenta in `ℤ⁴` and `2(m-1)` quadratic propagators the sum is exactly
log-critical, and one factor `L` is produced per member of a maximal
refinement chain of partitions of `{1,…,m}` whose blocks are intervals
*simultaneously* for the identity order and for the `τ` order.  The
identity has the full chain (`grade = m-1`); the `m = 4` bijection
`τ = (2,4,1,3)` has none but the trivial one (`grade = 1`), matching
the table in `R324CappedCrossGrading`.  The layer count in
`R324GradePermLayerCount` is the combinatorial statement that grade `j`
costs `(m-j)!` in the count; this is the combinatorial input and is
recorded as a hypothesis, not assumed anywhere silently.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Layered grading data -/

/-- **Layered grading at one capped order.**  A grade on the pure-cross
entities, bounded by `m-1`, with the per-entity window bound and the
factorial layer count.  This is exactly the input
`r324Grade_sum_pow_le_of_factorial` consumes. -/
def R324GradeLayeredAt (ρ : SmoothCutoff) (A : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ},
    0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| → 3 ≤ m → m ≤ truncOrder ε →
      ∃ grade : MomentContraction m → ℕ,
        (∀ e ∈ r324LedgerThreePermEntities m, grade e ≤ m - 1) ∧
        (∀ e ∈ r324LedgerThreePermEntities m,
            r324CappedCrossEntityIntegral ρ ε m e ≤
              A ^ m * |Real.log ε| ^ grade e) ∧
        (∀ j ≤ m - 1,
            (((r324LedgerThreePermEntities m).filter
                fun e => grade e = j).card : ℝ) ≤
              A ^ m * ((m - j).factorial : ℝ))

/-- **The σ-grading discharge.**  Layered grading data produce the exact
proved grading interface, with the constant doubled.  This is the
asymptotic content of clause A: the `m!` entities are re-summed against
their grades with no loss beyond `2^m`. -/
theorem r324Grade_gradingBoundAt_of_layered
    {ρ : SmoothCutoff} {A : ℝ} {m : ℕ} (hA : 0 ≤ A)
    (h : R324GradeLayeredAt ρ A m) :
    R324CappedCrossGradingBoundAt ρ (2 * A) m := by
  intro ε hε hε1 hlog hm3 hcap
  obtain ⟨grade, hle, hent, hcount⟩ := h hε hε1 hlog hm3 hcap
  refine ⟨grade, ?_, ?_⟩
  · intro e he
    refine (hent e he).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (abs_nonneg _) _)
    exact pow_le_pow_left₀ hA (by linarith) m
  · exact r324Grade_sum_pow_le_of_factorial _ grade hA (by omega)
      (r324Grade_cast_le_log hcap) hle hcount

/-! ## The lattice-side inputs -/

/-- **The graded lattice budget.**  The zero-sum lattice sum of the
bijection `τ` (the collapsed entity of `R324CollapseEntity`) obeys the
window bound at *its own* grade.  For `τ = id` the grade is `m-1` and
this is the proved doubled budget `R324ColDoubledBudgetAt`; for a
bijection with no critical proper subspace the grade is `1`. -/
def R324ColGradedBudgetAt (ρ : SmoothCutoff) (D : ℝ) (m : ℕ)
    (gradeP : Equiv.Perm (Fin m) → ℕ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → 1 ≤ |Real.log ε| →
    ∀ τ : Equiv.Perm (Fin m),
      (Summable fun q : R324ColZeroSum m =>
          r324ColLatWeight ρ ε τ (q : Fin m → Z4)) ∧
        (∑' q : R324ColZeroSum m,
            r324ColLatWeight ρ ε τ (q : Fin m → Z4)) ≤
          D ^ m * |Real.log ε| ^ gradeP τ

/-- **The physical→lattice collapse with an injective bijection
assignment.**  Same content as `R324ColPhysicalCollapseAt`, but the
bijection attached to an entity is required to be a function of the
entity and injective on the `m!` entities — which is how the collapse
is produced (the entity of `σ` collapses to `τ = σ⁻¹`).  Injectivity is
what transports a count on bijections to a count on entities. -/
def R324ColAssignedCollapseAt (ρ : SmoothCutoff) (C : ℝ) (m : ℕ) : Prop :=
  ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
    ∃ assign : MomentContraction m → Equiv.Perm (Fin m),
      Set.InjOn assign (r324LedgerThreePermEntities m) ∧
      ∀ e ∈ r324LedgerThreePermEntities m,
        r324CappedCrossEntityIntegral ρ ε m e ≤
          C ^ m * ∑' q : R324ColZeroSum m,
            r324ColLatWeight ρ ε (assign e) (q : Fin m → Z4)

/-- An assigned collapse is in particular the proved collapse. -/
theorem r324Col_physicalCollapseAt_of_assigned
    {ρ : SmoothCutoff} {C : ℝ} {m : ℕ}
    (h : R324ColAssignedCollapseAt ρ C m) :
    R324ColPhysicalCollapseAt ρ C m := by
  intro ε hε hε1 e he
  obtain ⟨assign, _, hbound⟩ := h hε hε1
  exact ⟨assign e, hbound e he⟩

/-- **The permutation layer count** — the σ-grading's combinatorial
clause.  Grade `j` may be carried by at most `A^m·(m-j)!` bijections.
`j = 0` is free (`m!` bijections in all); `j = m-1` says only `A^m`
bijections carry the full window power. -/
def R324GradePermLayerCount (A : ℝ) (m : ℕ)
    (gradeP : Equiv.Perm (Fin m) → ℕ) : Prop :=
  (∀ τ : Equiv.Perm (Fin m), gradeP τ ≤ m - 1) ∧
    ∀ j ≤ m - 1,
      (((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
          fun τ => gradeP τ = j).card : ℝ) ≤
        A ^ m * ((m - j).factorial : ℝ)

/-! ## Assembling the layered grading -/

/-- **The lattice route to layered grading.**  Collapse (with an
injective assignment), a graded lattice budget, and the permutation
layer count give the layered grading data at the product constant. -/
theorem r324Grade_layeredAt_of_collapse
    {ρ : SmoothCutoff} {C D A : ℝ} {m : ℕ}
    {gradeP : Equiv.Perm (Fin m) → ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hcol : R324ColAssignedCollapseAt ρ C m)
    (hbud : R324ColGradedBudgetAt ρ D m gradeP)
    (hcnt : R324GradePermLayerCount A m gradeP) :
    R324GradeLayeredAt ρ (max (C * D) A) m := by
  intro ε hε hε1 hlog _ _
  obtain ⟨assign, hinj, hbound⟩ := hcol hε hε1
  obtain ⟨hgle, hlayer⟩ := hcnt
  have hCm : (0 : ℝ) ≤ C ^ m := pow_nonneg hC m
  set grade : MomentContraction m → ℕ := fun e => gradeP (assign e) with hgradeDef
  refine ⟨grade, fun e _ => hgle _, ?_, ?_⟩
  · intro e he
    calc
      r324CappedCrossEntityIntegral ρ ε m e ≤
          C ^ m * ∑' q : R324ColZeroSum m,
            r324ColLatWeight ρ ε (assign e) (q : Fin m → Z4) := hbound e he
      _ ≤ C ^ m * (D ^ m * |Real.log ε| ^ gradeP (assign e)) :=
          mul_le_mul_of_nonneg_left (hbud hε hε1 hlog (assign e)).2 hCm
      _ = (C * D) ^ m * |Real.log ε| ^ gradeP (assign e) := by
          rw [mul_pow]; ring
      _ ≤ (max (C * D) A) ^ m * |Real.log ε| ^ gradeP (assign e) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (abs_nonneg _) _)
          exact pow_le_pow_left₀ (mul_nonneg hC hD) (le_max_left _ _) m
  · intro j hj
    have hcard :
        ((r324LedgerThreePermEntities m).filter fun e => grade e = j).card ≤
          ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
            fun τ => gradeP τ = j).card := by
      refine Finset.card_le_card_of_injOn assign (fun e he => ?_) ?_
      · have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
        exact Finset.mem_coe.mpr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'.2⟩)
      · refine hinj.mono (fun e he => ?_)
        exact Finset.mem_coe.mpr
          (Finset.mem_filter.mp (Finset.mem_coe.mp he)).1
    have hcardR :
        ((((r324LedgerThreePermEntities m).filter
            fun e => grade e = j).card : ℕ) : ℝ) ≤
          ((((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
            fun τ => gradeP τ = j).card : ℕ) : ℝ) := by
      exact_mod_cast hcard
    refine hcardR.trans ((hlayer j hj).trans ?_)
    refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact pow_le_pow_left₀ hA (le_max_right _ _) m

/-! ## End to end -/

/-- Layered grading at every capped order is the proved grading
Prop. -/
theorem r324Grade_gradingBound_of_layered
    {ρ : SmoothCutoff} {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ m : ℕ, R324GradeLayeredAt ρ A m) :
    R324CappedCrossGradingBound ρ (2 * A) :=
  fun m => r324Grade_gradingBoundAt_of_layered hA (h m)

/-- **The capped cross ledger from the σ-graded lattice budget.**
Collapse with an injective bijection assignment, the graded lattice
budget, and the permutation layer count give clause A outright. -/
theorem r324Grade_cappedCrossLedger_of_gradedLattice
    {ρ : SmoothCutoff} {C D A : ℝ}
    {gradeP : ∀ m : ℕ, Equiv.Perm (Fin m) → ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hcol : ∀ m : ℕ, R324ColAssignedCollapseAt ρ C m)
    (hbud : ∀ m : ℕ, R324ColGradedBudgetAt ρ D m (gradeP m))
    (hcnt : ∀ m : ℕ, R324GradePermLayerCount A m (gradeP m)) :
    ∃ K : ℝ, 0 ≤ K ∧ R324CappedCrossLedger ρ K := by
  have hlayered : ∀ m : ℕ, R324GradeLayeredAt ρ (max (C * D) A) m :=
    fun m => r324Grade_layeredAt_of_collapse hC hD hA
      (hcol m) (hbud m) (hcnt m)
  have hmax : (0 : ℝ) ≤ max (C * D) A := le_trans hA (le_max_right _ _)
  have hgrade : R324CappedCrossGradingBound ρ (2 * max (C * D) A) :=
    r324Grade_gradingBound_of_layered hmax hlayered
  have h2 : (0 : ℝ) ≤ 2 * max (C * D) A := by linarith
  exact ⟨_, mul_nonneg h2 h2,
    r324CappedCrossLedger_of_grading h2 hgrade⟩

/-- **The endpoint.**  The σ-graded lattice budget closes clause A, and
with the two other capped residual Props it delivers
`MainConditional`. -/
theorem r324Grade_mainConditional_of_gradedLattice
    {M : NoiseModel} {ρ : SmoothCutoff} {C D A : ℝ}
    {gradeP : ∀ m : ℕ, Equiv.Perm (Fin m) → ℕ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hcol : ∀ m : ℕ, R324ColAssignedCollapseAt ρ C m)
    (hbud : ∀ m : ℕ, R324ColGradedBudgetAt ρ D m (gradeP m))
    (hcnt : ∀ m : ℕ, R324GradePermLayerCount A m (gradeP m))
    (hmixed : ∃ K : ℝ, 0 ≤ K ∧ R324CappedMixedLedger ρ K)
    (hbracket : ∃ K : ℝ, 0 ≤ K ∧ R324CappedBracketLedger ρ K) :
    MainConditional M ρ := by
  have hmax : (0 : ℝ) ≤ max (C * D) A := le_trans hA (le_max_right _ _)
  have h2 : (0 : ℝ) ≤ 2 * max (C * D) A := by linarith
  refine mainConditional_of_crossGrading_capped
    ⟨2 * max (C * D) A, h2, ?_⟩ hmixed hbracket
  exact r324Grade_gradingBound_of_layered hmax
    (fun m => r324Grade_layeredAt_of_collapse hC hD hA
      (hcol m) (hbud m) (hcnt m))

/-! ## Consistency with the proved order-three calibration -/

/-- **The `m = 3` slice sits inside the layer criterion.**  All `3! = 6`
bijections carry the full grade `m-1 = 2`, and the criterion at
`j = m-1` asks for `6 ≤ A³·(3-2)! = A³`, true for `A = 2`.  So the
proved order-three route is the top layer of the σ-grading, and the
framework does not lose the calibration. -/
theorem r324Grade_permLayerCount_flat_three :
    R324GradePermLayerCount 2 3 (fun _ => 2) := by
  refine ⟨fun _ => le_refl _, ?_⟩
  intro j hj
  rcases Nat.lt_or_ge j 2 with hlt | hge
  · have hempty :
        ((Finset.univ : Finset (Equiv.Perm (Fin 3))).filter
          fun _ => (2 : ℕ) = j) = ∅ :=
      Finset.filter_false_of_mem (fun τ _ => by omega)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hj2 : j = 2 := le_antisymm (by omega) hge
    subst hj2
    have huniv :
        ((Finset.univ : Finset (Equiv.Perm (Fin 3))).filter
          fun _ => (2 : ℕ) = 2) = Finset.univ := by
      simp
    rw [huniv, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]

end

end Anderson4D
