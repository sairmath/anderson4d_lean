import Anderson4D.DetParametrix.Paper42_Moment.R324PhysicalFiber
import Anderson4D.Continuum.GreenLiftIntegrability

/-!
# Increasing Green-tree integrability for R-324

Expanding every renormalized difference in (4.18) replaces selected edges
of the linear Green chain by shortcuts whose left endpoint is still earlier
than the right endpoint.  Every expanded summand is therefore an increasing
rooted tree: vertex `i+1` has one parent among `0,...,i`.

This file proves joint integrability of the Green product for every such
parent map.  The proof removes the terminal vertex, uses Haar translation
invariance for its single incident parent edge, and transports the result
through the terminal-coordinate measurable equivalence.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- An increasing rooted tree on vertices `Fin (n+1)`: the edge indexed by
`i : Fin n` joins vertex `i+1` to a parent in `{0,...,i}`. -/
abbrev IncreasingTreeParent (n : ℕ) :=
  ∀ i : Fin n, Fin (i.val + 1)

/-- Embed the dependent parent index into the common vertex carrier. -/
def increasingTreeParentVertex {n : ℕ}
    (parent : IncreasingTreeParent n) (i : Fin n) :
    Fin (n + 1) :=
  Fin.castLE (by omega) (parent i)

/-- Product of one Green factor along every edge of an increasing tree. -/
def increasingTreeGreenProduct {n : ℕ}
    (parent : IncreasingTreeParent n)
    (x : Fin (n + 1) → T4) : ℂ :=
  ∏ i : Fin n,
    (greenFn
      (x (increasingTreeParentVertex parent i) -
        x i.succ) : ℂ)

/-- Restrict an increasing parent map to all nonterminal edges. -/
def IncreasingTreeParent.init {n : ℕ}
    (parent : IncreasingTreeParent (n + 1)) :
    IncreasingTreeParent n :=
  fun i => parent i.castSucc

/-- Parent of the terminal vertex, cast to the complete preceding carrier. -/
def IncreasingTreeParent.last {n : ℕ}
    (parent : IncreasingTreeParent (n + 1)) :
    Fin (n + 1) :=
  Fin.cast (by simp) (parent (Fin.last n))

/-- Separate the terminal vertex from all preceding vertices. -/
def increasingTreeLastEquiv (n : ℕ) :
    (Fin (n + 2) → T4) ≃ᵐ
      T4 × (Fin (n + 1) → T4) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 2) => T4) (Fin.last (n + 1))

@[simp]
theorem increasingTreeLastEquiv_symm_apply
    (n : ℕ) (y : T4) (v : Fin (n + 1) → T4) :
    (increasingTreeLastEquiv n).symm (y, v) =
      Fin.snoc v y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [increasingTreeLastEquiv]
  · simp [increasingTreeLastEquiv]

theorem measurePreserving_increasingTreeLastEquiv
    (n : ℕ) :
    MeasurePreserving
      (increasingTreeLastEquiv n)
      (Measure.pi fun _ : Fin (n + 2) => paperMeasure)
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (n + 1) => paperMeasure)) := by
  simpa only [increasingTreeLastEquiv,
    Fin.succAbove_last] using
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 2) => paperMeasure)
      (Fin.last (n + 1)))

private theorem increasingTreeParentVertex_init
    {n : ℕ} (parent : IncreasingTreeParent (n + 1))
    (i : Fin n) :
    increasingTreeParentVertex parent i.castSucc =
      (increasingTreeParentVertex parent.init i).castSucc := by
  apply Fin.ext
  rfl

private theorem increasingTree_succ_castSucc
    {n : ℕ} (i : Fin n) :
    i.castSucc.succ = i.succ.castSucc := by
  apply Fin.ext
  rfl

private theorem increasingTreeParentVertex_last
    {n : ℕ} (parent : IncreasingTreeParent (n + 1)) :
    increasingTreeParentVertex parent (Fin.last n) =
      parent.last.castSucc := by
  apply Fin.ext
  rfl

private theorem increasingTree_last_succ
    {n : ℕ} :
    (Fin.last n).succ = Fin.last (n + 1) := by
  apply Fin.ext
  rfl

/-- Terminal-vertex factorization of an increasing Green tree. -/
theorem increasingTreeGreenProduct_snoc
    {n : ℕ} (parent : IncreasingTreeParent (n + 1))
    (v : Fin (n + 1) → T4) (y : T4) :
    increasingTreeGreenProduct parent (Fin.snoc v y) =
      (greenFn
        (y - v parent.last) : ℂ) *
        increasingTreeGreenProduct parent.init v := by
  unfold increasingTreeGreenProduct
  rw [Fin.prod_univ_castSucc]
  have hinit :
      (∏ i : Fin n,
          (greenFn
            ((Fin.snoc v y : Fin (n + 2) → T4)
                (increasingTreeParentVertex parent i.castSucc) -
              (Fin.snoc v y : Fin (n + 2) → T4)
                i.castSucc.succ) : ℂ)) =
        ∏ i : Fin n,
          (greenFn
            (v (increasingTreeParentVertex parent.init i) -
              v i.succ) : ℂ) := by
    apply Finset.prod_congr rfl
    intro i _hi
    rw [increasingTreeParentVertex_init,
      increasingTree_succ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_castSucc]
  rw [hinit, increasingTreeParentVertex_last,
    Fin.snoc_castSucc, increasingTree_last_succ,
    Fin.snoc_last]
  change
    (∏ i : Fin n,
        (greenFn
          (v (increasingTreeParentVertex parent.init i) -
            v i.succ) : ℂ)) *
        (greenFn (v parent.last - y) : ℂ) =
      (greenFn (y - v parent.last) : ℂ) *
        ∏ i : Fin n,
          (greenFn
            (v (increasingTreeParentVertex parent.init i) -
              v i.succ) : ℂ)
  have hgreen :
      greenFn (v parent.last - y) =
        greenFn (y - v parent.last) := by
    have h :=
      (greenFn_memE.neg_invariant
        (v parent.last - y)).symm
    simpa only [neg_sub] using h
  rw [hgreen]
  ring

/-- Every increasing Green tree is jointly integrable in all its vertices.
This is the tree analogue of `integrable_weightedGreenPath_joint`. -/
theorem integrable_increasingTreeGreenProduct :
    ∀ {n : ℕ} (parent : IncreasingTreeParent n),
      Integrable
        (increasingTreeGreenProduct parent)
        (Measure.pi fun _ : Fin (n + 1) => paperMeasure) := by
  intro n
  induction n with
  | zero =>
      intro parent
      change
        Integrable
          (fun _ : Fin 1 → T4 => (1 : ℂ))
          (Measure.pi fun _ : Fin 1 => paperMeasure)
      exact integrable_const 1
  | succ n ih =>
      intro parent
      let μinit :=
        Measure.pi fun _ : Fin (n + 1) => paperMeasure
      let e := increasingTreeLastEquiv n
      have hinit :
          Integrable
            (increasingTreeGreenProduct parent.init)
            μinit := by
        simpa only [μinit] using ih parent.init
      have hshift :
          Measurable
            (fun v : Fin (n + 1) → T4 =>
              v parent.last) :=
        measurable_pi_apply _
      have htarget :
          Integrable
            (fun p : T4 × (Fin (n + 1) → T4) =>
              (greenFn
                (p.1 - p.2 parent.last) : ℂ) *
                increasingTreeGreenProduct parent.init p.2)
            (paperMeasure.prod μinit) := by
        exact integrable_greenFn_sub_mul_lift
          (increasingTreeGreenProduct parent.init)
          (fun v => v parent.last)
          hinit hshift
      have htarget' :
          Integrable
            (fun p : T4 × (Fin (n + 1) → T4) =>
              increasingTreeGreenProduct parent (e.symm p))
            (paperMeasure.prod μinit) := by
        convert htarget using 1
        funext p
        rcases p with ⟨y, v⟩
        change
          increasingTreeGreenProduct parent
              ((increasingTreeLastEquiv n).symm (y, v)) =
            (greenFn (y - v parent.last) : ℂ) *
              increasingTreeGreenProduct parent.init v
        rw [increasingTreeLastEquiv_symm_apply,
          increasingTreeGreenProduct_snoc]
      have hp :
          MeasurePreserving e
            (Measure.pi fun _ : Fin (n + 2) => paperMeasure)
            (paperMeasure.prod μinit) := by
        simpa only [e, μinit] using
          measurePreserving_increasingTreeLastEquiv n
      have hiff :=
        hp.integrable_comp_emb e.measurableEmbedding
          (g := fun p =>
            increasingTreeGreenProduct parent (e.symm p))
      have hs := hiff.mpr htarget'
      have heq :
          ((fun p =>
              increasingTreeGreenProduct parent (e.symm p)) ∘ e) =
            increasingTreeGreenProduct parent := by
        funext x
        exact congrArg (increasingTreeGreenProduct parent)
          (e.symm_apply_apply x)
      rw [heq] at hs
      exact hs

end

end Anderson4D
