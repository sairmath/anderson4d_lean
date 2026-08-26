import Anderson4D.Parametrix.IdentityLeftCaseThree
import Anderson4D.Parametrix.IdentityRightSymmetry
import Anderson4D.Continuum.CellSingular

/-!
# Orderwise symmetry of the random parametrix

The closed `detIntegrand` is deliberately right-oriented: an extracted
interval replaces its right boundary edge.  Consequently it is not
pointwise invariant under chain reversal.  This module instead uses the
graded resolvent-word expansion forced by Proposition 3.4.  Every word
kernel is manifestly transposed by reversing the word and all integration
coordinates; reversal is a bijection on compositions of the total order.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace PartialPairing

/-! ## Graded resolvent words -/

/-- Vertex weight of a graded resolvent word.  A block of size `1`
is one mollified-noise insertion.  A positive even block is a scalar
counterterm insertion; all other block sizes carry zero weight. -/
def renormWordWeight
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (d : ℕ) (z : T4) (ω : M.Ω) : ℝ :=
  if d = 1 then
    lamEps lam ε * M.xiEps ρ ε ω z
  else if Even d then
    -renormC2q ρ lam ε (d / 2)
  else 0

/-- A finite graded word evaluated on a full chain tuple. -/
def renormWordIntegrandOnTuple
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (word : List ℕ)
    (xt : Fin (word.length + 2) → T4)
    (ω : M.Ω) : ℝ :=
  (∏ e : Fin (word.length + 1),
      greenFn (xt e.castSucc - xt e.succ)) *
    ∏ i : Fin word.length,
      renormWordWeight M ρ lam ε
        (word.get i) (xt (varIdx i)) ω

/-- The spatial multiple integral attached to one graded word. -/
def renormWordKernel
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (word : List ℕ)
    (x y : T4) (ω : M.Ω) : ℝ :=
  ∫ v : Fin word.length → T4,
    renormWordIntegrandOnTuple
      M ρ lam ε word (assemble x y v) ω
    ∂(Measure.pi fun _ => paperMeasure)

/-- Reversal of a word's vertex indices, including the harmless cast
between the propositionally equal list lengths. -/
def renormWordReverseIndexEquiv
    (word : List ℕ) :
    Fin word.length ≃ Fin word.reverse.length :=
  Fin.revPerm.trans <| finCongr
    (List.length_reverse (as := word)).symm

/-- Reversal of the full chain slots. -/
def renormWordReverseFullIndexEquiv
    (word : List ℕ) :
    Fin (word.length + 2) ≃
      Fin (word.reverse.length + 2) :=
  Fin.revPerm.trans <| finCongr <|
    congrArg (· + 2)
      (List.length_reverse (as := word)).symm

/-- Reversal of chain-edge indices. -/
def renormWordReverseEdgeIndexEquiv
    (word : List ℕ) :
    Fin (word.length + 1) ≃
      Fin (word.reverse.length + 1) :=
  Fin.revPerm.trans <| finCongr <|
    congrArg (· + 1)
      (List.length_reverse (as := word)).symm

@[simp]
theorem renormWordReverseIndexEquiv_val
    (word : List ℕ) (i : Fin word.length) :
    (renormWordReverseIndexEquiv word i).val =
      word.length - 1 - i.val := by
  unfold renormWordReverseIndexEquiv
  simpa only [Equiv.trans_apply, finCongr_apply_coe,
    Fin.revPerm_apply, Nat.sub_sub,
    Nat.add_comm] using Fin.val_rev i

@[simp]
theorem renormWordReverseFullIndexEquiv_val
    (word : List ℕ)
    (i : Fin (word.length + 2)) :
    (renormWordReverseFullIndexEquiv word i).val =
      word.length + 2 - 1 - i.val := by
  unfold renormWordReverseFullIndexEquiv
  simpa only [Equiv.trans_apply, finCongr_apply_coe,
    Fin.revPerm_apply, Nat.sub_sub,
    Nat.add_comm] using Fin.val_rev i

@[simp]
theorem renormWordReverseEdgeIndexEquiv_val
    (word : List ℕ)
    (i : Fin (word.length + 1)) :
    (renormWordReverseEdgeIndexEquiv word i).val =
      word.length + 1 - 1 - i.val := by
  unfold renormWordReverseEdgeIndexEquiv
  simpa only [Equiv.trans_apply, finCongr_apply_coe,
    Fin.revPerm_apply, Nat.sub_sub,
    Nat.add_comm] using Fin.val_rev i

/-! ## Measure-preserving reversal of the integration variables -/

/-- Reverse the integration-variable coordinates of a graded word. -/
def renormWordReverseVariablesEquiv
    (word : List ℕ) :
    (Fin word.length → T4) ≃ᵐ
      (Fin word.reverse.length → T4) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin word.reverse.length => T4)
    (renormWordReverseIndexEquiv word)

@[simp]
theorem renormWordReverseVariablesEquiv_apply
    (word : List ℕ) (v : Fin word.length → T4)
    (i : Fin word.length) :
    renormWordReverseVariablesEquiv word v
        (renormWordReverseIndexEquiv word i) =
      v i := by
  simpa only [renormWordReverseVariablesEquiv] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin word.reverse.length => T4)
      (renormWordReverseIndexEquiv word) v i)

/-- Coordinate reversal preserves the finite product of paper Haar
measures. -/
theorem measurePreserving_renormWordReverseVariablesEquiv
    (word : List ℕ) :
    MeasurePreserving
      (renormWordReverseVariablesEquiv word)
      (Measure.pi fun _ : Fin word.length =>
        paperMeasure)
      (Measure.pi fun _ : Fin word.reverse.length =>
        paperMeasure) := by
  simpa only [renormWordReverseVariablesEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ : Fin word.reverse.length =>
        paperMeasure)
      (renormWordReverseIndexEquiv word))

/-- Reversing all internal coordinates and swapping the two external
points reverses the assembled full chain. -/
theorem assemble_renormWordReverseVariablesEquiv
    (word : List ℕ) (x y : T4)
    (v : Fin word.length → T4)
    (i : Fin (word.length + 2)) :
    assemble y x
        (renormWordReverseVariablesEquiv word v)
        (renormWordReverseFullIndexEquiv word i) =
      assemble x y v i := by
  have hi : i.val < word.length + 2 := i.isLt
  have hrev :=
    renormWordReverseFullIndexEquiv_val word i
  by_cases hzero : i.val = 0
  · have hrevLast :
        (renormWordReverseFullIndexEquiv word i).val =
          word.reverse.length + 1 := by
      simpa only [List.length_reverse] using hrev.trans
        (by omega)
    simp only [assemble]
    rw [dif_neg (by omega), dif_pos hrevLast,
      dif_pos hzero]
  · by_cases hlast : i.val = word.length + 1
    · have hrevZero :
          (renormWordReverseFullIndexEquiv word i).val =
            0 := by
        omega
      simp only [assemble]
      rw [dif_pos hrevZero, dif_neg hzero,
        dif_pos hlast]
    · have hrevZero :
          (renormWordReverseFullIndexEquiv word i).val ≠
            0 := by
        intro h
        omega
      have hrevLast :
          (renormWordReverseFullIndexEquiv word i).val ≠
            word.reverse.length + 1 := by
        simp only [List.length_reverse]
        intro h
        omega
      have hklt : i.val - 1 < word.length := by
        omega
      let k : Fin word.length :=
        ⟨i.val - 1, hklt⟩
      simp only [assemble]
      rw [dif_neg hrevZero, dif_neg hrevLast,
        dif_neg hzero, dif_neg hlast]
      have htarget :
          (⟨(renormWordReverseFullIndexEquiv
                word i).val - 1,
              by
                have :=
                  (renormWordReverseFullIndexEquiv
                    word i).isLt
                simpa only [List.length_reverse]
                  using (by omega :
                    (renormWordReverseFullIndexEquiv
                        word i).val - 1 <
                      word.length)⟩ :
            Fin word.reverse.length) =
            renormWordReverseIndexEquiv word k := by
        apply Fin.ext
        simp only [k, renormWordReverseIndexEquiv_val]
        omega
      rw [htarget,
        renormWordReverseVariablesEquiv_apply]

@[simp]
theorem reverse_get_renormWordReverseIndexEquiv
    (word : List ℕ) (i : Fin word.length) :
    word.reverse.get
        (renormWordReverseIndexEquiv word i) =
      word.get i := by
  rw [List.get_reverse']
  apply congrArg word.get
  apply Fin.ext
  all_goals
    simp only [renormWordReverseIndexEquiv_val]
    omega

/-- The left endpoint of a reversed edge is the reversal of the
original edge's right endpoint. -/
theorem assemble_reverseEdge_castSucc
    (word : List ℕ) (x y : T4)
    (v : Fin word.length → T4)
    (e : Fin (word.length + 1)) :
    assemble y x
        (renormWordReverseVariablesEquiv word v)
        (renormWordReverseEdgeIndexEquiv word e).castSucc =
      assemble x y v e.succ := by
  have hidx :
      (renormWordReverseEdgeIndexEquiv word e).castSucc =
        renormWordReverseFullIndexEquiv word e.succ := by
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ,
      renormWordReverseEdgeIndexEquiv_val,
      renormWordReverseFullIndexEquiv_val]
    omega
  rw [hidx,
    assemble_renormWordReverseVariablesEquiv]

/-- The right endpoint of a reversed edge is the reversal of the
original edge's left endpoint. -/
theorem assemble_reverseEdge_succ
    (word : List ℕ) (x y : T4)
    (v : Fin word.length → T4)
    (e : Fin (word.length + 1)) :
    assemble y x
        (renormWordReverseVariablesEquiv word v)
        (renormWordReverseEdgeIndexEquiv word e).succ =
      assemble x y v e.castSucc := by
  have hidx :
      (renormWordReverseEdgeIndexEquiv word e).succ =
        renormWordReverseFullIndexEquiv
          word e.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc,
      renormWordReverseEdgeIndexEquiv_val,
      renormWordReverseFullIndexEquiv_val]
    omega
  rw [hidx,
    assemble_renormWordReverseVariablesEquiv]

/-! ## Pointwise symmetry of a graded word -/

/-- Reversing a word and all chain coordinates transposes its
integrand. -/
theorem renormWordIntegrandOnTuple_reverse_assemble
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (word : List ℕ) (x y : T4)
    (v : Fin word.length → T4) (ω : M.Ω) :
    renormWordIntegrandOnTuple M ρ lam ε word.reverse
        (assemble y x
          (renormWordReverseVariablesEquiv word v)) ω =
      renormWordIntegrandOnTuple M ρ lam ε word
        (assemble x y v) ω := by
  have hchain :
      (∏ e : Fin (word.reverse.length + 1),
          greenFn
            (assemble y x
                (renormWordReverseVariablesEquiv word v)
                e.castSucc -
              assemble y x
                (renormWordReverseVariablesEquiv word v)
                e.succ)) =
        ∏ e : Fin (word.length + 1),
          greenFn
            (assemble x y v e.castSucc -
              assemble x y v e.succ) := by
    symm
    apply Fintype.prod_equiv
      (renormWordReverseEdgeIndexEquiv word)
    intro e
    rw [assemble_reverseEdge_castSucc,
      assemble_reverseEdge_succ]
    have hneg :
        assemble x y v e.succ -
            assemble x y v e.castSucc =
          -(assemble x y v e.castSucc -
            assemble x y v e.succ) := by
      abel
    rw [hneg, greenFn_memE.neg_invariant]
  have hvertices :
      (∏ i : Fin word.reverse.length,
          renormWordWeight M ρ lam ε
            (word.reverse.get i)
            (assemble y x
              (renormWordReverseVariablesEquiv word v)
              (varIdx i)) ω) =
        ∏ i : Fin word.length,
          renormWordWeight M ρ lam ε
            (word.get i)
            (assemble x y v (varIdx i)) ω := by
    symm
    apply Fintype.prod_equiv
      (renormWordReverseIndexEquiv word)
    intro i
    simp only [
      reverse_get_renormWordReverseIndexEquiv,
      assemble_varIdx,
      renormWordReverseVariablesEquiv_apply]
  unfold renormWordIntegrandOnTuple
  rw [hchain, hvertices]

/-- Every graded resolvent-word kernel is transposed by reversing the
word.  No integrability hypothesis is needed because the change of
variables is measure preserving. -/
theorem renormWordKernel_reverse
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (word : List ℕ) (x y : T4) (ω : M.Ω) :
    renormWordKernel M ρ lam ε word x y ω =
      renormWordKernel M ρ lam ε word.reverse
        y x ω := by
  unfold renormWordKernel
  calc
    (∫ v : Fin word.length → T4,
        renormWordIntegrandOnTuple M ρ lam ε word
          (assemble x y v) ω
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ v : Fin word.length → T4,
        renormWordIntegrandOnTuple M ρ lam ε
          word.reverse
          (assemble y x
            (renormWordReverseVariablesEquiv word v))
          ω
        ∂(Measure.pi fun _ => paperMeasure) := by
          apply integral_congr_ae
          filter_upwards with v
          exact
            (renormWordIntegrandOnTuple_reverse_assemble
              M ρ lam ε word x y v ω).symm
    _ =
      ∫ v : Fin word.reverse.length → T4,
        renormWordIntegrandOnTuple M ρ lam ε
          word.reverse (assemble y x v) ω
        ∂(Measure.pi fun _ => paperMeasure) := by
          exact
            (measurePreserving_renormWordReverseVariablesEquiv
              word).integral_comp'
              (fun v =>
                renormWordIntegrandOnTuple M ρ lam ε
                  word.reverse (assemble y x v) ω)

/-- The empty graded word is the free Green kernel. -/
theorem renormWordKernel_nil
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (x y : T4) (ω : M.Ω) :
    renormWordKernel M ρ lam ε [] x y ω =
      greenFn (x - y) := by
  unfold renormWordKernel
  simp [renormWordIntegrandOnTuple,
    assemble, Measure.real,
    Measure.pi_empty_univ]

/-! ## Composition sum of all graded words -/

/-- Sum of all graded resolvent words of total order `n`.  Positivity
of composition blocks excludes a spurious degree-zero vertex. -/
def gradedParametrix
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ c : Composition n,
    renormWordKernel M ρ lam ε c.blocks x y ω

/-- The complete graded-word sum is symmetric: composition reversal is
a bijection and transposes every individual word. -/
theorem gradedParametrix_symmetric
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) :
    gradedParametrix M ρ lam ε n x y ω =
      gradedParametrix M ρ lam ε n y x ω := by
  unfold gradedParametrix
  calc
    (∑ c : Composition n,
        renormWordKernel M ρ lam ε c.blocks x y ω) =
      ∑ c : Composition n,
        renormWordKernel M ρ lam ε c.blocks.reverse
          y x ω := by
            apply Fintype.sum_congr
            intro c
            exact renormWordKernel_reverse
              M ρ lam ε c.blocks x y ω
    _ =
      ∑ c : Composition n,
        renormWordKernel M ρ lam ε c.blocks y x ω := by
          simpa only [Composition.reverse_blocks] using
            (Composition.reverse_bijective.sum_comp
              (fun c : Composition n =>
                renormWordKernel M ρ lam ε
                  c.blocks y x ω))

/-- The order-zero graded sum is the free Green kernel. -/
theorem gradedParametrix_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (x y : T4) (ω : M.Ω) :
    gradedParametrix M ρ lam ε 0 x y ω =
      greenFn (x - y) := by
  unfold gradedParametrix
  calc
    (∑ c : Composition 0,
        renormWordKernel M ρ lam ε
          c.blocks x y ω) =
      ∑ _c : Composition 0,
        greenFn (x - y) := by
          apply Fintype.sum_congr
          intro c
          have hc : c.blocks = [] :=
            (Composition.blocks_eq_nil c).mpr rfl
          rw [hc, renormWordKernel_nil]
    _ = _ := by
      simp [composition_card]

/-! ## Head decomposition of graded words -/

/-- Fubini after separating the zero-th coordinate of a finite tuple.
Only integrability of the original joint function is assumed; no
pointwise integrability of the sections is required. -/
theorem integral_finSucc_zero
    {n : ℕ} (f : (Fin (n + 1) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure)) :
    (∫ v : Fin (n + 1) → T4, f v
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ z : T4, ∫ v : Fin n → T4,
        f (Fin.cons z v)
        ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure := by
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => T4) 0
  let μ :=
    Measure.pi fun _ : Fin (n + 1) =>
      paperMeasure
  let μtail :=
    Measure.pi fun _ : Fin n =>
      paperMeasure
  have hp :
      MeasurePreserving e μ
        (paperMeasure.prod μtail) := by
    simpa only [e, μ, μtail] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => paperMeasure) 0)
  have hf' :
      Integrable (fun p => f (e.symm p))
        (paperMeasure.prod μtail) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext v
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  calc
    (∫ v, f v ∂μ) =
        ∫ p, f (e.symm p)
          ∂(paperMeasure.prod μtail) := by
      simpa only [Function.comp_apply,
        e.symm_apply_apply] using
        hp.integral_comp'
          (fun p => f (e.symm p))
    _ =
        ∫ z : T4, ∫ v : Fin n → T4,
          f (e.symm (z, v)) ∂μtail
          ∂paperMeasure :=
      integral_prod _ hf'
    _ = _ := by
      simp only [e,
        MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero,
        Equiv.coe_fn_mk, cast_eq, μtail]

/-- The outer integral of the zero-th-coordinate sections is
integrable whenever the original joint function is integrable. -/
theorem integrable_integral_finSucc_zero
    {n : ℕ} (f : (Fin (n + 1) → T4) → ℝ)
    (hf :
      Integrable f
        (Measure.pi fun _ : Fin (n + 1) =>
          paperMeasure)) :
    Integrable
      (fun z : T4 =>
        ∫ v : Fin n → T4, f (Fin.cons z v)
          ∂(Measure.pi fun _ => paperMeasure))
      paperMeasure := by
  let e :=
    MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => T4) 0
  let μ :=
    Measure.pi fun _ : Fin (n + 1) =>
      paperMeasure
  let μtail :=
    Measure.pi fun _ : Fin n =>
      paperMeasure
  have hp :
      MeasurePreserving e μ
        (paperMeasure.prod μtail) := by
    simpa only [e, μ, μtail] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => paperMeasure) 0)
  have hf' :
      Integrable (fun p => f (e.symm p))
        (paperMeasure.prod μtail) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    convert hf using 1
    funext v
    simp only [Function.comp_apply,
      e.symm_apply_apply]
  have hout := hf'.integral_prod_left
  simpa only [e,
    MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero,
    Equiv.coe_fn_mk, cast_eq, μtail] using hout

/-- Dropping the first variable from an assembled nonempty chain turns
the old external left point into that first variable. -/
theorem assemble_cons_succ
    (word : List ℕ) (x y z : T4)
    (v : Fin word.length → T4)
    (i : Fin (word.length + 2)) :
    assemble x y (Fin.cons z v) i.succ =
      assemble z y v i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [assemble]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [assemble]
    · simp only [assemble, Fin.val_succ,
        Fin.val_castSucc]
      rw [dif_neg (by omega), dif_neg (by omega),
        dif_neg (by omega), dif_neg (by omega)]
      have hleft :
          (⟨k.val + 1 + 1 - 1, by omega⟩ :
            Fin (word.length + 1)) =
            k.succ := by
        apply Fin.ext
        simp
      have hright :
          (⟨k.val + 1 - 1, by omega⟩ :
            Fin word.length) =
            k := by
        apply Fin.ext
        simp
      rw [hleft, hright, Fin.cons_succ]

/-- A nonempty word integrand separates into its first edge, first
vertex weight, and the remaining word integrand. -/
theorem renormWordIntegrandOnTuple_cons
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (d : ℕ) (word : List ℕ) (x y z : T4)
    (v : Fin word.length → T4) (ω : M.Ω) :
    renormWordIntegrandOnTuple M ρ lam ε
        (d :: word)
        (assemble x y (Fin.cons z v)) ω =
      greenFn (x - z) *
        renormWordWeight M ρ lam ε d z ω *
          renormWordIntegrandOnTuple M ρ lam ε
            word (assemble z y v) ω := by
  have hchain :
      (∏ e : Fin (word.length + 2),
          greenFn
            (assemble x y (Fin.cons z v) e.castSucc -
              assemble x y (Fin.cons z v) e.succ)) =
        greenFn (x - z) *
          ∏ e : Fin (word.length + 1),
            greenFn
              (assemble z y v e.castSucc -
                assemble z y v e.succ) := by
    calc
      _ =
          greenFn
              (assemble x y (Fin.cons z v)
                  (0 : Fin (word.length + 2)).castSucc -
                assemble x y (Fin.cons z v)
                  (0 : Fin (word.length + 2)).succ) *
            ∏ e : Fin (word.length + 1),
              greenFn
                (assemble x y (Fin.cons z v)
                    e.succ.castSucc -
                  assemble x y (Fin.cons z v)
                    e.succ.succ) :=
        Fin.prod_univ_succ _
      _ = _ := by
        congr 1
        apply Finset.prod_congr rfl
        intro e _
        have hleft :
            e.succ.castSucc =
              e.castSucc.succ := by
          apply Fin.ext
          rfl
        rw [hleft]
        rw [assemble_cons_succ word x y z v
          e.castSucc]
        rw [assemble_cons_succ word x y z v
          e.succ]
  have hvertices :
      (∏ i : Fin (word.length + 1),
          renormWordWeight M ρ lam ε
            ((d :: word).get i)
            (assemble x y (Fin.cons z v)
              (varIdx i)) ω) =
        renormWordWeight M ρ lam ε d z ω *
          ∏ i : Fin word.length,
            renormWordWeight M ρ lam ε
              (word.get i)
              (assemble z y v (varIdx i)) ω := by
    calc
      _ =
          renormWordWeight M ρ lam ε
              ((d :: word).get
                (0 : Fin (word.length + 1)))
              (assemble x y (Fin.cons z v)
                (varIdx
                  (0 : Fin (word.length + 1)))) ω *
            ∏ i : Fin word.length,
              renormWordWeight M ρ lam ε
                ((d :: word).get i.succ)
                (assemble x y (Fin.cons z v)
                  (varIdx i.succ)) ω :=
        Fin.prod_univ_succ _
      _ = _ := by
        simp
  unfold renormWordIntegrandOnTuple
  simp only [List.length_cons]
  rw [hchain, hvertices]
  ring

/-- Joint integrability of one flat graded-word kernel.  This is the
right hypothesis for Fubini: section integrability is then needed only
almost everywhere and is supplied by `integral_prod`. -/
def RenormWordIntegrable
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (word : List ℕ) (x y : T4) (ω : M.Ω) : Prop :=
  Integrable
    (fun v : Fin word.length → T4 =>
      renormWordIntegrandOnTuple M ρ lam ε word
        (assemble x y v) ω)
    (Measure.pi fun _ => paperMeasure)

/-- A flat nonempty word kernel is its first weighted Green
convolution with the remaining word kernel. -/
theorem renormWordKernel_cons
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (d : ℕ) (word : List ℕ) (x y : T4) (ω : M.Ω)
    (hflat :
      RenormWordIntegrable M ρ lam ε
        (d :: word) x y ω) :
    renormWordKernel M ρ lam ε (d :: word) x y ω =
      ∫ z : T4,
        greenFn (x - z) *
          renormWordWeight M ρ lam ε d z ω *
            renormWordKernel M ρ lam ε word z y ω
        ∂paperMeasure := by
  let f : (Fin (word.length + 1) → T4) → ℝ :=
    fun v =>
      renormWordIntegrandOnTuple M ρ lam ε
        (d :: word) (assemble x y v) ω
  have hf :
      Integrable f
        (Measure.pi fun _ : Fin (word.length + 1) =>
          paperMeasure) := by
    simpa only [RenormWordIntegrable,
      List.length_cons] using hflat
  have hsplit :=
    integral_finSucc_zero f hf
  unfold renormWordKernel
  simp only [List.length_cons]
  rw [hsplit]
  apply integral_congr_ae
  filter_upwards with z
  simp_rw [f, renormWordIntegrandOnTuple_cons]
  rw [← integral_const_mul]

/-- Joint flat-word integrability implies integrability of the first
weighted Green convolution with the tail kernel. -/
theorem integrable_renormWordHeadConvolution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (d : ℕ) (word : List ℕ) (x y : T4) (ω : M.Ω)
    (hflat :
      RenormWordIntegrable M ρ lam ε
        (d :: word) x y ω) :
    Integrable
      (fun z : T4 =>
        greenFn (x - z) *
          renormWordWeight M ρ lam ε d z ω *
            renormWordKernel M ρ lam ε word z y ω)
      paperMeasure := by
  let f : (Fin (word.length + 1) → T4) → ℝ :=
    fun v =>
      renormWordIntegrandOnTuple M ρ lam ε
        (d :: word) (assemble x y v) ω
  have hf :
      Integrable f
        (Measure.pi fun _ : Fin (word.length + 1) =>
          paperMeasure) := by
    simpa only [RenormWordIntegrable,
      List.length_cons] using hflat
  have hout :=
    integrable_integral_finSucc_zero f hf
  convert hout using 1
  funext z
  simp_rw [f, renormWordIntegrandOnTuple_cons]
  unfold renormWordKernel
  rw [integral_const_mul]

/-! ## Compositions classified by their first block -/

/-- Remove the positive first block from a composition of `n+1`.
The finite index stores that block minus one. -/
def compositionHeadTail (n : ℕ) :
    Composition (n + 1) →
      Σ k : Fin (n + 1),
        Composition (n - k.val)
  | ⟨[], _, hsum⟩ => by
      simp at hsum
  | ⟨0 :: _, hpos, _⟩ => by
      have h := hpos (i := 0) (by simp)
      omega
  | ⟨(k + 1) :: word, hpos, hsum⟩ => by
      have hsum' : k + 1 + word.sum = n + 1 := by
        simpa only [List.sum_cons] using hsum
      have hk : k < n + 1 := by
        omega
      refine ⟨⟨k, hk⟩, ?_⟩
      exact
        { blocks := word
          blocks_pos := fun hi =>
            hpos (List.mem_cons_of_mem _ hi)
          blocks_sum := by
            change word.sum = n - k
            omega }

/-- Prepend the block `k+1` to a composition of the remaining
degree. -/
def compositionPrepend (n : ℕ) :
    (Σ k : Fin (n + 1),
      Composition (n - k.val)) →
      Composition (n + 1)
  | ⟨k, c⟩ =>
      { blocks := (k.val + 1) :: c.blocks
        blocks_pos := by
          intro d hd
          rw [List.mem_cons] at hd
          exact hd.elim (fun h => h ▸ by omega)
            c.blocks_pos
        blocks_sum := by
          simp only [List.sum_cons, c.blocks_sum]
          omega }

/-- Classifying a nonempty composition by its first block is a finite
equivalence. -/
def compositionHeadEquiv (n : ℕ) :
    Composition (n + 1) ≃
      Σ k : Fin (n + 1),
        Composition (n - k.val) where
  toFun := compositionHeadTail n
  invFun := compositionPrepend n
  left_inv := by
    rintro ⟨blocks, hpos, hsum⟩
    cases blocks with
    | nil =>
        simp at hsum
    | cons d word =>
        cases d with
        | zero =>
            have h := hpos (i := 0) (by simp)
            omega
        | succ k =>
            apply Composition.ext
            rfl
  right_inv := by
    rintro ⟨⟨k, hk⟩, ⟨word, hpos, hsum⟩⟩
    rfl

/-- The order-`n+1` graded sum, classified by the size of its first
positive block. -/
theorem gradedParametrix_succ_eq_sum_head
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) :
    gradedParametrix M ρ lam ε (n + 1) x y ω =
      ∑ k : Fin (n + 1),
        ∑ c : Composition (n - k.val),
          renormWordKernel M ρ lam ε
            ((k.val + 1) :: c.blocks) x y ω := by
  unfold gradedParametrix
  calc
    (∑ c : Composition (n + 1),
        renormWordKernel M ρ lam ε
          c.blocks x y ω) =
      ∑ p :
          Σ k : Fin (n + 1),
            Composition (n - k.val),
        renormWordKernel M ρ lam ε
          ((compositionHeadEquiv n).symm p).blocks
          x y ω := by
            symm
            exact (compositionHeadEquiv n).symm.sum_comp
              (fun c : Composition (n + 1) =>
                renormWordKernel M ρ lam ε
                  c.blocks x y ω)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Fintype.sum_congr
      intro k
      apply Fintype.sum_congr
      intro c
      rfl

/-- Head-block recurrence for the graded sum.  Joint integrability is
required only for the finitely many flat words at the new order. -/
theorem gradedParametrix_succ_eq_headConvolutions
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hflat :
      ∀ k : Fin (n + 1),
        ∀ c : Composition (n - k.val),
          RenormWordIntegrable M ρ lam ε
            ((k.val + 1) :: c.blocks) x y ω) :
    gradedParametrix M ρ lam ε (n + 1) x y ω =
      ∑ k : Fin (n + 1),
        ∫ z : T4,
          greenFn (x - z) *
            renormWordWeight M ρ lam ε
              (k.val + 1) z ω *
            gradedParametrix M ρ lam ε
              (n - k.val) z y ω
          ∂paperMeasure := by
  rw [gradedParametrix_succ_eq_sum_head]
  apply Fintype.sum_congr
  intro k
  calc
    (∑ c : Composition (n - k.val),
        renormWordKernel M ρ lam ε
          ((k.val + 1) :: c.blocks) x y ω) =
      ∑ c : Composition (n - k.val),
        ∫ z : T4,
          greenFn (x - z) *
            renormWordWeight M ρ lam ε
              (k.val + 1) z ω *
            renormWordKernel M ρ lam ε
              c.blocks z y ω
          ∂paperMeasure := by
            apply Fintype.sum_congr
            intro c
            exact renormWordKernel_cons
              M ρ lam ε (k.val + 1) c.blocks
              x y ω (hflat k c)
    _ =
      ∫ z : T4,
        ∑ c : Composition (n - k.val),
          greenFn (x - z) *
            renormWordWeight M ρ lam ε
              (k.val + 1) z ω *
            renormWordKernel M ρ lam ε
              c.blocks z y ω
        ∂paperMeasure := by
          symm
          simpa only [Finset.mem_univ, forall_const] using
            (integral_finsetSum
              (μ := paperMeasure) Finset.univ
              (fun c (_ : c ∈ Finset.univ) =>
                integrable_renormWordHeadConvolution
                  M ρ lam ε (k.val + 1) c.blocks
                  x y ω (hflat k c)))
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      unfold gradedParametrix
      rw [Finset.mul_sum]

/-! ## Even head blocks -/

/-- The even block of order `2q` as a head index (block size minus
one). -/
def evenHeadIndex
    (n : ℕ)
    (q : {q : ℕ //
      q ∈ Finset.Icc 1 ((n + 1) / 2)}) :
    {k : Fin (n + 1) // Even (k.val + 1)} := by
  have hq := Finset.mem_Icc.mp q.property
  have htwo' : q.val * 2 ≤ n + 1 :=
    (Nat.le_div_iff_mul_le
      (by omega : 0 < 2)).mp hq.2
  have htwo : 2 * q.val ≤ n + 1 := by
    omega
  refine ⟨⟨2 * q.val - 1, by omega⟩, ?_⟩
  change Even (2 * q.val - 1 + 1)
  refine ⟨q.val, ?_⟩
  omega

/-- Recover `q` from an even positive head block `2q`. -/
def evenHeadOrder
    (n : ℕ)
    (k : {k : Fin (n + 1) //
      Even (k.val + 1)}) :
    {q : ℕ //
      q ∈ Finset.Icc 1 ((n + 1) / 2)} := by
  refine ⟨(k.val + 1) / 2,
    Finset.mem_Icc.mpr ?_⟩
  obtain ⟨q, hq⟩ := k.property
  constructor
  · have hk := k.val.isLt
    omega
  · apply (Nat.le_div_iff_mul_le
      (by omega : 0 < 2)).mpr
    have hk := k.val.isLt
    omega

/-- Positive even head blocks are in bijection with the paper's
counterterm range `q ∈ [1, ⌊(n+1)/2⌋]`. -/
def evenHeadIndexEquiv (n : ℕ) :
    {q : ℕ //
      q ∈ Finset.Icc 1 ((n + 1) / 2)} ≃
      {k : Fin (n + 1) //
        Even (k.val + 1)} where
  toFun := evenHeadIndex n
  invFun := evenHeadOrder n
  left_inv := by
    rintro ⟨q, hq⟩
    apply Subtype.ext
    simp only [evenHeadIndex, evenHeadOrder]
    have hq' := Finset.mem_Icc.mp hq
    omega
  right_inv := by
    rintro ⟨⟨k, hk⟩, heven⟩
    obtain ⟨q, hq⟩ := heven
    have hhalf : (k + 1) / 2 = q := by
      calc
        (k + 1) / 2 = (q + q) / 2 := by
          rw [hq]
        _ = q := by omega
    have hkform : 2 * q - 1 = k := by
      rw [two_mul]
      exact
        (Nat.sub_eq_iff_eq_add
          (by omega : 1 ≤ q + q)).2 hq.symm
    apply Subtype.ext
    apply Fin.ext
    simp only [evenHeadOrder, evenHeadIndex]
    simpa only [hhalf] using hkform

/-- Summing a head-block selector leaves its degree-one term and the
negative contributions of exactly the positive even blocks. -/
theorem headSelector_sum
    (n : ℕ) (A : ℝ) (B : ℕ → ℝ) :
    (∑ k : Fin (n + 1),
      if k.val = 0 then A
      else if Even (k.val + 1) then
        -B ((k.val + 1) / 2)
      else 0) =
      A - ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
        B q := by
  have hsplit :
      (∑ k : Fin (n + 1),
        if k.val = 0 then A
        else if Even (k.val + 1) then
          -B ((k.val + 1) / 2)
        else 0) =
        (∑ k : Fin (n + 1),
          if k.val = 0 then A else 0) +
        ∑ k : Fin (n + 1),
          if Even (k.val + 1) then
            -B ((k.val + 1) / 2)
          else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val = 0
    · simp [hk]
    · simp [hk]
  rw [hsplit]
  have hzero :
      (∑ k : Fin (n + 1),
        if k.val = 0 then A else 0) = A := by
    rw [Fin.sum_univ_succ]
    simp
  rw [hzero]
  congr 1
  calc
    (∑ k : Fin (n + 1),
        if Even (k.val + 1) then
          -B ((k.val + 1) / 2)
        else 0) =
      ∑ k :
          {k : Fin (n + 1) //
            Even (k.val + 1)},
        -B ((k.val + 1) / 2) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_subtype
          intro k
          simp
    _ =
      ∑ q :
          {q : ℕ //
            q ∈ Finset.Icc 1 ((n + 1) / 2)},
        -B q.val := by
          calc
            _ =
                ∑ q :
                    {q : ℕ //
                      q ∈ Finset.Icc 1
                        ((n + 1) / 2)},
                  -B ((((evenHeadIndexEquiv n) q).val.val +
                    1) / 2) := by
                      symm
                      exact (evenHeadIndexEquiv n).sum_comp
                        (fun k =>
                          -B ((k.val.val + 1) / 2))
            _ = _ := by
              apply Fintype.sum_congr
              intro q
              congr 2
              have hinv :=
                (evenHeadIndexEquiv n).left_inv q
              have hval :=
                congrArg Subtype.val hinv
              change
                ((evenHeadIndex n q).val.val + 1) / 2 =
                  q.val
              simpa only [evenHeadIndexEquiv,
                evenHeadOrder] using hval
    _ =
      -(∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
        B q) := by
          rw [← Finset.sum_neg_distrib]
          symm
          apply Finset.sum_subtype
          intro q
          rfl

/-! ## Proposition 3.4 recurrence for the graded sum -/

/-- Degree-one head contribution for the graded parametrix. -/
def gradedParametrixNoiseSource
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∫ z : T4,
    greenFn (x - z) *
      (lamEps lam ε * M.xiEps ρ ε ω z) *
      gradedParametrix M ρ lam ε n z y ω
    ∂paperMeasure

/-- Positive even head contribution for the graded parametrix. -/
def gradedCountertermBlock
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  renormC2q ρ lam ε q *
    ∫ z : T4,
      greenFn (x - z) *
        gradedParametrix M ρ lam ε r z y ω
      ∂paperMeasure

/-- Sum of the positive even graded head blocks at order `n+1`. -/
def gradedOrderCountertermSum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
    gradedCountertermBlock M ρ lam ε q
      (n + 1 - 2 * q) x y ω

/-- The graded composition sum satisfies the left recurrence of
Proposition 3.4. -/
theorem gradedParametrix_succ_eq_noise_sub_counterterms
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω)
    (hflat :
      ∀ k : Fin (n + 1),
        ∀ c : Composition (n - k.val),
          RenormWordIntegrable M ρ lam ε
            ((k.val + 1) :: c.blocks) x y ω) :
    gradedParametrix M ρ lam ε (n + 1) x y ω =
      gradedParametrixNoiseSource
          M ρ lam ε n x y ω -
        gradedOrderCountertermSum
          M ρ lam ε n x y ω := by
  rw [gradedParametrix_succ_eq_headConvolutions
    M ρ lam ε n x y ω hflat]
  let A :=
    gradedParametrixNoiseSource
      M ρ lam ε n x y ω
  let B : ℕ → ℝ :=
    fun q =>
      gradedCountertermBlock M ρ lam ε q
        (n + 1 - 2 * q) x y ω
  calc
    (∑ k : Fin (n + 1),
        ∫ z : T4,
          greenFn (x - z) *
            renormWordWeight M ρ lam ε
              (k.val + 1) z ω *
            gradedParametrix M ρ lam ε
              (n - k.val) z y ω
          ∂paperMeasure) =
      ∑ k : Fin (n + 1),
        if k.val = 0 then A
        else if Even (k.val + 1) then
          -B ((k.val + 1) / 2)
        else 0 := by
          apply Fintype.sum_congr
          intro k
          by_cases hk : k.val = 0
          · have hkfin : k = 0 := by
              apply Fin.ext
              exact hk
            subst k
            simp only [Fin.val_zero, zero_add,
              if_pos, Nat.sub_zero]
            unfold A
            unfold gradedParametrixNoiseSource
            unfold renormWordWeight
            simp only [if_pos]
          · rw [if_neg hk]
            by_cases heven : Even (k.val + 1)
            · rw [if_pos heven]
              have hnotone : k.val + 1 ≠ 1 := by
                omega
              obtain ⟨q, hq⟩ := heven
              have hhalf :
                  (k.val + 1) / 2 = q := by
                calc
                  (k.val + 1) / 2 =
                      (q + q) / 2 := by rw [hq]
                  _ = q := by omega
              have htwice :
                  2 * ((k.val + 1) / 2) =
                    k.val + 1 := by
                rw [hhalf, two_mul, ← hq]
              have htail :
                  n - k.val =
                    n + 1 -
                      2 * ((k.val + 1) / 2) := by
                omega
              unfold B
              unfold gradedCountertermBlock
              unfold renormWordWeight
              simp only [if_neg hnotone,
                if_pos (show Even (k.val + 1) from
                  ⟨q, hq⟩)]
              rw [htail]
              calc
                (∫ z : T4,
                    greenFn (x - z) *
                      -renormC2q ρ lam ε
                        ((k.val + 1) / 2) *
                      gradedParametrix M ρ lam ε
                        (n + 1 -
                          2 * ((k.val + 1) / 2))
                        z y ω
                    ∂paperMeasure) =
                    -renormC2q ρ lam ε
                        ((k.val + 1) / 2) *
                      ∫ z : T4,
                        greenFn (x - z) *
                          gradedParametrix M ρ lam ε
                            (n + 1 -
                              2 * ((k.val + 1) / 2))
                            z y ω
                        ∂paperMeasure := by
                          rw [← integral_const_mul]
                          apply integral_congr_ae
                          filter_upwards with z
                          ring
                _ = _ := by ring
            · rw [if_neg heven]
              have hnotone : k.val + 1 ≠ 1 := by
                omega
              unfold renormWordWeight
              simp only [if_neg hnotone,
                if_neg heven, mul_zero, zero_mul,
                integral_zero]
    _ = A - ∑ q ∈ Finset.Icc 1 ((n + 1) / 2),
        B q :=
      headSelector_sum n A B
    _ = _ := by
      rfl

end PartialPairing

end

end Anderson4D
