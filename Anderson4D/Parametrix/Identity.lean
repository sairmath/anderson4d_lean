import Anderson4D.Parametrix.PairingCollapse
import Anderson4D.DetParametrix.Core.Constants
import Anderson4D.Continuum.SingularConv
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Parametrix identities

This file develops the analytic and finite-sum bridges used in
Proposition 3.4, paper (3.16)--(3.17).  The first section isolates the
measure-preserving reindexing of a finite tuple into two consecutive
blocks.  This is the Fubini mechanism needed to separate the internal
`J` variables from the variables of the remaining random kernel.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

local instance : IsFiniteMeasure paperMeasure := by
  refine ⟨?_⟩
  simp [paperMeasure]

/-! ## Consecutive finite blocks and product measure -/

/-- Reindex a tuple of length `a + b` as two consecutive tuples. -/
def finAddPiMeasurableEquiv (a b : ℕ) (X : Type*)
    [MeasurableSpace X] :
    (Fin (a + b) → X) ≃ᵐ
      (Fin a → X) × (Fin b → X) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (a + b) => X) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin a ⊕ Fin b => X))

@[simp]
theorem finAddPiMeasurableEquiv_apply
    (a b : ℕ) (X : Type*) [MeasurableSpace X]
    (v : Fin (a + b) → X) :
    finAddPiMeasurableEquiv a b X v =
      (fun i => v (Fin.castAdd b i),
        fun j => v (Fin.natAdd a j)) := by
  apply Prod.ext
  · funext i
    rfl
  · funext j
    rfl

@[simp]
theorem finAddPiMeasurableEquiv_symm_apply
    (a b : ℕ) (X : Type*) [MeasurableSpace X]
    (u : Fin a → X) (v : Fin b → X) :
    (finAddPiMeasurableEquiv a b X).symm (u, v) =
      Fin.append u v := by
  funext k
  obtain ⟨k, rfl⟩ :=
    (finSumFinEquiv :
      Fin a ⊕ Fin b ≃ Fin (a + b)).surjective k
  cases k with
  | inl i =>
      rw [finSumFinEquiv_apply_left]
      rw [Fin.append_left]
      have heq :=
        (finAddPiMeasurableEquiv a b X).apply_symm_apply (u, v)
      rw [finAddPiMeasurableEquiv_apply] at heq
      exact congrFun (congrArg Prod.fst heq) i
  | inr j =>
      rw [finSumFinEquiv_apply_right]
      rw [Fin.append_right]
      have heq :=
        (finAddPiMeasurableEquiv a b X).apply_symm_apply (u, v)
      rw [finAddPiMeasurableEquiv_apply] at heq
      exact congrFun (congrArg Prod.snd heq) j

/-- Product Haar measure is preserved when a finite tuple is split into
two consecutive blocks. -/
theorem measurePreserving_finAddPi
    (a b : ℕ) :
    MeasurePreserving
      (finAddPiMeasurableEquiv a b T4)
      (Measure.pi fun _ : Fin (a + b) => paperMeasure)
      ((Measure.pi fun _ : Fin a => paperMeasure).prod
        (Measure.pi fun _ : Fin b => paperMeasure)) := by
  let hcongr :=
    (measurePreserving_piCongrLeft
      (fun _ : Fin (a + b) => paperMeasure)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm
  let hsum :=
    measurePreserving_sumPiEquivProdPi
      (fun _ : Fin a ⊕ Fin b => paperMeasure)
  exact hsum.comp hcongr

/-- Fubini after the concrete `Fin (a+b)` consecutive-block
reindexing. -/
theorem integral_finAdd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℕ) (f : (Fin (a + b) → T4) → E)
    (hf : Integrable f
      (Measure.pi fun _ : Fin (a + b) => paperMeasure)) :
    (∫ x : Fin (a + b) → T4, f x
        ∂(Measure.pi fun _ => paperMeasure)) =
      ∫ u : Fin a → T4, ∫ v : Fin b → T4,
        f (Fin.append u v)
        ∂(Measure.pi fun _ => paperMeasure)
        ∂(Measure.pi fun _ => paperMeasure) := by
  let e := finAddPiMeasurableEquiv a b T4
  let μ := Measure.pi fun _ : Fin (a + b) => paperMeasure
  let μa := Measure.pi fun _ : Fin a => paperMeasure
  let μb := Measure.pi fun _ : Fin b => paperMeasure
  have hp : MeasurePreserving e μ (μa.prod μb) :=
    measurePreserving_finAddPi a b
  have hf' : Integrable (fun p => f (e.symm p)) (μa.prod μb) := by
    have hiff :=
      hp.integrable_comp_emb e.measurableEmbedding
        (g := fun p => f (e.symm p))
    apply hiff.mp
    have hcomp :
        Integrable (((fun p => f (e.symm p)) ∘ e)) μ := by
      convert hf using 1
      funext x
      simp only [Function.comp_apply, e.symm_apply_apply]
    exact hcomp
  calc
    (∫ x, f x ∂μ) =
        ∫ p, f (e.symm p) ∂(μa.prod μb) := by
      simpa only [Function.comp_apply, e.symm_apply_apply] using
        hp.integral_comp' (fun p => f (e.symm p))
    _ = ∫ u, ∫ v, f (e.symm (u, v)) ∂μb ∂μa :=
      integral_prod _ hf'
    _ = _ := by
      simp only [e, finAddPiMeasurableEquiv_symm_apply,
        μa, μb]

/-- A separated integrand factors after splitting consecutive finite
blocks.  `integral_prod_mul` makes this identity valid for totalized
Bochner integrals without auxiliary integrability assumptions. -/
theorem integral_finAdd_mul
    (a b : ℕ) (f : (Fin a → T4) → ℝ)
    (g : (Fin b → T4) → ℝ) :
    (∫ x : Fin (a + b) → T4,
        f (fun i => x (Fin.castAdd b i)) *
          g (fun j => x (Fin.natAdd a j))
        ∂(Measure.pi fun _ => paperMeasure)) =
      (∫ u : Fin a → T4, f u
          ∂(Measure.pi fun _ => paperMeasure)) *
        ∫ v : Fin b → T4, g v
          ∂(Measure.pi fun _ => paperMeasure) := by
  let e := finAddPiMeasurableEquiv a b T4
  let μ := Measure.pi fun _ : Fin (a + b) => paperMeasure
  let μa := Measure.pi fun _ : Fin a => paperMeasure
  let μb := Measure.pi fun _ : Fin b => paperMeasure
  have hp : MeasurePreserving e μ (μa.prod μb) :=
    measurePreserving_finAddPi a b
  calc
    _ = ∫ p : (Fin a → T4) × (Fin b → T4),
        f p.1 * g p.2 ∂(μa.prod μb) := by
      simpa only [Function.comp_apply, e,
        finAddPiMeasurableEquiv_apply, μ, μa, μb] using
        hp.integral_comp' (fun p => f p.1 * g p.2)
    _ = _ := integral_prod_mul f g

/-! ## The analytic case-(3) block -/

/-- Tuple `(z,u,w)` used by the positive-order `J` kernel.  The
arithmetic cast is the one appearing definitionally in `detJ`. -/
def detJTupleSucc (q : ℕ) (z w : T4)
    (u : Fin (2 * q) → T4) :
    Fin (2 * (q + 1)) → T4 :=
  fun j =>
    assemble z w u
      (Fin.cast (by omega : 2 * (q + 1) = 2 * q + 2) j)

@[simp]
theorem detJTupleSucc_zero
    (q : ℕ) (z w : T4) (u : Fin (2 * q) → T4) :
    detJTupleSucc q z w u 0 = z := by
  simp [detJTupleSucc]

/-- The inner spatial integral of a case-(3) contribution before it is
split into the fully paired prefix and the external remainder.  The
first `2q` coordinates are the internal coordinates of
`J_{2(q+1)}`; the last `r` coordinates belong to the remaining random
kernel. -/
def caseThreeJointCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (z w y : T4) (ω : M.Ω)
    (t : Fin (2 * q + r) → T4) : ℝ :=
  detJintegrand ρ ε (q + 1) σ
      (detJTupleSucc q z w
        (fun i => t (Fin.castAdd r i))) *
    randIntegrand M ρ ε τ
      (assemble w y
        (fun j => t (Fin.natAdd (2 * q) j))) ω

/-- Exact finite-product Fubini factorization of the inner case-(3)
integral.  No analytic side condition is needed: after reindexing, the
integrand is a separated product, so mathlib's totalized
`integral_prod_mul` applies directly. -/
theorem integral_caseThreeJointCore_eq_mul
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (z w y : T4) (ω : M.Ω) :
    (∫ t : Fin (2 * q + r) → T4,
        caseThreeJointCore M ρ ε q r σ τ z w y ω t
        ∂(Measure.pi fun _ => paperMeasure)) =
      (∫ u : Fin (2 * q) → T4,
          detJintegrand ρ ε (q + 1) σ
            (detJTupleSucc q z w u)
          ∂(Measure.pi fun _ => paperMeasure)) *
        ∫ v : Fin r → T4,
          randIntegrand M ρ ε τ (assemble w y v) ω
          ∂(Measure.pi fun _ => paperMeasure) := by
  simpa only [caseThreeJointCore] using
    integral_finAdd_mul (2 * q) r
      (fun u =>
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w u))
      (fun v =>
        randIntegrand M ρ ε τ (assemble w y v) ω)

/-- The unsplit case-(3) contribution, with the two boundary variables
`z,w` kept outside and all other variables integrated in their ambient
order. -/
def caseThreeJointContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (2 * (q + 1) + r) *
    ∫ z : T4, ∫ w : T4,
      greenFn (x - z) *
        ∫ t : Fin (2 * q + r) → T4,
          caseThreeJointCore M ρ ε q r σ τ z w y ω t
          ∂(Measure.pi fun _ => paperMeasure)
      ∂paperMeasure ∂paperMeasure

/-- The paper (3.18) form of the same contribution: an internal
`J_{2(q+1),σ}` multiplied by the external random kernel. -/
def caseThreeFactorizedContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) : ℝ :=
  ∫ z : T4, ∫ w : T4,
    greenFn (x - z) *
      detJ ρ lam ε (q + 1) σ z w *
      randRI M ρ lam ε r τ w y ω
    ∂paperMeasure ∂paperMeasure

/-- **Case-(3) analytic bridge (paper (3.18)).**  Consecutive-variable
reindexing, finite-product Fubini, and the coupling-power ledger turn
the joint integral into `detJ × randRI`. -/
theorem caseThreeJointContribution_eq_factorized
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) :
    caseThreeJointContribution M ρ lam ε q r σ τ x y ω =
      caseThreeFactorizedContribution
        M ρ lam ε q r σ τ x y ω := by
  unfold caseThreeJointContribution
  simp_rw [integral_caseThreeJointCore_eq_mul]
  let a := lamEps lam ε
  let F : T4 → T4 → ℝ := fun z w =>
    greenFn (x - z) *
      ((∫ u : Fin (2 * q) → T4,
          detJintegrand ρ ε (q + 1) σ
            (detJTupleSucc q z w u)
          ∂(Measure.pi fun _ => paperMeasure)) *
        ∫ v : Fin r → T4,
          randIntegrand M ρ ε τ (assemble w y v) ω
          ∂(Measure.pi fun _ => paperMeasure))
  change
    a ^ (2 * (q + 1) + r) *
        ∫ z, ∫ w, F z w ∂paperMeasure ∂paperMeasure =
      caseThreeFactorizedContribution
        M ρ lam ε q r σ τ x y ω
  calc
    a ^ (2 * (q + 1) + r) *
        ∫ z, ∫ w, F z w ∂paperMeasure ∂paperMeasure =
        ∫ z, a ^ (2 * (q + 1) + r) *
          (∫ w, F z w ∂paperMeasure) ∂paperMeasure := by
      rw [integral_const_mul]
    _ = ∫ z, ∫ w,
          a ^ (2 * (q + 1) + r) * F z w
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      exact
        (integral_const_mul
          (a ^ (2 * (q + 1) + r)) (fun w => F z w)).symm
    _ = _ := by
      unfold caseThreeFactorizedContribution
      simp only [detJ]
      unfold randRI
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with w
      change
        a ^ (2 * (q + 1) + r) * F z w =
          greenFn (x - z) *
            (a ^ (2 * (q + 1)) *
              ∫ u : Fin (2 * q) → T4,
                detJintegrand ρ ε (q + 1) σ
                  (detJTupleSucc q z w u)
                ∂(Measure.pi fun _ => paperMeasure)) *
            (a ^ r *
              ∫ v : Fin r → T4,
                randIntegrand M ρ ε τ (assemble w y v) ω
                ∂(Measure.pi fun _ => paperMeasure))
      rw [pow_add]
      ring

/-! ### The right-composition analogue (paper (3.17)) -/

/-- Mirrored case-(3) inner integrand: the external random block precedes
the fully paired `J` block. -/
def caseThreeRightJointCore
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x z w : T4) (ω : M.Ω)
    (t : Fin (r + 2 * q) → T4) : ℝ :=
  randIntegrand M ρ ε τ
      (assemble x z (fun i => t (Fin.castAdd (2 * q) i))) ω *
    detJintegrand ρ ε (q + 1) σ
      (detJTupleSucc q z w
        (fun j => t (Fin.natAdd r j)))

/-- Fubini factorization for the right-composition case-(3) block. -/
theorem integral_caseThreeRightJointCore_eq_mul
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x z w : T4) (ω : M.Ω) :
    (∫ t : Fin (r + 2 * q) → T4,
        caseThreeRightJointCore
          M ρ ε q r σ τ x z w ω t
        ∂(Measure.pi fun _ => paperMeasure)) =
      (∫ v : Fin r → T4,
          randIntegrand M ρ ε τ (assemble x z v) ω
          ∂(Measure.pi fun _ => paperMeasure)) *
        ∫ u : Fin (2 * q) → T4,
          detJintegrand ρ ε (q + 1) σ
            (detJTupleSucc q z w u)
          ∂(Measure.pi fun _ => paperMeasure) := by
  simpa only [caseThreeRightJointCore] using
    integral_finAdd_mul r (2 * q)
      (fun v =>
        randIntegrand M ρ ε τ (assemble x z v) ω)
      (fun u =>
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w u))

/-- The joint right-composition case-(3) contribution before separating
the random and deterministic blocks. -/
def caseThreeRightJointContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ (r + 2 * (q + 1)) *
    ∫ z : T4, ∫ w : T4,
      (∫ t : Fin (r + 2 * q) → T4,
        caseThreeRightJointCore
          M ρ ε q r σ τ x z w ω t
        ∂(Measure.pi fun _ => paperMeasure)) *
        greenFn (w - y)
      ∂paperMeasure ∂paperMeasure

/-- The factorized right-composition form, dual to paper (3.18). -/
def caseThreeRightFactorizedContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) : ℝ :=
  ∫ z : T4, ∫ w : T4,
    randRI M ρ lam ε r τ x z ω *
      detJ ρ lam ε (q + 1) σ z w *
      greenFn (w - y)
    ∂paperMeasure ∂paperMeasure

/-- **Right case-(3) analytic bridge (paper (3.17)).** -/
theorem caseThreeRightJointContribution_eq_factorized
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * (q + 1))))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) :
    caseThreeRightJointContribution
        M ρ lam ε q r σ τ x y ω =
      caseThreeRightFactorizedContribution
        M ρ lam ε q r σ τ x y ω := by
  unfold caseThreeRightJointContribution
  simp_rw [integral_caseThreeRightJointCore_eq_mul]
  let a := lamEps lam ε
  let F : T4 → T4 → ℝ := fun z w =>
    ((∫ v : Fin r → T4,
        randIntegrand M ρ ε τ (assemble x z v) ω
        ∂(Measure.pi fun _ => paperMeasure)) *
      ∫ u : Fin (2 * q) → T4,
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w u)
        ∂(Measure.pi fun _ => paperMeasure)) *
      greenFn (w - y)
  change
    a ^ (r + 2 * (q + 1)) *
        ∫ z, ∫ w, F z w ∂paperMeasure ∂paperMeasure =
      caseThreeRightFactorizedContribution
        M ρ lam ε q r σ τ x y ω
  calc
    a ^ (r + 2 * (q + 1)) *
        ∫ z, ∫ w, F z w ∂paperMeasure ∂paperMeasure =
        ∫ z, a ^ (r + 2 * (q + 1)) *
          (∫ w, F z w ∂paperMeasure) ∂paperMeasure := by
      rw [integral_const_mul]
    _ = ∫ z, ∫ w,
          a ^ (r + 2 * (q + 1)) * F z w
          ∂paperMeasure ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      exact
        (integral_const_mul
          (a ^ (r + 2 * (q + 1))) (fun w => F z w)).symm
    _ = _ := by
      unfold caseThreeRightFactorizedContribution
      unfold randRI
      simp only [detJ]
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with w
      change
        a ^ (r + 2 * (q + 1)) * F z w =
          (a ^ r *
            ∫ v : Fin r → T4,
              randIntegrand M ρ ε τ (assemble x z v) ω
              ∂(Measure.pi fun _ => paperMeasure)) *
          (a ^ (2 * (q + 1)) *
            ∫ u : Fin (2 * q) → T4,
              detJintegrand ρ ε (q + 1) σ
                (detJTupleSucc q z w u)
              ∂(Measure.pi fun _ => paperMeasure)) *
          greenFn (w - y)
      rw [pow_add]
      ring

/-! ## Finite sums of the counterterm block -/

/-- The scalar mass attached to one admissible internal pairing. -/
def detJMass
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q))) : ℝ :=
  ∫ z : T4, detJ ρ lam ε q σ z 0 ∂paperMeasure

/-- The finite double sum over an internal non-split pairing and an
arbitrary external pairing factors exactly into `C₂q · Pᵣ`.
This is the finite-sum exchange in the delta part of paper (3.19). -/
theorem sum_detJMass_mul_randRI
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) :
    (∑ σ ∈ Finset.univ.filter
          (fun σ : PartialPairing (Fin (2 * q)) => IsNonSplit σ),
        ∑ τ : PartialPairing (Fin r),
          detJMass ρ lam ε q σ *
            randRI M ρ lam ε r τ x y ω) =
      renormC2q ρ lam ε q *
        parametrixP M ρ lam ε r x y ω := by
  unfold detJMass renormC2q parametrixP
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.mul_sum]

/-- The same counterterm ledger with any external family in an
arbitrary commutative semiring.  It is useful when the external kernels
have already been mapped to Fourier multipliers. -/
theorem sum_internal_external_mul
    {R : Type*} [CommSemiring R]
    {A B : Type*} [Fintype A] [Fintype B]
    (internal : A → R) (external : B → R) :
    (∑ a : A, ∑ b : B, internal a * external b) =
      (∑ a : A, internal a) * ∑ b : B, external b := by
  rw [Finset.sum_mul]
  apply Fintype.sum_congr
  intro a
  rw [Finset.mul_sum]

/-! ## Translation ledger for `J` -/

theorem assemble_add_const
    {n : ℕ} (x y a : T4) (v : Fin n → T4)
    (j : Fin (n + 2)) :
    assemble (x + a) (y + a) (fun i => v i + a) j =
      assemble x y v j + a := by
  unfold assemble
  split_ifs <;> rfl

/-- The closed `J` integrand only contains differences, hence a common
translation of every spatial variable cancels pointwise. -/
theorem detJintegrand_add_const
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (xt : Fin (2 * q) → T4) (a : T4) :
    detJintegrand ρ ε q σ (fun i => xt i + a) =
      detJintegrand ρ ε q σ xt := by
  unfold detJintegrand
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro e he
      split_ifs
      · rfl
      · rename_i hmem hedge
        rw [add_sub_add_right_eq_sub]
      · rfl
    · apply congrArg List.prod
      apply List.map_congr_left
      intro p hp
      unfold diffFactorJ
      split_ifs
      · simp only [add_sub_add_right_eq_sub]
      · rfl
  · apply Finset.prod_congr rfl
    intro i hi
    rw [add_sub_add_right_eq_sub]

/-- Simultaneously translating both endpoints leaves the `J` kernel
unchanged.  The proof reindexes every internal coordinate by the same
Haar translation. -/
theorem detJ_add_const
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (z w a : T4) :
    detJ ρ lam ε q σ (z + a) (w + a) =
      detJ ρ lam ε q σ z w := by
  cases q with
  | zero =>
      rfl
  | succ q =>
      simp only [detJ]
      apply congrArg (fun t : ℝ =>
        lamEps lam ε ^ (2 * (q + 1)) * t)
      let shift :
          (Fin (2 * q) → T4) ≃ᵐ (Fin (2 * q) → T4) :=
        MeasurableEquiv.piCongrRight fun _ =>
          MeasurableEquiv.addRight a
      have hcoord (i : Fin (2 * q)) :
          MeasurePreserving (fun x : T4 => x + a)
            paperMeasure paperMeasure := by
        rw [paperMeasure_eq_volume]
        exact measurePreserving_add_right (volume : Measure T4) a
      have hp :
          MeasurePreserving shift
            (Measure.pi fun _ : Fin (2 * q) => paperMeasure)
            (Measure.pi fun _ : Fin (2 * q) => paperMeasure) := by
        change MeasurePreserving (fun v i => v i + a)
          (Measure.pi fun _ : Fin (2 * q) => paperMeasure)
          (Measure.pi fun _ : Fin (2 * q) => paperMeasure)
        exact measurePreserving_pi
          (fun _ : Fin (2 * q) => paperMeasure)
          (fun _ : Fin (2 * q) => paperMeasure) hcoord
      let fLeft : (Fin (2 * q) → T4) → ℝ := fun v =>
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q (z + a) (w + a) v)
      let fRight : (Fin (2 * q) → T4) → ℝ := fun v =>
        detJintegrand ρ ε (q + 1) σ
          (detJTupleSucc q z w v)
      calc
        (∫ v : Fin (2 * q) → T4,
            detJintegrand ρ ε (q + 1) σ
              (detJTupleSucc q (z + a) (w + a) v)
            ∂(Measure.pi fun _ => paperMeasure)) =
            ∫ v : Fin (2 * q) → T4, fLeft (shift v)
              ∂(Measure.pi fun _ => paperMeasure) := by
          exact (hp.integral_comp' fLeft).symm
        _ = ∫ v : Fin (2 * q) → T4, fRight v
              ∂(Measure.pi fun _ => paperMeasure) := by
          apply integral_congr_ae
          filter_upwards with v
          unfold fLeft fRight
          change
            detJintegrand ρ ε (q + 1) σ
                (detJTupleSucc q (z + a) (w + a)
                  (fun i => v i + a)) =
              detJintegrand ρ ε (q + 1) σ
                (detJTupleSucc q z w v)
          have htuple :
              detJTupleSucc q (z + a) (w + a)
                  (fun i => v i + a) =
                fun j => detJTupleSucc q z w v j + a := by
            funext j
            unfold detJTupleSucc
            exact assemble_add_const z w a v _
          rw [htuple, detJintegrand_add_const]
        _ = _ := rfl

/-- Difference form of translation invariance. -/
theorem detJ_eq_diff
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (z w : T4) :
    detJ ρ lam ε q σ z w =
      detJ ρ lam ε q σ (z - w) 0 := by
  have h :=
    detJ_add_const ρ lam ε q σ (z - w) 0 w
  simpa using h

/-- The coordinatewise involution `w ↦ z - w`, bundled as a measurable
equivalence of the four-torus. -/
def subLeftT4MeasurableEquiv (z : T4) : T4 ≃ᵐ T4 :=
  MeasurableEquiv.piCongrRight fun i =>
    (MeasurableEquiv.neg
        (AddCircle (2 * Real.pi))).trans
      (MeasurableEquiv.addLeft (z i))

@[simp]
theorem subLeftT4MeasurableEquiv_apply (z w : T4) :
    subLeftT4MeasurableEquiv z w = z - w := by
  funext i
  change
    (Equiv.piCongrRight (fun i =>
      ((MeasurableEquiv.neg
          (AddCircle (2 * Real.pi))).trans
        (MeasurableEquiv.addLeft (z i))).toEquiv) w) i =
      z i - w i
  rw [Equiv.piCongrRight_apply, Pi.map_apply]
  change z i + -w i = z i - w i
  rw [sub_eq_add_neg]

/-- Haar measure on the paper torus is invariant under `w ↦ z - w`. -/
theorem measurePreserving_subLeftT4 (z : T4) :
    MeasurePreserving (subLeftT4MeasurableEquiv z)
      paperMeasure paperMeasure := by
  rw [paperMeasure_eq_volume]
  have hpi :
      MeasurePreserving (fun w : T4 => fun i => z i + -w i)
        (volume : Measure T4) (volume : Measure T4) :=
    measurePreserving_pi
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (fun _ : Fin dim =>
        (volume : Measure (AddCircle (2 * Real.pi))))
      (f := fun i w => z i + -w) fun i =>
        (measurePreserving_add_left
          (volume : Measure (AddCircle (2 * Real.pi))) (z i)).comp
          (Measure.measurePreserving_neg _)
  have hfun :
      (subLeftT4MeasurableEquiv z : T4 → T4) =
        fun w : T4 => fun i => z i + -w i := by
    funext w i
    rw [subLeftT4MeasurableEquiv_apply]
    change z i - w i = z i + -w i
    rw [sub_eq_add_neg]
  rw [hfun]
  exact hpi

/-- The mass of `w ↦ J(z,w)` is independent of `z` and equals the
normalization used in `renormC2q`. -/
theorem integral_detJ_right_eq_mass
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ)
    (σ : PartialPairing (Fin (2 * q))) (z : T4) :
    (∫ w : T4, detJ ρ lam ε q σ z w ∂paperMeasure) =
      detJMass ρ lam ε q σ := by
  calc
    (∫ w : T4, detJ ρ lam ε q σ z w ∂paperMeasure) =
        ∫ w : T4, detJ ρ lam ε q σ (z - w) 0
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with w
      exact detJ_eq_diff ρ lam ε q σ z w
    _ = ∫ u : T4, detJ ρ lam ε q σ u 0
          ∂paperMeasure := by
      simpa only [subLeftT4MeasurableEquiv_apply] using
        (measurePreserving_subLeftT4 z).integral_comp'
          (fun u : T4 => detJ ρ lam ε q σ u 0)
    _ = detJMass ρ lam ε q σ := rfl

/-! ## The delta/counterterm part of case (3) -/

/-- The second term in paper (3.19), after the formal delta distribution
has collapsed `w` to `z`, but before replacing the mass of `J` by its
translation-independent normalization. -/
def caseThreeDeltaContribution
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) : ℝ :=
  ∫ z : T4,
    greenFn (x - z) *
      (∫ w : T4, detJ ρ lam ε q σ z w ∂paperMeasure) *
      randRI M ρ lam ε r τ z y ω
    ∂paperMeasure

/-- Translation invariance turns the collapsed `J` factor in (3.19) into
the scalar mass used in the definition of `C₂q`. -/
theorem caseThreeDeltaContribution_eq_mass
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ)
    (σ : PartialPairing (Fin (2 * q)))
    (τ : PartialPairing (Fin r))
    (x y : T4) (ω : M.Ω) :
    caseThreeDeltaContribution
        M ρ lam ε q r σ τ x y ω =
      ∫ z : T4,
        greenFn (x - z) * detJMass ρ lam ε q σ *
          randRI M ρ lam ε r τ z y ω
        ∂paperMeasure := by
  unfold caseThreeDeltaContribution
  simp_rw [integral_detJ_right_eq_mass]

/-- The canonical finite double sum of all case-(3) counterterms at
orders `(2q,r)`, kept inside the outer Green convolution.  Keeping the
finite sum inside the integrand avoids imposing irrelevant integrability
hypotheses merely to exchange a totalized Bochner integral and a sum. -/
def caseThreeCountertermBlock
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∫ z : T4, greenFn (x - z) *
    (∑ σ ∈ Finset.univ.filter
          (fun σ : PartialPairing (Fin (2 * q)) => IsNonSplit σ),
      ∑ τ : PartialPairing (Fin r),
        detJMass ρ lam ε q σ *
          randRI M ρ lam ε r τ z y ω)
    ∂paperMeasure

/-- **Counterterm collapse (paper (3.19)).**  The internal non-split
pairing sum and the external pairing sum collapse pointwise to
`C₂q · Pᵣ` under the outer Green convolution. -/
theorem caseThreeCountertermBlock_eq
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) :
    caseThreeCountertermBlock M ρ lam ε q r x y ω =
      renormC2q ρ lam ε q *
        ∫ z : T4,
          greenFn (x - z) *
            parametrixP M ρ lam ε r z y ω
          ∂paperMeasure := by
  unfold caseThreeCountertermBlock
  calc
    (∫ z : T4, greenFn (x - z) *
        (∑ σ ∈ Finset.univ.filter
              (fun σ : PartialPairing (Fin (2 * q)) => IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            detJMass ρ lam ε q σ *
              randRI M ρ lam ε r τ z y ω)
        ∂paperMeasure) =
        ∫ z : T4,
          renormC2q ρ lam ε q *
            (greenFn (x - z) *
              parametrixP M ρ lam ε r z y ω)
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      rw [sum_detJMass_mul_randRI]
      ring
    _ = _ := integral_const_mul
      (renormC2q ρ lam ε q)
      (fun z : T4 =>
        greenFn (x - z) *
          parametrixP M ρ lam ε r z y ω)

/-- Right-composition counterpart of `caseThreeCountertermBlock`: after
the delta collapse, `Pᵣ` lies to the left of the free Green kernel. -/
def caseThreeRightCountertermBlock
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∫ z : T4,
    (∑ σ ∈ Finset.univ.filter
          (fun σ : PartialPairing (Fin (2 * q)) => IsNonSplit σ),
      ∑ τ : PartialPairing (Fin r),
        randRI M ρ lam ε r τ x z ω *
          detJMass ρ lam ε q σ) *
      greenFn (z - y)
    ∂paperMeasure

/-- Right counterterm collapse used in paper (3.17). -/
theorem caseThreeRightCountertermBlock_eq
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (q r : ℕ) (x y : T4) (ω : M.Ω) :
    caseThreeRightCountertermBlock M ρ lam ε q r x y ω =
      renormC2q ρ lam ε q *
        ∫ z : T4,
          parametrixP M ρ lam ε r x z ω *
            greenFn (z - y)
          ∂paperMeasure := by
  unfold caseThreeRightCountertermBlock
  calc
    (∫ z : T4,
        (∑ σ ∈ Finset.univ.filter
              (fun σ : PartialPairing (Fin (2 * q)) => IsNonSplit σ),
          ∑ τ : PartialPairing (Fin r),
            randRI M ρ lam ε r τ x z ω *
              detJMass ρ lam ε q σ) *
          greenFn (z - y)
        ∂paperMeasure) =
        ∫ z : T4,
          renormC2q ρ lam ε q *
            (parametrixP M ρ lam ε r x z ω *
              greenFn (z - y))
          ∂paperMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      have hsum :
          (∑ σ ∈ Finset.univ.filter
                (fun σ : PartialPairing (Fin (2 * q)) => IsNonSplit σ),
            ∑ τ : PartialPairing (Fin r),
              randRI M ρ lam ε r τ x z ω *
                detJMass ρ lam ε q σ) =
            renormC2q ρ lam ε q *
              parametrixP M ρ lam ε r x z ω := by
        calc
          _ = ∑ σ ∈ Finset.univ.filter
                  (fun σ : PartialPairing (Fin (2 * q)) =>
                    IsNonSplit σ),
                ∑ τ : PartialPairing (Fin r),
                  detJMass ρ lam ε q σ *
                    randRI M ρ lam ε r τ x z ω := by
              apply Finset.sum_congr rfl
              intro σ hσ
              apply Fintype.sum_congr
              intro τ
              ring
          _ = _ := sum_detJMass_mul_randRI
            M ρ lam ε q r x z ω
      rw [hsum]
      ring
    _ = _ := integral_const_mul
      (renormC2q ρ lam ε q)
      (fun z : T4 =>
        parametrixP M ρ lam ε r x z ω *
          greenFn (z - y))

/-! ## Pointwise creation--contraction for the random integrand -/

/-- The Wick creation--contraction identity with the deterministic
renormalized integrand carried through unchanged.  This is the pointwise
algebra at the start of the left-composition proof of (3.16), before the
pairing reindexing into the three head cases. -/
theorem xi_mul_randIntegrand_eq_create_add_contract
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4)
    (z : T4) (ω : M.Ω) :
    M.xiEps ρ ε ω z * randIntegrand M ρ ε κ xt ω =
      detIntegrand ρ ε m κ xt *
        wickPolynomial
          (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
          (fun x ω' => M.xiEps ρ ε ω' x)
          (z :: wickAtSingleLabels κ xt) ω +
      ∑ j : Fin (wickAtSingleLabels κ xt).length,
        detIntegrand ρ ε m κ xt *
          (ρ.etaEpsT4 ε
              (z - (wickAtSingleLabels κ xt).get j) *
            wickPolynomial
              (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
              (fun x ω' => M.xiEps ρ ε ω' x)
              ((wickAtSingleLabels κ xt).eraseIdx j) ω) := by
  unfold randIntegrand
  calc
    M.xiEps ρ ε ω z *
        (detIntegrand ρ ε m κ xt * wickAt M ρ ε κ xt ω) =
        detIntegrand ρ ε m κ xt *
          (M.xiEps ρ ε ω z * wickAt M ρ ε κ xt ω) := by
      ring
    _ = detIntegrand ρ ε m κ xt *
        (wickPolynomial
            (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
            (fun x ω' => M.xiEps ρ ε ω' x)
            (z :: wickAtSingleLabels κ xt) ω +
          ∑ j : Fin (wickAtSingleLabels κ xt).length,
            ρ.etaEpsT4 ε
                (z - (wickAtSingleLabels κ xt).get j) *
              wickPolynomial
                (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
                (fun x ω' => M.xiEps ρ ε ω' x)
                ((wickAtSingleLabels κ xt).eraseIdx j) ω) := by
      rw [xi_mul_wickAt_eq_create_add_contract]
    _ = _ := by
      rw [mul_add, Finset.mul_sum]

/-! ## The order-zero boundary term -/

/-- At order zero the pairing has no single labels, so its Wick factor is
the empty Wick polynomial. -/
theorem wickAt_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ)
    (κ : PartialPairing (Fin 0)) (xt : Fin (0 + 2) → T4)
    (ω : M.Ω) :
    wickAt M ρ ε κ xt ω = 1 := by
  rw [wickAt_eq_wickPolynomial]
  have hlabels : wickAtSingleLabels κ xt = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [wickAtSingleLabels, PartialPairing.singles]
  rw [hlabels]
  exact wickPolynomial_nil
    (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
    (fun x ω' => M.xiEps ρ ε ω' x) ω

/-- The random order-zero kernel is the free Green kernel. -/
theorem randRI_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (κ : PartialPairing (Fin 0)) (x y : T4) (ω : M.Ω) :
    randRI M ρ lam ε 0 κ x y ω = greenFn (x - y) := by
  unfold randRI randIntegrand
  simp_rw [wickAt_zero]
  simp only [mul_one]
  exact detRIfull_zero ρ lam ε κ x y

/-- The order-zero parametrix piece is exactly `G`; this is the left
boundary term in the telescoping derivation of (3.20). -/
theorem parametrixP_zero
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (x y : T4) (ω : M.Ω) :
    parametrixP M ρ lam ε 0 x y ω = greenFn (x - y) := by
  letI : Unique (PartialPairing (Fin 0)) :=
    { default := PartialPairing.id
      uniq := fun κ => by
        apply PartialPairing.ext
        exact fun i => Fin.elim0 i }
  unfold parametrixP
  rw [Fintype.sum_unique]
  exact randRI_zero M ρ lam ε default x y ω

end

end Anderson4D
