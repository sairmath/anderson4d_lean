import Anderson4D.DetParametrix.Core.MomentReduction

/-!
# Physical fixed-signature fibers for R-324

Paper §4.2 fixes the within-half extraction data in (4.18), sums every
contraction with that data, and only then takes an absolute value.  This file
makes that operation concrete for the frozen deterministic moment sum.

The analytic ledger is joint integrability on the actual product space, not
pointwise integrability of every section.  This distinction is essential:
fixed-endpoint Green sections may fail to be integrable on exceptional
diagonals, whereas Tonelli--Fubini gives the required section statements
almost everywhere from joint integrability.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The contraction entities realizing one fixed within-half extraction
signature. -/
def momentContractionFiber
    (m : ℕ)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))) :
    Finset (MomentContraction m) :=
  (Finset.univ : Finset (MomentContraction m)).filter
    fun e => momentContractionSignature e = s

@[simp]
theorem mem_momentContractionFiber
    {m : ℕ}
    {s : Finset (Fin (2 * m)) × Finset (Fin (2 * m))}
    {e : MomentContraction m} :
    e ∈ momentContractionFiber m s ↔
      momentContractionSignature e = s := by
  simp [momentContractionFiber]

/-- The four inner physical variables in the order used by (4.18). -/
abbrev R324PhysicalRest (m : ℕ) :=
  T4 × (T4 × (T4 × (Fin (2 * m) → T4)))

/-- The full physical product space, right-associated in the frozen
integration order `(x,y,z,w,v)`. -/
abbrev R324PhysicalPoint (m : ℕ) :=
  T4 × R324PhysicalRest m

/-- Product measure on the four inner physical variables. -/
def r324PhysicalRestMeasure (m : ℕ) :
    Measure (R324PhysicalRest m) :=
  paperMeasure.prod
    (paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin (2 * m) => paperMeasure)))

/-- Product measure on all five physical variable groups. -/
def r324PhysicalMeasure (m : ℕ) :
    Measure (R324PhysicalPoint m) :=
  paperMeasure.prod (r324PhysicalRestMeasure m)

instance instSFiniteR324PhysicalRestMeasure (m : ℕ) :
    SFinite (r324PhysicalRestMeasure m) := by
  unfold r324PhysicalRestMeasure
  infer_instance

instance instSFiniteR324PhysicalMeasure (m : ℕ) :
    SFinite (r324PhysicalMeasure m) := by
  unfold r324PhysicalMeasure
  infer_instance

/-- Flatten a five-variable R-324 integrand onto its genuine product
space. -/
def r324Flatten {m : ℕ}
    (f : T4 → T4 → T4 → T4 →
      (Fin (2 * m) → T4) → ℂ)
    (p : R324PhysicalPoint m) : ℂ :=
  f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- Joint product-space integrability of one frozen contraction term. -/
def R324MomentIntegrable
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (e : MomentContraction m) : Prop :=
  Integrable
    (r324Flatten
      (deterministicMomentIntegrand ρ ε m α β
        e.1 e.2.1 e.2.2))
    (r324PhysicalMeasure m)

/-- Joint integrability gives the frozen five-fold iterated integral.
Every inner use of Fubini is made only on the almost-everywhere integrable
section supplied by the preceding product-space hypothesis. -/
theorem r324_integral_product_eq_five
    {m : ℕ}
    (f : T4 → T4 → T4 → T4 →
      (Fin (2 * m) → T4) → ℂ)
    (hf : Integrable (r324Flatten f)
      (r324PhysicalMeasure m)) :
    (∫ p, r324Flatten f p ∂(r324PhysicalMeasure m)) =
      ∫ x, ∫ y, ∫ z, ∫ w,
        ∫ v, f x y z w v
          ∂(Measure.pi fun _ => paperMeasure)
        ∂paperMeasure ∂paperMeasure ∂paperMeasure ∂paperMeasure := by
  unfold r324PhysicalMeasure r324PhysicalRestMeasure r324Flatten at hf ⊢
  rw [integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_right_ae] with x hx
  rw [integral_prod _ hx]
  apply integral_congr_ae
  filter_upwards [hx.prod_right_ae] with y hy
  rw [integral_prod _ hy]
  apply integral_congr_ae
  filter_upwards [hy.prod_right_ae] with z hz
  rw [integral_prod _ hz]

/-- Product-space form of one concrete contraction term. -/
theorem integral_r324Flatten_deterministicMomentIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (e : MomentContraction m)
    (hint : R324MomentIntegrable ρ ε m α β e) :
    (∫ p, r324Flatten
        (deterministicMomentIntegrand ρ ε m α β
          e.1 e.2.1 e.2.2) p
        ∂(r324PhysicalMeasure m)) =
      deterministicMomentContractionTerm
        ρ ε m α β e := by
  rw [r324_integral_product_eq_five _ hint]
  rfl

/-- The genuine physical integrand obtained by summing all contractions in
one fixed signature fiber before taking a norm. -/
def momentSignaturePhysicalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x y z w : T4) (v : Fin (2 * m) → T4) : ℂ :=
  ∑ e ∈ momentContractionFiber m s,
    deterministicMomentIntegrand ρ ε m α β
      e.1 e.2.1 e.2.2 x y z w v

/-- The flattened fixed-signature integrand is jointly integrable whenever
each concrete contraction in that finite fiber is. -/
theorem integrable_r324Flatten_momentSignaturePhysicalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hint :
      ∀ e ∈ momentContractionFiber m s,
        R324MomentIntegrable ρ ε m α β e) :
    Integrable
      (r324Flatten
        (momentSignaturePhysicalIntegrand ρ ε m α β s))
      (r324PhysicalMeasure m) := by
  unfold momentSignaturePhysicalIntegrand r324Flatten
  exact integrable_finsetSum _ fun e he => hint e he

/-- Fixed-signature form of (4.18): the product integral of the concrete
signature integrand is exactly the sum of the frozen contraction terms. -/
theorem integral_momentSignaturePhysicalIntegrand
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hint :
      ∀ e ∈ momentContractionFiber m s,
        R324MomentIntegrable ρ ε m α β e) :
    (∫ p, r324Flatten
        (momentSignaturePhysicalIntegrand ρ ε m α β s) p
        ∂(r324PhysicalMeasure m)) =
      ∑ e ∈ momentContractionFiber m s,
        deterministicMomentContractionTerm
          ρ ε m α β e := by
  change
    (∫ p, ∑ e ∈ momentContractionFiber m s,
        r324Flatten
          (deterministicMomentIntegrand ρ ε m α β
            e.1 e.2.1 e.2.2) p
        ∂(r324PhysicalMeasure m)) =
      ∑ e ∈ momentContractionFiber m s,
        deterministicMomentContractionTerm
          ρ ε m α β e
  rw [integral_finsetSum _ fun e he => hint e he]
  apply Finset.sum_congr rfl
  intro e he
  exact integral_r324Flatten_deterministicMomentIntegrand
    ρ ε m α β e (hint e he)

/-- Four inner product-space integrations of a fixed signature fiber,
leaving the first external point as the explicit density variable. -/
def momentSignatureOuterSection
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x : T4) : ℂ :=
  ∫ r : R324PhysicalRest m,
    r324Flatten
      (momentSignaturePhysicalIntegrand ρ ε m α β s)
      (x, r)
    ∂(r324PhysicalRestMeasure m)

/-- The canonical nonnegative physical density for a signature fiber.
The norm is outside both the contraction sum and all four inner physical
integrations. -/
def momentSignaturePhysicalDensity
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x : T4) : ℝ :=
  ‖momentSignatureOuterSection ρ ε m α β s x‖

theorem momentSignaturePhysicalDensity_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (x : T4) :
    0 ≤ momentSignaturePhysicalDensity ρ ε m α β s x :=
  norm_nonneg _

/-- The canonical physical density is genuinely integrable from joint
product-space integrability; no exceptional section is promoted to a
pointwise hypothesis. -/
theorem integrable_momentSignaturePhysicalDensity
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hint :
      ∀ e ∈ momentContractionFiber m s,
        R324MomentIntegrable ρ ε m α β e) :
    Integrable
      (momentSignaturePhysicalDensity ρ ε m α β s)
      paperMeasure := by
  have hsum :=
    integrable_r324Flatten_momentSignaturePhysicalIntegrand
      ρ ε m α β s hint
  unfold momentSignaturePhysicalDensity
  exact hsum.integral_prod_left.norm

/-- The norm of a fixed signature fiber is bounded by the integral of its
canonical physical density.  This is the exact triangle inequality used
after the cancellation-preserving contraction sum has been formed. -/
theorem momentContractionFiber_norm_le_density_integral
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (s : Finset (Fin (2 * m)) × Finset (Fin (2 * m)))
    (hint :
      ∀ e ∈ momentContractionFiber m s,
        R324MomentIntegrable ρ ε m α β e) :
    ‖∑ e ∈ momentContractionFiber m s,
        deterministicMomentContractionTerm ρ ε m α β e‖ ≤
      ∫ x, momentSignaturePhysicalDensity
        ρ ε m α β s x ∂paperMeasure := by
  have hsum :=
    integrable_r324Flatten_momentSignaturePhysicalIntegrand
      ρ ε m α β s hint
  have hFubini :
      (∫ p, r324Flatten
          (momentSignaturePhysicalIntegrand ρ ε m α β s) p
          ∂(r324PhysicalMeasure m)) =
        ∫ x, momentSignatureOuterSection
          ρ ε m α β s x ∂paperMeasure := by
    simpa [r324PhysicalMeasure, momentSignatureOuterSection] using
      (integral_prod
        (r324Flatten
          (momentSignaturePhysicalIntegrand ρ ε m α β s))
        hsum)
  rw [← integral_momentSignaturePhysicalIntegrand
    ρ ε m α β s hint]
  rw [hFubini]
  unfold momentSignaturePhysicalDensity
  exact norm_integral_le_integral_norm _

/-- The fully constructed physical part of the fixed-signature R-324
reduction.  Unlike `MomentFiberReductionData`, it stops immediately before
the Proposition 4.1 pointwise majorization and contains no target bound. -/
structure MomentPhysicalFiberReductionData
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4) where
  density :
    (Finset (Fin (2 * m)) × Finset (Fin (2 * m))) →
      T4 → ℝ
  density_eq :
    ∀ s ∈ momentContractionSignatures m,
      density s =
        momentSignaturePhysicalDensity ρ ε m α β s
  density_integrable :
    ∀ s ∈ momentContractionSignatures m,
      Integrable (density s) paperMeasure
  density_nonneg :
    ∀ s ∈ momentContractionSignatures m,
      ∀ x, 0 ≤ density s x
  fiber_le_density_integral :
    ∀ s ∈ momentContractionSignatures m,
      ‖∑ e ∈ (Finset.univ :
          Finset (MomentContraction m)) with
        momentContractionSignature e = s,
        deterministicMomentContractionTerm ρ ε m α β e‖ ≤
          ∫ x, density s x ∂paperMeasure

/-- Construct the complete physical fixed-signature data directly from
joint integrability of the frozen contraction terms. -/
def momentPhysicalFiberReductionData
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (hint :
      ∀ e : MomentContraction m,
        R324MomentIntegrable ρ ε m α β e) :
    MomentPhysicalFiberReductionData ρ ε m α β where
  density := momentSignaturePhysicalDensity ρ ε m α β
  density_eq := by
    intro s _hs
    rfl
  density_integrable := by
    intro s _hs
    exact integrable_momentSignaturePhysicalDensity
      ρ ε m α β s fun e _he => hint e
  density_nonneg := by
    intro s _hs x
    exact momentSignaturePhysicalDensity_nonneg
      ρ ε m α β s x
  fiber_le_density_integral := by
    intro s _hs
    change
      ‖∑ e ∈ momentContractionFiber m s,
          deterministicMomentContractionTerm ρ ε m α β e‖ ≤
        ∫ x, momentSignaturePhysicalDensity
          ρ ε m α β s x ∂paperMeasure
    exact momentContractionFiber_norm_le_density_integral
      ρ ε m α β s fun e _he => hint e

/-- Compatibility adapter to the pointwise-density interface.

The concrete paper proof does not use this adapter: the remaining variable
of `momentSignaturePhysicalDensity` is an absolute translation coordinate,
not the relative primitive-block endpoint governed by Proposition 4.1.
`R324PrimitiveIterationClosure` instead performs the external integrations
first and records the resulting scalar relative-endpoint bound. -/
def MomentPhysicalFiberReductionData.toMomentFiberReductionData
    {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {α β : Z4}
    {primitiveConstant supportConstant : ℝ}
    (d : MomentPhysicalFiberReductionData ρ ε m α β)
    (hdom :
      ∀ s ∈ momentContractionSignatures m,
        ∀ x,
          |lamEps lam ε| ^ (2 * m) * d.density s x ≤
            primitiveInsertedMajorant primitiveConstant lam ε
              supportConstant m x) :
    MomentFiberReductionData ρ lam ε m α β
      primitiveConstant supportConstant where
  density := d.density
  density_integrable := d.density_integrable
  density_nonneg := d.density_nonneg
  fiber_le_density_integral := d.fiber_le_density_integral
  pointwise_fiber_domination := hdom

end

end Anderson4D
