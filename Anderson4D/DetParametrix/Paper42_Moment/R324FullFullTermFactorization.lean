import Anderson4D.DetParametrix.Paper42_Moment.R324DetIntegrability
import Anderson4D.DetParametrix.Paper42_Moment.R324EmptyResidualStructure

/-!
# Exact factorization of the full/full R-324 contraction term

When both within-half pairings are full, their single sets are empty.
Thus the cross-copy covariance product in the frozen deterministic moment
integrand is the empty product.  The genuine five-group physical carrier
then reindexes, without changing Haar measure, as the product of the two
independent flat half-carriers.

The theorem below records the resulting exact factorization at the frozen
`deterministicMomentContractionTerm` boundary.  It keeps the four endpoint
characters with their original signs.  Its two `Integrable` hypotheses are
precisely the Fubini seam: they imply joint integrability of the separated
product after the measure-preserving reindexing.  No moment-reduction output
interface and no estimate is used.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- A full/full frozen contraction is exactly the product of its two
independent half-integrals.  The left endpoints retain modes `α, β`, while
the right endpoints retain the conjugate modes `-α, -β`. -/
theorem deterministicMomentContractionTerm_eq_fullHalfIntegral_mul
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles)
    (hp : κp.IsFull) (hm : κm.IsFull)
    (hleft :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          charT4 α p.1 * charT4 β p.2.1 *
            (detIntegrand ρ ε m κp
              (assemble p.1 p.2.1 p.2.2) : ℂ))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure))))
    (hright :
      Integrable
        (fun p : T4 × (T4 × (Fin m → T4)) =>
          charT4 (-α) p.1 * charT4 (-β) p.2.1 *
            (detIntegrand ρ ε m κm
              (assemble p.1 p.2.1 p.2.2) : ℂ))
        (paperMeasure.prod
          (paperMeasure.prod
            (Measure.pi fun _ : Fin m => paperMeasure)))) :
    deterministicMomentContractionTerm ρ ε m α β
        ⟨κp, κm, π⟩ =
      (∫ p : T4 × (T4 × (Fin m → T4)),
          charT4 α p.1 * charT4 β p.2.1 *
            (detIntegrand ρ ε m κp
              (assemble p.1 p.2.1 p.2.2) : ℂ)
          ∂(paperMeasure.prod
            (paperMeasure.prod
              (Measure.pi fun _ : Fin m => paperMeasure)))) *
        ∫ p : T4 × (T4 × (Fin m → T4)),
          charT4 (-α) p.1 * charT4 (-β) p.2.1 *
            (detIntegrand ρ ε m κm
              (assemble p.1 p.2.1 p.2.2) : ℂ)
          ∂(paperMeasure.prod
            (paperMeasure.prod
              (Measure.pi fun _ : Fin m => paperMeasure))) := by
  let Half := T4 × (T4 × (Fin m → T4))
  let μhalf : Measure Half :=
    paperMeasure.prod
      (paperMeasure.prod
        (Measure.pi fun _ : Fin m => paperMeasure))
  let left : Half → ℂ := fun p =>
    charT4 α p.1 * charT4 β p.2.1 *
      (detIntegrand ρ ε m κp
        (assemble p.1 p.2.1 p.2.2) : ℂ)
  let right : Half → ℂ := fun p =>
    charT4 (-α) p.1 * charT4 (-β) p.2.1 *
      (detIntegrand ρ ε m κm
        (assemble p.1 p.2.1 p.2.2) : ℂ)
  have hleft' : Integrable left μhalf := by
    simpa only [left, μhalf, Half] using hleft
  have hright' : Integrable right μhalf := by
    simpa only [right, μhalf, Half] using hright
  have hprod :
      Integrable
        (fun p : Half × Half => left p.1 * right p.2)
        (μhalf.prod μhalf) :=
    hleft'.mul_prod hright'
  have hboth : κp.IsFull ∧ κm.IsFull := ⟨hp, hm⟩
  let split := r324PhysicalSplitMeasurableEquiv m
  have hsplit :
      MeasurePreserving split
        (r324PhysicalMeasure m) (μhalf.prod μhalf) := by
    simpa only [split, μhalf, Half] using
      measurePreserving_r324PhysicalSplitMeasurableEquiv m
  have hcross :
      ∀ v : Fin (2 * m) → T4,
        momentCrossCovarianceProduct
          ρ ε m κp κm π v = 1 := by
    intro v
    unfold momentCrossCovarianceProduct
    apply Finset.prod_eq_one
    intro i _hi
    have hempty :
        κp.singles = (∅ : Finset (Fin m)) :=
      PartialPairing.isFull_iff_singles_eq_empty.mp hboth.1
    have hiEmpty : i.1 ∈ (∅ : Finset (Fin m)) :=
      hempty ▸ i.2
    simp at hiEmpty
  have hpoint :
      r324Flatten
          (deterministicMomentIntegrand
            ρ ε m α β κp κm π) =
        (fun p : Half × Half => left p.1 * right p.2) ∘ split := by
    funext p
    unfold r324Flatten deterministicMomentIntegrand
      left right split
    simp only [Function.comp_apply,
      r324PhysicalSplitMeasurableEquiv_apply]
    rw [hcross]
    push_cast
    ring
  have hpull :
      Integrable
        ((fun p : Half × Half => left p.1 * right p.2) ∘ split)
        (r324PhysicalMeasure m) := by
    exact
      (hsplit.integrable_comp_emb split.measurableEmbedding).mpr
        hprod
  have hphysical :
      R324MomentIntegrable ρ ε m α β ⟨κp, κm, π⟩ := by
    unfold R324MomentIntegrable
    rw [hpoint]
    exact hpull
  calc
    deterministicMomentContractionTerm ρ ε m α β
        ⟨κp, κm, π⟩ =
        ∫ p,
          r324Flatten
            (deterministicMomentIntegrand
              ρ ε m α β κp κm π) p
          ∂(r324PhysicalMeasure m) :=
      (integral_r324Flatten_deterministicMomentIntegrand
        ρ ε m α β ⟨κp, κm, π⟩ hphysical).symm
    _ =
        ∫ p : Half × Half,
          left p.1 * right p.2
          ∂(μhalf.prod μhalf) := by
      rw [hpoint]
      exact hsplit.integral_comp'
        (fun p : Half × Half => left p.1 * right p.2)
    _ = (∫ p : Half, left p ∂μhalf) *
          ∫ p : Half, right p ∂μhalf :=
      integral_prod_mul left right
    _ = _ := by
      rfl

end

end Anderson4D
