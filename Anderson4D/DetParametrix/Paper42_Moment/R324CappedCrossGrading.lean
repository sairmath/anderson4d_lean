import Anderson4D.DetParametrix.Paper42_Moment.R324CappedRebaseAssembly

/-!
# Capped cross ledger: the grading reduction

The capped cross ledger `R324CappedCrossLedger` bounds the physical
integral of an all-cross fibre by `K^m·L^{m-1}` (`L = |log ε|`).  The
fibre is a sum of `≤ m!` bijection entities; after full Parseval
collapse each entity `σ` is the zero-sum lattice sum

`I(σ) = c^m Σ_{k₁+…+k_m=0} ∏ᵢ h(kᵢ) ∏ⱼ ⟨Sⱼ⟩⁻² ⟨Tⱼ^σ⟩⁻²`,

with `h(k) = ‖ρ̂(εk)‖²`, `Sⱼ = k₁+…+kⱼ` the identity-order partial
sums and `Tⱼ^σ = k_{σ⁻¹(1)}+…+k_{σ⁻¹(j)}` the `σ`-order partial sums:
the two half chains contribute one `⟨·⟩⁻²` propagator per *partial
sum* of the cross momenta in their respective orders.  In `Z4 = ℤ⁴`
the weight `⟨·⟩⁻⁴` is log-critical, so each free momentum contributes
at most one factor `L`, and only when the propagators covering it are
resonant (doubled or critically entangled).

## The `m = 3` calibration table (two-sided)

At `m = 3` the propagator multiset of `σ` is
`{⟨k₁⟩⁻²,⟨k₃⟩⁻²,⟨k_{σ⁻¹(1)}⟩⁻²,⟨k_{σ⁻¹(3)}⟩⁻²}` (using
`S₂ = -k₃`, `T₂ = -k_{σ⁻¹(3)}`), summed over the two free momenta of
the window `|kᵢ| ≲ ε⁻¹`:

| `σ`     | collapsed propagators              | order   |
| ------- | ---------------------------------- | ------- |
| `id`    | `⟨k₁⟩⁻⁴⟨k₃⟩⁻⁴`                     | `L²`    |
| `(1 2)` | `⟨k₁⟩⁻²⟨k₂⟩⁻²⟨k₃⟩⁻⁴`               | `L²`    |
| `(2 3)` | `⟨k₁⟩⁻⁴⟨k₂⟩⁻²⟨k₃⟩⁻²`               | `L²`    |
| `(1 3)` | `⟨k₁⟩⁻⁴⟨k₃⟩⁻⁴`                     | `L²`    |
| `(123)` | `⟨k₁⟩⁻²⟨k₂⟩⁻²⟨k₃⟩⁻⁴`               | `L²`    |
| `(132)` | `⟨k₁⟩⁻⁴⟨k₂⟩⁻²⟨k₃⟩⁻²`               | `L²`    |

Every order-`3` entity is exactly of order `L² = L^{m-1}`: a doubled
propagator gives a quartic window (`~L`) and the residual pair
`⟨kᵢ⟩⁻²⟨kⱼ⟩⁻²` on one free momentum is the critical shifted
convolution (`~L`, uniformly in the shift).  Both mechanisms are
proved (`r324SW_translated_window_le_log`,
`r324SW_shifted_window_le_log`).  The fibre is `≤ 6·C·L² ≤ K³L²`: at
`m = 3` no grading is needed.  The first strict grade drop occurs at
`m = 4`: e.g. `σ⁻¹ = (2,4,1,3)` has propagators
`⟨k₁⟩⁻²⟨k₂⟩⁻²⟨k₃⟩⁻²⟨k₄⟩⁻²⟨k₁+k₂⟩⁻²⟨k₂+k₄⟩⁻²` with **no** critical
proper subspace (every lattice line carries ≥ 3 quadratic
propagators), hence order `L¹`, not `L³`.

## The grading Prop and the reduction

`R324CappedCrossGrading` records the paper's §5 graded per-entity
bound: at each capped order there is a grade function `r` on the
bijections with per-entity value `C^m·L^{r σ}` and graded count
`Σ_σ L^{r σ} ≤ C^m·L^{m-1}` (id-like entities carry `r = m-1` but
number only `C^m`-structurally; deranged entities lose window
resonance).  A uniform per-entity bound cannot replace it: every
entity is `≥ c^m` and id-like ones are `≈ C^m·L^{m-1}`, so the
ungraded per-entity ceiling `C^m·L^{m-1}` times the `m!` count
overshoots the budget by `L^{m-1}` on the capped range.

`r324CappedCrossLedger_of_grading` composes the grading Prop through
the fibre decomposition (each fibre is a subset of the `m!`
permutation entities, its density the entity-wise sum, integrated
term by term) to the exact Prop `R324CappedCrossLedger` consumed by
the proved `mainConditional_of_analyticResiduals_capped`.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-- The bijection carrier of the pure-cross entities at order `m`. -/
abbrev R324CappedCrossPerm (m : ℕ) :=
  ↥(PartialPairing.id : PartialPairing (Fin m)).singles ≃
    ↥(PartialPairing.id : PartialPairing (Fin m)).singles

/-- The physical density of one contraction entity inside a pure-cross
fibre: the two plain Green chains times its own cross covariance
product. -/
def r324CappedCrossEntityDensity (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (e : MomentContraction m) (p : R324PhysicalPoint m) : ℝ :=
  r324LedgerThreeLeftChain m p * r324LedgerThreeRightChain m p *
    momentCrossCovarianceProduct ρ ε m e.1 e.2.1 e.2.2 p.2.2.2.2

theorem r324CappedCrossEntityDensity_nonneg
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (e : MomentContraction m) (p : R324PhysicalPoint m) :
    0 ≤ r324CappedCrossEntityDensity ρ ε m e p :=
  mul_nonneg
    (mul_nonneg (r324LedgerThreeLeftChain_nonneg m p)
      (r324LedgerThreeRightChain_nonneg m p))
    (Finset.prod_nonneg fun _ _ => ρ.etaEpsT4_nonneg ε _)

/-- The summed fibre density is the entity-wise sum of the per-entity
densities. -/
theorem r324CappedCross_density_eq_sum
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ)
    (F : Finset (MomentContraction m)) (p : R324PhysicalPoint m) :
    r324LedgerThreeCrossDensity ρ ε m F p =
      ∑ e ∈ F, r324CappedCrossEntityDensity ρ ε m e p := by
  unfold r324LedgerThreeCrossDensity r324CappedCrossEntityDensity
  rw [Finset.mul_sum]

end

end Anderson4D
