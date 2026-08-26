import Anderson4D.DetParametrix.Paper42_Moment.R324RefinedRoutingClosure

/-!
# Concrete construction of the refined R-324 routing data

This module removes the remaining global exact-sum obligation from the
refined routing interface.  It proves directly that the deterministic
pairing sum is the finite sum of the actual residual-refined physical
integrals.  A caller then supplies only the configuration expansion and
the corresponding per-fibre Fubini exchange.
-/

set_option warningAsError true
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## Actual residual-refined physical integrals -/

/-- Product-space integral of one genuine residual-refined fibre. -/
def r324RefinedPhysicalIntegral
    (ρ : SmoothCutoff) (ε : ℝ) (m : ℕ) (α β : Z4)
    (p : R324RefinedScheduleIndex m) : ℂ :=
  ∫ z,
    r324Flatten
      (momentRefinedPhysicalIntegrand
        ρ ε m α β p.1.1 p.2.1) z
    ∂(r324PhysicalMeasure m)

theorem integrable_r324RefinedPhysicalIntegrand
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    Integrable
      (r324Flatten
        (momentRefinedPhysicalIntegrand
          ρ ε m α β p.1.1 p.2.1))
      (r324PhysicalMeasure m) := by
  unfold momentRefinedPhysicalIntegrand r324Flatten
  exact integrable_finsetSum _ fun e _he =>
    r324MomentIntegrable_all ρ hε hε1 α β e

/-- One refined physical integral is exactly the finite contraction sum
in that refined fibre. -/
theorem r324RefinedPhysicalIntegral_eq_sum_contractionTerms
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4)
    (p : R324RefinedScheduleIndex m) :
    r324RefinedPhysicalIntegral ρ ε m α β p =
      ∑ e ∈ momentRefinedContractionFiber
          m p.1.1 p.2.1,
        deterministicMomentContractionTerm
          ρ ε m α β e := by
  unfold r324RefinedPhysicalIntegral
    momentRefinedPhysicalIntegrand r324Flatten
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e _he
    exact integral_r324Flatten_deterministicMomentIntegrand
      ρ ε m α β e
      (r324MomentIntegrable_all ρ hε hε1 α β e)
  · intro e _he
    exact r324MomentIntegrable_all ρ hε hε1 α β e

/-- Summing the actual refined physical integrals over the genuine
schedule subtype recovers the complete contraction sum exactly. -/
theorem sum_r324RefinedPhysicalIntegral_eq_contractionTerms
    (ρ : SmoothCutoff) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) :
    (∑ p : R324RefinedScheduleIndex m,
        r324RefinedPhysicalIntegral ρ ε m α β p) =
      ∑ e : MomentContraction m,
        deterministicMomentContractionTerm
          ρ ε m α β e := by
  rw [Fintype.sum_sigma]
  calc
    (∑ s :
        {s :
          Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
          s ∈ momentContractionSignatures m},
        ∑ r :
          {r :
            Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
            r ∈ momentResidualChainSignaturesAt m s.1},
          r324RefinedPhysicalIntegral ρ ε m α β ⟨s, r⟩) =
      ∑ s :
        {s :
          Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
          s ∈ momentContractionSignatures m},
        ∑ r :
          {r :
            Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
            r ∈ momentResidualChainSignaturesAt m s.1},
          ∑ e ∈ momentRefinedContractionFiber m s r,
            deterministicMomentContractionTerm
              ρ ε m α β e := by
      apply Finset.sum_congr rfl
      intro s _hs
      apply Finset.sum_congr rfl
      intro r _hr
      exact
        r324RefinedPhysicalIntegral_eq_sum_contractionTerms
          ρ hε hε1 α β ⟨s, r⟩
    _ =
      ∑ s :
        {s :
          Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
          s ∈ momentContractionSignatures m},
          ∑ e ∈ momentContractionFiber m s,
            deterministicMomentContractionTerm
              ρ ε m α β e := by
      apply Finset.sum_congr rfl
      intro s _hs
      let F :
          Finset (Fin (2 * m)) × Finset (Fin (2 * m)) → ℂ :=
        fun r =>
          ∑ e ∈ momentRefinedContractionFiber m s.1 r,
            deterministicMomentContractionTerm
              ρ ε m α β e
      change
        (∑ r :
            {r :
              Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
              r ∈ momentResidualChainSignaturesAt m s.1},
            F r.1) =
          ∑ e ∈ momentContractionFiber m s.1,
            deterministicMomentContractionTerm
              ρ ε m α β e
      rw [← Finset.attach_eq_univ]
      rw [(momentResidualChainSignaturesAt m s.1).sum_attach F]
      exact
        sum_momentContractionFiber_by_residualChainSignature
          s.1 (deterministicMomentContractionTerm
            ρ ε m α β)
    _ =
      ∑ s ∈ momentContractionSignatures m,
        ∑ e ∈ momentContractionFiber m s,
          deterministicMomentContractionTerm
            ρ ε m α β e := by
      let F :
          Finset (Fin (2 * m)) × Finset (Fin (2 * m)) → ℂ :=
        fun s =>
          ∑ e ∈ momentContractionFiber m s,
            deterministicMomentContractionTerm
              ρ ε m α β e
      change
        (∑ s :
            {s :
              Finset (Fin (2 * m)) × Finset (Fin (2 * m)) //
              s ∈ momentContractionSignatures m},
            F s.1) =
          ∑ s ∈ momentContractionSignatures m, F s
      rw [← Finset.attach_eq_univ]
      exact (momentContractionSignatures m).sum_attach F
    _ = ∑ e : MomentContraction m,
          deterministicMomentContractionTerm
            ρ ε m α β e := by
      simpa only [momentContractionFiber] using
        (sum_momentContractions_by_signature m
          (deterministicMomentContractionTerm
            ρ ε m α β))

/-- Deterministic pairing sum as the finite refined-schedule integral,
with the common coupling factor still outside. -/
theorem deterministicMomentPairingSum_eq_sum_refinedPhysicalIntegral
    (ρ : SmoothCutoff) (lam : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m : ℕ} (α β : Z4) :
    deterministicMomentPairingSum ρ lam ε m α β =
      (lamEps lam ε ^ (2 * m) : ℂ) *
        ∑ p : R324RefinedScheduleIndex m,
          r324RefinedPhysicalIntegral ρ ε m α β p := by
  rw [deterministicMomentPairingSum_eq_contractionTerms,
    sum_r324RefinedPhysicalIntegral_eq_contractionTerms
      ρ hε hε1 α β]

/-! ## Canonical representative and per-fibre expansion data -/

/-- Canonical representative used by the concrete grouped core. -/
def r324RefinedScheduleRepresentative
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    MomentContraction m :=
  Classical.choose
    (momentContractionFiber_nonempty_iff_mem_signatures.mpr
      p.1.2)

theorem r324RefinedScheduleRepresentative_mem
    {m : ℕ} (p : R324RefinedScheduleIndex m) :
    r324RefinedScheduleRepresentative p ∈
      momentContractionFiber m p.1.1 := by
  exact
    Classical.choose_spec
      (momentContractionFiber_nonempty_iff_mem_signatures.mpr
        p.1.2)

/-- Concrete configuration expansion of every actual refined core.

The only analytic equality requested from the caller is local to one
refined fibre: its physical integral equals the `tsum` of the
endpoint-first configuration terms.  The global pairing-sum equality is
proved in this module. -/
structure R324ConcreteRefinedCoreExpansion
    (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ) (hm : 0 < m)
    (α β : Z4) where
  core :
    R324RefinedScheduleIndex m → ℕ →
      (Fin (2 * m) → T4) → ℂ
  summable_core :
    ∀ p v, Summable fun a => core p a v
  core_tsum_eq :
    ∀ p v,
      r324RefinedEndpointCore ρ ε m
          p.1.1 p.2.1
          (r324RefinedScheduleRepresentative p) v =
        ∑' a, core p a v
  refinedIntegral_eq_tsum :
    ∀ p,
      (lamEps lam ε ^ (2 * m) : ℂ) *
          r324RefinedPhysicalIntegral
            ρ ε m α β p =
        ∑' a,
          r324GroupedEndpointConfigurationTerm
            hm ρ lam ε α β
            (r324RefinedScheduleRepresentative p)
            (core p a)
  summable_term :
    Summable fun p : R324RefinedScheduleIndex m × ℕ =>
      r324GroupedEndpointConfigurationTerm
        hm ρ lam ε α β
        (r324RefinedScheduleRepresentative p.1)
        (core p.1 p.2)
  incrementCount :
    R324RefinedScheduleIndex m × ℕ → ℕ
  increment :
    ∀ p,
      Fin (incrementCount p) →
        EuclideanSpace ℝ (Fin dim)
  incrementCount_pos :
    ∀ p, 0 < incrementCount p
  incrementCount_le_trunc :
    ∀ p, incrementCount p ≤ truncOrder ε
  increment_sum :
    ∀ p, (∑ i, increment p i) =
      z4EuclideanFrequency (α + β)

namespace R324ConcreteRefinedCoreExpansion

variable
  {ρ : SmoothCutoff} {lam ε : ℝ} {m : ℕ} {hm : 0 < m}
  {α β : Z4}

/-- The local refined-core expansion automatically supplies the exact
global routing data. -/
def toRefinedFourierRoutingData
    (d : R324ConcreteRefinedCoreExpansion
      ρ lam ε m hm α β)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    R324RefinedFourierRoutingData
      ρ lam ε m hm α β where
  representative := r324RefinedScheduleRepresentative
  representative_mem :=
    r324RefinedScheduleRepresentative_mem
  core := d.core
  summable_core := d.summable_core
  core_tsum_eq := d.core_tsum_eq
  sum_eq := by
    rw [
      deterministicMomentPairingSum_eq_sum_refinedPhysicalIntegral
        ρ lam hε hε1 α β,
      Finset.mul_sum]
    calc
      (∑ p : R324RefinedScheduleIndex m,
          (lamEps lam ε ^ (2 * m) : ℂ) *
            r324RefinedPhysicalIntegral
              ρ ε m α β p) =
          ∑ p : R324RefinedScheduleIndex m,
            ∑' a,
              r324GroupedEndpointConfigurationTerm
                hm ρ lam ε α β
                (r324RefinedScheduleRepresentative p)
                (d.core p a) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact d.refinedIntegral_eq_tsum p
      _ = ∑' p : R324RefinedScheduleIndex m,
            ∑' a,
              r324GroupedEndpointConfigurationTerm
                hm ρ lam ε α β
                (r324RefinedScheduleRepresentative p)
                (d.core p a) := by
        rw [tsum_fintype]
      _ = ∑' p : R324RefinedScheduleIndex m × ℕ,
            r324GroupedEndpointConfigurationTerm
              hm ρ lam ε α β
              (r324RefinedScheduleRepresentative p.1)
              (d.core p.1 p.2) :=
        d.summable_term.tsum_prod.symm
  summable_term := d.summable_term
  incrementCount := d.incrementCount
  increment := d.increment
  incrementCount_pos := d.incrementCount_pos
  incrementCount_le_trunc := d.incrementCount_le_trunc
  increment_sum := d.increment_sum

end R324ConcreteRefinedCoreExpansion

end

end Anderson4D
