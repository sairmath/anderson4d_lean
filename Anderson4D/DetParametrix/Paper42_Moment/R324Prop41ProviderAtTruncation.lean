import Anderson4D.DetParametrix.Paper42_Moment.R324ConcretePhaseATraceAssembly
import Anderson4D.DetParametrix.Paper42_Moment.R324FullPairingBudgetTerminalAdapter

/-!
# Proposition 4.1 provider at the R-324 truncation

This module packages the proved truncation form of Proposition 4.1 as the
literal-head provider consumed by the within-half R-324 iteration.

The only order comparison is the structural fact that every extracted block
has order at most the ambient half-order.  Thus the provider introduces no
analytic assumption beyond the positivity, cutoff, and truncation hypotheses
already present in `proposition41_at_truncation`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- Proposition 4.1 at the paper truncation supplies its estimates uniformly
at every literal head of every within-half residual suffix.

The logarithmic lower bound used by the subsequent one-block collapse is
deliberately absent here: it is not a hypothesis of Proposition 4.1. -/
theorem exists_r324WithinHalfProp41Provider_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C : ℝ,
      0 < supportConstant ∧ 0 < C ∧
        ∀ (lam ε : ℝ) (m : ℕ)
          (pairing : PartialPairing (Fin m)),
          0 < lam → 0 < ε → ε ≤ 1 →
          m ≤ truncOrder ε →
          R324WithinHalfProp41Provider
            ρ C lam ε supportConstant pairing := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  refine ⟨supportConstant, C, hsupport, hC, ?_⟩
  intro lam ε m pairing hlam hε hε1 hm
    res head tail hremaining H hH
  exact
    hprop lam ε
      (residualBlockOrder head.2)
      (res.headContext
        head tail hremaining).one_le_blockOrder
      H hlam hε hε1
      ((res.headContext
        head tail hremaining).order_le_ambient.trans hm)
      hH

/-! ## Compatible budget and analytic traces -/

/-- A local analytic block provider promotes to the complete budget update
when the uniform outgoing Green scale is at least one.

This conversion keeps the same one-block constant `K`.  It is the small
compatibility fact needed to build the numerical and analytic terminal
traces from one Proposition 4.1 closure theorem. -/
theorem r324WithinHalfBudgetLocalBlockProvider_of_localBlockProvider
    {ρ : SmoothCutoff} {C lam ε K A : ℝ}
    {m : ℕ} {pairing : PartialPairing (Fin m)}
    (hA : 1 ≤ A)
    (provider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K pairing) :
    R324WithinHalfBudgetLocalBlockProvider
      ρ C lam ε K A pairing := by
  intro res head tail hremaining scale hreach hcertificate
  obtain ⟨_localBound, rawCertificate⟩ :=
    provider res head tail hremaining scale hcertificate
  have budgetCertificate :
      R324WithinHalfEdgeCertificate
        (res.afterHead head tail hremaining).state
        (res.budgetUpdatedEdgeScale
          head tail hremaining scale C lam K) :=
    hreach.promote_afterHead_certificate
      res rfl head tail hremaining hA rawCertificate
  refine ⟨?_, ?_, budgetCertificate⟩
  · intro x hx
    exact
      budgetCertificate.bound
        (r324WithinHalfPredecessorSlot
          res.state head) x hx
  · exact
      R324WithinHalfBudgetScaleReachable.afterHead
        res head tail hremaining hreach

namespace R324WithinHalfResidualPrefix

/-- At the paper truncation, one choice of Proposition 4.1 constants and one
one-block constant construct a compatible full-pairing budget stop and
analytic terminal assembly.

The two traces start from the same uniform all-Green certificate and use the
same local constant `K`.  Their scale-update functions remain distinct, as
required by the budget ledger; `R324FullPairingBudgetTerminalAdapter`
identifies only their canonical residual state. -/
theorem
    exists_r324FullPairingBudgetTerminalAdapter_at_truncation
    (ρ : SmoothCutoff) :
    ∃ supportConstant C K A : ℝ,
      0 < supportConstant ∧ 0 < C ∧
      0 < K ∧ 1 ≤ A ∧
        ∀ (lam ε : ℝ) (q : ℕ)
          (κ : PartialPairing (Fin (2 * q))),
          0 < lam → 0 < ε → ε ≤ 1 →
          1 ≤ |Real.log ε| →
          q ≤ truncOrder ε →
          1 ≤ q → κ.IsFull →
          ∃ budget :
              R324FullPairingBudgetStopTrace
                (ρ := ρ) (C := C) (lam := lam)
                (ε := ε) (K := K) (A := A) κ,
            Nonempty
              (R324FullPairingBudgetTerminalAdapter
                budget) := by
  obtain ⟨supportConstant, C, hsupport, hC, hprop⟩ :=
    proposition41_at_truncation ρ
  obtain ⟨K, hK, hlocal⟩ :=
    exists_r324WithinHalf_localBlockClosure hsupport
  obtain ⟨A, hA, hinitial⟩ :=
    exists_r324InitialWithinHalfEdgeCertificate_one_le_uniform
  refine
    ⟨supportConstant, C, K, A,
      hsupport, hC, hK, hA, ?_⟩
  intro lam ε q κ hlam hε hε1 hlog htrunc hq hκ
  let propProvider :
      R324WithinHalfProp41Provider
        ρ C lam ε supportConstant κ :=
    by
      intro res head tail hremaining H hH
      have hheadSchedule :
          head ∈ r322AnalyticSchedule κ :=
        (res.headContext
          head tail hremaining).step_mem_schedule
      have hheadMapped :
          head.2 ∈
            (r322AnalyticSchedule κ).map Prod.snd :=
        List.mem_map.mpr
          ⟨head, hheadSchedule, rfl⟩
      have hheadExtraction :
          head.2 ∈ extractionBlocks κ :=
        (r322AnalyticSchedule_blocks_perm_extractionBlocks κ)
          |>.mem_iff.mp hheadMapped
      exact
        hprop lam ε
          (residualBlockOrder head.2)
          (res.headContext
            head tail hremaining).one_le_blockOrder
          H hlam hε hε1
          (extractionBlockOrder_le_truncOrder
            κ hκ hheadExtraction ε htrunc)
          hH
  let localProvider :
      R324WithinHalfLocalBlockProvider
        ρ C lam ε K κ := by
    intro res head tail hremaining scale hcertificate
    exact
      hlocal ρ C lam ε (2 * q) κ
        res head tail hremaining scale hcertificate
        hC hlam hε hε1 hlog
        (fun H hH =>
          propProvider res head tail hremaining H hH)
  let budgetProvider :
      R324WithinHalfBudgetLocalBlockProvider
        ρ C lam ε K A κ :=
    r324WithinHalfBudgetLocalBlockProvider_of_localBlockProvider
      hA localProvider
  obtain ⟨budget⟩ :=
    R324FullPairingBudgetStopTrace.exists_of_initial_certificate
      hq hκ hA budgetProvider (hinitial (2 * q))
  obtain ⟨geometry⟩ :=
    R324FullPairingStopTraceAssembly.exists_of_initial_certificate
      hq hκ hε hε1 localProvider (hinitial (2 * q))
  exact
    ⟨budget,
      ⟨R324FullPairingBudgetTerminalAdapter.ofAssembly
        geometry⟩⟩

end R324WithinHalfResidualPrefix

end

end Anderson4D
