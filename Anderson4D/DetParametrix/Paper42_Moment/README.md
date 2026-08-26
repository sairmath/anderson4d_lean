# Paper §4.2: the deterministic moment bound

This directory contains the Lean proof of the signed two-half estimate in
paper §4.2, equations (4.16)–(4.20). Its public output is the deterministic
half of (3.24), exposed as
[`Anderson4D.deterministic_second_moment_bound`](../../Main/Final.lean#L28).

For the mathematical argument and a detailed paper–Lean correspondence, read
[`docs/R324_PAPER_PROOF.md`](../../../docs/R324_PAPER_PROOF.md). For lookup by
paper equation or proposition, use
[`docs/PAPER_TO_LEAN.md`](../../../docs/PAPER_TO_LEAN.md#step-4b).

## Proof route

1. **Step 1 — deterministic full pairings.** Successive removal of fully
   paired intervals and the terminal cosine-difference estimate are assembled
   in
   [`exists_r324Step1_deterministic_bound`](R324PaperStep1.lean#L493).

2. **Step 2 — second moment and within-half removals.** The Wick pairing is
   rewritten as the two-half physical integral, interval configurations are
   counted by
   [`card_intervalConfigs_two_mul_le`](R324PaperStep23.lean#L203), and each
   fixed configuration is closed by
   [`exists_r324Step23_config_bound`](R324PaperClosure.lean#L362). The exact
   bridge into the physical integral is
   [`momentRefinedDeterministicTermSum_eq_initialTwoHalfRoot`](R324CertifiedNonemptyRootEndpointBridge.lean#L340).

3. **Step 3 — nested cross blocks.** The surviving cross-cut intervals form a
   nested chain. Its physical estimate is
   [`exists_terminalPayload_physicalIntegral_le`](R324NestedCrossBudgetIteration.lean#L980),
   and the assembled Steps 2–3 input is
   [`exists_r324PaperRefinedStep23Input`](R324PaperRefinedStep23Closure.lean#L237).

4. **Step 4 — Fourier decay.** Endpoint oscillations supply the
   `⟨α⟩⁻⁴⟨β⟩⁻⁴` factor through the residual and full/full endpoint
   producers below. The total-frequency factor `⟨ε²(α+β)⟩⁻⁸` is obtained
   from the complete signed series: after common-left Fourier extraction,
   eight periodic integrations by parts give
   [`norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le`](R324ResidualCommonLeftFourier.lean#L208),
   which feeds the whole-series high-frequency producer. The relation to the
   paper's first-large-slot presentation is documented in the
   [Step 4(B) crosswalk](../../../docs/PAPER_TO_LEAN.md#step-4b).

## Three final producers

| Role | Public producer |
|---|---|
| Residual endpoint cases | [`exists_r324PaperResidualEndpointWeightedMajorantBound`](R324PaperResidualEndpointPatternProducer.lean#L175) |
| Full/full zero-shift endpoint case | [`exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound`](R324PaperFullFullZeroShiftProducer.lean#L478) |
| Whole-series total-frequency decay | [`exists_r324PaperHighWholeSeriesWeightedMajorantBound`](R324PaperWholeSeriesHighProducer.lean#L3140) |

Together with the closed Steps 2–3 input, these three producers are consumed
by
[`r324PaperScale_hdet_of_exists_paperEndpointCases_and_highWholeSeries`](R324PaperWholeSeriesCapstone.lean#L305).
That capstone is invoked directly by
[`deterministic_second_moment_bound`](../../Main/Final.lean#L28), which then
feeds the random moment estimate and the conditional main theorem.
