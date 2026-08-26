# R-324 (§4.2): paper–Lean proof correspondence

This note records the correspondence between §4.2 of Deng–Shen,
*The four-dimensional Anderson model: a case study for critical SPDEs*
(arXiv:2607.10105v1), and the Lean proof of the deterministic estimate
underlying (3.24). Citations below refer to §4.2, pages 18–21 of that version.

The paper and Lean prove the same estimate. Steps 1–3 follow the paper's
interval-removal and nested-chain organization. For the total-frequency
factor in Step 4(B), Lean uses a whole-series Fourier argument that preserves
the signed sum until Fourier extraction; the relation between the two proof
organizations is stated explicitly below and in
[PAPER_TO_LEAN](PAPER_TO_LEAN.md#step-4b).

## Starting expression: (4.16)

From (3.6), (3.15), and (3.23), the mode coefficient has the form

```text
P̂_m(α,β) = λ_ε^m Σ_κ ∫_{(T⁴)^{m+2}} e^{i(α·x+β·y)}
             · Π_{j∉{r₁,…,r_s}} G(x_j − x_{j+1})
             · Π_{i=1}^s [G(x_{r_i} − x_{r_i+1})
                           − G(x_{ℓ_i} − x_{r_i+1})]
             · Π_{{i,j}∈κ} η_ε(x_i − x_j)
             · Proj_{|S|} Π_{i∈S} ξ_ε(x_i),
```

where `(x₀, x_{m+1}) := (x,y)`, `κ` ranges over partial pairings of
`[1,m]`, and `S` is the set of singles. The estimate (3.24) has an unweighted
part and a weighted part containing

```text
ε⁻⁸ ⟨α⟩⁻⁴ ⟨β⟩⁻⁴ ⟨ε²(α+β)⟩⁻⁸.
```

Steps 1–3 give the unweighted estimate. Step 4 supplies the displayed decay.

## Step 1: deterministic terms

Assume `κ` is a full pairing.

1. Choose the maximal rightmost fully paired interval. It has the form
   `I* = [a,m]`.
2. Remove fully paired subintervals successively, first to the left of `I*`
   and then inside `I*`. Each application of Proposition 4.1 contributes a
   factor `Cλ` and replaces the removed block by an input `H` satisfying
   `|H(z)| ≲ |z|⁻²`, as in (4.13).
3. The remaining block carries a primitive full pairing on `2p` sites. The
   resulting expression is (4.17), with a factor `(Cλ)^{m-2p}` and integrand
   containing

   ```text
   G₀(x − x_a) · J_{2p,prim}(x_a − x_m)
     · [G(x_m − y) − G(x_a − y)].
   ```

4. Fourier integration in `y` gives

   ```text
   ∫ e^{iβ·y}[G(x_m−y) − G(x_a−y)] dy
     = ⟨β⟩⁻² e^{iβ·x_a}(e^{iβ·(x_m−x_a)} − 1).
   ```

5. Since `J_{2p,prim}` belongs to the symmetry class `E`, its imaginary
   contribution vanishes. The real part is controlled by

   ```text
   ⟨β⟩⁻² |cos(β·(x_m−x_a)) − 1|
     ≤ ε² + max_{i,j∈I*}|x_i−x_j|².
   ```

6. This is the insertion appearing in (4.4). Replacing `J_{2p,prim}` by its
   inserted form and applying Proposition 4.1 yields the required integrable
   majorant. Integrating the remaining variables gives

   ```text
   |P̂_m(α,β)| ≤ (Cλ)^m |log ε|⁻¹.
   ```

Lean packages this route in
[`exists_r324Step1_deterministic_bound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperStep1.lean#L493).

## Step 2: second moment and interval removal

1. Wick expansion identifies the sum over the two partial pairings and their
   cross-contractions with a sum over full pairings of `[1,2m]`.
2. Extract the fully paired subintervals contained wholly in `[1,m]` or in
   `[m+1,2m]`, and fix their positions. The number of interval configurations
   is bounded exponentially in `m`.
3. For each configuration, (4.18) is the physical integral with four external
   Green legs, the two chain products, the endpoint difference factors, and
   the covariance product.
4. Sum over the primitive pairing on each extracted interval and remove the
   interval using Proposition 4.1, exactly as in §4.1. The signed physical
   integrand is retained through all removals.
5. Only after the removals are complete are absolute values taken. The
   replacement inputs are then bounded by `|z|⁻²`, producing (4.19).

The positional count is
[`card_intervalConfigs_two_mul_le`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperStep23.lean#L203),
and the per-configuration conclusion is
[`exists_r324Step23_config_bound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperClosure.lean#L362).
The bridge from the deterministic second-moment sum to the initial two-half
physical integral is
[`momentRefinedDeterministicTermSum_eq_initialTwoHalfRoot`](../Anderson4D/DetParametrix/Paper42_Moment/R324CertifiedNonemptyRootEndpointBridge.lean#L340).

## Step 3: nested cross blocks

After the within-half removals, the surviving pairing is primitive and not
full on each half. Consequently every remaining fully paired interval crosses
the central cut, and these intervals are nested:

```text
1 ≤ a_t < ⋯ < a₁ ≤ p < p+1 ≤ b₁ < ⋯ < b_t ≤ p+q.
```

For the innermost interval `[a₁,b₁]`, Proposition 4.1 with the insertion from
(4.4) bounds the primitive block. The elementary two-endpoint convolution

```text
∫_{T⁸} |x_{a₁−1}−u|⁻² · J̃_{k₁,prim}(u−v)
        · |v−x_{b₁+1}|⁻² du dv
```

is uniformly bounded. Removing this block reconstructs the same form on the
next nested interval. Iteration removes the nested chain, after which one
last application of (4.4) closes the residual primitive pairing. The result is

```text
(Cλ)^{2m}|log ε|⁻¹
  ≤ λ_ε² · C(Cλ)^{2m−2}.
```

Lean represents the nested reduction by the two-half-to-nested identity
[`twoHalf_lamEps_pow_integral_eq_initialNested`](../Anderson4D/DetParametrix/Paper42_Moment/R324CertifiedTwoHalfPhysicalCollapse.lean#L348),
the primitive-head provider
[`exists_r324ProperHeadSharpProvider`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperProperHeadProvider.lean#L118),
and the physical nested-chain estimate
[`exists_terminalPayload_physicalIntegral_le`](../Anderson4D/DetParametrix/Paper42_Moment/R324NestedCrossBudgetIteration.lean#L980).
The assembled Step 3 inputs are exposed by
[`exists_r324Step3_handoff_inputs`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperStep3Capstone.lean#L75).

<a id="integrability-recipe"></a>
## Fixed-scale integrability recipe

All Fubini and measure-preserving reindexing steps are justified at a fixed
scale `ε > 0` on the genuine finite product space. The recurring argument is:

1. **Bound the covariance factors.** At fixed scale, every mollified
   covariance factor is bounded; hence any finite marked covariance product
   is bounded. The relevant uniform statement is
   [`exists_norm_r324MarkedPairingCovarianceProductOn_le`](../Anderson4D/DetParametrix/Paper42_Moment/R324InitialTwoHalfRootIntegrability.lean#L649).
2. **Integrate the Green chains jointly.** Each residual half is a finite
   chain of Green or `|z|⁻²`-majorized factors on the torus. Joint
   integrability is propagated through one removal by
   [`integrable_residualIntegrand_afterHead`](../Anderson4D/DetParametrix/Paper42_Moment/R324WithinHalfResidualIntegrability.lean#L633)
   and along a certified trace by
   [`eventually_weightedIntegrableAlong_const_initial`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperTraceIntegrable.lean#L137).
3. **Multiply bounded and integrable factors.** The bounded covariance
   product times the two integrable residual halves is integrable; this gives
   [`integrable_terminalMarkedPhysicalCore`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperNestedIntegrable.lean#L42).
4. **Transport integrability through reindexing.** Coordinate regroupings are
   implemented by measurable equivalences that preserve the product measure,
   notably
   [`measurePreserving_terminalProductPiMeasurableEquivNested`](../Anderson4D/DetParametrix/Paper42_Moment/R324TwoHalfToNestedCrossBridge.lean#L299).
   After transport, the nested physical core is integrable by
   [`integrable_initialNestedMarkedPhysicalCore`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperNestedIntegrable.lean#L96).

This fixed-scale argument supplies the hypotheses required before applying
Fubini; it does not rely on pointwise integrability of exceptional fixed
sections.

## Step 4: frequency decay

### Step 4(A): endpoint frequencies

The four external integrations in (4.18) yield two powers of Green Fourier
decay on each side. If an endpoint is outside every removed interval, its
oscillation is used after the interval removals and before taking norms. If it
lies in a terminal fully paired interval, the Step 1 cosine-difference
identity is used, now with the bound `|cos θ − 1| ≤ 2`. Applying this at all
four endpoints gives

```text
ε⁻⁸ ⟨α⟩⁻⁴ ⟨β⟩⁻⁴.
```

The residual and full-half endpoint cases are realized by
[`exists_r324PaperResidualEndpointWeightedMajorantBound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperResidualEndpointPatternProducer.lean#L175)
and
[`exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperFullFullZeroShiftProducer.lean#L478).

### Step 4(B): total frequency

The paper views the renormalized term as a composition of at most
`⌊|log ε|⌋` convolution and multiplication factors. If the total shift
`|α+β|` is of size `L ≥ ε⁻²`, a first-large-slot argument produces a factor
whose shift is at least `ε^{1/2}L`; rapid decay of the mollifier at that slot
gives `⟨ε²L⟩⁻⁸`.

Lean obtains the same total-frequency factor from the complete signed
cross-covariance family. It translates the common surviving left half,
identifies the whole-series Fourier coefficient, chooses a nonzero coordinate
of the external frequency, and applies eight periodic integrations by parts
before taking the norm. The central Fourier estimate is
[`norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le`](../Anderson4D/DetParametrix/Paper42_Moment/R324ResidualCommonLeftFourier.lean#L208),
and the resulting whole-series bound is
[`exists_r324PaperHighWholeSeriesWeightedMajorantBound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperWholeSeriesHighProducer.lean#L3140).

Thus both proof organizations yield the required factor
`⟨ε²(α+β)⟩⁻⁸`; the Lean organization keeps the cancellation in the signed
family until Fourier extraction.

## Final Lean endpoints

| Paper component | Checked Lean endpoint |
|---|---|
| Step 1, deterministic full pairings | [`exists_r324Step1_deterministic_bound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperStep1.lean#L493) |
| Steps 2–3, unweighted second moment | [`exists_r324Step23_config_bound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperClosure.lean#L362), [`exists_r324Step3_handoff_inputs`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperStep3Capstone.lean#L75) |
| Step 4(A), endpoint decay | [`exists_r324PaperResidualEndpointWeightedMajorantBound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperResidualEndpointPatternProducer.lean#L175), [`exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperFullFullZeroShiftProducer.lean#L478) |
| Step 4(B), total-frequency decay | [`exists_r324PaperHighWholeSeriesWeightedMajorantBound`](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperWholeSeriesHighProducer.lean#L3140) |
| Deterministic bound underlying (3.24) | [`Anderson4D.deterministic_second_moment_bound`](../Anderson4D/Main/Final.lean#L28) |
| Conditional Theorem 1.1 | [`Anderson4D.main_conditional`](../Anderson4D/Main/Final.lean#L48), [`Anderson4D.main_conditional_law`](../Anderson4D/Main/Final.lean#L60) |

For the complete paper-number-to-declaration index, see
[PAPER_TO_LEAN](PAPER_TO_LEAN.md).
