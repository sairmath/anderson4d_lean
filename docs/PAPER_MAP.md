# PAPER_MAP — node-by-node map: paper ↔ Lean

Authoritative table of the stable mathematical node IDs and paper-level
dependencies for arXiv:2607.10105v1. Exact declaration links live in
[PAPER_TO_LEAN.md](PAPER_TO_LEAN.md); the generated coarse module inventory is
[PAPER_INDEX.md](PAPER_INDEX.md); the mathematical statements and DAG live in
the [blueprint source](../blueprint/src/content.tex).

Conventions:
- **ID**: stable node identifier used by the blueprint labels.
- **Layer** (DESIGN §4): L0 combinatorics · L1 discrete core · L2 continuum ·
  L3 deterministic parametrix · L4 probability primitives · L5 random
  parametrix · L6 assembly · I infrastructure (not in paper).
- **Lean**: principal module (under `Anderson4D/`) and declaration
  name(s). PAPER_TO_LEAN supplies the clickable, line-specific version.
- **Uses**: node IDs of direct mathematical prerequisites (paper-level).

---

<a id="paper-map-section-2"></a>
## §2 — Preliminaries

| ID | Paper | Content | Layer | Uses | Lean |
|---|---|---|---|---|---|
| D-E | Def 2.1 | class $\mathcal{E}$: invariance under signed coordinate permutations (hyperoctahedral $B_4$, resp. on $(\mathbb{T}^4)^n$) | L2 | — | `Continuum/Basic.lean` · `MemEClassR4`, `MemEClassT4`, `SmoothCutoff` |
| D-pair | Def 2.2 | partial pairing $\kappa$ of a finite index set; pairs $P$, singles $S$; full pairing | L0 | — | `Combinatorics/Pairing.lean` · `PartialPairing` |
| D-int | Def 2.3 | intervals, subintervals, fully paired subinterval, primitive pairing | L0 | D-pair | `Combinatorics/Pairing.lean` · `IsFullyPairedOn`, `IsPrimitive` |
| P-wick | (2.3)–(2.4) | Wick theorem for $\xi_\varepsilon$ moments; chaos decomposition of products | L4 | I-noise, I-isserlis | `Probability/MollifiedWickLaw.lean`, `Parametrix/WickAtBridge.lean` · `NoiseModel.integral_xiEpsProduct_eq_wickPairingSum`, `wickAt_eq_chaosProjProduct` |

The L0 pairing API required by P-3.4 and §4.1 provides
restriction/extension of pairings along interval removal, the induced pairing
$\kappa'$ of Def 3.1(2a), enumeration finsets for fixed index sets, and the
"first fully paired subinterval" selector with its uniqueness lemma.

<a id="paper-map-section-3"></a>
## §3 — Parametrix construction

Every §3 object is split into a **deterministic profile kernel** (L3, all
$G$/$\eta_\varepsilon$ factors, single-index variables as free arguments) and
its **chaos-integrated random kernel** (L5); the Wick reduction lemma
(inside P-3.5b) connects the two and keeps the dependency graph acyclic
(DESIGN §4).

| ID | Paper | Content | Layer | Uses | Lean |
|---|---|---|---|---|---|
| D-Kdet | (3.1)–(3.2) structure | deterministic profile kernels of the chaos expansion, for each $(m,\kappa)$; generalized inputs $[G_0,\dots,G_m]$ | L3 | D-pair, D-int, I-green | `DetParametrix/Core/Kernels.lean` · `detIntegrand` |
| D-RI | Def 3.1 | renormalization at the deterministic level: induction removing smallest-leftmost fully paired subintervals; $J$, $\widetilde G$ ((3.3)–(3.5)) | L3 | D-int, D-Kdet | `DetParametrix/Core/Renormalized.lean` · `detRIkernel` |
| P-3.2 | Prop 3.2 | closed formula (3.6) (difference factors at endpoints $\ell_i, r_i$), deterministic level | L3 | D-RI | `DetParametrix/Core/Renormalized.lean` · `detRIkernel_eq_prod` |
| D-C2q | §3.2, (3.8)–(3.11) | $\mathcal{J}_{2q,\sigma}$, $\mathcal{C}_{2q,\sigma}$, $\mathcal{C}_{2q}$, $\mathcal{C}_\varepsilon$ (deterministic integrals); primitive-with-insertions structure | L3 | D-int, D-RI | `DetParametrix/Core/Kernels.lean` · `detJ`, `renormC2q`, `renormCEps` |
| P-3.3 | Prop 3.3 | closed formula (3.12) for $\mathcal{J}_{2q,\sigma}$ | L3 | D-C2q, P-3.2 | `DetParametrix/Core/Constants.lean` · `renormJ_eq_prod` |
| P-3.5a | (3.22) | $\lvert\mathcal{C}_{2q}\rvert \le \varepsilon^{-2}\lvert\log\varepsilon\rvert^{-1}(C\lambda)^{2q}$ — deterministic | L3 | D-C2q, P-4.1, R-322 | `DetParametrix/Paper41_Renorm/R322AnalyticResidualIteration.lean` · `R322AnalyticResidualPrefix.exists_r322_renormC2q_bound` |
| P-3.5b-det | §4.2 content | Deterministic pairing-sum bound underlying (3.24), incl. the $\langle\alpha\rangle^{-4}\langle\beta\rangle^{-4}\langle\varepsilon^2(\alpha+\beta)\rangle^{-8}$ decay. Step 4(B) uses a signed whole-series common-left Fourier proof of the same decay conclusion, retaining cancellation until the single post-extraction norm. | L3 | P-4.1, R-324 | `DetParametrix/Paper42_Moment/R324PaperWholeSeries{HighProducer,Capstone}.lean` · `SmoothCutoff.exists_r324PaperHighWholeSeriesWeightedMajorantBound`; realized right side `paperDeterministicMomentRHS` |
| D-Im | (3.1)–(3.2) | random kernels $\mathcal{I}_m$, $\mathcal{I}_{m,\kappa}$ = deterministic profile ∫-ed against chaos projections of $\prod\xi_\varepsilon$ | L5 | D-Kdet, I-chaos | `Parametrix/Random.lean` · `wickAt`, `randIntegrand`, `randRI` |
| D-para | (3.13)–(3.15) | random $\mathcal{RI}_{m,\kappa}$, $\mathcal{P}_m$, parametrix $\mathcal{P}_\varepsilon$; operator realization `Kop`, invertibility predicate; **primary mode objects = matrix coefficients** $\langle e_{-\alpha}, ((1-K_\varepsilon)^{-1}G - G)e_\beta\rangle$ (sign aligned to (3.23), checked by a rank-one roundtrip) with junk `0` off the invertibility event; HS-difference lemma **conditioned on invertibility** with the $(1+\log)$-weighted bound (DESIGN §5.2) | L5 | D-Im, D-RI, D-C2q, I-noise | `Parametrix/Random.lean`, `Parametrix/Operators.lean` · `parametrixP`, `Kop`, `operatorModeCoeffH` |
| P-3.4 | Prop 3.4 | key algebraic identity (3.16)–(3.17) of random kernels | L5 | D-para, P-wick, P-3.2, P-3.3 | `Parametrix/IdentityGradedComparison.lean`, `IdentityAECoefficientClosure.lean` · `PartialPairing.xi_comp_parametrix`, `ae_parametrixGradedCoefficientAgreement` |
| P-err | (3.20)–(3.21) | $\mathcal{L}_\varepsilon\mathcal{P}_\varepsilon = 1 + \mathcal{R}_\varepsilon$ (multiplier form), explicit $\mathcal{R}_\varepsilon, \mathcal{R}'_\varepsilon$ | L5 | P-3.4 | `Parametrix/IdentityGradedComparison.lean` · `PartialPairing.leftPreconditionedParametrixAction_eq_green_add_remainder_of_ledger`, right-hand analogue |
| P-3.5b | (3.24) | $\mathbb{E}\lvert\widehat{\mathcal{P}_m}(\alpha,\beta)\rvert^2$ bound = Wick reduction to P-3.5b-det | L5 | P-3.5b-det, P-wick, D-para | `Parametrix/MomentBounds.lean` · `parametrix_coeff_bound` |
| **P-3.6** | Prop 3.6 | moment factorization (3.26)–(3.28) — **external input** (Gabriel–Rosati); quantifier prescription in remark 6 | L6 | D-para, I-torus, D-limit | `Main/External.lean` · `Prop36WithConstant`, witness structure `Prop36`, uniform `Prop36Family` |
| P-L2 | §3.4 Step 1, (3.30)–(3.33) | $\mathbb{E}\lVert\mathcal{P}_m\rVert^2_{L^2\to L^2}$ via Plancherel double sums; $\mathbb{E}\lVert\xi_\varepsilon\rVert^2$ input; Chebyshev good event; one-sided compact Fredholm inversion from the paper's left residual (no $\lVert K_\varepsilon\rVert<1$ assumption); $\lVert\mathcal{L}_\varepsilon^{-1}-\mathcal{P}_\varepsilon\rVert \le \varepsilon^{12}$ | L5 | P-3.5a, P-3.5b, P-err, I-noise, I-l2op, D-para | `Main/GoodEventConstruction.lean`, `Main/DeterministicClosure.lean`, `Parametrix/FredholmCoefficientBridge.lean` |
| P-red | §3.4 Step 2 (finite-mode part) | replacement $\mathcal{H}_\varepsilon \to \mathcal{Q}_\varepsilon$ on the good event for fixed modes (mode functional ≤ op-norm comparison; $\mathbb{P}(Z_\varepsilon)\to 0$). **No tightness** is needed for the finite-mode target | L6 | P-L2, I-weakconv | `Main/GoodEventCharacteristic.lean` · `Prop36.tendsto_fullResolventChar_of_second_moment_and_goodEvent` |
| D-limit | (1.3), (3.25), (3.28) | four-point kernel $H$; $\mathfrak{X}$; nonnegative Cramér–Wold quadratic form on finite complex mode families; realified Gaussian-law interface (incl. conjugate pairs) | L6 | I-green, I-torus | `Continuum/FourPointCoefficient.lean`, `Main/GaussianLimit.lean`, `Main/GaussianPSD.lean` · `fourPointHCoeff`, `limitVar` |
| P-mom | §3.4 Step 3, (3.35)–(3.39) | truncation $\mathcal{Q}_{B,\varepsilon}$; moments → Gaussian ((3.36)–(3.37)); $B \to \infty$ geometric sum $\mathfrak{X}_B \to \frac{2\pi^2}{2\pi^2-\lambda^2}$; conjugate-mode closure (remark 7) | L6 | P-3.5b, P-3.6, I-gaussmm, D-limit | `Main/FixedTruncationGaussian.lean`, `GeometricTruncation.lean`, `TruncationGlue.lean`, `MomentAssembly.lean` |
| **T-1.1** | Thm 1.1 | Conditional Fourier-mode characteristic-function theorem and its finite-vector convergence-in-distribution corollary, with $\forall\rho\,\exists\lambda_0$ quantifiers (DESIGN §2); no unconditional `main` because Proposition 3.6 is an explicit external premise. | L6 | P-red, P-mom, P-3.6 | `Main/Final.lean` · `deterministic_second_moment_bound`, `main_conditional`, `main_conditional_law` |

<a id="paper-map-section-4"></a>
## §4 — Reduction to primitive pairing estimates

| ID | Paper | Content | Layer | Uses | Lean |
|---|---|---|---|---|---|
| I-green | (4.1) | torus Green's function $G$ **defined via the Bessel/heat-kernel time integral of the periodized Gaussian** (a plain Fourier `tsum` is ill-defined: $\langle k\rangle^{-2}\notin\ell^1\cup\ell^2$, $G\notin L^2$ — DESIGN §5.8); $\widehat G(k)=\langle k\rangle^{-2}$ as a lemma; membership in $\mathcal{E}$; $\lvert\nabla^k G(z)\rvert \lesssim \lvert z\rvert^{-2-k}$ ($k \le 2$ suffices); improved bound for $G - \frac{1}{4\pi^2\lvert z\rvert^2}$ | L2/I | I-torus | `Continuum/GreenFourier.lean`, `GreenBounds.lean`, `GreenRemainder.lean` · `paperFourierCoeff_greenFn`, `greenFn_memE`, `abs_greenLocalImprovedRemainder_le` |
| **P-4.1** | Prop 4.1 | primitive pairing estimate: bounds (4.3), (4.4) on $\mathcal{J}_{2n,\text{prim}}$ (with/without the $\varepsilon^2{+}\max\lvert x_i{-}x_j\rvert^2$ insertion) | L2 | R-51, R-4.1pf | `Continuum/PrimitiveProposition41.lean` · `proposition41`, `proposition41_at_truncation` |
| R-322 | §4.1 | proof of (3.22) ⇒ P-3.5a: Dyck-word bookkeeping of nested fully paired subintervals; iterative reduction; Taylor + $\mathcal{E}$-symmetry kills linear term ((4.9)); 3-case integral bounds ((4.10)–(4.12)) | L3 | P-4.1, I-green, D-int, D-C2q | `DetParametrix/Paper41_Renorm/R322AnalyticResidualIteration.lean` · `R322AnalyticResidualPrefix.exists_r322RenormFiberReductionOutputAE` |
| R-324 | §4.2 | Deterministic reduction to P-3.5b-det: interval removals and signed two-half collapse, followed in Step 4(B) by a whole-series common-left Fourier proof with eighth-order IBP for the $(4.16)$–$(4.20)$ decay. | L3 | P-4.1, R-322, D-RI | `DetParametrix/Paper42_Moment/R324{ResidualCommonLeftFourier,PaperEndpointCommonLeftFourier,PaperWholeSeriesHighProducer,PaperWholeSeriesCapstone}.lean` |

<a id="paper-map-section-5"></a>
## §5 — Proof of the primitive pairing estimates

### §5.1 discretization

| ID | Paper | Content | Layer | Uses | Lean |
|---|---|---|---|---|---|
| R-51 | §5.1, (5.1)–(5.5) | reduction of Prop 4.1 to the lattice counting bound (5.5): choice of $\mathcal{A}$, discretization $y_j = \lfloor\varepsilon^{-1}x_j\rfloor$, singular-convolution bounds (5.3), (5.4) | L2 | I-singconv | `Continuum/PrimitiveEndpointPeriodic.lean`, `PrimitiveHigherBound.lean` · `sum_primitiveInsertedIntegrand_lintegral_le_r51GlobalDecayBound`, `exists_uniform_primitiveKernelBounds_ge_two` |

### §5.2 Hepp trees and the two pillar estimates

| ID | Paper | Content | Layer | Uses | Lean |
|---|---|---|---|---|---|
| D-hepp | Def 5.1, 5.3 | Hepp tree; marking $(N_\mathfrak{n})$, multiplicities $(m_\mathfrak{l})$; $\mathcal{B}, \mathcal{L}, \gamma_\mathfrak{n}$, subtree, LCA | L1 | — | `HeppTree/Basic.lean` · `PlaneTree`, `PlaneTree.HeppMarking`, `PlaneTree.Multiplicities` |
| L-5.2 | Lemma 5.2 | # plane rooted trees with $r$ leaves, branching $\ge 2$: $\le C^r$ via explicit injection into Dyck words of bounded length (naive induction on the recurrence does not close; documented proof substitution, DESIGN §5.5) | L0 | — | `Combinatorics/TreeCountReal.lean` · `PlaneTree.key_injective`, `PlaneTree.card_validTreesAtMost_le` |
| D-adm | Def 5.4 | admissible embeddings $(z_\mathfrak{l}) : \mathcal{L} \to \mathbb{Z}^4_M$; $Z \leftrightarrow (\mathcal{T}, N_\mathfrak{n})$; multiset/multiplicity versions | L1 | D-hepp | `HeppTree/Admissible.lean` · `IsAdmissible`, `Realizes` |
| L-5.5 | Lemma 5.5 | existence: every $Z$ (resp. every paired vector $(y_j)$) is realized by some marked Hepp tree, $1 < N_\mathfrak{n} \lesssim M$, $m_\mathfrak{l}$ even | L1 | D-adm | `HeppTree/Decomposition.lean`, `PairedExistence.lean` · `rdec_exists_realizing_marked_tree`, `exists_realizing_tree` |
| R-decomp | (5.6)–(5.11) | sum decomposition: fix $\mathcal{T}$, $(m_\mathfrak{l})$, $\chi$; symmetry-factor denominator; word-sum bound (5.10) with explicit multinomial factors; conditions (a)–(c) | L1 | L-5.5, L-5.2, D-pair, D-int, D-adm | `HeppTree/Decomposition.lean`, `PairedIncidence.lean` · `latticeChainSum_le_treeSum`, `sum_eq_sum_paired_tree_incidence_div` |
| D-ledger | — (interface) | word sums and the definitional factorial ledger: `wordSum`, `paperSum := (∏ (mult l)!) * wordSum` (DESIGN §5.5); statement-boundary conversion lemmas | L1 | D-hepp | `PermSum/Words.lean` · `paperSum`, `wordSum` |
| **P-5.6** | Prop 5.6 | volume estimate: orbit-stabilizer lower bound (5.12) against order-forgetting $\mathrm{Aut}$ (DESIGN §5.5); embedding counts (5.13), (5.14) with $\lvert\mathrm{Aut}\rvert$ factors | L1 | D-adm, L-5.2, I-cayley | `HeppTree/VolumeEstimate.lean` · `volume_estimate` |
| **P-5.7** | Prop 5.7 | permutation-sum estimate (5.15): $\sum_W (n-\lvert W\rvert)!\,(m_\mathfrak{l}!)^{1/2} \cdots$ — the log-loss / factorial-gain balance | L1 | P-5.9 | `PermSum/Main.lean` · `permSum_estimate` |
| R-4.1pf | §5.2 end | **lattice-level assembly** of the (5.1)-form estimate from 5.6 + 5.7: geometric $(N_\mathfrak{n})$ summation (5.16)–(5.17), endpoint refinement $\min(\lvert W\rvert{+}1, n{-}2)$, elementary factorial–log inequality; consumed by P-4.1 through the discretization interface R-51 | L1 | P-5.6, P-5.7, D-ledger | `Continuum/PrimitiveFinalAssembly.lean`, `PrimitiveHigherBound.lean` · `primitive_lattice_estimate`, `exists_uniform_primitiveKernelBounds_ge_two` |

Proof-internal nodes of P-5.6 (§5.3, blueprint will carry all six steps):
orbit-stabilizer (mathlib `MulAction`); $\lvert\mathrm{Aut}(\mathcal{T})\rvert \ge C^{-r}\prod\gamma_\mathfrak{n}!$
via free action on orderings (5.21); geometric Steps 4–5: $\widetilde N_\mathfrak{n}$,
segment-connectivity, ball covering $3(1+\widetilde N_\mathfrak{n}/R)$, link trees,
the **parent-function upper bound** (node I-cayley, a documented proof
substitution for the exact weighted Cayley identity), iteration (5.23)–(5.29).

### §5.4 the inductive machine

| ID | Paper | Content | Layer | Uses | Lean |
|---|---|---|---|---|---|
| D-leaf | Def 5.8 | simple/compound leaves; $\gamma^2_\mathfrak{n}, \gamma^\infty_\mathfrak{n}$; identity (5.31) | L1 | D-hepp | `HeppTree/Leaves.lean` |
| **P-5.9** | Prop 5.9 | generalized inductive estimate (5.33) under (5.32), constants $C_0 > 1000$, $D = e^{C_0^{10}}$ | L1 | P-5.10, D-leaf | `PermSum/Inductive.lean` · `inductive_estimate` |
| <a id="node-r-5-7pf"></a>R-5.7pf | §5.4, (5.34)–(5.37) | Prop 5.7 from 5.9: merge adjacent equal-leaf copies; partition combinatorics; factorial comparison (5.37) | L1 | P-5.9, L-5.12 | `PermSum/Main.lean` |
| **P-5.10** | Prop 5.10 | single-scale-cluster estimate (5.39) with skipped set $O$; no primitivity required | L1 | L-5.12, L-5.13, L-5.14 | `PermSum/SingleScale.lean` · `singleScale_estimate` |
| <a id="node-r-5-9pf"></a>R-5.9pf | §5.4.1 | 5.9 from 5.10 by induction: lowest node with (5.40); collapse $\mathcal{T}_\mathfrak{n}$ to compound leaf as a **word-level `Equiv`** $\pi \leftrightarrow (\pi_1, O, \pi_2)$; comparability (5.41); the $((s+1)!)^{-1}$ of (5.45)(i) enters via the factorial ledger D-ledger, **not** fiber counting (DESIGN §5.5); factor audit (5.42)–(5.48) | L1 | P-5.10, D-leaf, D-ledger | `PermSum/Inductive.lean` · `inductive_estimate` |
| D-5.11 | Def 5.11 | lacunary families of positive integers (each dyadic window $[X,2X]$ contains $O(1)$ of them) | L0 | — | `Combinatorics/BinomialBounds.lean` · `Lacunary` |
| L-5.12 | Lemma 5.12 | binomial/multinomial bounds $\binom{m+n}{m} \le \alpha^m\beta^n$; lacunary version (5.51) | L0 | D-5.11 | `Combinatorics/BinomialBounds.lean` |
| L-5.13 | Lemma 5.13 | monotone-defect sequence counting (5.55), dyadic version (5.56), skip-$\le$100 variant | L0 | L-5.12 | `Combinatorics/SequenceCount.lean` |
| L-5.14 | Lemma 5.14 | bilinear lattice-cluster bound (5.58) with $P = \lvert A\rvert M^4$, $Q = \lvert B\rvert N^4$; dyadic shell counting (5.60)–(5.67) | L1 | — | `PermSum/LocalRefined.lean` · `bilinear_cluster_bound` |
| <a id="node-r-5-10pf"></a>R-5.10pf | §5.4.3, (5.68)–(5.98) | proof of 5.10: power-counting reductions; $(N,X,Y,P)$ scale classification $\sigma_1,\sigma_2,\sigma_3$; outer $\boldsymbol{X}$-sum (5.76)–(5.86) (lacunarity, $S/C$ split); inner $\pi$-sum (5.87)–(5.98) (local inequalities (5.90)–(5.92), parity ordering, $\le$20 skipped factors) | L1 | P-5.10 deps | `PermSum/SingleScale.lean` (proof sections) |

### warm-up (not a numbered paper result)

| ID | Paper | Content | Layer | Uses | Lean |
|---|---|---|---|---|---|
| T-toy | (1.14)–(1.15) | toy estimate: $\sum_{\pi\in S_n}\prod\lvert x_{\pi(j)}-x_{\pi(j+1)}\rvert^{-2} \le C^n (n!)^{1/2}\tau^{-2(n-1)}$ for $\tau$-separated points, via local inequality (1.15) | L1 | — | `PermSum/Toy.lean` · `toy_permSum_bound` |

## §I — Infrastructure nodes (not in the paper)

| ID | Content | Layer | Lean |
|---|---|---|---|
| I-torus | **deterministic Fourier core** on $\mathbb{T}^4$ (`Fin 4 → AddCircle (2π)`): characters, coefficients (3.23), Plancherel, multiplier calculus — required already by I-green, R-324, D-limit | L2/I | `Continuum/TorusFourier.lean` · `torusFourierBasis`, `paperKernelCoeff_eq_volume_sq_smul_normalized` |
| I-noise | white noise as random Fourier series; canonical product space; $\xi_\varepsilon$ a.s. smooth; covariance $\eta_\varepsilon$ | L4 | `Probability/Noise.lean`, `NoiseConstruction.lean`, `NoiseSmoothness.lean`, `Probability/CovariancePoisson.lean` |
| I-isserlis | Isserlis/Wick theorem for finite jointly-Gaussian families | L4 | `Probability/NoiseIsserlis.lean`, `ComplexNoiseIsserlis.lean` |
| I-chaos | minimal chaos-projection API: `Proj_k` of Gaussian polynomials, orthogonality (enough for (2.4), (3.2); Prop 3.6 externalized) | L4 | `Probability/Chaos.lean`, `ChaosDecomposition.lean` |
| I-gaussmm | Gaussian moment method: joint moments → Gaussian moments implies convergence in law (moment-determinacy of Gaussians) | L4 | `Main/FixedTruncationGaussian.lean` |
| I-weakconv | convergence in distribution glue for realified mode vectors; good-event restriction; **filter-indexed** weak-convergence lemmas | L4 | `Probability/WeakConvGlue.lean`, `Main/LawCorollary.lean` |
| I-l2op | kernel ↔ `ContinuousLinearMap` on $L^2(\mathbb{T}^4)$; (3.30) as Plancherel double sums — no named Hilbert–Schmidt API assumed; compact Fredholm inversion; Borel measurable totalized inverse and fixed-mode coefficient bridge | L5 | `Parametrix/L2Bounds.lean`, `Parametrix/L2Fredholm.lean`, `Parametrix/FredholmCoefficientBridge.lean` |
| I-singconv | singular convolution toolkit on $\mathbb{T}^4$: $\lvert z\rvert^{-2}$-chain bounds, (5.3)–(5.4)-type estimates, $\eta_\varepsilon$ support handling | L2 | `Continuum/SingularConv.lean`, `SingularChain.lean` · `binary_conv_invSqKer_le`, `triple_conv_invSqKer_le`, `singularChain_le_pow` |
| I-cayley | parent-function injection bound $\sum_{\mathcal{H}}\prod_i (1+w_i)^{d(i)-1} \le (q + \sum w_i)^{q-1}$ used in (5.24)–(5.25); documented substitution for the exact weighted Cayley identity | L0 | `ForMathlib/WeightedCayley.lean` · `parentCode_one_add_bound_real`, `weightedCayley_le_of_parent_injection` |
| I-green | listed with §4 above | L2/I | `Continuum/GreenFourier.lean`, `GreenBounds.lean`, `GreenRemainder.lean` |

## Statement-design remarks

1. **D-E**: we formalize $\mathcal{E}$ on $\mathbb{T}^4$ (and on $\mathbb{R}^4$ for
   the cutoff) as invariance under the hyperoctahedral group $B_4$
   (coordinate permutations and sign flips) — the only reading used on the
   critical path ((4.9) odd-moment vanishing; §4.2 $\sin$-part vanishing;
   $\int J(z-w)(z-w)\,\mathrm{d}w = 0$). The paper's general-$(\mathbb{T}^4)^n$
   display admits a stronger $B_{4n}$ reading which we neither need nor
   assert.
2. **L-5.2 proof substitution**: an explicit injection of plane trees into
   bounded-length Dyck words replaces the generating-function analyticity
   argument; the blueprint records the resulting exponential bound.
3. **P-5.9/P-5.10 constants**: `C₀`, `D` kept as parameters with hypotheses
   (`1000 < C₀`, `D = exp (C₀^10)`), discharged (absorbed into the running
   constant) in **R-5.7pf** — where the paper derives Prop 5.7 from
   Prop 5.9 — not at R-4.1pf.
4. **A = ⌊|log ε|⌋** enters only through the inequalities actually used
   (e.g. $(C\lambda)^A \varepsilon^{-2} \ll 1$); blueprint records each use site.
5. **Junk-value conventions** (DESIGN §5.7) are stated once in the blueprint
   preliminaries and referenced, not repeated per node.
6. **P-3.6 quantifiers**: one
   positive coefficient-bound constant $C$ is selected uniformly for the
   small-coupling family.  At a fixed coupling, `Prop36WithConstant` says
   that **for every $B$, $r$** there exists a function
   $\mathfrak{X}_B : \mathbb{N}\times\mathbb{N} \to \mathbb{R}$ with
   $\lvert\mathfrak{X}_B(m_1,m_2)\rvert \le C(C\lambda)^{m_1+m_2-2}$ for
   positive orders and the identity (3.28), summed over $m_1,m_2\ge1$:
   $(\lambda/(\sqrt{2}\,\pi))^{m-2}$ for even $m\le B$ and $0$ for odd
   $m\le B$, such that for every positive-order mode family
   there exist $C'$ and $\varepsilon_0 > 0$ with (3.26)–(3.27) holding for
   all $\varepsilon \in (0, \varepsilon_0)$ (`∀ᶠ ε in 𝓝[>] 0`) uniformly over
   orders $m_j \le B$; in particular the (3.26) error is exactly
   $C'\lambda_\varepsilon^r/\lvert\log\varepsilon\rvert$. This matches the
   paper's local quantifier order ($B, r$ fixed *before* $\mathfrak{X}$ is
   produced), while `Prop36Family` retains the one $C$ needed to choose
   $\lambda_0$ before quantifying $\lambda$.  `Prop36` is witness data, not
   an axiom or a Prop-valued structure with hidden data. The statement also
   exposes the measurability and
   integrability of every displayed finite product, which are implicit
   whenever the paper writes these expectations and are required by the
   formal moment method. No global-$\mathfrak{X}$ upgrade is needed: for the
   truncation $\mathcal Q_{B,\varepsilon}$, invoke the proposition at
   order bound $2B$; the aggregate pair covariance is then fixed directly
   by (3.28) through total order $2B$, independently of the chosen table.
7. **Conjugate modes**: P-mom must produce all real moments of the realified
   mode vector; the mode family is closed under negation (adding
   $(-\alpha_j,-\beta_j)$ costs nothing), so that
   $\mathbb{E}[Z_i\overline{Z_j}]$ is available alongside
   $\mathbb{E}[Z_iZ_j]$ (D-limit, DESIGN §2.2).
8. **Closed-formula renormalization** (DESIGN
   §5.7bis): `detRIkernel`/`renormJ` are *defined* by the closed formulas
   (3.6)/(3.12) over a combinatorial endpoint-extraction; the paper's
   recursive Def 3.1 and the closed-form Props 3.2/3.3 merge into one
   equivalence theorem. Node bookkeeping: D-RI's Lean home hosts
   the extraction + closed-form definitions; P-3.2/P-3.3 become the
   equivalence lemmas.
9. **Word-model statements**:
   `paperSum mult F := (∏ l, (mult l)!) * wordSum mult F` is the
   *definitional* ledger. P-5.7, P-5.9 and P-5.10 are stated with
   **`paperSum` on the LHS and the paper's RHS verbatim** (positive
   factorial exponents kept as printed). R-decomp's (5.10) keeps the
   paper's direction: `pairedWordSum` is on the left and
   `(∏ l, (mult l / 2)! / (mult l)!) * paperSum mult F` is on the right.
   Internal proofs manipulate `wordSum`; conversion happens only at
   statement boundaries.
   The collapse of R-5.9pf is a word-level `Equiv`; no fiber counting, no
   quotient types.
