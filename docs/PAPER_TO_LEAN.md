# PAPER_TO_LEAN — paper numbers ↔ public Lean declarations

This is the exact reader index for
[Deng--Shen, arXiv:2607.10105v1](https://arxiv.org/pdf/2607.10105v1). It records
the public declaration names; source links point at the corresponding
definitions.

<a id="scope"></a>
## Scope and sources of truth

The formal target is the **conditional** finite-mode form of Theorem 1.1.
[Anderson4D.main_conditional](../Anderson4D/Main/Final.lean#L47) supplies the
characteristic-function form, and
[Anderson4D.main_conditional_law](../Anderson4D/Main/Final.lean#L59) supplies
the advertised finite-vector convergence-in-distribution form. Both take
[Anderson4D.Prop36Family](../Anderson4D/Main/External.lean#L155) as an explicit
hypothesis. Proposition 3.6 is quoted by the paper from Gabriel--Rosati; its
proof is not formalized here. Consequently this repository has **no
unconditional `main`**.

The navigation documents have deliberately different jobs:

| Document | Authoritative for |
|---|---|
| [DESIGN.md](DESIGN.md) | scope, architecture, and formalization policy |
| [PAPER_MAP.md](PAPER_MAP.md) | stable node IDs, paper-level dependencies, and naming |
| **PAPER_TO_LEAN.md** | exact paper number ↔ public declaration links |
| [PAPER_INDEX.md](PAPER_INDEX.md) | generated, coarse `Paper:`-tag inventory for every module |
| [blueprint source](../blueprint/src/content.tex) | mathematical statements and dependency DAG |
| [PAPER_NOTES.md](PAPER_NOTES.md) | explicit formalization conventions for local readings of arXiv v1 |

<a id="how-to-read"></a>
## How to read the tables

- “Paper” gives the definition, lemma, proposition, step, or formula range in
  v1. Formula ranges group adjacent lines that share one formal interface.
- Blueprint DAG nodes link to their exact TeX statements.  The proof-range
  map-only IDs `R-5.7pf`, `R-5.9pf`, and `R-5.10pf` instead link to their
  `PAPER_MAP` rows because they organize proof ranges rather than standalone
  blueprint statements.
- “Lean” names a public declaration, not merely an implementation file.
  Names are namespace-qualified where that prevents ambiguity.
- `#L` fragments are conveniences, not identities: if later edits move a
  line, search the linked file for the displayed declaration name.

<a id="paper-section-1"></a>
## §1 — statement and toy model

| Paper | Node | Role | Lean |
|---|---|---|---|
| (1.14)–(1.15) | [T-toy](../blueprint/src/chapter/permsum.tex#L25) | warm-up permutation estimate | [Anderson4D.toy_permSum_bound](../Anderson4D/PermSum/Toy.lean#L623) |
| Theorem 1.1 | [T-1.1](../blueprint/src/chapter/main.tex#L84) | conditional finite-vector convergence in distribution | [Anderson4D.MainStatement](../Anderson4D/Main/Theorem.lean#L57), [Anderson4D.MainConditional](../Anderson4D/Main/Theorem.lean#L72), [Anderson4D.MainLawStatement](../Anderson4D/Main/LawCorollary.lean#L189), [Anderson4D.mainLawStatement_of_mainStatement](../Anderson4D/Main/LawCorollary.lean#L200), [Anderson4D.mainConditionalLaw_of_mainConditional](../Anderson4D/Main/LawCorollary.lean#L285), [Anderson4D.main_conditional](../Anderson4D/Main/Final.lean#L47), [Anderson4D.main_conditional_law](../Anderson4D/Main/Final.lean#L59) |

<a id="paper-section-2"></a>
## §2 — preliminaries

| Paper | Node | Role | Lean |
|---|---|---|---|
| Definition 2.1 | [D-E](../blueprint/src/chapter/continuum.tex#L6) | symmetry class on Euclidean and torus kernels | [Anderson4D.MemEClassR4](../Anderson4D/Continuum/Basic.lean#L72), [Anderson4D.MemEClassT4](../Anderson4D/Continuum/Basic.lean#L77), [Anderson4D.SmoothCutoff](../Anderson4D/Continuum/Basic.lean#L129) |
| Definition 2.2 | [D-pair](../blueprint/src/chapter/combinatorics.tex#L7) | partial pairings and paired/single sites | [Anderson4D.PartialPairing](../Anderson4D/Combinatorics/Pairing.lean#L44) |
| Definition 2.3 | [D-int](../blueprint/src/chapter/combinatorics.tex#L17) | fully paired intervals and primitivity | [Anderson4D.IsFullyPairedOn](../Anderson4D/Combinatorics/Pairing.lean#L301), [Anderson4D.IsPrimitive](../Anderson4D/Combinatorics/Pairing.lean#L399) |
| (2.3)–(2.4) | [P-wick](../blueprint/src/chapter/probability.tex#L49) | Wick pairing sum and chaos-product bridge | [Anderson4D.NoiseModel.integral_xiEpsProduct_eq_wickPairingSum](../Anderson4D/Probability/MollifiedWickLaw.lean#L192), [Anderson4D.wickAt_eq_chaosProjProduct](../Anderson4D/Parametrix/WickAtBridge.lean#L215) |

<a id="paper-section-3"></a>
## §3 — parametrix construction and main reduction

| Paper | Node | Role | Lean |
|---|---|---|---|
| (3.1)–(3.2) | [D-Kdet](../blueprint/src/chapter/detparametrix.tex#L7) | deterministic profile integrand | [Anderson4D.detIntegrand](../Anderson4D/DetParametrix/Core/Kernels.lean#L106) |
| Definition 3.1; (3.3)–(3.5) | [D-RI](../blueprint/src/chapter/detparametrix.tex#L18) | renormalized deterministic kernel | [Anderson4D.detRIkernel](../Anderson4D/DetParametrix/Core/Renormalized.lean#L243) |
| Proposition 3.2; (3.6)–(3.7) | [P-3.2](../blueprint/src/chapter/detparametrix.tex#L27) | recursive/closed-form and difference-factor identities | [Anderson4D.raw_sub_counterterm_eq_difference](../Anderson4D/DetParametrix/Core/Renormalized.lean#L61), [Anderson4D.detRIkernel_eq_prod](../Anderson4D/DetParametrix/Core/Renormalized.lean#L303) |
| (3.8)–(3.11) | [D-C2q](../blueprint/src/chapter/detparametrix.tex#L38) | deterministic integrals and renormalization constants | [Anderson4D.detJ](../Anderson4D/DetParametrix/Core/Kernels.lean#L178), [Anderson4D.renormC2q](../Anderson4D/DetParametrix/Core/Kernels.lean#L212), [Anderson4D.renormCEps](../Anderson4D/DetParametrix/Core/Kernels.lean#L219) |
| Proposition 3.3; (3.12) | [P-3.3](../blueprint/src/chapter/detparametrix.tex#L48) | closed product formula for the constant integrand | [Anderson4D.renormJ_eq_prod](../Anderson4D/DetParametrix/Core/Constants.lean#L213) |
| (3.13)–(3.15) | [D-para](../blueprint/src/chapter/parametrix.tex#L17) | random parametrix and operator coefficients | [Anderson4D.parametrixP](../Anderson4D/Parametrix/Random.lean#L66), [Anderson4D.neumannCoeff](../Anderson4D/Parametrix/Random.lean#L91), [Anderson4D.operatorModeCoeffH](../Anderson4D/Parametrix/Operators.lean#L48) |
| Proposition 3.4; (3.16)–(3.19) | [P-3.4](../blueprint/src/chapter/parametrix.tex#L36) | graded parametrix identity | [Anderson4D.PartialPairing.xi_comp_parametrix](../Anderson4D/Parametrix/IdentityGradedComparison.lean#L262), [Anderson4D.PartialPairing.ae_parametrixGradedCoefficientAgreement](../Anderson4D/Parametrix/IdentityAECoefficientClosure.lean#L1313) |
| (3.20)–(3.21) | [P-err](../blueprint/src/chapter/parametrix.tex#L55) | left/right preconditioned error identities | [Anderson4D.PartialPairing.leftPreconditionedParametrixAction_eq_green_add_remainder_of_ledger](../Anderson4D/Parametrix/IdentityGradedComparison.lean#L288), [Anderson4D.PartialPairing.rightPreconditionedParametrixAction_eq_green_add_remainder_of_ledger](../Anderson4D/Parametrix/IdentityGradedComparison.lean#L317) |
| (3.22) | [P-3.5a](../blueprint/src/chapter/detparametrix.tex#L54) | bound on each renormalization constant | [Anderson4D.R322AnalyticResidualPrefix.exists_r322_renormC2q_bound](../Anderson4D/DetParametrix/Paper41_Renorm/R322AnalyticResidualIteration.lean#L2684) |
| (3.23) | [I-torus](../blueprint/src/chapter/continuum.tex#L14) | paper-normalized torus Fourier coefficient | [Anderson4D.paperKernelCoeff_eq_volume_sq_smul_normalized](../Anderson4D/Continuum/TorusFourier.lean#L631) |
| (3.24), deterministic half | [P-3.5b-det](../blueprint/src/chapter/detparametrix.tex#L71) | deterministic pairing-sum bound | [Anderson4D.SmoothCutoff.exists_r324PaperHighWholeSeriesWeightedMajorantBound](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperWholeSeriesHighProducer.lean#L3139), [Anderson4D.deterministic_second_moment_bound](../Anderson4D/Main/Final.lean#L27) |
| (3.24), random half | [P-3.5b](../blueprint/src/chapter/parametrix.tex#L69) | Wick reduction and coefficient second moment | [Anderson4D.NoiseModel.wickAtSecondMomentLaw](../Anderson4D/Parametrix/MollifiedWickSecondMoment.lean#L27), [Anderson4D.parametrix_coeff_bound](../Anderson4D/Parametrix/MomentBounds.lean#L509) |
| (3.25), (3.28) | [D-limit](../blueprint/src/chapter/main.tex#L28) | four-point coefficient and Gaussian quadratic form | [Anderson4D.fourPointHCoeff](../Anderson4D/Continuum/FourPointCoefficient.lean#L25), [Anderson4D.limitVar](../Anderson4D/Main/GaussianLimit.lean#L72) |
| Proposition 3.6; (3.26)–(3.28) | [P-3.6](../blueprint/src/chapter/main.tex#L7) | **external hypothesis family**, not a proved GR26 theorem | [Anderson4D.Prop36WithConstant](../Anderson4D/Main/External.lean#L28), [Anderson4D.Prop36](../Anderson4D/Main/External.lean#L90), [Anderson4D.Prop36Family](../Anderson4D/Main/External.lean#L155) |
| §3.4 Step 1; (3.30)–(3.33) | [P-L2](../blueprint/src/chapter/parametrix.tex#L81) | kernel/operator and good-event construction | [Anderson4D.MainGoodEvent.nonempty_fixedModeGoodEventData_of_deterministic_bounds](../Anderson4D/Main/GoodEventConstruction.lean#L298), [Anderson4D.mainSecondMomentInput_of_deterministicMomentBound](../Anderson4D/Main/DeterministicClosure.lean#L30) |
| §3.4 Step 2; (3.34) | [P-red](../blueprint/src/chapter/main.tex#L45) | replace full resolvent modes by the controlled parametrix | [Anderson4D.Prop36.tendsto_fullResolventChar_of_second_moment_and_goodEvent](../Anderson4D/Main/GoodEventCharacteristic.lean#L201) |
| §3.4 Step 3; (3.35)–(3.39) | [P-mom](../blueprint/src/chapter/main.tex#L61) | fixed truncation, Gaussian moments, and geometric tail | [Anderson4D.Prop36.tendsto_fixedTruncationCharFun](../Anderson4D/Main/FixedTruncationGaussian.lean#L581), [Anderson4D.Prop36.tendsto_fullParametrixChar_of_geometric_second_moment_bound](../Anderson4D/Main/GeometricTruncation.lean#L231), [Anderson4D.tsum_prop36EvenTerms_eq_limitPrefactor](../Anderson4D/Main/MomentAssembly.lean#L228) |

<a id="paper-section-4"></a>
## §4 — reduction to primitive estimates

| Paper | Node | Role | Lean |
|---|---|---|---|
| (4.1) | [I-green](../blueprint/src/chapter/continuum.tex#L26) | Green kernel, Fourier coefficient, and singular bounds | [Anderson4D.greenFn](../Anderson4D/Continuum/GreenFunction.lean#L44), [Anderson4D.paperFourierCoeff_greenFn](../Anderson4D/Continuum/GreenFourier.lean#L651), [Anderson4D.greenFn_memE](../Anderson4D/Continuum/GreenBounds.lean#L505) |
| Proposition 4.1; (4.2)–(4.4) | [P-4.1](../blueprint/src/chapter/continuum.tex#L69) | primitive-pairing estimates, with and without insertion | [Anderson4D.proposition41_at_truncation](../Anderson4D/Continuum/PrimitiveProposition41.lean#L176), [Anderson4D.proposition41](../Anderson4D/Continuum/PrimitiveProposition41.lean#L204) |
| §4.1; (4.5)–(4.15) | [R-322](../blueprint/src/chapter/detparametrix.tex#L61) | interval removals and the (3.22) reduction | [Anderson4D.R322AnalyticResidualPrefix.exists_r322RenormFiberReductionOutputAE](../Anderson4D/DetParametrix/Paper41_Renorm/R322AnalyticResidualIteration.lean#L2468), [Anderson4D.R322AnalyticResidualPrefix.exists_r322_renormC2q_bound](../Anderson4D/DetParametrix/Paper41_Renorm/R322AnalyticResidualIteration.lean#L2684) |
| §4.2; (4.16)–(4.20) | [R-324](../blueprint/src/chapter/detparametrix.tex#L80) | signed two-half reduction, endpoint cases, and total-frequency decay | [Anderson4D.R324WithinHalfResidualPrefix.exists_r324PaperResidualEndpointWeightedMajorantBound](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperResidualEndpointPatternProducer.lean#L175), [Anderson4D.exists_r324PaperFullEndpointZeroShiftWeightedMajorantBound](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperFullFullZeroShiftProducer.lean#L478), [Anderson4D.SmoothCutoff.exists_r324PaperHighWholeSeriesWeightedMajorantBound](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperWholeSeriesHighProducer.lean#L3139) |

<a id="step-4b"></a>
### §4.2 Step 4(B): paper route and Lean route

The paper uses a first-large/high-slot argument to obtain the
`<ε²(α+β)>⁻⁸` factor in (4.16)–(4.20).  Lean proves the same required decay
while retaining the complete signed family:

1. retain the complete signed open series through all interval removals;
2. translate the common surviving left half and identify the Fourier
   coefficient of the **whole** cross-covariance family via
   [Anderson4D.R324WithinHalfResidualPrefix.r324CommonLeftFourierCoefficient](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperEndpointCommonLeftFourier.lean#L256);
3. choose a nonzero coordinate of the external frequency and apply the
   [eight-fold periodic integration-by-parts bound](../Anderson4D/Continuum/PeriodicFourierIBPIteration.lean#L186) to the complete product; the cross-family estimate is
   [Anderson4D.norm_fourierCoeffOn_r324MomentCrossCommonLeftCoordLineC_le](../Anderson4D/DetParametrix/Paper42_Moment/R324ResidualCommonLeftFourier.lean#L208);
4. take the first norm only after Fourier extraction, then reassemble the
   signed series in
   [Anderson4D.SmoothCutoff.exists_r324PaperHighWholeSeriesWeightedMajorantBound](../Anderson4D/DetParametrix/Paper42_Moment/R324PaperWholeSeriesHighProducer.lean#L3139).

Thus the paper and Lean reach the same
`<ε²(α+β)>⁻⁸` decay conclusion by different proof organizations: the paper
uses a first-large/high slot, while Lean uses the whole-series common-left
Fourier coefficient.  The detailed correspondence, including Step 4(A), is
recorded in [R324_PAPER_PROOF](R324_PAPER_PROOF.md#step-4-frequency-decay).

<a id="paper-section-5"></a>
## §5 — proof of Proposition 4.1

| Paper | Node | Role | Lean |
|---|---|---|---|
| §5.1; (5.1)–(5.5) | [R-51](../blueprint/src/chapter/continuum.tex#L58) | discretization and primitive integral reduction | [Anderson4D.pairedCellConstraints_of_covariance_ne_zero](../Anderson4D/Continuum/Discretization.lean#L474), [Anderson4D.sum_primitiveInsertedIntegrand_lintegral_le_r51GlobalDecayBound](../Anderson4D/Continuum/PrimitiveEndpointPeriodic.lean#L1528) |
| Definitions 5.1, 5.3 | [D-hepp](../blueprint/src/chapter/hepp.tex#L8) | plane trees, markings, multiplicities, automorphisms | [Anderson4D.PlaneTree](../Anderson4D/HeppTree/Basic.lean#L33), [Anderson4D.PlaneTree.HeppMarking](../Anderson4D/HeppTree/Basic.lean#L431), [Anderson4D.PlaneTree.Multiplicities](../Anderson4D/HeppTree/Basic.lean#L441) |
| Lemma 5.2 | [L-5.2](../blueprint/src/chapter/combinatorics.tex#L31) | exponential tree count | [Anderson4D.PlaneTree.key_injective](../Anderson4D/HeppTree/Basic.lean#L498), [Anderson4D.PlaneTree.card_validTreesAtMost_le](../Anderson4D/Combinatorics/TreeCountReal.lean#L237) |
| Definition 5.4 | [D-adm](../blueprint/src/chapter/hepp.tex#L27) | admissible realization | [Anderson4D.IsAdmissible](../Anderson4D/HeppTree/Admissible.lean#L158), [Anderson4D.Realizes](../Anderson4D/HeppTree/Admissible.lean#L171) |
| Lemma 5.5 | [L-5.5](../blueprint/src/chapter/hepp.tex#L39) | existence of a realizing marked tree | [Anderson4D.rdec_exists_realizing_marked_tree](../Anderson4D/HeppTree/Decomposition.lean#L991), [Anderson4D.exists_realizing_tree](../Anderson4D/HeppTree/Decomposition.lean#L1046) |
| (5.6)–(5.11) | [R-decomp](../blueprint/src/chapter/hepp.tex#L50) | Hepp-tree incidence and lattice-chain decomposition | [Anderson4D.latticeChainSum_le_treeSum](../Anderson4D/HeppTree/Decomposition.lean#L1338), [Anderson4D.sum_eq_sum_paired_tree_incidence_div](../Anderson4D/HeppTree/PairedIncidence.lean#L202) |
| (5.12)–(5.14), Proposition 5.6 | [P-5.6](../blueprint/src/chapter/hepp.tex#L79) | volume estimate | [Anderson4D.volume_estimate](../Anderson4D/HeppTree/VolumeEstimate.lean#L3502) |
| (5.15), Proposition 5.7 | [P-5.7](../blueprint/src/chapter/permsum.tex#L93) | final permutation-sum estimate | [Anderson4D.PermSumEstimate](../Anderson4D/PermSum/Statements.lean#L181), [Anderson4D.permSum_estimate](../Anderson4D/PermSum/Main.lean#L314) |
| (5.16)–(5.17) | [R-4.1pf](../blueprint/src/chapter/permsum.tex#L106) | lattice-level assembly of Proposition 4.1 from Propositions 5.6 and 5.7 | [Anderson4D.primitive_lattice_estimate](../Anderson4D/Continuum/PrimitiveFinalAssembly.lean#L1721), [Anderson4D.exists_uniform_primitiveKernelBounds_ge_two](../Anderson4D/Continuum/PrimitiveHigherBound.lean#L27) |
| §5.3; (5.18)–(5.29) | [P-5.6](../blueprint/src/chapter/hepp.tex#L79) | proof of the volume estimate | [Anderson4D.volume_estimate](../Anderson4D/HeppTree/VolumeEstimate.lean#L3502) |
| Definitions/interfaces around (5.30) | [D-ledger](../blueprint/src/chapter/permsum.tex#L7) | words and the factorial ledger | [Anderson4D.validWords](../Anderson4D/PermSum/Words.lean#L433), [Anderson4D.wordSum](../Anderson4D/PermSum/Words.lean#L482), [Anderson4D.paperSum](../Anderson4D/PermSum/Words.lean#L487) |
| Definition 5.8; (5.31) | [D-leaf](../blueprint/src/chapter/permsum.tex#L55) | simple/compound leaves and gamma invariants | [Anderson4D.compoundLeaves](../Anderson4D/HeppTree/Leaves.lean#L9), [Anderson4D.simpleLeaves](../Anderson4D/HeppTree/Leaves.lean#L12), [Anderson4D.gamma2](../Anderson4D/HeppTree/Leaves.lean#L19) |
| (5.32)–(5.33), Proposition 5.9 | [P-5.9](../blueprint/src/chapter/permsum.tex#L80) | inductive estimate | [Anderson4D.InductiveEstimate](../Anderson4D/PermSum/Statements.lean#L218), [Anderson4D.inductive_estimate](../Anderson4D/PermSum/Inductive.lean#L162) |
| (5.34)–(5.37) | [R-5.7pf](PAPER_MAP.md#node-r-5-7pf) | derivation of Proposition 5.7 | [Anderson4D.permSum_estimate](../Anderson4D/PermSum/Main.lean#L314) |
| (5.38)–(5.39), Proposition 5.10 | [P-5.10](../blueprint/src/chapter/permsum.tex#L65) | single-scale estimate | [Anderson4D.SingleScaleEstimate](../Anderson4D/PermSum/Statements.lean#L256), [Anderson4D.singleScale_estimate](../Anderson4D/PermSum/SingleScale.lean#L542) |
| (5.40)–(5.48) | [R-5.9pf](PAPER_MAP.md#node-r-5-9pf) | collapse/induction closing Proposition 5.9 | [Anderson4D.inductive_estimate](../Anderson4D/PermSum/Inductive.lean#L162) |
| Definition 5.11; (5.49) | [D-5.11](../blueprint/src/chapter/combinatorics.tex#L46) | lacunary families | [Anderson4D.Lacunary](../Anderson4D/Combinatorics/BinomialBounds.lean#L82) |
| Lemma 5.12; (5.50)–(5.54) | [L-5.12](../blueprint/src/chapter/combinatorics.tex#L52) | binomial and multinomial estimates | [Anderson4D.choose_le_pow_mul_pow](../Anderson4D/Combinatorics/BinomialBounds.lean#L36), [Anderson4D.multinomial_le_pow_of_lacunary](../Anderson4D/Combinatorics/BinomialBounds.lean#L419) |
| Lemma 5.13; (5.55)–(5.57) | [L-5.13](../blueprint/src/chapter/combinatorics.tex#L67) | sequence-counting sums | [Anderson4D.sum_min_two_rpow_le](../Anderson4D/Combinatorics/SequenceCount.lean#L365), [Anderson4D.sum_min_ratio_pow_le](../Anderson4D/Combinatorics/SequenceCount.lean#L581) |
| Lemma 5.14; (5.58)–(5.67) | [L-5.14](../blueprint/src/chapter/permsum.tex#L39) | bilinear cluster bound | [Anderson4D.bilinear_cluster_bound](../Anderson4D/PermSum/LocalRefined.lean#L1349) |
| (5.68)–(5.98) | [R-5.10pf](PAPER_MAP.md#node-r-5-10pf) | proof of the single-scale estimate | [Anderson4D.singleScale_estimate](../Anderson4D/PermSum/SingleScale.lean#L542) |

<a id="infrastructure"></a>
## Infrastructure nodes used across sections

| Node | Lean entry points |
|---|---|
| [I-torus](../blueprint/src/chapter/continuum.tex#L14) | [Anderson4D.torusFourierBasis](../Anderson4D/Continuum/TorusFourier.lean#L381), [Anderson4D.paperKernelCoeff_eq_volume_sq_smul_normalized](../Anderson4D/Continuum/TorusFourier.lean#L631) |
| [I-noise](../blueprint/src/chapter/probability.tex#L6) | [Anderson4D.NoiseModel](../Anderson4D/Probability/Noise.lean#L35), [Anderson4D.NoiseModel.xiEps](../Anderson4D/Probability/Noise.lean#L68) |
| [I-isserlis](../blueprint/src/chapter/probability.tex#L26) | [Anderson4D.NoiseModel.integral_coordinateProduct_eq_wickPairingSum](../Anderson4D/Probability/NoiseIsserlis.lean#L300) |
| [I-chaos](../blueprint/src/chapter/probability.tex#L40) | [Anderson4D.partialPairingChaosWeight_eq_pairProduct_mul_wickPolynomial](../Anderson4D/Probability/ChaosDecomposition.lean#L55) |
| [I-singconv](../blueprint/src/chapter/continuum.tex#L46) | [Anderson4D.integrable_invSqKer](../Anderson4D/Continuum/SingularConv.lean#L324), [Anderson4D.binary_conv_invSqKer_le](../Anderson4D/Continuum/SingularConv.lean#L1192), [Anderson4D.triple_conv_invSqKer_le](../Anderson4D/Continuum/SingularConv.lean#L1679) |
| [I-cayley](../blueprint/src/chapter/hepp.tex#L66) | [Anderson4D.parentCode_one_add_bound_real](../Anderson4D/ForMathlib/WeightedCayley.lean#L115), [Anderson4D.weightedCayley_le_of_parent_injection](../Anderson4D/ForMathlib/WeightedCayley.lean#L141) |

<a id="reverse-lookup"></a>
## Lean → paper reverse lookup

For a declaration not listed above:

1. open the generated [PAPER_INDEX.md](PAPER_INDEX.md) and search its file
   name; a `Paper:` tag gives the coarse node assignment;
2. follow that node to [PAPER_MAP.md](PAPER_MAP.md) for its paper dependency
   role;
3. use this file for the exact public endpoint.

Regenerate the coarse inventory with `python3 scripts/paper_index.py`; validate
this document's paths, anchors, line fragments, and displayed Lean declaration
names with `python3 scripts/check_doc_links.py`.
