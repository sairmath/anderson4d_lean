# DESIGN — architecture and design decisions

This document records the mathematical scope and architecture implemented by
the Lean source and blueprint.

Companion documents: [PAPER_MAP.md](PAPER_MAP.md) (stable node IDs and
paper-level dependencies), [PAPER_TO_LEAN.md](PAPER_TO_LEAN.md) (exact public
declaration links), [PAPER_INDEX.md](PAPER_INDEX.md) (generated coarse module
inventory), and the [blueprint source](../blueprint/src/content.tex)
(mathematical statements and DAG).

Paper references ("§", "Prop", "(x.y)") are to arXiv:2607.10105v1.

---

## 1. Scope and goal

**Goal.** Formalize Theorem 1.1 of Deng–Shen conditionally on the statement of
Proposition 3.6, together with unconditional formalizations of everything the
paper proves: the renormalized parametrix construction (§3.1–3.3), the main
estimates Prop 3.5 (§4) and Prop 4.1 (§5), and all supporting theory.

**In scope, unconditional:** Definitions 2.1–2.3, Wick/chaos identities
(2.3)–(2.4), Definition 3.1 and Prop 3.2, renormalization constants §3.2 and
Prop 3.3, parametrix and Prop 3.4, error identities (3.20)–(3.21), Prop 3.5,
the proof of Theorem 1.1 from Props 3.5 + 3.6 (§3.4), Prop 4.1 and its proof
(§5 in its entirety), all auxiliary lemmas (5.2, 5.5, 5.12–5.14, Props 5.6,
5.7, 5.9, 5.10), and all infrastructure listed in PAPER_MAP §I.

**External input (conditional):** the statement of Prop 3.6 ((3.26)–(3.28)),
whose proof the paper delegates to Gabriel–Rosati (arXiv:2602.22509,
Props 3.9 and 3.12). See §3 below for the mechanism.

**Outside the formalized scope:** the proof of Prop 3.6, the parabolic
Anderson model (Remark 1.2), nonlinear models, and a distribution-valued
strengthening of the finite-mode theorem.

## 2. The formal main statement

### 2.1 Design principle

The paper proves its random-field statement by tightness followed by
finite-family Fourier-mode convergence ((3.34)).  Our formal target is the
finite-family statement itself, so the tightness/Prokhorov detour is not a
dependency of the target.  The primary Lean form is the Cramér--Wold
characteristic-function identity for every finite complex linear combination;
this is exactly the finite-mode content used in the paper and is readable
directly in Lean.

### 2.2 Objects entering the statement

All of the following are *defined* (not assumed) in Lean; details in §5:

- the probability space: a `NoiseModel` satisfying the Fourier-coefficient
  covariance and finite-dimensional Gaussian specifications (§5.1); the
  main assembly is law-invariant and works for every such model;
- the mollifier class: `ρ : SmoothCutoff` — smooth, compactly supported in the
  fundamental domain, in the symmetry class $\mathcal{E}$ (Def 2.1), even,
  $\int \rho = 1$; the theorem quantifies over all such `ρ`;
- the mollified noise $\xi_\varepsilon$ as a random smooth function (a.s.
  convergent random Fourier series);
- $\mathcal{C}_\varepsilon$ by the explicit formula (3.11) — note the theorem
  then *has no existential quantifier over renormalization constants*: we
  prove convergence for the explicit choice, which is stronger and cleaner;
- $G_\varepsilon(x,y)$ via the parametrix-based inverse where it exists, junk
  value `0` otherwise (§5.7);
- $\mathcal{H}_\varepsilon = \lambda_\varepsilon^{-1}(G_\varepsilon - G)$ and its
  Fourier coefficients $\widehat{\mathcal{H}_\varepsilon}(\alpha,\beta)$
  ((3.23) normalization);
- the limit quadratic form `limitVar` (node D-limit), computed from the
  four-point kernel $H$ ((3.25)) and the factor
  $\frac{2\pi^2}{2\pi^2-\lambda^2}$.  It is proved nonnegative from the
  Gram representation of $H$.  The primary target is
  `exp (-limitVar / 2)` for every real Cramér--Wold test.  A centered Gaussian
  measure on the **realification** $\mathbb{R}^{2s}$ of $\mathbb{C}^s$ is a
  corollary interface: conjugate modes $(-\alpha,-\beta)$ determine both
  covariance and pseudo-covariance.  The subcritical condition
  $\lambda^2<2\pi^2$ is enforced by the selected coupling threshold.

### 2.3 Lean statement

`MainStatement M ρ` says that there is a positive `lam₀` such that, for
every `lam ∈ (0,lam₀)`, every finite mode family, and every complex
coefficient family `c`, the expectation

```lean
∫ ω, Complex.exp (Complex.I *
  (fredholmFiniteModeReal M ρ lam ε s modes c ω : ℂ))
```

tends along `𝓝[Set.Ioo 0 1] 0` to the real Gaussian characteristic
function `Real.exp (-(limitVar lam modes c) / 2)`, coerced to `ℂ`.
`MainConditional M ρ` is exactly
`Prop36Family M ρ → MainStatement M ρ`.  A
`ProbabilityMeasure.map`/realified convergence-in-distribution theorem is
derived from this primary Cramér--Wold form rather than replacing it.

Statement-level details:
- **quantifier order**: $\rho$ is fixed *before* $\lambda_0$ — the paper
  fixes the cutoff first, and its constants (hence the admissible
  $\lambda_0$) depend on $\rho$ through $\eta = \rho * \rho$; a
  cutoff-uniform $\lambda_0$ is not claimed by the paper and is not
  claimed by us;
- the expectation is over the explicit probability measure carried by
  `NoiseModel`; all mode tests have explicit measurability proofs, and the
  limit is along the single filter
  `𝓝[Set.Ioo 0 1] 0` (real $\varepsilon \to 0^+$, matching the paper; no
  dyadic subsequence);
- the mode functionals are bona fide random variables: measurability of
  $\omega \mapsto \widehat{\mathcal{H}_\varepsilon}(\alpha,\beta)$ is part of
  the definition layer.  The production representative applies the Borel
  totalized inverse `Ring.inverse` to the measurable bounded operator
  $1-K_\varepsilon$ and is zero off its open unit locus.  At every positive
  scale it agrees almost surely with the samplewise Fredholm inverse.  The
  separately retained `modeHcoeff` is the perturbative Neumann tail and is
  identified with the resolvent only under an explicit hypothesis that the
  Neumann expansion converges (§5.2, §5.7);
- the finite-mode target needs no tightness or Prokhorov theorem.  Those
  would be required only for a distribution-valued strengthening, which is
  outside the formalized scope.

## 3. External input policy

- `Anderson4D/Main/External.lean` states Prop 3.6 exactly ((3.26)–(3.28)).
  `Prop36WithConstant` is the Prop-valued formula; `Prop36` is a
  Type-valued witness structure carrying the one positive geometric
  constant together with a proof of that formula.  `Prop36Family` selects
  one such constant before quantifying the coupling.  This prevents an
  arbitrary per-coupling `Classical.choose` from destroying the uniform
  small-coupling threshold.  None of these is an `axiom`.
- The main theorem takes `hP36 : Prop36Family M ρ` as an explicit hypothesis
  (`MainConditional`). The public endpoints are `main_conditional` and its
  finite-vector law corollary `main_conditional_law`; there is no
  unconditional `main` because the proof of Proposition 3.6 is not part of
  this formalization.
- **No `axiom` declarations anywhere in the project, ever.** CI greps for
  `axiom` (and for `native_decide`) in `Anderson4D/`; `sorry` (= `sorryAx`)
  is governed by §6.2 and must not appear in the `#print axioms` output of
  any theorem claimed complete.
- Rationale: hypotheses keep the logical accounting visible in the statement
  itself; `#print axioms main_conditional` and
  `#print axioms main_conditional_law` report only Lean's standard axioms.

## 4. Layered architecture and module map

Seven layers; lower layers never import higher ones. Directories match
layers one-to-one.

| Layer | Directory | Content | Paper | Imports |
|---|---|---|---|---|
| L0 combinatorics | `Anderson4D/Combinatorics/` | pairings, fully paired subintervals, primitive pairings, Dyck-word bookkeeping, tree counting, elementary counting lemmas, lacunarity | Defs 2.2–2.3, 5.11, Lemmas 5.2, 5.12, 5.13 | mathlib only |
| L1 discrete core | `Anderson4D/HeppTree/`, `Anderson4D/PermSum/` | Hepp trees (incl. order-forgetting automorphisms), admissible embeddings into $\mathbb{Z}^4_M$, volume estimate, permutation-sum estimates | Defs 5.1–5.4, 5.8, Lemmas 5.5, 5.14, Props 5.6, 5.7, 5.9, 5.10 | L0 |
| L2 continuum estimates | `Anderson4D/Continuum/` | **deterministic Fourier core on the product torus** (characters, coefficients, Plancherel, multipliers — I-torus, needed here, not in L4), class $\mathcal{E}$, torus Green's function + (4.1), singular convolutions, discretization §5.1, Prop 4.1 | Def 2.1, (3.23), (4.1)–(4.4), §5.1 | L0–L1 |
| L3 deterministic parametrix | `Anderson4D/DetParametrix/` | deterministic profile kernels of the chaos expansion, renormalization $\mathcal{RI}$ (Def 3.1), $\mathcal{C}_{2q}$, (3.22), deterministic second-moment sum estimates (all of §4) | §3.1–3.2 (deterministic content), §4 | L0, L2 |
| L4 probability primitives | `Anderson4D/Probability/` | white noise, Isserlis/Wick, chaos projections, (2.3)–(2.4) (deterministic Fourier lives in L2) | §2.2 | mathlib probability, L2 |
| L5 random parametrix | `Anderson4D/Parametrix/` | random kernels $\mathcal{I}_{m,\kappa}$, parametrix, Prop 3.4, (3.20)–(3.21), (3.24) via Wick reduction, $L^2$ bounds and the inverse on the good event | §3.1–3.3, §3.4 Step 1 | L3, L4 |
| L6 assembly | `Anderson4D/Main/` | `External.lean` (Prop 3.6), limit law (D-limit), mode reduction (P-red), Theorem 1.1 | §3.4 Steps 2–3, Thm 1.1 | all |

The L3/L5 split keeps the dependency graph acyclic: each §3 object has a
deterministic profile kernel (L3) and a chaos-integrated random kernel (L5),
connected by the Wick reduction lemma. Proposition 3.5 correspondingly
splits into P-3.5a/(3.22) and P-3.5b-det at L3, then P-3.5b/(3.24) at L5.

Plus: `Anderson4D/ForMathlib/` contains mathlib-general supporting lemmas.

The full node-level map with public Lean names is PAPER_MAP.md.

## 5. Mathematical design decisions

### 5.1 White noise via random Fourier series (no distribution theory)

White noise on $\mathbb{T}^4$ is *defined* through its Fourier coefficients.
**Specification:** the probability space
carries independent standard *real* Gaussians, two per $\{\pm k\}$-orbit
($k \ne 0$) and one for the zero mode; the complex coefficients are
assembled as $g_k := (a_k + i\,b_k)/\sqrt2$ for $k$ in a fixed fundamental
domain $F$ of $k \mapsto -k$, $g_{-k} := \overline{g_k}$, and
$g_0 := a_0 \in \mathbb{R}$. (The family $(g_k)_{k\in\mathbb{Z}^4}$ is therefore
*not* i.i.d. — the orbit pairs are deterministically coupled; only the
per-orbit real generators are i.i.d.) The defining covariance identities,
fixed together with the normalization ledger, are

$$
\mathbb{E}[g_k\,g_l] = \mathbf{1}_{k = -l},\qquad
\mathbb{E}[g_k\,\overline{g_l}] = \mathbf{1}_{k = l}.
$$

The *only* object ever used analytically is the mollified noise

$$
\xi_\varepsilon(x) = (2\pi)^{-2}
\sum_{k \in \mathbb{Z}^4} \widehat{\rho}(\varepsilon k)\,
g_k\, e^{i k \cdot x} \quad(\text{a.s. absolutely convergent, a.s. } C^\infty),
$$

where $(2\pi)^{-2}$ is the half-density converting the probability-Haar
orthonormal character basis used by mathlib into Lebesgue-normalized white
noise on the paper's torus of volume $(2\pi)^4$.  Equivalently, the
Lebesgue-orthonormal basis is $(2\pi)^{-2}e_k$.  The variance-one
specification of the $g_k$ above is unchanged.

which is a random smooth function. Consequences:

- distribution-valued white noise never appears; no Minlos/nuclear-space
  machinery is needed;
- covariance identity
  $\mathbb{E}\,\xi_\varepsilon(x)\xi_\varepsilon(y)=\eta_\varepsilon(x-y)$,
  where $\eta=\rho*\rho$, is a Fourier computation;
- $\|\xi_\varepsilon\|_{L^\infty}\lesssim\varepsilon^{-2-}$-type
  high-probability bounds (used in §3.4 Step 1 via
  $\mathbb{E}\|\xi_\varepsilon\|_{L^2\to L^2}^2\lesssim\varepsilon^{-5}$)
  are proved from coefficient moments.

Fidelity note: the paper's $\xi$ is the standard white noise and
$\xi_\varepsilon = \rho_\varepsilon * \xi$; our construction produces exactly the
law of $(\xi_\varepsilon)_\varepsilon$ (jointly in $\varepsilon$, on one probability
space), which is all that Theorem 1.1 (a convergence-in-law statement)
refers to. This equivalence is documented in the blueprint's preliminaries
chapter.

**Cutoff and scaling live on $\mathbb{R}^4$.** The dilation
$x \mapsto x/\varepsilon$ is not intrinsic on the quotient torus, and
"compactly supported" is not a property of an abstract torus function.
Hence: $\rho$ is a function on $\mathbb{R}^4$ — smooth, $\ge 0$, compactly
supported **with an explicit support-radius field `R`** (support ⊆ ball
$R$), in the $\mathbb{R}^4$-version of the class $\mathcal{E}$, with
$\int_{\mathbb{R}^4}\rho = 1$ (this is the `SmoothCutoff` structure). We do
*not* normalize to $R = 1$: rescaling reparameterizes the scale as
$\varepsilon\mapsto R\varepsilon$ and perturbs $\lambda_\varepsilon$ and
$\mathcal{C}_\varepsilon$, so it
is not WLOG at fixed $\varepsilon$; instead every constant
may depend on $\rho$ *including* $R$;
$\rho_\varepsilon := \varepsilon^{-4}\rho(\cdot/\varepsilon)$ is defined on
$\mathbb{R}^4$; torus objects are obtained by periodization
$\Pi_{\mathrm{per}}f := \sum_{k\in(2\pi\mathbb{Z})^4} f(\cdot + k)$ (locally a
finite sum). By Poisson summation, periodized mollification agrees with the
Fourier-multiplier description
$\widehat{\xi_\varepsilon}(k)=\widehat{\rho}(\varepsilon k)\,g_k$
($\widehat\rho$ = $\mathbb{R}^4$ Fourier
transform); the two are proved equal once in the preliminaries and the
multiplier form is used everywhere after.

**Normalization ledger.** mathlib's `AddCircle` Fourier API is normalized
against probability Haar measure, while the paper uses Lebesgue measure on
$[-\pi,\pi]^4$ (mass $(2\pi)^4$) and the unnormalized coefficients (3.23);
constants like the $2\pi^2$ in (1.3) are convention-dependent. The
blueprint preliminaries fix, once and for all: the measure on
$\mathbb{T}^4$, the characters $e^{ik\cdot x}$, the coefficient convention
(3.23), the $\mathbb{R}^4$ Fourier convention for $\widehat\rho$, and the
variance convention for $(g_k)$, and the Fourier half-density
$(2\pi)^{-2}$ in $\xi_\varepsilon$ — plus a translation dictionary to
mathlib's normalized API. All $2\pi$-factors are centralized in this
dictionary and never appear ad hoc. The ledger is a foundational interface:
changing it would invalidate every constant downstream.

**Almost-sure regularity across $\varepsilon$.** On the single a.s. event
where $(g_k)$ grows at most polynomially (Borel–Cantelli), $\xi_\varepsilon$
is $C^\infty$ simultaneously for *every* $\varepsilon \in (0,1)$; no
per-$\varepsilon$ null-set bookkeeping is needed anywhere.

### 5.2 Kernels before operators

Following the paper's own convention (2.1), all objects $G$, $\mathcal{I}_{m,\kappa}$,
$\mathcal{RI}_{m,\kappa}$, $\mathcal{P}_m$, $\mathcal{R}_\varepsilon$ are treated as
**kernels**: measurable functions on $\mathbb{T}^4 \times \mathbb{T}^4$ (physical
side) or coefficient families on $\mathbb{Z}^4 \times \mathbb{Z}^4$ (Fourier side,
(3.23)), with explicit integrability lemmas. Composition is the integral
$\smash{(K_1 \circ K_2)(x,y) = \int K_1(x,z)K_2(z,y)\,dz}$ with Fubini
side-goals discharged by the estimates themselves.

**Operator realization (no unbounded operators).** $\mathcal{L}_\varepsilon$,
$1-\Delta$, and $\boldsymbol{\delta}_y$ are never formalized as operators:
$1-\Delta$ is unbounded on $L^2$, multiplication has no $L^2$ kernel, and
$\delta_y \notin L^2$. Instead:

- claims of the form "$(1-\Delta)K$" for explicit kernels $K$ are stated as
  Fourier-multiplier identities on the coefficients of $K$ (equivalently,
  $K = G \circ F$ and the claim is about $F$);
- the bounded object is $K_\varepsilon := G \circ M_\varepsilon \in \mathcal{B}(L^2)$,
  where $M_\varepsilon$ is multiplication by
  $\lambda_\varepsilon\xi_\varepsilon - \mathcal{C}_\varepsilon$ (a.s. $L^\infty$);
- *invertibility of $\mathcal{L}_\varepsilon$* is **defined** as invertibility
  of $1 - K_\varepsilon$ in $\mathcal{B}(L^2)$;
- **the primary random objects are the Fourier matrix coefficients**,
  with the sign convention aligned to (3.23): since
  $\widehat K(\alpha,\beta)=\iint e^{i(\alpha x+\beta y)}K(x,y)=\langle e_{-\alpha},K e_\beta\rangle$
  for an inner product
  conjugate-linear in the first slot,
  `modeCoeffH α β ω :=`
  $\big\langle e_{-\alpha},((1-K_\varepsilon)^{-1}\circ G-G)e_\beta\big\rangle$
  **on the
  invertibility event, and `0` (junk) off it** — bounded operators applied
  to smooth characters, so well-defined with no kernel-as-function needed
  in the main statement.  Its production random-variable representative
  uses the measurable realization of $K_\varepsilon$ and the Borel
  totalized `Ring.inverse`; it agrees almost surely with this samplewise
  object at positive scale. A **rank-one roundtrip
  test** (compute $\widehat K$ of an explicit rank-one kernel both ways)
  freezes the sign/normalization. Note $G$ is *not*
  Hilbert–Schmidt in $d = 4$ ($\sum_k\langle k\rangle^{-4} = \infty$), so
  "$(1-K_\varepsilon)^{-1}\circ G$ has a kernel" is not automatic and is not
  claimed;
- kernel level, where needed: **on the invertibility event** the
  difference is genuinely Hilbert–Schmidt —
  $(1-K_\varepsilon)^{-1}\circ G-G=(1-K_\varepsilon)^{-1}\circ G\circ M_\varepsilon\circ G$
  (this identity and
  the HS claim are *conditioned on* $1-K_\varepsilon$ being invertible; off
  the event $G_\varepsilon := 0$ and the difference $-G$ is not HS, which is
  why the junk branch lives in `modeCoeffH`), and
  $G\circ M_\varepsilon\circ M := G\circ M_\varepsilon\circ G$ has
  $\|\cdot\|_{HS}^2\lesssim\sum_\gamma\lvert\widehat m(\gamma)\rvert^2\langle\gamma\rangle^{-4}(1+\log\langle\gamma\rangle)<\infty$
  (the $1+{}$ keeps the $\gamma = 0$ contribution); the resulting
  HS-difference lemma is explicitly conditioned on invertibility;
- this matches the paper, whose §3.4 Step 1 itself constructs
  $\mathcal{L}_\varepsilon^{-1} = \mathcal{P}_\varepsilon(1+\mathcal{R}_\varepsilon)^{-1}$
  in $\mathcal{B}(L^2, L^2)$; a blueprint remark records the equivalence of
  our definition with the paper's reading of (1.2) (both default to $0$
  when no inverse exists);
- mathlib provides operator norms, openness of the unit locus, continuity
  of the inverse there, and the compact-operator Fredholm alternative.
  The paper's one-sided residual therefore yields invertibility without a
  false $\|K_\varepsilon\|<1$ premise.  The bound (3.30) is stated directly
  as a Plancherel double sum over Fourier coefficients (no named
  Hilbert–Schmidt API is assumed to exist).

The kernel→operator bridge lemmas live in `Parametrix/L2Bounds.lean`.

### 5.3 Value types: where ℝ, ℂ, ℝ≥0∞ each live

- **Identities** (Def 3.1, Props 3.2/3.3/3.4, (3.20)–(3.21)): signed — real
  (physical kernels) or complex (Fourier side). Subtraction and cancellation
  are of the essence; these cannot live in `ℝ≥0∞`.
- **Estimates** (all of §4, §5.1, all integral bounds): stated in `ℝ≥0∞`
  (`MeasureTheory.lintegral` etc.); explicit
  `ENNReal.ofReal`/`toReal` bridges at layer boundaries only.
- **Discrete core sums** (§5.2–5.4): finite `Finset` sums — stated in `ℝ≥0`
  (nonnegative terms, no convergence issues; cleaner than `ℝ≥0∞` since no
  `⊤` can occur, and multiplication is well-behaved). Bridge lemmas to
  `ℝ≥0∞` where §5.1 consumes them.
- **Lattice norm convention:** the finite geometric core uses the coordinate
  sup norm `znorm` on `ℤ⁴`, because dyadic boxes and exact cardinality
  estimates are coordinatewise.  Whenever the paper's `|·|` is read as the
  Euclidean norm, the production boundary lemmas
  `znorm z ≤ ‖z‖₂ ≤ 2 * znorm z` supplies the translation; in particular the
  corresponding fourth-order bracket weights differ by at most `16`.
  Proposition 5.6 absorbs this fixed factor into its universal `C^r`.
  Continuum statements use Euclidean norm and must cross this explicit
  bridge rather than silently changing norms.  The bridge lives in
  `HeppTree/LatticeNormBridge.lean`.
- Probability: laws as `Measure`/`ProbabilityMeasure`, expectations via
  Bochner integral for signed/complex quantities, `lintegral` for bounds.

### 5.4 Explicit constants

- No Landau/Vinogradov notation anywhere in Lean statements.
- **Hybrid constant policy**: a constant referenced by more than one node
  (e.g. `C_hepp` of Lemma 5.2, `C_vol` of Prop 5.6, `C_perm` of Prop 5.7,
  `C₀` with hypothesis `1000 < C₀` and `D := exp (C₀^10)` of Prop 5.9) is a
  **named `def`** — or a field of a `Params` structure recording its
  $\rho$-dependence; a paper "line constant" used in a single lemma is
  stated in `∃ C, …` form. Statements never contain anonymous numeric
  literals standing for "some large constant". Cross-node statements carry
  exact constant expressions ("$(C\lambda)^{2n}$" becomes
  `(C_prim * lam)^(2*n)` with `C_prim` named).
- Constants are **parameters, not magic numbers**, wherever the paper only
  uses "$C$ large enough": the final theorem instantiates them. This keeps
  each bookkeeping constant local and prevents cascading edits.
- The dependency of constants on $\rho$ (the cutoff) is threaded explicitly.

### 5.5 Discrete core representations

- Lattice: `ℤ⁴` is `Fin 4 → ℤ` (abbreviation `Z4`); the truncated lattice
  $\mathbb{Z}^4_M$ is a `Finset` parameterized by dyadic `M`. Dyadic scales are
  `ℕ` exponents (`N = 2^j`), avoiding real logarithms in the combinatorial
  layer entirely.
- **Hepp trees** (Def 5.1): plane carrier type
  `inductive HeppTree | leaf | node : List HeppTree → HeppTree`
  (leaves identified by their position paths), with validity predicates
  (branching nodes have ≥ 2 children), markings `N` (strictly increasing
  toward the root, dyadic values) and multiplicities `m` (≥ 2) as separate
  data, since the §5.4 induction mutates them independently.
  **Automorphisms:** `Aut(T)` is
  the **parent-map-commuting subgroup of `Equiv.Perm` on the finite
  vertex-position set** (`IsAut t e := ∀ v, e (parent v) = parent (e v)`)
  — *not* a recursive iso family: the subgroup form gets `Group`,
  `Fintype`, and decidability for free, avoids `HEq` entirely (the
  recursive `TreeIso` family elaborates but its group laws need
  transport), and the parent-map characterization already forgets plane
  order. Markings are functions on vertex positions; `Aut(T,N)` is the
  `MulAction` stabilizer, and orbit-stabilizer is mathlib's
  (`card_orbit_mul_card_autMarked`; finite sanity checks agree with
  `autCard`). **Kernel-computability rule:**
  tree helpers that `decide`/`rfl` must evaluate (vertex enumeration
  above all) are written by structural/mutual recursion, never
  well-founded recursion. An `Fintype.card (Aut t) = autCard t`
  cross-check lemma is part of the checked interface. Lemma 5.2 bounds the *plane*
  count, which dominates the unordered one.
- **Pure word model** for permutation sums with multiplicities ((5.15),
  (5.33)): all §5.4 sums are *stated and proved* as sums over **word maps**
  `w : Fin m → Leaf` with prescribed fiber sizes
  (`∀ l, (w⁻¹ l).card = m l`) — never over labeled copies, never over
  quotient types. **Factorial specification:**
  the ledger is *definitional* — `paperSum mult F :=
  (∏ l, (mult l)!) * wordSum mult F`. The statements of P-5.7,
  P-5.9 and P-5.10 put **`paperSum` on the left-hand side with the
  paper's right-hand sides verbatim** (positive exponents
  $(m_\mathfrak{l}!)^{1/2}$, $(m_\mathfrak{l}!)^{3/4}$ kept as printed).
  In R-decomp's (5.10), matching the paper, `paperSum` is instead the
  labeled-permutation sum on the **right**:
  `pairedWordSum ≤ (∏ l, (mult l / 2)! / (mult l)!) * paperSum mult F`;
  internal proofs manipulate `wordSum` and convert only at statement
  boundaries. This keeps statement fidelity inspectable line-by-line
  against the paper while the raw-word alternative (shifting exponents to
  $-1/2$, $-1/4$) is rejected. In this model
  the §5.4.1 collapse correspondence
  $\pi \leftrightarrow (\pi_1, O, \pi_2)$ **is an honest word-level
  `Equiv`** (words already treat copies as identical; reconstruction
  inserts the $\pi_1$-blocks into the occurrences of the compound letter in
  order), and the $((s+1)!)^{-1}$ of (5.45)(i) arises purely from the
  ledger when the induction hypothesis (calibrated against labeled sums)
  is invoked — *not* from fiber counting. "No adjacent equal copies" and
  primitivity are predicates on words. This representation and ledger are
  the fixed public interface.
- Counting statements (Lemma 5.2, (5.9), (5.10), Prop 5.6) are stated as
  `Finset.card` inequalities over explicit finsets. Lemma 5.2 is proved by
  an explicit injection of plane trees (branching ≥ 2, hence ≤ 2r−1
  vertices for r leaves) into Dyck words of bounded length, giving
  $A_r \le C^r$ with explicit $C$ — naive induction on the paper's
  recurrence does **not** close (composition counts are exponential), and
  the generating-function analyticity argument is not formalized; the
  injection is the documented proof substitution.

### 5.6 The parameter $\varepsilon$ and limits

- $\varepsilon$ ranges over $(0,1) \subset \mathbb{R}$; $A := \lfloor|\log\varepsilon|\rfloor$
  (natural number) as in the paper; all "$n \lesssim |\log\varepsilon|$"
  hypotheses become explicit `n ≤ K * A`-form inequalities with named `K`.
- Limits are along the filter `𝓝[>] 0` restricted to $(0,1)$.
- The discrete layer never sees $\varepsilon$: it is parameterized by `M`
  (lattice size) and `n`, with hypotheses `n ≤ C * log₂ M`-style; §5.1's
  discretization lemma is the sole translation point.

### 5.7 Degenerate cases and junk values

- $G_\varepsilon := 0$ when $\mathcal{L}_\varepsilon$ is not invertible (paper
  convention after (1.2)); invertibility is *derived* on the good event via
  the compact Fredholm alternative applied to the paper's norm-small
  one-sided parametrix residual.  A Neumann series is used only for the
  residual inverse $(1+\mathcal R_\varepsilon)^{-1}$, where its norm
  hypothesis is actually available.
- All kernels are total functions; integrability is a separate hypothesis
  carried by the estimates (standard mathlib style, junk values elsewhere).
- Division by $|\log\varepsilon|$, $|z|^{-2}$ at $z=0$, etc.: totalized with
  junk values; estimates quantify away the degenerate points.

### 5.7bis Renormalization via closed formulas

The paper's Def. 3.1 defines $\mathcal{RI}_{m,\kappa}$ by a recursion that
interleaves integral operations with interval removal, and Props. 3.2/3.3
then derive closed formulas ((3.6), (3.12)). We formalize in the
**opposite direction**: a purely combinatorial **endpoint-extraction
recursion** on pairings (iterate the smallest-leftmost fully-paired
relative-interval selector on a shrinking `active : Finset (Fin m)` —
fuel recursion, no type-changing induction, no integrals) produces the
$(\ell_i, r_i)$ lists, and $\mathcal{RI}$, $\mathcal{J}_{2q,\sigma}$ are
**defined** by the closed formulas (3.6)/(3.12) with those endpoints.
The equivalence with the paper's recursive definition (= Props. 3.2/3.3
read backwards) is a single checked equivalence theorem. Nothing is lost —
the equivalence is proved, not assumed — and the definitional layer needs no
integral-manipulating recursion.

### 5.8 Green's function representation

$G$ is **not** definable as a pointwise Fourier `tsum`: the coefficients
$\langle k\rangle^{-2}$ are neither $\ell^1$ nor $\ell^2$ over $\mathbb{Z}^4$,
and $G \notin L^2(\mathbb{T}^4)$ ($|z|^{-2}$ fails square-integrability in
$d = 4$). The adopted definition is the **Bessel-potential /
heat-kernel time integral**

$$
G(z) := \int_0^\infty e^{-t}\,\Theta(t,z)\,\mathrm{d}t,\qquad
\Theta(t,z) := \sum_{k\in(2\pi\mathbb{Z})^4}(4\pi t)^{-2}
e^{-\lvert z+k\rvert^2/4t}.
$$

(periodized Gaussian; rapidly convergent for every $t > 0$, positive,
manifestly in $\mathcal{E}$). The bounds (4.1) follow from Gaussian
integrals; the near-diagonal comparison with $\frac{1}{4\pi^2|z|^2}$ from
the $\mathbb{R}^4$ Bessel potential plus a smooth periodization error; the
Fourier coefficients $\widehat{G}(k) = \langle k\rangle^{-2}$ are a *lemma*
(termwise integration), not the definition.

## 6. Engineering conventions

### 6.1 Style and naming

- mathlib style conventions throughout; `Mathlib.Tactic` is allowed. The
  repository has no separate Lake lint driver, so the published mechanical
  contract is `lake build` plus `scripts/release_gate.sh`.
- Root namespace `Anderson4D`. Paper-traceable names: every Lean declaration
  realizing a paper node carries a doc-string with the paper reference
  (`/-- Paper: Prop 5.6, (5.13). ... -/`), and the blueprint `\lean{}` link
  closes the loop. PAPER_MAP.md is the authoritative name table.
- One blueprint node = one Lean declaration (or one small cluster in one
  file section); no omnibus lemmas.

### 6.2 Proof-completeness policy

- Published Lean source contains no `sorry` or `admit`.
- Project-specific `axiom` declarations and `native_decide` are forbidden.
- `scripts/sorries.sh` and `scripts/release_gate.sh` enforce these rules; the
  release gate also audits the axiom dependencies of the public theorem spine.

### 6.3 Toolchain and dependency policy

- Lean and mathlib are pinned to **v4.32.1** by `lean-toolchain`,
  `lakefile.toml`, and `lake-manifest.json`.
- The proof library's only direct mathematical dependency is mathlib. The
  tooling additionally pins `checkdecls` to an exact revision. Anything
  needed from other mathematical Lean repositories is *not* imported —
  the (small) needed statements are developed in `ForMathlib/` instead.
  Rationale: we need very little (§5.1's design removes the heavy
  probability prerequisites), and dependency churn costs more than the
  handful of lemmas.

### 6.4 Blueprint and CI

- `leanblueprint`-standard layout (`blueprint/src/{content.tex, web.tex,
  print.tex, macros/, ...}`). Local checks are `leanblueprint web` and
  `lake exe checkdecls blueprint/lean_decls`; PDF generation is optional.
- Blueprint chapters mirror the layer structure (L0–L6), each theorem/def
  environment carrying `\label`, `\uses`, `\lean`, and `\leanok` when its
  Lean declaration exists. The Proposition 3.6 node is visibly titled and
  described as an **external input**; its `\leanok` marks the checked Lean
  hypothesis interface, not a formal proof of the cited Gabriel--Rosati
  result.
- `.github/workflows/` builds the Lean project and checks the paper and
  blueprint indexes. The optional Pages build combines leanblueprint HTML
  with doc-gen4 API output.
- Formal-statement fidelity is tracked through `PAPER_TO_LEAN.md` and the
  blueprint declarations.

## 7. Verification

`lake build` checks the complete umbrella import. The aggregate
`scripts/release_gate.sh` additionally checks tracked-module coverage, the
zero-`sorry` and banned-declaration policies, public theorem axioms, paper and
documentation indexes, and all declarations listed in
`blueprint/lean_decls`. When the optional blueprint toolchain is installed it
also renders the blueprint; the Pages build installs that toolchain and
enforces rendering.

When a literal transcription admits more than one local reading, record the
precise convention used by Lean in
[`docs/PAPER_NOTES.md`](PAPER_NOTES.md), together with the checked downstream
statement. The note records mathematical conventions only.

## 8. Formalized scope boundary

The finite-mode form of Theorem 1.1 and all dependencies listed in
`PAPER_MAP.md` are formalized. The Gabriel--Rosati proof of Proposition 3.6
is outside this repository; its statement remains the sole explicit premise
of the conditional theorem.
