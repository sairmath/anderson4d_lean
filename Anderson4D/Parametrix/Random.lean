import Anderson4D.DetParametrix.Core.Kernels
import Anderson4D.Probability.Noise

/-!
# Random parametrix layer (blueprint nodes D-Im / D-para, coefficient route)

The random renormalized kernels `RI_{m,κ}` of Deng–Shen (arXiv:2607.10105)
§3.2: the deterministic closed-form integrand `detIntegrand` multiplied by
the Wick (chaos-projected) product of the noise at the single indices, then
integrated; the order-`m` parametrix piece `P_m` (paper (3.15)) and its
Fourier-mode coefficients (paper (3.23)); and the coefficient-level Neumann
route to `H_ε = λ_ε⁻¹(G_ε − G)` (DESIGN §5.2 refinement).

## Junk-totalization (DESIGN §5.7)

All `tsum`/Bochner integrals below default to `0` off summability /
integrability; downstream estimates carry the hypotheses excluding the junk
branches.  In particular, the `tsum` in `modeHcoeff` itself has junk value
`0` off the good event.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- **Wick factor at fixed points** (node D-Im).  For a pairing `κ` of the
`m` internal indices and an assembled tuple `xt = (x, v, y)`, the value of
the Wick product `:∏_{i ∈ S} ξ_ε(x_{i+1}):` over the singles `S` of `κ`,
written as the explicit combinatorial chaos projection (Hermite/Wick
expansion): the sum over sub-pairings `κ'` of `S` of
`(-1)^{#pairs κ'} · ∏_{pairs} η_ε(difference) · ∏_{new singles} ξ_ε`.

The projection `Proj_{|S|}` is defined by this combinatorial formula, with no
Hilbert-space machinery; `ChaosDecomposition` proves its relation to the
`L²(Ω)` chaos projection. -/
def wickAt (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4) (ω : M.Ω) : ℝ :=
  ∑ κ' : PartialPairing {i // i ∈ κ.singles},
    (-1 : ℝ) ^ κ'.pairs.card *
      (∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
        ρ.etaEpsT4 ε (xt (varIdx i.val) - xt (varIdx (κ' i).val))) *
      ∏ i ∈ κ'.singles, M.xiEps ρ ε ω (xt (varIdx i.val))

/-- **Random renormalized integrand** (node D-Im): the deterministic closed
form (3.6) times the Wick factor of the singles. -/
def randIntegrand (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4) (ω : M.Ω) : ℝ :=
  detIntegrand ρ ε m κ xt * wickAt M ρ ε κ xt ω

/-- **The random renormalized kernel** `RI_{m,κ}(x,y)` (paper Def 3.1 /
(3.6) with Wick factor): all `m` internal variables integrated against
`paperMeasure^{⊗m}`, with the coupling prefactor `λ_ε^m`.  Junk-totalized
Bochner integral. -/
def randRI (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (κ : PartialPairing (Fin m)) (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε ^ m *
    ∫ v : Fin m → T4, randIntegrand M ρ ε κ (assemble x y v) ω
      ∂(Measure.pi fun _ => paperMeasure)

/-- **The order-`m` parametrix piece** `P_m(x,y)` (paper (3.15)): the sum
of `RI_{m,κ}` over all partial pairings `κ` of the `m` internal indices.
(The full parametrix `∑_{m ≤ A} P_m` is not needed for the formal
statements.) -/
def parametrixP (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ κ : PartialPairing (Fin m), randRI M ρ lam ε m κ x y ω

/-- **Fourier-mode coefficients of `P_m`** (paper (3.23)): the pairing of
`P_m` with the characters `e_α ⊗ e_β` in both external variables, against
`paperMeasure` in each.  Junk-totalized iterated Bochner integrals. -/
def pmCoeff (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (ω : M.Ω) : ℂ :=
  ∫ x, ∫ y, charT4 α x * charT4 β y * (parametrixP M ρ lam ε m x y ω : ℂ)
    ∂paperMeasure ∂paperMeasure

/-- The renormalized multiplication function `λ_ε ξ_ε − C_ε` (the potential
entering `H_ε = G(λ_ε ξ_ε − C_ε)G + …`, paper (3.1)–(3.11)). -/
def multFun (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (z : T4)
    (ω : M.Ω) : ℝ :=
  lamEps lam ε * M.xiEps ρ ε ω z - renormCEps ρ lam ε

/-- **Neumann-series mode coefficient** (the coefficient-level definition
from DESIGN §5.2). Its equivalence with the operator route is proved in
`FredholmCoefficientBridge`. The kernel of the `n`-th
Neumann term is a chain of `n + 1` Green factors through `n`
multiplication points carrying `multFun`; it is paired with the characters
`e_α ⊗ e_β`.  At `n = 0` there are no multiplication factors and this is
the `Ĝ`-pairing.  Junk-totalized iterated Bochner integrals. -/
def neumannCoeff (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (n : ℕ)
    (α β : Z4) (ω : M.Ω) : ℂ :=
  ∫ x, ∫ y, ∫ v : Fin n → T4,
    charT4 α x * charT4 β y *
      (((∏ e : Fin (n + 1),
          greenFn ((assemble x y v) e.castSucc - (assemble x y v) e.succ)) *
        ∏ i, multFun M ρ lam ε (v i) ω : ℝ) : ℂ)
    ∂(Measure.pi fun _ => paperMeasure) ∂paperMeasure ∂paperMeasure

open Classical in
/-- **Mode coefficient of `H_ε = λ_ε⁻¹(G_ε − G)`** (coefficient route):
the `n ≥ 1` tail of the Neumann series of `G_ε`, divided by `λ_ε` — the
`n = 0` term *is* `Ĝ`, hence subtracted.  The standard totalized `tsum`
has junk value `0` when the tail is not summable; the good-event estimates
exclude that branch. -/
def modeHcoeff (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (α β : Z4)
    (ω : M.Ω) : ℂ :=
  (lamEps lam ε)⁻¹ •
    ∑' n : ℕ, neumannCoeff M ρ lam ε (n + 1) α β ω

end

end Anderson4D
