import Anderson4D.Parametrix.RemainderAlgebra

/-!
# The left preconditioned parametrix remainder

This module instantiates the finite telescope of paper
(3.20)--(3.21) with the actual random kernels.  The only input is the
order-by-order preconditioned form of Proposition 3.4; all finite
reindexing and boundary cancellation is proved in
`RemainderAlgebra`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace PartialPairing

/-- The kernel of the order-`A` truncated parametrix
`P_ε = ∑_{m=0}^A P_m`. -/
def truncatedParametrixKernel
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  ∑ m ∈ Finset.range (A + 1),
    parametrixP M ρ lam ε m x y ω

/-- The free-Green-preconditioned left action `G L_ε P_ε`, expanded
into the parametrix, noise, and counterterm pieces. -/
def leftPreconditionedParametrixAction
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  (∑ m ∈ Finset.range (A + 1),
      parametrixP M ρ lam ε m x y ω) -
    (∑ m ∈ Finset.range (A + 1),
      leftParametrixNoiseSource
        M ρ lam ε m x y ω) +
    ∑ r ∈ Finset.range (A + 1),
      ∑ q ∈ Finset.Icc 1 A,
        caseThreeCountertermBlock
          M ρ lam ε q r x y ω

/-- The preconditioned left remainder from paper (3.21):
the terminal noise composition plus exactly the counterterms crossing
the truncation boundary. -/
def leftPreconditionedRemainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  -leftParametrixNoiseSource
      M ρ lam ε A x y ω +
    ∑ r ∈ Finset.range (A + 1),
      ∑ q ∈ (Finset.Icc 1 A).filter
        (fun q => A < r + 2 * q),
        caseThreeCountertermBlock
          M ρ lam ε q r x y ω

/-- Paper (3.20)--(3.21), after applying the free Green operator on
the left.  The hypothesis is precisely the preconditioned order-`m`
identity (3.16), with no estimate or extra identity bundled into it. -/
theorem leftPreconditionedParametrixAction_eq_green_add_remainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω)
    (horder :
      ∀ m ∈ Finset.Icc 1 A,
        leftParametrixNoiseSource
            M ρ lam ε (m - 1) x y ω =
          parametrixP M ρ lam ε m x y ω +
            ∑ q ∈ Finset.Icc 1 (m / 2),
              caseThreeCountertermBlock
                M ρ lam ε q (m - 2 * q)
                  x y ω) :
    leftPreconditionedParametrixAction
        M ρ lam ε A x y ω =
      greenFn (x - y) +
        leftPreconditionedRemainder
          M ρ lam ε A x y ω := by
  let P : ℕ → ℝ :=
    fun m => parametrixP M ρ lam ε m x y ω
  let N : ℕ → ℝ :=
    fun m =>
      leftParametrixNoiseSource
        M ρ lam ε m x y ω
  let C : ℕ → ℕ → ℝ :=
    fun q r =>
      caseThreeCountertermBlock
        M ρ lam ε q r x y ω
  have htelescope :=
    parametrixTelescopeIcc A P N C
      (fun m hm => by
        simpa only [P, N, C] using horder m hm)
  unfold leftPreconditionedParametrixAction
  unfold leftPreconditionedRemainder
  change
    (∑ m ∈ Finset.range (A + 1), P m) -
          (∑ m ∈ Finset.range (A + 1), N m) +
        (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ Finset.Icc 1 A, C q r) =
      greenFn (x - y) +
        (-N A +
          ∑ r ∈ Finset.range (A + 1),
            ∑ q ∈ (Finset.Icc 1 A).filter
              (fun q => A < r + 2 * q),
              C q r)
  rw [htelescope]
  have hPzero :
      P 0 = greenFn (x - y) := by
    exact parametrixP_zero M ρ lam ε x y ω
  rw [hPzero]
  simp only [Nat.not_le]
  abel

/-! ## Right-composition counterpart -/

/-- The right noise part of `Pₙ (λ_ε ξ_ε) G`, i.e. the
free-Green-postconditioned source in paper (3.17). -/
def rightParametrixNoiseSource
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (n : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  lamEps lam ε *
    ∫ z : T4,
      parametrixP M ρ lam ε n x z ω *
        (M.xiEps ρ ε ω z *
          greenFn (z - y))
      ∂paperMeasure

/-- The free-Green-postconditioned right action
`P_ε L_ε G`, expanded into its three finite pieces. -/
def rightPreconditionedParametrixAction
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  (∑ m ∈ Finset.range (A + 1),
      parametrixP M ρ lam ε m x y ω) -
    (∑ m ∈ Finset.range (A + 1),
      rightParametrixNoiseSource
        M ρ lam ε m x y ω) +
    ∑ r ∈ Finset.range (A + 1),
      ∑ q ∈ Finset.Icc 1 A,
        caseThreeRightCountertermBlock
          M ρ lam ε q r x y ω

/-- The postconditioned right remainder from paper (3.21). -/
def rightPreconditionedRemainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω) : ℝ :=
  -rightParametrixNoiseSource
      M ρ lam ε A x y ω +
    ∑ r ∈ Finset.range (A + 1),
      ∑ q ∈ (Finset.Icc 1 A).filter
        (fun q => A < r + 2 * q),
        caseThreeRightCountertermBlock
          M ρ lam ε q r x y ω

/-- Right counterpart of (3.20)--(3.21), after applying the free Green
operator on the right. -/
theorem rightPreconditionedParametrixAction_eq_green_add_remainder
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (A : ℕ) (x y : T4) (ω : M.Ω)
    (horder :
      ∀ m ∈ Finset.Icc 1 A,
        rightParametrixNoiseSource
            M ρ lam ε (m - 1) x y ω =
          parametrixP M ρ lam ε m x y ω +
            ∑ q ∈ Finset.Icc 1 (m / 2),
              caseThreeRightCountertermBlock
                M ρ lam ε q (m - 2 * q)
                  x y ω) :
    rightPreconditionedParametrixAction
        M ρ lam ε A x y ω =
      greenFn (x - y) +
        rightPreconditionedRemainder
          M ρ lam ε A x y ω := by
  let P : ℕ → ℝ :=
    fun m => parametrixP M ρ lam ε m x y ω
  let N : ℕ → ℝ :=
    fun m =>
      rightParametrixNoiseSource
        M ρ lam ε m x y ω
  let C : ℕ → ℕ → ℝ :=
    fun q r =>
      caseThreeRightCountertermBlock
        M ρ lam ε q r x y ω
  have htelescope :=
    parametrixTelescopeIcc A P N C
      (fun m hm => by
        simpa only [P, N, C] using horder m hm)
  unfold rightPreconditionedParametrixAction
  unfold rightPreconditionedRemainder
  change
    (∑ m ∈ Finset.range (A + 1), P m) -
          (∑ m ∈ Finset.range (A + 1), N m) +
        (∑ r ∈ Finset.range (A + 1),
          ∑ q ∈ Finset.Icc 1 A, C q r) =
      greenFn (x - y) +
        (-N A +
          ∑ r ∈ Finset.range (A + 1),
            ∑ q ∈ (Finset.Icc 1 A).filter
              (fun q => A < r + 2 * q),
              C q r)
  rw [htelescope]
  have hPzero :
      P 0 = greenFn (x - y) := by
    exact parametrixP_zero M ρ lam ε x y ω
  rw [hPzero]
  simp only [Nat.not_le]
  abel

end PartialPairing

end

end Anderson4D
