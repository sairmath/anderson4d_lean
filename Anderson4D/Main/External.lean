import Anderson4D.Parametrix.Random
import Anderson4D.Continuum.FourPointCoefficient

/-!
# The external input: Proposition 3.6 (blueprint node P-3.6)

Paper: P-mom — the external input Prop 3.6 (Gabriel–Rosati)

The frozen statement of Deng–Shen's Proposition 3.6 in coefficient form
(PAPER_MAP remark 6): existence of the moment-asymptotics data
`𝔛 m₁ m₂` and constants under which the joint moments of the parametrix
mode coefficients `pmCoeff` Wick-factorize ((3.26)) and the pair
covariances converge to multiples of the four-point kernel coefficients
((3.27)–(3.28)).  The main theorem (`Anderson4D.Main.Theorem`) is frozen
*conditionally* on this proposition, quantified over all couplings.
-/

namespace Anderson4D

noncomputable section

open MeasureTheory

/-- **Proposition 3.6 with one named geometric constant.**  The paper's
generic constant `C` in the global coefficient bound is uniform in the
fixed truncation parameters `B` and `r`.  Keeping it as an explicit
parameter is essential for the corner-tail estimate in Step 3. -/
def Prop36WithConstant
    (M : NoiseModel) (ρ : SmoothCutoff) (lam C : ℝ) : Prop :=
  ∀ B r : ℕ, ∃ 𝔛 : ℕ → ℕ → ℝ,
    (∀ m₁ m₂ : ℕ, 1 ≤ m₁ → 1 ≤ m₂ →
      |𝔛 m₁ m₂| ≤ C * (C * lam) ^ (m₁ + m₂ - 2)) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal m).filter
          (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2), 𝔛 p.1 p.2) =
        if Even m then
          (lam / (Real.sqrt 2 * Real.pi)) ^ (m - 2)
        else 0) ∧
    ∀ modes : Fin r → (Z4 × Z4) × ℕ,
      (∀ j, 1 ≤ (modes j).2 ∧ (modes j).2 ≤ B) →
      (∀ ε : ℝ, ∀ j, Measurable
        (pmCoeff M ρ lam ε (modes j).2
          (modes j).1.1 (modes j).1.2)) ∧
      (∀ ε : ℝ, Integrable
        (fun ω => ∏ j, pmCoeff M ρ lam ε (modes j).2
          (modes j).1.1 (modes j).1.2 ω)) ∧
      ∃ C' : ℝ, 0 < C' ∧
        ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
          (‖(∫ ω, ∏ j, pmCoeff M ρ lam ε (modes j).2 (modes j).1.1
                (modes j).1.2 ω) -
              ∑ κ ∈ Finset.univ.filter
                  (fun κ : PartialPairing (Fin r) => κ.IsFull),
                ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
                  (∫ ω, pmCoeff M ρ lam ε (modes i).2 (modes i).1.1
                      (modes i).1.2 ω *
                    pmCoeff M ρ lam ε (modes (κ i)).2 (modes (κ i)).1.1
                      (modes (κ i)).1.2 ω)‖
            ≤ C' * lamEps lam ε ^ r / |Real.log ε|) ∧
          ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
            1 ≤ m₂ → m₂ ≤ B → ∀ α₁ β₁ α₂ β₂ : Z4,
            ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 * 𝔛 m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
              ≤ C' * lamEps lam ε ^ 2 / |Real.log ε|

/-- **Proposition 3.6 of the paper (node P-3.6), coefficient form.**
There is one positive coefficient-bound constant, uniform over the
fixed moment bound `B` and family size `r`; after fixing `B,r`, the
coefficient table may still be chosen existentially.  The clauses are:

* **bound clause** (part of (3.27)): `|𝔛 m₁ m₂| ≤ C (Cλ)^{m₁+m₂-2}`;
* **sum clause** ((3.28)): the sum is over positive orders
  `m₁,m₂ ≥ 1`; it equals `(λ/(√2·π))^{m-2}` for even `m`
  and zero for odd `m`;
* **Wick factorization** ((3.26)): for every family of `r` mode/order
  triples, eventually as `ε ↓ 0` the joint moment of the `pmCoeff`s
  differs from its full-pairing (Wick) factorization by
  `O(λ_ε^r/|log ε|)`; the paper's family `(m_j, α_j, β_j)` is packaged as
  `modes : Fin r → (Z4 × Z4) × ℕ` — component `.1` the mode pair
  `(α_j, β_j)`, component `.2` the order `m_j` — so a single quantifier
  covers it.  The same clause records the implicit regularity used when
  the paper calls these quantities moments: the coefficients are
  measurable and every displayed finite product is integrable;
* **covariance asymptotics** ((3.27)): each pair moment is
  `λ_ε² 𝔛 m₁ m₂ · fourPointHCoeff + O(λ_ε²/|log ε|)`.

Norms `‖·‖` are the complex modulus.  The eventuality filter is
`ε ↓ 0` within `(0, ∞)`. -/
structure Prop36 (M : NoiseModel) (ρ : SmoothCutoff) (lam : ℝ) where
  /-- The paper's uniform geometric coefficient-bound constant. -/
  boundConstant : ℝ
  boundConstant_pos : 0 < boundConstant
  withBoundConstant :
    Prop36WithConstant M ρ lam boundConstant

namespace Prop36

/-- Canonical coefficient table selected after fixing the paper's
finite order and family parameters. -/
def coefficientTable
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (h : Prop36 M ρ lam) (B r : ℕ) : ℕ → ℕ → ℝ :=
  Classical.choose (h.withBoundConstant B r)

theorem coefficientTable_spec
    {M : NoiseModel} {ρ : SmoothCutoff} {lam : ℝ}
    (h : Prop36 M ρ lam) (B r : ℕ) :
    (∀ m₁ m₂ : ℕ, 1 ≤ m₁ → 1 ≤ m₂ →
      |h.coefficientTable B r m₁ m₂| ≤
        h.boundConstant *
          (h.boundConstant * lam) ^ (m₁ + m₂ - 2)) ∧
    (∀ m : ℕ, 2 ≤ m →
      (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal m).filter
          (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2),
          h.coefficientTable B r p.1 p.2) =
        if Even m then
          (lam / (Real.sqrt 2 * Real.pi)) ^ (m - 2)
        else 0) ∧
    ∀ modes : Fin r → (Z4 × Z4) × ℕ,
      (∀ j, 1 ≤ (modes j).2 ∧ (modes j).2 ≤ B) →
      (∀ ε : ℝ, ∀ j, Measurable
        (pmCoeff M ρ lam ε (modes j).2
          (modes j).1.1 (modes j).1.2)) ∧
      (∀ ε : ℝ, Integrable
        (fun ω => ∏ j, pmCoeff M ρ lam ε (modes j).2
          (modes j).1.1 (modes j).1.2 ω)) ∧
      ∃ C' : ℝ, 0 < C' ∧
        ∀ᶠ ε in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
          (‖(∫ ω, ∏ j, pmCoeff M ρ lam ε (modes j).2 (modes j).1.1
                (modes j).1.2 ω) -
              ∑ κ ∈ Finset.univ.filter
                  (fun κ : PartialPairing (Fin r) => κ.IsFull),
                ∏ i ∈ κ.pairSupport.filter (fun i => i < κ i),
                  (∫ ω, pmCoeff M ρ lam ε (modes i).2 (modes i).1.1
                      (modes i).1.2 ω *
                    pmCoeff M ρ lam ε (modes (κ i)).2 (modes (κ i)).1.1
                      (modes (κ i)).1.2 ω)‖
            ≤ C' * lamEps lam ε ^ r / |Real.log ε|) ∧
          ∀ m₁ m₂ : ℕ, 1 ≤ m₁ → m₁ ≤ B →
            1 ≤ m₂ → m₂ ≤ B → ∀ α₁ β₁ α₂ β₂ : Z4,
            ‖(∫ ω, pmCoeff M ρ lam ε m₁ α₁ β₁ ω *
                pmCoeff M ρ lam ε m₂ α₂ β₂ ω) -
              (lamEps lam ε ^ 2 *
                  h.coefficientTable B r m₁ m₂ : ℝ) •
                fourPointHCoeff α₁ β₁ α₂ β₂‖
              ≤ C' * lamEps lam ε ^ 2 / |Real.log ε| :=
  Classical.choose_spec (h.withBoundConstant B r)

end Prop36

/-- Uniform-in-coupling form of the external input.  This is the
precise hypothesis needed by the conditional main theorem to choose a
single small-coupling threshold before `lam` is quantified. -/
def Prop36Family (M : NoiseModel) (ρ : SmoothCutoff) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ lam : ℝ, 0 < lam → Prop36WithConstant M ρ lam C

/-- The single coefficient-bound constant selected once for the whole
positive-coupling family. -/
noncomputable def Prop36Family.boundConstant
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) : ℝ :=
  Classical.choose h

theorem Prop36Family.boundConstant_pos
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) :
    0 < h.boundConstant :=
  (Classical.choose_spec h).1

theorem Prop36Family.withBoundConstant
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) :
    ∀ lam : ℝ, 0 < lam →
      Prop36WithConstant M ρ lam h.boundConstant :=
  (Classical.choose_spec h).2

/-- A uniform family specializes to Proposition 3.6 data at every
positive coupling, retaining the family's single selected constant. -/
noncomputable def Prop36Family.prop36
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) {lam : ℝ} (hlam : 0 < lam) :
    Prop36 M ρ lam :=
  ⟨h.boundConstant, h.boundConstant_pos,
    h.withBoundConstant lam hlam⟩

@[simp] theorem Prop36Family.prop36_boundConstant
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) {lam : ℝ} (hlam : 0 < lam) :
    (h.prop36 hlam).boundConstant = h.boundConstant :=
  rfl

/-- A concrete positive coupling threshold depending only on the one
family-wide coefficient constant.  The extra cutoff at one also gives
the paper's subcritical inequality `λ² < 2π²`. -/
noncomputable def Prop36Family.couplingThreshold
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) : ℝ :=
  min (1 / (2 * h.boundConstant)) 1

theorem Prop36Family.couplingThreshold_pos
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) :
    0 < h.couplingThreshold := by
  unfold couplingThreshold
  apply lt_min
  · exact div_pos zero_lt_one
      (mul_pos (by norm_num) h.boundConstant_pos)
  · norm_num

/-- Every coupling below the family threshold has geometric ratio
strictly smaller than one. -/
theorem Prop36Family.boundConstant_mul_lt_one
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) {lam : ℝ}
    (hlam : lam ∈ Set.Ioo 0 h.couplingThreshold) :
    h.boundConstant * lam < 1 := by
  have hlt :
      lam < 1 / (2 * h.boundConstant) := by
    exact (lt_min_iff.mp hlam.2).1
  have hden : 0 < 2 * h.boundConstant :=
    mul_pos (by norm_num) h.boundConstant_pos
  have hmul : lam * (2 * h.boundConstant) < 1 :=
    (lt_div_iff₀ hden).mp hlt
  nlinarith

/-- The same concrete threshold lies safely inside the paper's
subcritical range. -/
theorem Prop36Family.sq_lt_two_mul_pi_sq
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) {lam : ℝ}
    (hlam : lam ∈ Set.Ioo 0 h.couplingThreshold) :
    lam ^ 2 < 2 * Real.pi ^ 2 := by
  have hlt : lam < 1 := by
    exact (lt_min_iff.mp hlam.2).2
  have hlamSq : lam ^ 2 < 1 := by
    exact (sq_lt_one_iff₀ hlam.1.le).2 hlt
  have hpi : (1 : ℝ) < 2 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  exact hlamSq.trans hpi

/-- Refine the external Proposition 3.6 threshold by a second positive
geometric constant.  The latter is the constant produced internally by
the deterministic second-moment estimate, so both geometric series can
be controlled by one coupling range. -/
noncomputable def Prop36Family.couplingThresholdWith
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) (powerConstant : ℝ) : ℝ :=
  min h.couplingThreshold (1 / (2 * powerConstant))

theorem Prop36Family.couplingThresholdWith_pos
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) {powerConstant : ℝ}
    (hpower : 0 < powerConstant) :
    0 < h.couplingThresholdWith powerConstant := by
  unfold couplingThresholdWith
  apply lt_min
  · exact h.couplingThreshold_pos
  · exact div_pos zero_lt_one
      (mul_pos (by norm_num) hpower)

/-- The refined range remains inside the range selected from the
external coefficient table. -/
theorem Prop36Family.mem_couplingThreshold_of_mem_couplingThresholdWith
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) {powerConstant lam : ℝ}
    (hlam : lam ∈ Set.Ioo 0
      (h.couplingThresholdWith powerConstant)) :
    lam ∈ Set.Ioo 0 h.couplingThreshold :=
  ⟨hlam.1, (lt_min_iff.mp hlam.2).1⟩

/-- The internally produced geometric ratio is strictly less than one
throughout the refined coupling range. -/
theorem Prop36Family.powerConstant_mul_lt_one
    {M : NoiseModel} {ρ : SmoothCutoff}
    (h : Prop36Family M ρ) {powerConstant lam : ℝ}
    (hpower : 0 < powerConstant)
    (hlam : lam ∈ Set.Ioo 0
      (h.couplingThresholdWith powerConstant)) :
    powerConstant * lam < 1 := by
  have hlt :
      lam < 1 / (2 * powerConstant) :=
    (lt_min_iff.mp hlam.2).2
  have hden : 0 < 2 * powerConstant :=
    mul_pos (by norm_num) hpower
  have hmul : lam * (2 * powerConstant) < 1 :=
    (lt_div_iff₀ hden).mp hlt
  nlinarith

end

end Anderson4D
