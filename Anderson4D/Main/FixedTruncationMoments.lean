import Anderson4D.Main.MomentAssembly
import Anderson4D.ForMathlib.GaussianMomentMethod
import Anderson4D.Continuum.TorusFourier

/-!
# Fixed-truncation moment assembly

This file develops paper (3.36)--(3.38) for a fixed perturbative cutoff.
The first step is the reality/conjugate-mode ledger needed to turn real
Cramér--Wold moments into the complex mode products controlled by
Proposition 3.6.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open Filter MeasureTheory ComplexConjugate
open scoped BigOperators Topology

/-- Fourier coefficients of the real random kernel `P_m` obey the expected
conjugate-mode identity.  The statement is unconditional because the
Bochner integral and complex conjugation use the same junk value `0`. -/
theorem conj_pmCoeff
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ) (m : ℕ)
    (α β : Z4) (ω : M.Ω) :
    conj (pmCoeff M ρ lam ε m α β ω) =
      pmCoeff M ρ lam ε m (-α) (-β) ω := by
  unfold pmCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with y
  simp only [map_mul, Complex.conj_ofReal, conj_charT4]

/-- One atomic choice in the expansion of a real fixed-truncation mode
functional: a requested mode, a positive perturbative order, and the
choice of the original or conjugate summand. -/
structure FixedTruncationAtom (s B : ℕ) where
  mode : Fin s
  orderIndex : Fin B
  conjugated : Bool
deriving DecidableEq, Fintype

/-- Product coordinates for summing over atoms. -/
def FixedTruncationAtom.equivProd (s B : ℕ) :
    FixedTruncationAtom s B ≃ Fin s × (Fin B × Bool) where
  toFun a := (a.mode, a.orderIndex, a.conjugated)
  invFun p :=
    { mode := p.1, orderIndex := p.2.1, conjugated := p.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem FixedTruncationAtom.equivProd_symm_apply
    {s B : ℕ} (p : Fin s × (Fin B × Bool)) :
    (FixedTruncationAtom.equivProd s B).symm p =
      { mode := p.1, orderIndex := p.2.1, conjugated := p.2.2 } :=
  rfl

/-- The positive perturbative order represented by an atom. -/
def FixedTruncationAtom.order {s B : ℕ}
    (a : FixedTruncationAtom s B) : ℕ :=
  a.orderIndex + 1

theorem FixedTruncationAtom.order_pos {s B : ℕ}
    (a : FixedTruncationAtom s B) :
    1 ≤ a.order := by
  unfold FixedTruncationAtom.order
  omega

theorem FixedTruncationAtom.order_le {s B : ℕ}
    (a : FixedTruncationAtom s B) :
    a.order ≤ B := by
  unfold FixedTruncationAtom.order
  exact a.orderIndex.isLt

/-- Mode negation encodes conjugation of a Fourier coefficient. -/
def FixedTruncationAtom.modePair {s B : ℕ}
    (modes : Fin s → Z4 × Z4)
    (a : FixedTruncationAtom s B) : Z4 × Z4 :=
  if a.conjugated then (-(modes a.mode).1, -(modes a.mode).2)
  else modes a.mode

/-- Coefficient in the identity
`Re(c z) = (c z + conj(c) conj(z))/2`. -/
def FixedTruncationAtom.coeff {s B : ℕ}
    (c : Fin s → ℂ) (a : FixedTruncationAtom s B) : ℂ :=
  if a.conjugated then conj (c a.mode) / 2 else c a.mode / 2

/-- The complex fixed-truncation scalar whose real part is used in the
Cramér--Wold argument. -/
def fixedTruncationModeSum
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (B s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) : ℂ :=
  (lamEps lam ε : ℂ)⁻¹ *
    ∑ j, c j * ∑ m : Fin B,
      pmCoeff M ρ lam ε (m + 1)
        (modes j).1 (modes j).2 ω

/-- Real scalar tested in the fixed-`B` moment method. -/
def fixedTruncationReal
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (B s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) : ℝ :=
  (fixedTruncationModeSum M ρ lam ε B s modes c ω).re

/-- One normalized complex atom in the real-part expansion. -/
def fixedTruncationAtomTerm
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {B s : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (a : FixedTruncationAtom s B) (ω : M.Ω) : ℂ :=
  a.coeff c * (lamEps lam ε : ℂ)⁻¹ *
    pmCoeff M ρ lam ε a.order
      (a.modePair modes).1 (a.modePair modes).2 ω

/-- Exact conjugate-mode expansion of the real fixed-truncation scalar. -/
theorem ofReal_fixedTruncationReal_eq_sum_atoms
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (B s : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) :
    (fixedTruncationReal M ρ lam ε B s modes c ω : ℂ) =
      ∑ a : FixedTruncationAtom s B,
        fixedTruncationAtomTerm M ρ lam ε modes c a ω := by
  rw [← (FixedTruncationAtom.equivProd s B).symm.sum_comp
    (fun a : FixedTruncationAtom s B =>
      fixedTruncationAtomTerm M ρ lam ε modes c a ω)]
  rw [fixedTruncationReal, Complex.re_eq_add_conj]
  unfold fixedTruncationModeSum fixedTruncationAtomTerm
    FixedTruncationAtom.coeff FixedTruncationAtom.modePair
    FixedTruncationAtom.order
  simp_rw [Fintype.sum_prod_type]
  simp only [FixedTruncationAtom.equivProd_symm_apply, Fintype.sum_bool]
  simp only [map_mul, map_sum, Complex.conj_inv, Complex.conj_ofReal,
    conj_pmCoeff, Bool.false_eq_true, ↓reduceIte, Finset.mul_sum]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [Finset.sum_mul]
  abel

/-- The `r`-th power of a real fixed-truncation scalar is the finite sum
over all assignments of one atom to each factor. -/
theorem ofReal_fixedTruncationReal_pow_eq_sum_assignments
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    (B s r : ℕ) (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (ω : M.Ω) :
    (fixedTruncationReal M ρ lam ε B s modes c ω : ℂ) ^ r =
      ∑ assignment : Fin r → FixedTruncationAtom s B,
        ∏ i, fixedTruncationAtomTerm M ρ lam ε modes c
          (assignment i) ω := by
  rw [ofReal_fixedTruncationReal_eq_sum_atoms, Fintype.sum_pow]

/-- Pull all deterministic coefficients and normalizing powers out of one
assignment product.  The remaining product is exactly the random product
appearing in Proposition 3.6. -/
theorem prod_fixedTruncationAtomTerm
    (M : NoiseModel) (ρ : SmoothCutoff) (lam ε : ℝ)
    {B s r : ℕ} (modes : Fin s → Z4 × Z4) (c : Fin s → ℂ)
    (assignment : Fin r → FixedTruncationAtom s B) (ω : M.Ω) :
    (∏ i, fixedTruncationAtomTerm M ρ lam ε modes c
        (assignment i) ω) =
      (∏ i, (assignment i).coeff c) *
        (lamEps lam ε : ℂ)⁻¹ ^ r *
        ∏ i, pmCoeff M ρ lam ε (assignment i).order
          ((assignment i).modePair modes).1
          ((assignment i).modePair modes).2 ω := by
  simp only [fixedTruncationAtomTerm, Finset.prod_mul_distrib]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end

end Anderson4D
