import Anderson4D.PermSum.SingleScaleOuterAssembly
import Anderson4D.PermSum.SingleScalePowerLedger

/-!
# Leaf payoff ledger for the end of Proposition 5.10

The inner estimate supplies one inverse-square parent scale per labeled
copy.  The outer majority estimate supplies `originalOuterLeafPayoff`.
This file combines those two products exactly into the simple/compound
factorial and scale products printed in (5.89).
-/

namespace Anderson4D

open PlaneTree
open scoped BigOperators

noncomputable section

private theorem prod_heppLeaf_eq_prod_leaves
    {t : PlaneTree} (f : HeppLeaf t → ℝ) (g : VPos t → ℝ)
    (hfg : ∀ v (hv : v ∈ Leaves t), f ⟨v, hv⟩ = g v) :
    (∏ l : HeppLeaf t, f l) = ∏ v ∈ Leaves t, g v := by
  apply Finset.prod_bij
      (fun l _hl => l.1)
      (fun l _hl => l.2)
      (fun a _ha b _hb hab => Subtype.ext hab)
      (fun v hv => ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩)
  intro l _hl
  exact hfg l.1 l.2

private theorem sqrtFactorial_mul_quarterFactorial (k : ℕ) :
    sqrtFactorial k * quarterFactorial k =
      factorialThreeQuarters k := by
  have hk : 0 < ((k.factorial : ℕ) : ℝ) := by positivity
  unfold sqrtFactorial quarterFactorial factorialThreeQuarters
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk]
  congr 1
  ring

/--
The global factorial/outer-payoff product, split over the exact simple and
compound leaf partition.
-/
theorem globalFactorialOuterPayoff_eq
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    (∏ l : HeppLeaf t,
        sqrtFactorial (leafMultiplicity mu l) *
          originalOuterLeafPayoff Nm mu compound l) =
      (∏ l ∈ simpleLeaves t compound,
        sqrtFactorial (mu.m l) *
          (scaleN Nm (parentV l) : ℝ) ^ (2 * (mu.m l - 2))) *
      ∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l) := by
  rw [prod_heppLeaf_eq_prod_leaves
    (fun l =>
      sqrtFactorial (leafMultiplicity mu l) *
        originalOuterLeafPayoff Nm mu compound l)
    (fun l =>
      sqrtFactorial (mu.m l) *
        if l ∈ compound then
          quarterFactorial (mu.m l)
        else
          (scaleN Nm (parentV l) : ℝ) ^ (2 * (mu.m l - 2)))
    (fun v hv => by
      by_cases hc : v ∈ compound
      · simp [leafMultiplicity, originalOuterLeafPayoff,
          hc]
      · simp [leafMultiplicity, originalOuterLeafPayoff,
          simpleScaleExponent, hc])]
  rw [← simple_union_compound t compound,
    Finset.prod_union (disjoint_simple_compound t compound)]
  congr 1
  · apply Finset.prod_congr rfl
    intro l hl
    have hc : l ∉ compound := (Finset.mem_sdiff.mp hl).2
    simp [hc]
  · apply Finset.prod_congr rfl
    intro l hl
    have hc : l ∈ compound := (Finset.mem_inter.mp hl).2
    simp [hc, sqrtFactorial_mul_quarterFactorial]

/--
Exact (5.88)-to-(5.89) leaf ledger.  One inverse-square parent-scale factor
per labeled copy combines with the outer payoff to leave exponent `-4` on
simple leaves and exponent `-2m_l` on compound leaves.
-/
theorem globalBaseScaleFactorialOuterPayoff_eq
    {t : PlaneTree} (Nm : HeppMarking t) (mu : Multiplicities t)
    (compound : Finset (VPos t)) :
    (∏ l : HeppLeaf t,
        (scaleN Nm (parentV l.1) : ℝ) ^
          ((-2 : ℤ) * (leafMultiplicity mu l : ℤ))) *
      (∏ l : HeppLeaf t,
        sqrtFactorial (leafMultiplicity mu l) *
          originalOuterLeafPayoff Nm mu compound l) =
      (∏ l ∈ simpleLeaves t compound, sqrtFactorial (mu.m l)) *
      (∏ l ∈ compoundLeaves t compound,
        factorialThreeQuarters (mu.m l)) *
      (∏ l ∈ simpleLeaves t compound,
        (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ)) *
      ∏ l ∈ compoundLeaves t compound,
        (scaleN Nm (parentV l) : ℝ) ^
          ((-2 : ℤ) * (mu.m l : ℤ)) := by
  rw [← Finset.prod_mul_distrib]
  rw [prod_heppLeaf_eq_prod_leaves
    (fun l =>
      (scaleN Nm (parentV l.1) : ℝ) ^
          ((-2 : ℤ) * (leafMultiplicity mu l : ℤ)) *
        (sqrtFactorial (leafMultiplicity mu l) *
          originalOuterLeafPayoff Nm mu compound l))
    (fun l =>
      if l ∈ compound then
        factorialThreeQuarters (mu.m l) *
          (scaleN Nm (parentV l) : ℝ) ^
            ((-2 : ℤ) * (mu.m l : ℤ))
      else
        sqrtFactorial (mu.m l) *
          (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ))
    (fun v hv => by
      by_cases hc : v ∈ compound
      · simp only [leafMultiplicity, originalOuterLeafPayoff, hc,
          if_pos]
        rw [sqrtFactorial_mul_quarterFactorial]
        ring
      · have hm : 2 ≤ mu.m v := mu.two_le v hv
        have hscale :
            (scaleN Nm (parentV v) : ℝ) ≠ 0 := by
          exact_mod_cast (scaleN_pos Nm (parentV v)).ne'
        simp only [leafMultiplicity, originalOuterLeafPayoff, hc,
          if_false, simpleScaleExponent]
        rw [← zpow_natCast]
        have hexp :
            (-2 : ℤ) * (mu.m v : ℤ) +
                (2 * (mu.m v - 2) : ℕ) =
              -4 := by
          exact_mod_cast show
            (-2 : ℤ) * (mu.m v : ℤ) +
                ((2 * (mu.m v - 2) : ℕ) : ℤ) = -4 by
            omega
        calc
          (scaleN Nm (parentV v) : ℝ) ^
                ((-2 : ℤ) * (mu.m v : ℤ)) *
              (sqrtFactorial (mu.m v) *
                (scaleN Nm (parentV v) : ℝ) ^
                  ((2 * (mu.m v - 2) : ℕ) : ℤ)) =
              sqrtFactorial (mu.m v) *
                ((scaleN Nm (parentV v) : ℝ) ^
                    ((-2 : ℤ) * (mu.m v : ℤ)) *
                  (scaleN Nm (parentV v) : ℝ) ^
                    ((2 * (mu.m v - 2) : ℕ) : ℤ)) := by ring
          _ = sqrtFactorial (mu.m v) *
                (scaleN Nm (parentV v) : ℝ) ^
                  ((-2 : ℤ) * (mu.m v : ℤ) +
                    ((2 * (mu.m v - 2) : ℕ) : ℤ)) := by
            rw [zpow_add₀ hscale]
          _ = sqrtFactorial (mu.m v) *
                (scaleN Nm (parentV v) : ℝ) ^ (-4 : ℤ) := by
            rw [hexp])]
  rw [← simple_union_compound t compound,
    Finset.prod_union (disjoint_simple_compound t compound)]
  have hs :
      (∏ l ∈ simpleLeaves t compound,
          if l ∈ compound then
            factorialThreeQuarters (mu.m l) *
              (scaleN Nm (parentV l) : ℝ) ^
                ((-2 : ℤ) * (mu.m l : ℤ))
          else
            sqrtFactorial (mu.m l) *
              (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ)) =
        ∏ l ∈ simpleLeaves t compound,
          sqrtFactorial (mu.m l) *
            (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ) := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [if_neg (Finset.mem_sdiff.mp hl).2]
  have hc :
      (∏ l ∈ compoundLeaves t compound,
          if l ∈ compound then
            factorialThreeQuarters (mu.m l) *
              (scaleN Nm (parentV l) : ℝ) ^
                ((-2 : ℤ) * (mu.m l : ℤ))
          else
            sqrtFactorial (mu.m l) *
              (scaleN Nm (parentV l) : ℝ) ^ (-4 : ℤ)) =
        ∏ l ∈ compoundLeaves t compound,
          factorialThreeQuarters (mu.m l) *
            (scaleN Nm (parentV l) : ℝ) ^
              ((-2 : ℤ) * (mu.m l : ℤ)) := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [if_pos (Finset.mem_inter.mp hl).2]
  rw [hs, hc, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end

end Anderson4D
