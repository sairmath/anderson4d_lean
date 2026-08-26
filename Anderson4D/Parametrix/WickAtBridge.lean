import Anderson4D.Parametrix.Random
import Anderson4D.Probability.PartialPairingWick

/-!
# Bridge from `wickAt` to recursive Wick polynomials

The random parametrix layer defines its Wick factor directly as a sum over
partial pairings of the outer pairing's single indices.  This file identifies
that formula with `explicitPartialPairingWick` and hence with
`wickPolynomial`.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

namespace PartialPairing

/-- In a finite linear order, the smaller endpoints of the nontrivial
two-cycles are in bijection with the unordered pairs. -/
theorem card_representatives_eq_card_pairs
    {α : Type*} [Fintype α] [LinearOrder α]
    (κ : PartialPairing α) :
    κ.representatives.card = κ.pairs.card := by
  classical
  refine Finset.card_bij (fun i _hi => s(i, κ i)) ?_ ?_ ?_
  · intro i hi
    exact PartialPairing.mem_pairs.mpr
      ⟨i, (PartialPairing.mem_representatives.mp hi).1, rfl⟩
  · intro i hi j hj hij
    rcases Sym2.eq_iff.mp hij with hsame | hswap
    · exact hsame.1
    · have hi' := (PartialPairing.mem_representatives.mp hi).2
      have hj' := (PartialPairing.mem_representatives.mp hj).2
      have hback : κ i < i := by
        calc
          κ i = j := hswap.2
          _ < κ j := hj'
          _ = i := hswap.1.symm
      exact False.elim (lt_asymm hi' hback)
  · intro p hp
    obtain ⟨a, ha, hap⟩ := PartialPairing.mem_pairs.mp hp
    by_cases hlt : a < κ a
    · exact ⟨a, PartialPairing.mem_representatives.mpr
        ⟨ha, hlt⟩, hap⟩
    · have hback : κ a < a := by
        exact lt_of_le_of_ne (le_of_not_gt hlt) ha
      refine ⟨κ a, PartialPairing.mem_representatives.mpr
        ⟨?_, ?_⟩, ?_⟩
      · exact fun h => ha (by
          rw [κ.apply_apply] at h
          exact h.symm)
      · simpa only [κ.apply_apply] using hback
      · rw [κ.apply_apply, Sym2.eq_swap]
        exact hap

/-- Pulling one minus sign out of every representative covariance produces
the sign convention used by `wickAt`. -/
theorem prod_neg_eq_neg_one_pow_pairs_mul
    {α : Type*} [Fintype α] [LinearOrder α]
    (κ : PartialPairing α) (c : α → ℝ) :
    (∏ i ∈ κ.representatives, -c i) =
      (-1 : ℝ) ^ κ.pairs.card * ∏ i ∈ κ.representatives, c i := by
  rw [Finset.prod_neg, κ.card_representatives_eq_card_pairs]

end PartialPairing

/-- The single indices of `κ`, evaluated in increasing order at the
corresponding internal positions of `xt`. -/
def wickAtSingleLabels {m : ℕ} (κ : PartialPairing (Fin m))
    (xt : Fin (m + 2) → T4) : List T4 :=
  List.ofFn fun j : Fin κ.singles.card =>
    xt (varIdx (κ.singles.orderEmbOfFin rfl j))

/-- A generic ordered-finset bridge from a partial-pairing sum on the
subtype carrier to the list-indexed explicit Wick expansion. -/
theorem explicitPartialPairingWick_finsetSubtype_eq_list
    {α ι Ω : Type*} [LinearOrder α]
    (s : Finset α) (C : ι → ι → ℝ) (X : ι → Ω → ℝ)
    (v : s → ι) (ω : Ω) :
    explicitPartialPairingWick C X v ω =
      explicitPartialPairingWickList C X
        (List.ofFn fun j : Fin s.card =>
          v (s.orderIsoOfFin rfl j)) ω := by
  let labels :=
    List.ofFn fun j : Fin s.card => v (s.orderIsoOfFin rfl j)
  let e : Fin labels.length ≃o s :=
    (Fin.castOrderIso (by simp [labels])).trans
      (s.orderIsoOfFin rfl)
  let ee : Fin labels.length ≃ s := EquivLike.toEquiv e
  have horder : ∀ i j, ee i < ee j ↔ i < j :=
    fun _ _ => e.lt_iff_lt
  have hlabel :
      v ∘ ee = fun i : Fin labels.length => labels.get i := by
    funext i
    simp [labels, e, ee, Function.comp_apply]
    apply congrArg v
    congr 1
  change explicitPartialPairingWick C X v ω =
    explicitPartialPairingWickList C X labels ω
  unfold explicitPartialPairingWick explicitPartialPairingWickList
  rw [explicitPartialPairingWickBy_congr
    (· < ·) (· < ·) ee horder C X]
  rw [hlabel]
  rfl

/-- The summand in `wickAt` is precisely the standard explicit Wick weight:
its external sign is the product of the minus signs on representative
covariances. -/
theorem wickAt_summand_eq_partialPairingWickWeight
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4)
    (ω : M.Ω) (κ' : PartialPairing {i // i ∈ κ.singles}) :
    (-1 : ℝ) ^ κ'.pairs.card *
        (∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
          ρ.etaEpsT4 ε
            (xt (varIdx i.val) - xt (varIdx (κ' i).val))) *
        ∏ i ∈ κ'.singles,
          M.xiEps ρ ε ω (xt (varIdx i.val)) =
      partialPairingWickWeight
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
        (fun x ω' => M.xiEps ρ ε ω' x)
        (fun i : {i // i ∈ κ.singles} => xt (varIdx i.val))
        κ' ω := by
  change
    ((-1 : ℝ) ^ κ'.pairs.card *
        (∏ i ∈ κ'.representatives,
          ρ.etaEpsT4 ε
            (xt (varIdx i.val) - xt (varIdx (κ' i).val)))) *
        ∏ i ∈ κ'.singles,
          M.xiEps ρ ε ω (xt (varIdx i.val)) = _
  unfold partialPairingWickWeight partialPairingWickWeightBy
  rw [Finset.prod_neg]
  change
    ((-1 : ℝ) ^ κ'.pairs.card *
        (∏ i ∈ κ'.representatives,
          ρ.etaEpsT4 ε
            (xt (varIdx i.val) - xt (varIdx (κ' i).val)))) *
        ∏ i ∈ κ'.singles,
          M.xiEps ρ ε ω (xt (varIdx i.val)) =
      ((-1 : ℝ) ^ κ'.representatives.card *
        (∏ i ∈ κ'.representatives,
          ρ.etaEpsT4 ε
            (xt (varIdx i.val) - xt (varIdx (κ' i).val)))) *
        ∏ i ∈ κ'.singles,
          M.xiEps ρ ε ω (xt (varIdx i.val))
  apply congrArg (fun z : ℝ =>
    z * ∏ i ∈ κ'.singles,
      M.xiEps ρ ε ω (xt (varIdx i.val)))
  apply congrArg (fun z : ℝ =>
    z * ∏ i ∈ κ'.representatives,
      ρ.etaEpsT4 ε
        (xt (varIdx i.val) - xt (varIdx (κ' i).val)))
  exact congrArg (fun n : ℕ => (-1 : ℝ) ^ n)
    κ'.card_representatives_eq_card_pairs.symm

/-- `wickAt` is the explicit partial-pairing Wick expansion on the ordered
subtype of the original pairing's single indices. -/
theorem wickAt_eq_explicitPartialPairingWick
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4)
    (ω : M.Ω) :
    wickAt M ρ ε κ xt ω =
      explicitPartialPairingWick
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
        (fun x ω' => M.xiEps ρ ε ω' x)
        (fun i : {i // i ∈ κ.singles} => xt (varIdx i.val)) ω := by
  unfold wickAt
  change
    (∑ κ' : PartialPairing {i // i ∈ κ.singles},
      (-1 : ℝ) ^ κ'.pairs.card *
        (∏ i ∈ κ'.pairSupport.filter (fun i => i < κ' i),
          ρ.etaEpsT4 ε
            (xt (varIdx i.val) - xt (varIdx (κ' i).val))) *
        ∏ i ∈ κ'.singles,
          M.xiEps ρ ε ω (xt (varIdx i.val))) =
      ∑ κ' : PartialPairing {i // i ∈ κ.singles},
        partialPairingWickWeight
          (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
          (fun x ω' => M.xiEps ρ ε ω' x)
          (fun i : {i // i ∈ κ.singles} => xt (varIdx i.val))
          κ' ω
  apply Fintype.sum_congr
  intro κ'
  exact wickAt_summand_eq_partialPairingWickWeight
    M ρ ε κ xt ω κ'

/-- **P-3.4 Wick bridge.**  The explicit sub-pairing formula used by
`Parametrix.Random.wickAt` is exactly the recursive Wick polynomial of the
noise values at the original pairing's single indices, enumerated in their
ambient order. -/
theorem wickAt_eq_wickPolynomial
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4)
    (ω : M.Ω) :
    wickAt M ρ ε κ xt ω =
      wickPolynomial
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
        (fun x ω' => M.xiEps ρ ε ω' x)
        (wickAtSingleLabels κ xt) ω := by
  rw [wickAt_eq_explicitPartialPairingWick]
  rw [explicitPartialPairingWick_finsetSubtype_eq_list]
  rw [explicitPartialPairingWickList_apply_eq_wickPolynomial]
  rfl

/-- The random factor used in `randRI` is literally the degree
`|singles κ|` finite-product chaos projection.  Together with
`GaussianPolynomialLaw.integral_chaosProjProduct_mul_eq_zero_of_ne`,
this closes the minimal `Projₖ` API required by (2.4) and (3.2). -/
theorem wickAt_eq_chaosProjProduct
    (M : NoiseModel) (ρ : SmoothCutoff) (ε : ℝ) {m : ℕ}
    (κ : PartialPairing (Fin m)) (xt : Fin (m + 2) → T4)
    (ω : M.Ω) :
    wickAt M ρ ε κ xt ω =
      chaosProjProduct κ.singles.card
        (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
        (fun x ω' => M.xiEps ρ ε ω' x)
        (wickAtSingleLabels κ xt) ω := by
  rw [wickAt_eq_wickPolynomial]
  have hdegree :
      (wickAtSingleLabels κ xt).length =
        κ.singles.card := by
    simp [wickAtSingleLabels]
  rw [chaosProjProduct_eq_wickPolynomial
    (fun x y : T4 => ρ.etaEpsT4 ε (x - y))
    (fun x ω' => M.xiEps ρ ε ω' x) hdegree]

end

end Anderson4D
