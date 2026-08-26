import Anderson4D.DetParametrix.Core.FinalBound
import Anderson4D.Continuum.PrimitiveProposition41

/-!
# The terminal primitive block in the R-322 reduction

Paper §4.1, Step 4 ends the interval-removal loop with one primitive full
pairing on the remaining generalized interval.  This file closes the part of
that assertion which does not yet involve previously collapsed input kernels:

* a primitive full pairing on a nonempty interval has exactly one extraction,
  namely the whole interval;
* its closed `J` integrand is literally the integrand of Proposition 4.1;
* summing over every primitive full pairing gives the primitive kernel (4.2);
* consequently Proposition 4.1 gives the exact pointwise (4.3) majorant for
  this terminal sum.

This is a constructive component of R-322.  It does not assume
`RenormReductionOutput`, a pointwise bound for `detJ`, or any form of (3.22).
The remaining general R-322 step is to show that successive proper-block
collapses produce admissible generalized inputs and preserve this terminal
identity.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory
open scoped BigOperators

/-! ## A primitive full pairing has one whole-interval extraction -/

/-- On a nonempty carrier, the extraction list of a primitive full pairing is
the singleton consisting of the two endpoints of the whole interval. -/
theorem extract_eq_singleton_whole_of_full_of_primitive
    {m : ℕ} {κ : PartialPairing (Fin (m + 1))}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    extract κ = [(0, Fin.last m)] := by
  have hcand :
      ∃ a b, IsRelFullyPaired κ
        (Finset.univ : Finset (Fin (m + 1))) a b := by
    obtain ⟨a, b, hab, hpaired⟩ :=
      hfull.hasFullyPairedSubinterval
    refine ⟨a, b, ?_⟩
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, hab, ?_⟩
    rw [show relIcc (Finset.univ : Finset (Fin (m + 1))) a b =
        Finset.Icc a b by
      ext i
      simp [relIcc]]
    exact hpaired
  have hselected :=
    selectRel_isRelFullyPaired κ
      (Finset.univ : Finset (Fin (m + 1))) hcand
  have hselectedIcc :
      Finset.Icc (selectRel κ Finset.univ hcand).1
          (selectRel κ Finset.univ hcand).2 =
        (Finset.univ : Finset (Fin (m + 1))) := by
    apply hprimitive
    · exact hselected.le
    · rw [← show relIcc (Finset.univ : Finset (Fin (m + 1)))
          (selectRel κ Finset.univ hcand).1
          (selectRel κ Finset.univ hcand).2 =
        Finset.Icc (selectRel κ Finset.univ hcand).1
          (selectRel κ Finset.univ hcand).2 by
        ext i
        simp [relIcc]]
      exact hselected.isFullyPairedOn
  have hleft :
      (selectRel κ Finset.univ hcand).1 = 0 := by
    have hzero :
        (0 : Fin (m + 1)) ∈
          Finset.Icc (selectRel κ Finset.univ hcand).1
            (selectRel κ Finset.univ hcand).2 := by
      rw [hselectedIcc]
      exact Finset.mem_univ _
    rw [Finset.mem_Icc] at hzero
    exact le_antisymm hzero.1 (Fin.zero_le _)
  have hright :
      (selectRel κ Finset.univ hcand).2 = Fin.last m := by
    have hlast :
        Fin.last m ∈
          Finset.Icc (selectRel κ Finset.univ hcand).1
            (selectRel κ Finset.univ hcand).2 := by
      rw [hselectedIcc]
      exact Finset.mem_univ _
    rw [Finset.mem_Icc] at hlast
    exact le_antisymm (Fin.le_last _) hlast.2
  have hselectedPair :
      selectRel κ Finset.univ hcand = (0, Fin.last m) :=
    Prod.ext hleft hright
  unfold extract
  rw [extractAux_succ_pos m hcand, hselectedPair]
  have hempty :
      (Finset.univ : Finset (Fin (m + 1))) \
          relIcc Finset.univ (0 : Fin (m + 1)) (Fin.last m) =
        ∅ := by
    rw [show relIcc (Finset.univ : Finset (Fin (m + 1)))
        (0 : Fin (m + 1)) (Fin.last m) = Finset.univ by
      ext i
      simp [relIcc, Fin.le_last]]
    simp
  rw [hempty]
  have hnone :
      ¬∃ a b, IsRelFullyPaired κ
        (∅ : Finset (Fin (m + 1))) a b := by
    simp [IsRelFullyPaired]
  rw [extractAux_nil_of_no_candidate m hnone]

/-- Cardinality-generic form of
`extract_eq_singleton_whole_of_full_of_primitive`. -/
theorem extract_eq_singleton_whole_of_pos_full_primitive
    {n : ℕ} (hn : 0 < n) {κ : PartialPairing (Fin n)}
    (hfull : κ.IsFull) (hprimitive : IsPrimitive κ) :
    extract κ =
      [((⟨0, hn⟩ : Fin n),
        (⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ : Fin n))] := by
  cases n with
  | zero =>
      omega
  | succ m =>
      simpa [Fin.last] using
        (extract_eq_singleton_whole_of_full_of_primitive
          (m := m) hfull hprimitive)

/-- A primitive full pairing belongs to the non-concatenation class used by
the renormalization constant.  A fully paired proper prefix would itself be
a proper fully paired interval, contradicting primitivity. -/
theorem isNonSplit_of_full_of_primitive
    {q : ℕ} (hq : 1 ≤ q)
    {σ : PartialPairing (Fin (2 * q))}
    (hfull : σ.IsFull) (hprimitive : IsPrimitive σ) :
    IsNonSplit σ := by
  refine ⟨hfull, ?_⟩
  rintro ⟨p, _hpRange, hp, hpaired⟩
  let a : Fin (2 * q) := ⟨0, by omega⟩
  let b : Fin (2 * q) := ⟨p, by omega⟩
  have hprefix :
      Finset.Icc a b =
        Finset.univ.filter
          (fun i : Fin (2 * q) => i.val ≤ p) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (0 ≤ i.val ∧ i.val ≤ p ↔ i.val ≤ p)
    omega
  have hpairedIcc :
      IsFullyPairedOn σ
        (Finset.Icc a b) := by
    rw [hprefix]
    exact hpaired
  have hwhole :
      Finset.Icc a b =
        Finset.univ :=
    hprimitive a b (by
      change 0 ≤ b.val
      omega) hpairedIcc
  have hlast :
      (⟨2 * q - 1, by omega⟩ : Fin (2 * q)) ∈
        Finset.Icc a b := by
    rw [hwhole]
    exact Finset.mem_univ _
  have hle := (Finset.mem_Icc.mp hlast).2
  change 2 * q - 1 ≤ p at hle
  omega

/-- The extraction endpoint signature of a primitive full pairing is the
single whole-interval signature. -/
theorem reductionEndpointSignature_eq_primitive
    {q : ℕ} (hq : 1 ≤ q)
    {σ : PartialPairing (Fin (2 * q))}
    (hfull : σ.IsFull) (hprimitive : IsPrimitive σ) :
    reductionEndpointSignature σ =
      ({⟨0, by omega⟩},
        {⟨2 * q - 1, by omega⟩}) := by
  unfold reductionEndpointSignature leftEndpoints rightEndpoints
  rw [extract_eq_singleton_whole_of_pos_full_primitive
    (n := 2 * q) (by omega) hfull hprimitive]
  simp

/-! ## Identification with the primitive kernel -/

/-- The terminal whole-interval difference factor is `1`, so the closed
`J` integrand of a primitive full pairing is exactly the Proposition 4.1
integrand with the free Green function in every chain slot. -/
theorem detJintegrand_eq_primitiveIntegrand_of_full_of_primitive
    (ρ : SmoothCutoff) (ε : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (σ : PartialPairing (Fin (2 * q)))
    (hfull : σ.IsFull) (hprimitive : IsPrimitive σ)
    (x : Fin (2 * q) → T4) :
    detJintegrand ρ ε q σ x =
      primitiveIntegrand ρ ε q hq
        (fun _ => greenFn) σ x := by
  have hextract :
      extract σ =
        [((⟨0, by omega⟩ : Fin (2 * q)),
          (⟨2 * q - 1, by omega⟩ : Fin (2 * q)))] :=
    extract_eq_singleton_whole_of_pos_full_primitive
      (by omega) hfull hprimitive
  rw [detJintegrand, primitiveIntegrand,
    primitiveChainProduct, primitiveCovarianceProduct, hextract]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  have hnotmem :
      ∀ e : Fin (2 * q - 1),
        e.val ∉ [((⟨2 * q - 1, by omega⟩ : Fin (2 * q))).val] := by
    intro e he
    simp only [List.mem_singleton] at he
    have := e.isLt
    omega
  simp only [hnotmem, if_false]
  have hguard :
      ∀ e : Fin (2 * q - 1), e.val + 1 < 2 * q := by
    intro e
    have := e.isLt
    omega
  simp only [hguard, dif_pos]
  have hterminal :
      diffFactorJ x
          ((⟨0, by omega⟩ : Fin (2 * q)),
            (⟨2 * q - 1, by omega⟩ : Fin (2 * q))) = 1 := by
    unfold diffFactorJ
    simp only
    rw [dif_neg (by omega)]
  rw [hterminal, mul_one]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro e _
    rfl
  · rfl

/-- Summing `detJ` over the terminal primitive pairings is exactly the
primitive kernel (4.2), before translating the second endpoint to zero. -/
theorem sum_detJ_primitive_eq_primitiveKernel
    (ρ : SmoothCutoff) (lam ε : ℝ) (q : ℕ) (hq : 1 ≤ q)
    (z w : T4) :
    (∑ σ ∈ primitiveFullPairings q,
        detJ ρ lam ε q σ z w) =
      primitiveKernel ρ lam ε q hq
        (fun _ => greenFn) z w := by
  cases q with
  | zero =>
      omega
  | succ q =>
      unfold primitiveKernel
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      obtain ⟨hfull, hprimitive⟩ :=
        mem_primitiveFullPairings.mp hσ
      rw [detJ]
      apply congrArg
        (fun a : ℝ => lamEps lam ε ^ (2 * (q + 1)) * a)
      apply integral_congr_ae
      filter_upwards with v
      exact
        detJintegrand_eq_primitiveIntegrand_of_full_of_primitive
          ρ ε (q + 1) hq σ hfull hprimitive
            (primitiveAssemble (q + 1) hq z w v)

/-- Proposition 4.1 supplies the exact (4.3) majorant for the terminal
primitive sum in the R-322 reduction. -/
theorem sum_detJ_primitive_le_primitiveKernelMajorant
    (ρ : SmoothCutoff)
    {orderConstant supportConstant C lam ε : ℝ}
    {q : ℕ} (hq : 1 ≤ q)
    (hprop41 :
      Prop41BoundPredicate ρ lam ε q hq
        (fun _ => greenFn)
        orderConstant supportConstant C)
    (hreg :
      PrimitiveEstimateRegime q lam ε
        orderConstant supportConstant C)
    (hinput :
      IsAdmissiblePrimitiveInput q
        (fun _ => greenFn))
    (z : T4) :
    |∑ σ ∈ primitiveFullPairings q,
        detJ ρ lam ε q σ z 0| ≤
      primitiveKernelMajorant C lam ε
        supportConstant q z := by
  obtain ⟨_hmem, _hmemInserted, hbounds⟩ :=
    hprop41 hreg hinput
  rw [sum_detJ_primitive_eq_primitiveKernel
    ρ lam ε q hq z 0]
  simpa only [primitiveKernelDiff, sub_zero] using
    (hbounds z).1

end

end Anderson4D
