import Mathlib
import Anderson4D.Combinatorics.BinomialBounds

/-!
# Counting sequences with geometric-decay weights

Paper: L-5.13 — (5.55)/(5.56) — sequence counting

Formalization of **Lemma 5.13** of Deng–Shen (arXiv:2607.10105), PAPER_MAP node
**L-5.13**: the bounds (5.55) and (5.56), plus a variant of
(5.55) where an exception set of at most `B` consecutive-pair positions is
omitted from the product.

* `Anderson4D.sum_min_two_rpow_le` — paper **(5.55)**: for `θ > 0` there is
  `C = C(θ) ≥ 1` such that for all `m + 1 ≤ n`, summing over tuples
  `z : Fin (m+1) → Fin n` the products `∏ⱼ min 1 (2 ^ (−θ(z_j − z_{j+1})))`
  over consecutive pairs gives at most `C ^ n`.
* `Anderson4D.sum_min_two_rpow_skip_le` — (5.55) with the product restricted
  to `univ \ E` for an exception set `E` with `E.card ≤ B`; `C = C(θ, B)`.
* `Anderson4D.sum_min_ratio_pow_le` — paper **(5.56)**: for `n + 1` distinct
  dyadics `P_k = 2 ^ (e k)` (with `e` injective), summing over all maps
  `x : Fin (n+1) → Fin (n+1)` the products
  `∏ⱼ min 1 ((P_{x(j+1)} / P_{x(j)}) ^ θ)` gives at most `C ^ (n+1)`.
* `Anderson4D.sum_min_ratio_pow_skip_le_rect` — the rectangular, bounded-skip
  form used in Step 3 of Proposition 5.10, where the sequence may be longer
  than the family of distinct dyadic values.

**Representation choices.**  Tuples of length `m + 1` with the product over
`j : Fin m` via `Fin.castSucc`/`Fin.succ` replace the paper's length-`m`
tuples with `m - 1` consecutive pairs (avoiding truncated subtraction in the
index type).  The paper's `2 ^ (−θ(z_j − z_{j+1}))` has a real exponent, so it
is a **real power (`rpow`)** of an integer-valued difference; in (5.56) the
dyadics `2 ^ (e k)` are integer powers (`zpow`) and the outer exponent `θ`
is again `rpow`.
-/

namespace Anderson4D

open Finset

/-- Single-factor bound in the proof of (5.55): with `w = max 0 (a - b)`
(truncated `ℕ`-subtraction), `min 1 (2 ^ (−θ(a − b))) ≤ (2 ^ (−θ)) ^ w`. -/
private theorem min_rpow_le_pow (θ : ℝ) (a b : ℕ) :
    min 1 ((2 : ℝ) ^ (-(θ * ((a - b : ℤ) : ℝ))))
      ≤ ((2 : ℝ) ^ (-θ)) ^ (a - b) := by
  rcases le_or_gt b a with hba | hab
  · have hzk : (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) := by omega
    have hrw : (2 : ℝ) ^ (-(θ * ((a - b : ℤ) : ℝ)))
        = ((2 : ℝ) ^ (-θ)) ^ (a - b) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-θ)) (a - b),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [hzk]
      push_cast
      ring
    exact le_of_le_of_eq (min_le_right _ _) hrw
  · have h0 : a - b = 0 := by omega
    rw [h0, pow_zero]
    exact min_le_left _ _

/-- Two strictly monotone tuples `Fin k → ℕ` with the same image are equal. -/
private theorem strictMono_image_inj {k : ℕ} {f g : Fin k → ℕ}
    (hf : StrictMono f) (hg : StrictMono g)
    (h : Finset.univ.image f = Finset.univ.image g) : f = g := by
  have hcard : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ,
      Fintype.card_fin]
  have h1 := Finset.orderEmbOfFin_unique hcard
    (fun x => Finset.mem_image_of_mem f (Finset.mem_univ x)) hf
  have h2 := Finset.orderEmbOfFin_unique hcard
    (fun x => h ▸ Finset.mem_image_of_mem g (Finset.mem_univ x)) hg
  exact h1.trans h2.symm

/-- Geometric sum bound: for `0 ≤ r < 1`, `∑_{i<n} rⁱ ≤ (1 - r)⁻¹`. -/
private theorem geom_sum_le_inv_one_sub {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1)
    (n : ℕ) : ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  have h1r : 0 < 1 - r := by linarith
  have hkey : (∑ i ∈ Finset.range n, r ^ i) * (1 - r) = 1 - r ^ n := by
    have h := geom_sum_mul r n
    linear_combination -h
  rw [inv_eq_one_div, le_div_iff₀ h1r, hkey]
  have hrn : (0 : ℝ) ≤ r ^ n := pow_nonneg h0 n
  linarith

/-- Auxiliary for the counting step of (5.55): the weight
`if j ∈ E then n else w j` extended by zero to all of `ℕ`, so that prefix
sums are `Finset.range`-sums. -/
private def extWeight (m n : ℕ) (E : Finset (Fin m)) (w : Fin m → ℕ)
    (i : ℕ) : ℕ :=
  if h : i < m then (if (⟨i, h⟩ : Fin m) ∈ E then n else w ⟨i, h⟩) else 0

private theorem extWeight_fin (m n : ℕ) (E : Finset (Fin m)) (w : Fin m → ℕ)
    (j : Fin m) : extWeight m n E w j.val = if j ∈ E then n else w j := by
  simp [extWeight]

private theorem sum_extWeight_le (m n : ℕ) (E : Finset (Fin m)) (w : Fin m → ℕ)
    {t : ℕ} (ht : t ≤ m) :
    ∑ i ∈ Finset.range t, extWeight m n E w i
      ≤ ∑ j, (if j ∈ E then n else w j) := by
  calc ∑ i ∈ Finset.range t, extWeight m n E w i
      ≤ ∑ i ∈ Finset.range m, extWeight m n E w i :=
        Finset.sum_le_sum_of_subset (fun x hx => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) ht))
    _ = ∑ j, (if j ∈ E then n else w j) := by
        rw [← Fin.sum_univ_eq_sum_range (extWeight m n E w) m]
        exact Finset.sum_congr rfl fun j _ => extWeight_fin m n E w j

/-- Counting step of (5.55) (with exception set): the tuples
`z : Fin (m+1) → Fin n` whose consecutive drops `z_j - z_{j+1}` (truncated)
agree with `w` off `E` number at most `(n + m + ∑ v).choose (m+1)`, where
`v j = w j` off `E` and `v j = n` on `E`.  Proof: `Z_j = z_j + j + ∑_{i<j} v_i`
is strictly monotone with values in `[0, n + m + ∑ v)`, and `z ↦ image Z`
is injective into the `(m+1)`-subsets. -/
private theorem card_filter_drop_le (m n : ℕ) (E : Finset (Fin m))
    (w : Fin m → ℕ) :
    ((Finset.univ : Finset (Fin (m + 1) → Fin n)).filter fun z =>
        ∀ j : Fin m, j ∉ E → (z j.castSucc : ℕ) - (z j.succ : ℕ) = w j).card
      ≤ (n + m + ∑ j, (if j ∈ E then n else w j)).choose (m + 1) := by
  have hmono : ∀ y : Fin (m + 1) → Fin n,
      (∀ j : Fin m, j ∉ E → (y j.castSucc : ℕ) - (y j.succ : ℕ) = w j) →
      StrictMono (fun j : Fin (m + 1) =>
        (y j : ℕ) + j.val + ∑ i ∈ Finset.range j.val, extWeight m n E w i) := by
    intro y hy
    rw [Fin.strictMono_iff_lt_succ]
    intro j
    have hkey : (y j.castSucc : ℕ) ≤ (y j.succ : ℕ) + extWeight m n E w j.val := by
      rw [extWeight_fin]
      by_cases hj : j ∈ E
      · have h1 : (y j.castSucc : ℕ) < n := (y j.castSucc).isLt
        simp only [if_pos hj]
        omega
      · have h1 := hy j hj
        simp only [if_neg hj]
        omega
    simp only [Fin.val_castSucc, Fin.val_succ, Finset.sum_range_succ]
    omega
  have hcard :
      ((Finset.univ : Finset (Fin (m + 1) → Fin n)).filter fun z =>
          ∀ j : Fin m, j ∉ E → (z j.castSucc : ℕ) - (z j.succ : ℕ) = w j).card
        ≤ ((Finset.range (n + m + ∑ j, (if j ∈ E then n else w j))).powersetCard
            (m + 1)).card := by
    refine Finset.card_le_card_of_injOn
      (fun z => Finset.univ.image fun j : Fin (m + 1) =>
        (z j : ℕ) + j.val + ∑ i ∈ Finset.range j.val, extWeight m n E w i) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      constructor
      · intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨j, -, rfl⟩ := ht
        rw [Finset.mem_range]
        have h1 : (z j : ℕ) < n := (z j).isLt
        have h2 := sum_extWeight_le m n E w (Nat.lt_succ_iff.mp j.isLt)
        omega
      · rw [Finset.card_image_of_injective _ (hmono z hz.2).injective,
          Finset.card_univ, Fintype.card_fin]
    · intro z hz z' hz' himg
      rw [Finset.mem_coe, Finset.mem_filter] at hz hz'
      have hZ := strictMono_image_inj (hmono z hz.2) (hmono z' hz'.2) himg
      funext j
      have hj := congrFun hZ j
      have hval : (z j : ℕ) = (z' j : ℕ) := by omega
      exact Fin.ext hval
  refine hcard.trans (le_of_eq ?_)
  rw [Finset.card_powersetCard, Finset.card_range]

/-- The truncated drop vector `j ↦ max 0 (z_j − z_{j+1})` of a tuple, with
exceptional positions zeroed out; used to group the (5.55)-sum into fibers. -/
private def dropVec (m n : ℕ) (hn : 0 < n) (E : Finset (Fin m))
    (z : Fin (m + 1) → Fin n) : Fin m → Fin n := fun j =>
  if j ∈ E then ⟨0, hn⟩
  else ⟨(z j.castSucc : ℕ) - (z j.succ : ℕ),
    lt_of_le_of_lt (Nat.sub_le _ _) (z j.castSucc).isLt⟩

private theorem dropVec_val_of_not_mem (m n : ℕ) (hn : 0 < n)
    (E : Finset (Fin m)) (z : Fin (m + 1) → Fin n) (j : Fin m) (hj : j ∉ E) :
    (dropVec m n hn E z j : ℕ) = (z j.castSucc : ℕ) - (z j.succ : ℕ) := by
  simp [dropVec, hj]

private theorem dropVec_val_of_mem (m n : ℕ) (hn : 0 < n)
    (E : Finset (Fin m)) (z : Fin (m + 1) → Fin n) (j : Fin m) (hj : j ∈ E) :
    (dropVec m n hn E z j : ℕ) = 0 := by
  simp [dropVec, hj]

/-- Core estimate behind (5.55) and its skip variant: for `α = 2 ^ (θ/2)`
(abstracted through `hα2`) and any exception set `E` with `E.card ≤ B`,
the (5.55)-sum with the product restricted to `univ \ E` is at most
`(α ^ (B+1) · (α/(α-1))²) ^ n`. -/
private theorem sum_skip_core (θ α : ℝ) (hα : 1 < α)
    (hα2 : (2 : ℝ) ^ (-θ) = (α⁻¹) ^ 2) (B m n : ℕ) (hmn : m + 1 ≤ n)
    (E : Finset (Fin m)) (hE : E.card ≤ B) :
    ∑ z : Fin (m + 1) → Fin n, ∏ j ∈ Finset.univ \ E,
        min 1 ((2 : ℝ) ^ (-(θ * (((z j.castSucc : ℕ) - (z j.succ : ℕ) : ℤ) : ℝ))))
      ≤ (α ^ (B + 1) * (α / (α - 1)) ^ 2) ^ n := by
  have hn : 0 < n := by omega
  have hα0 : (0 : ℝ) < α := lt_trans one_pos hα
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hβ1 : 1 < α / (α - 1) := (one_lt_div hα1).mpr (by linarith)
  have hβ0 : (0 : ℝ) < α / (α - 1) := lt_trans one_pos hβ1
  have hr0 : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα0
  have hr1 : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have hrα : α * α⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hα0)
  -- Step 1: pointwise bound of each product by a power of `α⁻¹`
  have hprod : ∀ z : Fin (m + 1) → Fin n,
      (∏ j ∈ Finset.univ \ E,
        min 1 ((2 : ℝ) ^ (-(θ * (((z j.castSucc : ℕ) - (z j.succ : ℕ) : ℤ) : ℝ)))))
        ≤ α⁻¹ ^ (2 * ∑ j, (dropVec m n hn E z j : ℕ)) := by
    intro z
    have hsum_eq : ∑ j ∈ Finset.univ \ E, ((z j.castSucc : ℕ) - (z j.succ : ℕ))
        = ∑ j, (dropVec m n hn E z j : ℕ) := by
      rw [Finset.sum_congr rfl (fun j hj => (dropVec_val_of_not_mem m n hn E z j
        (Finset.mem_sdiff.mp hj).2).symm)]
      exact Finset.sum_subset Finset.sdiff_subset (fun j _ hj =>
        dropVec_val_of_mem m n hn E z j (by
          by_contra hnot
          exact hj (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hnot⟩)))
    calc ∏ j ∈ Finset.univ \ E,
        min 1 ((2 : ℝ) ^ (-(θ * (((z j.castSucc : ℕ) - (z j.succ : ℕ) : ℤ) : ℝ))))
        ≤ ∏ j ∈ Finset.univ \ E,
            (α⁻¹ ^ 2) ^ ((z j.castSucc : ℕ) - (z j.succ : ℕ)) := by
          refine Finset.prod_le_prod
            (fun j _ => le_min zero_le_one (Real.rpow_nonneg (by norm_num) _))
            (fun j _ => ?_)
          have h := min_rpow_le_pow θ (z j.castSucc : ℕ) (z j.succ : ℕ)
          rwa [hα2] at h
      _ = (α⁻¹ ^ 2) ^ (∑ j ∈ Finset.univ \ E,
            ((z j.castSucc : ℕ) - (z j.succ : ℕ))) :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ = α⁻¹ ^ (2 * ∑ j, (dropVec m n hn E z j : ℕ)) := by
          rw [hsum_eq, ← pow_mul]
  -- Step 2: geometric sum over the drop vectors
  have hsumu : ∑ u : Fin m → Fin n, α⁻¹ ^ (∑ j, (u j : ℕ))
      ≤ (α / (α - 1)) ^ m := by
    have hαne : α ≠ 0 := ne_of_gt hα0
    have h1r : 1 - α⁻¹ = (α - 1) / α := by field_simp
    have hβr : (1 - α⁻¹)⁻¹ = α / (α - 1) := by rw [h1r, inv_div]
    calc ∑ u : Fin m → Fin n, α⁻¹ ^ (∑ j, (u j : ℕ))
        = ∑ u : Fin m → Fin n, ∏ j, α⁻¹ ^ (u j : ℕ) :=
          Finset.sum_congr rfl fun u _ => (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ = ∏ _j : Fin m, ∑ v : Fin n, α⁻¹ ^ (v : ℕ) := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ ≤ ∏ _j : Fin m, (1 - α⁻¹)⁻¹ := by
          refine Finset.prod_le_prod
            (fun j _ => Finset.sum_nonneg fun v _ => pow_nonneg hr0.le _)
            (fun j _ => ?_)
          rw [Fin.sum_univ_eq_sum_range (fun i => α⁻¹ ^ i) n]
          exact geom_sum_le_inv_one_sub hr0.le hr1 n
      _ = (α / (α - 1)) ^ m := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hβr]
  -- Step 3: fiberwise decomposition and per-fiber counting
  calc ∑ z : Fin (m + 1) → Fin n, ∏ j ∈ Finset.univ \ E,
      min 1 ((2 : ℝ) ^ (-(θ * (((z j.castSucc : ℕ) - (z j.succ : ℕ) : ℤ) : ℝ))))
      ≤ ∑ z : Fin (m + 1) → Fin n,
          α⁻¹ ^ (2 * ∑ j, (dropVec m n hn E z j : ℕ)) :=
        Finset.sum_le_sum fun z _ => hprod z
    _ = ∑ u : Fin m → Fin n,
          ∑ z ∈ Finset.univ.filter (fun z => dropVec m n hn E z = u),
            α⁻¹ ^ (2 * ∑ j, (dropVec m n hn E z j : ℕ)) :=
        (Finset.sum_fiberwise_of_maps_to (fun z _ => Finset.mem_univ _) _).symm
    _ ≤ ∑ u : Fin m → Fin n,
          (α ^ (n - 1) * α ^ (E.card * n) * (α / (α - 1)) ^ (m + 1))
            * α⁻¹ ^ (∑ j, (u j : ℕ)) := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hconst : ∑ z ∈ Finset.univ.filter (fun z => dropVec m n hn E z = u),
            α⁻¹ ^ (2 * ∑ j, (dropVec m n hn E z j : ℕ))
            = ((Finset.univ.filter fun z => dropVec m n hn E z = u).card : ℝ)
              * α⁻¹ ^ (2 * ∑ j, (u j : ℕ)) := by
          rw [Finset.sum_congr rfl (fun z hz => by
            rw [(Finset.mem_filter.mp hz).2]), Finset.sum_const, nsmul_eq_mul]
        have hcard : ((Finset.univ.filter fun z => dropVec m n hn E z = u).card : ℝ)
            ≤ (((n + m + (E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ))).choose
                (m + 1) : ℕ) : ℝ) := by
          have hsub : (Finset.univ.filter fun z => dropVec m n hn E z = u)
              ⊆ Finset.univ.filter (fun z => ∀ j : Fin m, j ∉ E →
                  (z j.castSucc : ℕ) - (z j.succ : ℕ) = (u j : ℕ)) := by
            intro z hz
            rw [Finset.mem_filter] at hz ⊢
            refine ⟨Finset.mem_univ z, fun j hj => ?_⟩
            rw [← hz.2]
            exact (dropVec_val_of_not_mem m n hn E z j hj).symm
          have h2 := card_filter_drop_le m n E (fun j => (u j : ℕ))
          have h3 : ∑ j, (if j ∈ E then n else (u j : ℕ))
              = E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ) := by
            rw [Finset.sum_ite, Finset.filter_univ_mem, Finset.sum_const,
              smul_eq_mul, ← Finset.sdiff_eq_filter]
          rw [h3] at h2
          exact_mod_cast (Finset.card_le_card hsub).trans h2
        have hchoose : (((n + m + (E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ))).choose
              (m + 1) : ℕ) : ℝ)
            ≤ α ^ (n - 1) * α ^ (E.card * n) * α ^ (∑ j, (u j : ℕ))
              * (α / (α - 1)) ^ (m + 1) := by
          have hN : n + m + (E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ))
              = (n - 1 + E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ)) + (m + 1) := by
            omega
          have hs'le : ∑ j ∈ Finset.univ \ E, (u j : ℕ) ≤ ∑ j, (u j : ℕ) :=
            Finset.sum_le_sum_of_subset Finset.sdiff_subset
          calc (((n + m + (E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ))).choose
                (m + 1) : ℕ) : ℝ)
              = (((n - 1 + E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ)) + (m + 1)).choose
                  (n - 1 + E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ)) : ℕ) := by
                rw [hN, Nat.choose_symm_add]
            _ ≤ α ^ (n - 1 + E.card * n + ∑ j ∈ Finset.univ \ E, (u j : ℕ))
                  * (α / (α - 1)) ^ (m + 1) := choose_le_pow_mul_pow α hα _ _
            _ = α ^ (n - 1) * α ^ (E.card * n)
                  * α ^ (∑ j ∈ Finset.univ \ E, (u j : ℕ))
                  * (α / (α - 1)) ^ (m + 1) := by rw [pow_add, pow_add]
            _ ≤ α ^ (n - 1) * α ^ (E.card * n) * α ^ (∑ j, (u j : ℕ))
                  * (α / (α - 1)) ^ (m + 1) := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                  (pow_le_pow_right₀ (le_of_lt hα) hs'le)
                  (mul_pos (pow_pos hα0 _) (pow_pos hα0 _)).le) (pow_pos hβ0 _).le
        rw [hconst]
        calc ((Finset.univ.filter fun z => dropVec m n hn E z = u).card : ℝ)
              * α⁻¹ ^ (2 * ∑ j, (u j : ℕ))
            ≤ (α ^ (n - 1) * α ^ (E.card * n) * α ^ (∑ j, (u j : ℕ))
                * (α / (α - 1)) ^ (m + 1)) * α⁻¹ ^ (2 * ∑ j, (u j : ℕ)) :=
              mul_le_mul_of_nonneg_right (hcard.trans hchoose) (pow_nonneg hr0.le _)
          _ = (α ^ (n - 1) * α ^ (E.card * n) * (α / (α - 1)) ^ (m + 1))
                * α⁻¹ ^ (∑ j, (u j : ℕ)) * (α * α⁻¹) ^ (∑ j, (u j : ℕ)) := by
              rw [mul_pow, two_mul, pow_add]; ring
          _ = (α ^ (n - 1) * α ^ (E.card * n) * (α / (α - 1)) ^ (m + 1))
                * α⁻¹ ^ (∑ j, (u j : ℕ)) := by rw [hrα, one_pow, mul_one]
    _ = (α ^ (n - 1) * α ^ (E.card * n) * (α / (α - 1)) ^ (m + 1))
          * ∑ u : Fin m → Fin n, α⁻¹ ^ (∑ j, (u j : ℕ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (α ^ (n - 1) * α ^ (E.card * n) * (α / (α - 1)) ^ (m + 1))
          * (α / (α - 1)) ^ m :=
        mul_le_mul_of_nonneg_left hsumu
          (mul_pos (mul_pos (pow_pos hα0 _) (pow_pos hα0 _)) (pow_pos hβ0 _)).le
    _ ≤ (α ^ (B + 1) * (α / (α - 1)) ^ 2) ^ n := by
        have he1 : (n - 1) + E.card * n ≤ (B + 1) * n := by
          calc (n - 1) + E.card * n ≤ n + B * n :=
              Nat.add_le_add (Nat.sub_le n 1) (Nat.mul_le_mul_right n hE)
            _ = (B + 1) * n := by ring
        have he2 : (m + 1) + m ≤ 2 * n := by omega
        calc (α ^ (n - 1) * α ^ (E.card * n) * (α / (α - 1)) ^ (m + 1))
              * (α / (α - 1)) ^ m
            = α ^ ((n - 1) + E.card * n) * (α / (α - 1)) ^ ((m + 1) + m) := by
              rw [pow_add, pow_add]; ring
          _ ≤ α ^ ((B + 1) * n) * (α / (α - 1)) ^ (2 * n) :=
              mul_le_mul (pow_le_pow_right₀ (le_of_lt hα) he1)
                (pow_le_pow_right₀ (le_of_lt hβ1) he2)
                (pow_pos hβ0 _).le (pow_pos hα0 _).le
          _ = (α ^ (B + 1) * (α / (α - 1)) ^ 2) ^ n := by
              rw [mul_pow, ← pow_mul, ← pow_mul]

/-- The base `α = 2 ^ (θ/2)` used in the proof of (5.55): it exceeds `1` and
satisfies `2 ^ (-θ) = (α⁻¹)²`. -/
private theorem exists_alpha (θ : ℝ) (hθ : 0 < θ) :
    ∃ α : ℝ, 1 < α ∧ (2 : ℝ) ^ (-θ) = α⁻¹ ^ 2 := by
  refine ⟨(2 : ℝ) ^ (θ / 2), ?_, ?_⟩
  · rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by rw [Real.rpow_zero]]
    exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith)
  · rw [inv_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (θ / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num

/-- **Paper (5.55), Lemma 5.13 (node L-5.13).**  For `θ > 0` there is
`C = C(θ) ≥ 1` such that for all `m, n` with `m + 1 ≤ n`,
`∑_{z : Fin (m+1) → Fin n} ∏_{j} min 1 (2 ^ (−θ(z_j − z_{j+1}))) ≤ C ^ n`,
the product running over the `m` consecutive pairs and the difference
`z_j − z_{j+1}` being integer-valued (the power is `rpow`). -/
theorem sum_min_two_rpow_le (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m n : ℕ, m + 1 ≤ n →
      ∑ z : Fin (m + 1) → Fin n, ∏ j : Fin m,
        min 1 ((2 : ℝ) ^ (-(θ * (((z j.castSucc : ℕ) - (z j.succ : ℕ) : ℤ) : ℝ))))
      ≤ C ^ n := by
  obtain ⟨α, hα, hα2⟩ := exists_alpha θ hθ
  have hβ1 : 1 < α / (α - 1) := (one_lt_div (by linarith)).mpr (by linarith)
  refine ⟨α * (α / (α - 1)) ^ 2, ?_, ?_⟩
  · have h2 : 1 ≤ (α / (α - 1)) ^ 2 := one_le_pow₀ hβ1.le
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ α * (α / (α - 1)) ^ 2 := mul_le_mul hα.le h2 zero_le_one (by linarith)
  · intro m n hmn
    have h := sum_skip_core θ α hα hα2 0 m n hmn ∅ (by simp)
    simpa [Finset.sdiff_empty, pow_one] using h

/-- **Skip variant of paper (5.55), Lemma 5.13.**  The (5.55)-bound with the
product over consecutive pairs outside an exception set `E` of size at most
`B`; the constant depends only on `θ` and `B`. -/
theorem sum_min_two_rpow_skip_le (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m n : ℕ, m + 1 ≤ n → ∀ E : Finset (Fin m), E.card ≤ B →
      ∑ z : Fin (m + 1) → Fin n, ∏ j ∈ Finset.univ \ E,
        min 1 ((2 : ℝ) ^ (-(θ * (((z j.castSucc : ℕ) - (z j.succ : ℕ) : ℤ) : ℝ))))
      ≤ C ^ n := by
  obtain ⟨α, hα, hα2⟩ := exists_alpha θ hθ
  have hβ1 : 1 < α / (α - 1) := (one_lt_div (by linarith)).mpr (by linarith)
  refine ⟨α ^ (B + 1) * (α / (α - 1)) ^ 2, ?_, ?_⟩
  · have h1 : 1 ≤ α ^ (B + 1) := one_le_pow₀ hα.le
    have h2 : 1 ≤ (α / (α - 1)) ^ 2 := one_le_pow₀ hβ1.le
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ α ^ (B + 1) * (α / (α - 1)) ^ 2 :=
        mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)
  · intro m n hmn E hE
    exact sum_skip_core θ α hα hα2 B m n hmn E hE

/-- The rank of `a` among the values of `e`: the number of indices with
strictly smaller `e`-value.  Used to replace distinct dyadic exponents by
their order ranks in the reduction of (5.56) to (5.55). -/
private def rank {ν : ℕ} (e : Fin ν → ℤ) (a : Fin ν) : ℕ :=
  (Finset.univ.filter fun b => e b < e a).card

private theorem rank_lt {ν : ℕ} (e : Fin ν → ℤ) (a : Fin ν) : rank e a < ν := by
  have hne : a ∉ Finset.univ.filter fun b => e b < e a := by simp
  have hlt : (Finset.univ.filter fun b => e b < e a).card
      < (Finset.univ : Finset (Fin ν)).card :=
    Finset.card_lt_card (Finset.ssubset_univ_iff.mpr
      (fun h => hne (by rw [h]; exact Finset.mem_univ a)))
  simpa [rank] using hlt

private theorem rank_lt_rank {ν : ℕ} {e : Fin ν → ℤ} {a b : Fin ν}
    (hab : e a < e b) : rank e a < rank e b := by
  have hsub : insert a (Finset.univ.filter fun c => e c < e a)
      ⊆ Finset.univ.filter fun c => e c < e b := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_trans (Finset.mem_filter.mp hc).2 hab⟩
  have hnotmem : a ∉ Finset.univ.filter fun c => e c < e a := by simp
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnotmem] at h1
  exact h1

/-- Distinct integers have gaps at least `1`: the rank difference is at most
the value difference.  This is the order-isomorphism step in the reduction of
(5.56) to (5.55). -/
private theorem rank_sub_rank_le {ν : ℕ} {e : Fin ν → ℤ}
    (he : Function.Injective e) {a b : Fin ν} (hab : e a < e b) :
    (rank e b : ℤ) - (rank e a : ℤ) ≤ e b - e a := by
  have hsub : (Finset.univ.filter fun c => e c < e a)
      ⊆ Finset.univ.filter fun c => e c < e b := fun c hc =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_trans (Finset.mem_filter.mp hc).2 hab⟩
  have hcard : ((Finset.univ.filter fun c => e c < e b) \
      (Finset.univ.filter fun c => e c < e a)).card = rank e b - rank e a := by
    rw [Finset.card_sdiff_of_subset hsub]; rfl
  have hinj : ((Finset.univ.filter fun c => e c < e b) \
      (Finset.univ.filter fun c => e c < e a)).card
      ≤ (Finset.Ico (e a) (e b)).card := by
    refine Finset.card_le_card_of_injOn e ?_ ?_
    · intro c hc
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_filter] at hc
      rw [Finset.mem_coe, Finset.mem_Ico]
      refine ⟨?_, hc.1.2⟩
      exact le_of_not_gt fun hlt => hc.2 ⟨Finset.mem_univ _, hlt⟩
    · exact fun x _ y _ hxy => he hxy
  have hIco : (Finset.Ico (e a) (e b)).card = (e b - e a).toNat :=
    Int.card_Ico _ _
  have hr : rank e a ≤ rank e b := (rank_lt_rank hab).le
  omega

private theorem rank_injective {ν : ℕ} {e : Fin ν → ℤ}
    (he : Function.Injective e) :
    Function.Injective fun a => (⟨rank e a, rank_lt e a⟩ : Fin ν) := by
  intro a b hab
  by_contra hne
  have hene : e a ≠ e b := fun h => hne (he h)
  have heq : rank e a = rank e b := by simpa using congrArg Fin.val hab
  rcases lt_or_gt_of_ne hene with h | h
  · exact absurd heq (Nat.ne_of_lt (rank_lt_rank h))
  · exact absurd heq (Nat.ne_of_gt (rank_lt_rank h))

/-- Single-factor bound in the reduction of (5.56) to (5.55): the dyadic
ratio factor is dominated by the (5.55)-factor of the rank differences. -/
private theorem min_ratio_le_min_rank (θ : ℝ) (hθ : 0 < θ) {ν : ℕ}
    {e : Fin ν → ℤ} (he : Function.Injective e) (p q : Fin ν) :
    min 1 (((2 : ℝ) ^ e q / (2 : ℝ) ^ e p) ^ θ)
      ≤ min 1 ((2 : ℝ) ^ (-(θ * (((rank e p : ℤ) - (rank e q : ℤ) : ℤ) : ℝ)))) := by
  rcases le_or_gt (e p) (e q) with hpq | hqp
  · -- non-decreasing pair: the right-hand minimum is `1`
    have hrk : rank e p ≤ rank e q := by
      rcases eq_or_lt_of_le hpq with heq | hlt
      · rw [he heq]
      · exact (rank_lt_rank hlt).le
    have hd : (((rank e p : ℤ) - (rank e q : ℤ) : ℤ) : ℝ) ≤ 0 := by
      have h : ((rank e p : ℕ) : ℝ) ≤ ((rank e q : ℕ) : ℝ) := Nat.cast_le.mpr hrk
      push_cast
      linarith
    have hexp : (0 : ℝ) ≤ -(θ * (((rank e p : ℤ) - (rank e q : ℤ) : ℤ) : ℝ)) := by
      nlinarith
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (-(θ * (((rank e p : ℤ) - (rank e q : ℤ) : ℤ) : ℝ))) := by
      rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
    rw [min_eq_left h1]
    exact min_le_left _ _
  · -- strictly decreasing pair: compare the exponents through the rank gap
    have hgap := rank_sub_rank_le he hqp
    refine min_le_min (le_refl 1) ?_
    have hzr : (2 : ℝ) ^ e q / (2 : ℝ) ^ e p = (2 : ℝ) ^ ((e q - e p : ℤ) : ℝ) := by
      rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_intCast]
    have hexp : ((e q - e p : ℤ) : ℝ) * θ
        ≤ -(θ * (((rank e p : ℤ) - (rank e q : ℤ) : ℤ) : ℝ)) := by
      have hgR : (((rank e p : ℤ) - (rank e q : ℤ) : ℤ) : ℝ) ≤ ((e p - e q : ℤ) : ℝ) :=
        Int.cast_le.mpr hgap
      push_cast at hgR ⊢
      nlinarith
    calc ((2 : ℝ) ^ e q / (2 : ℝ) ^ e p) ^ θ
        = (2 : ℝ) ^ (((e q - e p : ℤ) : ℝ) * θ) := by
          rw [hzr, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (2 : ℝ) ^ (-(θ * (((rank e p : ℤ) - (rank e q : ℤ) : ℤ) : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two hexp

/--
**Rectangular bounded-skip form of paper (5.56), Lemma 5.13.**

The paper applies (5.56) to a sequence whose length is the total
multiplicity, while its entries belong to a possibly smaller finite family
of distinct dyadic values.  This theorem records that exact reindexing:
if `ν ≤ m + 1`, an injective exponent family `e : Fin ν → ℤ` may be ranked
inside `Fin (m + 1)`, and the resulting sum is bounded by `C ^ (m + 1)`.
The product may omit a set `E` of at most `B` adjacent pairs.
-/
theorem sum_min_ratio_pow_skip_le_rect (θ : ℝ) (hθ : 0 < θ) (B : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (m ν : ℕ) (e : Fin ν → ℤ), ν ≤ m + 1 → Function.Injective e →
        ∀ E : Finset (Fin m), E.card ≤ B →
          ∑ x : Fin (m + 1) → Fin ν, ∏ j ∈ Finset.univ \ E,
            min 1 (((2 : ℝ) ^ e (x j.succ) /
              (2 : ℝ) ^ e (x j.castSucc)) ^ θ)
          ≤ C ^ (m + 1) := by
  obtain ⟨C, hC1, hC⟩ := sum_min_two_rpow_skip_le θ hθ B
  refine ⟨C, hC1, ?_⟩
  intro m ν e hν he E hE
  let r : Fin ν → Fin (m + 1) := fun a =>
    ⟨rank e a, lt_of_lt_of_le (rank_lt e a) hν⟩
  have hrinj : Function.Injective r := by
    intro a b hab
    have hrank : rank e a = rank e b := by
      simpa [r] using congrArg Fin.val hab
    apply rank_injective he
    apply Fin.ext
    exact hrank
  let φ : (Fin (m + 1) → Fin ν) → (Fin (m + 1) → Fin (m + 1)) :=
    fun x => r ∘ x
  have hφinj : Function.Injective φ := by
    intro x y hxy
    funext i
    exact hrinj (congrFun hxy i)
  let w : (Fin (m + 1) → Fin (m + 1)) → Fin m → ℝ := fun y j =>
    min 1 ((2 : ℝ) ^ (-(θ *
      (((y j.castSucc : ℕ) - (y j.succ : ℕ) : ℤ) : ℝ))))
  calc
    ∑ x : Fin (m + 1) → Fin ν, ∏ j ∈ Finset.univ \ E,
          min 1 (((2 : ℝ) ^ e (x j.succ) /
            (2 : ℝ) ^ e (x j.castSucc)) ^ θ)
        ≤ ∑ x : Fin (m + 1) → Fin ν, ∏ j ∈ Finset.univ \ E, w (φ x) j := by
          refine Finset.sum_le_sum fun x _ =>
            Finset.prod_le_prod
              (fun j _ => le_min zero_le_one
                (Real.rpow_nonneg
                  (div_nonneg (zpow_nonneg (by norm_num) _)
                    (zpow_nonneg (by norm_num) _)) _))
              (fun j _ => ?_)
          simpa [w, φ, r] using
            min_ratio_le_min_rank θ hθ he (x j.castSucc) (x j.succ)
    _ = ∑ y ∈ Finset.univ.image φ, ∏ j ∈ Finset.univ \ E, w y j :=
        (Finset.sum_image
          (f := fun y : Fin (m + 1) → Fin (m + 1) =>
            ∏ j ∈ Finset.univ \ E, w y j)
          (fun x _ y _ h => hφinj h)).symm
    _ ≤ ∑ y : Fin (m + 1) → Fin (m + 1), ∏ j ∈ Finset.univ \ E, w y j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun y _ _ => Finset.prod_nonneg fun j _ =>
            le_min zero_le_one (Real.rpow_nonneg (by norm_num) _))
    _ ≤ C ^ (m + 1) := by
      simpa [w] using hC m (m + 1) (le_refl _) E hE

/-- **Paper (5.56), Lemma 5.13 (node L-5.13).**  For `θ > 0` there is
`C = C(θ) ≥ 1` with the following property: for every `n` and every injective
exponent family `e : Fin (n+1) → ℤ` — encoding `n + 1` distinct dyadics
`P_k = 2 ^ (e k)` — summing over all maps `x : Fin (n+1) → Fin (n+1)` the
products `∏ⱼ min 1 ((P_{x(j+1)} / P_{x(j)}) ^ θ)` over the `n` consecutive
pairs gives at most `C ^ (n+1)`.  The dyadics are integer powers (`zpow`) of
`2`; the outer exponent `θ` is a real power (`rpow`).  Proof: replace the
`e`-values by their ranks (`rank_sub_rank_le`) and compose with the injection
`x ↦ rank ∘ x` into the (5.55)-sum. -/
theorem sum_min_ratio_pow_le (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (e : Fin (n + 1) → ℤ), Function.Injective e →
      ∑ x : Fin (n + 1) → Fin (n + 1), ∏ j : Fin n,
        min 1 (((2 : ℝ) ^ e (x j.succ) / (2 : ℝ) ^ e (x j.castSucc)) ^ θ)
      ≤ C ^ (n + 1) := by
  obtain ⟨C, hC1, hC⟩ := sum_min_two_rpow_le θ hθ
  refine ⟨C, hC1, ?_⟩
  intro n e he
  have hRinj : Function.Injective
      (fun a : Fin (n + 1) => (⟨rank e a, rank_lt e a⟩ : Fin (n + 1))) :=
    rank_injective he
  have hφinj : Function.Injective (fun x : Fin (n + 1) → Fin (n + 1) =>
      (fun a : Fin (n + 1) => (⟨rank e a, rank_lt e a⟩ : Fin (n + 1))) ∘ x) := by
    intro x y hxy
    funext i
    exact hRinj (congrFun hxy i)
  calc ∑ x : Fin (n + 1) → Fin (n + 1), ∏ j : Fin n,
        min 1 (((2 : ℝ) ^ e (x j.succ) / (2 : ℝ) ^ e (x j.castSucc)) ^ θ)
      ≤ ∑ x : Fin (n + 1) → Fin (n + 1), ∏ j : Fin n,
          min 1 ((2 : ℝ) ^ (-(θ *
            (((((fun a : Fin (n + 1) => (⟨rank e a, rank_lt e a⟩ : Fin (n + 1))) ∘ x)
                j.castSucc : ℕ)
              - (((fun a : Fin (n + 1) => (⟨rank e a, rank_lt e a⟩ : Fin (n + 1))) ∘ x)
                j.succ : ℕ) : ℤ) : ℝ)))) := by
        refine Finset.sum_le_sum fun x _ => Finset.prod_le_prod
          (fun j _ => le_min zero_le_one (Real.rpow_nonneg
            (div_nonneg (zpow_nonneg (by norm_num) _) (zpow_nonneg (by norm_num) _)) _))
          (fun j _ => ?_)
        exact min_ratio_le_min_rank θ hθ he (x j.castSucc) (x j.succ)
    _ = ∑ y ∈ Finset.univ.image (fun x : Fin (n + 1) → Fin (n + 1) =>
            (fun a : Fin (n + 1) => (⟨rank e a, rank_lt e a⟩ : Fin (n + 1))) ∘ x),
          ∏ j : Fin n,
            min 1 ((2 : ℝ) ^ (-(θ * (((y j.castSucc : ℕ) - (y j.succ : ℕ) : ℤ) : ℝ)))) :=
        (Finset.sum_image
          (f := fun y : Fin (n + 1) → Fin (n + 1) => ∏ j : Fin n,
            min 1 ((2 : ℝ) ^ (-(θ * (((y j.castSucc : ℕ) - (y j.succ : ℕ) : ℤ) : ℝ)))))
          (fun x _ y _ h => hφinj h)).symm
    _ ≤ ∑ z : Fin (n + 1) → Fin (n + 1), ∏ j : Fin n,
          min 1 ((2 : ℝ) ^ (-(θ * (((z j.castSucc : ℕ) - (z j.succ : ℕ) : ℤ) : ℝ)))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun y _ _ => Finset.prod_nonneg fun j _ =>
            le_min zero_le_one (Real.rpow_nonneg (by norm_num) _))
    _ ≤ C ^ (n + 1) := hC n (n + 1) (le_refl _)

/-- **Paper (5.56), Lemma 5.13 — sorted form.**  The bound of
`sum_min_ratio_pow_le` for strictly increasing exponent families. -/
theorem sum_min_ratio_pow_le_of_strictMono (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (e : Fin (n + 1) → ℤ), StrictMono e →
      ∑ x : Fin (n + 1) → Fin (n + 1), ∏ j : Fin n,
        min 1 (((2 : ℝ) ^ e (x j.succ) / (2 : ℝ) ^ e (x j.castSucc)) ^ θ)
      ≤ C ^ (n + 1) := by
  obtain ⟨C, hC1, hC⟩ := sum_min_ratio_pow_le θ hθ
  exact ⟨C, hC1, fun n e he => hC n e he.injective⟩

end Anderson4D
