import Anderson4D.Probability.ComplexNoiseIsserlis
import Anderson4D.Combinatorics.Pairing

/-!
# Regrouping complex Wick expansions

This file proves the finite algebraic bridge from the real/imaginary
expansion in `complexNoiseWickPairingSum` to one recursive full-pairing sum
whose contractions are complex covariances.  The recursion pairs the first
label with one remaining label and removes both, so every labeled full
pairing occurs exactly once.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open MeasureTheory ProbabilityTheory Complex NoiseModel
open scoped BigOperators

/-! ## A scalar-generic full-pairing recursion -/

/-- Full-pairing sum on a finite vector.  At each step the first label is
paired with `j.succ`, and both labels are removed. -/
def finWickPairing {α R : Type*} [CommSemiring R]
    (C : α → α → R) : (n : ℕ) → (Fin n → α) → R
  | 0, _ => 1
  | 1, _ => 0
  | n + 2, v =>
      ∑ j : Fin (n + 1),
        C (v 0) (v j.succ) *
          finWickPairing C n
            (fun i => v (j.succAbove i).succ)

@[simp]
theorem finWickPairing_zero {α R : Type*} [CommSemiring R]
    (C : α → α → R) (v : Fin 0 → α) :
    finWickPairing C 0 v = 1 := by
  rw [finWickPairing]

@[simp]
theorem finWickPairing_one {α R : Type*} [CommSemiring R]
    (C : α → α → R) (v : Fin 1 → α) :
    finWickPairing C 1 v = 0 := by
  rw [finWickPairing]

@[simp]
theorem finWickPairing_add_two {α R : Type*} [CommSemiring R]
    (C : α → α → R) (n : ℕ) (v : Fin (n + 2) → α) :
    finWickPairing C (n + 2) v =
      ∑ j : Fin (n + 1),
        C (v 0) (v j.succ) *
          finWickPairing C n
            (fun i => v (j.succAbove i).succ) := by
  rw [finWickPairing]

/-- Pulling every vertex label through a map is the same as pulling the
edge kernel back through that map. -/
theorem finWickPairing_comp {α β R : Type*} [CommSemiring R]
    (C : α → α → R) (f : β → α) (n : ℕ) (v : Fin n → β) :
    finWickPairing C n (fun i => f (v i)) =
      finWickPairing (fun x y => C (f x) (f y)) n v := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp
  | one =>
      simp
  | more n ih _ihSucc =>
      rw [finWickPairing_add_two, finWickPairing_add_two]
      apply Fintype.sum_congr
      intro j
      congr 1
      exact ih (fun i => v (j.succAbove i).succ)

/-! ## Explicit labeled full pairings -/

/-- A recursively labeled full pairing.  For `n + 2` vertices, the first
vertex chooses its partner in `Fin (n + 1)`, and the tail is a full
pairing of the remaining `n` relabeled vertices. -/
def LabeledFullPairing : ℕ → Type
  | 0 => PUnit
  | 1 => Empty
  | n + 2 => Fin (n + 1) × LabeledFullPairing n

/-- Constructor equivalence for a nonempty labeled full pairing. -/
def labeledFullPairingAddTwoEquiv (n : ℕ) :
    (Fin (n + 1) × LabeledFullPairing n) ≃
      LabeledFullPairing (n + 2) where
  toFun p := p
  invFun p := p
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem labeledFullPairingAddTwoEquiv_apply
    (n : ℕ) (p : Fin (n + 1) × LabeledFullPairing n) :
    labeledFullPairingAddTwoEquiv n p = p := rfl

instance labeledFullPairingFinite (n : ℕ) :
    Finite (LabeledFullPairing n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      unfold LabeledFullPairing
      infer_instance
  | one =>
      unfold LabeledFullPairing
      infer_instance
  | more n ih _ihSucc =>
      letI := ih
      unfold LabeledFullPairing
      infer_instance

noncomputable instance labeledFullPairingFintype (n : ℕ) :
    Fintype (LabeledFullPairing n) :=
  Fintype.ofFinite _

/-- The edge list represented by a recursively labeled full pairing.
Every vertex occurs in exactly one edge by construction. -/
def labeledFullPairingEdges :
    (n : ℕ) → LabeledFullPairing n → List (Fin n × Fin n)
  | 0, _ => []
  | 1, p => nomatch p
  | n + 2, p =>
      (0, p.1.succ) ::
        (labeledFullPairingEdges n p.2).map
          (fun e =>
            ((p.1.succAbove e.1).succ,
              (p.1.succAbove e.2).succ))

/-- Product of edge contractions attached to one labeled full pairing. -/
def labeledFullPairingProduct {α R : Type*} [CommMonoid R]
    (C : α → α → R) :
    (n : ℕ) → LabeledFullPairing n → (Fin n → α) → R
  | n, p, v =>
      ((labeledFullPairingEdges n p).map
        (fun e => C (v e.1) (v e.2))).prod

@[simp]
theorem labeledFullPairingProduct_zero
    {α R : Type*} [CommMonoid R] (C : α → α → R)
    (p : LabeledFullPairing 0) (v : Fin 0 → α) :
    labeledFullPairingProduct C 0 p v = 1 := by
  rfl

@[simp]
theorem labeledFullPairingProduct_add_two
    {α R : Type*} [CommMonoid R] (C : α → α → R)
    (n : ℕ) (p : LabeledFullPairing (n + 2))
    (v : Fin (n + 2) → α) :
    labeledFullPairingProduct C (n + 2) p v =
      C (v 0) (v p.1.succ) *
        labeledFullPairingProduct C n p.2
          (fun i => v (p.1.succAbove i).succ) := by
  simp [labeledFullPairingProduct, labeledFullPairingEdges,
    List.map_map, Function.comp_def]

/-- A literal single sum over labeled full pairings, each summand being
the product of the contractions on its edge list. -/
def fullPairingCovarianceSum {α R : Type*} [CommSemiring R]
    (C : α → α → R) (n : ℕ) (v : Fin n → α) : R :=
  ∑ p : LabeledFullPairing n,
    labeledFullPairingProduct C n p v

/-- The explicit full-pairing sum and the head-partner recursion are
equal.  Thus the recursive algebra used below has no hidden multiplicity. -/
theorem fullPairingCovarianceSum_eq_finWickPairing
    {α R : Type*} [CommSemiring R]
    (C : α → α → R) (n : ℕ) (v : Fin n → α) :
    fullPairingCovarianceSum C n v =
      finWickPairing C n v := by
  induction n using Nat.twoStepInduction with
  | zero =>
      let e : PUnit ≃ LabeledFullPairing 0 := Equiv.refl _
      unfold fullPairingCovarianceSum
      calc
        (∑ p : LabeledFullPairing 0,
            labeledFullPairingProduct C 0 p v) =
            ∑ p : PUnit,
              labeledFullPairingProduct C 0 (e p) v := by
          symm
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = 1 := by simp
  | one =>
      let e : Empty ≃ LabeledFullPairing 1 := Equiv.refl _
      unfold fullPairingCovarianceSum
      calc
        (∑ p : LabeledFullPairing 1,
            labeledFullPairingProduct C 1 p v) =
            ∑ p : Empty,
              labeledFullPairingProduct C 1 (e p) v := by
          symm
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = 0 := by simp
  | more n ih _ihSucc =>
      unfold fullPairingCovarianceSum
      let e :
          (Fin (n + 1) × LabeledFullPairing n) ≃
            LabeledFullPairing (n + 2) :=
        labeledFullPairingAddTwoEquiv n
      calc
        (∑ p : LabeledFullPairing (n + 2),
            labeledFullPairingProduct C (n + 2) p v) =
            ∑ p : Fin (n + 1) × LabeledFullPairing n,
              labeledFullPairingProduct C (n + 2) (e p) v := by
          symm
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = ∑ j : Fin (n + 1),
              C (v 0) (v j.succ) *
                finWickPairing C n
                  (fun i => v (j.succAbove i).succ) := by
          rw [Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro j
          simp only [e, labeledFullPairingAddTwoEquiv_apply,
            labeledFullPairingProduct_add_two]
          rw [← Finset.mul_sum]
          exact congrArg (C (v 0) (v j.succ) * ·)
            (ih (fun i => v (j.succAbove i).succ))
        _ = finWickPairing C (n + 2) v := by
          rw [finWickPairing_add_two]

/-! ## Cross-single interface -/

/-- Product of cross covariances indexed by a bijection between the
single sets of two partial pairings.  This is the exact indexing shape
used by `deterministicMomentPairingSum`. -/
def crossSinglesEquivCovarianceProduct
    {ιp ιm R : Type*}
    [Fintype ιp] [DecidableEq ιp]
    [Fintype ιm] [DecidableEq ιm]
    [CommMonoid R]
    (κp : PartialPairing ιp) (κm : PartialPairing ιm)
    (C : ↥κp.singles → ↥κm.singles → R)
    (π : κp.singles ≃ κm.singles) : R :=
  ∏ i, C i (π i)

/-- Sum over cross-single bijections.  Consumers of the deterministic
moment decomposition can use this without quotienting or reindexing its
existing `κp.singles ≃ κm.singles` parameter. -/
def crossSinglesEquivCovarianceSum
    {ιp ιm R : Type*}
    [Fintype ιp] [DecidableEq ιp]
    [Fintype ιm] [DecidableEq ιm]
    [CommSemiring R]
    (κp : PartialPairing ιp) (κm : PartialPairing ιm)
    (C : ↥κp.singles → ↥κm.singles → R) : R :=
  ∑ π : κp.singles ≃ κm.singles,
    crossSinglesEquivCovarianceProduct κp κm C π

private theorem eraseIdx_ofFn_removeNth {α : Type*} {n : ℕ}
    (v : Fin (n + 1) → α) (j : Fin (n + 1)) :
    (List.ofFn v).eraseIdx j = List.ofFn (Fin.removeNth j v) := by
  induction n with
  | zero =>
      fin_cases j
      simp
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [List.ofFn_succ]
        simp only [Fin.val_zero, List.eraseIdx_cons_zero]
        congr 1
      · rw [List.ofFn_succ]
        simp only [Fin.val_succ, List.eraseIdx_cons_succ]
        rw [ih]
        rw [List.ofFn_succ]
        congr 1
        exact congrArg List.ofFn (by
          funext i
          simp [Fin.removeNth])

/-- The vector recursion is the existing real `wickPairingSum`. -/
theorem finWickPairing_real_eq_wickPairingSum
    {α : Type*} (C : α → α → ℝ) (n : ℕ) (v : Fin n → α) :
    finWickPairing C n v =
      wickPairingSum (fun i j => C (v i) (v j)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp
  | one =>
      rw [finWickPairing_one]
      exact (wickPairingSum_odd 0 _).symm
  | more n ih _ihSucc =>
      rw [finWickPairing_add_two]
      unfold wickPairingSum
      have hofn :
          List.ofFn (id : Fin (n + 2) → Fin (n + 2)) =
            0 :: List.ofFn (fun i : Fin (n + 1) => i.succ) := by
        rw [List.ofFn_succ]
        rfl
      rw [hofn, wickPairingList_cons]
      let e : Fin (n + 1) ≃
          Fin (List.ofFn (fun i : Fin (n + 1) => i.succ)).length :=
        finCongr (by simp)
      refine Fintype.sum_equiv e _ _ ?_
      intro j
      have hget :
          (List.ofFn (fun i : Fin (n + 1) => i.succ)).get (e j) =
            j.succ := by
        rw [List.get_ofFn]
        simp [e]
      have heval : (e j).val = j.val := by
        simp [e]
      rw [hget, heval, eraseIdx_ofFn_removeNth]
      congr 1
      have herase :
          List.ofFn
              (Fin.removeNth j
                (fun i : Fin (n + 1) => i.succ)) =
            List.ofFn
              (fun i : Fin n => (j.succAbove i).succ) := by
        apply congrArg List.ofFn
        funext i
        rfl
      rw [herase]
      rw [show
        List.ofFn (fun i : Fin n => (j.succAbove i).succ) =
          (List.ofFn id).map
            (fun i : Fin n => (j.succAbove i).succ) by
        rw [List.map_ofFn]
        rfl]
      rw [wickPairingList_map]
      exact ih (fun i => v (j.succAbove i).succ)

/-! ## Complexification and regrouping -/

/-- Scalar attached to a real/imaginary choice. -/
def complexChoiceCoefficient (b : Bool) : ℂ :=
  if b then I else 1

/-- Bilinear complexification of a covariance on real/imaginary labels. -/
def complexifiedCovariance {α : Type*}
    (C : (α × Bool) → (α × Bool) → ℝ) (x y : α) : ℂ :=
  ∑ b : Bool, ∑ c : Bool,
    complexChoiceCoefficient b * complexChoiceCoefficient c *
      (C (x, b) (y, c) : ℂ)

/-- Split a Boolean assignment into the choice at the head, the choice at
the selected partner, and the choices at all remaining positions. -/
def pairChoiceEquiv {n : ℕ} (j : Fin (n + 1)) :
    Bool × (Bool × (Fin n → Bool)) ≃ (Fin (n + 2) → Bool) :=
  ((Equiv.refl Bool).prodCongr
      (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) j)).trans
    (Fin.consEquiv (fun _ : Fin (n + 2) => Bool))

@[simp]
theorem pairChoiceEquiv_zero {n : ℕ} (j : Fin (n + 1))
    (b c : Bool) (τ : Fin n → Bool) :
    pairChoiceEquiv j (b, c, τ) 0 = b := by
  simp [pairChoiceEquiv]

@[simp]
theorem pairChoiceEquiv_partner {n : ℕ} (j : Fin (n + 1))
    (b c : Bool) (τ : Fin n → Bool) :
    pairChoiceEquiv j (b, c, τ) j.succ = c := by
  simp [pairChoiceEquiv]

@[simp]
theorem pairChoiceEquiv_remaining {n : ℕ} (j : Fin (n + 1))
    (b c : Bool) (τ : Fin n → Bool) (i : Fin n) :
    pairChoiceEquiv j (b, c, τ) (j.succAbove i).succ = τ i := by
  simp [pairChoiceEquiv]

/-- The coefficient of a split assignment factors over the selected pair
and the remaining positions. -/
theorem complexCoordinateCoefficient_pairChoiceEquiv
    {n : ℕ} (j : Fin (n + 1)) (b c : Bool) (τ : Fin n → Bool) :
    complexCoordinateCoefficient (pairChoiceEquiv j (b, c, τ)) =
      complexChoiceCoefficient b * complexChoiceCoefficient c *
        complexCoordinateCoefficient τ := by
  unfold complexCoordinateCoefficient
  rw [Fin.prod_univ_succ]
  rw [Fin.prod_univ_succAbove
    (fun i : Fin (n + 1) =>
      if pairChoiceEquiv j (b, c, τ) i.succ then I else 1) j]
  cases b
  · cases c
    · simp [complexChoiceCoefficient]
    · simp [complexChoiceCoefficient]
  · cases c
    · simp [complexChoiceCoefficient]
    · simp [complexChoiceCoefficient]
      ring_nf
      simp [Complex.I_sq]

/-- Regrouping theorem: choosing real/imaginary coordinates globally and
then summing real full pairings equals one complex full-pairing recursion
with the bilinearly complexified covariance. -/
theorem complexCoordinateExpansion_eq_finWickPairing
    {α : Type*} (C : (α × Bool) → (α × Bool) → ℝ)
    (n : ℕ) (v : Fin n → α) :
    (∑ σ : Fin n → Bool,
      complexCoordinateCoefficient σ *
        ((finWickPairing C n (fun i => (v i, σ i)) : ℝ) : ℂ)) =
      finWickPairing (complexifiedCovariance C) n v := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [complexCoordinateCoefficient]
  | one =>
      simp
  | more n ih _ihSucc =>
      rw [finWickPairing_add_two]
      simp_rw [finWickPairing_add_two
        (C := C) (n := n)]
      simp_rw [Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro j
      let e := pairChoiceEquiv j
      calc
        (∑ σ : Fin (n + 2) → Bool,
            complexCoordinateCoefficient σ *
              ((C (v 0, σ 0) (v j.succ, σ j.succ) : ℂ) *
                ((finWickPairing C n
                  (fun i =>
                    (v (j.succAbove i).succ,
                      σ (j.succAbove i).succ)) : ℝ) : ℂ))) =
            ∑ p : Bool × (Bool × (Fin n → Bool)),
              complexCoordinateCoefficient (e p) *
                ((C (v 0, e p 0) (v j.succ, e p j.succ) : ℂ) *
                  ((finWickPairing C n
                    (fun i =>
                      (v (j.succAbove i).succ,
                        e p (j.succAbove i).succ)) : ℝ) : ℂ)) := by
          symm
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = ∑ b : Bool, ∑ c : Bool, ∑ τ : Fin n → Bool,
              (complexChoiceCoefficient b *
                  complexChoiceCoefficient c *
                  complexCoordinateCoefficient τ) *
                ((C (v 0, b) (v j.succ, c) : ℂ) *
                  ((finWickPairing C n
                    (fun i =>
                      (v (j.succAbove i).succ, τ i)) : ℝ) : ℂ)) := by
          simp only [Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro b
          apply Fintype.sum_congr
          intro c
          apply Fintype.sum_congr
          intro τ
          simp [e,
            complexCoordinateCoefficient_pairChoiceEquiv]
        _ = (∑ b : Bool, ∑ c : Bool,
              complexChoiceCoefficient b *
                complexChoiceCoefficient c *
                (C (v 0, b) (v j.succ, c) : ℂ)) *
            (∑ τ : Fin n → Bool,
              complexCoordinateCoefficient τ *
                ((finWickPairing C n
                  (fun i =>
                    (v (j.succAbove i).succ, τ i)) : ℝ) : ℂ)) := by
          calc
            (∑ b : Bool, ∑ c : Bool, ∑ τ : Fin n → Bool,
                (complexChoiceCoefficient b *
                    complexChoiceCoefficient c *
                    complexCoordinateCoefficient τ) *
                  ((C (v 0, b) (v j.succ, c) : ℂ) *
                    ((finWickPairing C n
                      (fun i =>
                        (v (j.succAbove i).succ, τ i)) : ℝ) : ℂ))) =
                ∑ b : Bool, ∑ τ : Fin n → Bool, ∑ c : Bool,
                  (complexChoiceCoefficient b *
                      complexChoiceCoefficient c *
                      complexCoordinateCoefficient τ) *
                    ((C (v 0, b) (v j.succ, c) : ℂ) *
                      ((finWickPairing C n
                        (fun i =>
                          (v (j.succAbove i).succ, τ i)) : ℝ) : ℂ)) := by
              apply Fintype.sum_congr
              intro b
              rw [Finset.sum_comm]
            _ = ∑ τ : Fin n → Bool, ∑ b : Bool, ∑ c : Bool,
                  (complexChoiceCoefficient b *
                      complexChoiceCoefficient c *
                      complexCoordinateCoefficient τ) *
                    ((C (v 0, b) (v j.succ, c) : ℂ) *
                      ((finWickPairing C n
                        (fun i =>
                          (v (j.succAbove i).succ, τ i)) : ℝ) : ℂ)) := by
              rw [Finset.sum_comm]
            _ = _ := by
              rw [Finset.mul_sum]
              apply Fintype.sum_congr
              intro τ
              symm
              rw [Finset.sum_mul]
              apply Fintype.sum_congr
              intro b
              rw [Finset.sum_mul]
              apply Fintype.sum_congr
              intro c
              ring
        _ = complexifiedCovariance C (v 0) (v j.succ) *
            finWickPairing (complexifiedCovariance C) n
              (fun i => v (j.succAbove i).succ) := by
          rw [ih (fun i => v (j.succAbove i).succ)]
          rfl

/-! ## Arbitrary finite linear combinations -/

/-- Weight of one global assignment of a summand to every position. -/
def finiteAssignmentWeight {α β : Type*} {n : ℕ}
    (w : α → β → ℂ) (v : Fin n → α) (σ : Fin n → β) : ℂ :=
  ∏ i, w (v i) (σ i)

/-- Split an arbitrary finite assignment at the head and its selected
partner. -/
def pairAssignmentEquiv {β : Type*} {n : ℕ} (j : Fin (n + 1)) :
    β × (β × (Fin n → β)) ≃ (Fin (n + 2) → β) :=
  ((Equiv.refl β).prodCongr
      (Fin.insertNthEquiv (fun _ : Fin (n + 1) => β) j)).trans
    (Fin.consEquiv (fun _ : Fin (n + 2) => β))

@[simp]
theorem pairAssignmentEquiv_zero {β : Type*} {n : ℕ}
    (j : Fin (n + 1)) (b c : β) (τ : Fin n → β) :
    pairAssignmentEquiv j (b, c, τ) 0 = b := by
  simp [pairAssignmentEquiv]

@[simp]
theorem pairAssignmentEquiv_partner {β : Type*} {n : ℕ}
    (j : Fin (n + 1)) (b c : β) (τ : Fin n → β) :
    pairAssignmentEquiv j (b, c, τ) j.succ = c := by
  simp [pairAssignmentEquiv]

@[simp]
theorem pairAssignmentEquiv_remaining {β : Type*} {n : ℕ}
    (j : Fin (n + 1)) (b c : β) (τ : Fin n → β) (i : Fin n) :
    pairAssignmentEquiv j (b, c, τ)
        (j.succAbove i).succ = τ i := by
  simp [pairAssignmentEquiv]

/-- Assignment weights factor over the selected pair and the remaining
positions. -/
theorem finiteAssignmentWeight_pairAssignmentEquiv
    {α β : Type*} {n : ℕ} (w : α → β → ℂ)
    (v : Fin (n + 2) → α) (j : Fin (n + 1))
    (b c : β) (τ : Fin n → β) :
    finiteAssignmentWeight w v
        (pairAssignmentEquiv j (b, c, τ)) =
      w (v 0) b * w (v j.succ) c *
        finiteAssignmentWeight w
          (fun i => v (j.succAbove i).succ) τ := by
  unfold finiteAssignmentWeight
  rw [Fin.prod_univ_succ]
  rw [Fin.prod_univ_succAbove
    (fun i : Fin (n + 1) =>
      w (v i.succ)
        (pairAssignmentEquiv j (b, c, τ) i.succ)) j]
  simp [mul_assoc]

/-- Finite multilinearity of the full-pairing sum.  Expanding one finite
linear combination at every vertex and then summing full pairings equals a
single full-pairing sum of the contracted covariance matrix. -/
theorem finiteAssignmentExpansion_eq_finWickPairing
    {α β : Type*} [Fintype β]
    (C : (α × β) → (α × β) → ℂ)
    (w : α → β → ℂ) (n : ℕ) (v : Fin n → α) :
    (∑ σ : Fin n → β,
      finiteAssignmentWeight w v σ *
        finWickPairing C n (fun i => (v i, σ i))) =
      finWickPairing
        (fun x y =>
          ∑ b : β, ∑ c : β,
            w x b * w y c * C (x, b) (y, c))
        n v := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [finiteAssignmentWeight]
  | one =>
      simp
  | more n ih _ihSucc =>
      rw [finWickPairing_add_two]
      simp_rw [finWickPairing_add_two
        (C := C) (n := n)]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro j
      let e := pairAssignmentEquiv (β := β) j
      calc
        (∑ σ : Fin (n + 2) → β,
            finiteAssignmentWeight w v σ *
              (C (v 0, σ 0) (v j.succ, σ j.succ) *
                finWickPairing C n
                  (fun i =>
                    (v (j.succAbove i).succ,
                      σ (j.succAbove i).succ)))) =
            ∑ p : β × (β × (Fin n → β)),
              finiteAssignmentWeight w v (e p) *
                (C (v 0, e p 0) (v j.succ, e p j.succ) *
                  finWickPairing C n
                    (fun i =>
                      (v (j.succAbove i).succ,
                        e p (j.succAbove i).succ))) := by
          symm
          exact Fintype.sum_equiv e _ _ (fun _ => rfl)
        _ = ∑ b : β, ∑ c : β, ∑ τ : Fin n → β,
              (w (v 0) b * w (v j.succ) c *
                  finiteAssignmentWeight w
                    (fun i => v (j.succAbove i).succ) τ) *
                (C (v 0, b) (v j.succ, c) *
                  finWickPairing C n
                    (fun i =>
                      (v (j.succAbove i).succ, τ i))) := by
          simp only [Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro b
          apply Fintype.sum_congr
          intro c
          apply Fintype.sum_congr
          intro τ
          simp [e, finiteAssignmentWeight_pairAssignmentEquiv]
        _ = (∑ b : β, ∑ c : β,
              w (v 0) b * w (v j.succ) c *
                C (v 0, b) (v j.succ, c)) *
            (∑ τ : Fin n → β,
              finiteAssignmentWeight w
                  (fun i => v (j.succAbove i).succ) τ *
                finWickPairing C n
                  (fun i =>
                    (v (j.succAbove i).succ, τ i))) := by
          calc
            (∑ b : β, ∑ c : β, ∑ τ : Fin n → β,
                (w (v 0) b * w (v j.succ) c *
                    finiteAssignmentWeight w
                      (fun i => v (j.succAbove i).succ) τ) *
                  (C (v 0, b) (v j.succ, c) *
                    finWickPairing C n
                      (fun i =>
                        (v (j.succAbove i).succ, τ i)))) =
                ∑ b : β, ∑ τ : Fin n → β, ∑ c : β,
                  (w (v 0) b * w (v j.succ) c *
                      finiteAssignmentWeight w
                        (fun i => v (j.succAbove i).succ) τ) *
                    (C (v 0, b) (v j.succ, c) *
                      finWickPairing C n
                        (fun i =>
                          (v (j.succAbove i).succ, τ i))) := by
              apply Fintype.sum_congr
              intro b
              rw [Finset.sum_comm]
            _ = ∑ τ : Fin n → β, ∑ b : β, ∑ c : β,
                  (w (v 0) b * w (v j.succ) c *
                      finiteAssignmentWeight w
                        (fun i => v (j.succAbove i).succ) τ) *
                    (C (v 0, b) (v j.succ, c) *
                      finWickPairing C n
                        (fun i =>
                          (v (j.succAbove i).succ, τ i))) := by
              rw [Finset.sum_comm]
            _ = _ := by
              rw [Finset.mul_sum]
              apply Fintype.sum_congr
              intro τ
              symm
              rw [Finset.sum_mul]
              apply Fintype.sum_congr
              intro b
              rw [Finset.sum_mul]
              apply Fintype.sum_congr
              intro c
              ring
        _ = (∑ b : β, ∑ c : β,
              w (v 0) b * w (v j.succ) c *
                C (v 0, b) (v j.succ, c)) *
            finWickPairing
              (fun x y =>
                ∑ b : β, ∑ c : β,
                  w x b * w y c * C (x, b) (y, c))
              n (fun i => v (j.succAbove i).succ) := by
          rw [ih (fun i => v (j.succAbove i).succ)]

/-! ## Fourier-noise specialization -/

namespace NoiseModel

variable (M : NoiseModel)

/-- The complex Fourier Wick expansion is one full-pairing recursion with
the complexified real-coordinate covariance. -/
theorem complexNoiseWickPairingSum_eq_complexifiedFullPairing
    {n : ℕ} (k : Fin n → Z4) :
    M.complexNoiseWickPairingSum k =
      finWickPairing
        (complexifiedCovariance
          (fun p q : Fin n × Bool =>
            M.coordinateCovariance k p q))
        n id := by
  unfold complexNoiseWickPairingSum selectedCoordinateCovariance
  calc
    (∑ σ : Fin n → Bool,
        complexCoordinateCoefficient σ *
          (wickPairingSum
            (fun i j =>
              M.coordinateCovariance k (i, σ i) (j, σ j)) : ℂ)) =
        ∑ σ : Fin n → Bool,
          complexCoordinateCoefficient σ *
            ((finWickPairing
              (fun p q : Fin n × Bool =>
                M.coordinateCovariance k p q)
              n (fun i => (i, σ i)) : ℝ) : ℂ) := by
      apply Fintype.sum_congr
      intro σ
      rw [finWickPairing_real_eq_wickPairingSum]
    _ = finWickPairing
          (complexifiedCovariance
            (fun p q : Fin n × Bool =>
              M.coordinateCovariance k p q))
          n id :=
      complexCoordinateExpansion_eq_finWickPairing
        (fun p q : Fin n × Bool =>
          M.coordinateCovariance k p q) n id

private theorem coordinateCovariance_twoModes
    {n : ℕ} (k : Fin n → Z4) (i j : Fin n) (b c : Bool) :
    M.coordinateCovariance k (i, b) (j, c) =
      M.coordinateCovariance (twoModes (k i) (k j))
        (0, b) (1, c) := by
  rw [M.coordinateCovariance_eq_integral,
    M.coordinateCovariance_eq_integral]
  cases b <;> cases c <;>
    rfl

/-- The bilinear complexification of the real/imaginary covariance matrix
is the exact Fourier contraction. -/
theorem complexified_coordinateCovariance_eq_fourier
    {n : ℕ} (k : Fin n → Z4) (i j : Fin n) :
    complexifiedCovariance
        (fun p q : Fin n × Bool =>
          M.coordinateCovariance k p q) i j =
      if k i = -k j then 1 else 0 := by
  have htwo :=
    M.complexNoiseWickPairingSum_eq_complexifiedFullPairing
      (twoModes (k i) (k j))
  rw [M.complexNoiseWickPairingSum_two] at htwo
  have htwo' :
      complexifiedCovariance
          (fun p q : Fin 2 × Bool =>
            M.coordinateCovariance (twoModes (k i) (k j)) p q)
          0 1 =
        if k i = -k j then 1 else 0 := by
    simpa [finWickPairing] using htwo.symm
  rw [← htwo']
  unfold complexifiedCovariance
  apply Fintype.sum_congr
  intro b
  apply Fintype.sum_congr
  intro c
  rw [show
    (fun p q : Fin n × Bool =>
      M.coordinateCovariance k p q) (i, b) (j, c) =
      (fun p q : Fin 2 × Bool =>
        M.coordinateCovariance (twoModes (k i) (k j)) p q)
        (0, b) (1, c) from
    M.coordinateCovariance_twoModes k i j b c]

/-- Single-layer labeled full-pairing sum for Fourier contractions. -/
def fourierFullPairingSum {n : ℕ} (k : Fin n → Z4) : ℂ :=
  fullPairingCovarianceSum
    (fun i j => if k i = -k j then 1 else 0) n id

/-- Expanded presentation: sum over one finite type of labeled full
pairings, with each term the product of its Kronecker contractions. -/
theorem fourierFullPairingSum_eq_sum_edgeProducts
    {n : ℕ} (k : Fin n → Z4) :
    fourierFullPairingSum k =
      ∑ p : LabeledFullPairing n,
        labeledFullPairingProduct
          (fun i j => if k i = -k j then 1 else 0)
          n p id := by
  rfl

/-- The real/imaginary expansion is exactly the single-layer Fourier
full-pairing sum. -/
theorem complexNoiseWickPairingSum_eq_fourierFullPairingSum
    {n : ℕ} (k : Fin n → Z4) :
    M.complexNoiseWickPairingSum k =
      fourierFullPairingSum k := by
  rw [M.complexNoiseWickPairingSum_eq_complexifiedFullPairing]
  unfold fourierFullPairingSum
  rw [fullPairingCovarianceSum_eq_finWickPairing]
  congr 1
  funext i j
  exact M.complexified_coordinateCovariance_eq_fourier k i j

/-- Direct complex Wick theorem in the Fourier contraction presentation. -/
theorem integral_g_product_eq_fourierFullPairingSum
    {n : ℕ} (k : Fin n → Z4) :
    (∫ ω, ∏ i, M.g (k i) ω
        ∂(volume : Measure M.Ω)) =
      fourierFullPairingSum k := by
  rw [M.integral_g_product_eq_complexNoiseWickPairingSum,
    M.complexNoiseWickPairingSum_eq_fourierFullPairingSum]

/-! ## Covariance form for finite complex linear combinations -/

/-- The bilinear covariance (without conjugation) of two members of a
finite family of Fourier-noise linear combinations. -/
def finiteNoiseCombinationCovariance {n : ℕ}
    (s : Finset Z4) (a : Fin n → Z4 → ℂ) (i j : Fin n) : ℂ :=
  ∫ ω, M.finiteNoiseCombination s (a i) ω *
      M.finiteNoiseCombination s (a j) ω
      ∂(volume : Measure M.Ω)

/-- One full-pairing sum whose edge weights are the covariances of the
finite complex linear combinations. -/
def finiteCombinationCovarianceFullPairingSum {n : ℕ}
    (s : Finset Z4) (a : Fin n → Z4 → ℂ) : ℂ :=
  fullPairingCovarianceSum
    (M.finiteNoiseCombinationCovariance s a) n id

/-- The covariance of two finite combinations is the finite double
Fourier contraction sum, written over the support subtype. -/
theorem finiteNoiseCombinationCovariance_eq_sum {n : ℕ}
    (s : Finset Z4) (a : Fin n → Z4 → ℂ) (i j : Fin n) :
    M.finiteNoiseCombinationCovariance s a i j =
      ∑ k : ↥s, ∑ l : ↥s,
        a i k * a j l *
          (if (k : Z4) = -(l : Z4) then 1 else 0) := by
  rw [finiteNoiseCombinationCovariance,
    M.integral_finiteNoiseCombination_mul]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_attach]
  simp

/-- Regrouping for arbitrary finite complex linear combinations: the
mode-assignment expansion is exactly one full-pairing covariance sum. -/
theorem finiteCombinationWickPairingSum_eq_covarianceFullPairingSum
    {n : ℕ} (s : Finset Z4) (a : Fin n → Z4 → ℂ) :
    M.finiteCombinationWickPairingSum s a =
      M.finiteCombinationCovarianceFullPairingSum s a := by
  let C : (Fin n × ↥s) → (Fin n × ↥s) → ℂ :=
    fun p q =>
      if (p.2 : Z4) = -(q.2 : Z4) then 1 else 0
  have hmulti :=
    finiteAssignmentExpansion_eq_finWickPairing
      C (fun i (k : ↥s) => a i k) n id
  have hleft :
      (∑ modes : Fin n → ↥s,
          finiteAssignmentWeight
              (fun i (k : ↥s) => a i k) id modes *
            finWickPairing C n
              (fun i => (id i, modes i))) =
        M.finiteCombinationWickPairingSum s a := by
    unfold finiteCombinationWickPairingSum
    apply Fintype.sum_congr
    intro modes
    rw [M.complexNoiseWickPairingSum_eq_fourierFullPairingSum]
    unfold finiteAssignmentWeight fourierFullPairingSum
    congr 1
    rw [fullPairingCovarianceSum_eq_finWickPairing]
    simpa only [C, Function.comp_apply, id_eq] using
      finWickPairing_comp C
        (fun i : Fin n => (i, modes i)) n id
  rw [hleft] at hmulti
  rw [hmulti]
  unfold finiteCombinationCovarianceFullPairingSum
  rw [fullPairingCovarianceSum_eq_finWickPairing]
  congr 1
  funext i j
  rw [M.finiteNoiseCombinationCovariance_eq_sum]

/-- High-order Isserlis formula for finite complex linear combinations,
in covariance full-pairing form. -/
theorem integral_finiteNoiseCombination_product_eq_covarianceFullPairingSum
    {n : ℕ} (s : Finset Z4) (a : Fin n → Z4 → ℂ) :
    (∫ ω, ∏ i, M.finiteNoiseCombination s (a i) ω
        ∂(volume : Measure M.Ω)) =
      M.finiteCombinationCovarianceFullPairingSum s a := by
  rw [M.integral_finiteNoiseCombination_product_eq_wick,
    M.finiteCombinationWickPairingSum_eq_covarianceFullPairingSum]

end NoiseModel

end

end Anderson4D
