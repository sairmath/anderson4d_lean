import Anderson4D.Probability.ComplexWickRegroup
import Anderson4D.Probability.PartialPairingWick
import Anderson4D.Probability.WickOrthogonality

/-!
# Reindexing cross Wick contractions by finite equivalences

The recursive list contraction used by the generic Wick theorem is the same
finite sum as the paper's bijection-between-single-sets representation.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

open scoped BigOperators

/-- The product attached to a bijection between the positions of two lists. -/
def listEquivCovarianceProduct
    {ι R : Type*} [CommMonoid R]
    (C : ι → ι → R) (xs ys : List ι)
    (e : Fin xs.length ≃ Fin ys.length) : R :=
  ∏ i, C (xs.get i) (ys.get (e i))

/-- Sum of covariance products over all bijections between list positions. -/
def listEquivCovarianceSum
    {ι R : Type*} [CommSemiring R]
    (C : ι → ι → R) (xs ys : List ι) : R :=
  ∑ e : Fin xs.length ≃ Fin ys.length,
    listEquivCovarianceProduct C xs ys e

namespace CrossWickEquiv

private def consFinEquiv
    {ι : Type*} {n : ℕ} (ys : List ι) (j : Fin ys.length)
    (e : Fin n ≃ Fin (ys.eraseIdx j).length) :
    Fin (n + 1) ≃ Fin ys.length :=
  Equiv.ofBijective
    (Fin.cases j fun i =>
      (PartialPairing.eraseIdxOrderIso ys j (e i)).1)
    (by
      constructor
      · intro a b hab
        by_cases ha : a = 0
        · subst a
          by_cases hb : b = 0
          · exact hb.symm
          · obtain ⟨b, rfl⟩ := Fin.eq_succ_of_ne_zero hb
            change
              j =
                (PartialPairing.eraseIdxOrderIso ys j (e b)).1
              at hab
            exact False.elim
              ((PartialPairing.eraseIdxOrderIso ys j (e b)).2 hab.symm)
        · obtain ⟨a, rfl⟩ := Fin.eq_succ_of_ne_zero ha
          by_cases hb : b = 0
          · subst b
            change
              (PartialPairing.eraseIdxOrderIso ys j (e a)).1 =
                j
              at hab
            exact False.elim
              ((PartialPairing.eraseIdxOrderIso ys j (e a)).2 hab)
          · obtain ⟨b, rfl⟩ := Fin.eq_succ_of_ne_zero hb
            change
              (PartialPairing.eraseIdxOrderIso ys j (e a)).1 =
                (PartialPairing.eraseIdxOrderIso ys j (e b)).1
              at hab
            have he : e a = e b := by
              apply (PartialPairing.eraseIdxOrderIso ys j).injective
              exact Subtype.ext hab
            exact congrArg Fin.succ (e.injective he)
      · intro k
        by_cases hk : k = j
        · exact ⟨0, hk.symm⟩
        · let i : Fin (ys.eraseIdx j).length :=
            (PartialPairing.eraseIdxOrderIso ys j).symm ⟨k, hk⟩
          refine ⟨(e.symm i).succ, ?_⟩
          change
            (PartialPairing.eraseIdxOrderIso ys j
              (e (e.symm i))).1 = k
          rw [e.apply_symm_apply]
          exact congrArg Subtype.val
            ((PartialPairing.eraseIdxOrderIso ys j).apply_symm_apply
              ⟨k, hk⟩))

private def tailFinEquiv
    {ι : Type*} {n : ℕ} (ys : List ι)
    (e : Fin (n + 1) ≃ Fin ys.length) :
    Fin n ≃ Fin (ys.eraseIdx (e 0)).length :=
  let e' : Fin n ≃ {k : Fin ys.length // k ≠ e 0} :=
    Equiv.ofBijective
      (fun i => ⟨e i.succ, fun h => Fin.succ_ne_zero i (e.injective h)⟩)
      (by
        constructor
        · intro i j h
          apply Fin.succ_injective
          apply e.injective
          exact congrArg Subtype.val h
        · intro k
          have hne : e.symm k.1 ≠ 0 := by
            intro h
            apply k.2
            rw [← e.apply_symm_apply k.1, h]
          obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero hne
          refine ⟨i, ?_⟩
          apply Subtype.ext
          simpa only [hi] using e.apply_symm_apply k.1)
  e'.trans
    (EquivLike.toEquiv
      (PartialPairing.eraseIdxOrderIso ys (e 0))).symm

/-- Splitting a bijection by the image of the new head position. -/
private def finEquivConsDecomposition
    {ι : Type*} (n : ℕ) (ys : List ι) :
    (Fin (n + 1) ≃ Fin ys.length) ≃
      Σ j : Fin ys.length, Fin n ≃ Fin (ys.eraseIdx j).length where
  toFun e := ⟨e 0, tailFinEquiv ys e⟩
  invFun p := consFinEquiv ys p.1 p.2
  left_inv := by
    intro e
    apply Equiv.ext
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · change
        (PartialPairing.eraseIdxOrderIso ys (e 0)
          (tailFinEquiv ys e i)).1 = e i.succ
      simp [tailFinEquiv]
  right_inv := by
    rintro ⟨j, e⟩
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply Equiv.ext
    intro i
    change
      (tailFinEquiv ys (consFinEquiv ys j e)) i = e i
    simp [tailFinEquiv, consFinEquiv]
    exact
      (EquivLike.toEquiv
        (PartialPairing.eraseIdxOrderIso ys j)).symm_apply_apply (e i)

private theorem listEquivCovarianceProduct_cons
    {ι R : Type*} [CommMonoid R]
    (C : ι → ι → R) (x : ι) (xs ys : List ι)
    (j : Fin ys.length)
    (e : Fin xs.length ≃ Fin (ys.eraseIdx j).length) :
    listEquivCovarianceProduct C (x :: xs) ys
        (consFinEquiv ys j e) =
      C x (ys.get j) *
        listEquivCovarianceProduct C xs (ys.eraseIdx j) e := by
  unfold listEquivCovarianceProduct
  change
    (∏ i : Fin (xs.length + 1),
      C ((x :: xs).get i)
        (ys.get ((consFinEquiv ys j e) i))) =
      C x (ys.get j) *
        ∏ i, C (xs.get i) ((ys.eraseIdx j).get (e i))
  rw [Fin.prod_univ_succ]
  apply congrArg₂ (· * ·)
  · rfl
  · apply Fintype.prod_congr
    intro i
    exact congrArg (C (xs.get i))
      (PartialPairing.get_eraseIdxOrderIso ys j (e i))

/-- Expanding a list-position bijection by the image of its head gives the
same one-step recursion as `crossWickList`. -/
theorem listEquivCovarianceSum_cons
    {ι R : Type*} [CommSemiring R]
    (C : ι → ι → R) (x : ι) (xs ys : List ι) :
    listEquivCovarianceSum C (x :: xs) ys =
      ∑ j : Fin ys.length,
        C x (ys.get j) *
          listEquivCovarianceSum C xs (ys.eraseIdx j) := by
  unfold listEquivCovarianceSum
  let d := finEquivConsDecomposition xs.length ys
  calc
    (∑ e : Fin (x :: xs).length ≃ Fin ys.length,
        listEquivCovarianceProduct C (x :: xs) ys e) =
        ∑ p : Σ j : Fin ys.length,
            Fin xs.length ≃ Fin (ys.eraseIdx j).length,
          C x (ys.get p.1) *
            listEquivCovarianceProduct C xs
              (ys.eraseIdx p.1) p.2 := by
      apply Fintype.sum_equiv d
      intro e
      have he :
          consFinEquiv ys (d e).1 (d e).2 = e :=
        d.symm_apply_apply e
      calc
        listEquivCovarianceProduct C (x :: xs) ys e =
            listEquivCovarianceProduct C (x :: xs) ys
              (consFinEquiv ys (d e).1 (d e).2) :=
          congrArg
            (listEquivCovarianceProduct C (x :: xs) ys) he.symm
        _ = C x (ys.get (d e).1) *
            listEquivCovarianceProduct C xs
              (ys.eraseIdx (d e).1) (d e).2 :=
          listEquivCovarianceProduct_cons
            C x xs ys (d e).1 (d e).2
    _ = ∑ j : Fin ys.length,
        ∑ e : Fin xs.length ≃ Fin (ys.eraseIdx j).length,
          C x (ys.get j) *
            listEquivCovarianceProduct C xs
              (ys.eraseIdx j) e := by
      rw [Fintype.sum_sigma]
    _ = ∑ j : Fin ys.length,
        C x (ys.get j) *
          ∑ e : Fin xs.length ≃ Fin (ys.eraseIdx j).length,
            listEquivCovarianceProduct C xs
              (ys.eraseIdx j) e := by
      apply Fintype.sum_congr
      intro j
      rw [Finset.mul_sum]

end CrossWickEquiv

/-- The recursive cross-contraction polynomial equals the explicit sum over
all bijections between the two lists' positions. -/
theorem crossWickList_eq_listEquivCovarianceSum
    {ι : Type*}
    (C : ι → ι → ℝ) (xs ys : List ι) :
    crossWickList C xs ys =
      listEquivCovarianceSum C xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil =>
          simp [crossWickList, listEquivCovarianceSum,
            listEquivCovarianceProduct]
      | cons y ys =>
          rw [crossWickList_nil_cons]
          unfold listEquivCovarianceSum
          symm
          apply Fintype.sum_eq_zero
          intro e
          exact Fin.elim0 (e.symm 0)
  | cons x xs ih =>
      rw [crossWickList_cons,
        CrossWickEquiv.listEquivCovarianceSum_cons]
      apply Fintype.sum_congr
      intro j
      rw [ih]

/-- Reindexing the positions of two lists transports the explicit
bijection sum without changing its weights. -/
theorem listEquivCovarianceSum_reindex
    {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (C : ι → ι → ℝ) (xs ys : List ι)
    (ep : Fin xs.length ≃ α) (em : Fin ys.length ≃ β) :
    listEquivCovarianceSum C xs ys =
      ∑ π : α ≃ β,
        ∏ i, C (xs.get (ep.symm i))
          (ys.get (em.symm (π i))) := by
  unfold listEquivCovarianceSum
  apply Fintype.sum_equiv (ep.equivCongr em)
  intro e
  unfold listEquivCovarianceProduct
  apply Fintype.prod_equiv ep
  intro j
  simp

/-- Ordered enumeration of two finite sets transports the list-position
bijection sum to a sum over bijections of the finite-set subtypes. -/
theorem listEquivCovarianceSum_orderedFinsets
    {α β ι : Type*} [LinearOrder α] [LinearOrder β]
    (sp : Finset α) (sm : Finset β)
    (C : ι → ι → ℝ) (lp : sp → ι) (lm : sm → ι) :
    listEquivCovarianceSum C
        (List.ofFn fun j : Fin sp.card =>
          lp (sp.orderIsoOfFin rfl j))
        (List.ofFn fun j : Fin sm.card =>
          lm (sm.orderIsoOfFin rfl j)) =
      ∑ π : sp ≃ sm, ∏ i, C (lp i) (lm (π i)) := by
  let xs : List ι :=
    List.ofFn fun j : Fin sp.card =>
      lp (sp.orderIsoOfFin rfl j)
  let ys : List ι :=
    List.ofFn fun j : Fin sm.card =>
      lm (sm.orderIsoOfFin rfl j)
  let ep : Fin xs.length ≃ sp :=
    EquivLike.toEquiv
      ((Fin.castOrderIso (by simp [xs])).trans
        (sp.orderIsoOfFin rfl))
  let em : Fin ys.length ≃ sm :=
    EquivLike.toEquiv
      ((Fin.castOrderIso (by simp [ys])).trans
        (sm.orderIsoOfFin rfl))
  have hxs (j : Fin xs.length) :
      xs.get j = lp (ep j) := by
    simp [xs, ep]
    apply congrArg lp
    exact congrArg (sp.orderIsoOfFin rfl) (Fin.ext rfl)
  have hys (j : Fin ys.length) :
      ys.get j = lm (em j) := by
    simp [ys, em]
    apply congrArg lm
    exact congrArg (sm.orderIsoOfFin rfl) (Fin.ext rfl)
  change listEquivCovarianceSum C xs ys =
    ∑ π : sp ≃ sm, ∏ i, C (lp i) (lm (π i))
  rw [listEquivCovarianceSum_reindex C xs ys ep em]
  apply Fintype.sum_congr
  intro π
  apply Fintype.prod_congr
  intro i
  rw [hxs, hys, ep.apply_symm_apply, em.apply_symm_apply]

end

end Anderson4D
