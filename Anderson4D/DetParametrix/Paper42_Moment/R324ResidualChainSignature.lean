import Anderson4D.DetParametrix.Paper42_Moment.R324PrimitiveBlockLedger
import Anderson4D.DetParametrix.Paper42_Moment.R324MomentFiberReindex

/-!
# Exponential residual-chain signatures for R-324

After the two within-half endpoint signatures have been fixed, paper
Section 4.2 Step 3 fixes the nested intervals which cross the central cut.
Recording the interval list itself would obscure the exponential counting
ledger.  A nested inside-to-outside chain is instead determined by the
finite sets of its left and right endpoints: the left endpoints occur in
strictly decreasing order and the right endpoints in strictly increasing
order.

This file packages that endpoint signature, proves its rigidity, and
regroups a fixed moment-signature fibre by at most `4^(2m)` residual
signatures.  Within each refined fibre the complete primitive-block
schedule is literally identical.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

noncomputable section

/-- Endpoint-role signature of the nested residual chain. -/
def momentResidualChainSignature
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    Finset (Fin (2 * m)) × Finset (Fin (2 * m)) :=
  (((momentResidualIntervalChain κp κm π).map
      Prod.fst).toFinset,
    ((momentResidualIntervalChain κp κm π).map
      Prod.snd).toFinset)

/-- Two lists sorted by an asymmetric relation are equal once their
underlying finite sets agree. -/
private theorem List.eq_of_toFinset_eq_of_pairwise_asymm
    {α : Type*} [DecidableEq α]
    {r : α → α → Prop}
    (hasymm : ∀ a b, r a b → r b a → False)
    {left right : List α}
    (hleft : left.Pairwise r)
    (hright : right.Pairwise r)
    (hset : left.toFinset = right.toFinset) :
    left = right := by
  have hleftNodup : left.Nodup := by
    exact hleft.imp fun {a b} hab habEq => by
      subst b
      exact (hasymm a a hab hab).elim
  have hrightNodup : right.Nodup := by
    exact hright.imp fun {a b} hab habEq => by
      subst b
      exact (hasymm a a hab hab).elim
  have hperm : left.Perm right :=
    List.perm_of_nodup_nodup_toFinset_eq
      hleftNodup hrightNodup hset
  exact hperm.eq_of_pairwise
    (fun a b _ _ hab hba =>
      (hasymm a b hab hba).elim)
    hleft hright

/-- A list of pairs is determined by its two coordinate lists. -/
private theorem List.prod_eq_of_map_fst_eq_map_snd_eq
    {α β : Type*}
    {left right : List (α × β)}
    (hfst : left.map Prod.fst = right.map Prod.fst)
    (hsnd : left.map Prod.snd = right.map Prod.snd) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons b right =>
          simp only [List.map_cons, List.map_nil,
            reduceCtorEq] at hfst
  | cons a left ih =>
      cases right with
      | nil =>
          simp only [List.map_cons, List.map_nil,
            reduceCtorEq] at hfst
      | cons b right =>
          simp only [List.map_cons, List.cons.injEq] at hfst hsnd
          have hab : a = b :=
            Prod.ext hfst.1 hsnd.1
          subst b
          rw [ih hfst.2 hsnd.2]

theorem momentResidualIntervalChain_left_pairwise
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ((momentResidualIntervalChain κp κm π).map
      Prod.fst).Pairwise (fun a b => b < a) := by
  rw [List.pairwise_map]
  exact
    (momentResidualIntervalChain_pairwise_laterContains
      κp κm π).imp fun h => h.1

theorem momentResidualIntervalChain_right_pairwise
    {m : ℕ} (κp κm : PartialPairing (Fin m))
    (π : κp.singles ≃ κm.singles) :
    ((momentResidualIntervalChain κp κm π).map
      Prod.snd).Pairwise (fun a b => a < b) := by
  rw [List.pairwise_map]
  exact
    (momentResidualIntervalChain_pairwise_laterContains
      κp κm π).imp fun h => h.2

/-- The two endpoint sets determine the canonical residual interval chain
exactly. -/
theorem momentResidualIntervalChain_eq_of_signature_eq
    {m : ℕ} (e e' : MomentContraction m)
    (hsignature :
      momentResidualChainSignature e.1 e.2.1 e.2.2 =
        momentResidualChainSignature e'.1 e'.2.1 e'.2.2) :
    momentResidualIntervalChain e.1 e.2.1 e.2.2 =
      momentResidualIntervalChain e'.1 e'.2.1 e'.2.2 := by
  have hleftSet :
      ((momentResidualIntervalChain e.1 e.2.1 e.2.2).map
          Prod.fst).toFinset =
        ((momentResidualIntervalChain e'.1 e'.2.1 e'.2.2).map
          Prod.fst).toFinset := by
    exact congrArg Prod.fst hsignature
  have hrightSet :
      ((momentResidualIntervalChain e.1 e.2.1 e.2.2).map
          Prod.snd).toFinset =
        ((momentResidualIntervalChain e'.1 e'.2.1 e'.2.2).map
          Prod.snd).toFinset := by
    exact congrArg Prod.snd hsignature
  have hleft :
      (momentResidualIntervalChain e.1 e.2.1 e.2.2).map
          Prod.fst =
        (momentResidualIntervalChain e'.1 e'.2.1 e'.2.2).map
          Prod.fst := by
    exact List.eq_of_toFinset_eq_of_pairwise_asymm
      (fun a b hab hba => (lt_asymm hab hba))
      (momentResidualIntervalChain_left_pairwise
        e.1 e.2.1 e.2.2)
      (momentResidualIntervalChain_left_pairwise
        e'.1 e'.2.1 e'.2.2)
      hleftSet
  have hright :
      (momentResidualIntervalChain e.1 e.2.1 e.2.2).map
          Prod.snd =
        (momentResidualIntervalChain e'.1 e'.2.1 e'.2.2).map
          Prod.snd := by
    exact List.eq_of_toFinset_eq_of_pairwise_asymm
      (fun a b hab hba => (lt_asymm hab hba))
      (momentResidualIntervalChain_right_pairwise
        e.1 e.2.1 e.2.2)
      (momentResidualIntervalChain_right_pairwise
        e'.1 e'.2.1 e'.2.2)
      hrightSet
  exact List.prod_eq_of_map_fst_eq_map_snd_eq
    hleft hright

/-- Residual endpoint signatures realized by all order-`m` contraction
entities. -/
def momentResidualChainSignatures (m : ℕ) :
    Finset
      (Finset (Fin (2 * m)) ×
        Finset (Fin (2 * m))) :=
  (Finset.univ : Finset (MomentContraction m)).image
    fun e =>
      momentResidualChainSignature e.1 e.2.1 e.2.2

/-- Fixing the cross-cut nested intervals costs only an exponential
`4^(2m)` factor. -/
theorem card_momentResidualChainSignatures_le
    (m : ℕ) :
    (momentResidualChainSignatures m).card ≤
      4 ^ (2 * m) := by
  calc
    (momentResidualChainSignatures m).card ≤
        Fintype.card
          (Finset (Fin (2 * m)) ×
            Finset (Fin (2 * m))) :=
      Finset.card_le_univ _
    _ = 4 ^ (2 * m) := by
      simp only [Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin]
      rw [show (4 : ℕ) = 2 * 2 by norm_num,
        mul_pow]

/-- Residual endpoint signatures realized inside one fixed within-half
moment-signature fibre. -/
def momentResidualChainSignaturesInFiber
    {m : ℕ} (e₀ : MomentContraction m) :
    Finset
      (Finset (Fin (2 * m)) ×
        Finset (Fin (2 * m))) :=
  (Finset.univ : Finset (MomentSignatureFiberAt e₀)).image
    fun e =>
      momentResidualChainSignature
        e.1.1 e.1.2.1 e.1.2.2

theorem card_momentResidualChainSignaturesInFiber_le
    {m : ℕ} (e₀ : MomentContraction m) :
    (momentResidualChainSignaturesInFiber e₀).card ≤
      4 ^ (2 * m) := by
  calc
    (momentResidualChainSignaturesInFiber e₀).card ≤
        Fintype.card
          (Finset (Fin (2 * m)) ×
            Finset (Fin (2 * m))) :=
      Finset.card_le_univ _
    _ = 4 ^ (2 * m) := by
      simp only [Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin]
      rw [show (4 : ℕ) = 2 * 2 by norm_num,
        mul_pow]

/-- Exact regrouping of one moment-signature fibre by its residual-chain
endpoint signature. -/
theorem sum_momentSignatureFiber_by_residualChainSignature
    {m : ℕ} (e₀ : MomentContraction m)
    {A : Type*} [AddCommMonoid A]
    (F : MomentSignatureFiberAt e₀ → A) :
    (∑ r ∈ momentResidualChainSignaturesInFiber e₀,
        ∑ e ∈ (Finset.univ :
            Finset (MomentSignatureFiberAt e₀)) with
          momentResidualChainSignature
            e.1.1 e.1.2.1 e.1.2.2 = r,
          F e) =
      ∑ e : MomentSignatureFiberAt e₀, F e := by
  apply Finset.sum_fiberwise_of_maps_to
  intro e he
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

/-- Equal within-half and residual endpoint signatures give the identical
complete primitive-block schedule. -/
theorem momentNonemptyPrimitiveBlocks_eq_of_signatures_eq
    {m : ℕ} (e e' : MomentContraction m)
    (hmoment :
      momentContractionSignature e =
        momentContractionSignature e')
    (hresidual :
      momentResidualChainSignature e.1 e.2.1 e.2.2 =
        momentResidualChainSignature e'.1 e'.2.1 e'.2.2) :
    momentNonemptyPrimitiveBlocks e.1 e.2.1 e.2.2 =
      momentNonemptyPrimitiveBlocks e'.1 e'.2.1 e'.2.2 := by
  have hextraction :=
    momentExtractionBlocks_eq_of_momentContractionSignature_eq
      e e' hmoment
  have hfinal :=
    momentFinalActive_eq_of_momentContractionSignature_eq
      e e' hmoment
  have hactive :
      momentResidualActive e.1 e.2.1 =
        momentResidualActive e'.1 e'.2.1 := by
    unfold momentResidualActive
    rw [hfinal.1, hfinal.2]
  have hchain :=
    momentResidualIntervalChain_eq_of_signature_eq
      e e' hresidual
  unfold momentNonemptyPrimitiveBlocks
    momentAllPrimitiveBlocks
  rw [hextraction.1, hextraction.2]
  congr 1
  unfold momentResidualCollapseBlocks
  rw [hactive, hchain]

end

end Anderson4D
