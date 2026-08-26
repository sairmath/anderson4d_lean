import Anderson4D.HeppTree.ClusterDiameter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Linear covers of admissible Hepp clusters

Paper §5.3 Step 4(b) covers the leaf cluster below `v` by at most

`3 * (1 + tildeScale Nm v / R)`

balls of radius `R`.  The proof is split into two reusable finite statements:
a polygonal-tour cover lemma, and the extraction of a tour of total length at
most `2 * tildeScale` from the recursive `LinkedChildren` structure.
-/

namespace Anderson4D

open PlaneTree
open List
open scoped Sym2

universe u

section FiniteTour

variable {α : Type*}

/-!
## A double traversal of a finite connected graph

Mathlib does not currently expose the usual doubled-edge tour of a spanning
tree.  The following finite induction supplies exactly that statement.  It
removes one vertex while preserving connectedness, recursively tours the
induced complement, rotates the tour to a neighbour of the removed vertex,
and appends the two-edge excursion to that vertex.
-/

private theorem exists_double_tour_aux :
    ∀ n : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V),
      Fintype.card V = n → G.Connected →
      ∃ r, ∃ p : G.Walk r r,
        p.support.toFinset = Finset.univ ∧
          ∀ e, p.edges.count e ≤ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V instV instDecV G hcard hconn
      classical
      by_cases hnt : Nontrivial V
      · letI : Nontrivial V := hnt
        obtain ⟨v, hvconn⟩ :=
          hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
        let S : Set V := {v}ᶜ
        letI : Fintype S := S.toFinite.fintype
        have hlt : Fintype.card S < Fintype.card V := by
          apply Fintype.card_lt_of_injective_not_surjective
            (fun x : S => (x : V)) Subtype.val_injective
          intro hsurj
          obtain ⟨x, hx⟩ := hsurj v
          exact x.property (by simpa [S] using hx)
        obtain ⟨r, q, hqcover, hqcount⟩ :=
          ih (Fintype.card S) (hcard ▸ hlt) S (G.induce S) rfl
            (by simpa [S] using hvconn)
        obtain ⟨w, hvw⟩ :=
          hconn.preconnected.exists_adj_of_nontrivial v
        have hwS : w ∈ S := by
          simp [S, hvw.ne']
        let wS : S := ⟨w, hwS⟩
        have hwq : wS ∈ q.support := by
          apply List.mem_toFinset.mp
          rw [hqcover]
          exact Finset.mem_univ wS
        let f : (G.induce S) →g G :=
          (SimpleGraph.Embedding.induce S).toHom
        let qG : G.Walk (r : V) (r : V) := q.map f
        have hqGsupport : qG.support = q.support.map f := by
          dsimp only [qG]
          exact SimpleGraph.Walk.support_map f q
        have hqGedges : qG.edges = q.edges.map (Sym2.map f) := by
          dsimp only [qG]
          exact SimpleGraph.Walk.edges_map f q
        let fe : S ↪ V :=
          ⟨f, (SimpleGraph.Embedding.induce (G := G) S).injective⟩
        have hfinj : Function.Injective (Sym2.map (f : S → V)) :=
          fe.sym2Map.injective
        have hwqG : w ∈ qG.support := by
          rw [hqGsupport]
          simpa [f, wS] using
            List.mem_map_of_mem (f := (f : S → V)) hwq
        let qR : G.Walk w w := qG.rotate w hwqG
        let exc : G.Walk w w :=
          SimpleGraph.Walk.cons hvw.symm
            (SimpleGraph.Walk.cons hvw SimpleGraph.Walk.nil)
        let p : G.Walk w w := qR.append exc
        refine ⟨w, p, ?_, ?_⟩
        · ext x
          simp only [Finset.mem_univ, iff_true]
          rw [List.mem_toFinset]
          by_cases hxv : x = v
          · subst x
            simp [p, exc]
          · have hxS : x ∈ S := by
              simp [S, hxv]
            let xS : S := ⟨x, hxS⟩
            have hxq : xS ∈ q.support := by
              apply List.mem_toFinset.mp
              rw [hqcover]
              exact Finset.mem_univ xS
            have hxqG : x ∈ qG.support := by
              rw [hqGsupport]
              simpa [f, xS] using
                List.mem_map_of_mem (f := (f : S → V)) hxq
            by_cases hxw : x = w
            · subst x
              exact SimpleGraph.Walk.start_mem_support p
            · have hxqGtail : x ∈ qG.support.tail := by
                by_cases hxr : x = (r : V)
                · subst x
                  apply qG.end_mem_tail_support
                  intro hnil
                  rw [SimpleGraph.Walk.nil_iff_support_eq] at hnil
                  have hwr : w = (r : V) := by
                    simpa [hnil] using hwqG
                  exact hxw hwr.symm
                · rw [← qG.cons_tail_support] at hxqG
                  exact List.mem_of_ne_of_mem hxr hxqG
              have hxqRtail : x ∈ qR.support.tail :=
                (SimpleGraph.Walk.support_rotate qG w hwqG).mem_iff.mpr
                  hxqGtail
              have hxqR : x ∈ qR.support :=
                List.mem_of_mem_tail hxqRtail
              simpa [p, SimpleGraph.Walk.support_append] using
                (List.mem_append_left exc.support.tail hxqR)
        · intro e
          simp only [p, SimpleGraph.Walk.edges_append, qR]
          rw [List.count_append]
          have hrot :
              (qG.rotate w hwqG).edges.count e = qG.edges.count e :=
            (SimpleGraph.Walk.rotate_edges qG w hwqG).perm.count_eq e
          rw [hrot]
          by_cases he : e = s(w, v)
          · subst e
            have hqGzero : qG.edges.count s(w, v) = 0 := by
              apply List.count_eq_zero_of_not_mem
              intro he_mem
              rw [hqGedges] at he_mem
              obtain ⟨eS, heSq, heeq⟩ := List.mem_map.mp he_mem
              have hvmap : v ∈ Sym2.map (f : S → V) eS := by
                rw [heeq]
                simp
              rw [Sym2.mem_map] at hvmap
              obtain ⟨a, ha, hav⟩ := hvmap
              exact a.property (by simpa [S, f] using hav)
            simp [hqGzero, exc]
          · have hqGle : qG.edges.count e ≤ 2 := by
              by_cases he_mem : e ∈ qG.edges
              · rw [hqGedges] at he_mem ⊢
                obtain ⟨eS, heSq, rfl⟩ := List.mem_map.mp he_mem
                rw [List.count_map_of_injective q.edges
                  (Sym2.map (f : S → V)) hfinj eS]
                exact hqcount eS
              · simp [List.count_eq_zero_of_not_mem he_mem]
            have he' : e ≠ s(v, w) := by
              simpa [Sym2.eq_swap] using he
            have heExc : exc.edges.count e = 0 := by
              apply List.count_eq_zero_of_not_mem
              simp [exc, he, he']
            rw [heExc, Nat.add_zero]
            exact hqGle
      · haveI : Subsingleton V :=
          not_nontrivial_iff_subsingleton.mp hnt
        let r : V := hconn.nonempty.some
        refine ⟨r, SimpleGraph.Walk.nil, ?_, ?_⟩
        · ext x
          simp [Subsingleton.elim x r]
        · simp

/-- A finite connected graph has a closed walk visiting all its vertices in
which every undirected edge is used at most twice. -/
theorem exists_double_tour {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) :
    ∃ r, ∃ p : G.Walk r r,
      p.support.toFinset = Finset.univ ∧
        ∀ e, p.edges.count e ≤ 2 :=
  exists_double_tour_aux (Fintype.card V) V G rfl hG

/-- Length of a finite polygonal chain after an initial point `a`. -/
def chainLengthFrom (d : α → α → ℝ) (a : α) : List α → ℝ
  | [] => 0
  | b :: bs => d a b + chainLengthFrom d b bs

/-- Total consecutive-edge length of a finite list. -/
def chainLength (d : α → α → ℝ) : List α → ℝ
  | [] => 0
  | a :: as => chainLengthFrom d a as

/-- The weight induced on an undirected edge by a symmetric cost. -/
def sym2Weight (d : α → α → ℝ) (hsymm : ∀ a b, d a b = d b a) :
    Sym2 α → ℝ :=
  Sym2.lift ⟨d, hsymm⟩

@[simp] theorem sym2Weight_mk (d : α → α → ℝ)
    (hsymm : ∀ a b, d a b = d b a) (a b : α) :
    sym2Weight d hsymm s(a, b) = d a b := by
  simp [sym2Weight]

@[simp] theorem chainLength_nil (d : α → α → ℝ) :
    chainLength d [] = 0 := rfl

@[simp] theorem chainLength_singleton (d : α → α → ℝ) (a : α) :
    chainLength d [a] = 0 := rfl

@[simp] theorem chainLength_cons_cons (d : α → α → ℝ)
    (a b : α) (xs : List α) :
    chainLength d (a :: b :: xs) =
      d a b + chainLength d (b :: xs) := rfl

private theorem chainLengthFrom_map {β : Type*}
    (d : β → β → ℝ) (f : α → β) (a : α) :
    ∀ xs : List α,
      chainLengthFrom d (f a) (xs.map f) =
        chainLengthFrom (fun x y => d (f x) (f y)) a xs
  | [] => rfl
  | b :: bs => by
      simp only [List.map_cons, chainLengthFrom]
      exact congrArg (d (f a) (f b) + ·)
        (chainLengthFrom_map d f b bs)

/-- Consecutive length commutes with mapping the vertices of a chain. -/
theorem chainLength_map {β : Type*}
    (d : β → β → ℝ) (f : α → β) (xs : List α) :
    chainLength d (xs.map f) =
      chainLength (fun x y => d (f x) (f y)) xs := by
  cases xs with
  | nil => rfl
  | cons a as =>
      exact chainLengthFrom_map d f a as

/-- The length of a graph walk's support list is the sum of the weights of
its edge list. -/
theorem chainLength_walk_support {V : Type*} {G : SimpleGraph V}
    (d : V → V → ℝ) (hsymm : ∀ a b, d a b = d b a)
    {a b : V} (p : G.Walk a b) :
    chainLength d p.support =
      (p.edges.map (sym2Weight d hsymm)).sum := by
  induction p with
  | nil =>
      simp [chainLength, chainLengthFrom]
  | cons h p ih =>
      cases p with
      | nil =>
          simp [chainLength, chainLengthFrom]
      | cons h' p =>
          simp only [SimpleGraph.Walk.support_cons, chainLength_cons_cons,
            SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons,
            sym2Weight_mk]
          congr 1

/-- A connected weighted finite graph has a vertex tour whose polygonal
length is at most twice its total edge weight. -/
theorem exists_short_tour_of_connected_graph
    {V : Type u} [Fintype V] [DecidableEq V]
    (d : V → V → ℝ) (hd : ∀ a b, 0 ≤ d a b)
    (hsymm : ∀ a b, d a b = d b a)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) :
    ∃ xs : List V,
      xs ≠ [] ∧ xs.toFinset = Finset.univ ∧
        chainLength d xs ≤
          2 * ∑ e ∈ G.edgeFinset, sym2Weight d hsymm e := by
  classical
  obtain ⟨r, p, hpcover, hpcount⟩ :=
    exists_double_tour G hG
  refine ⟨p.support, p.support_ne_nil, hpcover, ?_⟩
  rw [chainLength_walk_support d hsymm p,
    Finset.sum_list_map_count]
  have hw : ∀ e, 0 ≤ sym2Weight d hsymm e := by
    intro e
    refine Sym2.inductionOn e ?_
    intro a b
    simpa using hd a b
  have hsub : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset]
    exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)
  calc
    ∑ e ∈ p.edges.toFinset,
        p.edges.count e • sym2Weight d hsymm e
        ≤ ∑ e ∈ p.edges.toFinset,
            2 • sym2Weight d hsymm e := by
          apply Finset.sum_le_sum
          intro e he
          exact nsmul_le_nsmul_left (hw e) (hpcount e)
    _ = 2 * ∑ e ∈ p.edges.toFinset, sym2Weight d hsymm e := by
          rw [Finset.sum_nsmul]
          simp
    _ ≤ 2 * ∑ e ∈ G.edgeFinset, sym2Weight d hsymm e := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
            intro e heG hep
            exact hw e)

private theorem chainLengthFrom_nonneg
    (d : α → α → ℝ) (hd : ∀ a b, 0 ≤ d a b) :
    ∀ a xs, 0 ≤ chainLengthFrom d a xs
  | _, [] => le_rfl
  | a, b :: bs => by
      rw [chainLengthFrom]
      exact add_nonneg (hd a b) (chainLengthFrom_nonneg d hd b bs)

theorem chainLength_nonneg
    (d : α → α → ℝ) (hd : ∀ a b, 0 ≤ d a b) :
    ∀ xs, 0 ≤ chainLength d xs
  | [] => le_rfl
  | a :: as => chainLengthFrom_nonneg d hd a as

private theorem chainLengthFrom_shortcut
    (d : α → α → ℝ) (hd : ∀ a b, 0 ≤ d a b)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (a b : α) :
    ∀ xs, chainLengthFrom d a xs ≤
      d a b + chainLengthFrom d b xs
  | [] => by
      change 0 ≤ d a b + 0
      linarith [hd a b]
  | c :: cs => by
      rw [chainLengthFrom, chainLengthFrom]
      linarith [htri a b c]

/-- Shortcutting a polygonal chain cannot increase its length. -/
theorem chainLength_mono_sublist
    (d : α → α → ℝ) (hd : ∀ a b, 0 ≤ d a b)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    {xs ys : List α} (hsub : xs <+ ys) :
    chainLength d xs ≤ chainLength d ys := by
  have hcons :
      ∀ b ys, chainLength d ys ≤ chainLength d (b :: ys) := by
    intro b ys
    cases ys with
    | nil => rfl
    | cons c cs =>
        rw [chainLength_cons_cons]
        linarith [hd b c]
  have hboth :
      ∀ {xs ys : List α}, xs <+ ys →
        chainLength d xs ≤ chainLength d ys ∧
          ∀ a, chainLengthFrom d a xs ≤ chainLengthFrom d a ys := by
    intro xs ys h
    induction h with
    | slnil =>
        exact ⟨le_rfl, fun _ => le_rfl⟩
    | cons b h ih =>
        refine ⟨ih.1.trans (hcons b _), ?_⟩
        intro a
        exact (chainLengthFrom_shortcut d hd htri a b _).trans
          (add_le_add (le_refl (d a b)) (ih.2 b))
    | cons_cons b h ih =>
        refine ⟨ih.2 b, ?_⟩
        intro a
        simp only [chainLengthFrom]
        exact add_le_add (le_refl (d a b)) (ih.2 b)
  exact (hboth hsub).1

/-- Pairwise `R`-separation forces a lower bound on polygonal-chain length. -/
private theorem card_sub_one_mul_le_chainLength
    (d : α → α → ℝ) {R : ℝ} :
    ∀ xs : List α, xs.Nodup →
      (∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → R ≤ d a b) →
      (((xs.length - 1 : ℕ) : ℝ) * R ≤ chainLength d xs)
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: xs, hnodup, hsep => by
      have hab : R ≤ d a b :=
        hsep a (by simp) b (by simp) (by
          intro h
          subst b
          exact (List.nodup_cons.mp hnodup).1 (by simp))
      have htail :
          ((((b :: xs).length - 1 : ℕ) : ℝ) * R ≤
            chainLength d (b :: xs)) :=
        card_sub_one_mul_le_chainLength d (b :: xs)
          (List.nodup_cons.mp hnodup).2
          (fun x hx y hy hxy =>
            hsep x (by simp [hx]) y (by simp [hy]) hxy)
      rw [chainLength_cons_cons]
      have hlen :
          ((((a :: b :: xs).length - 1 : ℕ) : ℝ) * R) =
            R + (((((b :: xs).length - 1 : ℕ) : ℝ) * R)) := by
        simp
        ring
      rw [hlen]
      linarith

/-- A finite polygonal tour admits a linear-cardinality radius-`R` cover.
This is the metric-combinatorial core of Step 4(b). -/
theorem exists_cover_of_chain
    [DecidableEq α] (d : α → α → ℝ)
    (hd : ∀ a b, 0 ≤ d a b)
    (hself : ∀ a, d a a = 0)
    (hsymm : ∀ a b, d a b = d b a)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (xs : List α) (hxs : xs ≠ []) {R : ℝ} (hR : 0 < R) :
    ∃ Q : Finset α,
      Q ⊆ xs.toFinset ∧
      (∀ x ∈ xs.toFinset, ∃ q ∈ Q, d x q ≤ R) ∧
      (Q.card : ℝ) ≤ 1 + chainLength d xs / R := by
  classical
  let X := xs.toFinset
  let IsSeparated : Finset α → Prop := fun Q =>
    ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → R < d a b
  let candidates : Finset (Finset α) :=
    X.powerset.filter IsSeparated
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, IsSeparated]
  obtain ⟨Q, hQcan, hQmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hQsub : Q ⊆ X :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hQcan).1
  have hQsep : IsSeparated Q :=
    (Finset.mem_filter.mp hQcan).2
  have hX : X.Nonempty := by
    exact (List.toFinset_nonempty_iff xs).mpr hxs
  have hQne : Q.Nonempty := by
    obtain ⟨x, hx⟩ := hX
    have hsingle : {x} ∈ candidates := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr (by simpa),
        by simp [IsSeparated]⟩
    have hcard := hQmax {x} hsingle
    simpa using hcard
  have hcover : ∀ x ∈ X, ∃ q ∈ Q, d x q ≤ R := by
    intro x hx
    by_contra hno
    have hfar : ∀ q ∈ Q, R < d x q := by
      intro q hq
      exact lt_of_not_ge fun hle => hno ⟨q, hq, hle⟩
    have hxQ : x ∉ Q := by
      intro hxQ
      have := hfar x hxQ
      rw [hself] at this
      linarith
    have hinsertSep : IsSeparated (insert x Q) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hax | haQ
      · rcases Finset.mem_insert.mp hb with hbx | hbQ
        · exact (hab (hax.trans hbx.symm)).elim
        · rw [hax]
          exact hfar b hbQ
      · rcases Finset.mem_insert.mp hb with hbx | hbQ
        · rw [hbx, hsymm]
          exact hfar a haQ
        · exact hQsep a haQ b hbQ hab
    have hinsert : insert x Q ∈ candidates := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr
        (Finset.insert_subset hx hQsub), hinsertSep⟩
    have hmax := hQmax (insert x Q) hinsert
    rw [Finset.card_insert_of_notMem hxQ] at hmax
    omega
  let qs := (xs.filter fun x => decide (x ∈ Q)).dedup
  have hqsub : qs <+ xs :=
    (List.dedup_sublist _).trans List.filter_sublist
  have hqnodup : qs.Nodup := by
    exact List.nodup_dedup _
  have hqfin : qs.toFinset = Q := by
    ext x
    simp only [List.mem_toFinset, qs, List.mem_dedup,
      List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro hxQ
      exact ⟨by
        have hxX := hQsub hxQ
        exact List.mem_toFinset.mp hxX, hxQ⟩
  have hqcard : qs.length = Q.card := by
    rw [← List.toFinset_card_of_nodup hqnodup, hqfin]
  have hpack :
      ((((Q.card - 1 : ℕ) : ℝ) * R) ≤ chainLength d xs) := by
    rw [← hqcard]
    exact (card_sub_one_mul_le_chainLength d qs hqnodup
      (fun a ha b hb hab =>
        (hQsep a (by
          rw [← hqfin]
          exact List.mem_toFinset.mpr ha) b (by
          rw [← hqfin]
          exact List.mem_toFinset.mpr hb) hab).le)).trans
      (chainLength_mono_sublist d hd htri hqsub)
  have hQpos : 0 < Q.card := Finset.card_pos.mpr hQne
  have hsubcast : ((Q.card - 1 : ℕ) : ℝ) = (Q.card : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hQpos))]
    norm_num
  rw [hsubcast] at hpack
  have hdiv :
      (Q.card : ℝ) - 1 ≤ chainLength d xs / R := by
    rw [le_div_iff₀ hR]
    nlinarith
  exact ⟨Q, hQsub, hcover, by linarith⟩

end FiniteTour

/-- Distance between two embedded leaves. -/
def leafDistance {t : PlaneTree}
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ)
    (l l' : {l // l ∈ Leaves t}) : ℝ :=
  znorm (z l - z l')

private theorem cc_leafDistance_triangle {t : PlaneTree}
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ)
    (a b c : {l // l ∈ Leaves t}) :
    leafDistance z a c ≤ leafDistance z a b + leafDistance z b c := by
  have hadd (x y : Fin 4 → ℤ) :
      znorm (x + y) ≤ znorm x + znorm y := by
    unfold znorm
    have h : (fun i => (((x + y) i) : ℝ)) =
        (fun i => ((x i : ℤ) : ℝ)) + (fun i => ((y i : ℤ) : ℝ)) := by
      funext i
      simp
    rw [h]
    exact norm_add_le _ _
  have h : z a - z c = (z a - z b) + (z b - z c) := by
    abel
  rw [leafDistance, leafDistance, leafDistance, h]
  exact hadd _ _

/-- The metric on the leaves below a fixed vertex, keeping the proof-relevant
subtype needed to speak about a graph on exactly that cluster. -/
def clusterLeafDistance {t : PlaneTree}
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t)
    (a b : {l // l ∈ leavesUnder v}) : ℝ :=
  leafDistance z a.1 b.1

private theorem cc_clusterLeafDistance_symm {t : PlaneTree}
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t)
    (a b : {l // l ∈ leavesUnder v}) :
    clusterLeafDistance z v a b = clusterLeafDistance z v b a := by
  exact znorm_sub_comm _ _

/-- Total geometric length of a finite graph connecting the leaves below
`v`.  Its edges are measured by the actual `znorm` distance of their embedded
endpoints. -/
noncomputable def clusterNetworkLength {t : PlaneTree}
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t)
    (G : SimpleGraph {l // l ∈ leavesUnder v}) : ℝ := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  exact ∑ e ∈ G.edgeFinset,
    sym2Weight (clusterLeafDistance z v)
      (cc_clusterLeafDistance_symm z v) e

/-- The exact geometric certificate underlying §5.3 Step 4(b): the leaf
cluster has a connected network of total length at most its accumulated Hepp
scale.  The recursive `LinkedChildren` construction is intended to produce
this certificate by joining the child certificates with one link per edge of
a child spanning tree. -/
def HasClusterNetwork {t : PlaneTree} (Nm : HeppMarking t)
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ) (v : VPos t) : Prop :=
  ∃ G : SimpleGraph {l // l ∈ leavesUnder v},
    G.Connected ∧ clusterNetworkLength z v G ≤ tildeScale Nm v

/-- Exact tour certificate needed for the cluster-cover claim: the list
visits precisely the leaves below `v` (repetitions allowed), and its total
polygonal length is at most twice the accumulated Hepp scale.  The factor
two is the standard traversal of each edge of a connecting tree in both
directions. -/
def IsClusterTour {t : PlaneTree} (Nm : HeppMarking t)
    (z : {l // l ∈ Leaves t} → Fin 4 → ℤ)
    (v : VPos t) (xs : List {l // l ∈ Leaves t}) : Prop :=
  xs ≠ [] ∧ xs.toFinset = leavesUnder v ∧
    chainLength (leafDistance z) xs ≤ 2 * tildeScale Nm v

/-- Step 4(b) once the precise finite tour certificate has been extracted
from `LinkedChildren`.  This lemma already produces lattice-valued centers,
not merely leaf indices, and has exactly the constant in the paper. -/
theorem exists_clusterCover_of_tour
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (v : VPos t)
    (xs : List {l // l ∈ Leaves t}) (htour : IsClusterTour Nm z v xs)
    {R : ℝ} (hR : 0 < R) :
    ∃ Q : Finset (Fin 4 → ℤ),
      Q ⊆ (leavesUnder v).image z ∧
      (∀ l ∈ leavesUnder v, ∃ q ∈ Q, znorm (z l - q) ≤ R) ∧
      (Q.card : ℝ) ≤ 3 * (1 + tildeScale Nm v / R) := by
  classical
  have hd : ∀ a b, 0 ≤ leafDistance z a b :=
    fun a b => znorm_nonneg _
  have hself : ∀ a, leafDistance z a a = 0 := by
    intro a
    simp [leafDistance, znorm]
  have hsymm : ∀ a b, leafDistance z a b = leafDistance z b a := by
    intro a b
    exact znorm_sub_comm _ _
  obtain ⟨P, hPsub, hPcover, hPcard⟩ :=
    exists_cover_of_chain (leafDistance z) hd hself hsymm
      (cc_leafDistance_triangle z) xs htour.1 hR
  let Q : Finset (Fin 4 → ℤ) := P.image z
  have hQcard : Q.card = P.card :=
    Finset.card_image_of_injective P hadm.inj
  have hQsub : Q ⊆ (leavesUnder v).image z := by
    intro q hq
    obtain ⟨l, hlP, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_image_of_mem
    rw [← htour.2.1]
    exact hPsub hlP
  have hQcover :
      ∀ l ∈ leavesUnder v, ∃ q ∈ Q, znorm (z l - q) ≤ R := by
    intro l hl
    have hlxs : l ∈ xs.toFinset := by
      rw [htour.2.1]
      exact hl
    obtain ⟨q, hqP, hdq⟩ := hPcover l hlxs
    exact ⟨z q, Finset.mem_image_of_mem z hqP, hdq⟩
  refine ⟨Q, hQsub, hQcover, ?_⟩
  rw [hQcard]
  have hchain :
      chainLength (leafDistance z) xs / R ≤
        2 * tildeScale Nm v / R :=
    div_le_div_of_nonneg_right htour.2.2 hR.le
  have htilde := tildeScale_nonneg Nm v
  have hratio : 0 ≤ tildeScale Nm v / R :=
    div_nonneg htilde hR.le
  have htwo :
      2 * tildeScale Nm v / R =
        2 * (tildeScale Nm v / R) := by
    ring
  rw [htwo] at hchain
  linarith

/-- **Cluster cover from a connected network, §5.3 Step 4(b).**
A connected leaf network of total length at most `tildeScale` yields the
paper's lattice-centre cover with the exact stated constant.  This is the
precise metric-tree main lemma consumed by the recursive `LinkedChildren`
construction; no ambient box-counting loss is used. -/
theorem exists_clusterCover_of_network
    {t : PlaneTree} {Nm : HeppMarking t} {M : ℕ}
    {z : {l // l ∈ Leaves t} → Fin 4 → ℤ}
    (hadm : IsAdmissible Nm M z) (v : VPos t)
    (hnetwork : HasClusterNetwork Nm z v)
    {R : ℝ} (hR : 0 < R) :
    ∃ Q : Finset (Fin 4 → ℤ),
      Q ⊆ (leavesUnder v).image z ∧
      (∀ l ∈ leavesUnder v, ∃ q ∈ Q, znorm (z l - q) ≤ R) ∧
      (Q.card : ℝ) ≤ 3 * (1 + tildeScale Nm v / R) := by
  classical
  obtain ⟨G, hG, hGlen⟩ := hnetwork
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let d := clusterLeafDistance z v
  have hd : ∀ a b, 0 ≤ d a b := by
    intro a b
    exact znorm_nonneg _
  have hsymm : ∀ a b, d a b = d b a :=
    cc_clusterLeafDistance_symm z v
  obtain ⟨ys, hysne, hyscover, hyslen⟩ :=
    exists_short_tour_of_connected_graph d hd hsymm G hG
  let xs : List {l // l ∈ Leaves t} := ys.map Subtype.val
  have hxsne : xs ≠ [] := by
    simpa [xs] using hysne
  have hxscover : xs.toFinset = leavesUnder v := by
    ext l
    simp only [xs, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact a.property
    · intro hl
      let a : {l // l ∈ leavesUnder v} := ⟨l, hl⟩
      refine ⟨a, ?_, rfl⟩
      apply List.mem_toFinset.mp
      rw [hyscover]
      exact Finset.mem_univ a
  have hmap :
      chainLength (leafDistance z) xs =
        chainLength d ys := by
    exact chainLength_map (leafDistance z) Subtype.val ys
  have hedge :
      (∑ e ∈ G.edgeFinset, sym2Weight d hsymm e) =
        clusterNetworkLength z v G := by
    simp only [clusterNetworkLength, d]
  have hyslen' :
      chainLength d ys ≤ 2 * tildeScale Nm v := by
    calc
      chainLength d ys
          ≤ 2 * ∑ e ∈ G.edgeFinset, sym2Weight d hsymm e :=
        hyslen
      _ = 2 * clusterNetworkLength z v G := by rw [hedge]
      _ ≤ 2 * tildeScale Nm v :=
        mul_le_mul_of_nonneg_left hGlen (by norm_num)
  have htour : IsClusterTour Nm z v xs :=
    ⟨hxsne, hxscover, hmap.trans_le hyslen'⟩
  exact exists_clusterCover_of_tour hadm v xs htour hR

end Anderson4D
