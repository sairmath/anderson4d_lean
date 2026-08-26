import Anderson4D.PermSum.SingleScaleAnchorScaleLedger

/-!
# A canonical valid active class word

The final single-scale assembly needs one fixed valid active `(N,X)` word
against which the word-independent completed anchor coefficient can be
normalized.  The labeled-copy cardinal identity supplies a canonical
arrangement, and its induced class word is automatically valid.
-/

set_option warningAsError true
set_option autoImplicit false

namespace Anderson4D

open PlaneTree

noncomputable section

/-- A canonical labeled arrangement, obtained only from the cardinal
ledger for labeled Hepp copies. -/
noncomputable def referenceHeppArrangement {t : PlaneTree}
    (mu : Multiplicities t) : HeppArrangement mu :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rfl)

/-- A fixed active `(N,X)` word available for every marking. -/
noncomputable def referenceNXWord {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    Fin (totalMultiplicity mu) → ActiveNXClass Nm mu :=
  arrangementNXWord Nm mu (referenceHeppArrangement mu)

/-- The canonical reference word has exactly the prescribed active-class
multiplicities. -/
@[simp] theorem referenceNXWord_mem_validWords {t : PlaneTree}
    (Nm : HeppMarking t) (mu : Multiplicities t) :
    referenceNXWord Nm mu ∈
      validWords (M := totalMultiplicity mu)
        (activeNXMultiplicity Nm mu) := by
  exact arrangementNXWord_mem_validWords Nm mu
    (referenceHeppArrangement mu)

end

end Anderson4D
