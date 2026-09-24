import proofs.RAFQueryCompilation.ChargedLocal
import proofs.RAFQueryCompilation.ChargedState

namespace RAFQueryCompilation
open RAF

structure QueryStep (n m : ℕ) where
  answer : Option (Finset (Fin m))
  state : QueryState n m
  charge : ℕ

def editPrepCharge {R : Type*} (removed added : Finset R) : ℕ :=
  1+(removed.card+added.card+1)^2

/-- One decoded query, with local output sorting/word emission budget.
Source setup and decoding of raw byte streams are separate batch costs. -/
def chargedQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) : QueryStep n m :=
  let checked := chargedLocal Q cats succ needs (fun r => state.answer[r.val])
    (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
    (fun x => state.counts[x.val]) cert
  match checked.1 with
  | none => ⟨none, state, editPrepCharge removed added+checked.2+1⟩
  | some L =>
    let update := chargedState Q state removed added E L
    ⟨some L, update.1, editPrepCharge removed added+checked.2+update.2+(1+L.card^2)⟩

theorem checked_region_edits {R : Type*} [DecidableEq R] (succ : R → Finset R)
    (D E : Finset R) (h : checkRegion succ D E = true) : D ⊆ E := by
  have hh : D ⊆ E ∧ ∀ e ∈ E, succ e ⊆ E := of_decide_eq_true h
  exact hh.1

theorem chargedQuery_answer {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) :
    (chargedQuery Q cats succ needs state removed added E cert).answer =
      checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs (fun r => state.answer[r.val])
        (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
        (fun x => state.counts[x.val]) cert := by
  simp only [chargedQuery, chargedLocal_refines]
  split <;> simp_all only

theorem chargedQuery_state {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) :
    (chargedQuery Q cats succ needs state removed added E cert).state =
      match checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs (fun r => state.answer[r.val])
        (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
        (fun x => state.counts[x.val]) cert with
      | none => state
      | some L => applyLocalState Q state removed added E L := by
  simp only [chargedQuery, chargedLocal_refines]
  split <;> simp_all only
  rfl

theorem chargedQuery_bound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (i o c : ℕ)
    (hi : ∀ r ∈ E, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ E, (Q.outputs r).card ≤ o)
    (hc : ∀ r ∈ E, (cats r).card ≤ c) :
    (chargedQuery Q cats succ needs state removed added E cert).charge ≤
      editPrepCharge removed added + (regionCharge succ (removed ∪ added) E + boundaryCharge Q needs E +
      cert.flatten.length * replayCap E.card i o (sourceEnvelope Q needs E).card +
      (E.card+1) * pruningRoundCap E.card i o c (sourceEnvelope Q needs E).card +
      stateCap Q E + (1+E.card^2)) := by
  have hb := chargedLocal_bound Q cats succ needs (fun r => state.answer[r.val])
    (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
    (fun x => state.counts[x.val]) cert i o c hi ho hc
  simp only [chargedQuery, chargedLocal_refines]
  cases hresult : checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs
      (fun r => state.answer[r.val]) (editedMask (fun r => state.available[r.val]) removed added)
      (removed ∪ added) E (fun x => state.counts[x.val]) cert with
  | none =>
    have hx : 1 ≤ stateCap Q E + (1+E.card^2) := by omega
    simpa only [Nat.add_assoc] using
      Nat.add_le_add_left (Nat.add_le_add hb hx) (editPrepCharge removed added)
  | some L =>
    have hl := checkMaskedLocal_subset Q (fun x r => x ∈ cats r) succ needs
      _ _ _ E _ cert hresult
    have hd : removed ∪ added ⊆ E := by
      unfold checkMaskedLocal at hresult
      split at hresult
      next hr => exact checked_region_edits succ (removed ∪ added) E hr
      next => contradiction
    have hs := chargedState_bound Q state removed added E L hd hl
    have hout := Nat.add_le_add_left (Nat.pow_le_pow_left (Finset.card_le_card hl) 2) 1
    simpa only [Nat.add_assoc] using Nat.add_le_add_left
      (Nat.add_le_add (Nat.add_le_add hb hs) hout) (editPrepCharge removed added)

end RAFQueryCompilation
