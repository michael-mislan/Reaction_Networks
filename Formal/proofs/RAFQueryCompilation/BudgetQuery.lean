import proofs.RAFQueryCompilation.LocalBudgetBounds
import proofs.RAFQueryCompilation.ChargedQuery

namespace RAFQueryCompilation
open RAF

def metadataStateCap (md : RegionalMetadata) (e : ℕ) : ℕ :=
  1+(4*e+1)^2+(md.outputEntries+1)^2+
    (md.outputEntries+1)*(2*e+1)*(md.outputEntries+1)

theorem metadataStateCap_covers {M R : Type*} [DecidableEq M]
    (Q : CRS M R) (cats : R → Finset M) (succ : R → Finset R)
    (needs : R → Finset M) (E : Finset R) :
    stateCap Q E ≤ metadataStateCap (collectRegionalMetadata Q cats succ needs E) E.card := by
  have h : (E.biUnion Q.outputs).card ≤ ∑ r ∈ E, (Q.outputs r).card := Finset.card_biUnion_le
  have h1 := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2
  have h2 := Nat.mul_le_mul_right ((∑ r ∈ E, (Q.outputs r).card)+1)
    (Nat.mul_le_mul_right (2*E.card+1) (Nat.add_le_add_right h 1))
  exact Nat.add_le_add (Nat.add_le_add_left h1 _) h2

/-- A failed attempt leaves every state field unchanged. The second regional
metadata pass is deliberately paid; no union is evaluated to estimate commit cost. -/
def budgetQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ) : QueryStep n m :=
  let prep := editPrepCharge removed added
  if prep ≤ budget then
    let checked := budgetLocal Q cats succ needs (fun r => state.answer[r.val])
      (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
      (fun x => state.counts[x.val]) cert (budget-prep)
    let spent := prep+checked.2
    match checked.1 with
    | none => ⟨none,state,spent⟩
    | some L =>
      if spent+metadataCharge E ≤ budget then
        let md := collectRegionalMetadata Q cats succ needs E
        let fee := spent+metadataCharge E+metadataStateCap md E.card+(1+E.card^2)
        if fee ≤ budget then ⟨some L,applyLocalState Q state removed added E L,fee⟩
        else ⟨none,state,spent+metadataCharge E⟩
      else ⟨none,state,spent⟩
  else ⟨none,state,0⟩

theorem budgetQuery_bound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ) :
    (budgetQuery Q cats succ needs state removed added E cert budget).charge ≤ budget := by
  have hb := budgetLocal_bound Q cats succ needs (fun r => state.answer[r.val])
    (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
    (fun x => state.counts[x.val]) cert (budget-editPrepCharge removed added)
  dsimp only [budgetQuery]
  split
  · split
    · simp only []
      omega
    · split_ifs <;> simp_all only
      omega
  · exact Nat.zero_le _

theorem budgetQuery_rejected_state {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ)
    (h : (budgetQuery Q cats succ needs state removed added E cert budget).answer = none) :
    (budgetQuery Q cats succ needs state removed added E cert budget).state = state := by
  dsimp only [budgetQuery] at h ⊢
  split
  · split
    · rfl
    · split_ifs <;> simp_all
  · rfl

theorem budgetQuery_accepted {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ)
    {L : Finset (Fin m)}
    (h : (budgetQuery Q cats succ needs state removed added E cert budget).answer = some L) :
    checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs (fun r => state.answer[r.val])
      (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
      (fun x => state.counts[x.val]) cert = some L ∧
    (budgetQuery Q cats succ needs state removed added E cert budget).state =
      applyLocalState Q state removed added E L := by
  dsimp only [budgetQuery] at h ⊢
  split
  · split
    · simp_all
    · rename_i out hout
      split_ifs <;> simp_all
      exact budgetLocal_refines _ cats _ _ _ _ _ _ _ cert _ hout
  · simp_all

end RAFQueryCompilation
