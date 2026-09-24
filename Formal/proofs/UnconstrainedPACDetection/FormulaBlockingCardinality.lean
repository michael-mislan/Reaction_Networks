import proofs.UnconstrainedPACDetection.ClauseSatisfaction
import proofs.UnconstrainedPACDetection.FormulaEnumeration

namespace UnconstrainedPACDetection.FormulaBlockingCardinality
open Complexity.SAT FormulaWiring

def pairs (φ : CNF) (i : Fin (levels φ)) : Finset (Fin (varCount φ) × Bool) :=
  Finset.univ.filter fun p => blocked φ i p.1 p.2 = true

theorem literal_bound (φ : CNF) (i : Fin (levels φ)) {c : Nat} {l : Lit}
    (h : lookup φ i = some (c,l)) : l.var < varCount φ := by
  obtain ⟨cl,hcl,hl⟩ := ClauseSatisfaction.lookup_clause φ i h
  have hm := Clause.var_le_maxVar hl
  have hc := CNF.clause_maxVar_le_maxVar (List.mem_of_getElem? hcl)
  unfold varCount
  omega

/-- A real occurrence has one blocked rail pair; absence has none. -/
theorem pairs_card_lookup (φ : CNF) (i : Fin (levels φ)) :
    (pairs φ i).card = if (lookup φ i).isSome then 1 else 0 := by
  cases h : lookup φ i with
  | none => simp [pairs,blocked,h]
  | some o =>
    obtain ⟨c,l⟩ := o
    let p : Fin (varCount φ) × Bool := (⟨l.var,literal_bound φ i h⟩,!l.sign)
    have hp : blocked φ i p.1 p.2 = true := by
      simp [p,blocked,h]
    have he : pairs φ i = {p} := by
      ext q
      simp only [pairs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · intro hq
        obtain ⟨hv,hb⟩ := LogicalTrace.blocked_unique φ i hq hp
        exact Prod.ext hv hb
      · rintro rfl
        exact hp
    simp [he]

theorem pairs_card (φ : CNF) (i : Fin (levels φ)) :
    (pairs φ i).card = if i.val < (occurrences φ).length then 1 else 0 := by
  rw [pairs_card_lookup]
  by_cases hi : i.val < (occurrences φ).length
  · simp [lookup,hi]
  · simp [lookup,hi]

/-- Summing the blocking columns contributes exactly the number of real occurrences. -/
theorem total_blocked (φ : CNF) :
    (∑ i : Fin (levels φ), (pairs φ i).card) = (occurrences φ).length := by
  change (∑ i : Fin ((occurrences φ).length+1), (pairs φ i).card) = _
  rw [Fin.sum_univ_castSucc]
  have hr : ∀ i : Fin (occurrences φ).length, (pairs φ i.castSucc).card = 1 := by
    intro i
    rw [pairs_card]
    simp [i.isLt]
  have hd : (pairs φ (Fin.last (occurrences φ).length)).card = 0 := by
    rw [pairs_card]
    simp
  simp_rw [hr]
  rw [hd]
  simp

end UnconstrainedPACDetection.FormulaBlockingCardinality
