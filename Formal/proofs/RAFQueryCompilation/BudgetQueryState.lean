import proofs.RAFQueryCompilation.BudgetQuery

namespace RAFQueryCompilation
open RAF

theorem budgetQuery_state_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n))
    (hi : IndexSound Q (fun x r => x ∈ cats r) succ)
    (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (A removed added E : Finset (Fin m)) (state : QueryState n m)
    (cert : List (List (Fin m))) (budget : ℕ)
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x)
    {L : Finset (Fin m)}
    (h : (budgetQuery Q cats succ needs state removed added E cert budget).answer = some L) :
    (∀ r, (budgetQuery Q cats succ needs state removed added E cert budget).state.answer[r.val] = true ↔
      r ∈ evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) ∧
    (∀ x, (budgetQuery Q cats succ needs state removed added E cert budget).state.counts[x.val] =
      producerCount Q (evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) x) ∧
    (∀ r, (budgetQuery Q cats succ needs state removed added E cert budget).state.available[r.val] = true ↔
      r ∈ (A \ removed) ∪ added) := by
  have hs := budgetQuery_accepted Q cats succ needs state removed added E cert budget h
  rw [hs.2]
  exact applyLocalState_correct Q (fun x r => x ∈ cats r) succ needs hi hn
    A removed added E state cert ho ha hc hs.1

/-- The reserved state/output allowance dominates the earlier declared patch cost. -/
theorem budgetQuery_commit_covers {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ)
    {L : Finset (Fin m)}
    (h : (budgetQuery Q cats succ needs state removed added E cert budget).answer = some L) :
    (chargedState Q state removed added E L).2+(1+L.card^2) ≤
      metadataStateCap (collectRegionalMetadata Q cats succ needs E) E.card+(1+E.card^2) := by
  have hs := (budgetQuery_accepted Q cats succ needs state removed added E cert budget h).1
  have hl := checkMaskedLocal_subset Q (fun x r => x ∈ cats r) succ needs _ _ _ E _ cert hs
  have hd : removed ∪ added ⊆ E := by
    unfold checkMaskedLocal at hs
    split at hs
    next hr => exact checked_region_edits succ (removed ∪ added) E hr
    next => contradiction
  exact Nat.add_le_add
    ((chargedState_bound Q state removed added E L hd hl).trans
      (metadataStateCap_covers Q cats succ needs E))
    (Nat.add_le_add_left (Nat.pow_le_pow_left (Finset.card_le_card hl) 2) 1)

end RAFQueryCompilation
