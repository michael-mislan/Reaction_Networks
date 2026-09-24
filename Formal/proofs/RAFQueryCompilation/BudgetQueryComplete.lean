import proofs.RAFQueryCompilation.BudgetQueryState

namespace RAFQueryCompilation
open RAF

def querySourceCap {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (removed added E : Finset (Fin m))
    (cert : List (List (Fin m))) : ℕ :=
  editPrepCharge removed added+localSourceCap Q cats succ needs (removed ∪ added) E cert+
    metadataCharge E+metadataStateCap (collectRegionalMetadata Q cats succ needs E) E.card+
    (1+E.card^2)

/-- Sufficient source budget guarantees the accepted query, not just safety on success. -/
theorem budgetQuery_source_complete {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ)
    (hb : querySourceCap Q cats succ needs removed added E cert ≤ budget)
    {L : Finset (Fin m)}
    (h : checkMaskedLocal Q (fun x r => x ∈ cats r) succ needs (fun r => state.answer[r.val])
      (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
      (fun x => state.counts[x.val]) cert = some L) :
    (budgetQuery Q cats succ needs state removed added E cert budget).answer = some L := by
  have hp : editPrepCharge removed added ≤ budget := by
    unfold querySourceCap at hb
    omega
  have hl : localSourceCap Q cats succ needs (removed ∪ added) E cert ≤
      budget-editPrepCharge removed added := by
    unfold querySourceCap at hb
    omega
  have hc := budgetLocal_source_complete Q cats succ needs (fun r => state.answer[r.val])
    (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
    (fun x => state.counts[x.val]) cert (budget-editPrepCharge removed added) hl
  have hfee := cappedLocal_source_bound Q cats succ needs (fun r => state.answer[r.val])
    (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
    (fun x => state.counts[x.val]) cert
  have hm : editPrepCharge removed added+
      (cappedLocal Q cats succ needs (fun r => state.answer[r.val])
        (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
        (fun x => state.counts[x.val]) cert).2+metadataCharge E ≤ budget := by
    unfold querySourceCap at hb
    omega
  have hf : editPrepCharge removed added+
      (cappedLocal Q cats succ needs (fun r => state.answer[r.val])
        (editedMask (fun r => state.available[r.val]) removed added) (removed ∪ added) E
        (fun x => state.counts[x.val]) cert).2+metadataCharge E+
        metadataStateCap (collectRegionalMetadata Q cats succ needs E) E.card+(1+E.card^2) ≤ budget := by
    unfold querySourceCap at hb
    omega
  simp only [budgetQuery, if_pos hp, hc, cappedLocal_refines, h, if_pos hm, if_pos hf]

end RAFQueryCompilation
