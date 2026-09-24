import proofs.RAFQueryCompilation.FreshQuery

namespace RAFQueryCompilation
open RAF

/-- A decoded proposal is tried within budget. Fresh evaluation runs only after
rejection, against the original unchanged state. One unit pays branch dispatch. -/
def hybridQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ) :
    QueryState n m × ℕ :=
  let attempt := budgetQuery Q cats succ needs state removed added E cert budget
  match attempt.answer with
  | none =>
    let baseline := freshQuery Q cats state removed added
    (baseline.1,attempt.charge+1+baseline.2)
  | some _ => (attempt.state,attempt.charge+1)

theorem hybridQuery_bound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) (budget : ℕ) :
    (hybridQuery Q cats succ needs state removed added E cert budget).2 ≤
      budget+1+(freshQuery Q cats state removed added).2 := by
  have hb := budgetQuery_bound Q cats succ needs state removed added E cert budget
  dsimp only [hybridQuery]
  split <;> simp only [] <;> omega

/-- Choosing the reaction-universe size needs no speculative baseline run. -/
theorem hybridQuery_competitive {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (cert : List (List (Fin m))) :
    (hybridQuery Q cats succ needs state removed added E cert m).2 ≤
      2*(freshQuery Q cats state removed added).2+1 := by
  have hb := hybridQuery_bound Q cats succ needs state removed added E cert m
  have hr := freshQuery_reads Q cats state removed added
  omega

theorem hybridQuery_state_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n))
    (hi : IndexSound Q (fun x r => x ∈ cats r) succ)
    (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (A removed added E : Finset (Fin m)) (state : QueryState n m)
    (cert : List (List (Fin m))) (budget : ℕ)
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x) :
    (∀ r, (hybridQuery Q cats succ needs state removed added E cert budget).1.answer[r.val] = true ↔
      r ∈ evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) ∧
    (∀ x, (hybridQuery Q cats succ needs state removed added E cert budget).1.counts[x.val] =
      producerCount Q (evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) x) ∧
    (∀ r, (hybridQuery Q cats succ needs state removed added E cert budget).1.available[r.val] = true ↔
      r ∈ (A \ removed) ∪ added) := by
  cases h : (budgetQuery Q cats succ needs state removed added E cert budget).answer with
  | none =>
    simp only [hybridQuery, h]
    exact freshQuery_state_correct Q cats state A removed added ha
  | some L =>
    simp only [hybridQuery, h]
    exact budgetQuery_state_correct Q cats succ needs hi hn A removed added E state cert budget ho ha hc h

end RAFQueryCompilation
