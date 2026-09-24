import proofs.RAFQueryCompilation.SupportPruning
import proofs.RAFQueryCompilation.HybridQuery

namespace RAFQueryCompilation
open RAF

def fastRebuildState {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (available answer : Finset (Fin m)) : QueryState n m :=
  { answer := patchVector (Vector.replicate m false) answer (fun _ => true)
    available := patchVector (Vector.replicate m false) available (fun _ => true)
    counts := sourceCounts Q answer }

def supportFallback {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added : Finset (Fin m)) (cert : List (SupportRound m)) : Option (QueryState n m) :=
  let B := freshAvailable state removed added
  (checkSupportPruning Q cats B cert).map (fastRebuildState Q B)

theorem supportFallback_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state next : QueryState n m)
    (A removed added : Finset (Fin m)) (cert : List (SupportRound m))
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (h : supportFallback Q cats state removed added cert = some next) :
    (∀ r, next.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) ∧
    (∀ x, next.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) x) ∧
    (∀ r, next.available[r.val] = true ↔ r ∈ (A \ removed) ∪ added) := by
  unfold supportFallback at h
  cases hs : checkSupportPruning Q cats (freshAvailable state removed added) cert with
  | none => simp [hs] at h
  | some answer =>
    simp only [hs,Option.map_some,Option.some.injEq] at h
    subst next
    have he := checkSupportPruning_sound Q cats cert _ hs
    rw [freshAvailable_correct state A removed added ha] at he ⊢
    simp [fastRebuildState,patchVector_get,sourceCounts_correct,he]

/-- Fast certified fallback is optional; a rejected certificate retains exact fresh fallback. -/
def supportHybridQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n)) (state : QueryState n m)
    (removed added E : Finset (Fin m)) (localCert : List (List (Fin m)))
    (fallbackCert : List (SupportRound m)) (budget : ℕ) : QueryState n m :=
  let attempt := budgetQuery Q cats succ needs state removed added E localCert budget
  match attempt.answer with
  | some _ => attempt.state
  | none =>
    match supportFallback Q cats state removed added fallbackCert with
    | some next => next
    | none => (freshQuery Q cats state removed added).1

theorem supportHybridQuery_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (succ : Fin m → Finset (Fin m))
    (needs : Fin m → Finset (Fin n))
    (hi : IndexSound Q (fun x r => x ∈ cats r) succ)
    (hn : NeedsSound Q (fun x r => x ∈ cats r) needs)
    (state : QueryState n m) (A removed added E : Finset (Fin m))
    (localCert : List (List (Fin m))) (fallbackCert : List (SupportRound m)) (budget : ℕ)
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (hc : ∀ x, state.counts[x.val] = producerCount Q (evaluate Q (fun x r => x ∈ cats r) A) x) :
    (∀ r, (supportHybridQuery Q cats succ needs state removed added E localCert fallbackCert budget).answer[r.val] = true ↔
      r ∈ evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) ∧
    (∀ x, (supportHybridQuery Q cats succ needs state removed added E localCert fallbackCert budget).counts[x.val] =
      producerCount Q (evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added)) x) ∧
    (∀ r, (supportHybridQuery Q cats succ needs state removed added E localCert fallbackCert budget).available[r.val] = true ↔
      r ∈ (A \ removed) ∪ added) := by
  cases hb : (budgetQuery Q cats succ needs state removed added E localCert budget).answer with
  | some L =>
    simp only [supportHybridQuery,hb]
    exact budgetQuery_state_correct Q cats succ needs hi hn A removed added E state localCert budget ho ha hc hb
  | none =>
    cases hs : supportFallback Q cats state removed added fallbackCert with
    | some next =>
      simp only [supportHybridQuery,hb,hs]
      exact supportFallback_correct Q cats state next A removed added fallbackCert ha hs
    | none =>
      simp only [supportHybridQuery,hb,hs]
      exact freshQuery_state_correct Q cats state A removed added ha

end RAFQueryCompilation
