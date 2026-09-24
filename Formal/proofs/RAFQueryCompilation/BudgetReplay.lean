import proofs.RAFQueryCompilation.ChargedReplay

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Reserve membership, subset testing and union separately, before each probe.
An abort may have paid earlier probes but never performs an unpaid union. -/
def budgetScheduleStep (Q : CRS M R) (A : Finset R) (pool : Finset M)
    (r : R) (budget : ℕ) : Option (Finset M) × ℕ :=
  let m := 1+A.card
  if m ≤ budget then
    if r ∈ A then
      let t := ((Q.inputs r).card+1)*(pool.card+1)
      if m+t ≤ budget then
        if Q.inputs r ⊆ pool then
          let u := (pool.card+(Q.outputs r).card+1)^2
          if m+t+u ≤ budget then (some (pool ∪ Q.outputs r),m+t+u)
          else (none,m+t)
        else (some pool,m+t)
      else (none,m)
    else (some pool,m)
  else (none,0)

theorem budgetScheduleStep_bound (Q : CRS M R) (A : Finset R) (pool : Finset M)
    (r : R) (budget : ℕ) : (budgetScheduleStep Q A pool r budget).2 ≤ budget := by
  dsimp only [budgetScheduleStep]
  split_ifs <;> dsimp only <;> omega

theorem budgetScheduleStep_refines (Q : CRS M R) (A : Finset R) (pool : Finset M)
    (r : R) (budget : ℕ) {out : Finset M}
    (h : (budgetScheduleStep Q A pool r budget).1 = some out) :
    out = scheduleStep Q A pool r := by
  dsimp only [budgetScheduleStep] at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · simp_all [scheduleStep]
          · simp at h
        · simp_all [scheduleStep]
      · simp at h
    · simp_all [scheduleStep]
  · simp at h

theorem budgetScheduleStep_complete (Q : CRS M R) (A : Finset R) (pool : Finset M)
    (r : R) (budget : ℕ) (h : replayStepCharge Q A pool r ≤ budget) :
    budgetScheduleStep Q A pool r budget =
      (some (scheduleStep Q A pool r), replayStepCharge Q A pool r) := by
  by_cases hr : r ∈ A
  · by_cases hi : Q.inputs r ⊆ pool
    · simp only [replayStepCharge, if_pos hr, if_pos hi] at h
      have hm : 1+A.card ≤ budget := by omega
      have ht : 1+A.card+((Q.inputs r).card+1)*(pool.card+1) ≤ budget := by omega
      have hu : 1+A.card+((Q.inputs r).card+1)*(pool.card+1)+
          (pool.card+(Q.outputs r).card+1)^2 ≤ budget := by omega
      simp only [budgetScheduleStep, if_pos hm, if_pos hr, if_pos ht, if_pos hi, if_pos hu]
      simp [scheduleStep, replayStepCharge, hr, hi, Nat.add_assoc]
    · simp only [replayStepCharge, if_pos hr, if_neg hi, Nat.add_zero] at h
      have hm : 1+A.card ≤ budget := by omega
      simp [budgetScheduleStep, scheduleStep, replayStepCharge, hr, hi, hm, h]
  · simp only [replayStepCharge, if_neg hr, Nat.add_zero] at h
    simp [budgetScheduleStep, scheduleStep, replayStepCharge, hr, h]

def budgetReplayFrom (Q : CRS M R) (A : Finset R) :
    List R → Finset M → ℕ → Option (Finset M) × ℕ
  | [], pool, _ => (some pool,0)
  | r::rs, pool, budget =>
    let step := budgetScheduleStep Q A pool r budget
    match step.1 with
    | none => (none,step.2)
    | some next =>
      let tail := budgetReplayFrom Q A rs next (budget-step.2)
      (tail.1,step.2+tail.2)

theorem budgetReplay_bound (Q : CRS M R) (A : Finset R) (order : List R)
    (pool : Finset M) (budget : ℕ) : (budgetReplayFrom Q A order pool budget).2 ≤ budget := by
  induction order generalizing pool budget with
  | nil => simp [budgetReplayFrom]
  | cons r rs ih =>
    have hs := budgetScheduleStep_bound Q A pool r budget
    dsimp only [budgetReplayFrom]
    cases h : (budgetScheduleStep Q A pool r budget).1 with
    | none => exact hs
    | some next =>
      have ht := ih next (budget-(budgetScheduleStep Q A pool r budget).2)
      dsimp only
      omega

theorem budgetReplay_refines (Q : CRS M R) (A : Finset R) (order : List R)
    (pool : Finset M) (budget : ℕ) {out : Finset M}
    (h : (budgetReplayFrom Q A order pool budget).1 = some out) :
    out = order.foldl (scheduleStep Q A) pool := by
  induction order generalizing pool budget with
  | nil => simpa [budgetReplayFrom] using h.symm
  | cons r rs ih =>
    dsimp only [budgetReplayFrom] at h
    cases hs : (budgetScheduleStep Q A pool r budget).1 with
    | none => simp [hs] at h
    | some next =>
      simp only [hs] at h
      have hn := budgetScheduleStep_refines Q A pool r budget hs
      simpa [List.foldl_cons, hn] using ih next _ h

theorem budgetReplay_complete (Q : CRS M R) (A : Finset R) (order : List R)
    (pool : Finset M) (budget : ℕ)
    (h : (chargedReplayFrom Q A order pool).2 ≤ budget) :
    budgetReplayFrom Q A order pool budget =
      (some (chargedReplayFrom Q A order pool).1, (chargedReplayFrom Q A order pool).2) := by
  induction order generalizing pool budget with
  | nil => rfl
  | cons r rs ih =>
    have hs : replayStepCharge Q A pool r ≤ budget := by
      dsimp only [chargedReplayFrom] at h
      omega
    have ht : (chargedReplayFrom Q A rs (scheduleStep Q A pool r)).2 ≤
        budget-replayStepCharge Q A pool r := by
      dsimp only [chargedReplayFrom] at h
      omega
    have step := budgetScheduleStep_complete Q A pool r budget hs
    have tail := ih (scheduleStep Q A pool r) (budget-replayStepCharge Q A pool r) ht
    dsimp only [budgetReplayFrom]
    rw [step]
    dsimp only
    rw [tail]
    rfl

end RAFQueryCompilation
