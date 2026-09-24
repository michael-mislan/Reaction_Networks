import proofs.RAFQueryCompilation.BudgetClosure
import proofs.RAFQueryCompilation.ChargedPruning

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

def supportCap (e i c p : ℕ) : ℕ := 1+e*((i+c+2)*(p+1))+2*(e+1)^2

omit [DecidableEq R] in
theorem supportCap_covers_charge (Q : CRS M R) (cats : R → Finset M)
    (A : Finset R) (pool : Finset M) (i c : ℕ)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i) (hc : ∀ r ∈ A, (cats r).card ≤ c) :
    supportCharge Q cats A pool ≤ supportCap A.card i c pool.card :=
  supportCharge_le Q cats A pool A.card i c pool.card (Nat.le_refl _) (Nat.le_refl _) hi hc

def cappedPruning (Q : CRS M R) (cats : R → Finset M) (i o c : ℕ) :
    Finset R → List (List R) → Option (Finset R) × ℕ
  | _, [] => (none,0)
  | A, order::rest =>
    let cl := cappedClosure Q A order i o
    match cl.1 with
    | none => (none,cl.2)
    | some pool =>
      let T := pruneWithPool Q (fun x r => x ∈ cats r) A pool
      let fee := cl.2+supportCap A.card i c pool.card
      if T=A then (some A,fee) else
        let tail := cappedPruning Q cats i o c T rest
        (tail.1,fee+tail.2)

def budgetPruning (Q : CRS M R) (cats : R → Finset M) (i o c : ℕ) :
    Finset R → List (List R) → ℕ → Option (Finset R) × ℕ
  | _, [], _ => (none,0)
  | A, order::rest, budget =>
    let cl := budgetClosure Q A order i o budget
    match cl.1 with
    | none => (none,cl.2)
    | some pool =>
      let fee := cl.2+supportCap A.card i c pool.card
      if fee ≤ budget then
        let T := pruneWithPool Q (fun x r => x ∈ cats r) A pool
        if T=A then (some A,fee) else
          let tail := budgetPruning Q cats i o c T rest (budget-fee)
          (tail.1,fee+tail.2)
      else (none,cl.2)

theorem budgetPruning_bound (Q : CRS M R) (cats : R → Finset M) (i o c : ℕ)
    (A : Finset R) (cert : List (List R)) (budget : ℕ) :
    (budgetPruning Q cats i o c A cert budget).2 ≤ budget := by
  induction cert generalizing A budget with
  | nil => simp [budgetPruning]
  | cons order rest ih =>
    have hc := budgetClosure_bound Q A order i o budget
    dsimp only [budgetPruning]
    cases hcl : (budgetClosure Q A order i o budget).1 with
    | none => exact hc
    | some pool =>
      simp only []
      split
      · split
        · simp only []; omega
        · have ht := ih (pruneWithPool Q (fun x r => x ∈ cats r) A pool)
            (budget-((budgetClosure Q A order i o budget).2+supportCap A.card i c pool.card))
          simp only []
          omega
      · exact hc

theorem budgetPruning_refines (Q : CRS M R) (cats : R → Finset M) (i o c : ℕ)
    (A : Finset R) (cert : List (List R)) (budget : ℕ) {answer : Finset R}
    (h : (budgetPruning Q cats i o c A cert budget).1 = some answer) :
    checkPruning Q (fun x r => x ∈ cats r) A cert = some answer := by
  induction cert generalizing A budget with
  | nil => simp [budgetPruning] at h
  | cons order rest ih =>
    dsimp only [budgetPruning] at h
    cases hcl : (budgetClosure Q A order i o budget).1 with
    | none => simp [hcl] at h
    | some pool =>
      simp only [hcl] at h
      have hc := budgetClosure_refines Q A order i o budget hcl
      dsimp only [checkPruning]
      rw [hc]
      dsimp only
      split at h
      · split at h
        · rename_i he
          rw [if_pos he]
          exact h
        · rename_i he
          rw [if_neg he]
          exact ih _ _ h
      · simp at h

theorem cappedPruning_refines (Q : CRS M R) (cats : R → Finset M) (i o c : ℕ)
    (cert : List (List R)) (A : Finset R) :
    (cappedPruning Q cats i o c A cert).1 = checkPruning Q (fun x r => x ∈ cats r) A cert := by
  induction cert generalizing A with
  | nil => rfl
  | cons order rest ih =>
    simp only [cappedPruning, cappedClosure_refines, checkPruning]
    cases hc : checkClosure Q A order with
    | none => rfl
    | some pool =>
      by_cases he : pruneWithPool Q (fun x r => x ∈ cats r) A pool = A
      · simp [he]
      · simp [he, ih]

theorem budgetPruning_complete (Q : CRS M R) (cats : R → Finset M) (i o c : ℕ)
    (A : Finset R) (cert : List (List R)) (budget : ℕ)
    (h : (cappedPruning Q cats i o c A cert).2 ≤ budget) :
    budgetPruning Q cats i o c A cert budget = cappedPruning Q cats i o c A cert := by
  induction cert generalizing A budget with
  | nil => rfl
  | cons order rest ih =>
    cases hcl : (cappedClosure Q A order i o).1 with
    | none =>
      have hc : (cappedClosure Q A order i o).2 ≤ budget := by
        simpa only [cappedPruning, hcl] using h
      have hb := budgetClosure_complete Q A order i o budget hc
      simp only [budgetPruning, hb, hcl, cappedPruning]
    | some pool =>
      have hf : (cappedClosure Q A order i o).2+supportCap A.card i c pool.card ≤ budget := by
        have hl : (cappedClosure Q A order i o).2+supportCap A.card i c pool.card ≤
            (cappedPruning Q cats i o c A (order::rest)).2 := by
          by_cases he : pruneWithPool Q (fun x r => x ∈ cats r) A pool = A <;>
            simp [cappedPruning, hcl, he]
        exact hl.trans h
      have hc : (cappedClosure Q A order i o).2 ≤ budget := by omega
      have hb := budgetClosure_complete Q A order i o budget hc
      simp only [budgetPruning, hb, hcl, if_pos hf]
      by_cases he : pruneWithPool Q (fun x r => x ∈ cats r) A pool = A
      · simp [he, cappedPruning, hcl]
      · have ht : (cappedPruning Q cats i o c
            (pruneWithPool Q (fun x r => x ∈ cats r) A pool) rest).2 ≤
            budget-((cappedClosure Q A order i o).2+supportCap A.card i c pool.card) := by
          simp only [cappedPruning, hcl, if_neg he] at h
          omega
        have tail := ih _ _ ht
        simp only [if_neg he, tail, cappedPruning, hcl]

end RAFQueryCompilation
