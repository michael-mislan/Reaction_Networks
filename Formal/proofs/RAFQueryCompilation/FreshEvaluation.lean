import proofs.RAFQueryCompilation.ChargedPruning

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Literal fixed-point baseline, charging each entered closure step and equality test. -/
def freshClosureFuel (Q : CRS M R) (A : Finset R) : ℕ → Finset M → Finset M × ℕ
  | 0, pool => (pool,0)
  | fuel+1, pool =>
    let next := closureStep Q A pool
    let fee := closureTerminalCharge Q A pool
    if next = pool then (pool,fee)
    else
      let tail := freshClosureFuel Q A fuel next
      (tail.1,fee+tail.2)

omit [DecidableEq R] in
theorem freshClosureFuel_refines (Q : CRS M R) (A : Finset R) (fuel : ℕ) (pool : Finset M) :
    (freshClosureFuel Q A fuel pool).1 = settle (closureStep Q A) fuel pool := by
  induction fuel generalizing pool with
  | zero => rfl
  | succ fuel ih =>
    simp only [freshClosureFuel, settle]
    split
    · rfl
    · exact ih _

def freshPruningFuel [Fintype M] (Q : CRS M R) (cats : R → Finset M) :
    ℕ → Finset R → Finset R × ℕ
  | 0, A => (A,0)
  | fuel+1, A =>
    let cl := freshClosureFuel Q A (Fintype.card M) Q.food
    let next := pruneWithPool Q (fun x r => x ∈ cats r) A cl.1
    let fee := Q.food.card+cl.2+supportCharge Q cats A cl.1
    if next = A then (A,fee)
    else
      let tail := freshPruningFuel Q cats fuel next
      (tail.1,fee+tail.2)

theorem freshPruningFuel_refines [Fintype M] (Q : CRS M R) (cats : R → Finset M)
    (fuel : ℕ) (A : Finset R) :
    (freshPruningFuel Q cats fuel A).1 = settle (executablePrune Q (fun x r => x ∈ cats r)) fuel A := by
  induction fuel generalizing A with
  | zero => rfl
  | succ fuel ih =>
    have hp : pruneWithPool Q (fun x r => x ∈ cats r) A
        (freshClosureFuel Q A (Fintype.card M) Q.food).1 =
          executablePrune Q (fun x r => x ∈ cats r) A := by
      rw [freshClosureFuel_refines]
      rfl
    simp only [freshPruningFuel, hp, settle]
    split
    · rfl
    · exact ih _

/-- The initial active-set traversal/copy is included even when pruning fuel is zero. -/
def freshEvaluate [Fintype M] (Q : CRS M R) (cats : R → Finset M) (A : Finset R) :
    Finset R × ℕ :=
  let result := freshPruningFuel Q cats A.card A
  (result.1,A.card+result.2)

theorem freshEvaluate_refines [Fintype M] (Q : CRS M R) (cats : R → Finset M) (A : Finset R) :
    (freshEvaluate Q cats A).1 = evaluate Q (fun x r => x ∈ cats r) A :=
  freshPruningFuel_refines Q cats A.card A

theorem freshEvaluate_reads [Fintype M] (Q : CRS M R) (cats : R → Finset M) (A : Finset R) :
    A.card ≤ (freshEvaluate Q cats A).2 := Nat.le_add_right _ _

end RAFQueryCompilation
