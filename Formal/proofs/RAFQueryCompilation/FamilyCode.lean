import proofs.RAFQueryCompilation.IndexedFamily

namespace RAFQueryCompilation.ModuleFamily

/-- The family relabeling has a fixed arithmetic expression; no enumeration,
search, quotient or remainder operation is needed in the forward direction. -/
theorem reactionCode_pair_value {n : ℕ} (i : Fin n) (b : Bool) :
    (reactionCode n (some (i,b))).val = (if b then 1 else 0)+2*i.val+1 := by
  cases b <;> simp [reactionCode,finProdFinEquiv,finTwoEquiv]

theorem reactionCode_hub_value (n : ℕ) : (reactionCode n none).val = 0 := by
  simp [reactionCode]

/-- Executable forward encoder written directly in arithmetic. Bounds are
proof fields, so they do not require a runtime proof search. -/
def arithmeticReactionCode {n : ℕ} : Reaction n → Fin (n*2+1)
  | none => ⟨0,by omega⟩
  | some (i,b) => ⟨(if b then 1 else 0)+2*i.val+1,by
      have hi := i.isLt
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩

theorem arithmeticReactionCode_eq {n : ℕ} (r : Reaction n) :
    arithmeticReactionCode r = reactionCode n r := by
  cases r with
  | none => apply Fin.ext; exact (reactionCode_hub_value n).symm
  | some r =>
    rcases r with ⟨i,b⟩
    apply Fin.ext
    exact (reactionCode_pair_value i b).symm

end RAFQueryCompilation.ModuleFamily
