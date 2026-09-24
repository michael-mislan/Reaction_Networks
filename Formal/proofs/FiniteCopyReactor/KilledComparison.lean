import proofs.FiniteCopyReactor.ResidencePhase

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical

/-- Freezing can increase an unrestricted event. The terminal active mask is
essential: only paths that have not reached the additional stop are compared. -/
theorem killed_steps_comparison {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (active : α → Prop) (hQ : ∀ f x, Q.step f x = if active x then P.step f x else f x)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : α) :
    Q.steps n (fun y => if active y then f y else 0) x ≤ P.steps n f x := by
  have hz (n : ℕ) (x : α) (hx : ¬active x) :
      Q.steps n (fun y => if active y then f y else 0) x=0 := by
    induction n with
    | zero => simp only [FiniteKernel.steps,if_neg hx]
    | succ n ih => simpa only [FiniteKernel.steps,hQ,if_neg hx] using ih
  induction n generalizing x with
  | zero =>
    change (if active x then f x else 0) ≤ f x
    split_ifs
    · exact le_rfl
    · exact hf x
  | succ n ih =>
    by_cases hx : active x
    · change Q.step (Q.steps n (fun y => if active y then f y else 0)) x ≤ P.step (P.steps n f) x
      rw [hQ,if_pos hx]
      exact P.step_mono ih x
    · rw [hz (n+1) x hx]
      have h := P.steps_mono hf (n+1) x
      simpa only [P.steps_const] using h

end
end FiniteCopyReactor
