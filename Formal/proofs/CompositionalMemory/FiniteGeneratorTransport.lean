import proofs.CompositionalMemory.FiniteDeadlineCertificate

namespace CompositionalMemory
open FiniteCopy

theorem finite_time_generator_congr {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    [DecidableEq α] (M : FiniteJumpModel α β) (N : FiniteJumpModel α δ)
    (hgen : ∀ f x, M.generator f x=N.generator f x)
    (t : NNReal) (f : α → ℝ) (x : α) :
    finiteTimeExpectation M t f x=finiteTimeExpectation N t f x := by
  obtain ⟨qN,hqN,_,hbN⟩ := N.exists_clock 0
  obtain ⟨q,hq,hqNq,hbM⟩ := M.exists_clock qN
  have hbN' (z : α) : N.total z ≤ q := (hbN z).trans hqNq
  let P := M.uniformize q hq hbM
  let Q := N.uniformize q hq hbN'
  have hs (g : α → ℝ) (z : α) : P.step g z=Q.step g z := by
    simp only [P,Q,FiniteJumpModel.uniformize_step,hgen]
  have hn (n : Nat) (z : α) : P.steps n f z=Q.steps n f z := by
    induction n generalizing z with
    | zero => rfl
    | succ n ih =>
      change P.step (P.steps n f) z=Q.step (Q.steps n f) z
      rw [show P.steps n f=Q.steps n f from funext ih]
      exact hs _ z
  rw [finite_time_eq_uniformized M q t hq hbM,finite_time_eq_uniformized N q t hq hbN']
  change P.poissonized (q*t) f x=Q.poissonized (q*t) f x
  unfold FiniteKernel.poissonized
  exact tsum_congr (fun n => congrArg (fun z => poissonWeight (q*t) n*z) (hn n x))

theorem finite_time_mono {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (t : NNReal) (f g : α → ℝ)
    (h : ∀ x, f x ≤ g x) (x : α) :
    finiteTimeExpectation M t f x ≤ finiteTimeExpectation M t g x := by
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  rw [finite_time_eq_uniformized M q t hq hb,finite_time_eq_uniformized M q t hq hb]
  exact HeritableCompositions.poisson_mono _ _ f g h x

end CompositionalMemory
