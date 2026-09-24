import proofs.CompositionalMemory.MatrixClockIdentity

namespace CompositionalMemory
open FiniteCopy

/-- The finite reaction law expressed without an auxiliary uniformization clock. -/
noncomputable def finiteTimeExpectation {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (t : NNReal) (f : α → ℝ) (x : α) : ℝ :=
  (NormedSpace.exp ((t : ℝ) • jumpGeneratorMatrix M)).mulVec f x

theorem finite_time_eq_uniformized {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hb : ∀ x, M.total x ≤ q) (f : α → ℝ) (x : α) :
    finiteTimeExpectation M t f x = (M.uniformize q hq hb).poissonized (q*t) f x :=
  (uniformized_law_generator_matrix M q t hq hb f x).symm

theorem finite_time_bounds {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (t : NNReal) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : α) :
    0 ≤ finiteTimeExpectation M t f x ∧ finiteTimeExpectation M t f x ≤ 1 := by
  obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
  rw [finite_time_eq_uniformized M q t hq hb]
  constructor
  · exact FiniteKernel.poissonized_nonneg _ _ _ (fun y => (hf y).1) x
  · have h := (M.uniformize q hq hb).poissonized_mono (q*t) f (fun _ => 1)
      (fun y => (hf y).1) (fun _ => by norm_num) (fun y => (hf y).2) x
    simpa only [FiniteKernel.poissonized_const] using h

end CompositionalMemory
