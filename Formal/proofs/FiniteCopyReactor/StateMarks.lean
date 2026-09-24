import proofs.FiniteCopy.MarkedMarginal

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped BigOperators

/-- Retain the source state in a zero-redundancy label to allow a predictable
state-dependent mark. Only labels whose source equals the current state carry mass. -/
def stateMarks {α β : Type*} [Fintype α] [Fintype β] (P : MarkedKernel α β)
    (m : α → β → ℝ) : MarkedKernel α (α × β) where
  prob x j := if j.1=x then P.prob x j.2 else 0
  next x j := P.next x j.2
  mark j := m j.1 j.2
  nonneg x j := by split_ifs; exact P.nonneg x j.2; rfl
  row_sum x := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simpa using P.row_sum x

theorem state_marks_step {α β : Type*} [Fintype α] [Fintype β] (P : MarkedKernel α β)
    (m : α → β → ℝ) (f : α → ℝ → ℝ) (x : α) (z : ℝ) :
    (stateMarks P m).step f x z = ∑ j,P.prob x j*f (P.next x j) (z+m x j) := by
  unfold MarkedKernel.step
  rw [Fintype.sum_prod_type]
  simp [stateMarks,ite_mul]

theorem state_marks_marginal {α β : Type*} [Fintype α] [Fintype β] (P : MarkedKernel α β)
    (m : α → β → ℝ) (f : α → ℝ) (x : α) (z : ℝ) :
    (stateMarks P m).step (fun y _ => f y) x z=P.step (fun y _ => f y) x z := by
  rw [state_marks_step]
  rfl

theorem state_marks_identity_step {α β : Type*} [Fintype α] [Fintype β] (P : MarkedKernel α β)
    (b : α → ℝ) (x : α) (z : ℝ) :
    (stateMarks P (fun y _ => b y)).step (fun _ w => w) x z=z+b x := by
  rw [state_marks_step]
  simp only [← Finset.sum_mul,P.row_sum,one_mul]

/-- Monotonicity on nonnegative counters suffices for actual nonnegative marks. -/
theorem marked_law_nonnegative_mono {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (hm : ∀ j, 0 ≤ P.mark j) (f g : α → ℝ → ℝ)
    (hfg : ∀ x z, 0 ≤ z → f x z ≤ g x z) (n : ℕ) (x : α) (z : ℝ) (hz : 0 ≤ z) :
    P.law n f x z ≤ P.law n g x z := by
  induction n generalizing x z with
  | zero => exact hfg x z hz
  | succ n ih =>
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (ih _ _ (add_nonneg hz (hm j))) (P.nonneg x j)

theorem marked_count_markov {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (hm : ∀ j, 0 ≤ P.mark j) (a : ℝ) (n : ℕ) (x : α) :
    a*P.law n (MarkedKernel.eventIndicator {s | a ≤ s.2}) x 0 ≤
      P.law n (fun _ w => w) x 0 := by
  rw [← P.law_scale]
  apply marked_law_nonnegative_mono P hm _ _ _ n x 0 (by norm_num)
  intro y z hz
  unfold MarkedKernel.eventIndicator
  split_ifs with h
  · simpa using h
  · simpa using hz

end
end FiniteCopyReactor
