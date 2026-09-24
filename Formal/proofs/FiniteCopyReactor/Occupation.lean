import proofs.FiniteCopyReactor.StateMarks
import proofs.RandomViability.BindingEntrySchedule
import proofs.FiniteCopy.KernelExpectations

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy RandomViability.Binding Classical
open scoped BigOperators

def occupationMean {α : Type*} [Fintype α] (R : FiniteKernel α) (b : α → ℝ)
    (n : ℕ) (x : α) : ℝ := ∑ k ∈ Finset.range n,R.steps k b x

theorem occupation_mean_succ {α : Type*} [Fintype α] (R : FiniteKernel α) (b : α → ℝ)
    (n : ℕ) (x : α) : occupationMean R b (n+1) x=b x+R.step (occupationMean R b n) x := by
  unfold occupationMean
  rw [Finset.sum_range_succ']
  simp only [FiniteKernel.steps]
  unfold FiniteKernel.step
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  ring

theorem occupation_law_mean {α β : Type*} [Fintype α] [Fintype β]
    (P : MarkedKernel α β) (R : FiniteKernel α)
    (hR : ∀ f x z, P.step (fun y _ => f y) x z=R.step f x)
    (b : α → ℝ) (n : ℕ) (x : α) (z : ℝ) :
    (stateMarks P (fun y _ => b y)).law n (fun _ w => w) x z=z+occupationMean R b n x := by
  induction n generalizing x z with
  | zero => simp [MarkedKernel.law,occupationMean]
  | succ n ih =>
    change (stateMarks P (fun y _ => b y)).step _ x z=_
    rw [state_marks_step]
    simp only [ih,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,P.row_sum,one_mul]
    have he := hR (occupationMean R b n) x z
    change (∑ j,P.prob x j*occupationMean R b n (P.next x j))=_ at he
    rw [he,occupation_mean_succ]
    ring

theorem occupation_after_burnin {α : Type*} [Fintype α] (R : FiniteKernel α)
    (b : α → ℝ) (L m n : ℕ) (hm : L ≤ m) (e : ℝ)
    (he : ∀ k, L ≤ k → ∀ x, R.steps k b x ≤ e) (x : α) :
    R.steps m (occupationMean R b n) x ≤ (n:ℝ)*e := by
  have hsum : R.steps m (occupationMean R b n) x =
      ∑ k ∈ Finset.range n,R.steps (m+k) b x := by
    induction n with
    | zero =>
      simp only [Finset.range_zero,Finset.sum_empty]
      have heq : occupationMean R b 0 = fun _ => 0 := by funext y; simp [occupationMean]
      rw [heq,R.steps_const]
    | succ n ih =>
      have hf : occupationMean R b (n+1) = fun y => occupationMean R b n y+R.steps n b y := by
        funext y
        simp only [occupationMean,Finset.sum_range_succ]
      rw [hf,R.steps_add,ih,← steps_comp,Finset.sum_range_succ]
  rw [hsum]
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => he (m+k) (by omega) x)
  simpa using hh

theorem occupation_markov_after_burnin {α β : Type*} [Fintype α] [Fintype β]
    (P : MarkedKernel α β) (R : FiniteKernel α)
    (hR : ∀ f x z, P.step (fun y _ => f y) x z=R.step f x)
    (b : α → ℝ) (hb : ∀ x, 0 ≤ b x) (L m n : ℕ) (hm : L ≤ m) (e a : ℝ)
    (he : ∀ k, L ≤ k → ∀ x, R.steps k b x ≤ e) (x : α) :
    a*R.steps m (fun y => (stateMarks P (fun z _ => b z)).law n
      (MarkedKernel.eventIndicator {s | a ≤ s.2}) y 0) x ≤ (n:ℝ)*e := by
  have hh (y) := marked_count_markov (stateMarks P (fun z _ => b z))
    (fun j => hb j.1) a n y
  simp only [occupation_law_mean P R hR,zero_add] at hh
  have ht := R.steps_mono hh m x
  rw [R.steps_scale] at ht
  exact ht.trans (occupation_after_burnin R b L m n hm e he x)

end
end FiniteCopyReactor
