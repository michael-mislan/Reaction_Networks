import proofs.FiniteCopy.KernelExpectations

namespace ResourceLimitedCompetition
open FiniteCopy
open scoped NNReal

theorem event_indicator_nonneg {α : Type*} (A : Set α) (x : α) :
    0 ≤ FiniteKernel.eventIndicator A x := by
  classical
  unfold FiniteKernel.eventIndicator
  split_ifs <;> norm_num

theorem poissonized_finset_sum {α ι : Type*} [Fintype α] (P : FiniteKernel α)
    (t : ℝ≥0) (I : Finset ι) (f : ι → α → ℝ) (hf : ∀ i x, 0 ≤ f i x) (x : α) :
    P.poissonized t (fun y => ∑ i ∈ I, f i y) x = ∑ i ∈ I, P.poissonized t (f i) x := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using P.poissonized_const t 0 x
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    rw [P.poissonized_add t (f i) (fun y => ∑ j ∈ I, f j y) (hf i)
      (fun y => Finset.sum_nonneg (fun j _ => hf j y)),ih]

theorem poissonized_event_cover {α ι : Type*} [Fintype α] [Fintype ι]
    (P : FiniteKernel α) (t : ℝ≥0) (A : Set α) (B : ι → Set α)
    (hcover : ∀ x ∈ A, ∃ i, x ∈ B i) (x : α) :
    P.poissonized t (FiniteKernel.eventIndicator A) x ≤
      ∑ i, P.poissonized t (FiniteKernel.eventIndicator (B i)) x := by
  classical
  have hn (y : α) : 0 ≤ ∑ i, FiniteKernel.eventIndicator (B i) y :=
    Finset.sum_nonneg (fun i _ => event_indicator_nonneg _ _)
  have hp (y : α) : FiniteKernel.eventIndicator A y ≤ ∑ i, FiniteKernel.eventIndicator (B i) y := by
    by_cases hy : y ∈ A
    · obtain ⟨i,hi⟩ := hcover y hy
      have h := Finset.single_le_sum (fun j _ => event_indicator_nonneg (B j) y) (Finset.mem_univ i)
      simpa only [FiniteKernel.eventIndicator,if_pos hy,if_pos hi] using h
    · simpa only [FiniteKernel.eventIndicator,if_neg hy] using hn y
  have h := P.poissonized_mono t _ _ (event_indicator_nonneg A) hn hp x
  rw [poissonized_finset_sum P t Finset.univ (fun i => FiniteKernel.eventIndicator (B i))
    (fun i => event_indicator_nonneg (B i))] at h
  exact h

theorem probability_complement_lower {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : ℝ≥0) (A : Set α) (e : ℝ) (x : α)
    (h : P.poissonized t (FiniteKernel.eventIndicator Aᶜ) x ≤ e) :
    1-e ≤ P.poissonized t (FiniteKernel.eventIndicator A) x := by
  classical
  have hfun : (fun y => FiniteKernel.eventIndicator Aᶜ y+FiniteKernel.eventIndicator A y)=(fun _ => 1) := by
    funext y
    simp only [FiniteKernel.eventIndicator,Set.mem_compl_iff]
    split_ifs <;> norm_num
  have hs := P.poissonized_add t (FiniteKernel.eventIndicator Aᶜ) (FiniteKernel.eventIndicator A)
    (event_indicator_nonneg Aᶜ) (event_indicator_nonneg A) x
  rw [hfun,P.poissonized_const] at hs
  linarith only [hs,h]

end ResourceLimitedCompetition
