import proofs.FiniteCopyReactor.StateMarks

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped BigOperators NNReal
set_option maxHeartbeats 30000

theorem bernoulli_mark_step {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (hm : ∀ j, P.mark j=0 ∨ P.mark j=1) (p s : ℝ) (hs : 0 ≤ s)
    (hmean : ∀ x, (∑ j,P.prob x j*P.mark j) ≤ p) (x : α) (z : ℝ) :
    P.step (fun _ w => Real.exp (s*w)) x z ≤ (1+p*(Real.exp s-1))*Real.exp (s*z) := by
  have he (j) : Real.exp (s*P.mark j)=1+P.mark j*(Real.exp s-1) := by
    rcases hm j with h|h <;> simp [h]
  have hrow : (∑ j,P.prob x j*Real.exp (s*P.mark j)) ≤ 1+p*(Real.exp s-1) := by
    simp only [he,mul_add,mul_one,Finset.sum_add_distrib]
    rw [P.row_sum]
    have ht : (∑ j,P.prob x j*(P.mark j*(Real.exp s-1))) =
        (∑ j,P.prob x j*P.mark j)*(Real.exp s-1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [ht]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hmean x)
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hs)))
  have hex : P.step (fun _ w => Real.exp (s*w)) x z =
      (∑ j,P.prob x j*Real.exp (s*P.mark j))*Real.exp (s*z) := by
    unfold MarkedKernel.step
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only
    rw [mul_add,Real.exp_add]
    ring
  rw [hex]
  exact mul_le_mul_of_nonneg_right hrow (Real.exp_pos _).le

theorem marked_bounded_poisson {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f : α → ℝ → ℝ) (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ 1)
    (t : ℝ≥0) (x : α) (z : ℝ) :
    0 ≤ P.poissonized t f x z ∧ P.poissonized t f x z ≤ 1 := by
  have hlo (n) : 0 ≤ P.law n f x z := by
    have h := P.law_mono _ _ (fun y w => (hf y w).1) n x z
    simpa only [P.law_const] using h
  have hhi (n) : P.law n f x z ≤ 1 := by
    have h := P.law_mono _ _ (fun y w => (hf y w).2) n x z
    simpa only [P.law_const] using h
  have hs : Summable (fun n => poissonWeight t n*P.law n f x z) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (poissonWeight_nonneg t n) (hlo n))
      (fun n => mul_le_of_le_one_right (poissonWeight_nonneg t n) (hhi n)) (poissonWeight_sum t).summable
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (poissonWeight_nonneg t n) (hlo n))
  · exact (Summable.tsum_le_tsum (fun n => mul_le_of_le_one_right (poissonWeight_nonneg t n) (hhi n))
      hs (poissonWeight_sum t).summable).trans_eq (poissonWeight_sum t).tsum_eq

theorem marked_exponential_domination {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f : α → ℝ → ℝ) (hf : ∀ x z, 0 ≤ f x z ∧ f x z ≤ 1) (c s rho : ℝ)
    (hc : 0 ≤ c) (hrho : 0 ≤ rho) (hdom : ∀ x z, f x z ≤ c*Real.exp (s*z))
    (hstep : ∀ x z, P.step (fun _ w => Real.exp (s*w)) x z ≤ rho*Real.exp (s*z))
    (t : ℝ≥0) (x : α) (z : ℝ) :
    P.poissonized t f x z ≤ c*Real.exp ((t:ℝ)*(rho-1))*Real.exp (s*z) := by
  have hb (n) : P.law n f x z ≤ c*(rho^n*Real.exp (s*z)) := by
    have hh := P.law_mono _ _ hdom n x z
    rw [P.law_scale] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (P.law_decay _ rho hrho hstep n x z) hc)
  have hs : HasSum (fun n => poissonWeight t n*(c*(rho^n*Real.exp (s*z))))
      (c*Real.exp ((t:ℝ)*(rho-1))*Real.exp (s*z)) := by
    convert (poissonWeight_geometric t rho).mul_right (c*Real.exp (s*z)) using 1
    · funext n
      ring
    · ring
  have hnon (n) : 0 ≤ P.law n f x z := by
    have h := P.law_mono _ _ (fun y w => (hf y w).1) n x z
    simpa only [P.law_const] using h
  have hsum := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (hnon n))
    (fun n => mul_le_mul_of_nonneg_left (hb n) (poissonWeight_nonneg t n)) hs.summable
  exact (Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hb n) (poissonWeight_nonneg t n))
    hsum hs.summable).trans_eq hs.tsum_eq

end
end FiniteCopyReactor
