import proofs.FiniteCopyReactor.FinitePoissonInterchange

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

theorem poisson_geometric_sequence (t : NNReal) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 1) (a b r : ℝ)
    (h : ∀ n, f n ≤ a+b*r^n) :
    (∑' n,poissonWeight t n*f n) ≤ a+b*Real.exp ((t:ℝ)*(r-1)) := by
  have hs : HasSum (fun n => poissonWeight t n*(a+b*r^n))
      (a+b*Real.exp ((t:ℝ)*(r-1))) := by
    convert ((poissonWeight_sum t).mul_right a).add ((poissonWeight_geometric t r).mul_left b) using 1
    · funext n
      ring
    · ring
  have hsf := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (hf n).1)
    (fun n => mul_le_of_le_one_right (poissonWeight_nonneg t n) (hf n).2) (poissonWeight_sum t).summable
  exact (Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (h n) (poissonWeight_nonneg t n)) hsf hs.summable).trans_eq hs.tsum_eq

theorem finite_poisson_nested_expand {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t u : NNReal) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (x : α) :
    P.poissonized t (fun y => Q.poissonized u f y) x=
      ∑' m,poissonWeight u m*P.poissonized t (Q.steps m f) x := by
  change P.poissonized t (fun y => ∑' m,poissonWeight u m*Q.steps m f y) x = _
  rw [finite_poisson_tsum P _ (fun y => Q.nonneg_summable u f hf y)]
  simp only [P.poissonized_scale]

theorem finite_two_clock_geometric {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t u : NNReal) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (a b r : ℝ) (x : α)
    (h : ∀ n m, P.steps n (Q.steps m f) x ≤ a+b*r^(n+m)) :
    P.poissonized t (fun y => Q.poissonized u f y) x ≤ a+b*Real.exp (((t:ℝ)+(u:ℝ))*(r-1)) := by
  have hQ (m y) : 0 ≤ Q.steps m f y ∧ Q.steps m f y ≤ 1 :=
    ⟨Q.steps_nonneg m (fun y => (hf y).1) y,Q.steps_le_one m (fun y => (hf y).2) y⟩
  have hb (m) : P.poissonized t (Q.steps m f) x ≤ a+(b*r^m)*Real.exp ((t:ℝ)*(r-1)) := by
    apply poisson_geometric_sequence
    · intro n
      exact ⟨P.steps_nonneg n (fun y => (hQ m y).1) x,P.steps_le_one n (fun y => (hQ m y).2) x⟩
    · intro n
      convert h n m using 1
      rw [pow_add]
      ring
  rw [finite_poisson_nested_expand P Q t u f (fun y => (hf y).1)]
  have hPB (m) : 0 ≤ P.poissonized t (Q.steps m f) x ∧ P.poissonized t (Q.steps m f) x ≤ 1 := by
    refine ⟨P.poissonized_nonneg t _ (fun y => (hQ m y).1) x,?_⟩
    have hh := P.poissonized_mono t _ (fun _ => 1) (fun y => (hQ m y).1) (fun _ => by norm_num) (fun y => (hQ m y).2) x
    simpa only [P.poissonized_const] using hh
  have hh := poisson_geometric_sequence u _ hPB a (b*Real.exp ((t:ℝ)*(r-1))) r
    (fun m => by convert hb m using 1; ring)
  apply hh.trans_eq
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

end
end FiniteCopyReactor
