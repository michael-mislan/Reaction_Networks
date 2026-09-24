import proofs.FiniteCopyReactor.PoissonComposition

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

theorem finite_poisson_unit_interval {α : Type*} [Fintype α] (P : FiniteKernel α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (t : NNReal) (x : α) :
    0 ≤ P.poissonized t f x ∧ P.poissonized t f x ≤ 1 := by
  refine ⟨P.poissonized_nonneg t f (fun y => (hf y).1) x,?_⟩
  have h := P.poissonized_mono t f (fun _ => 1) (fun y => (hf y).1)
    (fun _ => by norm_num) (fun y => (hf y).2) x
  simpa only [P.poissonized_const] using h

theorem finite_three_clock_geometric {α : Type*} [Fintype α] (P Q R : FiniteKernel α)
    (t u v : NNReal) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (a b r : ℝ) (x : α)
    (h : ∀ n m k, P.steps n (Q.steps m (R.steps k f)) x ≤ a+b*r^(n+m+k)) :
    P.poissonized t (fun y => Q.poissonized u (fun z => R.poissonized v f z) y) x ≤
      a+b*Real.exp (((t:ℝ)+(u:ℝ)+(v:ℝ))*(r-1)) := by
  have hR (k y) : 0 ≤ R.steps k f y ∧ R.steps k f y ≤ 1 :=
    ⟨R.steps_nonneg k (fun z => (hf z).1) y,R.steps_le_one k (fun z => (hf z).2) y⟩
  have hQ (k y) := finite_poisson_unit_interval Q (R.steps k f) (hR k) u y
  have hP (k) := finite_poisson_unit_interval P (fun y => Q.poissonized u (R.steps k f) y) (hQ k) t x
  have hsum (y) : Summable (fun k => poissonWeight v k*Q.poissonized u (R.steps k f) y) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (poissonWeight_nonneg v k) (hQ k y).1)
      (fun k => mul_le_of_le_one_right (poissonWeight_nonneg v k) (hQ k y).2) (poissonWeight_sum v).summable
  simp_rw [finite_poisson_nested_expand Q R u v f (fun y => (hf y).1)]
  rw [finite_poisson_tsum P _ hsum]
  simp_rw [P.poissonized_scale]
  have hb (k) : P.poissonized t (fun y => Q.poissonized u (R.steps k f) y) x ≤
      a+(b*r^k)*Real.exp (((t:ℝ)+(u:ℝ))*(r-1)) := by
    apply finite_two_clock_geometric P Q t u (R.steps k f) (hR k) a (b*r^k) r x
    intro n m
    convert h n m k using 1
    rw [pow_add]
    ring
  have hh := poisson_geometric_sequence v _ hP a
    (b*Real.exp (((t:ℝ)+(u:ℝ))*(r-1))) r (fun k => by convert hb k using 1; ring)
  apply hh.trans_eq
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

end
end FiniteCopyReactor
