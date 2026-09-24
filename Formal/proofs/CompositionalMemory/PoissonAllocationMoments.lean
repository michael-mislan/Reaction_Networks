import proofs.FiniteCopy.PoissonKernel

namespace CompositionalMemory
open FiniteCopy
open MeasureTheory ProbabilityTheory

private theorem poisson_successor (t : NNReal) (n : ℕ) :
    ((n : ℝ)+1)*poissonWeight t (n+1)=(t : ℝ)*poissonWeight t n := by
  unfold poissonWeight
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem poisson_moment_lift (t : NNReal) (p : ℕ) (m : ℝ)
    (h : HasSum (fun n : ℕ => ((n : ℝ)+1)^p*poissonWeight t n) m) :
    HasSum (fun n : ℕ => (n : ℝ)^(p+1)*poissonWeight t n) ((t : ℝ)*m) := by
  have he (n : ℕ) : ((n+1 : ℕ) : ℝ)^(p+1)*poissonWeight t (n+1)=
      (t : ℝ)*(((n : ℝ)+1)^p*poissonWeight t n) := by
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    calc
      _ = ((n : ℝ)+1)^p*(((n : ℝ)+1)*poissonWeight t (n+1)) := by ring
      _ = _ := by rw [poisson_successor]; ring
  have hs : HasSum (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(p+1)*poissonWeight t (n+1)) ((t : ℝ)*m) := by
    simpa only [he] using h.mul_left (t : ℝ)
  have hh := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(p+1)*poissonWeight t n) 1).mp hs
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_pow (Nat.succ_ne_zero p),zero_mul,add_zero] using hh

theorem poisson_second_raw (t : NNReal) :
    HasSum (fun n : ℕ => (n : ℝ)^2*poissonWeight t n) ((t : ℝ)^2+t) := by
  have hh : HasSum (fun n : ℕ => ((n : ℝ)+1)^1*poissonWeight t n) ((t : ℝ)+1) := by
    convert (poissonWeight_mean t).add (poissonWeight_sum t) using 1
    funext n; ring
  convert poisson_moment_lift t 1 ((t : ℝ)+1) hh using 1
  ring

theorem poisson_third_raw (t : NNReal) :
    HasSum (fun n : ℕ => (n : ℝ)^3*poissonWeight t n) ((t : ℝ)^3+3*t^2+t) := by
  have hh : HasSum (fun n : ℕ => ((n : ℝ)+1)^2*poissonWeight t n)
      (((t : ℝ)^2+t)+2*t+1) := by
    convert ((poisson_second_raw t).add ((poissonWeight_mean t).mul_left 2)).add (poissonWeight_sum t) using 1
    funext n; ring
  convert poisson_moment_lift t 2 _ hh using 1
  ring

theorem poisson_fourth_raw (t : NNReal) :
    HasSum (fun n : ℕ => (n : ℝ)^4*poissonWeight t n) ((t : ℝ)^4+6*t^3+7*t^2+t) := by
  have hh : HasSum (fun n : ℕ => ((n : ℝ)+1)^3*poissonWeight t n)
      (((t : ℝ)^3+3*t^2+t)+3*(t^2+t)+3*t+1) := by
    convert (((poisson_third_raw t).add ((poisson_second_raw t).mul_left 3)).add
      ((poissonWeight_mean t).mul_left 3)).add (poissonWeight_sum t) using 1
    funext n; ring
  convert poisson_moment_lift t 3 _ hh using 1
  ring

theorem poisson_centered_mean (t : NNReal) :
    HasSum (fun n : ℕ => ((n : ℝ)-t)*poissonWeight t n) 0 := by
  convert (poissonWeight_mean t).sub ((poissonWeight_sum t).mul_left (t : ℝ)) using 1
  · funext n; ring
  · ring

theorem poisson_centered_second (t : NNReal) :
    HasSum (fun n : ℕ => ((n : ℝ)-t)^2*poissonWeight t n) (t : ℝ) := by
  convert ((poisson_second_raw t).sub ((poissonWeight_mean t).mul_left (2*(t : ℝ)))).add
    ((poissonWeight_sum t).mul_left ((t : ℝ)^2)) using 1
  · funext n; ring
  · ring

theorem poisson_centered_fourth (t : NNReal) :
    HasSum (fun n : ℕ => ((n : ℝ)-t)^4*poissonWeight t n) (3*(t : ℝ)^2+t) := by
  convert ((((poisson_fourth_raw t).sub ((poisson_third_raw t).mul_left (4*(t : ℝ)))).add
    ((poisson_second_raw t).mul_left (6*(t : ℝ)^2))).sub
    ((poissonWeight_mean t).mul_left (4*(t : ℝ)^3))).add
    ((poissonWeight_sum t).mul_left ((t : ℝ)^4)) using 1
  · funext n; ring
  · ring

theorem poisson_centered_third (t : NNReal) :
    HasSum (fun n : ℕ => ((n : ℝ)-t)^3*poissonWeight t n) (t : ℝ) := by
  convert (((poisson_third_raw t).sub ((poisson_second_raw t).mul_left (3*(t : ℝ)))).add
    ((poissonWeight_mean t).mul_left (3*(t : ℝ)^2))).sub
    ((poissonWeight_sum t).mul_left ((t : ℝ)^3)) using 1
  · funext n; ring
  · ring

theorem poisson_integrable_of_hasSum (t : NNReal) (f : ℕ → ℝ) (v : ℝ)
    (h : HasSum (fun n => f n*poissonWeight t n) v) :
    Integrable f (poissonMeasure t) := by
  apply integrable_poissonMeasure_iff.mpr
  change Summable (fun n => poissonWeight t n*‖f n‖)
  have hh := h.summable.norm
  have he : (fun n => ‖f n*poissonWeight t n‖) = (fun n => poissonWeight t n*‖f n‖) := by
    funext n
    rw [norm_mul,Real.norm_of_nonneg (poissonWeight_nonneg t n)]
    ring
  rw [he] at hh
  exact hh

theorem poisson_integral_of_hasSum (t : NNReal) (f : ℕ → ℝ) (v : ℝ)
    (h : HasSum (fun n => f n*poissonWeight t n) v) :
    (∫ n,f n ∂poissonMeasure t)=v := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul,mul_comm,poissonWeight] using h.tsum_eq

theorem poisson_actual_centered_moments (t : NNReal) :
    (∫ n,((n : ℝ)-t) ∂poissonMeasure t)=0 ∧
    (∫ n,((n : ℝ)-t)^2 ∂poissonMeasure t)=(t : ℝ) ∧
    (∫ n,((n : ℝ)-t)^4 ∂poissonMeasure t)=3*(t : ℝ)^2+t := by
  exact ⟨poisson_integral_of_hasSum t _ _ (poisson_centered_mean t),
    poisson_integral_of_hasSum t _ _ (poisson_centered_second t),
    poisson_integral_of_hasSum t _ _ (poisson_centered_fourth t)⟩

end CompositionalMemory
