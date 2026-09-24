import proofs.RandomViability.RewardPaths

namespace RandomViability
open Classical FiniteCopy
noncomputable section
namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β]

def pathEventMass (K : FiniteLabeledKernel α β) (n : ℕ) (x : α)
    (E : RewardPath β n → Prop) : ℝ := ∑ p, if E p then K.pathWeight n x p else 0

theorem pathEventMass_bounds (K : FiniteLabeledKernel α β) (n : ℕ) (x : α)
    (E : RewardPath β n → Prop) : 0 ≤ K.pathEventMass n x E ∧ K.pathEventMass n x E ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact K.pathWeight_nonneg n x p
    · exact le_refl 0
  · calc
      _ ≤ ∑ p, K.pathWeight n x p := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · exact le_refl _
        · exact K.pathWeight_nonneg n x p
      _ = _ := K.pathWeight_sum n x

theorem pathWeight_domination (K L : FiniteLabeledKernel α β) (r : ℝ) (hr : 0 ≤ r)
    (hnext : ∀ x b, L.next x b = K.next x b)
    (hprob : ∀ x b, r*K.prob x b ≤ L.prob x b)
    (n : ℕ) (x : α) (p : RewardPath β n) :
    r^n*K.pathWeight n x p ≤ L.pathWeight n x p := by
  induction n generalizing x with
  | zero => simp only [pathWeight, pow_zero, one_mul, le_refl]
  | succ n ih =>
    change r^(n+1)*(K.prob x p.1*K.pathWeight n (K.next x p.1) p.2) ≤
      L.prob x p.1*L.pathWeight n (L.next x p.1) p.2
    rw [hnext]
    calc
      _ = (r*K.prob x p.1)*(r^n*K.pathWeight n (K.next x p.1) p.2) := by ring
      _ ≤ _ := mul_le_mul (hprob x p.1) (ih _ p.2)
        (mul_nonneg (pow_nonneg hr n) (K.pathWeight_nonneg _ _ _)) (L.nonneg _ _)

theorem pathEventMass_domination (K L : FiniteLabeledKernel α β) (r : ℝ) (hr : 0 ≤ r)
    (hnext : ∀ x b, L.next x b = K.next x b)
    (hprob : ∀ x b, r*K.prob x b ≤ L.prob x b)
    (n : ℕ) (x : α) (E : RewardPath β n → Prop) :
    r^n*K.pathEventMass n x E ≤ L.pathEventMass n x E := by
  unfold pathEventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact pathWeight_domination K L r hr hnext hprob n x p
  · simp only [mul_zero, le_refl]

def poissonEventMass (K : FiniteLabeledKernel α β) (t : NNReal) (x : α)
    (E : (n : ℕ) → RewardPath β n → Prop) : ℝ :=
  ∑' n, poissonWeight t n*K.pathEventMass n x (E n)

theorem poissonEventMass_summable (K : FiniteLabeledKernel α β) (t : NNReal) (x : α)
    (E : (n : ℕ) → RewardPath β n → Prop) :
    Summable (fun n => poissonWeight t n*K.pathEventMass n x (E n)) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (poissonWeight_nonneg t n) (K.pathEventMass_bounds n x (E n)).1)
    (fun n => ?_) (poissonWeight_sum t).summable
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (K.pathEventMass_bounds n x (E n)).2
    (poissonWeight_nonneg t n)

end FiniteLabeledKernel

theorem poissonWeight_tilt (t r : NNReal) (n : ℕ) :
    poissonWeight t n*(r : ℝ)^n =
      Real.exp (((r : ℝ)-1)*t)*poissonWeight (r*t) n := by
  have he : Real.exp (((r : ℝ)-1)*t)*Real.exp (-((r : ℝ)*t)) = Real.exp (-(t : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold poissonWeight
  simp only [NNReal.coe_mul, mul_pow]
  calc
    _ = (Real.exp (((r : ℝ)-1)*t)*Real.exp (-((r : ℝ)*t)))*
        ((r : ℝ)^n*(t : ℝ)^n)/(n.factorial : ℝ) := by rw [he]; ring
    _ = _ := by ring

namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β]

theorem poissonEventMass_domination (K L : FiniteLabeledKernel α β) (r t : NNReal)
    (hnext : ∀ x b, L.next x b = K.next x b)
    (hprob : ∀ x b, (r : ℝ)*K.prob x b ≤ L.prob x b)
    (x : α) (E : (n : ℕ) → RewardPath β n → Prop) :
    Real.exp (((r : ℝ)-1)*t)*K.poissonEventMass (r*t) x E ≤ L.poissonEventMass t x E := by
  have hb : ∀ n : ℕ,
      Real.exp (((r : ℝ)-1)*t)*(poissonWeight (r*t) n*K.pathEventMass n x (E n)) ≤
        poissonWeight t n*L.pathEventMass n x (E n) := by
    intro n
    have hh := mul_le_mul_of_nonneg_left
      (pathEventMass_domination K L r r.coe_nonneg hnext hprob n x (E n)) (poissonWeight_nonneg t n)
    calc
      _ = (poissonWeight t n*(r : ℝ)^n)*K.pathEventMass n x (E n) := by rw [poissonWeight_tilt]; ring
      _ ≤ _ := by simpa only [mul_assoc] using hh
  have hs := (K.poissonEventMass_summable (r*t) x E).mul_left (Real.exp (((r : ℝ)-1)*t))
  have hh := Summable.tsum_le_tsum hb hs (L.poissonEventMass_summable t x E)
  simpa only [poissonEventMass, tsum_mul_left] using hh

end FiniteLabeledKernel
end
end RandomViability
