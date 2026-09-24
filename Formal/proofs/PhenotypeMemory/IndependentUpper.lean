import proofs.PhenotypeMemory.Source

namespace PhenotypeMemory
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail
def independentUpper : Fin 6 → ℚ :=
  ![948115/1000000,983103/1000000,987779/1000000,
    378814/1000000,775706/1000000,335634/1000000]
theorem independent_supersolution (i : Fin 6) :
    molecular (1/100) independentUpper i + death i*(1-independentUpper i) +
      ((daughter independentUpper i)^2-independentUpper i)/10 < 0 := by
  fin_cases i <;> norm_num [molecular, death, daughter, independentUpper]
theorem independent_upper_range (i : Fin 6) :
    0 ≤ independentUpper i ∧ independentUpper i < 988/1000 := by
  fin_cases i <;> norm_num [independentUpper]
theorem hit_arithmetic_scalar (x : ℚ) (hx : x < 273/10000) :
    (686709/1000000 : ℚ)/(1-x) < 706/1000 := by
  apply (div_lt_iff₀ (by linarith : (0 : ℚ) < 1-x)).2
  linarith
theorem deadline_arithmetic_scalar (x : ℚ) (hx : x < 20/7) :
    (1 : ℚ)-22/100-x*(227/1000-22/100) > 760/1000 := by linarith
theorem hit300_arithmetic :
    (686709/1000000 : ℚ)/(1-(988/1000)^300) < 706/1000 ∧
    (765/1000 : ℚ)-706/1000 = 59/1000 := by
  have h25 : (988/1000 : ℚ)^25 ≤ 74/100 := by norm_num
  have h300 : (988/1000 : ℚ)^300 ≤ (74/100)^12 := by
    calc
      (988/1000 : ℚ)^300 = ((988/1000 : ℚ)^25)^12 := by rw [← pow_mul]
      _ ≤ (74/100)^12 := pow_le_pow_left₀ (by positivity) h25 12
  have hb : (988/1000 : ℚ)^300 < 273/10000 := by
    calc
      _ ≤ (74/100 : ℚ)^12 := h300
      _ < 273/10000 := by norm_num
  constructor
  · exact hit_arithmetic_scalar _ hb
  · norm_num
theorem deadline_arithmetic :
    (1 : ℚ)-22/100-(300/299)^299*(227/1000-22/100) > 760/1000 := by
  have h10 : (300/299 : ℚ)^10 ≤ 207/200 := by norm_num
  have h300 : (300/299 : ℚ)^300 ≤ (207/200)^30 := by
    calc
      (300/299 : ℚ)^300 = ((300/299 : ℚ)^10)^30 := by rw [← pow_mul]
      _ ≤ (207/200)^30 := pow_le_pow_left₀ (by positivity) h10 30
  have hstep : (300/299 : ℚ)^299 ≤ (300/299)^300 := by
    calc
      _ ≤ (300/299 : ℚ)^299 * (300/299) := le_mul_of_one_le_right (by positivity) (by norm_num)
      _ = _ := (pow_succ _ _).symm
  have hb : (300/299 : ℚ)^299 < 20/7 := by
    calc
      _ ≤ (300/299 : ℚ)^300 := hstep
      _ ≤ (207/200 : ℚ)^30 := h300
      _ < 20/7 := by norm_num
  exact deadline_arithmetic_scalar _ hb
end PhenotypeMemory
