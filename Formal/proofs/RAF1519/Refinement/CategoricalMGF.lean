import proofs.RAF1519.Refinement.CategoricalPulse

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem categorical_probability_bounds (c : ι → Fin 3 → ℝ)
    (hc : ∀ m a, 0 ≤ c m a) (ht : ∀ m, ∑ a, c m a=1) (m : ι) :
    0 ≤ c m 0 ∧ c m 0 ≤ 1 := by
  refine ⟨hc m 0,?_⟩
  rw [← ht m]
  exact Finset.single_le_sum (fun a _ => hc m a) (Finset.mem_univ 0)

theorem categorical_centered_mgf (c : ι → Fin 3 → ℝ)
    (hc : ∀ m a, 0 ≤ c m a) (htotal : ∀ m, ∑ a, c m a=1)
    (w : ι → ℝ) (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 2)
    (t : ℝ) (ht : |t| ≤ 1/100) :
    (∑ o, categoricalMass c o*Real.exp (t*(categoricalStock w o-categoricalMean c w))) ≤
      Real.exp ((6/5)*t^2*(∑ m, w m)) := by
  have hm : categoricalMean c w ≤ ∑ m, w m := by
    unfold categoricalMean
    apply Finset.sum_le_sum
    intro m _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (categorical_probability_bounds c hc htotal m).2 (hw m)
  have hprod : (∏ m, (1-c m 0+c m 0*Real.exp (t*w m))) ≤
      Real.exp ((t+(6/5)*t^2)*categoricalMean c w) := by
    unfold categoricalMean
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro m _
      exact add_nonneg (sub_nonneg.mpr (categorical_probability_bounds c hc htotal m).2)
        (mul_nonneg (hc m 0) (Real.exp_pos _).le)
    · intro m _
      have h := categorical_retention_factor (c m 0) (w m) t (hc m 0) (hw m) (hw' m) ht
      convert h using 1
      congr 1
      ring
  have heq : (∑ o, categoricalMass c o*Real.exp (t*(categoricalStock w o-categoricalMean c w))) =
      Real.exp (-t*categoricalMean c w)*(∏ m, (1-c m 0+c m 0*Real.exp (t*w m))) := by
    rw [← categorical_transform c htotal w t,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    rw [← mul_assoc,mul_comm (Real.exp _),mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-t*categoricalMean c w)).le
  rw [← Real.exp_add] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (6/5)*t^2 by positivity)
  nlinarith

def categoricalTail (c : ι → Fin 3 → ℝ) (w : ι → ℝ) (sign a : ℝ) : ℝ :=
  ∑ o, if a ≤ sign*(categoricalStock w o-categoricalMean c w) then categoricalMass c o else 0

theorem categorical_deviation_tail (c : ι → Fin 3 → ℝ)
    (hc : ∀ m a, 0 ≤ c m a) (htotal : ∀ m, ∑ a, c m a=1)
    (w : ι → ℝ) (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 2)
    (sign s a : ℝ) (hsign : |sign|=1) (hs : 0 ≤ s) (hs' : s ≤ 1/100) :
    categoricalTail c w sign a ≤ Real.exp (-s*a+(6/5)*s^2*(∑ m, w m)) := by
  have ht : |sign*s| ≤ 1/100 := by rw [abs_mul,hsign,abs_of_nonneg hs,one_mul]; exact hs'
  have hs2 : sign^2=1 := by nlinarith [sq_abs sign]
  have htail : Real.exp (s*a)*categoricalTail c w sign a ≤
      ∑ o, categoricalMass c o*Real.exp ((sign*s)*(categoricalStock w o-categoricalMean c w)) := by
    unfold categoricalTail
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o _
    split_ifs with ho
    · have hh := mul_le_mul_of_nonneg_left ho hs
      have he : Real.exp (s*a) ≤ Real.exp ((sign*s)*(categoricalStock w o-categoricalMean c w)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right he (categoricalMass_nonneg c hc o)
    · simp only [mul_zero]
      exact mul_nonneg (categoricalMass_nonneg c hc o) (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left
    (htail.trans (categorical_centered_mgf c hc htotal w hw hw' (sign*s) ht)) (Real.exp_pos (-s*a)).le
  have he : Real.exp (-s*a)*Real.exp (s*a)=1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [← mul_assoc,he,one_mul,← Real.exp_add,mul_pow,hs2,one_mul] at h
  exact h

end
end RAF1519.Refinement
