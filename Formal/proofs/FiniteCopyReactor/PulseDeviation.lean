import proofs.FiniteCopyReactor.PulseInventory

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

def retainedMean (N : Counts) (p : Intervention) (w : Molecules N → ℝ) : ℝ :=
  ∑ m, p.q*p.loss m.1*w m

theorem signed_retention_factor (p w t : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hw' : w ≤ 2) (ht : |t| ≤ 1/100) :
    1-p+p*Real.exp (t*w) ≤ Real.exp (t*p*w+(6/5)*t^2*p*w) := by
  have hab : |t*w| ≤ 9/50 := by
    rw [abs_mul,abs_of_nonneg hw]
    exact (mul_le_mul ht hw' hw (by norm_num)).trans (by norm_num)
  have he := mul_le_mul_of_nonneg_left (exp_small_quadratic (t*w) hab) hp
  have hw2 : w^2 ≤ 2*w := by nlinarith
  have hq := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ (3/5)*p*t^2 by positivity)
  have hh : 1-p+p*Real.exp (t*w) ≤ (t*p*w+(6/5)*t^2*p*w)+1 := by nlinarith
  exact hh.trans (Real.add_one_le_exp _)

/-- Centered transform of the actual independent categorical withdrawal law. -/
theorem pulse_centered_mgf (N : Counts) (p : Intervention) (w : Molecules N → ℝ)
    (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 2)
    (t : ℝ) (ht : |t| ≤ 1/100) :
    (∑ o, pulseMass N p o * Real.exp (t*(retainedStock N w o-retainedMean N p w))) ≤
      Real.exp ((6/5)*t^2*(∑ m, w m)) := by
  classical
  have hm : retainedMean N p w ≤ ∑ m, w m := by
    unfold retainedMean
    apply Finset.sum_le_sum
    intro m _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (retention_probability_bounds p m.1).2 (hw m)
  have hprod : (∏ m, (1-p.q*p.loss m.1+p.q*p.loss m.1*Real.exp (t*w m))) ≤
      Real.exp ((t+(6/5)*t^2)*retainedMean N p w) := by
    unfold retainedMean
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro m _
      obtain ⟨hl,hu⟩ := retention_probability_bounds p m.1
      have hp : 0 ≤ p.q*p.loss m.1 := by linarith
      exact add_nonneg (sub_nonneg.mpr hu) (mul_nonneg hp (Real.exp_pos _).le)
    · intro m _
      have h := signed_retention_factor (p.q*p.loss m.1) (w m) t
        (by linarith [(retention_probability_bounds p m.1).1]) (hw m) (hw' m) ht
      convert h using 1
      congr 1
      ring
  have heq : (∑ o, pulseMass N p o * Real.exp (t*(retainedStock N w o-retainedMean N p w))) =
      Real.exp (-t*retainedMean N p w) *
        (∏ m, (1-p.q*p.loss m.1+p.q*p.loss m.1*Real.exp (t*w m))) := by
    have h := pulse_laplace N p w (-t)
    simp only [neg_neg] at h
    rw [← h,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    rw [← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hprod (Real.exp_pos (-t*retainedMean N p w)).le
  rw [← Real.exp_add] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (6/5)*t^2 by positivity)
  nlinarith

def deviationTail (N : Counts) (p : Intervention) (w : Molecules N → ℝ)
    (sign a : ℝ) : ℝ :=
  ∑ o, if a ≤ sign*(retainedStock N w o-retainedMean N p w) then pulseMass N p o else 0

theorem pulse_deviation_tail (N : Counts) (p : Intervention) (w : Molecules N → ℝ)
    (V sign : ℝ) (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 2)
    (hsign : |sign|=1) (hbound : (∑ m, w m) ≤ (161/160)*V) :
    deviationTail N p w sign (V/100) ≤ Real.exp (-V/100000) := by
  classical
  let t : ℝ := sign/500
  have hV : 0 ≤ V := by
    have hsum := Finset.sum_nonneg (fun (m : Molecules N) (_ : m ∈ Finset.univ) => hw m)
    linarith
  have ht : |t| ≤ 1/100 := by
    dsimp [t]
    rw [abs_div,hsign]
    norm_num
  have hs2 : sign^2=1 := by nlinarith [sq_abs sign]
  have htt : t^2=1/250000 := by dsimp [t]; nlinarith
  have htail : Real.exp (V/50000)*deviationTail N p w sign (V/100) ≤
      ∑ o, pulseMass N p o * Real.exp (t*(retainedStock N w o-retainedMean N p w)) := by
    unfold deviationTail
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o _
    split_ifs with ho
    · have he : Real.exp (V/50000) ≤ Real.exp (t*(retainedStock N w o-retainedMean N p w)) := by
        apply Real.exp_le_exp.mpr
        dsimp [t]
        linarith
      have hh := mul_le_mul_of_nonneg_right he (pulseMass_nonneg N p o)
      simpa only [mul_comm] using hh
    · simp only [mul_zero]
      exact mul_nonneg (pulseMass_nonneg N p o) (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left
    (htail.trans (pulse_centered_mgf N p w hw hw' t ht)) (Real.exp_pos (-V/50000)).le
  have he : Real.exp (-V/50000)*Real.exp (V/50000) = 1 := by
    rw [← Real.exp_add, show -V/50000+V/50000=0 by ring, Real.exp_zero]
  rw [← mul_assoc,he,one_mul,← Real.exp_add,htt] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  linarith

end
end FiniteCopyReactor
