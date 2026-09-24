import Mathlib

namespace CompositionalMemory
open Real

/-- Supporting-line inequality for the logarithm of nonempty-bin probability. -/
theorem log_partition_tangent (x m : ℝ) (hx : 0 < x) (hm : 0 < m) :
    log (1-exp (-x)) ≤ log (1-exp (-m)) + exp (-m)/(1-exp (-m))*(x-m) := by
  have hx' : 0 < 1-exp (-x) := sub_pos.mpr (exp_lt_one_iff.mpr (by linarith))
  have hm' : 0 < 1-exp (-m) := sub_pos.mpr (exp_lt_one_iff.mpr (by linarith))
  have hlog := log_le_sub_one_of_pos (div_pos hx' hm')
  rw [log_div (ne_of_gt hx') (ne_of_gt hm')] at hlog
  have he := mul_le_mul_of_nonneg_left (add_one_le_exp (m-x)) (exp_pos (-m)).le
  rw [← exp_add] at he
  have hh : -m+(m-x) = -x := by ring
  rw [hh] at he
  have hdiv : (1-exp (-x))/(1-exp (-m))-1 ≤ exp (-m)/(1-exp (-m))*(x-m) := by
    calc
      _ = ((1-exp (-x))-(1-exp (-m)))/(1-exp (-m)) := by field_simp
      _ ≤ (exp (-m)*(x-m))/(1-exp (-m)) :=
        div_le_div_of_nonneg_right (by nlinarith only [he]) hm'.le
      _ = _ := by ring
  linarith only [hlog,hdiv]

/-- Unequal allocations cannot improve the equal-budget envelope. Zero counts are allowed. -/
theorem unequal_allocation_bound {k : ℕ} (hk : 1 ≤ k) (b : Fin k → ℝ)
    (hb : ∀ i,0 ≤ b i) (B : ℝ) (hB : ∑ i,b i ≤ B) :
    (∏ i, (1-exp (-(log 2)*b i))) ≤ (1-exp (-(log 2)*B/k))^k := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hB0 : 0 ≤ B := (Finset.sum_nonneg (fun i _ => hb i)).trans hB
  have hbase : 0 ≤ 1-exp (-(log 2)*B/k) := sub_nonneg.mpr
    (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlog.le) hB0) hk'.le))
  by_cases hz : ∃ i,b i=0
  · obtain ⟨i,hi⟩ := hz
    have hp : (∏ i, (1-exp (-(log 2)*b i)))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hp]
    exact pow_nonneg hbase _
  · have hp (i) : 0 < b i := lt_of_le_of_ne (hb i) (Ne.symm (fun h => hz ⟨i,h⟩))
    have hsum : 0 < ∑ i,b i := Finset.sum_pos (fun i _ => hp i) (by simp)
    have hm : 0 < log 2*B/k := div_pos (mul_pos hlog (hsum.trans_le hB)) hk'
    have ht (i) := log_partition_tangent (log 2*b i) (log 2*B/k) (mul_pos hlog (hp i)) hm
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ht i)
    have hcancel : ∑ i : Fin k,(log 2*b i-log 2*B/k) ≤ 0 := by
      rw [Finset.sum_sub_distrib,← Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have he : (k : ℝ)*(log 2*B/k)=log 2*B := by field_simp
      rw [he]
      exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hB hlog.le)
    have hd : 0 ≤ exp (-(log 2*B/k))/(1-exp (-(log 2*B/k))) :=
      div_nonneg (exp_pos _).le (sub_nonneg.mpr (exp_le_one_iff.mpr (by linarith)))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum] at hs
    have hs' : (∑ i, log (1-exp (-(log 2*b i)))) ≤ (k : ℝ)*log (1-exp (-(log 2*B/k))) :=
      by
        have hz := mul_nonpos_of_nonneg_of_nonpos hd hcancel
        linarith only [hs,hz]
    have hnon : ∀ i,0 < 1-exp (-(log 2*b i)) := fun i =>
      sub_pos.mpr (exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hlog (hp i))))
    have htarget : 0 < 1-exp (-(log 2*B/k)) := sub_pos.mpr (exp_lt_one_iff.mpr (neg_neg_of_pos hm))
    have hexp := exp_le_exp.mpr hs'
    rw [exp_sum] at hexp
    simp only [exp_log (hnon _),exp_nat_mul,exp_log htarget] at hexp
    simpa only [neg_mul,neg_div] using hexp

end CompositionalMemory
