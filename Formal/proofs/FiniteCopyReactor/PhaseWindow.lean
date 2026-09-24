import proofs.FiniteCopyReactor.PhaseWeights
import proofs.RandomViability.BindingEntryExponential

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem phase_window_decay (V : ℕ) (hV : 0 < (V:ℝ)) (n : ℕ) (hn : n ≤ 91*V) :
    (1/12:ℝ) ≤ (1-70/(3000*(V:ℝ)))^n := by
  have hv1 : (1:ℝ) ≤ V := by
    have hv : 0 < V := by exact_mod_cast hV
    exact_mod_cast (show 1 ≤ V by omega)
  have hq : 0 < 3000*(V:ℝ) := by positivity
  have hq70 : 0 < 3000*(V:ℝ)-70 := by linarith
  have ha : 0 < 1-70/(3000*(V:ℝ)) := by
    apply sub_pos.mpr
    apply (div_lt_one hq).mpr
    linarith
  have hl := Real.one_sub_inv_le_log_of_pos ha
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) n)
  have he : (n:ℝ)*(1-(1-70/(3000*(V:ℝ)))⁻¹) = -70*(n:ℝ)/(3000*(V:ℝ)-70) := by
    field_simp
    ring
  rw [he] at hm
  have hnr : (n:ℝ) ≤ 91*V := by exact_mod_cast hn
  have ht : 70*(n:ℝ)/(3000*(V:ℝ)-70) ≤ 11/5 := (div_le_iff₀ hq70).mpr (by nlinarith)
  have helo : Real.exp (-(11/5:ℝ)) ≤ (1-70/(3000*(V:ℝ)))^n := by
    rw [← Real.exp_log ha,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [show -70*(n:ℝ)/(3000*(V:ℝ)-70) = -(70*(n:ℝ)/(3000*(V:ℝ)-70)) by ring] at hm
    linarith
  have he2 : Real.exp (2:ℝ) ≤ 9 := by
    rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
    nlinarith [Real.exp_one_lt_three,Real.exp_pos 1]
  have hb := Real.exp_bound (x := (1/5:ℝ)) (by norm_num) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at hb
  have he5 : Real.exp (1/5:ℝ) ≤ 5/4 := by linarith [(abs_le.mp hb).2]
  have hex : Real.exp (11/5:ℝ) ≤ 12 := by
    rw [show (11/5:ℝ)=2+1/5 by norm_num,Real.exp_add]
    nlinarith [mul_le_mul he2 he5 (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 9)]
  apply le_trans _ helo
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos (11/5)) hex

theorem phase_window_stock (V : ℕ) (hV : 0 < (V:ℝ)) (n : ℕ)
    (hn : 89*V ≤ n) (hn' : n ≤ 91*V) (N : Counts) :
    weightedCount N/35 ≤ (phaseWeights (3000*(V:ℝ)) n).obs N := by
  have hv1 : (1:ℝ) ≤ V := by
    have hv : 0 < V := by exact_mod_cast hV
    exact_mod_cast (show 1 ≤ V by omega)
  let q : ℝ := 3000*V
  let a : ℝ := 1-70/q
  have hq : 0 < q := by dsimp [q]; positivity
  have hq70 : 70 < q := by dsimp [q]; linarith
  have ha : 0 < a := sub_pos.mpr ((div_lt_one hq).mpr hq70)
  have ha1 : a ≤ 1 := sub_le_self _ (div_nonneg (by norm_num) hq.le)
  have hnr : (89:ℝ)*V ≤ n := by exact_mod_cast hn
  have hnr1 : (88:ℝ)*V ≤ (n:ℝ)-1 := by linarith
  have hka : (89/3000:ℝ) ≤ (n:ℝ)/(q*a) := by
    apply (le_div_iff₀ (mul_pos hq ha)).mpr
    have hh := mul_le_mul_of_nonneg_left ha1 hq.le
    dsimp [q] at hh
    nlinarith
  have hkb : (89*88/9000000:ℝ) ≤ (n:ℝ)*((n:ℝ)-1)/(q^2*a^2) := by
    apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hq) (sq_pos_of_pos ha))).mpr
    have haa : a^2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left haa (sq_nonneg q)
    have hp := mul_le_mul hnr hnr1 (by positivity : (0:ℝ) ≤ 88*V) (Nat.cast_nonneg (α := ℝ) n)
    dsimp [q] at hh
    nlinarith
  have hp : (1/12:ℝ) ≤ a^n := phase_window_decay V hV n hn'
  have h1 := mul_le_mul hp hka (by norm_num : (0:ℝ) ≤ 89/3000) (pow_nonneg ha.le n)
  have h2 := mul_le_mul hp hkb (by norm_num : (0:ℝ) ≤ 89*88/9000000) (pow_nonneg ha.le n)
  rw [phase_weights_closed q hq hq70]
  have hx : (1/35:ℝ) ≤ (phaseWeightsClosed q n).x := by
    change _ ≤ a^n
    linarith
  have hc1 : (9/8/35:ℝ) ≤ (phaseWeightsClosed q n).c1 := by
    change _ ≤ a^n*(20*(n:ℝ))/(q*a)
    have he : a^n*(20*(n:ℝ))/(q*a)=20*(a^n*((n:ℝ)/(q*a))) := by ring
    rw [he]
    linarith
  have hc2 : (7/5/35:ℝ) ≤ (phaseWeightsClosed q n).c2 := by
    change _ ≤ a^n*(580*(n:ℝ)*((n:ℝ)-1))/(q^2*a^2)
    have he : a^n*(580*(n:ℝ)*((n:ℝ)-1))/(q^2*a^2)=580*(a^n*((n:ℝ)*((n:ℝ)-1)/(q^2*a^2))) := by ring
    rw [he]
    linarith
  have hz : (9/5/35:ℝ) ≤ (phaseWeightsClosed q n).z := by
    change _ ≤ a^n*(38*(n:ℝ))/(q*a)
    have he : a^n*(38*(n:ℝ))/(q*a)=38*(a^n*((n:ℝ)/(q*a))) := by ring
    rw [he]
    linarith
  have hh := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg (N 2)))
    (mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg (N 3))))
    (mul_le_mul_of_nonneg_right hc2 (Nat.cast_nonneg (N 4))))
    (mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg (N 5)))
  dsimp [weightedCount,weighted,PhaseWeights.obs]
  convert hh using 1
  ring

end
end FiniteCopyReactor
