import proofs.RepeatedFunction.C6Resolution

namespace RandomViability
open Finset
noncomputable section
set_option maxHeartbeats 100000

/-- Sharp food-pair quadratic bound on the monomer-mass corridor. -/
theorem food_pair_birth_bound (x y : ℝ) (hy : 0 ≤ y) (hm : x+2*y ≤ 11) :
    2*x*y+y^2 ≤ 121/3 := by
  have hh := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 2*y)
  nlinarith [sq_nonneg (3*y-11)]

theorem startup_intensity_bound (x y eps V rate : ℝ)
    (hy : 0 ≤ y) (hm : x+2*y ≤ 11) (he : 0 ≤ eps) (hv : 0 ≤ V)
    (hr : rate ≤ 4*eps*V*(2*x*y+y^2)) : rate ≤ (484/3)*eps*V := by
  have hh := mul_le_mul_of_nonneg_left (food_pair_birth_bound x y hy hm)
    (show 0 ≤ 4*eps*V by positivity)
  nlinarith only [hh,hr]

/-- Survival of a killed finite transition kernel. Corridor exits are sent to
a safe absorbing state, while first births are killed. Its row deficit is
therefore only the stopped birth probability, not the corridor-exit hazard. -/
def startupSurvival {ι : Type*} [Fintype ι] (P : ι → ι → ℝ) : ℕ → ι → ℝ
  | 0,_ => 1
  | k+1,i => ∑ j,P i j*startupSurvival P k j

theorem startup_survival_lower {ι : Type*} [Fintype ι]
    (P : ι → ι → ℝ) (hP : ∀ i j,0 ≤ P i j) (h : ℝ) (hh1 : h ≤ 1)
    (hrow : ∀ i,1-h ≤ ∑ j,P i j) (k : ℕ) (i : ι) :
    (1-h)^k ≤ startupSurvival P k i := by
  induction k generalizing i with
  | zero => simp [startupSurvival]
  | succ k ih =>
    simp only [startupSurvival,pow_succ]
    calc
      _ ≤ (∑ j,P i j)*(1-h)^k := by
        have hc := mul_le_mul_of_nonneg_right (hrow i) (pow_nonneg (sub_nonneg.mpr hh1) k)
        nlinarith only [hc]
      _ = ∑ j,P i j*(1-h)^k := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ih j) (hP i j))

/-- Necessary deadline/count-scale constraint, given the proved hazard ceiling.
The literal stopped-generator docking is provided conventionally in the paper. -/
theorem startup_necessary_scale (q eta lambda V t : ℝ) (heta : 0 < eta)
    (hupper : q ≤ 1-Real.exp (-(lambda*V*t))) (hreliable : 1-eta ≤ q) :
    Real.log (1/eta) ≤ lambda*V*t := by
  have he : Real.exp (-(lambda*V*t)) ≤ eta := by linarith only [hupper,hreliable]
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  rw [Real.log_div (by norm_num) heta.ne',Real.log_one,zero_sub]
  linarith only [hl]

theorem mission_material_recovery (Q B : ℝ) (hQ : (1/5 : ℝ) < Q)
    (hB : 0 ≤ B) (hcap : B ≤ 2390) : (1/12000 : ℝ) < Q/(10+B) := by
  apply (lt_div_iff₀ (by linarith only [hB])).2
  linarith only [hQ,hcap]

end
end RandomViability
