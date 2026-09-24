import proofs.FiniteCopy.Source

namespace ProductiveMemory
set_option maxHeartbeats 200000
set_option Elab.async false
open FiniteCopy Set
noncomputable section

def extractDrift (rho q : ℝ) (x : Point) : Point :=
  drift (1/100000) q x - ![0,0,rho*x 2,0]
def reducedB (z : ℝ) : ℝ := 60/(z+2)
def reducedH (z : ℝ) : ℝ := (16*z+2*z^2)/(2+1/10000)
def reducedK (z : ℝ) : ℝ :=
  (2*(1+2/10000)*z^2-16*(1-1/10000)*z)/(2+1/10000)
def reducedA (rho z : ℝ) : ℝ := z*reducedB z+reducedK z+rho*z
def residual (rho z : ℝ) : ℝ :=
  27-(1+1/100000)*reducedB z+reducedK z+rho*z+(reducedA rho z)^2/100000
def lift (rho z : ℝ) : Point := ![reducedA rho z,reducedB z,z,reducedH z]

theorem lift_residual (rho z : ℝ) (hz : z+2 ≠ 0) :
    extractDrift rho 0 (lift rho z) = ![-2*residual rho z,residual rho z,0,0] := by
  unfold extractDrift
  rw [drift_formula]
  ext i
  fin_cases i <;> norm_num [lift,residual,reducedA,reducedB,reducedK,reducedH,
    Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals field_simp
  all_goals ring

theorem lift_stationary (rho z : ℝ) (hz : z+2 ≠ 0) (hr : residual rho z = 0) :
    extractDrift rho 0 (lift rho z) = 0 := by
  rw [lift_residual rho z hz,hr]
  ext i
  fin_cases i <;> simp

theorem finite_count_correction (rho q : ℝ) (x : Point) :
    extractDrift rho q x - extractDrift rho 0 x =
    ![2/100000*q*x 0,-1/100000*q*x 0,4*q*x 2,-2*q*x 2] := by
  unfold extractDrift
  rw [drift_formula,drift_formula]
  ext i
  fin_cases i <;> norm_num

theorem stationary_reconstruction (rho : ℝ) (x : Point)
    (hz : x 2+2 ≠ 0) (hx : extractDrift rho 0 x = 0) : x = lift rho (x 2) := by
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  have h2 := congrFun hx 2
  have h3 := congrFun hx 3
  simp [extractDrift,drift_formula] at h0 h1 h2 h3
  have hB : x 1 = reducedB (x 2) := by
    unfold reducedB
    apply (eq_div_iff hz).2
    linarith
  have hH : x 3 = reducedH (x 2) := by
    unfold reducedH
    apply (eq_div_iff (by norm_num : (2+1/10000:ℝ) ≠ 0)).2
    linarith
  have hA : x 0 = reducedA rho (x 2) := by
    unfold reducedA reducedK
    rw [← hB]
    rw [hH] at h2
    norm_num [reducedH] at h2 ⊢
    linarith
  ext i
  fin_cases i <;> simp [lift,hA,hB,hH]

theorem stationary_iff (rho : ℝ) (x : Point) (hz : x 2+2 ≠ 0) :
    extractDrift rho 0 x = 0 ↔ x = lift rho (x 2) ∧ residual rho (x 2) = 0 := by
  constructor
  · intro hx
    have he := stationary_reconstruction rho x hz hx
    refine ⟨he,?_⟩
    have hl := lift_residual rho (x 2) hz
    rw [← he,hx] at hl
    have hh := congrFun hl 1
    simpa using hh.symm
  · rintro ⟨he,hr⟩
    calc extractDrift rho 0 x = extractDrift rho 0 (lift rho (x 2)) := congrArg _ he
         _ = 0 := lift_stationary rho (x 2) hz hr

theorem residual_continuous (rho lo hi : ℝ) (hl : -2 < lo) :
    ContinuousOn (residual rho) (Icc lo hi) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hz : x+2 ≠ 0 := by linarith [hx.1]
  unfold residual reducedA reducedB reducedK
  fun_prop (disch := first | exact hz | norm_num)

theorem low_root_at_one_percent :
    ∃ z ∈ Icc (98172441/100000000 : ℝ) (98172442/100000000),
      extractDrift (1/100) 0 (lift (1/100) z) = 0 := by
  have hl : residual (1/100) (98172441/100000000) ≤ 0 := by
    norm_num [residual,reducedA,reducedB,reducedK]
  have hr : 0 ≤ residual (1/100) (98172442/100000000) := by
    norm_num [residual,reducedA,reducedB,reducedK]
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc (by norm_num :
    (98172441/100000000:ℝ) ≤ 98172442/100000000)
    (residual_continuous (1/100) _ _ (by norm_num)) ⟨hl,hr⟩
  exact ⟨z,hz,lift_stationary _ _ (by linarith [hz.1]) he⟩

theorem high_root_at_one_percent :
    ∃ z ∈ Icc (289014929/100000000 : ℝ) (289014930/100000000),
      extractDrift (1/100) 0 (lift (1/100) z) = 0 := by
  have hl : residual (1/100) (289014929/100000000) ≤ 0 := by
    norm_num [residual,reducedA,reducedB,reducedK]
  have hr : 0 ≤ residual (1/100) (289014930/100000000) := by
    norm_num [residual,reducedA,reducedB,reducedK]
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc (by norm_num :
    (289014929/100000000:ℝ) ≤ 289014930/100000000)
    (residual_continuous (1/100) _ _ (by norm_num)) ⟨hl,hr⟩
  exact ⟨z,hz,lift_stationary _ _ (by linarith [hz.1]) he⟩

end
end ProductiveMemory
