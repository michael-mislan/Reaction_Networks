import proofs.ProductiveRecovery.StrongGrowth
import proofs.FiniteReservoir.Reservoir

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery

/-- Same six internal equations, with independent driven coefficients. -/
def field (r alpha beta : ℝ) (c : ProductiveRecovery.State) : ProductiveRecovery.State :=
  let j := ProductiveRecovery.flux r 0 c
  let drive := alpha*c 2-beta*c 0*c 1
  ![1-c 0-j 0-j 1+drive, 1-c 1-j 0-j 2+drive,
    -c 2+j 0-j 1+2*j 4-drive, -c 3+j 1-j 2,
    -c 4+j 2-j 3, -c 5+j 3-j 4]

theorem material_A (r alpha beta : ℝ) (c : ProductiveRecovery.State) :
    A (field r alpha beta c)=1-A c := by simp [A,field]; ring

theorem material_B (r alpha beta : ℝ) (c : ProductiveRecovery.State) :
    B (field r alpha beta c)=1-B c := by simp [B,field]; ring

theorem weighted_drift (r alpha beta : ℝ) (c : ProductiveRecovery.State) :
    Y (field r alpha beta c) = ((1/500000000)+beta)*c 0*c 1 +
      ((5/2)*c 0-1-alpha-(1/5000000000))*c 2 +
      ((11/2)*c 1-(29/8))*c 3 + (11/10)*c 4 +
      (r/5-13/5)*c 5 - (r/5)*c 2^2 := by
  simp [Y,field,ProductiveRecovery.flux]; ring

theorem parameterized_drift (r alpha beta b : ℝ) (c : ProductiveRecovery.State)
    (hc : Nonneg c) (hr : r ≤ 21) (ha : alpha ≤ 1/25)
    (hA : 9/10 ≤ A c) (hB : 9/10 ≤ B c) (hY : Y c ≤ b) :
    ((1/500000000)+beta)*c 0*c 1 +
      (163/300-1/5000000000-(389/45)*b)*c 2 +
      (23/40-(55/7)*b)*c 3 + (1/6)*c 4 + (r/5-19/5)*c 5 ≤
      Y (field r alpha beta c)-(2/3)*Y c := by
  obtain ⟨hfoodA,hfoodB,hx⟩ := material_to_food c hc
  have hu : 9/10-(16/9)*b ≤ c 0 := by linarith
  have hw : 9/10-(10/7)*b ≤ c 1 := by linarith
  have hxx : c 2^2 ≤ b*c 2 := by
    nlinarith [mul_nonneg (hc 2) (sub_nonneg.mpr (hx.trans hY))]
  have hu' := mul_nonneg (sub_nonneg.mpr hu) (hc 2)
  have hw' := mul_nonneg (sub_nonneg.mpr hw) (hc 3)
  have ha' := mul_nonneg (sub_nonneg.mpr ha) (hc 2)
  have hr' := mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (c 2))
  rw [weighted_drift]
  dsimp [Y]
  nlinarith

theorem guarded_growth (r alpha beta : ℝ) (c : ProductiveRecovery.State)
    (hc : Nonneg c) (hr : 19 ≤ r) (hr' : r ≤ 21) (hbox : RateBox alpha beta)
    (hA : 9/10 ≤ A c) (hB : 9/10 ≤ B c) (hY : Y c ≤ 3/50) :
    (2/3)*Y c+1/1000000000 ≤ Y (field r alpha beta c) := by
  have hs := parameterized_drift r alpha beta (3/50) c hc hr' hbox.alpha_upper hA hB hY
  obtain ⟨hfoodA,hfoodB,_⟩ := material_to_food c hc
  have hu : (3/4:ℝ) ≤ c 0 := by linarith
  have hw : (3/4:ℝ) ≤ c 1 := by linarith
  have huw := mul_le_mul hu hw (by norm_num : (0:ℝ) ≤ 3/4) (hc 0)
  have hb := mul_nonneg (mul_nonneg hbox.beta_nonneg (hc 0)) (hc 1)
  have hz := mul_nonneg (show 0 ≤ r/5-19/5 by linarith) (hc 5)
  norm_num at hs huw
  nlinarith [hc 2,hc 3,hc 4]

theorem gross_bound (alpha beta u w x : ℝ) (hbox : RateBox alpha beta)
    (hu0 : 0 ≤ u) (hw0 : 0 ≤ w) (hx0 : 0 ≤ x)
    (hu : u ≤ 11/10) (hw : w ≤ 11/10) (hx : x ≤ 11/10) :
    alpha*x+beta*u*w ≤ 880000000121/20000000000000 ∧
    alpha*x+beta*u*w < 9/200 := by
  have ha := mul_le_mul hbox.alpha_upper hx hx0 (by norm_num : (0:ℝ) ≤ 1/25)
  have huw := mul_le_mul hu hw hw0 (by norm_num : (0:ℝ) ≤ 11/10)
  have hb := mul_le_mul hbox.beta_upper huw (mul_nonneg hu0 hw0)
    (by norm_num : (0:ℝ) ≤ 1/200000000000)
  constructor <;> nlinarith

end
end FiniteReservoir
