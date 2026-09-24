import proofs.ProductiveMemory.ExtractionEquilibria

namespace ProductiveMemory
open FiniteCopy Set
noncomputable section
set_option Elab.async false

theorem reconstructed_A_pos (rho z : ℝ) (hr : 0 ≤ rho) (hz : 0 < z) :
    0 < reducedA rho z := by
  have hd : z+2 ≠ 0 := by positivity
  have hid : reducedA rho z =
      z*(20004*(z-3)^2+48*z+700056+20001*rho*(z+2))/((z+2)*20001) := by
    unfold reducedA reducedB reducedK
    field_simp
    ring
  rw [hid]
  positivity

theorem reconstructed_positive (rho z : ℝ) (hr : 0 ≤ rho) (hz : 0 < z) :
    ∀ i, 0 < lift rho z i := by
  intro i
  fin_cases i
  · exact reconstructed_A_pos rho z hr hz
  · change 0 < 60/(z+2)
    positivity
  · exact hz
  · change 0 < (16*z+2*z^2)/(2+1/10000:ℝ)
    positivity

theorem residual_rate_difference (r s z : ℝ) :
    residual s z-residual r z =
      (s-r)*z*(1+(reducedA s z+reducedA r z)/100000) := by
  unfold residual reducedA
  ring

theorem residual_rate_mono (r s z : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hz : 0 < z) :
    residual r z ≤ residual s z := by
  have ha := reconstructed_A_pos r z hr hz
  have hb := reconstructed_A_pos s z (hr.trans hrs) hz
  have hdiff := residual_rate_difference r s z
  have hp : 0 ≤ (s-r)*z*(1+(reducedA s z+reducedA r z)/100000) := by
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hrs) hz.le) (by positivity)
  linarith only [hdiff,hp]

theorem interval_root (rho lo hi : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) (hl : 0 < lo) (hlh : lo ≤ hi)
    (hleft : residual (1/100) lo ≤ 0)
    (hright : 0 ≤ residual (9999/1000000) hi) :
    ∃ z ∈ Icc lo hi, extractDrift rho 0 (lift rho z) = 0 ∧ ∀ i, 0 < lift rho z i := by
  have hlo : residual rho lo ≤ 0 := (residual_rate_mono rho (1/100) lo
    (by linarith [hr.1]) hr.2 hl).trans hleft
  have hhi : 0 ≤ residual rho hi := hright.trans (residual_rate_mono (9999/1000000)
    rho hi (by norm_num) hr.1 (hl.trans_le hlh))
  obtain ⟨z,hz,he⟩ := intermediate_value_Icc hlh
    (residual_continuous rho lo hi (by linarith)) ⟨hlo,hhi⟩
  have hzpos : 0 < z := hl.trans_le hz.1
  exact ⟨z,hz,lift_stationary rho z (by positivity) he,
    reconstructed_positive rho z (by linarith [hr.1]) hzpos⟩

/-- Two distinct positive stationary states for every extraction rate in a
nonzero rational interval. This does not yet claim stability or copying. -/
theorem two_positive_stationary_states (rho : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100)) :
    (∃ z ∈ Icc (98172/100000:ℝ) (98174/100000),
      extractDrift rho 0 (lift rho z) = 0 ∧ ∀ i, 0 < lift rho z i) ∧
    (∃ z ∈ Icc (289014/100000:ℝ) (289017/100000),
      extractDrift rho 0 (lift rho z) = 0 ∧ ∀ i, 0 < lift rho z i) := by
  constructor
  · apply interval_root rho _ _ hr (by norm_num) (by norm_num)
    · norm_num [residual,reducedA,reducedB,reducedK]
    · norm_num [residual,reducedA,reducedB,reducedK]
  · apply interval_root rho _ _ hr (by norm_num) (by norm_num)
    · norm_num [residual,reducedA,reducedB,reducedK]
    · norm_num [residual,reducedA,reducedB,reducedK]

end
end ProductiveMemory
