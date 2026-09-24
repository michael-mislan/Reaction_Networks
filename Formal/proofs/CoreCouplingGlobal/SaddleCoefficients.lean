import proofs.CoreCouplingGlobal.QuadraticConeSides
import proofs.CoreCouplingGlobal.EquilibriumBarrier

namespace CoreCouplingGlobal
open CoreCouplingCAC

noncomputable def localWeight (z : ℝ) : ℝ := (z+1)*(z+2)
noncomputable def localForkSlope (e B z : ℝ) : ℝ :=
  (1-responseSlope e B/(z+1))/(B*(z+2))
noncomputable def localHSlope (z : ℝ) : ℝ := 3/((16+4*z)*localWeight z)

theorem local_response_coefficients (e A B z : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12) :
    99/100 ≤ 1+e*(A+responseA e B) ∧ 1+e*(A+responseA e B) ≤ 101/100 ∧
    -(1/500) ≤ responseSlope e B ∧ responseSlope e B ≤ 1/500 ∧
    1/500 ≤ localForkSlope e B z ∧ localForkSlope e B z ≤ 13/50 ∧
    2 ≤ localWeight z ∧ localWeight z ≤ 182 ∧ 1/4000 ≤ localHSlope z ∧
    localForkSlope e B z*B*localWeight z = 1+z-responseSlope e B ∧
    localHSlope z*(16+4*z)*localWeight z = 3 := by
  obtain ⟨ha,ha',hc,hc'⟩ := response_coefficient_bounds e A B he hu hA hA' hB hB'
  have hden : 4 ≤ B*(z+2) := by nlinarith
  have hden' : B*(z+2) ≤ 476 :=
    (mul_le_mul hB' (by linarith : z+2 ≤ 14) (by positivity) (by norm_num)).trans (by norm_num)
  obtain ⟨hm,hm'⟩ := fork_gradient_coefficient B (responseSlope e B) z (by linarith) hden hden' hc hc'
  have hw : 2 ≤ localWeight z := by unfold localWeight; nlinarith
  have hw' : localWeight z ≤ 182 := by unfold localWeight; nlinarith [sq_nonneg (z-12)]
  have hw0 : 0 < localWeight z := by linarith
  have hC : 0 < 16+4*z := by positivity
  refine ⟨ha,ha',hc,hc',hm,hm',hw,hw',?_,?_,?_⟩
  · unfold localHSlope
    apply (le_div_iff₀ (mul_pos hC hw0)).2
    have hp := mul_le_mul (show 16+4*z ≤ 64 by linarith) hw' hw0.le (by norm_num : (0:ℝ) ≤ 64)
    nlinarith
  · unfold localForkSlope localWeight
    have hB0 : B ≠ 0 := by linarith
    have hz1 : z+1 ≠ 0 := by positivity
    have hz2 : z+2 ≠ 0 := by positivity
    field_simp
    ring
  · unfold localHSlope
    field_simp

/-- Positivity on zero B displacement, using the explicit response coefficients. -/
theorem state_quadratic_B_plane_positive (e : ℝ)
    (s : State) (hs : s.Positive)
    (hB : 8 ≤ s.B) (ζ η r : ℝ) (hn : ζ ≠ 0 ∨ η ≠ 0 ∨ r ≠ 0) :
    0 < responseQuadratic s.B s.z (localForkSlope e s.B s.z) (localWeight s.z) (localHSlope s.z) 0 ζ η r := by
  have hz0 := hs.2.2.1.le
  have hw : 0 < localWeight s.z := by unfold localWeight; positivity
  exact quadratic_B_plane_positive s.B s.z (localForkSlope e s.B s.z) (localWeight s.z) ζ η r hB hz0 hw hn

end CoreCouplingGlobal
