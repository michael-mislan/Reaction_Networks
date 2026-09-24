import proofs.SandwichImmunoassay.Robust

namespace SandwichImmunoassay

/-! ### The hook involution `u ↦ (C+K)^2/u`. -/

theorem Occupancy.involution {u C K p : ℝ} (h : Occupancy u C K p) (hu : 0 < u) :
    Occupancy ((C+K)^2/u) C K (u*p/(C+K)) := by
  have cp := h.total_pos
  have kp := h.kd_pos
  have pp := h.pos
  have S : 0 < C+K := by linarith only [cp,kp]
  have up : u*p < C+K := by linarith only [h.total_bound,kp]
  have poly := h.polynomial
  refine ⟨by positivity, cp, kp, by positivity, (div_lt_one S).2 up, ?_⟩
  have hS : C+K ≠ 0 := S.ne'
  have hne : C+K-u*p ≠ 0 := ne_of_gt (sub_pos.mpr up)
  have e1 : (C+K)^2/u*(u*p/(C+K)) = (C+K)*p := by field_simp
  have e0 : 1-u*p/(C+K) = (C+K-u*p)/(C+K) := by field_simp
  have e2 : K*(u*p/(C+K))/((C+K-u*p)/(C+K)) = K*(u*p)/(C+K-u*p) := by field_simp
  have e3 : K*(u*p)/(C+K-u*p) = C-(C+K)*p := by
    rw [div_eq_iff hne]
    linear_combination -(C+K)*poly
  rw [e1,e0,e2,e3]
  ring

theorem signal_involution {u C D K J p q : ℝ}
    (h : Reaction u C D K J p q) (hu : 0 < u) (hS : C+K = D+J) :
    Reaction ((C+K)^2/u) C D K J (u*p/(C+K)) (u*q/(C+K)) ∧
    signal ((C+K)^2/u) (u*p/(C+K)) (u*q/(C+K)) = signal u p q := by
  have S : 0 < C+K := by linarith only [h.capture.total_pos,h.capture.kd_pos]
  have hne : C+K ≠ 0 := S.ne'
  refine ⟨⟨h.capture.involution hu, ?_⟩, ?_⟩
  · have det := h.detector.involution hu
    rw [← hS] at det
    exact det
  · unfold signal
    field_simp

end SandwichImmunoassay
