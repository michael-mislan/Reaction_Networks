import Mathlib

namespace CommonPhysicalRealization
noncomputable section

/-- The gross bill bounds absolute work of this reservoir pair alone. -/
theorem chemical_work_bound (force f p cap : ℝ) (hf : 0 ≤ f) (hp : 0 ≤ p)
    (hcap : f+p ≤ cap) : |force*(f-p)| ≤ |force| * cap := by
  rw [abs_mul]
  have h : |f-p| ≤ f+p := by
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_mul_of_nonneg_left (h.trans hcap) (abs_nonneg force)

/-- A finite bath can keep activities within a tolerance, but this alone does
not preserve the donor's fixed reverse/forward ratio. -/
theorem stock_tolerance (initial current budget rho : ℝ) (hi : 0 < initial)
    (hdev : |current-initial| ≤ budget) (hstock : budget ≤ rho*initial) :
    1-rho ≤ current/initial ∧ current/initial ≤ 1+rho := by
  have h := abs_le.mp (hdev.trans hstock)
  constructor
  · apply (le_div_iff₀ hi).mpr
    nlinarith [h.1]
  · apply (div_le_iff₀ hi).mpr
    nlinarith [h.2]

theorem paired_ratio_changed (d eta aF aP : ℝ) (hd : 0 < d) (ha : 0 < aF) :
    (d*eta*aP)/(d*aF)=eta*(aP/aF) := by
  field_simp [ne_of_gt hd,ne_of_gt ha]

end
end CommonPhysicalRealization
