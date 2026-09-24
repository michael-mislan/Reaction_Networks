import proofs.SandwichImmunoassay.Robust

noncomputable section

namespace SandwichImmunoassay

def accessibleAction (x rho d s : ℝ) : ℝ := rho*x/d+s

theorem masking_action_equivalence {x y rho sigma : ℝ} (h : rho*x=sigma*y)
    (d s : ℝ) (response : ℝ → ℝ) :
    response (accessibleAction x rho d s) = response (accessibleAction y sigma d s) := by
  simp only [accessibleAction, h]

theorem masking_low_high_witness (d s : ℝ) (response : ℝ → ℝ) :
    response (accessibleAction (1/10) 1 d s) =
      response (accessibleAction 100 (1/1000) d s) := by
  apply masking_action_equivalence
  norm_num

theorem availability_repair {x rho lo hi rmin rmax : ℝ}
    (hx : 0 ≤ x) (hrmin : 0 < rmin) (hr : rmin ≤ rho)
    (hrmax : rho ≤ rmax) (hlo : lo ≤ rho*x) (hhi : rho*x ≤ hi) :
    lo/rmax ≤ x ∧ x ≤ hi/rmin := by
  have rp : 0 < rmax := by linarith
  constructor
  · apply (div_le_iff₀ rp).2
    nlinarith [mul_le_mul_of_nonneg_right hrmax hx]
  · apply (le_div_iff₀ hrmin).2
    nlinarith [mul_le_mul_of_nonneg_right hr hx]

theorem native_low {x rho : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1/10)
    (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) : 0 ≤ rho*x ∧ rho*x ≤ 1/10 := by
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_right hr1 hx0]

theorem native_high {x rho : ℝ} (hx0 : 25 ≤ x) (hx1 : x ≤ 100)
    (hr0 : 4/5 ≤ rho) (hr1 : rho ≤ 1) : 20 ≤ rho*x ∧ rho*x ≤ 100 := by
  have xp : 0 ≤ x := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hr0 xp]
  · nlinarith [mul_le_mul_of_nonneg_right hr1 xp]

/-- For arbitrary shared response, no rule on the complete action function separates
the masking worlds. This includes any deterministic adaptive querying procedure. -/
theorem no_masking_classifier (response : ℝ → ℝ)
    (rule : (ℝ → ℝ → ℝ) → Bool) :
    ¬ (rule (fun d s => response (accessibleAction (1/10) 1 d s)) = false ∧
       rule (fun d s => response (accessibleAction 100 (1/1000) d s)) = true) := by
  have eqn : (fun d s => response (accessibleAction (1/10) 1 d s)) =
      (fun d s => response (accessibleAction 100 (1/1000) d s)) := by
    funext d s
    exact masking_low_high_witness d s response
  rw [eqn]
  intro h
  have j := h.2
  rw [h.1] at j
  contradiction

end SandwichImmunoassay
