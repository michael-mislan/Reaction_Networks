import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
namespace PersisterMemory
/-- The bracket left after differentiating the remaining-budget product. -/
theorem remaining_budget_sign (V s drift : ℝ) (hV : 0 ≤ V)
    (hd : drift ≤ s) : V*(s-drift) ≥ 0 :=
  mul_nonneg hV (sub_nonneg.mpr hd)

/-- Product differentiation step used inductively for an arbitrary population. -/
theorem product_derivative_step (p dp q dq : ℝ) :
    -(dp*q+p*dq) = -dp*q-p*dq := by ring

theorem population_budget_bracket (V q phi c v : ℝ) :
    -V*phi/q + v*(V*c*(1-q)/q) =
      V/q*(c*v*(1-q)-phi) := by ring
end PersisterMemory
