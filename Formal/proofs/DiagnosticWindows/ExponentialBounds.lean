import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

noncomputable section
namespace DiagnosticWindows
open scoped BigOperators

def taylor12 (x : ℝ) : ℝ := ∑ m ∈ Finset.range 12, x^m/(m.factorial:ℝ)
def error12 (x : ℝ) : ℝ := |x|^12 * (13/((12:ℕ).factorial*12:ℝ))

/-- All numeric exponential certificates reduce to rational inequalities here. -/
theorem exp_enclosure16 (x l u : ℝ) (hx : |x/16| ≤ 1) (hl : 0 ≤ l)
    (hlo : l ≤ taylor12 (x/16)-error12 (x/16))
    (hhi : taylor12 (x/16)+error12 (x/16) ≤ u) :
    l^16 ≤ Real.exp x ∧ Real.exp x ≤ u^16 := by
  have ht := Real.exp_bound hx (n := 12) (by norm_num)
  change |Real.exp (x/16)-taylor12 (x/16)| ≤ error12 (x/16) at ht
  have heL : l ≤ Real.exp (x/16) := by linarith [(abs_le.mp ht).1]
  have heU : Real.exp (x/16) ≤ u := by linarith [(abs_le.mp ht).2]
  have he : Real.exp x = Real.exp (x/16)^16 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  exact ⟨pow_le_pow_left₀ hl heL 16,
    pow_le_pow_left₀ (Real.exp_pos _).le heU 16⟩

end DiagnosticWindows
