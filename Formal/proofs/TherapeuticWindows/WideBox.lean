import proofs.TherapeuticWindows.Robustness
import proofs.TherapeuticWindows.Delivery

noncomputable section
namespace TherapeuticWindows

theorem tighter_contraction (e : ℝ) (lo : 29/100 ≤ e) (hi : e ≤ 31/100)
    (i : Fin 6) : meanAction e weight i ≤ -(99/1000)*weight i := by
  fin_cases i <;> norm_num [meanAction, chemistry, expectedDaughters, deaths, weight] <;> linarith

theorem tighter_growth (e : ℝ) (lo : 1/100 ≤ e) (hi : e ≤ 31/100)
    (i : Fin 6) : meanAction e weight i ≤ (67/500)*weight i := by
  fin_cases i <;> norm_num [meanAction, chemistry, expectedDaughters, deaths, weight] <;> linarith

def relativeEnvelope (e : ℝ) (i : Fin 6) : ℝ :=
  (∑ j : Fin 6, if i.val=j.val then 0 else
    chemistry e (fun l => if l.val=j.val then 1 else 0) i * |weight j-weight i|) +
  |expectedDaughters weight i-weight i|/10 + deaths i*weight i

theorem relative_envelope_bound (e : ℝ) (_lo : 1/100 ≤ e) (hi : e ≤ 31/100)
    (i : Fin 6) : relativeEnvelope e i ≤ (27/20)*weight i := by
  fin_cases i <;> norm_num [relativeEnvelope, Fin.sum_univ_succ, chemistry,
    expectedDaughters, deaths, weight] <;> linarith

theorem wide_box_arithmetic :
    (99/1000 : ℚ)-27/2000 = 171/2000 ∧
    (67/500 : ℚ)+27/2000 = 59/400 ∧
    (108 : ℚ)*(171/2000)-4*(59/400) = 2161/250 ∧
    (43/5 : ℚ) < 2161/250 ∧
    (214/5 : ℚ)/5000 = 107/12500 ∧
    (107/12500 : ℚ) < 1/100 := by norm_num

set_option maxRecDepth 2048 in
theorem wide_exponential_certificate : 5000 < expLower (43/5) 30 := by
  norm_num [expLower, Finset.sum_range_succ, Nat.factorial]

end TherapeuticWindows
