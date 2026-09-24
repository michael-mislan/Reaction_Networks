import proofs.TherapeuticWindows.Source
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace TherapeuticWindows

/-- Triangle-inequality envelope for the explicit chemistry/division/death box. -/
def perturbationEnvelope (e : ℝ) (i : Fin 6) : ℝ :=
  (∑ j : Fin 6, if i.val=j.val then 0 else
    chemistry e (fun l => if l.val=j.val then 1 else 0) i * |weight j-weight i|)/10000 +
  |expectedDaughters weight i-weight i|/100000 + weight i/100000

theorem perturbation_budget (e : ℝ) (_lo : 1/100 ≤ e) (hi : e ≤ 31/100)
    (i : Fin 6) : perturbationEnvelope e i ≤ weight i/1000 := by
  fin_cases i <;>
    norm_num [perturbationEnvelope, Fin.sum_univ_succ, chemistry,
      expectedDaughters, weight] <;> linarith

end TherapeuticWindows
