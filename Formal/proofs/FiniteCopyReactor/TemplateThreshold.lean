import proofs.FiniteCopyReactor.Template

namespace FiniteCopyReactor
noncomputable section
open RandomViability.Binding

theorem template_ceiling_failure_subset (V : ℕ) (s : BoxCounts V × ℝ)
    (h : residenceActive V s.1 ∧ s.2 < (Nat.ceil ((V:ℝ)/56):ℝ)) :
    residenceActive V s.1 ∧ s.2 ≤ (V:ℝ)/56+1 := by
  refine ⟨h.1,?_⟩
  exact (h.2.trans (Nat.ceil_lt_add_one (show 0 ≤ (V:ℝ)/56 by positivity))).le

end
end FiniteCopyReactor
