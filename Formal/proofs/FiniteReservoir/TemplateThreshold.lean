import proofs.FiniteReservoir.Template

namespace FiniteReservoir
noncomputable section
open RandomViability.Binding FiniteCopyReactor

theorem template_ceiling_failure_subset (V M : ℕ) (s : BoxState V M × ℝ)
    (h : residenceActive V s.1.1 ∧ s.2 < (Nat.ceil ((V:ℝ)/56):ℝ)) :
    residenceActive V s.1.1 ∧ s.2 ≤ (V:ℝ)/56+1 := by
  refine ⟨h.1,?_⟩
  exact (h.2.trans (Nat.ceil_lt_add_one (show 0 ≤ (V:ℝ)/56 by positivity))).le

end
end FiniteReservoir
