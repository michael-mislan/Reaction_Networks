import proofs.FiniteCopyReactor.FreeCollection

namespace FiniteCopyReactor
noncomputable section
open RandomViability.Binding

/-- The proved shortfall event contains failure of the required integer target. -/
theorem free_ceiling_failure_subset (V : ℕ) (s : BoxCounts V × ℝ)
    (h : residenceActive V s.1 ∧ s.2 < (Nat.ceil ((V:ℝ)/1080):ℝ)) :
    s ∈ FreeShortfall V ((V:ℝ)/1080+1) := by
  refine ⟨h.1,?_⟩
  exact (h.2.trans (Nat.ceil_lt_add_one (show 0 ≤ (V:ℝ)/1080 by positivity))).le

end
end FiniteCopyReactor
