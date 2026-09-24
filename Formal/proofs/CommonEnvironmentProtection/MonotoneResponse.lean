import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace CommonEnvironmentProtection

/-- Endpoint signs are necessary and sufficient for a unique zero in the
admitted service band. Continuity and strict decrease are explicit obligations. -/
theorem safe_equilibrium_iff (H : ℝ → ℝ) (L U : ℝ) (hLU : L ≤ U)
    (hc : ContinuousOn H (Set.Icc L U)) (hd : StrictAntiOn H (Set.Icc L U)) :
    (∃! r, r ∈ Set.Icc L U ∧ H r = 0) ↔ 0 ≤ H L ∧ H U ≤ 0 := by
  constructor
  · rintro ⟨r, ⟨hr, hz⟩, _⟩
    constructor
    · have h := hd.antitoneOn ⟨le_rfl, hLU⟩ hr hr.1
      linarith
    · have h := hd.antitoneOn hr ⟨hLU, le_rfl⟩ hr.2
      linarith
  · rintro ⟨hl, hu⟩
    obtain ⟨r, hr, hz⟩ := intermediate_value_Icc' hLU hc ⟨hu, hl⟩
    refine ⟨r, ⟨hr, hz⟩, ?_⟩
    intro y hy
    exact hd.injOn hy.1 hr (hy.2.trans hz.symm)

end CommonEnvironmentProtection
