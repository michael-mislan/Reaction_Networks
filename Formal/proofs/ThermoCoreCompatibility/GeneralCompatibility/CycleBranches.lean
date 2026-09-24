import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

namespace ThermoCoreCompatibility.GeneralCompatibility

/-- A witnessed violation excludes an identity return map, even at zero margin. -/
theorem finite_cycle_roots_of_violation {T : ℝ → ℝ} {u a : ℝ}
    (ha : a ∈ Set.Icc 0 u) (hT : AnalyticOnNhd ℝ T (Set.Icc 0 u))
    (hviolation : a < T a) :
    {x | x ∈ Set.Icc 0 u ∧ T x = x}.Finite := by
  rcases hT.eqOn_or_eventually_ne_of_preconnected analyticOnNhd_id
      isPreconnected_Icc with hid | hne
  · have heq : T a = a := hid ha
    exact False.elim (ne_of_gt hviolation heq)
  · have hf := isCompact_Icc.finite_diff_of_mem_codiscreteWithin hne
    simpa only [Set.diff_eq, Set.compl_setOf, not_not, Set.inter_setOf_eq_sep] using hf

/-- A positive-at-zero analytic return map has finitely many fixed points in
a nonnegative compact interval. Source-map analyticity and composition are
separate docking obligations; no algorithmic cost is asserted here. -/
theorem finite_cycle_roots {T : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hT : AnalyticOnNhd ℝ T (Set.Icc 0 u)) (hzero : 0 < T 0) :
    {x | x ∈ Set.Icc 0 u ∧ T x = x}.Finite := by
  rcases hT.eqOn_or_eventually_ne_of_preconnected analyticOnNhd_id
      isPreconnected_Icc with hid | hne
  · have h := hid (show (0:ℝ) ∈ Set.Icc 0 u from ⟨le_rfl, hu⟩)
    have heq : T 0 = 0 := h
    exact False.elim (ne_of_gt hzero heq)
  · have hf := isCompact_Icc.finite_diff_of_mem_codiscreteWithin hne
    simpa only [Set.diff_eq, Set.compl_setOf, not_not, Set.inter_setOf_eq_sep] using hf

end ThermoCoreCompatibility.GeneralCompatibility
