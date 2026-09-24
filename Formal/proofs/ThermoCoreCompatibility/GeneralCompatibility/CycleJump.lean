import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace ThermoCoreCompatibility.GeneralCompatibility

theorem lifted_cycle_violation {T : ℝ → ℝ} {a b : ℝ}
    (hT : MonotoneOn T (Set.Ici 0)) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbad : b < T a) : b < T b :=
  lt_of_lt_of_le hbad (hT ha (ha.trans hab) hab)

theorem fixed_between_violation_and_prefixed {T : ℝ → ℝ} {a z : ℝ}
    (haz : a ≤ z) (hT : ContinuousOn T (Set.Icc a z))
    (ha : a < T a) (hz : T z ≤ z) :
    ∃ r, a < r ∧ r ≤ z ∧ T r = r := by
  have hc : ContinuousOn (fun x => T x - x) (Set.Icc a z) :=
    hT.sub continuousOn_id
  have hm : (0:ℝ) ∈ Set.Icc (T z-z) (T a-a) := ⟨by linarith, by linarith⟩
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc' haz hc hm
  have hf : T r = r := by linarith
  have har : a < r := by
    rcases hr.1.eq_or_lt with he | he
    · rw [← he] at hf
      linarith
    · exact he
  exact ⟨r, har, hr.2, hf⟩

theorem least_cycle_root_preserves_bound {T : ℝ → ℝ} {a u r z : ℝ}
    (hT : ContinuousOn T (Set.Icc a u)) (ha : a < T a)
    (hr : IsLeast {x | a < x ∧ x ≤ u ∧ T x = x} r)
    (hz0 : a ≤ z) (hzu : z ≤ u) (hz : T z ≤ z) : r ≤ z := by
  obtain ⟨s, has, hsz, hs⟩ := fixed_between_violation_and_prefixed hz0
    (hT.mono (Set.Icc_subset_Icc_right hzu)) ha hz
  exact (hr.2 ⟨has, hsz.trans hzu, hs⟩).trans hsz

theorem no_cycle_root_rejects_prefixed {T : ℝ → ℝ} {a u z : ℝ}
    (hT : ContinuousOn T (Set.Icc a u)) (ha : a < T a)
    (hnone : ¬ ∃ r, a < r ∧ r ≤ u ∧ T r = r)
    (hz0 : a ≤ z) (hzu : z ≤ u) : ¬ T z ≤ z := by
  intro hz
  obtain ⟨r, har, hrz, hr⟩ := fixed_between_violation_and_prefixed hz0
    (hT.mono (Set.Icc_subset_Icc_right hzu)) ha hz
  exact hnone ⟨r, har, hrz.trans hzu, hr⟩

end ThermoCoreCompatibility.GeneralCompatibility
