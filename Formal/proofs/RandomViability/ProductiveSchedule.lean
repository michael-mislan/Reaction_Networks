import Mathlib.Tactic

namespace RandomViability

def productiveLigations (m i : ℕ) : ℕ :=
  if i ≤ m then i else m+(i-m+1)/2

def productiveExports (m i : ℕ) : ℕ :=
  if i ≤ m then 0 else (i-m)/2

def productiveLigationStep (m i : ℕ) : Prop := i < m ∨ (i-m)%2 = 0

theorem productive_schedule_bounds (m i : ℕ) (hi : i ≤ 3*m) :
    productiveExports m i ≤ productiveLigations m i ∧
    productiveLigations m i ≤ 2*m ∧ productiveExports m i ≤ m := by
  unfold productiveLigations productiveExports
  split_ifs <;> omega

theorem productive_schedule_positive (m i : ℕ) (hm : 0 < m) (hi : 0 < i) :
    productiveExports m i < productiveLigations m i := by
  unfold productiveLigations productiveExports
  split_ifs <;> omega

theorem productive_schedule_ligation (m i : ℕ) (hs : productiveLigationStep m i) :
    productiveLigations m (i+1) = productiveLigations m i+1 ∧
    productiveExports m (i+1) = productiveExports m i := by
  unfold productiveLigations productiveExports productiveLigationStep at *
  split_ifs <;> omega

theorem productive_schedule_export (m i : ℕ) (hs : ¬productiveLigationStep m i) :
    productiveLigations m (i+1) = productiveLigations m i ∧
    productiveExports m (i+1) = productiveExports m i+1 := by
  unfold productiveLigations productiveExports productiveLigationStep at *
  split_ifs <;> omega

theorem productive_schedule_operating (m i : ℕ) (hi : m ≤ i) :
    m ≤ productiveLigations m i-productiveExports m i ∧
    productiveLigations m i-productiveExports m i ≤ m+1 := by
  unfold productiveLigations productiveExports
  split_ifs <;> omega

theorem productive_schedule_endpoints (m : ℕ) :
    productiveLigations m 0 = 0 ∧ productiveExports m 0 = 0 ∧
    productiveLigations m m = m ∧ productiveExports m m = 0 ∧
    productiveLigations m (3*m) = 2*m ∧ productiveExports m (3*m) = m := by
  unfold productiveLigations productiveExports
  split_ifs <;> omega

theorem productive_volume_rounding (V : ℕ) (hV : 40 ≤ V) :
    0 < (V+9)/10 ∧ 4*((V+9)/10) ≤ V ∧ V ≤ 10*((V+9)/10) ∧
    20*((V+9)/10+1) ≤ 3*V := by omega

end RandomViability
