import proofs.ThermoCoreCompatibility.BeyondJunction.TangentCounterexample

namespace ThermoCoreCompatibility.GeneralCompatibility

open MultiInterface BeyondJunction

def UnitMargin (x y : ℝ) : Prop :=
  unitFactors.lower x + 1/64 ≤ y ∧ y + 1/64 ≤ unitFactors.upper x

def SupportState (x y z : ℝ) : Prop :=
  1/8 ≤ x ∧ x ≤ 7/8 ∧ 1/16 ≤ y ∧ y ≤ 7/8 ∧ z = 41/64 ∧ UnitMargin x y

def FullState (x y z : ℝ) : Prop := SupportState x y z ∧ UnitMargin x z

theorem selected_state : SupportState (1/4) (9/64) (41/64) := by
  norm_num [SupportState, UnitMargin, unitFactors, Factors.lower, Factors.upper]

theorem global_state : FullState (3/4) (41/64) (41/64) := by
  norm_num [FullState, SupportState, UnitMargin, unitFactors, Factors.lower, Factors.upper]

theorem support_least {x y z : ℝ} (h : SupportState x y z) :
    1/4 ≤ x ∧ 9/64 ≤ y ∧ 41/64 ≤ z := by
  obtain ⟨hx0, _, _, _, hz, hl, hu⟩ := h
  have hx : (1/4:ℝ) ≤ x := by
    norm_num [unitFactors, Factors.lower, Factors.upper] at hl hu
    by_contra hn
    have ht : x < 1/4 := lt_of_not_ge hn
    have hp := mul_pos (show 0 < 1/4-x by linarith) (show 0 < 3/4-x by linarith)
    nlinarith
  have hm := unitFactors.lower_strictMono.monotoneOn (by norm_num : (0:ℝ) ≤ 1/4)
    (show 0 ≤ x by linarith) hx
  norm_num [unitFactors, Factors.lower] at hm hl
  exact ⟨hx, by linarith, by linarith⟩

theorem full_least {x y z : ℝ} (h : FullState x y z) :
    3/4 ≤ x ∧ 41/64 ≤ y ∧ 41/64 ≤ z := by
  obtain ⟨⟨hx0, _, _, _, hz, hl, _⟩, _, hu⟩ := h
  have hx : (3/4:ℝ) ≤ x := by
    norm_num [unitFactors, Factors.upper] at hu
    by_contra hn
    have ht : x < 3/4 := lt_of_not_ge hn
    have hp := mul_pos (show 0 < 3/4-x by linarith) (show 0 < 7/4+x by linarith)
    nlinarith
  have hm := unitFactors.lower_strictMono.monotoneOn (by norm_num : (0:ℝ) ≤ 3/4)
    (show 0 ≤ x by linarith) hx
  norm_num [unitFactors, Factors.lower] at hm hl
  exact ⟨hx, by linarith, by linarith⟩

theorem selected_support_is_tight_at_global :
    unitFactors.lower (3/4) + 1/64 = (41/64:ℝ) ∧
    (41/64:ℝ) + 1/64 = unitFactors.upper (3/4) := by
  norm_num [unitFactors, Factors.lower, Factors.upper]

theorem selected_least_not_global : ¬ FullState (1/4) (9/64) (41/64) := by
  norm_num [FullState, SupportState, UnitMargin, unitFactors, Factors.lower, Factors.upper]

end ThermoCoreCompatibility.GeneralCompatibility
