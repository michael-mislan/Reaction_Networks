import proofs.RandomViability.BindingCompetitionSuppliedOperating

namespace RandomViability.Binding
noncomputable section
open Classical

theorem competition_counter_next_coordinate {C : ℕ} (c : CompetitionGrossCounters C)
    (label : Option (Fin 4)) (i : Fin 4) :
    (competitionCounterNext c label i).val = min C ((c i).val+(if label=some i then 1 else 0)) := by
  have hc : (c i).val ≤ C := by have := (c i).isLt; omega
  cases label with
  | none => simp [competitionCounterNext,hc]
  | some j =>
    by_cases hij : i=j
    · subst j
      simp [competitionCounterNext]
    · simp [competitionCounterNext,hij,Ne.symm hij,hc]

theorem competition_counter_history_coordinate {C : ℕ} (c : CompetitionGrossCounters C)
    (labels : List (Option (Fin 4))) (i : Fin 4) :
    (labels.foldl competitionCounterNext c i).val=
      min C ((c i).val+(labels.map (fun label => if label=some i then 1 else 0)).sum) := by
  induction labels generalizing c with
  | nil =>
    have hc : (c i).val ≤ C := by have := (c i).isLt; omega
    simp [hc]
  | cons label labels ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    rw [ih,competition_counter_next_coordinate,competition_saturate_step]
    congr 1
    omega

theorem competition_cap_preserves_real_failure (C n : ℕ) (limit : ℝ) (hlimit : limit<(C:ℝ)) :
    limit<((min C n:ℕ):ℝ) ↔ limit<(n:ℝ) := by
  by_cases hn : C ≤ n
  · rw [Nat.min_eq_left hn]
    have hh : (C:ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨fun _ => hlimit.trans_le hh,fun _ => hlimit⟩
  · rw [Nat.min_eq_right (by omega : n≤C)]

theorem competition_cap_preserves_sum_failure (C a b : ℕ) (limit : ℝ) (hlimit : limit<(C:ℝ)) :
    limit<((min C a:ℕ):ℝ)+((min C b:ℕ):ℝ) ↔ limit<(a:ℝ)+(b:ℝ) := by
  by_cases ha : C ≤ a
  · rw [Nat.min_eq_left ha]
    have ha' : (C:ℝ) ≤ a := by exact_mod_cast ha
    have hn : 0 ≤ ((min C b:ℕ):ℝ) := Nat.cast_nonneg _
    have hb : 0 ≤ (b:ℝ) := Nat.cast_nonneg _
    constructor <;> intro _ <;> linarith
  · rw [Nat.min_eq_right (by omega : a≤C)]
    by_cases hb : C ≤ b
    · rw [Nat.min_eq_left hb]
      have hb' : (C:ℝ) ≤ b := by exact_mod_cast hb
      have hn : 0 ≤ (a:ℝ) := Nat.cast_nonneg _
      constructor <;> intro _ <;> linarith
    · rw [Nat.min_eq_right (by omega : b≤C)]

theorem competition_fuel_threshold_below_cap (V : ℕ) :
    (V:ℝ)*(500+competitionDuration V)/8<(competitionSupplyCap V:ℝ) := by
  have hh := competition_supply_cap_strict V
  have hn : 0 ≤ (V:ℝ)*(500+competitionDuration V) := by unfold competitionDuration; positivity
  linarith

end
end RandomViability.Binding
