import proofs.RandomViability.BindingCompetitionThroughput
import proofs.RandomViability.BindingCompetitionScalarBounds

namespace RandomViability.Binding
noncomputable section

theorem competition_windows_time_lower (V : ℕ) (hV : 100000000 ≤ V) :
    (500+competitionDuration V)/4 ≤ (competitionWindowNumber V:ℝ) := by
  have hd := competition_duration_large V hV
  have hp := competition_horizon_partition V
  have hf := competition_fraction_lt_one V
  linarith

theorem competition_windows_time_upper (V : ℕ) (hV : 100000000 ≤ V) :
    500+competitionDuration V ≤ 502*(competitionWindowNumber V:ℝ) := by
  have hd := competition_duration_large V hV
  have hp := competition_horizon_partition V
  have hf := competition_fraction_lt_one V
  linarith

theorem competition_total_export_scaling (V : ℕ) (hV : 100000000 ≤ V)
    (exports : List ℕ) (hlen : exports.length=competitionWindowNumber V)
    (he : ∀ x ∈ exports,(V:ℝ)/5000 ≤ (x:ℝ)) :
    (V:ℝ)*(500+competitionDuration V)/20000 ≤ (exports.sum:ℝ) := by
  have hw := competition_window_total_export V exports he
  rw [hlen] at hw
  have ht := mul_le_mul_of_nonneg_left (competition_windows_time_lower V hV) (Nat.cast_nonneg (α := ℝ) V)
  linarith

/-- Sustained exported mass forces replenishment proportional to the full horizon. -/
theorem competition_input_lower_scaling (V : ℕ) (hV : 100000000 ≤ V) (input output : ℝ)
    (he : (V:ℝ)*(500+competitionDuration V)/20000 ≤ output)
    (hb : output ≤ 4*(V:ℝ)+input) :
    (V:ℝ)*(500+competitionDuration V)/40000 ≤ input := by
  have hd := competition_duration_large V hV
  have hm := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) V)
  linarith

end
end RandomViability.Binding
