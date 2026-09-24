import proofs.RandomViability.BindingCompetitionWindowProbability

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def competitionWindowCap (V : ℕ) : ℕ := ⌈(V:ℝ)/5000⌉₊

theorem competition_window_cap_upper (V : ℕ) :
    (competitionWindowCap V:ℝ) ≤ (V:ℝ)/5000+1 :=
  (Nat.ceil_lt_add_one (show 0 ≤ (V:ℝ)/5000 by positivity)).le

theorem competition_saturate_step (C n mark : ℕ) :
    min C (min C n+mark) = min C (n+mark) := by omega

theorem competition_saturate_history (C n : ℕ) (marks : List ℕ) :
    marks.foldl (fun count mark => min C (count+mark)) (min C n) = min C (n+marks.sum) := by
  induction marks generalizing n with
  | nil => simp
  | cons mark marks ih =>
    simp only [List.foldl_cons,competition_saturate_step,List.sum_cons]
    rw [ih]
    congr 1
    omega

theorem competition_insufficient_iff (V total : ℕ) :
    min (competitionWindowCap V) total < competitionWindowCap V ↔ (total:ℝ)<(V:ℝ)/5000 := by
  have h : min (competitionWindowCap V) total < competitionWindowCap V ↔ total<competitionWindowCap V := by omega
  rw [h]
  exact Nat.lt_ceil

/-- Rounded cap, one physical time unit, uniformly over the full initial state.
No independence or reactor restart is a premise. -/
theorem competition_unit_window_probability (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (q : ℝ≥0) (hq : 0 < (q:ℝ)) (hclock : (V:ℝ)/27000 ≤ q)
    (hb : ∀ X, (competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk hr hd).total X ≤ q)
    (X : CompetitionWindowState V (competitionWindowCap V)) :
    ((competitionWindowModel V (competitionWindowCap V) eps k r delta hV heps hk hr hd).uniformize q hq hb).poissonized q
      (FiniteKernel.eventIndicator {Z | competitionWindowActive Z}) X ≤
      Real.exp (1/8-(13/1080000)*(V:ℝ)) := by
  have h := competition_window_probability eps k r delta hV heps hk hr hd q 1 hq hclock hb X
  norm_num only [mul_one,NNReal.coe_one,one_mul] at h
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hc := competition_window_cap_upper V
  linarith

end
end RandomViability.Binding
