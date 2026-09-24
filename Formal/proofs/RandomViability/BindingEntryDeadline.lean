import proofs.RandomViability.BindingEntryProbability

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def operatingEntryKernel (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) : FiniteKernel (BoxCounts 100000000) :=
  (entryModel 100000000 40000 (1/500000000) k r (by norm_num) (by norm_num) hk (by linarith)).uniformize
    300000000000 (by norm_num) (by
      intro N
      have hb := entry_total_bound 100000000 40000 (1/500000000) k r (by norm_num)
        (by norm_num) (by norm_num) hk hk1 (by linarith) hr1 N
      norm_num at hb
      exact hb)

theorem operating_entry_discrete (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (n : ℕ) (hn : 149700000000000 ≤ n)
    (N : BoxCounts 100000000) :
    (operatingEntryKernel k r hk hk1 hr hr1).steps n
      (FiniteKernel.eventIndicator {X | entryActive 100000000 40000 X}) N ≤ 1/12 := by
  have hbound (X : BoxCounts 100000000) :
      (entryModel 100000000 40000 (1/500000000) k r (by norm_num) (by norm_num) hk (by linarith)).total X ≤
        (300000000000:ℝ) := by
    have hb := entry_total_bound 100000000 40000 (1/500000000) k r (by norm_num)
      (by norm_num) (by norm_num) hk hk1 (by linarith) hr1 X
    norm_num at hb
    exact hb
  have h := entry_discrete_after_startup 100000000 300000000000 40000 (1/500000000) k r
    (by norm_num) (by norm_num) (by norm_num) hk hk1 hr hr1 (by norm_num) (by norm_num)
    hbound (n-30000000000000) N
  have he : n-30000000000000+100*300000000000 = n := by omega
  rw [he] at h
  have hm : (119700000000000:ℝ) ≤ (n-30000000000000:ℕ) := by exact_mod_cast (show 119700000000000 ≤ n-30000000000000 by omega)
  have hh : (40000:ℝ)/40000-
      ((14/25)*(1/500000000)*100000000*(2/25)/300000000000)*(n-30000000000000:ℕ) ≤ -8047/3125 := by
    linarith
  exact (h.trans (Real.exp_le_exp.mpr hh)).trans entry_scalar_budget.le

/-- Evaluated no-entry/no-resource-exit probability in the exact auxiliary
count kernel. The absorption is only for this event; residence uses continued counts. -/
theorem operating_entry_deadline (k r : ℝ) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (N : BoxCounts 100000000) :
    (operatingEntryKernel k r hk hk1 hr hr1).poissonized 150000000000000
      (FiniteKernel.eventIndicator {X | entryActive 100000000 40000 X}) N <
        1/12+1/600000000 := by
  have h := poissonized_after_cutoff (operatingEntryKernel k r hk hk1 hr hr1)
    {X | entryActive 100000000 40000 X} N 150000000000000 149700000000000 (1/12) (999/1000)
    (by norm_num) (by norm_num) (by norm_num)
    (fun n hn => operating_entry_discrete k r hk hk1 hr hr1 n hn N)
  have hc := clock_exponent_bound 300000000000 (by norm_num)
  have he : Real.exp (-(149700000000000*Real.log (999/1000))+ -150000000000) ≤
      Real.exp (-600000) := Real.exp_le_exp.mpr (by norm_num at hc; linarith)
  norm_num at h
  have hb := evaluated_clock_error
  norm_num at hb
  linarith

end
end RandomViability.Binding
