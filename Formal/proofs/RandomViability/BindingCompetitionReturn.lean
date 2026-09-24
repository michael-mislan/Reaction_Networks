import proofs.RandomViability.BindingCompetitionEntryKernel

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def competitionReturnPotential (V : ℝ) (N : Counts) : ℝ :=
  Real.exp (-(2/25)*(weightedCount N-V/5000))

def competitionReturnSource (V : ℝ) : ℝ := 3000*V*Real.exp (18/125-V/15625)

theorem competition_generator_scale (N : Counts) (V eps k r delta c : ℝ) (f : Counts → ℝ) :
    competitionGenerator N V eps k r delta (fun X => c*f X) =
      c*competitionGenerator N V eps k r delta f := by
  unfold competitionGenerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem competition_return_small (V : ℝ) (N : Counts) (h : V/2500 ≤ weightedCount N) :
    competitionReturnPotential V N ≤ Real.exp (-V/62500) := by
  apply Real.exp_le_exp.mpr
  linarith

theorem competition_return_exit (V : ℝ) (N : Counts) (h : weightedCount N ≤ V/5000) :
    1 ≤ competitionReturnPotential V N := by
  apply Real.one_le_exp_iff.mpr
  linarith

theorem competition_return_low (N : Counts) (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (h : resourceGood N V)
    (hY : weightedCount N ≤ (V:ℝ)/1000) :
    competitionGenerator N V eps k r delta (competitionReturnPotential V) ≤ 0 := by
  have he : competitionReturnPotential V =
      (fun X => Real.exp ((V:ℝ)/62500)*Real.exp (-(2/25)*weightedCount X)) := by
    funext X
    unfold competitionReturnPotential
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he,competition_generator_scale]
  have hg := competition_entry_exponential N V eps k r delta (2/25) hV
    heps heps1 hk hk1 hr hr1 hd hd1 h hY (by norm_num) (by norm_num)
  have hy := weightedCount_nonneg N
  have hp : 0 ≤ eps*(V:ℝ) := by positivity
  have hn : -(3/10*(2/25)-3*(2/25)^2)*weightedCount N-(14/25)*eps*(V:ℝ)*(2/25) ≤ 0 := by
    nlinarith
  have hh := hg.trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hn)
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hh

theorem competition_return_high (N : Counts) (V eps k r delta : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) (hd : 0 ≤ delta)
    (hY : V/1000 ≤ weightedCount N)
    (htotal : (∑ j,competitionRate N V eps k r delta j) ≤ 3000*V) :
    competitionGenerator N V eps k r delta (competitionReturnPotential V) ≤ competitionReturnSource V := by
  have hm : competitionGenerator N V eps k r delta (competitionReturnPotential V) ≤
      (∑ j,competitionRate N V eps k r delta j)*Real.exp (18/125-V/15625) := by
    rw [competitionGenerator,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    by_cases hz : competitionRate N V eps k r delta j = 0
    · simp [hz]
    · have hj := weighted_actual_jump N (competitionBase j)
        (competition_rate_support N V eps k r delta j hz)
      have hb := (abs_le.mp (weightedJump_bound (competitionBase j))).1
      have hnext : competitionReturnPotential V (competitionNext N j) ≤
          Real.exp (18/125-V/15625) := by
        apply Real.exp_le_exp.mpr
        change -(2/25)*(weightedCount (countNext N (competitionBase j))-V/5000) ≤ _
        linarith
      have hf : competitionReturnPotential V (competitionNext N j)-competitionReturnPotential V N ≤
          Real.exp (18/125-V/15625) := by
        have hp : 0 ≤ competitionReturnPotential V N := (Real.exp_pos _).le
        linarith
      exact mul_le_mul_of_nonneg_left hf (competitionRate_nonneg N V eps k r delta hV heps hk hr hd j)
  exact hm.trans (mul_le_mul_of_nonneg_right htotal (Real.exp_pos _).le)

theorem competition_return_foster (N : Counts) (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (h : resourceGood N V) :
    competitionGenerator N V eps k r delta (competitionReturnPotential V) ≤ competitionReturnSource V := by
  by_cases hY : weightedCount N ≤ (V:ℝ)/1000
  · exact (competition_return_low N V eps k r delta hV heps heps1 hk hk1 hr hr1 hd hd1 h hY).trans
      (by unfold competitionReturnSource; positivity)
  · apply competition_return_high N V eps k r delta hV heps hk (by linarith) hd (by linarith)
    apply competition_total_rate_bound N V eps k r delta hV heps (by linarith) hk hk1
      (by linarith) hr1 hd hd1
    intro i
    have hi := resource_count_cap N V h i
    linarith

end
end RandomViability.Binding
