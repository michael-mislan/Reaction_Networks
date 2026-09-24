import proofs.RandomViability.BindingCompetitionDrift
import proofs.RandomViability.BindingCountExponential

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

theorem competition_actual_variance (N : Counts) (V eps k r delta : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (hu : (N 0:ℝ)/V ≤ 11/10) (hw : (N 1:ℝ)/V ≤ 11/10)
    (huw : ((N 0:ℝ)/V)*((N 1:ℝ)/V) ≤ 121/100)
    (hx : (N 2:ℝ)/V ≤ 1/1000) :
    competitionVariance N V eps k r delta ≤ 5*weightedCount N+(25/16)*eps*V := by
  have he := competition_variance_envelope ((N 0:ℝ)/V) ((N 1:ℝ)/V)
    ((N 2:ℝ)/V) ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V) eps k r delta
    hu hw huw (by positivity) hx (by positivity) (by positivity) (by positivity)
    heps heps1 hk hk1 hr hr1 hd hd1
  have hf := factorial_le_square (N 2)
  have hid : competitionVariance N V eps k r delta =
      (varianceEnvelope ((N 0:ℝ)/V) ((N 1:ℝ)/V) ((N 2:ℝ)/V)
        ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V) eps k r +
        delta*((N 2:ℝ)/V)+delta*eps/16*((N 0:ℝ)/V)*((N 1:ℝ)/V))*V -
      (r/V)*((N 2:ℝ)^2-(N 2*(N 2-1):ℕ))/25 := by
    rw [competition_variance_expansion, countVariance_expansion]
    dsimp [varianceEnvelope]
    field_simp
    ring
  have hm := mul_le_mul_of_nonneg_right he hV.le
  have hl : (5*weighted ((N 2:ℝ)/V) ((N 3:ℝ)/V) ((N 4:ℝ)/V)
      ((N 5:ℝ)/V)+(25/16)*eps)*V = 5*weightedCount N+(25/16)*eps*V := by
    dsimp [weighted,weightedCount]
    field_simp
  rw [hl] at hm
  rw [hid]
  exact (sub_le_self _ (div_nonneg
    (mul_nonneg (div_nonneg hr hV.le) (sub_nonneg.mpr hf)) (by norm_num))).trans hm

theorem competition_corridor_exponential (N : Counts) (V : ℕ) (eps k r delta s : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (h : resourceGood N V) (hY : weightedCount N ≤ (V:ℝ)/1000)
    (hs : 0 ≤ s) (hs1 : s ≤ 2/25) :
    (∑ j,competitionRate N V eps k r delta j *
      (Real.exp (-s*weightedJump (competitionBase j))-1)) ≤
      -(3/10*s-3*s^2)*weightedCount N-(14/25)*eps*V*s := by
  have hf := low_count_food_corridor N V hV h.1 h.2.2.1 hY
  have hx : (N 2:ℝ)/(V:ℝ) ≤ 1/1000 := by
    apply (div_le_iff₀ hV).mpr
    have hh := (freeCount_le_weighted N).trans hY
    linarith
  have hc (i : Fin 6) : (N i:ℝ)/(V:ℝ) ≤ 11/10 :=
    (div_le_iff₀ hV).mpr (resource_count_cap N V h i)
  have huw : ((N 0:ℝ)/(V:ℝ))*((N 1:ℝ)/(V:ℝ)) ≤ 121/100 := by
    have hh := mul_le_mul (hc 0) (hc 1) (by positivity : 0 ≤ (N 1:ℝ)/(V:ℝ))
      (by norm_num : (0:ℝ) ≤ 11/10)
    norm_num at hh
    exact hh
  have hg := competition_actual_growth N V eps k r delta hV heps heps1 hk hk1
    hr hr1 hd hd1 ((le_div_iff₀ hV).mpr hf.1) ((le_div_iff₀ hV).mpr hf.2) hx
  have hq := competition_actual_variance N V eps k r delta hV heps heps1 hk hk1
    (by linarith) hr1 hd hd1 (hc 0) (hc 1) huw hx
  have hj (j : CompetitionChannel) :
      competitionRate N V eps k r delta j *
        (weightedCount (competitionNext N j)-weightedCount N) =
      competitionRate N V eps k r delta j * weightedJump (competitionBase j) := by
    simp only [weighted_count_sum, competition_rated_linear_jump, weighted_stoich]
  simp only [competitionGenerator,hj] at hg
  simpa only [mul_assoc] using entry_exponential_strong
    (competitionRate N V eps k r delta) (fun j => weightedJump (competitionBase j))
    (weightedCount N) (eps*V) s
    (competitionRate_nonneg N V eps k r delta hV heps hk (by linarith) hd)
    competition_jump_bound (weightedCount_nonneg N) (by positivity) hs hs1
    (by simpa only [mul_assoc] using hg) (by simpa only [mul_assoc] using hq)

end
end RandomViability.Binding
