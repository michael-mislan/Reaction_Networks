import proofs.RandomViability.BindingCompetitionSource

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

theorem competition_growth_expansion (N : Counts) (V eps k r delta : ℝ) :
    competitionGenerator N V eps k r delta weightedCount =
      countGrowth N V eps k r - delta*(N 2) + delta*eps/16*(N 0)*(N 1)/V := by
  have hj (j : CompetitionChannel) :
      competitionRate N V eps k r delta j *
        (weightedCount (competitionNext N j)-weightedCount N) =
      competitionRate N V eps k r delta j * weightedJump (competitionBase j) := by
    simp only [weighted_count_sum, competition_rated_linear_jump, weighted_stoich]
  have ho : countGrowth N V eps k r = ∑ j, countRate N V eps k r j*weightedJump j := by
    simp only [countGrowth, rated_weighted_jump]
  simp only [competitionGenerator, hj]
  simp only [Fintype.sum_sum_type, competitionRate, competitionBase]
  rw [← ho]
  simp [Fin.sum_univ_succ, drivenBase, drivenRate_zero, drivenRate_one, weightedJump]
  ring

def competitionVariance (N : Counts) (V eps k r delta : ℝ) : ℝ :=
  ∑ j, competitionRate N V eps k r delta j *
    (weightedJump (competitionBase j))^2

theorem competition_variance_expansion (N : Counts) (V eps k r delta : ℝ) :
    competitionVariance N V eps k r delta =
      countVariance N V eps k r + delta*(N 2) + delta*eps/16*(N 0)*(N 1)/V := by
  simp only [competitionVariance, Fintype.sum_sum_type, competitionRate,
    competitionBase]
  change countVariance N V eps k r + _ = _
  simp [Fin.sum_univ_succ, drivenBase, drivenRate_zero, drivenRate_one, weightedJump]
  ring

theorem competition_jump_bound (j : CompetitionChannel) :
    |weightedJump (competitionBase j)| ≤ (9/5:ℝ) :=
  weightedJump_bound _

/-- Phase-specific estimate: the new loss is paid only by free X. -/
theorem competition_corridor_growth (u w x c₁ c₂ z eps k r delta : ℝ)
    (hu : 4/5 ≤ u) (hw : 4/5 ≤ w)
    (hx : 0 ≤ x) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hz : 0 ≤ z)
    (heps : 0 ≤ eps) (hepsSmall : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hsmall : x ≤ 1/1000) :
    (39/100)*weighted x c₁ c₂ z+(16/25)*eps ≤
    (eps+delta*eps/16)*u*w-(eps*k+delta)*x+(5/2*u-1)*x+
      (-29/8+11/2*w)*c₁+11/10*c₂+(r/5-9/5-8*k)*z-r/5*x*x := by
  have hp : (16/25:ℝ) ≤ u*w := by
    have h := mul_le_mul hu hw (by norm_num : (0:ℝ) ≤ 4/5) (by linarith : 0 ≤ u)
    norm_num at h
    exact h
  have hb := mul_le_mul_of_nonneg_left hp heps
  have hxu := mul_le_mul_of_nonneg_right hu hx
  have hcw := mul_le_mul_of_nonneg_right hw hc₁
  have hzr := mul_le_mul_of_nonneg_right hr hz
  have hzk := mul_le_mul_of_nonneg_right hk1 hz
  have he : eps*k ≤ 1/8000000 :=
    (mul_le_mul hepsSmall hk1 hk (by norm_num)).trans (by norm_num)
  have hex := mul_le_mul_of_nonneg_right he hx
  have hrx : r*x ≤ 22/1000 :=
    (mul_le_mul hr1 hsmall hx (by norm_num)).trans (by norm_num)
  have hrxx := mul_le_mul_of_nonneg_right hrx hx
  have hdx := mul_le_mul_of_nonneg_right hd1 hx
  have hrev : 0 ≤ delta*eps/16*u*w := by
    have hu0 : 0 ≤ u := by linarith
    have hw0 : 0 ≤ w := by linarith
    positivity
  dsimp [weighted]
  nlinarith

theorem competition_variance_envelope (u w x c₁ c₂ z eps k r delta : ℝ)
    (hu : u ≤ 11/10) (hw : w ≤ 11/10) (huw : u*w ≤ 121/100)
    (hx : 0 ≤ x) (hxx : x ≤ 1/1000)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hz : 0 ≤ z)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (_hr : 0 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) :
    varianceEnvelope u w x c₁ c₂ z eps k r + delta*x + delta*eps/16*u*w ≤
      5*weighted x c₁ c₂ z+(25/16)*eps := by
  have b₀ := mul_le_mul_of_nonneg_left huw heps
  have b₁ : eps*k*x ≤ (1/8000000)*x := by
    have he : eps*k ≤ 1/8000000 :=
      (mul_le_mul heps1 hk1 hk (by norm_num)).trans (by norm_num)
    exact mul_le_mul_of_nonneg_right he hx
  have b₂ := mul_le_mul_of_nonneg_left hu hx
  have b₃ := mul_le_mul_of_nonneg_left hw hc₁
  have b₄ := mul_le_mul_of_nonneg_right hk1 hz
  have b₅ := mul_le_mul_of_nonneg_right hr1 hz
  have b₆ : r*x*x ≤ (22/1000)*x := by
    have hb : r*x ≤ 22/1000 := (mul_le_mul hr1 hxx hx (by norm_num)).trans (by norm_num)
    exact mul_le_mul_of_nonneg_right hb hx
  have b₇ := mul_le_mul_of_nonneg_right hd1 hx
  have b₈ := mul_le_mul_of_nonneg_left huw (mul_nonneg hd heps)
  have b₉ := mul_le_mul_of_nonneg_right hd1 heps
  dsimp [varianceEnvelope,weighted]
  nlinarith

theorem competition_actual_growth (N : Counts) (V eps k r delta : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hepsSmall : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (hu : 4/5 ≤ (N 0:ℝ)/V) (hw : 4/5 ≤ (N 1:ℝ)/V)
    (hx : (N 2:ℝ)/V ≤ 1/1000) :
    (39/100)*weightedCount N+(16/25)*eps*V ≤
      competitionGenerator N V eps k r delta weightedCount := by
  have he := competition_corridor_growth ((N 0:ℝ)/V) ((N 1:ℝ)/V)
    ((N 2:ℝ)/V) ((N 3:ℝ)/V) ((N 4:ℝ)/V) ((N 5:ℝ)/V) eps k r delta
    hu hw (by positivity) (by positivity) (by positivity) (by positivity)
    heps hepsSmall hk hk1 hr hr1 hd hd1 hx
  have hm := mul_le_mul_of_nonneg_right he hV.le
  have hid : competitionGenerator N V eps k r delta weightedCount =
    ((eps+delta*eps/16)*((N 0:ℝ)/V)*((N 1:ℝ)/V)-
      (eps*k+delta)*((N 2:ℝ)/V)+(5/2*((N 0:ℝ)/V)-1)*((N 2:ℝ)/V)+
      (-29/8+11/2*((N 1:ℝ)/V))*((N 3:ℝ)/V)+11/10*((N 4:ℝ)/V)+
      (r/5-9/5-8*k)*((N 5:ℝ)/V)-r/5*((N 2:ℝ)/V)*((N 2:ℝ)/V))*V+
      r/(5*V)*(N 2) := by
    rw [competition_growth_expansion, countGrowth_expansion]
    field_simp
    ring
  have hl : ((39/100)*weighted ((N 2:ℝ)/V) ((N 3:ℝ)/V)
      ((N 4:ℝ)/V) ((N 5:ℝ)/V)+(16/25)*eps)*V =
      (39/100)*weightedCount N+(16/25)*eps*V := by
    dsimp [weighted,weightedCount]
    field_simp
  rw [hl] at hm
  rw [hid]
  have hr0 : 0 ≤ r := by linarith
  exact hm.trans (le_add_of_nonneg_right (by positivity))

end
end RandomViability.Binding
