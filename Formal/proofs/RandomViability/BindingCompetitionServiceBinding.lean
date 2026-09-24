import proofs.RandomViability.BindingCompetitionCounterTilt
import proofs.RandomViability.BindingCompetitionWindowModel

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def competitionServiceRateBound (V : ℕ) (mode : Fin 3) : ℝ :=
  if mode=2 then (3/50)*(V:ℝ) else V

theorem competitionServiceRateBound_nonneg (V : ℕ) (mode : Fin 3) :
    0 ≤ competitionServiceRateBound V mode := by unfold competitionServiceRateBound; split_ifs <;> positivity

theorem competition_service_mark_identity (mode : Fin 3) (j : CompetitionChannel) :
    competitionServiceIncrement mode (competitionServiceLabel j)=
      if mode=0 then competitionFoodMark 0 j else if mode=1 then competitionFoodMark 1 j
      else competitionGrossServiceMark j := by
  cases j with
  | inl j => fin_cases mode <;> fin_cases j <;>
      norm_num [competitionServiceIncrement,competitionServiceLabel,competitionFoodMark,competitionGrossServiceMark,Fin.ext_iff]
  | inr j => fin_cases mode <;> fin_cases j <;>
      norm_num [competitionServiceIncrement,competitionServiceLabel,competitionFoodMark,competitionGrossServiceMark,Fin.ext_iff]

theorem competition_source_service_bound (N : Counts) (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1/20) (hg : resourceGood N V) (mode : Fin 3) :
    (∑ j,competitionRate N V eps k r delta j*(competitionServiceIncrement mode (competitionServiceLabel j):ℝ)) ≤
      competitionServiceRateBound V mode := by
  simp_rw [competition_service_mark_identity]
  fin_cases mode
  · simpa [competitionServiceRateBound] using (competition_food_intensity N V eps k r delta 0).le
  · simpa [competitionServiceRateBound] using (competition_food_intensity N V eps k r delta 1).le
  · norm_num [competitionServiceRateBound,Fin.ext_iff]
    simpa only [competitionRate,competitionGrossServiceMark,Nat.cast_one,mul_one,Fin.sum_univ_two] using
      competition_gross_service_rate N V eps delta hV heps heps1 hd hd1 hg

theorem competition_model_service_bound (V : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1/20) (mode : Fin 3) (X : CompetitionCounts V) :
    (∑ j,(competitionModel V eps k r delta hV heps hk hr hd).rate X j*
      (competitionServiceIncrement mode (competitionServiceLabel j):ℝ)) ≤ competitionServiceRateBound V mode := by
  by_cases hen : competitionEnabled X
  · simp only [competitionModel,if_pos hen]
    exact competition_source_service_bound _ V eps k r delta hV heps heps1 hd hd1 hen.2 mode
  · simpa [competitionModel,hen] using competitionServiceRateBound_nonneg V mode

theorem competition_window_service_bound (V C : ℕ) (eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1/20) (mode : Fin 3) (X : CompetitionWindowState V C) :
    (∑ j,(competitionWindowModel V C eps k r delta hV heps hk hr hd).rate X j*
      (competitionServiceIncrement mode (competitionServiceLabel j):ℝ)) ≤ competitionServiceRateBound V mode := by
  by_cases hp : competitionPhase X.1=0
  · simpa [competitionWindowModel,hp] using competitionServiceRateBound_nonneg V mode
  · simpa only [competitionWindowModel,if_neg hp] using
      competition_model_service_bound V eps k r delta hV heps heps1 hk hr hd hd1 mode X.1

end
end RandomViability.Binding
