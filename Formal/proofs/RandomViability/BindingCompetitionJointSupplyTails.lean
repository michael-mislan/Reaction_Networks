import proofs.RandomViability.BindingCompetitionJointCounterBounds
import proofs.RandomViability.BindingCompetitionCounterProbability
import Mathlib.Analysis.Complex.ExponentialBounds

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

def competitionJointInitial (V C : ℕ) (hV : 0 < (V:ℝ)) : CompetitionCounts V × CompetitionGrossCounters C :=
  (competitionFoodInitial V hV,fun _ => 0)

def competitionJointServiceFailure {V C : ℕ} (mode : Fin 3) (limit : ℝ) (X : CompetitionJointState V C) : ℝ :=
  FiniteKernel.eventIndicator {Z | limit<(competitionServiceCount mode Z.1.2:ℝ)} X

theorem competition_joint_service_probability (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (mode : Fin 3) (theta limit : ℝ) (htheta : 0 ≤ theta) (s : ℝ≥0) (m : ℕ) :
    competitionJointLaw (competitionJointStartupKernel V C p hV) (competitionJointWindowKernel V C p hV)
      (competitionClock V) s m (competitionJointServiceFailure mode limit) (competitionJointInitial V C hV) ≤
      Real.exp (-theta*limit+competitionServiceRateBound V mode*(Real.exp theta-1)*(500+(m:ℝ)+(s:ℝ))) := by
  let S := competitionJointStartupKernel V C p hV
  let Q := competitionJointWindowKernel V C p hV
  let q : ℝ≥0 := competitionClock V
  let X := competitionJointInitial V C hV
  have hi (Z : CompetitionJointState V C) : competitionJointServiceFailure mode limit Z ≤
      Real.exp (-theta*limit)*competitionJointCounterPotential mode theta Z :=
    competition_counter_indicator_bound C mode theta limit htheta Z.1
  have hn (Z : CompetitionJointState V C) : 0 ≤ competitionJointServiceFailure mode limit Z :=
    (FiniteKernel.eventIndicator_bounds _ Z).1
  have hm := competition_joint_law_mono Q S q s m _ _ hn
    (fun Z => by unfold competitionJointCounterPotential; positivity) hi X
  rw [competition_joint_law_scale] at hm
  have hg := competition_joint_counter_growth V C p hV mode theta htheta s m X
  have hz : Real.exp (theta*(competitionServiceCount mode X.2:ℝ))=1 := by
    simp [X,competitionJointInitial,competitionServiceCount]
  rw [hz,mul_one] at hg
  have hh := mul_le_mul_of_nonneg_left hg (Real.exp_pos (-theta*limit)).le
  exact hm.trans (hh.trans_eq (Real.exp_add _ _).symm)

theorem competition_joint_food_tail (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (mode : Fin 3) (hmode : mode≠2) (s : ℝ≥0) (m : ℕ) :
    competitionJointLaw (competitionJointStartupKernel V C p hV) (competitionJointWindowKernel V C p hV)
      (competitionClock V) s m
      (competitionJointServiceFailure mode (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ)))) (competitionJointInitial V C hV) ≤
      Real.exp (-(2*Real.log 2-1)*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) := by
  have hh := competition_joint_service_probability V C p hV mode (Real.log 2)
    (2*(V:ℝ)*(500+(m:ℝ)+(s:ℝ))) (Real.log_nonneg (by norm_num)) s m
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  simp only [competitionServiceRateBound,if_neg hmode] at hh
  convert hh using 1
  congr 1
  ring

theorem competition_joint_fuel_tail (V C : ℕ) (p : CompetitionRateBox) (hV : 0 < (V:ℝ))
    (s : ℝ≥0) (m : ℕ) :
    competitionJointLaw (competitionJointStartupKernel V C p hV) (competitionJointWindowKernel V C p hV)
      (competitionClock V) s m
      (competitionJointServiceFailure 2 ((V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8)) (competitionJointInitial V C hV) ≤
      Real.exp (-(V:ℝ)*(500+(m:ℝ)+(s:ℝ))/200) := by
  have hh := competition_joint_service_probability V C p hV 2 1
    ((V:ℝ)*(500+(m:ℝ)+(s:ℝ))/8) (by norm_num) s m
  apply hh.trans (Real.exp_le_exp.mpr ?_)
  norm_num [competitionServiceRateBound,Fin.ext_iff]
  have ht : 0 ≤ (V:ℝ)*(500+(m:ℝ)+(s:ℝ)) := by positivity
  have he := mul_nonneg (show 0 ≤ 3-Real.exp 1 by linarith [Real.exp_one_lt_three]) ht
  nlinarith

end
end RandomViability.Binding
