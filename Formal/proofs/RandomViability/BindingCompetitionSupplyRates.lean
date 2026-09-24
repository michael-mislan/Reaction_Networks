import proofs.RandomViability.BindingCompetitionBookkeeping
import proofs.RandomViability.BindingStoppedModel

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

/-- The gross service rate counts both driven directions, not their net flux. -/
theorem competition_gross_service_rate (N : Counts) (V : ℕ) (eps delta : ℝ)
    (hV : 0 < (V:ℝ)) (_heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1/20) (hg : resourceGood N V) :
    (∑ j : Fin 2, drivenRate N V eps delta j) ≤ (3/50)*(V:ℝ) := by
  have hu := resource_count_cap N V hg 0
  have hw := resource_count_cap N V hg 1
  have hx := resource_count_cap N V hg 2
  have hn (i : Fin 6) : 0 ≤ (N i:ℝ) := Nat.cast_nonneg _
  have hde : delta*eps ≤ 1/20 :=
    (mul_le_mul_of_nonneg_left heps1 hd).trans (by simpa using hd1)
  have hdx : delta*(N 2:ℝ) ≤ (11/200)*(V:ℝ) := by
    calc
      _ ≤ (1/20)*((11/10)*(V:ℝ)) := mul_le_mul hd1 hx (hn 2) (by norm_num)
      _ = _ := by ring
  have huw : (N 0:ℝ)*(N 1:ℝ) ≤ (121/100)*(V:ℝ)^2 := by
    have hh := mul_le_mul hu hw (hn 1) (by positivity : 0 ≤ (11/10)*(V:ℝ))
    nlinarith
  have hrev : delta*eps/16*(N 0:ℝ)*(N 1:ℝ)/(V:ℝ) ≤ (121/32000)*(V:ℝ) := by
    apply (div_le_iff₀ hV).mpr
    have hh := mul_le_mul (div_le_div_of_nonneg_right hde (by norm_num : (0:ℝ)≤16)) huw
      (mul_nonneg (hn 0) (hn 1)) (by norm_num : (0:ℝ)≤(1/20)/16)
    nlinarith
  simp only [Fin.sum_univ_two,drivenRate_zero,drivenRate_one]
  linarith

def competitionFoodMark (side : Fin 2) : CompetitionChannel → ℕ
  | .inl j => if j.val=10+side.val then 1 else 0
  | .inr _ => 0

def competitionGrossServiceMark : CompetitionChannel → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem competition_food_intensity (N : Counts) (V eps k r delta : ℝ) (side : Fin 2) :
    (∑ j,competitionRate N V eps k r delta j*(competitionFoodMark side j:ℝ))=V := by
  fin_cases side <;>
    norm_num [Fintype.sum_sum_type,competitionRate,competitionFoodMark,countRate,Fin.sum_univ_succ]

theorem competition_service_intensity (N : Counts) (V eps k r delta : ℝ) :
    (∑ j,competitionRate N V eps k r delta j*(competitionGrossServiceMark j:ℝ))=
      ∑ j : Fin 2,drivenRate N V eps delta j := by
  simp [Fintype.sum_sum_type,competitionRate,competitionGrossServiceMark]

def competitionResidentMass (N : Counts) : ℝ :=
  2*(N 0)+2*(N 1)+4*(N 2)+6*(N 3)+8*(N 4)+8*(N 5)

theorem competition_mass_identity (N : Counts) :
    competitionResidentMass N=2*(uCount N+wCount N) := by
  rw [uCount_expansion,wCount_expansion]
  unfold competitionResidentMass
  ring

theorem competition_resident_mass_bound (N : Counts) (V : ℕ) (hg : resourceGood N V) :
    competitionResidentMass N ≤ (22/5)*(V:ℝ) := by
  rw [competition_mass_identity]
  have ha := hg.2.1
  have hb := hg.2.2.2
  linarith

end
end RandomViability.Binding
