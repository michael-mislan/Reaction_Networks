import proofs.RandomViability.BindingCompetitionSupplyRates
import proofs.RandomViability.BindingBookkeeping
import proofs.RandomViability.BindingCompetitionWindowModel

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def competitionMassWashoutMark : CompetitionChannel → ℕ
  | .inl j => ![0,0,0,0,0,0,0,0,0,0,0,0,2,2,4,6,8,8] j
  | .inr _ => 0

theorem competition_mass_mark_identity (j : CompetitionChannel) :
    massJump (competitionBase j)+(competitionMassWashoutMark j:ℝ)=
      2*(competitionFoodMark 0 j:ℝ)+2*(competitionFoodMark 1 j:ℝ) := by
  cases j with
  | inl j => fin_cases j <;> norm_num [competitionBase,massJump,competitionMassWashoutMark,competitionFoodMark]
  | inr j => fin_cases j <;> norm_num [competitionBase,drivenBase,massJump,competitionMassWashoutMark,competitionFoodMark]

theorem competition_count_mass_eq (N : Counts) : countMass N=competitionResidentMass N := by
  simp [countMass,massSpecies,competitionResidentMass,Fin.sum_univ_succ]
  ring

theorem competition_count_mass_nonneg (N : Counts) : 0 ≤ countMass N := by
  rw [competition_count_mass_eq]
  unfold competitionResidentMass
  positivity

theorem competition_mass_step (N : Counts) (j : CompetitionChannel)
    (hs : ∀ i,reactants (competitionBase j) i ≤ N i) :
    countMass (competitionNext N j)+(competitionMassWashoutMark j:ℝ)=
      countMass N+2*(competitionFoodMark 0 j:ℝ)+2*(competitionFoodMark 1 j:ℝ) := by
  have hh := next_linear_difference N (competitionBase j) massSpecies hs
  rw [mass_stoich] at hh
  change countMass (competitionNext N j)-countMass N=massJump (competitionBase j) at hh
  have hm := competition_mass_mark_identity j
  linarith

def competitionFeasibleTrace : Counts → List CompetitionChannel → Prop
  | _,[] => True
  | N,j::js => (∀ i,reactants (competitionBase j) i ≤ N i) ∧ competitionFeasibleTrace (competitionNext N j) js

theorem competition_mass_history (N : Counts) (js : List CompetitionChannel) (hs : competitionFeasibleTrace N js) :
    countMass (js.foldl competitionNext N)+((js.map competitionMassWashoutMark).sum:ℝ)=
      countMass N+2*((js.map (competitionFoodMark 0)).sum:ℝ)+2*((js.map (competitionFoodMark 1)).sum:ℝ) := by
  induction js generalizing N with
  | nil => simp
  | cons j js ih =>
    have hh := ih (competitionNext N j) hs.2
    have hm := competition_mass_step N j hs.1
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,Nat.cast_add]
    linarith

theorem competition_initial_mass (V : ℕ) : countMass (boxCounts (foodInitial V))=4*(V:ℝ) := by
  simp [countMass,massSpecies,foodInitial,boxCounts,Fin.sum_univ_succ]
  ring

/-- Food and total washout throughput scale with the full physical horizon. -/
theorem competition_food_throughput (V : ℕ) (T : ℝ) (js : List CompetitionChannel)
    (hs : competitionFeasibleTrace (boxCounts (foodInitial V)) js)
    (hu : ((js.map (competitionFoodMark 0)).sum:ℝ) ≤ 2*(V:ℝ)*T)
    (hw : ((js.map (competitionFoodMark 1)).sum:ℝ) ≤ 2*(V:ℝ)*T) :
    2*((js.map (competitionFoodMark 0)).sum:ℝ)+2*((js.map (competitionFoodMark 1)).sum:ℝ) ≤ 8*(V:ℝ)*T ∧
    ((js.map competitionMassWashoutMark).sum:ℝ) ≤ 4*(V:ℝ)+8*(V:ℝ)*T := by
  have hh := competition_mass_history (boxCounts (foodInitial V)) js hs
  rw [competition_initial_mass] at hh
  have hn := competition_count_mass_nonneg (js.foldl competitionNext (boxCounts (foodInitial V)))
  constructor <;> linarith

theorem competition_export_le_washout (j : CompetitionChannel) : competitionExportUnits j ≤ competitionMassWashoutMark j := by
  cases j with
  | inl j => fin_cases j <;> norm_num [competitionExportUnits,exportUnits,competitionMassWashoutMark]
  | inr j => simp [competitionExportUnits,competitionMassWashoutMark]

theorem competition_export_history_le_washout (js : List CompetitionChannel) :
    (js.map competitionExportUnits).sum ≤ (js.map competitionMassWashoutMark).sum := by
  induction js with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (competition_export_le_washout j) ih

theorem competition_window_total_export (V : ℕ) (exports : List ℕ)
    (h : ∀ x ∈ exports, (V:ℝ)/5000 ≤ (x:ℝ)) :
    (V:ℝ)*(exports.length:ℝ)/5000 ≤ (exports.sum:ℝ) := by
  induction exports with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    linarith

end
end RandomViability.Binding
