import proofs.RandomViability.BindingCountDrift
import proofs.RandomViability.BindingMoietyDrift

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

/-- Eighteen inherited labels and two distinct reservoir-service labels. -/
abbrev CompetitionChannel := Fin 18 ⊕ Fin 2

def drivenBase : Fin 2 → Fin 18 := ![1,0]

def drivenRate (N : Counts) (V eps delta : ℝ) (j : Fin 2) : ℝ :=
  countRate N V (if j = 0 then delta else delta*eps/16) 1 0 (drivenBase j)

def competitionRate (N : Counts) (V eps k r delta : ℝ) : CompetitionChannel → ℝ
  | .inl j => countRate N V eps k r j
  | .inr j => drivenRate N V eps delta j

def competitionBase : CompetitionChannel → Fin 18
  | .inl j => j
  | .inr j => drivenBase j

def competitionNext (N : Counts) (j : CompetitionChannel) : Counts :=
  countNext N (competitionBase j)

def competitionExport : CompetitionChannel → ℝ
  | .inl j => exportMark j
  | .inr _ => 0

/-- Separate gross counters, in the order F consumed and P consumed. -/
def reservoirMark (direction : Fin 2) : CompetitionChannel → ℕ
  | .inl _ => 0
  | .inr j => if j = direction then 1 else 0

def competitionGenerator (N : Counts) (V eps k r delta : ℝ) (f : Counts → ℝ) : ℝ :=
  ∑ j, competitionRate N V eps k r delta j * (f (competitionNext N j)-f N)

theorem drivenRate_zero (N : Counts) (V eps delta : ℝ) :
    drivenRate N V eps delta 0 = delta*(N 2) := by
  simp [drivenRate, drivenBase, countRate]

theorem drivenRate_one (N : Counts) (V eps delta : ℝ) :
    drivenRate N V eps delta 1 = delta*eps/16*(N 0)*(N 1)/V := by
  norm_num [drivenRate, drivenBase, countRate]

theorem competition_rate_support (N : Counts) (V eps k r delta : ℝ)
    (j : CompetitionChannel) (h : competitionRate N V eps k r delta j ≠ 0) :
    ∀ i, reactants (competitionBase j) i ≤ N i := by
  cases j with
  | inl j => exact rate_support N V eps k r j h
  | inr j => exact rate_support N V _ 1 0 (drivenBase j) h

theorem competitionRate_nonneg (N : Counts) (V eps k r delta : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hd : 0 ≤ delta) (j : CompetitionChannel) :
    0 ≤ competitionRate N V eps k r delta j := by
  cases j with
  | inl j => exact countRate_nonneg N V eps k r hV heps hk hr j
  | inr j =>
    apply countRate_nonneg N V _ 1 0 hV _ (by norm_num) (by norm_num)
    split_ifs <;> positivity

theorem competition_rated_linear_jump (N : Counts) (V eps k r delta : ℝ)
    (j : CompetitionChannel) (a : Fin 6 → ℝ) :
    competitionRate N V eps k r delta j *
      ((∑ i,a i*(competitionNext N j i:ℝ))-(∑ i,a i*(N i:ℝ))) =
    competitionRate N V eps k r delta j *
      (∑ i,a i*((products (competitionBase j) i:ℝ)-(reactants (competitionBase j) i:ℝ))) := by
  by_cases h : competitionRate N V eps k r delta j = 0
  · simp [h]
  · rw [competitionNext, next_linear_difference N _ a
      (competition_rate_support N V eps k r delta j h)]

theorem competition_u_drift (N : Counts) (V eps k r delta : ℝ) :
    competitionGenerator N V eps k r delta uCount = V-uCount N := by
  simp only [competitionGenerator, uCount, competition_rated_linear_jump, u_units_stoich]
  simp only [Fintype.sum_sum_type, competitionRate, competitionBase]
  have h := uCount_actual_drift N V eps k r
  simp only [uCount, rated_linear_jump, u_units_stoich] at h
  rw [h]
  simp [Fin.sum_univ_succ, drivenBase, uUnitJump]

theorem competition_w_drift (N : Counts) (V eps k r delta : ℝ) :
    competitionGenerator N V eps k r delta wCount = V-wCount N := by
  simp only [competitionGenerator, wCount, competition_rated_linear_jump, w_units_stoich]
  simp only [Fintype.sum_sum_type, competitionRate, competitionBase]
  have h := wCount_actual_drift N V eps k r
  simp only [wCount, rated_linear_jump, w_units_stoich] at h
  rw [h]
  simp [Fin.sum_univ_succ, drivenBase, wUnitJump]

end
end RandomViability.Binding
