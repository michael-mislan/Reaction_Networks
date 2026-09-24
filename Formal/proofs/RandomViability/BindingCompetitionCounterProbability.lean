import proofs.RandomViability.BindingCompetitionCounterTilt

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

section Model
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (C : ℕ) (M : FiniteJumpModel α β) (mark : β → Option (Fin 4))

omit [Fintype α] [DecidableEq α] in
theorem competition_counter_indicator_bound (mode : Fin 3) (theta limit : ℝ) (htheta : 0 ≤ theta)
    (X : α × CompetitionGrossCounters C) :
    FiniteKernel.eventIndicator {Z : α × CompetitionGrossCounters C | limit<(competitionServiceCount mode Z.2:ℝ)} X ≤
      Real.exp (-theta*limit)*competitionCounterPotential C mode theta X := by
  by_cases hh : limit<(competitionServiceCount mode X.2:ℝ)
  · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_pos hh,competitionCounterPotential]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith
  · simp only [FiniteKernel.eventIndicator,Set.mem_setOf_eq,if_neg hh,competitionCounterPotential]
    positivity

theorem competition_counter_probability (mode : Fin 3) (theta rateBound limit : ℝ)
    (htheta : 0 ≤ theta) (hr : 0 ≤ rateBound)
    (hrate : ∀ x, (∑ j,M.rate x j*(competitionServiceIncrement mode (mark j):ℝ)) ≤ rateBound)
    (q t : ℝ≥0) (hq : 0 < (q:ℝ)) (hb : ∀ X, M.total X ≤ q)
    (X : α × CompetitionGrossCounters C) :
    ((competitionCountedModel C M mark).uniformize q hq (fun Z => hb Z.1)).poissonized (q*t)
      (FiniteKernel.eventIndicator {Z | limit<(competitionServiceCount mode Z.2:ℝ)}) X ≤
      Real.exp (-theta*limit+rateBound*(Real.exp theta-1)*(t:ℝ))*competitionCounterPotential C mode theta X := by
  let P := (competitionCountedModel C M mark).uniformize q hq (fun Z => hb Z.1)
  have hm := P.poissonized_mono (q*t) _
    (fun Z => Real.exp (-theta*limit)*competitionCounterPotential C mode theta Z)
    (fun Z => (FiniteKernel.eventIndicator_bounds _ Z).1) (fun Z => by unfold competitionCounterPotential; positivity)
    (competition_counter_indicator_bound C mode theta limit htheta) X
  rw [P.poissonized_scale] at hm
  have ht := competition_counter_exponential_time C M mark mode theta rateBound htheta hr hrate q t hq hb X
  have hh := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-theta*limit)).le
  apply hm.trans (hh.trans_eq ?_)
  rw [Real.exp_add]
  ring

end Model
end
end RandomViability.Binding
