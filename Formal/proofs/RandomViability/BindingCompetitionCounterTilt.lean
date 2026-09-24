import proofs.RandomViability.BindingCompetitionGrossCounters

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

theorem competition_counter_exp_increment {C : ℕ} (mode : Fin 3) (theta : ℝ)
    (htheta : 0 ≤ theta) (c : CompetitionGrossCounters C) (label : Option (Fin 4)) :
    Real.exp (theta*(competitionServiceCount mode (competitionCounterNext c label):ℝ))-
      Real.exp (theta*(competitionServiceCount mode c:ℝ)) ≤
      Real.exp (theta*(competitionServiceCount mode c:ℝ))*(Real.exp theta-1)*
        (competitionServiceIncrement mode label:ℝ) := by
  have hc : (competitionServiceCount mode (competitionCounterNext c label):ℝ) ≤
      (competitionServiceCount mode c:ℝ)+(competitionServiceIncrement mode label:ℝ) := by
    exact_mod_cast competition_counter_increment_bound mode c label
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc htheta)
  rw [mul_add,Real.exp_add] at he
  rcases competition_service_increment_binary mode label with hi | hi
  · simp only [hi,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at he ⊢
    linarith
  · simp only [hi,Nat.cast_one,mul_one] at he ⊢
    nlinarith

section Model
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (C : ℕ) (M : FiniteJumpModel α β) (mark : β → Option (Fin 4))

def competitionCounterPotential (mode : Fin 3) (theta : ℝ) (X : α × CompetitionGrossCounters C) : ℝ :=
  Real.exp (theta*(competitionServiceCount mode X.2:ℝ))

omit [DecidableEq α] in
theorem competition_counter_tilt (mode : Fin 3) (theta rateBound : ℝ) (htheta : 0 ≤ theta)
    (hrate : ∀ x, (∑ j,M.rate x j*(competitionServiceIncrement mode (mark j):ℝ)) ≤ rateBound)
    (X : α × CompetitionGrossCounters C) :
    (competitionCountedModel C M mark).generator (competitionCounterPotential C mode theta) X ≤
      rateBound*(Real.exp theta-1)*competitionCounterPotential C mode theta X := by
  have hpos : 0 ≤ Real.exp theta-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr htheta)
  have hs : (competitionCountedModel C M mark).generator (competitionCounterPotential C mode theta) X ≤
      ∑ j,M.rate X.1 j*(competitionCounterPotential C mode theta X*(Real.exp theta-1)*
        (competitionServiceIncrement mode (mark j):ℝ)) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (competition_counter_exp_increment mode theta htheta X.2 (mark j)) (M.nonneg X.1 j)
  have he : (∑ j,M.rate X.1 j*(competitionCounterPotential C mode theta X*(Real.exp theta-1)*
        (competitionServiceIncrement mode (mark j):ℝ))) =
      (∑ j,M.rate X.1 j*(competitionServiceIncrement mode (mark j):ℝ))*
        (Real.exp theta-1)*competitionCounterPotential C mode theta X := by
    rw [Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hs
  exact hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hrate X.1) hpos) (Real.exp_pos _).le)

theorem competition_counter_exponential_time (mode : Fin 3) (theta rateBound : ℝ)
    (htheta : 0 ≤ theta) (hr : 0 ≤ rateBound)
    (hrate : ∀ x, (∑ j,M.rate x j*(competitionServiceIncrement mode (mark j):ℝ)) ≤ rateBound)
    (q t : ℝ≥0) (hq : 0 < (q:ℝ)) (hb : ∀ X, M.total X ≤ q)
    (X : α × CompetitionGrossCounters C) :
    ((competitionCountedModel C M mark).uniformize q hq (fun Z => hb Z.1)).poissonized (q*t)
      (competitionCounterPotential C mode theta) X ≤
      Real.exp (rateBound*(Real.exp theta-1)*(t:ℝ))*competitionCounterPotential C mode theta X := by
  have hg (Z : α × CompetitionGrossCounters C) := competition_counter_tilt C M mark mode theta rateBound htheta hrate Z
  have hpos : 0 ≤ Real.exp theta-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr htheta)
  have hkq : -(rateBound*(Real.exp theta-1)) ≤ (q:ℝ) := by nlinarith [q.property]
  have hh := (competitionCountedModel C M mark).uniformized_decay_bound q t hq (fun Z => hb Z.1)
    (competitionCounterPotential C mode theta) (fun Z => (Real.exp_pos _).le)
    (-(rateBound*(Real.exp theta-1))) hkq (by intro Z; simpa only [neg_neg,mul_assoc] using hg Z) X
  simpa only [neg_neg] using hh

end Model
end
end RandomViability.Binding
