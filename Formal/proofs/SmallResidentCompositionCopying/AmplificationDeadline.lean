import proofs.SmallResidentCompositionCopying.AmplificationSource

namespace SmallResidentCompositionCopying.Amplification
open FiniteCopy CompositionalMemory
noncomputable section

def partitionSuccess : ℝ := ((1048574:ℝ)/1048576)^2
def baseline : State → ℝ := fun s => s.elim 0 (fun _ => partitionSuccess)
def payoff : State → ℝ := fun s => s.elim 0 fun z =>
  if z.1.val=19 ∧ z.2.val=19 then partitionSuccess else 0

theorem partition_bounds : 0 ≤ partitionSuccess ∧ partitionSuccess ≤ 1 := by
  norm_num [partitionSuccess]

theorem baseline_generator (s : State) : model.generator baseline s = 0 := by
  cases s <;> simp [FiniteJumpModel.generator,model,baseline]

theorem cover (s : State) : baseline s ≤ payoff s + remaining s := by
  cases s with
  | none => norm_num [baseline,payoff,remaining]
  | some z =>
    have ha := z.1.isLt
    have hb := z.2.isLt
    by_cases h : z.1.val=19 ∧ z.2.val=19
    · norm_num [baseline,payoff,h,remaining]
    · have hn : z.1.val+z.2.val ≤ 37 := by omega
      have hr : (z.1.val:ℝ)+(z.2.val:ℝ) ≤ 37 := by exact_mod_cast hn
      simp only [baseline,Option.elim,payoff,if_neg h,remaining]
      linarith [partition_bounds.2]

theorem small_exponential : Real.exp (-1000:ℝ) ≤ 1/251001 := by
  have h := Real.add_one_le_exp (500:ℝ)
  have hn := Real.exp_pos (500:ℝ)
  have he : (251001:ℝ) ≤ Real.exp 1000 := by
    rw [show (1000:ℝ)=500+500 by norm_num,Real.exp_add]
    nlinarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he

def quota : ℕ := 1000000000
def cycleModel := killedBudgetModel model quota
def cyclePayoff := killedBudgetObservable quota payoff
def cycleStart (z : Counts) : Option (Counts × Fin quota) := some (z,⟨0,by norm_num [quota]⟩)

/-- This is the actual finite CTMC expectation of terminal complementary
return, with every quota-exhausted history assigned zero. -/
theorem deadline_bound (z : Counts) : (99:ℝ)/100 ≤
    finiteTimeExpectation cycleModel 20 cyclePayoff (cycleStart z) := by
  have h := killed_budget_deadline model quota (by norm_num [quota])
    payoff baseline remaining 0 0 50 120000 20
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rfl)
    (fun s => by cases s <;> simp [baseline,partition_bounds.2])
    (fun s => by cases s with
      | none => exact le_rfl
      | some a => exact (remaining_bounds a).1)
    rate_bound
    (fun s => by rw [baseline_generator]; norm_num)
    (fun s => by simpa using generator_remaining s)
    cover z
  have hw := remaining_bounds z
  have hex := mul_le_mul_of_nonneg_right small_exponential hw.1
  have hmax := mul_le_mul_of_nonneg_left hw.2 (show (0:ℝ) ≤ 1/251001 by norm_num)
  change _ ≤ finiteTimeExpectation (killedBudgetModel model quota) 20
    (killedBudgetObservable quota payoff) (some (z,⟨0,by norm_num [quota]⟩))
  norm_num [baseline,quota,partitionSuccess] at h
  linarith

end
end SmallResidentCompositionCopying.Amplification
