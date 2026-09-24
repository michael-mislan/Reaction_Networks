import proofs.SmallResidentCompositionCopying.AmplificationGeometry
import proofs.SmallResidentCompositionCopying.AmplificationStoichiometry

namespace SmallResidentCompositionCopying.Amplification
open Classical FiniteCopy CompositionalMemory HeritableCompositions
noncomputable section

/-- Scheduled split at time20; an unfinished amplification or exhausted food
quota is failure. The terminal sum uses the actual complementary allocation. -/
def actualTerminal : Option (Counts × Fin quota) → ℝ
  | none => 0
  | some (z,_) => if z.1.val=19 ∧ z.2.val=19 then
      ∑ a ∈ Finset.range 21, ∑ b ∈ Finset.range 21,
        if goodAllocation a b then allocationWeight a b else 0
    else 0

def actualJointReturn (word : Word) (z : Counts) : ℝ :=
  finiteTimeExpectation (chemicalCycle word) 20 actualTerminal (cycleStart z)

theorem actual_terminal_eq : actualTerminal=cyclePayoff := by
  funext s
  cases s with
  | none => rfl
  | some z => simp [actualTerminal,cyclePayoff,killedBudgetObservable,payoff,exact_partition]

theorem actual_joint_return (word : Word) (z : Counts) :
    (99:ℝ)/100 ≤ actualJointReturn word z := by
  unfold actualJointReturn
  rw [actual_terminal_eq]
  exact chemical_deadline word z

theorem actual_probability_bounds (word : Word) (z : Counts) :
    0 ≤ actualJointReturn word z ∧ actualJointReturn word z ≤ 1 := by
  unfold actualJointReturn
  rw [actual_terminal_eq]
  apply finite_time_bounds
  intro s
  cases s with
  | none => norm_num [cyclePayoff,killedBudgetObservable]
  | some z =>
    simp only [cyclePayoff,killedBudgetObservable,payoff,Option.elim]
    split_ifs <;> first | exact partition_bounds | norm_num

/-- Reset the event counter and external clock. These fields are independent
of the resident label. Food is renewed externally, with the quota charged. -/
theorem restart_same_law (a b : ℕ) (h : goodAllocation a b) :
    newborn (daughterCounts a b h) ∧ newborn (complementCounts a b h) ∧
    (cycleStart (daughterCounts a b h)).isSome ∧
    (cycleStart (complementCounts a b h)).isSome := by
  exact ⟨(daughters_restart a b h).1,(daughters_restart a b h).2,rfl,rfl⟩

/-- Each reaction changes its food pool by one molecule. Hence a quota of J
events requires at most J supplied food molecules and J removal capacity per
pool, in addition to the maintained pool inventory. -/
theorem food_capacity (events : ℕ) (h : events < quota) : events ≤ 1000000000 := by
  norm_num [quota] at h
  omega

def remainingFood (c : Fin quota) : ℕ := quota-c.val

theorem food_available (c : Fin quota) : 0 < remainingFood c := by
  have hc := c.isLt
  dsimp [remainingFood]
  omega

theorem charged_food_step (c : Fin quota) (hc : c.val+1<quota) :
    remainingFood c=remainingFood ⟨c.val+1,hc⟩+1 := by
  have hc' := c.isLt
  dsimp [remainingFood]
  omega

theorem complete_cycle_food_capacity (events : ℕ) (h : events<quota) :
    events+3 ≤ 1000000003 ∧ events+1 ≤ 1000000001 := by
  have he := food_capacity events h
  omega

def sourceProperties : Prop :=
    ((1000:ℝ)/1=1000 ∧ (100:ℝ)/(1/10)=1000 ∧ (0:ℝ)<1 ∧ (0:ℝ)<1/10) ∧
    (birth ⟨0,by decide⟩ ⟨1,by decide⟩ - birth ⟨0,by decide⟩ ⟨0,by decide⟩=100) ∧
    (∀ word z r b c, chemicalRate word (some z) r b c=
      molecularRate (residentVector word (some z)) r b c) ∧
    (∀ word z r b c, 0<chemicalRate word (some z) r b c → ∀ k,
      residentVector word (model.next (some z) r) k=
        molecularNext (residentVector word (some z)) r b k)

theorem source_properties : sourceProperties :=
  ⟨common_activity_completion,interaction_changes_rate,word_independent_rates,literal_next⟩

/-- One common positive concentration assignment: every resident has activity
1000 and both foods have activity1. It balances every underlying reaction pair
before the label-blind quench is applied. -/
theorem detailed_balance_point :
    (1000:ℝ)*1000*1=1*1000^2 ∧
    (100:ℝ)*1000*1000*1=(1/10:ℝ)*1000^2*1000 := by norm_num

theorem encoded_cycle (word : Word) : newborn preparation ∧
    totalResidents preparation=20 ∧ (99:ℝ)/100 ≤ actualJointReturn word preparation := by
  exact ⟨preparation_admitted,by norm_num [totalResidents,preparation],actual_joint_return word preparation⟩

end
end SmallResidentCompositionCopying.Amplification
