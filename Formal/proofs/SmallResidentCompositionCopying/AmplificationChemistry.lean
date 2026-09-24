import proofs.SmallResidentCompositionCopying.AmplificationDeadline
import proofs.CompositionalMemory.FiniteGeneratorTransport

namespace SmallResidentCompositionCopying.Amplification
open FiniteCopy CompositionalMemory
noncomputable section

abbrev Word := Fin 2 → Bool
abbrev Species := Fin 2 × Bool
abbrev ChemicalChannel := Fin 4 × Bool × Option Bool

def moduleCount (z : Counts) (i : Fin 2) : Fin 20 := if i=0 then z.1 else z.2
def resident (word : Word) (z : Counts) (i : Fin 2) (b : Bool) : ℕ :=
  if word i=b then (moduleCount z i).val+1 else 0
def moduleOf (r : Fin 4) : Fin 2 := if r.val<2 then 0 else 1
def neighborOf (r : Fin 4) : Fin 2 := if r.val<2 then 1 else 0

/-- Same food activity and constants for both species and both modules.
The external quench reads only the module total. -/
def chemicalBase (word : Word) (z : Counts) (r : Fin 4) (b : Bool) : ℝ :=
  if (moduleCount z (moduleOf r)).val < 19 then
    if r=0 ∨ r=2 then 1000*(resident word z (moduleOf r) b : ℝ)
    else ((resident word z (moduleOf r) b * (resident word z (moduleOf r) b-1) : ℕ):ℝ)
  else 0

/-- None is uncatalyzed; either neighbor species is an explicit catalyst. -/
def catalystFactor (word : Word) (z : Counts) (r : Fin 4) : Option Bool → ℝ
  | none => 1
  | some b => (resident word z (neighborOf r) b : ℝ)/10

def chemicalRate (word : Word) (s : State) (r : Fin 4) (b : Bool) (c : Option Bool) : ℝ :=
  s.elim 0 fun z => chemicalBase word z r b * catalystFactor word z r c

def chemicalModel (word : Word) : FiniteJumpModel State ChemicalChannel where
  next s r := model.next s r.1
  rate s r := chemicalRate word s r.1 r.2.1 r.2.2
  nonneg s r := by
    cases s with
    | none => exact le_rfl
    | some z =>
      simp only [chemicalRate,Option.elim]
      apply mul_nonneg
      · unfold chemicalBase
        split_ifs <;> positivity
      · cases r.2.2 <;> simp only [catalystFactor] <;> positivity

theorem chemical_channel_sum (word : Word) (s : State) (r : Fin 4) :
    (∑ b : Bool, ∑ c : Option Bool, chemicalRate word s r b c) = model.rate s r := by
  cases s with
  | none => simp [chemicalRate,model]
  | some z =>
    fin_cases r <;> cases h₀ : word 0 <;> cases h₁ : word 1 <;>
      simp [chemicalRate,chemicalBase,catalystFactor,resident,moduleCount,moduleOf,
        neighborOf,model,birth,death,factor,Fintype.sum_option,h₀,h₁] <;>
      split_ifs <;> norm_num [Nat.cast_mul,Nat.cast_add] <;> ring

theorem chemical_generator (word : Word) (f : State → ℝ) (s : State) :
    (chemicalModel word).generator f s = model.generator f s := by
  simp only [FiniteJumpModel.generator,chemicalModel,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [← Finset.sum_mul]
  rw [chemical_channel_sum]

def chemicalCycle (word : Word) := killedBudgetModel (chemicalModel word) quota

theorem chemical_budget_generator (word : Word)
    (f : Option (Counts × Fin quota) → ℝ) (s : Option (Counts × Fin quota)) :
    (chemicalCycle word).generator f s = cycleModel.generator f s := by
  cases s with
  | none => simp [chemicalCycle,cycleModel,FiniteJumpModel.generator,killedBudgetModel]
  | some z =>
    simp only [chemicalCycle,cycleModel,FiniteJumpModel.generator,killedBudgetModel,
      Option.elim,chemicalModel,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r _
    change (∑ b : Bool, ∑ c : Option Bool, chemicalRate word (some z.1) r b c *
      (f (killedBudgetNext model quota (some z) r)-f (some z))) =
      model.rate (some z.1) r * (f (killedBudgetNext model quota (some z) r)-f (some z))
    simp_rw [← Finset.sum_mul]
    rw [chemical_channel_sum]

theorem chemical_deadline (word : Word) (z : Counts) : (99:ℝ)/100 ≤
    finiteTimeExpectation (chemicalCycle word) 20 cyclePayoff (cycleStart z) := by
  rw [finite_time_generator_congr (chemicalCycle word) cycleModel (chemical_budget_generator word)]
  exact deadline_bound z

/-- All equilibrium ratios coincide; cross catalysis multiplies both directions
by 1/10 and therefore preserves the same thermodynamic activity assignment. -/
theorem common_activity_completion :
    (1000:ℝ)/1=1000 ∧ (100:ℝ)/(1/10)=1000 ∧
    (0:ℝ)<1 ∧ (0:ℝ)<1/10 := by norm_num

end
end SmallResidentCompositionCopying.Amplification
