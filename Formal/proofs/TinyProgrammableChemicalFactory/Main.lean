import proofs.TinyProgrammableChemicalFactory.ConcreteWitness
import proofs.TinyProgrammableChemicalFactory.Partition
import proofs.TinyProgrammableChemicalFactory.UniformizationLower
import proofs.TinyProgrammableChemicalFactory.Iteration

/-! Compiled portions of the conventional/exact factory theorem.
The complete Python recurrence and CTMC clock-coupling bridges are NOT asserted
as Lean theorems here. See LEAN_SCOPE.md for the exact verification boundary. -/

namespace TinyProgrammableChemicalFactory

theorem certified_arithmetic_margin :
    (2147232289 : ℚ)/2147483648-15/1000000 > 4999/5000 ∧
    (4999/5000 : ℚ)^10 > 998/1000 :=
  ⟨concrete_budget,ten_cycle_budget⟩

end TinyProgrammableChemicalFactory

#print axioms TinyProgrammableChemicalFactory.literal_repair_clock
#print axioms TinyProgrammableChemicalFactory.corrected_inventory
#print axioms TinyProgrammableChemicalFactory.partition_is_binomial_expectation
#print axioms TinyProgrammableChemicalFactory.truncated_uniformization_lower
#print axioms TinyProgrammableChemicalFactory.conditional_iteration
#print axioms TinyProgrammableChemicalFactory.certified_arithmetic_margin
