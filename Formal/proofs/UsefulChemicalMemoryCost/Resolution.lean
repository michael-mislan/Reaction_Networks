import proofs.UsefulChemicalMemoryCost.Frontier

/-! Formal spine of the C/E publication. The external integer recurrence and
the complete literal CTMC probability bridge are not claimed as K evidence. -/
namespace UsefulChemicalMemoryCost

theorem publication_arithmetic :
    (2145514420 : ℚ)/2147483648 > 999/1000 ∧
    ((2145514420 : ℚ)/2147483648)^10 > 99/100 :=
  ⟨exact_frontier_margins.1, ten_cycle_margin⟩

end UsefulChemicalMemoryCost

#print axioms UsefulChemicalMemoryCost.envelope_le_kernel
#print axioms UsefulChemicalMemoryCost.robust_poisson_lower
#print axioms UsefulChemicalMemoryCost.complement_upper
#print axioms UsefulChemicalMemoryCost.jump_conserves
#print axioms UsefulChemicalMemoryCost.release_affine
#print axioms UsefulChemicalMemoryCost.complementary_daughter_return
#print axioms UsefulChemicalMemoryCost.material_necessary
#print axioms UsefulChemicalMemoryCost.publication_arithmetic
