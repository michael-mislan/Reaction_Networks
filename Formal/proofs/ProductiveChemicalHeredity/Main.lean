import proofs.ProductiveChemicalHeredity.Partition
import proofs.ProductiveChemicalHeredity.Rates
import proofs.ProductiveChemicalHeredity.Bounds
import proofs.TinyProgrammableChemicalFactory.Iteration

/-! Modular verification of the PCHF-1 conventional theorem. The finite-CTMC
clock argument and uniform Bernoulli endpoint coupling remain conventional;
this module does not assert an end-to-end formal probability theorem. -/

namespace ProductiveChemicalHeredity

theorem declared_arithmetic_and_budget :
    (49999/50000 : ℚ)*(99957/100000)>1999/2000 ∧
    (1999/2000 : ℚ)^10>995/1000 ∧ (415+420*10 : ℕ)=4615 := by
  exact ⟨joint_margin,ten_cycle_margin,finite_supply_ledger.1⟩

theorem repeated_conditional_success (p : ℕ → ℝ) (h0 : p 0=1)
    (hstep : ∀ n, (1999/2000 : ℝ)*p n≤p (n+1)) :
    (1999/2000 : ℝ)^10≤p 10 :=
  TinyProgrammableChemicalFactory.conditional_iteration p (1999/2000) (by norm_num) h0 hstep 10

end ProductiveChemicalHeredity

#print axioms ProductiveChemicalHeredity.exact_closed_pair
#print axioms ProductiveChemicalHeredity.forward_rate_lower
#print axioms ProductiveChemicalHeredity.reverse_rate_upper
#print axioms ProductiveChemicalHeredity.complementary_binomial_law
#print axioms ProductiveChemicalHeredity.endpoint_tail_certificate
#print axioms ProductiveChemicalHeredity.forward_wait_bound
#print axioms ProductiveChemicalHeredity.repeated_conditional_success
#print axioms ProductiveChemicalHeredity.declared_arithmetic_and_budget
