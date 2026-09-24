import Mathlib

namespace CompositionalMemory.ReversibleChemistry

/-- Species order is F,W,M,X,Y. Each forward channel has its exact opposite
as reverse channel. Equal assigned molecular masses are an explicit formal
completion, not an identification of particular chemical compounds. -/
def forwardStoich (r : Fin 6) : Fin 5 → Int :=
  ![![-1,0,0,1,0],![-1,0,0,2,-1],![0,0,0,-1,1],
    ![0,1,0,-1,0],![0,1,0,-1,0],![0,0,1,-1,0]] r

def stoich (r : Fin 6) (reverse : Bool) (j : Fin 5) : Int :=
  if reverse then -forwardStoich r j else forwardStoich r j

theorem forward_mass_balance (r : Fin 6) : (∑ j,forwardStoich r j)=0 := by
  fin_cases r <;> norm_num [forwardStoich,Fin.sum_univ_succ]

theorem mass_balance (r : Fin 6) (reverse : Bool) : (∑ j,stoich r reverse j)=0 := by
  cases reverse <;> simp [stoich,forward_mass_balance,Finset.sum_neg_distrib]

def forwardCoefficient : Fin 5 → ℚ := ![193/5,1555,15,100,105/2]
def reverseCoefficient : Fin 5 → ℚ := ![193/750000,311/30000,15,1/1000,21/40000]

theorem coefficients_positive (r : Fin 5) :
    0 < forwardCoefficient r ∧ 0 < reverseCoefficient r := by
  fin_cases r <;> norm_num [forwardCoefficient,reverseCoefficient]

/-- These effective chemostatted ratios obey both shared-reservoir cycle
constraints. The equal X/Y ratio also permits symmetric catalytic conversion. -/
theorem fixed_cycle_ratios :
    forwardCoefficient 0/reverseCoefficient 0=150000 ∧
    forwardCoefficient 1/reverseCoefficient 1=150000 ∧
    forwardCoefficient 2/reverseCoefficient 2=1 ∧
    forwardCoefficient 3/reverseCoefficient 3=100000 ∧
    forwardCoefficient 4/reverseCoefficient 4=100000 := by
  change (193/5 : ℚ)/(193/750000)=150000 ∧ (1555 : ℚ)/(311/30000)=150000 ∧
    (15 : ℚ)/15=1 ∧ (100 : ℚ)/(1/1000)=100000 ∧ (105/2 : ℚ)/(21/40000)=100000
  norm_num

theorem reverse_growth_budget :
    (9901/10000 : ℚ)-80*53*(1/100000000)-20*4000000/(2000000000000)=618761/625000 ∧
    (99/100 : ℚ)<618761/625000 := by
  norm_num

end CompositionalMemory.ReversibleChemistry
