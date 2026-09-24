import proofs.CompositionalMemory.ReversibleReservoirBudget

namespace CompositionalMemory

/-- Gross supply required to reset complementary allocations to equal targets.
This controller acts only on growth material and chemostatted pools; it does
not repair or relabel the information-bearing resident allocation. -/
def reversibleDivisionResetSupply (q a : Int) : Int :=
  max (q-a) 0+max (q-(2*q-a)) 0

def reversibleDivisionResetDisposal (q a : Int) : Int :=
  max (a-q) 0+max ((2*q-a)-q) 0

theorem reversible_division_reset_bounds (q a : Int)
    (ha : 0 ≤ a) (hau : a ≤ 2*q) :
    reversibleDivisionResetSupply q a ≤ q ∧
      reversibleDivisionResetDisposal q a ≤ q := by
  by_cases h : a ≤ q
  · have h1 : 0 ≤ q-a := by omega
    have h2 : q-(2*q-a) ≤ 0 := by omega
    have h3 : a-q ≤ 0 := by omega
    have h4 : 0 ≤ (2*q-a)-q := by omega
    simp only [reversibleDivisionResetSupply,reversibleDivisionResetDisposal,
      max_eq_left h1,max_eq_right h2,max_eq_right h3,max_eq_left h4]
    omega
  · have h1 : q-a ≤ 0 := by omega
    have h2 : 0 ≤ q-(2*q-a) := by omega
    have h3 : 0 ≤ a-q := by omega
    have h4 : (2*q-a)-q ≤ 0 := by omega
    simp only [reversibleDivisionResetSupply,reversibleDivisionResetDisposal,
      max_eq_right h1,max_eq_left h2,max_eq_left h3,max_eq_right h4]
    omega

theorem reversible_division_reset_targets (q a : Int) :
    a+(q-a)=q ∧ (2*q-a)+(q-(2*q-a))=q := by constructor <;> ring

/-- Includes startup, arbitrary chemical prefix, division reset, and disposal
of both final local pools. Replacing discarded pools is never assumed free. -/
theorem reversible_complete_pool_supply_budget (N J t : Nat) (ht : t ≤ J)
    (events : Nat → Option ReversiblePhysicalChannel) (slot pool : Fin 2)
    (a : Int) (ha : 0 ≤ a) (hau : a ≤ 2*(1000*(N : Int))) :
    1000*(N : Int)+(∑ i ∈ Finset.range t,max (reversibleControllerExchange slot pool (events i)) 0)+
      reversibleDivisionResetSupply (1000*N) a+2*(1000*N) ≤
      4000*(N : Int)+1001*(J : Int) := by
  have hc := reversible_controller_supply_budget N J t ht events slot pool
  have hr := (reversible_division_reset_bounds (1000*(N : Int)) a ha hau).1
  omega

theorem reversible_complete_pool_disposal_budget (N J t : Nat) (ht : t ≤ J)
    (events : Nat → Option ReversiblePhysicalChannel) (slot pool : Fin 2)
    (a : Int) (ha : 0 ≤ a) (hau : a ≤ 2*(1000*(N : Int))) :
    1000*(N : Int)+(∑ i ∈ Finset.range t,max (-reversibleControllerExchange slot pool (events i)) 0)+
      reversibleDivisionResetDisposal (1000*N) a+2*(1000*N) ≤
      4000*(N : Int)+1001*(J : Int) := by
  have hc := reversible_controller_disposal_budget N J t ht events slot pool
  have hr := (reversible_division_reset_bounds (1000*(N : Int)) a ha hau).2
  omega

theorem reversible_complete_inventory_numbers :
    (4000*53+1001*100000000 : Nat)=100100212000 ∧
      4*10*(4000*53+1001*100000000 : Nat)=4004008480000 ∧
      (4*53 : Nat)=212 := by norm_num

end CompositionalMemory
