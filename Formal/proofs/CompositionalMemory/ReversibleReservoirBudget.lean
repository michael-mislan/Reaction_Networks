import proofs.CompositionalMemory.ReversiblePhysicalSource
import proofs.CompositionalMemory.ReversibleChemicalBookkeeping

namespace CompositionalMemory
open FiniteCopy

/-- Local F,W,M,X,Y increments, in the fourteen-channel physical-source order.
The other slot's catalyst is unchanged in the cross channels. -/
def reversibleChannelStoich : Fin 14 → Fin 5 → Int :=
  ![![-1,0,0,1,0],![-1,0,0,2,-1],![0,0,0,-1,1],
    ![0,1,0,-1,0],![0,1,0,-1,0],![0,0,1,-1,0],
    ![0,0,0,-1,1],![0,0,0,1,-1],![1,0,0,-1,0],
    ![1,0,0,-2,1],![0,0,0,1,-1],![0,-1,0,1,0],
    ![0,-1,0,1,0],![0,0,-1,1,0]]

theorem reversible_channel_mass_balance (r : Fin 14) : (∑ i,reversibleChannelStoich r i)=0 := by
  fin_cases r <;> norm_num [reversibleChannelStoich,Fin.sum_univ_succ]

/-- Signed local exchange with an external supply/disposal system. Positive
means supply. Both F and W are held at exactly1000*m molecules per slot. -/
def reversibleControllerExchange (slot : Fin 2) (pool : Fin 2)
    (r : Option ReversiblePhysicalChannel) : Int :=
  match r with
  | none => 0
  | some (actor,channel) =>
    1000*reversibleChannelStoich channel 2-
      if actor=slot then reversibleChannelStoich channel ⟨pool.val,by omega⟩ else 0

theorem reversible_controller_exchange_bounds (slot pool : Fin 2)
    (r : Option ReversiblePhysicalChannel) :
    -1001 ≤ reversibleControllerExchange slot pool r ∧
      reversibleControllerExchange slot pool r ≤ 1001 := by
  cases r with
  | none => norm_num [reversibleControllerExchange]
  | some r =>
    rcases r with ⟨actor,channel⟩
    by_cases h : actor=slot
    · fin_cases channel <;> fin_cases pool <;>
        norm_num [reversibleControllerExchange,reversibleChannelStoich,h,Matrix.cons_val_two]
    · fin_cases channel <;> fin_cases pool <;>
        norm_num [reversibleControllerExchange,reversibleChannelStoich,h,Matrix.cons_val_two]

theorem reversible_controller_restores_pool (m : Int) (slot pool : Fin 2)
    (actor : Fin 2) (channel : Fin 14) :
    1000*m+(if actor=slot then reversibleChannelStoich channel ⟨pool.val,by omega⟩ else 0)+
      reversibleControllerExchange slot pool (some (actor,channel))=
      1000*(m+reversibleChannelStoich channel 2) := by
  simp only [reversibleControllerExchange]
  ring

/-- Gross supply bound: removed material need never be recycled to obtain
this finite-stock guarantee. The initial local pool is included. -/
theorem reversible_controller_supply_budget (N J q : Nat) (hq : q ≤ J)
    (events : Nat → Option ReversiblePhysicalChannel) (slot pool : Fin 2) :
    1000*(N : Int)+(∑ i ∈ Finset.range q,max (reversibleControllerExchange slot pool (events i)) 0) ≤
      1000*(N : Int)+1001*(J : Int) := by
  have hs : (∑ i ∈ Finset.range q,max (reversibleControllerExchange slot pool (events i)) 0) ≤
      1001*(q : Int) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range q,(1001 : Int) := by
        apply Finset.sum_le_sum
        intro i _
        exact max_le (reversible_controller_exchange_bounds slot pool (events i)).2 (by norm_num)
      _ = _ := by simp; ring
  have hc : (q : Int) ≤ J := Int.ofNat_le.mpr hq
  omega

theorem reversible_controller_disposal_budget (N J q : Nat) (hq : q ≤ J)
    (events : Nat → Option ReversiblePhysicalChannel) (slot pool : Fin 2) :
    1000*(N : Int)+(∑ i ∈ Finset.range q,max (-reversibleControllerExchange slot pool (events i)) 0) ≤
      1000*(N : Int)+1001*(J : Int) := by
  have hs : (∑ i ∈ Finset.range q,max (-reversibleControllerExchange slot pool (events i)) 0) ≤
      1001*(q : Int) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range q,(1001 : Int) := by
        apply Finset.sum_le_sum
        intro i _
        apply max_le _ (by norm_num)
        have hh := (reversible_controller_exchange_bounds slot pool (events i)).1
        omega
      _ = _ := by simp; ring
  have hc : (q : Int) ≤ J := Int.ofNat_le.mpr hq
  omega

theorem reversible_controller_concrete_inventory :
    (1000*53+1001*100000000 : Nat)=100100053000 ∧
      4*10*(1000*53+1001*100000000 : Nat)=4004002120000 := by norm_num

end CompositionalMemory
