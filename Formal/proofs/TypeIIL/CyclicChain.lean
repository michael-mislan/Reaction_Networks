import proofs.TypeIIL.CyclicArc
import proofs.TypeII3.Network.ChainNetwork

namespace TypeIIL

open TypeII3

/-- Source-faithful positive-gap data: every one-to-one segment may contain an
arbitrary finite reversible unit chain with positive intermediate degradation. -/
structure CyclicChainData (l : ℕ) where
  next : Fin l ≃ Fin l
  next_singleCycle : IsSingleCycle next
  arc : Fin l → ArcChainRates
  fork : Fin l → ForkRates

noncomputable def CyclicChainData.effective (D : CyclicChainData l) : CyclicArcData l :=
  { next := D.next
    next_singleCycle := D.next_singleCycle
    arc := fun i => (D.arc i).effective
    fork := D.fork }

@[ext] structure CyclicChainState (D : CyclicChainData l) where
  endpoints : CyclicArcState l
  rp : ∀ i, (D.arc i).rp.State
  pq : ∀ i, (D.arc i).pq.State

def PositiveCyclicChainState {D : CyclicChainData l}
    (x : CyclicChainState D) : Prop := PositiveCyclicArcState x.endpoints

def IsCyclicChainStationary {D : CyclicChainData l}
    (x : CyclicChainState D) : Prop :=
  ∀ i, ArcChainSteady (D.arc i) (x.rp i) (x.pq i)
    (D.fork (D.next.symm i)).m
    (cyclicForkCurrent D.effective x.endpoints (D.next.symm i))
    (cyclicForkCurrent D.effective x.endpoints i)
    (x.endpoints.R (D.next.symm i)) (x.endpoints.P i) (x.endpoints.Q i)

theorem cyclic_chain_to_arc_stationary
    {D : CyclicChainData l} (x : CyclicChainState D)
    (h : IsCyclicChainStationary x) :
    IsCyclicArcStationary D.effective x.endpoints := by
  intro i
  exact arc_chain_compress (D.arc i) (x.rp i) (x.pq i) (h i)

/-- Unistationarity after inserting arbitrary finite positive-gap unit chains. -/
theorem cyclic_chain_unistationarity [NeZero l]
    (D : CyclicChainData l) (x y : CyclicChainState D)
    (hx : PositiveCyclicChainState x) (hy : PositiveCyclicChainState y)
    (hxstat : IsCyclicChainStationary x)
    (hystat : IsCyclicChainStationary y) : x = y := by
  have he : x.endpoints = y.endpoints :=
    cyclic_arc_unistationarity D.effective x.endpoints y.endpoints hx hy
      (cyclic_chain_to_arc_stationary x hxstat)
      (cyclic_chain_to_arc_stationary y hystat)
  cases x with
  | mk xe xrp xpq =>
    cases y with
    | mk ye yrp ypq =>
      dsimp at he hxstat hystat ⊢
      subst ye
      have hrp : xrp = yrp := by
        funext i
        exact (arc_chain_states_unique (D.arc i) (xrp i) (yrp i)
          (xpq i) (ypq i) (hxstat i) (hystat i)).1
      have hpq : xpq = ypq := by
        funext i
        exact (arc_chain_states_unique (D.arc i) (xrp i) (yrp i)
          (xpq i) (ypq i) (hxstat i) (hystat i)).2
      subst yrp
      subst ypq
      rfl

end TypeIIL
