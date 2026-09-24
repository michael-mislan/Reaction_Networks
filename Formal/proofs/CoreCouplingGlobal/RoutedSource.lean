import proofs.CoreCouplingCAC.Boundary
import proofs.CoreCouplingGlobal.RoutedCoupling

namespace CoreCouplingGlobal
open CoreCouplingCAC

/-- Species A,B,z,H,Zb; reaction 7 is the buffered fork. Zb is held at 1. -/
def routedInput : Fin 5 → Fin 8 → ℕ :=
  ![![1,0,0,0,0,0,0,1],![0,0,0,0,0,1,0,0],
    ![0,1,0,0,0,0,0,0],![0,0,1,0,0,0,1,0],![0,0,0,0,0,0,0,0]]
def routedOutput : Fin 5 → Fin 8 → ℕ :=
  ![![0,0,0,1,0,2,0,0],![1,0,0,0,1,0,0,1],
    ![1,0,2,0,0,0,0,0],![0,1,0,0,0,0,0,0],![0,0,0,0,0,0,0,1]]
noncomputable def routedForward (p : Rates) (g : ℝ) : Fin 8 → ℝ :=
  ![g,p.u,1,p.a,p.b,p.e,p.d,1-g]
noncomputable def routedReverse (p : Rates) (g : ℝ) : Fin 8 → ℝ :=
  ![g,1,p.v,1,1,p.e,0,1-g]
noncomputable def bufferedCoordinates (x : State) : Fin 5 → ℝ := ![x.A,x.B,x.z,x.H,1]
noncomputable def routedCurrent (p : Rates) (g : ℝ) (x : State) (r : Fin 8) : ℝ :=
  routedForward p g r*(∏ i, bufferedCoordinates x i^routedInput i r) -
  routedReverse p g r*(∏ i, bufferedCoordinates x i^routedOutput i r)
noncomputable def routedDerivative (p : Rates) (g : ℝ) (x : State) (i : Fin 4) : ℝ :=
  ∑ r, ((routedOutput i.castSucc r : ℝ)-routedInput i.castSucc r)*routedCurrent p g x r

theorem routed_literal_ODE (e g : ℝ) (x : State) :
    routedDerivative (flagshipRates e) g x =
      ![fA (flagshipRates e) x.A x.B (1-g+g*x.z),
        fB (flagshipRates e) x.A x.B (1-g+g*x.z),
        routedZ e g x,fH (flagshipRates e) x.z x.H] := by
  funext i
  fin_cases i <;>
    norm_num [routedDerivative,routedCurrent,routedForward,routedReverse,
      routedInput,routedOutput,bufferedCoordinates,Fin.sum_univ_succ,Fin.prod_univ_succ,
      fA,fB,fH,routedZ,flagshipRates] <;> ring

theorem fork_capacity_preserved (p : Rates) (g : ℝ) :
    routedForward p g 0+routedForward p g 7=1 ∧
    routedReverse p g 0+routedReverse p g 7=1 := by
  change g+(1-g)=1 ∧ g+(1-g)=1
  constructor <;> ring

theorem routed_AB_core (buffered : Bool) (i r : Fin 2) :
    routedInput (![0,1] i) (![if buffered then 7 else 0,5] r)=coreInput i r ∧
    routedOutput (![0,1] i) (![if buffered then 7 else 0,5] r)=coreOutput i r := by
  cases buffered <;> fin_cases i <;> fin_cases r <;> decide

theorem routed_ZH_core (i r : Fin 2) :
    routedInput (![2,3] i) (![1,2] r)=coreInput i r ∧
    routedOutput (![2,3] i) (![1,2] r)=coreOutput i r := by
  fin_cases i <;> fin_cases r <;> decide

def routedMass : Fin 5 → ℕ := ![2,1,1,2,1]
def routedExternalInput : Fin 5 → Fin 8 → ℕ :=
  ![![0,1,0,0,0,0,0,0],![0,0,0,0,0,1,0,0],
    ![0,0,0,1,0,0,0,0],![0,0,0,0,1,0,0,0],![0,0,0,0,0,0,0,0]]
def routedExternalOutput : Fin 5 → Fin 8 → ℕ :=
  ![![0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0],![0,0,0,0,0,0,1,0]]

theorem routed_mass_balance (r : Fin 8) :
    (∑ i, routedMass i*routedInput i r)+(∑ i, externalMass i*routedExternalInput i r)=
    (∑ i, routedMass i*routedOutput i r)+(∑ i, externalMass i*routedExternalOutput i r) := by
  fin_cases r <;> norm_num [routedMass,routedInput,routedOutput,externalMass,
    routedExternalInput,routedExternalOutput,Fin.sum_univ_succ]

noncomputable def routedPotential (p : Rates) : Fin 5 → ℝ := ![0,0,0,-Real.log p.v,0]
noncomputable def routedAffinity (p : Rates) (r : Fin 8) : ℝ :=
  (∑ i, routedPotential p i*((routedInput i r : ℝ)-routedOutput i r))+
  (∑ i, externalPotential p i*((routedExternalInput i r : ℝ)-routedExternalOutput i r))

theorem routed_reversible_ratios (p : Rates) (hp : p.Positive) (g : ℝ)
    (hg : 0 < g) (hg1 : g < 1) (r : Fin 8) (hr : r ≠ 6) :
    routedForward p g r/routedReverse p g r = Real.exp (routedAffinity p r) := by
  rcases hp with ⟨ha,hb,hu,hv,he,hd⟩
  have hg' : 1-g ≠ 0 := by linarith
  fin_cases r <;>
    norm_num [routedForward,routedReverse,routedAffinity,routedPotential,externalPotential,
      routedInput,routedOutput,routedExternalInput,routedExternalOutput,Fin.sum_univ_succ,
      ne_of_gt hg,hg'] at hr ⊢
  · rw [Real.exp_log hu]
  · rw [Real.exp_neg,Real.exp_log hv]
  · rw [Real.exp_log ha]
  · rw [Real.exp_log hb]
  · exact ne_of_gt he
  · exact (hr rfl).elim

end CoreCouplingGlobal
