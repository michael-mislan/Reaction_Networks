import proofs.CompositionalMemory.SemenovLowInitialMetric
import proofs.CompositionalMemory.SemenovLowMetric15

namespace CompositionalMemory.Semenov.SemenovLowEndpoint
open Matrix

def ratio : ℚ := (9/100 : ℚ)
def AData : List ℚ := decodeRationals "717087301927/1099511627776,0,0,0,0,0,0,0,126763349521/1099511627776,373646379777/549755813888,0,0,0,0,0,0,-6638022191/68719476736,-594807872359/549755813888,179233350637/137438953472,0,0,0,0,0,-64515621687/1099511627776,-390748493765/549755813888,-287346121035/549755813888,782530807585/549755813888,0,0,0,0,-79151715415/549755813888,-796642732735/549755813888,892778105737/1099511627776,916070198497/1099511627776,1089569324507/1099511627776,0,0,0,210810617081/1099511627776,1012998121191/549755813888,365787549123/1099511627776,-2576609679121/1099511627776,-87716745107/137438953472,1328938443643/1099511627776,0,0,57660856235/549755813888,662496669249/549755813888,-1658948091213/549755813888,415566673965/274877906944,-127214472673/274877906944,-704763612913/1099511627776,784695966701/549755813888,0,-101069244669/1099511627776,-1152682307147/549755813888,109785707279/34359738368,1548039138587/549755813888,2363669915277/1099511627776,-538801539491/549755813888,-1290023825063/1099511627776,985205728823/274877906944"
def A : Matrix (Fin 8) (Fin 8) ℚ := fun i j => AData.getD (i.val*8+j.val) 0
def M : Matrix (Fin 8) (Fin 8) ℚ := fun i j => ratio*SemenovLowMetric15.pr i j-SemenovLowInitialMetric.pl i j/4
def G : Matrix (Fin 8) (Fin 8) ℚ := A*M*A.transpose

theorem finite_checks :
    (∀ i j,i<j → A i j=0) ∧ (∀ i,0<A i i) ∧
    (0 < ∑ i,∑ j,(A i j)^2) ∧
    (∀ i,(1/2 : ℚ) ≤ G i i-∑ j,if j=i then 0 else |G i j|) ∧
    (∀ i j,M i j=M j i) ∧
    (∀ i,(∑ j,|SemenovLowInitialMetric.pl i j|) ≤ (1601/1 : ℚ)) ∧
    (∀ i,SemenovLowInitialMetric.zl i=(SemenovLowMetric15.zr i+feedRational i)/2) ∧
    ((∑ i,SemenovLowMetric15.zr i)+8*SemenovLowMetric15.radius ≤ (1/5 : ℚ)) ∧
    ((∑ i,SemenovLowMetric15.zr i)/4+2*SemenovLowMetric15.radius+(∑ i,feedRational i)/2 ≤ (23/200 : ℚ)) ∧
    (SemenovLowMetric15.zr 1+SemenovLowMetric15.zr 2+SemenovLowMetric15.zr 3+3*SemenovLowMetric15.radius < (1/200 : ℚ)) := by native_decide

def initialCounts : Fin 8 → ℕ := ![1195666503776200872,5549468225961,293102171777,28928608368403,2399274129818308343,718782635388153,7087546303714,51141274954967074]
def initialDeviation (j : Fin 8) : ℚ := (initialCounts j : ℚ)/24000000000000000000-SemenovLowMetric15.zr j

theorem initial_encoder_checks :
    ((∑ i,∑ j,SemenovLowMetric15.pr i j*initialDeviation i*initialDeviation j) ≤ SemenovLowMetric15.eta) ∧
    ((∑ j,initialCounts j)+12000000000000000000 ≤ 20000000000000000000) ∧
    (∀ j,initialCounts j ≤ 20000000000000000000) := by native_decide

end CompositionalMemory.Semenov.SemenovLowEndpoint
