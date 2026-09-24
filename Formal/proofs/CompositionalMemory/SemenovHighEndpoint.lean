import proofs.CompositionalMemory.SemenovHighInitialMetric
import proofs.CompositionalMemory.SemenovHighMetric21

namespace CompositionalMemory.Semenov.SemenovHighEndpoint
open Matrix

def ratio : ℚ := (13/50 : ℚ)
def AData : List ℚ := decodeRationals "40032557743/549755813888,0,0,0,0,0,0,0,1611468317/274877906944,19839070411/137438953472,0,0,0,0,0,0,-67286986883/1099511627776,2401126527/1099511627776,67049496709/549755813888,0,0,0,0,0,-68557669595/549755813888,4955512451/1099511627776,103588264929/1099511627776,42389463851/274877906944,0,0,0,0,39522144713/1099511627776,-123802097525/1099511627776,8591183933/1099511627776,266980393/34359738368,73279692159/549755813888,0,0,0,-15962119239/137438953472,246113558699/549755813888,129708865967/1099511627776,-134294839423/549755813888,-209464635583/549755813888,210604421931/549755813888,0,0,-150404652313/1099511627776,579589923247/1099511627776,-251180578903/1099511627776,43895589169/549755813888,-493237481597/1099511627776,17208832275/274877906944,6672902397/17179869184,0,-251875494851/1099511627776,1722007050645/549755813888,108562325505/68719476736,1740621671775/1099511627776,-332498009077/549755813888,320031025863/1099511627776,160206103081/549755813888,777124157587/137438953472"
def A : Matrix (Fin 8) (Fin 8) ℚ := fun i j => AData.getD (i.val*8+j.val) 0
def M : Matrix (Fin 8) (Fin 8) ℚ := fun i j => ratio*SemenovHighMetric21.pr i j-SemenovHighInitialMetric.pl i j/4
def G : Matrix (Fin 8) (Fin 8) ℚ := A*M*A.transpose

theorem finite_checks :
    (∀ i j,i<j → A i j=0) ∧ (∀ i,0<A i i) ∧
    (0 < ∑ i,∑ j,(A i j)^2) ∧
    (∀ i,(1/2 : ℚ) ≤ G i i-∑ j,if j=i then 0 else |G i j|) ∧
    (∀ i j,M i j=M j i) ∧
    (∀ i,(∑ j,|SemenovHighInitialMetric.pl i j|) ≤ (3818/1 : ℚ)) ∧
    (∀ i,SemenovHighInitialMetric.zl i=(SemenovHighMetric21.zr i+feedRational i)/2) ∧
    ((∑ i,SemenovHighMetric21.zr i)+8*SemenovHighMetric21.radius ≤ (1/5 : ℚ)) ∧
    ((∑ i,SemenovHighMetric21.zr i)/4+2*SemenovHighMetric21.radius+(∑ i,feedRational i)/2 ≤ (57/500 : ℚ)) ∧
    ((1/200 : ℚ) < SemenovHighMetric21.zr 1+SemenovHighMetric21.zr 2+SemenovHighMetric21.zr 3-3*SemenovHighMetric21.radius) := by native_decide

def initialCounts : Fin 8 → ℕ := ![316345972886838230,352371068533633244,237729813559436550,238134557442879452,1140555790456085905,630262775889742582,629181433654173311,21412422786833]
def initialDeviation (j : Fin 8) : ℚ := (initialCounts j : ℚ)/24000000000000000000-SemenovHighMetric21.zr j

theorem initial_encoder_checks :
    ((∑ i,∑ j,SemenovHighMetric21.pr i j*initialDeviation i*initialDeviation j) ≤ SemenovHighMetric21.eta) ∧
    ((∑ j,initialCounts j)+12000000000000000000 ≤ 20000000000000000000) ∧
    (∀ j,initialCounts j ≤ 20000000000000000000) := by native_decide

end CompositionalMemory.Semenov.SemenovHighEndpoint
