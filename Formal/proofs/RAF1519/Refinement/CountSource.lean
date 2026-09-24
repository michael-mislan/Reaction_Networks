import proofs.RAF1519.Refinement.Source

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

/-- Seven oriented chemical pairs; negative direction has the opposite jump. -/
def chemicalJump (j : Fin 7) : Fin 7 → ℝ :=
  ![![-1,-1,1,0,0,0,0],![-1,0,-1,1,0,0,0],
    ![0,-1,0,-1,1,0,0],![0,0,0,0,-1,1,0],
    ![0,0,2,0,0,-1,0],![0,0,-1,0,0,0,1],![1,1,0,0,0,0,-1]] j

/-- Pair 3 is C2 -> Z, with coordinates U,W,X,C1,C2,Z,D. -/
def jumps (j : Fin 7) : Fin 7 → ℝ := chemicalJump j

def forwardRate (r d beta theta : ℝ) (c : State) : Fin 7 → ℝ :=
  ![(1/500000000)*c 0*c 1,20*c 2*c 0,20*c 3*c 1,
    20*c 4,r*c 5,d*(1+beta)*c 2,d/theta*c 6]
def reverseRate (r d beta theta V : ℝ) (c : State) : Fin 7 → ℝ :=
  ![(1/5000000000)*c 2,20*c 3,20*c 4,2*c 5,
    r*(c 2^2-c 2/V),d*beta/theta*c 6,
    d*(1/8000000000)*(1+beta)/beta*c 0*c 1]

/-- Concentration drift of fourteen chemical labels, two feeds, seven washouts. -/
def countDrift (r d beta theta V : ℝ) (c : State) : State := fun i =>
  ![1,1,0,0,0,0,0] i-c i +
    ∑ j : Fin 7, (forwardRate r d beta theta c j-reverseRate r d beta theta V c j)*jumps j i

theorem chemical_material (j : Fin 7) : materialA (jumps j) = 0 ∧ materialB (jumps j) = 0 := by
  fin_cases j
  · change (-1+1+2*0+2*0+2*0+0:ℝ)=0 ∧ (-1+1+0+2*0+2*0+0:ℝ)=0
    norm_num
  · change (-1+(-1)+2*1+2*0+2*0+0:ℝ)=0 ∧ (0+(-1)+1+2*0+2*0+0:ℝ)=0
    norm_num
  · change (0+0+2*(-1)+2*1+2*0+0:ℝ)=0 ∧ (-1+0+(-1)+2*1+2*0+0:ℝ)=0
    norm_num
  · change (0+0+2*0+2*(-1)+2*1+0:ℝ)=0 ∧ (0+0+0+2*(-1)+2*1+0:ℝ)=0
    norm_num
  · change (0+2+2*0+2*0+2*(-1)+0:ℝ)=0 ∧ (0+2+0+2*0+2*(-1)+0:ℝ)=0
    norm_num
  · change (0+(-1)+2*0+2*0+2*0+1:ℝ)=0 ∧ (0+(-1)+0+2*0+2*0+1:ℝ)=0
    norm_num
  · change (1+0+2*0+2*0+2*0+(-1):ℝ)=0 ∧ (1+0+0+2*0+2*0+(-1):ℝ)=0
    norm_num

theorem count_drift_correction (r d beta theta V : ℝ) (c : State) :
    countDrift r d beta theta V c = field r d beta theta c +
      ![0,0,2*r*c 2/V,0,0,-r*c 2/V,0] := by
  funext i
  fin_cases i <;> simp [countDrift,forwardRate,reverseRate,jumps,chemicalJump,
    Fin.sum_univ_succ,field,firstFlux,secondFlux,ProductiveRecovery.flux,free] <;> ring

theorem count_material_A (r d beta theta V : ℝ) (c : State) :
    materialA (countDrift r d beta theta V c) = 1-materialA c := by
  rw [count_drift_correction]
  have hm := material_A r d beta theta c
  simp [materialA,ProductiveRecovery.A,free] at hm ⊢
  linear_combination hm

theorem count_material_B (r d beta theta V : ℝ) (c : State) :
    materialB (countDrift r d beta theta V c) = 1-materialB c := by
  rw [count_drift_correction]
  have hm := material_B r d beta theta c
  simp [materialB,ProductiveRecovery.B,free] at hm ⊢
  linear_combination hm

theorem count_stock_correction (r d beta theta V : ℝ) (c : State) :
    stock (countDrift r d beta theta V c) = stock (field r d beta theta c)+r*c 2/(5*V) := by
  rw [count_drift_correction]
  simp [stock,ProductiveRecovery.Y,free]
  ring

/-- The normalized falling factorial matches the integer molecular propensity. -/
theorem falling_factorial_rate (N : ℕ) (V : ℝ) :
    ((N:ℝ)/V)^2-((N:ℝ)/V)/V = (N:ℝ)*((N:ℝ)-1)/V^2 := by ring

theorem falling_factorial_nonnegative (N : ℕ) : 0 ≤ (N:ℝ)*((N:ℝ)-1) := by
  cases N with
  | zero => norm_num
  | succ n =>
    have h : (0:ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    nlinarith
end
end RAF1519.Refinement
