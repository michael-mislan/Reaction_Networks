import Mathlib

namespace TinyProgrammableChemicalFactory

abbrev Counts := Fin 7 → ℕ
abbrev Channel := Fin 14

/-- Species order X,Y,F,PX,PY,H,W; forward and reverse channels are adjacent. -/
def reactants : Channel → Counts := ![
  ![1,0,1,0,0,0,0], ![2,0,0,0,0,0,0],
  ![0,1,1,0,0,0,0], ![0,2,0,0,0,0,0],
  ![1,0,1,0,0,0,0], ![1,0,0,1,0,0,0],
  ![0,1,1,0,0,0,0], ![0,1,0,0,1,0,0],
  ![1,0,0,0,0,0,0], ![0,1,0,0,0,0,0],
  ![2,1,0,0,0,1,0], ![3,0,0,0,0,0,1],
  ![1,2,0,0,0,1,0], ![0,3,0,0,0,0,1]]

def products : Channel → Counts := ![
  ![2,0,0,0,0,0,0], ![1,0,1,0,0,0,0],
  ![0,2,0,0,0,0,0], ![0,1,1,0,0,0,0],
  ![1,0,0,1,0,0,0], ![1,0,1,0,0,0,0],
  ![0,1,0,0,1,0,0], ![0,1,1,0,0,0,0],
  ![0,1,0,0,0,0,0], ![1,0,0,0,0,0,0],
  ![3,0,0,0,0,0,1], ![2,1,0,0,0,1,0],
  ![0,3,0,0,0,0,1], ![1,2,0,0,0,1,0]]

def enabled (z : Counts) (r : Channel) : Prop := ∀ i, reactants r i ≤ z i
def update (z : Counts) (r : Channel) : Counts := fun i => z i-reactants r i+products r i
def coreMass (z : Counts) : ℕ := z 0+z 1+z 2+z 3+z 4
def fuelMass (z : Counts) : ℕ := z 5+z 6

noncomputable def rate (γ β ε : ℝ) (z : Counts) : Channel → ℝ := ![
  (z 0*z 2 : ℕ), (z 0*(z 0-1) : ℕ)/100,
  (z 1*z 2 : ℕ), (z 1*(z 1-1) : ℕ)/100,
  (z 0*z 2 : ℕ), (z 0*z 3 : ℕ)/100,
  (z 1*z 2 : ℕ), (z 1*z 4 : ℕ)/100,
  ε*z 0, ε*z 1,
  γ*(z 5*z 0*(z 0-1)*z 1 : ℕ), β*(z 6*z 0*(z 0-1)*(z 0-2) : ℕ),
  γ*(z 5*z 1*(z 1-1)*z 0 : ℕ), β*(z 6*z 1*(z 1-1)*(z 1-2) : ℕ)]

def restartX (z : Counts) : Prop :=
  coreMass z=80 ∧ z 0≥8 ∧ z 1≤1 ∧ z 3=0 ∧ z 4=0 ∧ z 5=1 ∧ z 6=0

theorem rate_nonneg (γ β ε : ℝ) (hγ : 0≤γ) (hβ : 0≤β) (hε : 0≤ε)
    (z : Counts) (r : Channel) : 0≤rate γ β ε z r := by
  fin_cases r <;> norm_num [rate] <;> positivity

theorem opposing_majority_vanishes (γ β ε : ℝ) (z : Counts) (hy : z 1≤1) :
    rate γ β ε z 12=0 := by
  have h : z 1-1=0 := by omega
  simp [rate,h]

theorem repair_rate (γ β ε : ℝ) (z : Counts) (hy : z 1=1) (hh : z 5=1) :
    rate γ β ε z 10=γ*(z 0*(z 0-1) : ℕ) := by
  simp [rate,hy,hh]

theorem repair_factor_lower (x : ℕ) (hx : 8≤x) : 56≤x*(x-1) := by
  have h : 7≤x-1 := by omega
  nlinarith

end TinyProgrammableChemicalFactory
