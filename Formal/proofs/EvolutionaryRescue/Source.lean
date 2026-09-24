import proofs.PersisterMemory.ControlSource

namespace EvolutionaryRescue
open PersisterMemory.Source
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

def mutationReward : Fin 6 → ℚ := ![1/10,1/10,1/10,2/5,1/10,2/5]

def offspringJ (mu y : ℚ) (x : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  (1-mu)*daughterPair x i+mu*y*daughter x i

def offspringI (mu y : ℚ) (x : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  (1-mu)*(daughter x i)^2+mu*y*daughter x i

def molecularMean (e c mu g : ℚ) (f : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  molecular e f i + ((2-mu)*daughter f i+mu*g-f i)/10-(death i+c)*f i

def residualJ (e c mu y : ℚ) (x : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  molecular e x i+(death i+c)*(1-x i)+(offspringJ mu y x i-x i)/10

def residualI (e c mu y : ℚ) (x : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  molecular e x i+(death i+c)*(1-x i)+(offspringI mu y x i-x i)/10

theorem offspring_normalized (mu : ℚ) (i : Fin 6) :
    offspringJ mu 1 (fun _ => 1) i=1 ∧ offspringI mu 1 (fun _ => 1) i=1 := by
  simp [offspringJ, offspringI, daughter_normalized, daughter_pair_normalized]

theorem joint_augmented_linearization (e c mu t g : ℚ) (f : Fin 6 → ℚ) (i : Fin 6) :
    residualJ e c mu (1-t*g) (fun j => 1-t*f j) i =
      -t*molecularMean e c mu g f i +
      t^2*((1-mu)*daughterPair f i+mu*g*daughter f i)/10 := by
  fin_cases i <;> simp [residualJ, offspringJ, molecularMean, molecular, daughter,
    daughterPair, death] <;> ring

theorem independent_augmented_linearization (e c mu t g : ℚ) (f : Fin 6 → ℚ) (i : Fin 6) :
    residualI e c mu (1-t*g) (fun j => 1-t*f j) i =
      -t*molecularMean e c mu g f i +
      t^2*((1-mu)*(daughter f i)^2+mu*g*daughter f i)/10 := by
  fin_cases i <;> simp [residualI, offspringI, molecularMean, molecular, daughter,
    death] <;> ring

theorem mutation_domain (eps : ℚ) (he : 0≤eps) (he' : eps≤5/2) (i : Fin 6) :
    0≤eps*mutationReward i ∧ eps*mutationReward i≤1 := by
  fin_cases i <;> norm_num [mutationReward] <;> constructor <;> linarith

theorem continuation_contracts (i : Fin 6) :
    meanAction (3/10) extinctionWeight i ≤ -(9/100)*extinctionWeight i :=
  uniform_extinction_certificate (3/10) (by norm_num) (by norm_num) i

theorem mutant_equilibrium :
    (1/50:ℚ)*(1-1/5)+(1/10)*((1/5)^2-1/5)=0 := by norm_num

end EvolutionaryRescue
