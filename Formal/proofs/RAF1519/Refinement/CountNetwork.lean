import proofs.RAF1519.Refinement.ReactionLaw
import proofs.RAF1519.Refinement.CountSource

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def chemicalInput (j : Fin 7) : Fin 7 → ℕ := match j.val with
  | 0 => ![1,1,0,0,0,0,0]
  | 1 => ![1,0,1,0,0,0,0]
  | 2 => ![0,1,0,1,0,0,0]
  | 3 => ![0,0,0,0,1,0,0]
  | 4 => ![0,0,0,0,0,1,0]
  | 5 => ![0,0,1,0,0,0,0]
  | _ => ![0,0,0,0,0,0,1]

def chemicalOutput (j : Fin 7) : Fin 7 → ℕ := match j.val with
  | 0 => ![0,0,1,0,0,0,0]
  | 1 => ![0,0,0,1,0,0,0]
  | 2 => ![0,0,0,0,1,0,0]
  | 3 => ![0,0,0,0,0,1,0]
  | 4 => ![0,0,2,0,0,0,0]
  | 5 => ![0,0,0,0,0,0,1]
  | _ => ![1,1,0,0,0,0,0]

def forwardCoefficient (r d : ℝ) (j : Fin 7) : ℝ := match j.val with
  | 0 => 1/500000000
  | 1 => 20
  | 2 => 20
  | 3 => 20
  | 4 => r
  | 5 => d*(101/100)
  | _ => 100*d

def reverseCoefficient (r d : ℝ) (j : Fin 7) : ℝ := match j.val with
  | 0 => 1/5000000000
  | 1 => 20
  | 2 => 20
  | 3 => 2
  | 4 => r
  | 5 => d
  | _ => d*(101/8000000000)

/-- Fourteen chemical directions, two food feeds, seven washouts. -/
abbrev LocalChannel := (Fin 7 × Bool) ⊕ (Fin 2 ⊕ Fin 7)

def localReaction (r d : ℝ) : LocalChannel → Reaction (Fin 7)
  | .inl (j,false) => ⟨chemicalInput j,chemicalOutput j,forwardCoefficient r d j⟩
  | .inl (j,true) => ⟨chemicalOutput j,chemicalInput j,reverseCoefficient r d j⟩
  | .inr (.inl i) => ⟨0,Pi.single (Fin.castLE (by omega) i) 1,1⟩
  | .inr (.inr i) => ⟨Pi.single i 1,0,1⟩

theorem local_channel_card : Fintype.card LocalChannel = 23 := by decide

theorem local_coefficient_nonnegative (r d : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (j : LocalChannel) : 0 ≤ (localReaction r d j).coefficient := by
  rcases j with ⟨j,b⟩ | (i | i)
  · cases b <;> fin_cases j <;>
      simp only [localReaction,forwardCoefficient,reverseCoefficient] <;> positivity
  · norm_num [localReaction]
  · norm_num [localReaction]

theorem local_rate_nonnegative (r d V : ℝ) (hr : 0 ≤ r) (hd : 0 ≤ d) (hV : 0 ≤ V)
    (N : Fin 7 → ℕ) (j : LocalChannel) : 0 ≤ (localReaction r d j).rate V N :=
  Reaction.rate_nonnegative _ V hV (local_coefficient_nonnegative r d hr hd j) N

def weightA : Fin 7 → ℝ := ![1,0,1,2,2,2,1]
def weightB : Fin 7 → ℝ := ![0,1,1,1,2,2,1]

theorem chemical_input_output (j i : Fin 7) :
    (chemicalOutput j i:ℝ)-(chemicalInput j i:ℝ) = jumps j i := by
  fin_cases j <;> fin_cases i <;> norm_num [chemicalInput,chemicalOutput,jumps,chemicalJump]

theorem weighted_chemical_zero (j : Fin 7) :
    (∑ i, weightA i*((chemicalOutput j i:ℝ)-(chemicalInput j i:ℝ))) = 0 ∧
    (∑ i, weightB i*((chemicalOutput j i:ℝ)-(chemicalInput j i:ℝ))) = 0 := by
  fin_cases j <;> norm_num [chemicalInput,chemicalOutput,weightA,weightB,Fin.sum_univ_succ]

end
end RAF1519.Refinement
