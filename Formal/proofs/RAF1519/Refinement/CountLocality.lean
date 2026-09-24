import proofs.RAF1519.Refinement.CountLaw
import proofs.RAF1519.Refinement.CountRateBinding

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 20000

theorem atNode_rate {n : ℕ} (i : Fin n) (R : Reaction (Fin 7)) (V : ℝ)
    (N : MolecularState n) : (atNode i R).rate V N = R.rate V (fun s => N (i,s)) := by
  unfold Reaction.rate
  congr 1
  rw [Fintype.prod_prod_type,Finset.prod_eq_single i]
  · simp [atNode]
  · intro j _ hji
    simp [atNode,hji]
  · simp

theorem single_reactant_rate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (p : ι → ℕ) (c V : ℝ) (hV : V ≠ 0) (N : ι → ℕ) :
    (Reaction.mk (Pi.single i 1) p c).rate V N = c*(N i:ℝ) := by
  unfold Reaction.rate
  rw [Finset.prod_eq_single i]
  · simp only [Pi.single_eq_same,Nat.descFactorial_one,pow_one]
    field_simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem local_wash_rate (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) (i : Fin 7) :
    (localReaction r d (.inr (.inr i))).rate V N = (N i:ℝ) := by
  simpa only [one_mul] using single_reactant_rate i (0 : Fin 7 → ℕ) 1 V hV N

theorem local_food_rate (r d V : ℝ) (N : Fin 7 → ℕ) (i : Fin 2) :
    (localReaction r d (.inr (.inl i))).rate V N = V := by
  simp [localReaction,Reaction.rate]

theorem exchange_rate {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (N : MolecularState n) (i j : Fin n) (s : Fin 7) :
    molecularRate r d k V N (.inr (i,j,s)) = k i j*(N (i,s):ℝ) := by
  exact single_reactant_rate (i,s) (Pi.single (j,s) 1) (k i j) V hV N

end
end RAF1519.Refinement
