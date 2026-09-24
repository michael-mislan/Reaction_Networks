import proofs.RAF1519.Refinement.CountNetwork
import proofs.RAF1519.Refinement.GraphNoiseBounds

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def weightedCoordinate (w c : Fin 7 → ℝ) : ℝ := ∑ s, w s*c s

theorem materialA_weighted (c : State) : materialA c = weightedCoordinate weightA c := by
  simp [materialA,weightedCoordinate,weightA,free,ProductiveRecovery.A,Fin.sum_univ_succ]
  ring

theorem materialB_weighted (c : State) : materialB c = weightedCoordinate weightB c := by
  simp [materialB,weightedCoordinate,weightB,free,ProductiveRecovery.B,Fin.sum_univ_succ]
  ring

theorem weightedCoordinate_sub (w x y : Fin 7 → ℝ) :
    weightedCoordinate w (fun s => x s-y s) = weightedCoordinate w x-weightedCoordinate w y := by
  simp only [weightedCoordinate,mul_sub,Finset.sum_sub_distrib]

theorem weightedCoordinate_add (w x y : Fin 7 → ℝ) :
    weightedCoordinate w (fun s => x s+y s) = weightedCoordinate w x+weightedCoordinate w y := by
  simp only [weightedCoordinate,mul_add,Finset.sum_add_distrib]

theorem weightedCoordinate_diffusion {ι : Type*} [Fintype ι]
    (w : Fin 7 → ℝ) (k : ι → ι → ℝ) (c : ι → Fin 7 → ℝ) (i : ι) :
    weightedCoordinate w (fun s => graphDiffusion k (fun j => c j s) i) =
      graphDiffusion k (fun j => weightedCoordinate w (c j)) i := by
  unfold weightedCoordinate graphDiffusion
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem weightedCoordinate_noise (w x y : Fin 7 → ℝ) (ε : ℝ)
    (hw : ∀ s, 0 ≤ w s) (h : ∀ s, |x s-y s| ≤ ε) :
    |weightedCoordinate w x-weightedCoordinate w y| ≤ (∑ s, w s)*ε := by
  rw [← weightedCoordinate_sub,weightedCoordinate]
  calc
    _ ≤ ∑ s, |w s*(x s-y s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, w s*ε := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul,abs_of_nonneg (hw s)]
      exact mul_le_mul_of_nonneg_left (h s) (hw s)
    _ = _ := by rw [Finset.sum_mul]

theorem material_weight_bounds :
    (∀ s, 0 ≤ weightA s) ∧ (∀ s, 0 ≤ weightB s) ∧
      (∑ s, weightA s) = 9 ∧ (∑ s, weightB s) = 8 := by
  constructor
  · intro s; fin_cases s <;> norm_num [weightA]
  constructor
  · intro s; fin_cases s <;> norm_num [weightB]
  norm_num [weightA,weightB,Fin.sum_univ_succ]

theorem weightedCoordinate_right_derivative (w : Fin 7 → ℝ) (F : ℝ → Fin 7 → ℝ)
    (v : Fin 7 → ℝ) (t : ℝ)
    (h : ∀ s, HasDerivWithinAt (fun u => F u s) (v s) (Set.Ici t) t) :
    HasDerivWithinAt (fun u => weightedCoordinate w (F u)) (weightedCoordinate w v) (Set.Ici t) t :=
  HasDerivWithinAt.fun_sum (fun s _ => (h s).const_mul (w s))

end
end RAF1519.Refinement
