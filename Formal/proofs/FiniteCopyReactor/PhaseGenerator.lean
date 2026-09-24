import proofs.FiniteCopyReactor.MaterialModel

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def coordinateGenerator (N : Counts) (V r d : ℝ) (i : Fin 6) : ℝ :=
  competitionGenerator N V (1/500000000) (1/10) r d (fun X => (X i:ℝ))

theorem coordinate_generator_stoich (N : Counts) (V r d : ℝ) (i : Fin 6) :
    coordinateGenerator N V r d i = ∑ j,competitionRate N V (1/500000000) (1/10) r d j *
      ((products (competitionBase j) i:ℝ)-(reactants (competitionBase j) i:ℝ)) := by
  unfold coordinateGenerator competitionGenerator
  apply Finset.sum_congr rfl
  intro j _
  simpa using competition_rated_linear_jump N V (1/500000000) (1/10) r d j
    (fun k => if k=i then 1 else 0)

theorem phase_generator_expansion (N : Counts) (V r d : ℝ) :
    coordinateGenerator N V r d 2 =
      (1/500000000+d/8000000000)*(N 0)*(N 1)/V-
      (1+1/5000000000+d)*(N 2)-20*(N 2)*(N 0)/V+20*(N 3)+
      2*r*(N 5)-2*r*(N 2*(N 2-1):ℕ)/V ∧
    coordinateGenerator N V r d 3 =
      20*(N 2)*(N 0)/V-21*(N 3)-20*(N 3)*(N 1)/V+20*(N 4) ∧
    coordinateGenerator N V r d 4 =
      20*(N 3)*(N 1)/V-41*(N 4)+2*(N 5) ∧
    coordinateGenerator N V r d 5 =
      20*(N 4)-(3+r)*(N 5)+r*(N 2*(N 2-1):ℕ)/V := by
  simp only [coordinate_generator_stoich,Fintype.sum_sum_type,competitionRate,competitionBase]
  norm_num [Fin.sum_univ_succ,countRate,products,reactants,drivenRate_zero,drivenRate_one,drivenBase]
  simp only [show (![0,0,1,0,0,0] : Fin 6 → ℕ) 2=1 by decide,
    show (![1,0,1,0,0,0] : Fin 6 → ℕ) 2=1 by decide,
    show (![0,0,2,0,0,0] : Fin 6 → ℕ) 2=2 by decide,
    show (![0,0,0,1,0,0] : Fin 6 → ℕ) 3=1 by decide,
    show (![0,1,0,1,0,0] : Fin 6 → ℕ) 3=1 by decide,
    show (![0,0,0,0,1,0] : Fin 6 → ℕ) 4=1 by decide,
    show (![0,0,0,0,0,1] : Fin 6 → ℕ) 5=1 by decide]
  norm_num
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end
end FiniteCopyReactor
