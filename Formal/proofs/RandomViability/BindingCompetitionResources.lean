import proofs.RandomViability.BindingCompetitionModel
import proofs.RandomViability.BindingResourceProbability

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

/-- Every function of the two resource moieties has unchanged generator.
The added reaction labels are retained; their contributions are zero. -/
theorem competition_resource_generator (N : Counts) (V eps k r delta : ℝ)
    (f : ℝ → ℝ → ℝ) :
    competitionGenerator N V eps k r delta (fun X => f (uCount X) (wCount X)) =
    literalGenerator N V eps k r (fun X => f (uCount X) (wCount X)) := by
  have hz (j : Fin 2) : drivenRate N V eps delta j *
      (f (uCount (countNext N (drivenBase j))) (wCount (countNext N (drivenBase j))) -
        f (uCount N) (wCount N)) = 0 := by
    by_cases hj : drivenRate N V eps delta j = 0
    · simp [hj]
    · have hu := rated_linear_jump N V (if j=0 then delta else delta*eps/16) 1 0
        (drivenBase j) uUnits
      have hw := rated_linear_jump N V (if j=0 then delta else delta*eps/16) 1 0
        (drivenBase j) wUnits
      change drivenRate N V eps delta j *
        (uCount (countNext N (drivenBase j))-uCount N) = _ at hu
      change drivenRate N V eps delta j *
        (wCount (countNext N (drivenBase j))-wCount N) = _ at hw
      rw [u_units_stoich] at hu
      rw [w_units_stoich] at hw
      have hju : uUnitJump (drivenBase j) = 0 := by
        fin_cases j <;> norm_num [drivenBase,uUnitJump]
      have hjw : wUnitJump (drivenBase j) = 0 := by
        fin_cases j <;> norm_num [drivenBase,wUnitJump]
      rw [hju,mul_zero] at hu
      rw [hjw,mul_zero] at hw
      have hue := sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left hj)
      have hwe := sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left hj)
      rw [hue,hwe,sub_self,mul_zero]
  simp only [competitionGenerator,Fintype.sum_sum_type,competitionRate,
    competitionNext,competitionBase,hz,Finset.sum_const_zero,add_zero,literalGenerator]

end
end RandomViability.Binding
