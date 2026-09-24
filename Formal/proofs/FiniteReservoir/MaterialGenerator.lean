import proofs.FiniteReservoir.FiniteModel

namespace FiniteReservoir
noncomputable section
open RandomViability.Binding
open scoped BigOperators

/-- Every function of the two resource moieties has unchanged generator.
The added reaction labels are retained; their contributions are zero. -/
theorem resource_generator (N : Counts) (V r alpha beta : ℝ)
    (f : ℝ → ℝ → ℝ) :
    generator N V r alpha beta (fun X => f (uCount X) (wCount X)) =
    literalGenerator N V (1/500000000) (1/10) r (fun X => f (uCount X) (wCount X)) := by
  have hz (j : Fin 2) : internalRate N V r alpha beta (.inr j) *
      (f (uCount (countNext N (drivenBase j))) (wCount (countNext N (drivenBase j))) -
        f (uCount N) (wCount N)) = 0 := by
    by_cases hj : internalRate N V r alpha beta (.inr j) = 0
    · simp [hj]
    · have hu := rated_linear_jump N V (if j=0 then alpha else beta) 1 0
        (drivenBase j) uUnits
      have hw := rated_linear_jump N V (if j=0 then alpha else beta) 1 0
        (drivenBase j) wUnits
      change internalRate N V r alpha beta (.inr j) *
        (uCount (countNext N (drivenBase j))-uCount N) = _ at hu
      change internalRate N V r alpha beta (.inr j) *
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
  simp only [internalRate] at hz
  simp only [generator,Fintype.sum_sum_type,internalRate,
    competitionNext,competitionBase,hz,Finset.sum_const_zero,add_zero,literalGenerator]

theorem resource_potential_generator (N : Counts) (V r alpha beta : ℝ) :
    generator N V r alpha beta (resourcePotential V)=
      literalGenerator N V (1/500000000) (1/10) r (resourcePotential V) := by
  have h := resource_generator N V r alpha beta (fun u w =>
    Real.exp ((1/100)*(u-(11/10)*V))+Real.exp ((-1/100)*(u-(9/10)*V))+
    Real.exp ((1/100)*(w-(11/10)*V))+Real.exp ((-1/100)*(w-(9/10)*V)))
  simpa only [resourcePotential,upperUnitPotential,lowerUnitPotential,unitObs,
    ↓reduceIte] using h

end
end FiniteReservoir
