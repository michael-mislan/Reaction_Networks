import proofs.DynamicSharedResource.RectangularSource
import proofs.DynamicSharedResource.PhysicalService

namespace DynamicSharedResource.Certificate
noncomputable section
open scoped BigOperators

def recoveryR : State := ![9/10,417/500,7/10,7/10,7/10,7/10,7/10,7/10]
def serviceR : State := ![9/10,7/10,7/10,7/10,7/10,7/10,7/10,7/10]
def rectVelocity : State := ![0,-67/2,0,0,0,0,0,0]
def fastDeadline : ℝ := 1/250
def rectWidth (q : State) (i : Fin 8) : ℝ := ∑ j, |basis i j| *q j

theorem rect_radii (i : Fin 8) :
    0 < serviceR i ∧ serviceR i ≤ recoveryR i ∧ recoveryR i ≤ 1 := by
  fin_cases i <;> norm_num [serviceR,recoveryR]

theorem rect_velocity (i : Fin 8) : rectVelocity i=250*(serviceR i-recoveryR i) := by
  fin_cases i <;> norm_num [rectVelocity,serviceR,recoveryR]

theorem rect_velocity_nonpos (i : Fin 8) : rectVelocity i ≤ 0 := by
  fin_cases i <;> norm_num [rectVelocity]

set_option maxHeartbeats 8000000 in
theorem recovery_face_check (i : Fin 8) : faceBudget recoveryR i < rectVelocity i := by
  fin_cases i <;>
    norm_num [faceBudget,recoveryR,rectVelocity,A,b,nb,Finset.sum_erase_eq_sub,Fin.sum_univ_succ]

set_option maxHeartbeats 8000000 in
theorem service_face_check (i : Fin 8) : faceBudget serviceR i < rectVelocity i := by
  fin_cases i <;>
    norm_num [faceBudget,serviceR,rectVelocity,A,b,nb,Finset.sum_erase_eq_sub,Fin.sum_univ_succ]

set_option maxHeartbeats 4000000 in
theorem enlarged_inclusion_check (i : Fin 8) :
    |seed i|+(∑ j, |inverse i j|)*(1/2000000:ℝ) < recoveryR i := by
  fin_cases i <;> norm_num [seed,inverse,recoveryR,Fin.sum_univ_succ]

end
end DynamicSharedResource.Certificate
