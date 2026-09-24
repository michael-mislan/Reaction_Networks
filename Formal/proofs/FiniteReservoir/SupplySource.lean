import proofs.FiniteReservoir.RateBounds
import proofs.FiniteCopyReactor.SupplySource

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

theorem foodU_intensity (N : Counts) (V r alpha beta : ℝ) :
    (∑ j,internalRate N V r alpha beta j*supplyMark .foodU j)=V := by
  simp [Fintype.sum_sum_type,internalRate,supplyMark,countRate]

theorem foodW_intensity (N : Counts) (V r alpha beta : ℝ) :
    (∑ j,internalRate N V r alpha beta j*supplyMark .foodW j)=V := by
  simp [Fintype.sum_sum_type,internalRate,supplyMark,countRate]

theorem gross_intensity (N : Counts) (V r alpha beta : ℝ) :
    (∑ j,internalRate N V r alpha beta j*supplyMark .gross j)=
      alpha*(N 2)+beta*(N 0)*(N 1)/V := by
  norm_num [Fintype.sum_sum_type,supplyMark,Fin.sum_univ_two,internalRate_forward,internalRate_reverse]

theorem supply_intensity_bound (k : SupplyKind) (N : Counts) (V : ℕ) (r alpha beta : ℝ)
    (hV : 0 < (V:ℝ)) (hbox : RateBox alpha beta) (hc : resourceGood N V) :
    (∑ j,internalRate N V r alpha beta j*supplyMark k j) ≤ supplyRateCap k*(V:ℝ) := by
  cases k with
  | foodU => rw [foodU_intensity]; simp [supplyRateCap]
  | foodW => rw [foodW_intensity]; simp [supplyRateCap]
  | gross =>
    rw [gross_intensity]
    exact (count_gross_bound N V alpha beta hV hbox hc).le

end
end FiniteReservoir
