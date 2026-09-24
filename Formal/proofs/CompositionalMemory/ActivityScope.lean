import proofs.HeritableCompositions.ActivityObstruction
import proofs.CompositionalMemory.SourceBirthGeometry

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC HeritableCompositions Set

theorem source_shifted_H_negative (z : ℝ) (hz : 0 ≤ z) (hz3 : z ≤ 3)
    (hs : Stationary sourceRates (lift sourceRates z)) :
    (∑ r, densityRates (1/100000) 0 (pointOfState (lift sourceRates z)+activityDisplacement) r*markH r) < 0 := by
  have hstat := hs.2.2.2
  change 16*z+2*z^2-(2+1/10000)*reducedH sourceRates z=0 at hstat
  have hh := shifted_H_current_negative z (reducedH sourceRates z) hz hz3 hstat
  rw [activity_H_formula]
  simpa [pointOfState,lift,activityDisplacement,Matrix.cons_val_two,Matrix.cons_val_three,sub_eq_add_neg,neg_div] using hh

theorem low_growing_H_counterexample (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000:ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) :
    ∃ x : Point, (∀ i, 0 < x i) ∧
      lowEnergy (x-pointOfState (lift sourceRates z)) < 4*innerEnergy ∧
      (∑ r, densityRates (1/100000) 0 x r*markH r) < 0 := by
  have hb := low_source_box z hz
  refine ⟨pointOfState (lift sourceRates z)+activityDisplacement,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [pointOfState,lift,activityDisplacement,Matrix.cons_val_two,Matrix.cons_val_three] <;>
      linarith only [hb.1.1,hb.2.1.1,hb.2.2.1,hz.1]
  · have he : pointOfState (lift sourceRates z)+activityDisplacement-pointOfState (lift sourceRates z)=activityDisplacement := by abel
    rw [he]
    exact activity_displacement_inside.1
  · exact source_shifted_H_negative z (by linarith [hz.1]) (by linarith [hz.2]) hs

theorem high_growing_H_counterexample (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000:ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) :
    ∃ x : Point, (∀ i, 0 < x i) ∧
      highEnergy (x-pointOfState (lift sourceRates z)) < 4*innerEnergy ∧
      (∑ r, densityRates (1/100000) 0 x r*markH r) < 0 := by
  have hb := high_source_box z hz
  refine ⟨pointOfState (lift sourceRates z)+activityDisplacement,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [pointOfState,lift,activityDisplacement,Matrix.cons_val_two,Matrix.cons_val_three] <;>
      linarith only [hb.1.1,hb.2.1.1,hb.2.2.1,hz.1]
  · have he : pointOfState (lift sourceRates z)+activityDisplacement-pointOfState (lift sourceRates z)=activityDisplacement := by abel
    rw [he]
    exact activity_displacement_inside.2
  · exact source_shifted_H_negative z (by linarith [hz.1]) (by linarith [hz.2]) hs

end CompositionalMemory
