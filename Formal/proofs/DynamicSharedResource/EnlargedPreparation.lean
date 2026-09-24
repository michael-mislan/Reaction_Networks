import proofs.DynamicSharedResource.FastOutputs

namespace DynamicSharedResource.Certificate
noncomputable section
open scoped BigOperators

def enlargedEpsilon : ℝ := 1/2000000
def EnlargedPrepared (u : State) : Prop := ∀ i, |u i-preparation i| ≤ enlargedEpsilon

theorem enlarged_preparation_mem : EnlargedPrepared preparation := by
  intro i
  norm_num [enlargedEpsilon]

theorem enlarged_contains_ball :
    Metric.ball preparation enlargedEpsilon ⊆ {u | EnlargedPrepared u} := by
  intro u hu i
  have h := dist_le_pi_dist u preparation i
  rw [Real.dist_eq] at h
  exact h.trans (le_of_lt hu)

theorem enlarged_prepared_in_recovery (u : State) (hu : EnlargedPrepared u) :
    InRect recoveryR (coordinates u) := by
  have he : coordinates u = seed+inverse.mulVec (u-preparation) := by
    have hh : u-center = (preparation-center)+(u-preparation) := by abel
    unfold coordinates
    rw [hh,Matrix.mulVec_add]
    have hc := coordinates_reconstruct seed
    change inverse.mulVec (preparation-center)=seed at hc
    rw [hc]
  intro i
  have hd := abs_mulVec_le inverse (u-preparation) enlargedEpsilon hu i
  have hc := enlarged_inclusion_check i
  rw [he,Pi.add_apply]
  exact (abs_add_le _ _).trans (by dsimp [enlargedEpsilon] at hd; linarith)

theorem enlarged_prepared_physical (u : State) (hu : EnlargedPrepared u) : Physical u := by
  have hr := enlarged_prepared_in_recovery u hu
  have hp := outer_physical (coordinates u) (fun i => (hr i).trans (rect_radii i).2.2)
  simpa only [reconstruct_coordinates] using hp

set_option maxHeartbeats 4000000 in
theorem preparation_deficiency_arithmetic :
    0 ≤ 101/200-preparation 4+enlargedEpsilon ∧
    0 ≤ preparation 7-enlargedEpsilon ∧
    (21/10:ℝ)*(101/200-preparation 4+enlargedEpsilon)*(preparation 7+enlargedEpsilon) < 4 := by
  norm_num [enlargedEpsilon,preparation,reconstruct,seed,center,basis,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals simp
  all_goals norm_num

theorem enlarged_prepared_deficient (u : State) (hu : EnlargedPrepared u) : HT u < 4 := by
  have h4 := abs_le.mp (hu 4)
  have h7 := abs_le.mp (hu 7)
  have h := preparation_deficiency_arithmetic
  have hy : y u ≤ 101/200-preparation 4+enlargedEpsilon := by dsimp [y]; linarith
  have hv : u 7 ≤ preparation 7+enlargedEpsilon := by linarith
  have hp := mul_le_mul hy hv (by linarith [h.2.1] : 0 ≤ u 7) h.1
  dsimp [HT]
  nlinarith [h.2.2]

theorem old_prepared_enlarged (u : State) (hu : Prepared u) : EnlargedPrepared u := by
  intro i
  exact (hu i).trans (by norm_num [enlargedEpsilon])

end
end DynamicSharedResource.Certificate
