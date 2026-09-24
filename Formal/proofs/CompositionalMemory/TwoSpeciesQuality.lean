import proofs.CompositionalMemory.TwoSpeciesDissipation
import proofs.CompositionalMemory.TwoSpeciesReactions

namespace CompositionalMemory

theorem two_center_norm (b : Bool) : ‖twoCenter b‖ ≤ 54 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro a
  fin_cases a <;> cases b <;> norm_num [twoCenter]

theorem two_well_radius (b : Bool) (u : TwoPoint)
    (he : twoQ b (u-twoCenter b) (u-twoCenter b) < 1/100000000) :
    ‖u-twoCenter b‖ ≤ 1/10000 := by
  have hc := twoQ_coercive b (u-twoCenter b)
  nlinarith only [hc,he,norm_nonneg (u-twoCenter b)]

theorem two_well_growth_bounds (b : Bool) (u : TwoPoint)
    (he : twoQ b (u-twoCenter b) (u-twoCenter b) < 1/100000000) :
    1/2 ≤ u 0 ∧ u 0 ≤ 4 := by
  have h := (two_coordinate_abs_le (u-twoCenter b) 0).trans (two_well_radius b u he)
  have hh := abs_le.mp h
  cases b <;> simp only [twoCenter,Bool.false_eq_true,if_false,if_true,Pi.sub_apply] at hh <;>
    norm_num at hh <;> constructor <;> linarith only [hh.1,hh.2]

/-- All primitive local hypotheses for the common uniform theorem. -/
theorem two_module_quality (b : Bool) (u : TwoPoint)
    (he : twoQ b (u-twoCenter b) (u-twoCenter b) < 1/100000000) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1/10000 ∧ ‖u-twoCenter b‖ ≤ r ∧ ‖u‖ ≤ 55 ∧
      (∀ a, u a ≤ 55) ∧
      (∀ j, |twoQ b (u-twoCenter b) (twoStoich j)| ≤ 100000*r) ∧
      (∀ j, |twoQ b (twoStoich j) (twoStoich j)| ≤ 200000) ∧
      2*twoQ b (u-twoCenter b)
        (∑ j, (twoCoeff j*(∏ a, (u a)^(twoConsume j a))) • twoStoich j) ≤ -200*r^2 ∧
      twoQ b (u-twoCenter b) (u-twoCenter b) ≤ 50000*r^2 := by
  let y := u-twoCenter b
  have hr : ‖y‖ ≤ 1/10000 := two_well_radius b u he
  have hu : ‖u‖ ≤ 55 := by
    have hh := norm_add_le y (twoCenter b)
    have hy : y+twoCenter b=u := sub_add_cancel _ _
    rw [hy] at hh
    linarith only [hh,hr,two_center_norm b]
  refine ⟨‖y‖,norm_nonneg y,hr,le_rfl,hu,?_,?_,?_,?_,?_⟩
  · intro a
    exact (le_abs_self (u a)).trans ((two_coordinate_abs_le u a).trans hu)
  · intro j
    have hh := twoQ_operator b y (twoStoich j)
    have hj := mul_le_mul_of_nonneg_left (two_stoich_norm j) (show 0 ≤ 50000*‖y‖ by positivity)
    nlinarith only [hh,hj]
  · intro j
    have hh := twoQ_operator b (twoStoich j) (twoStoich j)
    have hj := (sq_le_sq₀ (norm_nonneg (twoStoich j)) (by norm_num : (0:ℝ) ≤ 2)).mpr (two_stoich_norm j)
    nlinarith only [hh,hj]
  · rw [two_mass_action_field]
    have hy : twoCenter b+y=u := by dsimp [y]; abel
    have hh := two_local_dissipation b y hr
    rw [hy] at hh
    exact hh
  · have hh := twoQ_operator b y y
    nlinarith only [le_abs_self (twoQ b y y),hh]

theorem two_well_signed_readout (b : Bool) (u : TwoPoint)
    (he : twoQ b (u-twoCenter b) (u-twoCenter b) < 1/100000000) :
    if b then 0 < u 1-12*u 0 else u 1-12*u 0 < 0 := by
  have h₀ := abs_le.mp ((two_coordinate_abs_le (u-twoCenter b) 0).trans (two_well_radius b u he))
  have h₁ := abs_le.mp ((two_coordinate_abs_le (u-twoCenter b) 1).trans (two_well_radius b u he))
  cases b <;> simp only [twoCenter,Bool.false_eq_true,if_false,if_true,Pi.sub_apply] at h₀ h₁ ⊢ <;>
    norm_num at h₀ h₁ <;> linarith only [h₀.1,h₀.2,h₁.1,h₁.2]

end CompositionalMemory
