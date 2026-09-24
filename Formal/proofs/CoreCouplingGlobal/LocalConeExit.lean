import proofs.CoreCouplingGlobal.PerturbedQuadratic
import proofs.CoreCouplingGlobal.ConeEscape

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem middle_unit_neighborhood_B_bounds (z H : ℝ) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (x : SaddleVector) (hx : dist x ![60/(z+2),z,H,0] < 1) : x 0 ∈ Icc (2:ℝ) 34 := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hB : 10 ≤ 60/(z+2) ∧ 60/(z+2) ≤ 20 := by
    constructor
    · apply (le_div_iff₀ (by positivity : 0 < z+2)).2
      linarith [hz.2]
    · apply (div_le_iff₀ (by positivity : 0 < z+2)).2
      linarith [hz.1]
  have hc := norm_le_pi_norm (x-![60/(z+2),z,H,0]) 0
  have hn : ‖x-![60/(z+2),z,H,0]‖ < 1 := by simpa only [dist_eq_norm] using hx
  have ha : |x 0-60/(z+2)| < 1 := lt_of_le_of_lt hc hn
  obtain ⟨hl,hu⟩ := abs_lt.mp ha
  exact ⟨by linarith [hB.1],by linarith [hB.2]⟩

/-- A negative perturbed quadratic difference between two literal positive
trajectories forces at least one trajectory to leave the certified neighborhood.
No global B-box or local dissipation assumption is left to the caller. -/
theorem middle_actual_exit_certificate (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ α η δ : ℝ, 0 < α ∧ 0 < η ∧ 0 < δ ∧
      perturbedSaddleQuadratic e z α
        ![-(60/(z+2))/(z+2),1,(16+4*z)/(20001/10000),0] < 0 ∧
      (∀ x y : SaddleVector, dist x ![60/(z+2),z,H,0] < δ →
        dist y ![60/(z+2),z,H,0] < δ →
        saddlePairing (perturbedGradient (saddleGradient e z).toContinuousLinearMap α (x-y))
          (responseCoordinateField e x-responseCoordinateField e y) ≤ -(η*‖x-y‖^2)) ∧
      ∀ X Y : ℝ → State, IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      perturbedSaddleQuadratic e z α (saddleCoordinates e (X 0)-saddleCoordinates e (Y 0)) < 0 →
      ∃ t : ℝ, 0 ≤ t ∧
        (δ ≤ dist (saddleCoordinates e (X t)) ![60/(z+2),z,H,0] ∨
         δ ≤ dist (saddleCoordinates e (Y t)) ![60/(z+2),z,H,0]) := by
  obtain ⟨α,η,δ0,hα,hη,hδ0,htangent,hpair⟩ := middle_perturbed_pair_certificate e z H he hu hz
  let δ := min δ0 1
  have hδ : 0 < δ := lt_min hδ0 (by norm_num)
  obtain ⟨M,hM,hQ⟩ := perturbedSaddleQuadratic_norm_bound e z α
  have hpair' : ∀ x y : SaddleVector, dist x ![60/(z+2),z,H,0] < δ →
      dist y ![60/(z+2),z,H,0] < δ →
      saddlePairing (perturbedGradient (saddleGradient e z).toContinuousLinearMap α (x-y))
        (responseCoordinateField e x-responseCoordinateField e y) ≤ -(η*‖x-y‖^2) := by
    intro x y hx hy
    exact hpair x y (lt_of_lt_of_le hx (min_le_left _ _)) (lt_of_lt_of_le hy (min_le_left _ _))
  refine ⟨α,η,δ,hα,hη,hδ,htangent,hpair',?_⟩
  intro X Y hX hY hstart
  by_contra hno
  push Not at hno
  let p : SaddleVector := ![60/(z+2),z,H,0]
  let v := fun t => saddleCoordinates e (X t)-saddleCoordinates e (Y t)
  let q := fun t => perturbedSaddleQuadratic e z α (v t)
  let N := fun t => ‖v t‖^2
  let dq := fun t => saddlePairing
    (perturbedGradient (saddleGradient e z).toContinuousLinearMap α (v t))
    (responseCoordinateField e (saddleCoordinates e (X t))-
      responseCoordinateField e (saddleCoordinates e (Y t)))
  have hstay : ∀ t, 0 ≤ t → dist (saddleCoordinates e (X t)) p < δ ∧
      dist (saddleCoordinates e (Y t)) p < δ := hno
  have hBX : ∀ t, 0 ≤ t → (X t).B ∈ Icc (2:ℝ) 34 := by
    intro t ht
    exact middle_unit_neighborhood_B_bounds z H hz (saddleCoordinates e (X t))
      (lt_of_lt_of_le (hstay t ht).1 (min_le_right _ _))
  have hBY : ∀ t, 0 ≤ t → (Y t).B ∈ Icc (2:ℝ) 34 := by
    intro t ht
    exact middle_unit_neighborhood_B_bounds z H hz (saddleCoordinates e (Y t))
      (lt_of_lt_of_le (hstay t ht).2 (min_le_right _ _))
  have hd : ∀ t, 0 ≤ t → HasDerivAt q (dq t) t := by
    intro t ht
    have hv := (saddleCoordinates_hasDerivAt e he hu X hX t ht (hBX t ht)).sub
      (saddleCoordinates_hasDerivAt e he hu Y hY t ht (hBY t ht))
    exact perturbedSaddleQuadratic_hasDerivAt e z α (by linarith [hz.1]) v _ t hv
  have hdec : ∀ t, 0 ≤ t → dq t ≤ -η*N t := by
    intro t ht
    have hh := hpair (saddleCoordinates e (X t)) (saddleCoordinates e (Y t))
      (lt_of_lt_of_le (hstay t ht).1 (min_le_left _ _))
      (lt_of_lt_of_le (hstay t ht).2 (min_le_left _ _))
    simpa only [neg_mul] using hh
  have hscale : ∀ t, 0 ≤ t → -M*N t ≤ q t := by
    intro t _ht
    have hh := (abs_le.mp (hQ (v t))).1
    dsimp [N,q]
    linarith only [hh]
  have hbounded : ∀ t, 0 ≤ t → -(M*(2*δ)^2) ≤ q t := by
    intro t ht
    have hn : ‖v t‖ < 2*δ := by
      have htri := dist_triangle (saddleCoordinates e (X t)) p (saddleCoordinates e (Y t))
      rw [dist_comm p (saddleCoordinates e (Y t))] at htri
      rw [dist_eq_norm] at htri
      change ‖v t‖ ≤ _ at htri
      linarith [(hstay t ht).1,(hstay t ht).2]
    have hn2 : N t ≤ (2*δ)^2 := by dsimp [N]; nlinarith [norm_nonneg (v t)]
    have hm := mul_le_mul_of_nonneg_left hn2 hM.le
    have hs := hscale t ht
    linarith only [hm,hs]
  exact negative_quadratic_not_globally_bounded q dq N M η (M*(2*δ)^2)
    hM hη (by positivity) hd (fun t _ => sq_nonneg ‖v t‖) hscale hdec hbounded hstart

theorem middle_actual_pair_forces_exit (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ α δ : ℝ, 0 < α ∧ 0 < δ ∧
      perturbedSaddleQuadratic e z α
        ![-(60/(z+2))/(z+2),1,(16+4*z)/(20001/10000),0] < 0 ∧
      ∀ X Y : ℝ → State, IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      perturbedSaddleQuadratic e z α (saddleCoordinates e (X 0)-saddleCoordinates e (Y 0)) < 0 →
      ∃ t : ℝ, 0 ≤ t ∧
        (δ ≤ dist (saddleCoordinates e (X t)) ![60/(z+2),z,H,0] ∨
         δ ≤ dist (saddleCoordinates e (Y t)) ![60/(z+2),z,H,0]) := by
  obtain ⟨α,η,δ,hα,_hη,hδ,htangent,_hpair,hexit⟩ := middle_actual_exit_certificate e z H he hu hz
  exact ⟨α,δ,hα,hδ,htangent,hexit⟩

/-- If a reference trajectory remains nearby, a negative-cone perturbation
must itself leave. This is the form needed after restarting a middle-basin orbit. -/
theorem middle_reference_forces_perturbation_exit (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ α δ : ℝ, 0 < α ∧ 0 < δ ∧
      perturbedSaddleQuadratic e z α
        ![-(60/(z+2))/(z+2),1,(16+4*z)/(20001/10000),0] < 0 ∧
      ∀ X Y : ℝ → State, IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      (∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) ![60/(z+2),z,H,0] < δ) →
      perturbedSaddleQuadratic e z α (saddleCoordinates e (X 0)-saddleCoordinates e (Y 0)) < 0 →
      ∃ t : ℝ, 0 ≤ t ∧ δ ≤ dist (saddleCoordinates e (Y t)) ![60/(z+2),z,H,0] := by
  obtain ⟨α,δ,hα,hδ,hnegative,hexit⟩ := middle_actual_pair_forces_exit e z H he hu hz
  refine ⟨α,δ,hα,hδ,hnegative,?_⟩
  intro X Y hX hY hstay hstart
  obtain ⟨t,ht,hcases⟩ := hexit X Y hX hY hstart
  refine ⟨t,ht,?_⟩
  rcases hcases with hbad | hgood
  · exact False.elim (not_le_of_gt (hstay t ht) hbad)
  · exact hgood

end CoreCouplingGlobal
