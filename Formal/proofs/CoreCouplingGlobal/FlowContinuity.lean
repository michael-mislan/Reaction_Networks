import proofs.CoreCouplingGlobal.FlowDependence

namespace CoreCouplingGlobal
open CoreCouplingCAC

theorem bounded_region_of_initial_distance (x y : State) (S W : ℝ)
    (hS : x.A+x.B+2 ≤ S) (hW : x.z+(7/4:ℝ)*x.H+3 ≤ W)
    (hd : dist (encodeState y) (encodeState x) < 1) : InBoundedRegion S W y := by
  have hc : ∀ i : Fin 4, encodeState y i-encodeState x i ≤ 1 := by
    intro i
    have hh := dist_le_pi_dist (encodeState y) (encodeState x) i
    rw [Real.dist_eq] at hh
    have hs := le_abs_self (encodeState y i-encodeState x i)
    linarith
  have hA : y.A-x.A ≤ 1 := hc 0
  have hB : y.B-x.B ≤ 1 := hc 1
  have hz : y.z-x.z ≤ 1 := hc 2
  have hH : y.H-x.H ≤ 1 := hc 3
  exact ⟨by linarith,by linarith⟩

/-- Finite-time continuity in positive initial concentrations, with no boundedness
assumption supplied by the caller. -/
theorem positive_trajectories_continuous_initial_data (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) (t : ℝ) (ht : 0 ≤ t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℝ → State, IsPositiveTrajectory e Y →
      dist (encodeState (Y 0)) (encodeState (X 0)) < δ →
      dist (encodeState (Y t)) (encodeState (X t)) < ε := by
  let S := max 34 ((X 0).A+(X 0).B+2)
  let W := max ((7/2)*(S+76)) ((X 0).z+(7/4:ℝ)*(X 0).H+3)
  have hS : 34 ≤ S := le_max_left _ _
  have hW : (7/2)*(S+76) ≤ W := le_max_left _ _
  have hSx : (X 0).A+(X 0).B+2 ≤ S := le_max_right _ _
  have hWx : (X 0).z+(7/4:ℝ)*(X 0).H+3 ≤ W := le_max_right _ _
  have hX0 : InBoundedRegion S W (X 0) := ⟨by linarith,by linarith⟩
  obtain ⟨K,hK⟩ := bounded_initial_data_dependence e S W he hu hS hW
  have hExp : 0 < Real.exp (K*t) := Real.exp_pos _
  refine ⟨min 1 (ε/Real.exp (K*t)),lt_min (by norm_num) (div_pos hε hExp),?_⟩
  intro Y hY hdist
  have hdist1 : dist (encodeState (Y 0)) (encodeState (X 0)) < 1 :=
    lt_of_lt_of_le hdist (min_le_left _ _)
  have hY0 := bounded_region_of_initial_distance (X 0) (Y 0) S W hSx hWx hdist1
  have hbound := hK Y X hY hX hY0 hX0 t ht
  have hsmall := (lt_div_iff₀ hExp).1 (lt_of_lt_of_le hdist (min_le_right _ _))
  exact lt_of_le_of_lt hbound hsmall

theorem positiveFlow_continuous_initial_data (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (x : {s : State // s.Positive}) (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : {s : State // s.Positive},
      dist (encodeState y) (encodeState x) < δ →
      dist (encodeState (positiveFlow e he hu y t)) (encodeState (positiveFlow e he hu x t)) < ε := by
  obtain ⟨δ,hδ,hbound⟩ := positive_trajectories_continuous_initial_data e he hu
    (positiveFlow e he hu x) (positiveFlow_spec e he hu x).2 t ht ε hε
  refine ⟨δ,hδ,?_⟩
  intro y hdist
  apply hbound (positiveFlow e he hu y) (positiveFlow_spec e he hu y).2
  simpa only [(positiveFlow_spec e he hu y).1,(positiveFlow_spec e he hu x).1] using hdist

end CoreCouplingGlobal
