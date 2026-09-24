import proofs.CoreCouplingGlobal.NonlinearQuadratic

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

noncomputable def saddleCoordinates (e : ℝ) (s : State) : SaddleVector :=
  ![s.B,s.z,s.H,s.A+s.B-responseTotal e s.B]

theorem saddleCoordinates_hasDerivAt (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) (t : ℝ) (ht : 0 ≤ t)
    (hB : (X t).B ∈ Icc (2:ℝ) 34) :
    HasDerivAt (fun s => saddleCoordinates e (X s))
      (responseCoordinateField e (saddleCoordinates e (X t))) t := by
  unfold saddleCoordinates
  rw [responseCoordinateField_literal e (X t).A (X t).B (X t).z (X t).H he hu hB]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hX.dB t ht
  · exact hX.dz t ht
  · exact hX.dH t ht
  · have dh := (responseTotal_hasDerivAt e (X t).B he hu hB.1 hB.2).comp t (hX.dB t ht)
    simpa only [Function.comp_def] using ((hX.dA t ht).add (hX.dB t ht)).sub dh

noncomputable def saddleQuadraticValue (e z : ℝ) (x : SaddleVector) : ℝ :=
  responseQuadratic (60/(z+2)) z (localForkSlope e (60/(z+2)) z)
    (localWeight z) (localHSlope z) (x 0) (x 1) (x 2) (x 3)

theorem saddleQuadraticValue_hasDerivAt (e z : ℝ) (hz : 0 ≤ z)
    (x : ℝ → SaddleVector) (dx : SaddleVector) (t : ℝ) (hx : HasDerivAt x dx t) :
    HasDerivAt (fun s => saddleQuadraticValue e z (x s))
      (saddlePairing (saddleGradient e z (x t)) dx) t := by
  have hw : localWeight z ≠ 0 := by unfold localWeight; positivity
  have hv := responseQuadratic_hasDerivAt (60/(z+2)) z
    (localForkSlope e (60/(z+2)) z) (localWeight z) (localHSlope z) hw
    (fun s => x s 0) (fun s => x s 1) (fun s => x s 2) (fun s => x s 3)
    t (dx 0) (dx 1) (dx 2) (dx 3) ((hasDerivAt_pi.mp hx) 0)
    ((hasDerivAt_pi.mp hx) 1) ((hasDerivAt_pi.mp hx) 2) ((hasDerivAt_pi.mp hx) 3)
  convert hv using 1
  simp [saddlePairing,saddleGradient,Fin.sum_univ_succ]
  ring

/-- Strict dissipation for differences of two literal positive trajectories
while both response states lie in the certified neighborhood. -/
theorem middle_trajectory_pair_dissipation (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧
      ∀ X Y : ℝ → State, IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      ∀ t : ℝ, 0 ≤ t → (X t).B ∈ Icc (2:ℝ) 34 → (Y t).B ∈ Icc (2:ℝ) 34 →
      dist (saddleCoordinates e (X t)) ![60/(z+2),z,H,0] < δ →
      dist (saddleCoordinates e (Y t)) ![60/(z+2),z,H,0] < δ →
      ∃ dq : ℝ,
        HasDerivAt (fun s => saddleQuadraticValue e z
          (saddleCoordinates e (X s)-saddleCoordinates e (Y s))) dq t ∧
        dq ≤ -(η*‖saddleCoordinates e (X t)-saddleCoordinates e (Y t)‖^2) := by
  obtain ⟨η,δ,hη,hδ,hpair⟩ := middle_nonlinear_pair_dissipation e z H he hu hz
  refine ⟨η,δ,hη,hδ,?_⟩
  intro X Y hX hY t ht hBX hBY hx hy
  have hd := (saddleCoordinates_hasDerivAt e he hu X hX t ht hBX).sub
    (saddleCoordinates_hasDerivAt e he hu Y hY t ht hBY)
  have hq := saddleQuadraticValue_hasDerivAt e z (by linarith [hz.1])
    (fun s => saddleCoordinates e (X s)-saddleCoordinates e (Y s))
    (responseCoordinateField e (saddleCoordinates e (X t))-
      responseCoordinateField e (saddleCoordinates e (Y t))) t hd
  exact ⟨_,hq,hpair _ _ hx hy⟩

end CoreCouplingGlobal
