import proofs.CoreCouplingGlobal.EnergyBarrier
import proofs.CoreCouplingGlobal.TrajectoryEnergy

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem trajectory_potential_antitone (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Ici T, InResponseBox (X t)) :
    AntitoneOn (fun t => statePotential e p (X t)) (Ici T) := by
  have hd := fun t ht => trajectory_energy_derivative e p he he' X hX t
    (le_trans hT ht) (hb t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici T)
  · intro t ht
    exact (hd t ht).choose_spec.1.continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).choose_spec.1.differentiableAt.differentiableWithinAt
  · intro t ht
    obtain ⟨v,hv,hv'⟩ := hd t (interior_subset ht)
    rw [hv.deriv]
    linarith [responseResidualNorm_nonneg e (X t)]

/-- Below the barrier, an actual trajectory in the response box never reaches its plane. -/
theorem trajectory_avoids_saddle_plane (e : ℝ) (p : PotentialPrimitives e)
    (hp : ∀ H ∈ Icc (0:ℝ) 256, HasDerivAt p.R (3*responseLog (responsePhi H)) H)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Ici T, InResponseBox (X t))
    (Bs zs : ℝ) (hBs : 8 ≤ Bs) (hzs : zs ∈ Icc (0:ℝ) 12)
    (hroot : reducedZ e Bs zs = 0)
    (henergy : statePotential e p (X T) < responsePotential e p Bs zs (naturalH zs) 0) :
    ∀ t ∈ Ici T, (X t).B ≠ Bs := by
  intro t ht heq
  have hmono := trajectory_potential_antitone e p he he' X hX T hT hb
  have hdec := hmono (show T ∈ Ici T by simp) ht ht
  obtain ⟨_,_,_,_,hz,hz',hH,hH'⟩ := hb t ht
  have hbar := saddle_plane_energy_barrier e p hp Bs zs (X t).z (X t).H
    ((X t).A+(X t).B-responseTotal e (X t).B) hBs hzs hroot ⟨hz,hz'⟩
    ⟨hH,by linarith⟩
  have hpEq : statePotential e p (X t) = responsePotential e p Bs (X t).z (X t).H
      ((X t).A+(X t).B-responseTotal e (X t).B) := by
    unfold statePotential
    rw [heq]
  rw [← hpEq] at hbar
  linarith

/-- Continuity turns avoidance of a plane into preservation of its two sides. -/
theorem continuous_plane_side_preserved (b : ℝ → ℝ) (T c : ℝ)
    (hc : ContinuousOn b (Ici T)) (ha : ∀ t ∈ Ici T, b t ≠ c) :
    ∀ t ∈ Ici T, (b t < c ↔ b T < c) := by
  intro t ht
  have hcont : ContinuousOn b (Icc T t) := hc.mono (fun _ hx => hx.1)
  constructor
  · intro hlt
    by_contra hn
    have hge : c ≤ b T := le_of_not_gt hn
    obtain ⟨s,hs,hsc⟩ := intermediate_value_Icc' ht hcont ⟨hlt.le,hge⟩
    exact ha s hs.1 hsc
  · intro hlt
    by_contra hn
    have hge : c ≤ b t := le_of_not_gt hn
    obtain ⟨s,hs,hsc⟩ := intermediate_value_Icc ht hcont ⟨hlt.le,hge⟩
    exact ha s hs.1 hsc

theorem trajectory_barrier_side_preserved (e : ℝ) (p : PotentialPrimitives e)
    (hp : ∀ H ∈ Icc (0:ℝ) 256, HasDerivAt p.R (3*responseLog (responsePhi H)) H)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Ici T, InResponseBox (X t))
    (Bs zs : ℝ) (hBs : 8 ≤ Bs) (hzs : zs ∈ Icc (0:ℝ) 12)
    (hroot : reducedZ e Bs zs = 0)
    (henergy : statePotential e p (X T) < responsePotential e p Bs zs (naturalH zs) 0) :
    ∀ t ∈ Ici T, ((X t).B < Bs ↔ (X T).B < Bs) := by
  apply continuous_plane_side_preserved
  · intro t ht
    exact (hX.dB t (le_trans hT ht)).continuousAt.continuousWithinAt
  · exact trajectory_avoids_saddle_plane e p hp he he' X hX T hT hb Bs zs hBs hzs hroot henergy

end CoreCouplingGlobal
