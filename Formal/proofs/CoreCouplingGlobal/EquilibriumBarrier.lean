import proofs.CoreCouplingGlobal.EnergySelection
import proofs.CoreCouplingGlobal.EquilibriumBrackets

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem stationary_positive_trajectory (e : ℝ) (s : State) (hs : s.Positive)
    (heq : Stationary (flagshipRates e) s) : IsPositiveTrajectory e (fun _ => s) := by
  refine ⟨fun _ _ => hs,?_,?_,?_,?_⟩
  · intro t _
    simpa only [heq.1] using hasDerivAt_const t s.A
  · intro t _
    simpa only [heq.2.1] using hasDerivAt_const t s.B
  · intro t _
    simpa only [heq.2.2.1] using hasDerivAt_const t s.z
  · intro t _
    simpa only [heq.2.2.2] using hasDerivAt_const t s.H

theorem positive_stationary_in_responseBox (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (heq : Stationary (flagshipRates e) s) :
    InResponseBox s := by
  have hb := trajectory_eventually_responseBox e he he' (fun _ => s)
    (stationary_positive_trajectory e s hs heq)
  exact hb.exists.choose_spec

theorem positive_stationary_residual_zero (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (heq : Stationary (flagshipRates e) s) :
    responseResidualNorm e s = 0 := by
  obtain ⟨p⟩ := potentialPrimitives_nonempty e he he'
  obtain ⟨v,hv,hv'⟩ := trajectory_energy_derivative e p he he' (fun _ => s)
    (stationary_positive_trajectory e s hs heq) 0 (by norm_num)
    (positive_stationary_in_responseBox e he he' s hs heq)
  have hv0 : v = 0 := hv.unique (hasDerivAt_const 0 (statePotential e p s))
  have hn := responseResidualNorm_nonneg e s
  rw [hv0] at hv'
  linarith

theorem positive_stationary_barrier_identities (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (heq : Stationary (flagshipRates e) s) :
    s.A+s.B-responseTotal e s.B = 0 ∧ s.H = naturalH s.z ∧ reducedZ e s.B s.z = 0 := by
  have hn := positive_stationary_residual_zero e he he' s hs heq
  have hr2 := sq_nonneg (s.A+s.B-responseTotal e s.B)
  have hF2 := sq_nonneg (60-(2+s.z)*s.B)
  have hZ2 := sq_nonneg (responseTotal e s.B-(1+s.z)*s.B-16*s.z-4*s.z^2+3*s.H)
  have hK2 := sq_nonneg (fH (flagshipRates e) s.z s.H)
  unfold responseResidualNorm at hn
  have hr : s.A+s.B-responseTotal e s.B = 0 := by nlinarith only [hn,hr2,hF2,hZ2,hK2]
  have hZ : responseTotal e s.B-(1+s.z)*s.B-16*s.z-4*s.z^2+3*s.H = 0 := by
    nlinarith only [hn,hr2,hF2,hZ2,hK2]
  have hH := heq.2.2.2
  dsimp [fH,flagshipRates] at hH
  have hnat : s.H = naturalH s.z := by
    unfold naturalH
    apply (eq_div_iff (by norm_num : (20001/10000:ℝ) ≠ 0)).2
    linarith
  refine ⟨hr,hnat,?_⟩
  unfold reducedZ
  nlinarith only [hH,hZ]

theorem stationary_energy_barrier (e : ℝ) (p : PotentialPrimitives e)
    (hp : ∀ H ∈ Icc (0:ℝ) 256, HasDerivAt p.R (3*responseLog (responsePhi H)) H)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (heq : Stationary (flagshipRates e) s) (hB : 8 ≤ s.B)
    (x : State) (hx : InResponseBox x) (hplane : x.B = s.B) :
    statePotential e p s ≤ statePotential e p x := by
  obtain ⟨hr,hH,hroot⟩ := positive_stationary_barrier_identities e he he' s hs heq
  obtain ⟨_,_,_,_,hz,hz',_,_⟩ := positive_stationary_in_responseBox e he he' s hs heq
  obtain ⟨_,_,_,_,hxz,hxz',hxH,hxH'⟩ := hx
  have hbar := saddle_plane_energy_barrier e p hp s.B s.z x.z x.H
    (x.A+x.B-responseTotal e x.B) hB ⟨hz,hz'⟩ hroot ⟨hxz,hxz'⟩ ⟨hxH,by linarith⟩
  unfold statePotential
  rw [hr,hH,hplane]
  simpa only [hplane] using hbar

theorem stationary_B_ge_eight (e : ℝ) (s : State) (hs : s.Positive)
    (heq : Stationary (flagshipRates e) s) (hz : s.z ≤ 5) : 8 ≤ s.B := by
  have hA := heq.1
  have hB := heq.2.1
  dsimp [fA,fB,flagshipRates] at hA hB
  have hsum : 60-(2+s.z)*s.B = 0 := by linear_combination hA+2*hB
  have hprod := mul_nonneg (show 0 ≤ 5-s.z by linarith) hs.2.1.le
  nlinarith

/-- The barrier is realized by the middle member of the exact three-state classification. -/
theorem classified_middle_energy_barrier (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) :
    ∃ p : PotentialPrimitives e, ∃ low mid high : State,
      low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      (∀ s : State, s.Positive → Stationary (flagshipRates e) s →
        s = low ∨ s = mid ∨ s = high) ∧
      (∀ x : State, InResponseBox x → x.B = mid.B → statePotential e p mid ≤ statePotential e p x) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨p,hp⟩ := extendedPotentialPrimitives_nonempty e he hu
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,_,hbm,_,hall⟩ :=
    exactly_three_bracketed_equilibria e hl hu
  have heq : varyRates e = flagshipRates e := rfl
  rw [heq] at hslo hsm hshi hall
  refine ⟨p,low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,?_,?_⟩
  · intro s hs hss
    exact (hall s hs hss).1
  · intro x hx hplane
    exact stationary_energy_barrier e p hp he hu mid hm hsm
      (stationary_B_ge_eight e mid hm hsm (by linarith [hbm.2])) x hx hplane

end CoreCouplingGlobal

-- Final source checkpoint: classified middle-state barrier included.
