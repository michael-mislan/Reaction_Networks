import proofs.CoreCouplingGlobal.ResponseDissipation

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

def InResponseBox (X : State) : Prop :=
  0 ≤ X.A ∧ X.A ≤ 34 ∧ 2 ≤ X.B ∧ X.B ≤ 34 ∧
    0 ≤ X.z ∧ X.z ≤ 12 ∧ 0 ≤ X.H ∧ X.H ≤ 1536/7

noncomputable def statePotential (e : ℝ) (p : PotentialPrimitives e) (X : State) : ℝ :=
  responsePotential e p X.B X.z X.H (X.A+X.B-responseTotal e X.B)

noncomputable def responseResidualNorm (e : ℝ) (X : State) : ℝ :=
  (X.A+X.B-responseTotal e X.B)^2/4+(60-(2+X.z)*X.B)^2/1000+
    (responseTotal e X.B-(1+X.z)*X.B-16*X.z-4*X.z^2+3*X.H)^2/364+
    (fH (flagshipRates e) X.z X.H)^2/4000

theorem trajectory_energy_derivative (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (t : ℝ) (ht : 0 ≤ t) (hb : InResponseBox (X t)) :
    ∃ v : ℝ, HasDerivAt (fun s => statePotential e p (X s)) v t ∧
      v ≤ -responseResidualNorm e (X t) := by
  obtain ⟨hA,hA',hB,hB',hz,hz',hH,hH'⟩ := hb
  have dr := ((hX.dA t ht).add (hX.dB t ht)).sub
    ((responseTotal_hasDerivAt e (X t).B he he' hB hB').comp t (hX.dB t ht))
  have hv := responsePotential_hasDerivAt e p he he'
    (fun s => (X s).B) (fun s => (X s).z) (fun s => (X s).H)
    (fun s => (X s).A+(X s).B-responseTotal e (X s).B) t _ _ _ _
    ⟨hB,hB'⟩ ⟨hz,hz'⟩ ⟨hH,hH'⟩ (hX.dB t ht) (hX.dz t ht) (hX.dH t ht) dr
  refine ⟨_,hv,?_⟩
  have hh := response_directional_dissipation e (X t).A (X t).B (X t).z (X t).H
    he he' hA hA' hB hB' hz hz' hH hH'
  dsimp [responseResidualNorm]
  convert hh using 1
  ring

theorem trajectory_eventually_responseBox (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) :
    ∀ᶠ t in Filter.atTop, InResponseBox (X t) := by
  filter_upwards [trajectory_eventually_absorbing e he he' X hX,
    Filter.eventually_ge_atTop (0:ℝ)] with t ht ht0
  have hp := hX.positive t ht0
  obtain ⟨hs,hW,hz,hB⟩ := ht
  rcases hp with ⟨hA0,hB0,hz0,hH0⟩
  exact ⟨hA0.le,by linarith,hB.le,by linarith,hz0.le,hz.le,hH0.le,by linarith⟩

theorem responseResidualNorm_nonneg (e : ℝ) (X : State) : 0 ≤ responseResidualNorm e X := by
  unfold responseResidualNorm
  positivity

theorem stationary_of_responseResidualNorm_zero (e : ℝ) (X : State)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hb : InResponseBox X)
    (hzero : responseResidualNorm e X = 0) : Stationary (flagshipRates e) X := by
  obtain ⟨_,_,hB,hB',_,_,_,_⟩ := hb
  have hq : responseTotal e X.B+e*(responseTotal e X.B-X.B)^2 = 33+e*X.B := by
    have hh := response_quadratic e X.B he he' hB hB'
    dsimp [responseTotal]
    nlinarith only [hh]
  obtain ⟨hs,hbb,hzz⟩ := response_residual_identities e X.A X.B X.z X.H (responseTotal e X.B) hq
  have hr2 := sq_nonneg (X.A+X.B-responseTotal e X.B)
  have hF2 := sq_nonneg (60-(2+X.z)*X.B)
  have hZ2 := sq_nonneg (responseTotal e X.B-(1+X.z)*X.B-16*X.z-4*X.z^2+3*X.H)
  have hK2 := sq_nonneg (fH (flagshipRates e) X.z X.H)
  unfold responseResidualNorm at hzero
  have hr : X.A+X.B-responseTotal e X.B = 0 := by nlinarith only [hzero,hr2,hF2,hZ2,hK2]
  have hF : 60-(2+X.z)*X.B = 0 := by nlinarith only [hzero,hr2,hF2,hZ2,hK2]
  have hZ : responseTotal e X.B-(1+X.z)*X.B-16*X.z-4*X.z^2+3*X.H = 0 := by
    nlinarith only [hzero,hr2,hF2,hZ2,hK2]
  have hK : fH (flagshipRates e) X.z X.H = 0 := by nlinarith only [hzero,hr2,hF2,hZ2,hK2]
  rw [hr,mul_zero] at hs
  rw [hr,hF,mul_zero,zero_add] at hbb
  rw [hr,hZ,add_zero] at hzz
  exact ⟨by linarith,hbb,hzz,hK⟩

end CoreCouplingGlobal
