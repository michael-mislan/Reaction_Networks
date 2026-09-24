import proofs.CoreCouplingGlobal.TrajectoryEnergy
import proofs.CoreCouplingGlobal.CompactDissipation

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

abbrev ResponseVector := Fin 4 → ℝ
def encodeState (X : State) : ResponseVector := ![X.A,X.B,X.z,X.H]
def decodeState (x : ResponseVector) : State := ⟨x 0,x 1,x 2,x 3⟩
def responseBox : Set ResponseVector := Icc ![0,2,0,0] ![34,34,12,1536/7]

theorem decode_encodeState (X : State) : decodeState (encodeState X) = X := by cases X; rfl

theorem responseBox_iff (x : ResponseVector) : x ∈ responseBox ↔ InResponseBox (decodeState x) := by
  simp [responseBox,InResponseBox,decodeState,Pi.le_def,Fin.forall_fin_succ]
  tauto

noncomputable def responseVectorField (e : ℝ) (x : ResponseVector) : ResponseVector :=
  ![fA (flagshipRates e) (x 0) (x 1) (x 2),fB (flagshipRates e) (x 0) (x 1) (x 2),
    fZ (flagshipRates e) (x 0) (x 1) (x 2) (x 3),fH (flagshipRates e) (x 2) (x 3)]

theorem responseVectorField_continuous (e : ℝ) : Continuous (responseVectorField e) := by
  unfold responseVectorField fA fB fZ fH flagshipRates
  fun_prop

theorem residualNorm_continuous (e : ℝ) :
    Continuous (fun x : ResponseVector => responseResidualNorm e (decodeState x)) := by
  have hc := responseA_continuous e
  unfold responseResidualNorm responseTotal decodeState fH flagshipRates
  fun_prop

theorem statePotential_continuousOn (e : ℝ) (p : PotentialPrimitives e) :
    ContinuousOn (fun x : ResponseVector => statePotential e p (decodeState x)) responseBox := by
  intro x hx
  have hb := (responseBox_iff x).1 hx
  have hz : 0 ≤ x 2 := hb.2.2.2.2.1
  have hz1 : x 2+1 ≠ 0 := by linarith
  have hz2 : x 2+2 ≠ 0 := by linarith
  have hc := responseA_continuous e
  have hU := p.continuousU
  have hP := p.continuousP
  have hR := p.continuousR
  have hzC : ContinuousAt (fun y : ResponseVector => y 2) x := (continuous_apply 2).continuousAt
  have hl₁ : ContinuousAt (fun y : ResponseVector => Real.log (y 2+1)) x :=
    (hzC.add continuousAt_const).log hz1
  have hl₂ : ContinuousAt (fun y : ResponseVector => Real.log (y 2+2)) x :=
    (hzC.add continuousAt_const).log hz2
  have hAc : ContinuousAt (fun y : ResponseVector => responseA e (y 1)) x :=
    hc.continuousAt.comp (f := fun y : ResponseVector => y 1) (continuous_apply 1).continuousAt
  have hUc : ContinuousAt (fun y : ResponseVector => p.U (y 2)) x :=
    hU.continuousAt.comp (f := fun y : ResponseVector => y 2) hzC
  have hPc : ContinuousAt (fun y : ResponseVector => p.P (y 1)) x :=
    hP.continuousAt.comp (f := fun y : ResponseVector => y 1) (continuous_apply 1).continuousAt
  have hRc : ContinuousAt (fun y : ResponseVector => p.R (y 3)) x :=
    hR.continuousAt.comp (f := fun y : ResponseVector => y 3) (continuous_apply 3).continuousAt
  apply ContinuousAt.continuousWithinAt
  unfold statePotential responsePotential responseTotal responseLog decodeState
  dsimp only
  have h₀ := (continuous_apply (0 : Fin 4) : Continuous (fun y : ResponseVector => y 0)).continuousAt (x := x)
  have h₁ := (continuous_apply (1 : Fin 4) : Continuous (fun y : ResponseVector => y 1)).continuousAt (x := x)
  have h₃ := (continuous_apply (3 : Fin 4) : Continuous (fun y : ResponseVector => y 3)).continuousAt (x := x)
  exact ((((((h₁.mul hl₂).sub ((h₁.add hAc).mul (hl₁.sub hl₂))).add hUc).sub
    ((continuousAt_const.mul h₃).mul (hl₁.sub hl₂))).add hPc).add hRc).add
    ((((h₀.add h₁).sub (h₁.add hAc)).pow 2).div_const 2)

theorem trajectory_residual_tendsto_zero (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) :
    Tendsto (fun t => responseResidualNorm e (X t)) atTop (𝓝 0) := by
  obtain ⟨p⟩ := potentialPrimitives_nonempty e he he'
  obtain ⟨T,hT⟩ := eventually_atTop.1
    ((trajectory_eventually_responseBox e he he' X hX).and (eventually_ge_atTop (0:ℝ)))
  have hh := compact_trajectory_dissipation responseBox isCompact_Icc
    (responseVectorField e) (fun x => statePotential e p (decodeState x))
    (fun x => responseResidualNorm e (decodeState x))
    (responseVectorField_continuous e).continuousOn (statePotential_continuousOn e p)
    (residualNorm_continuous e).continuousOn
    (fun x _ => responseResidualNorm_nonneg e (decodeState x))
    (fun t => encodeState (X t)) T
    (fun t ht => (responseBox_iff _).2 (by simpa only [decode_encodeState] using (hT t ht).1))
    (by
      intro t ht
      apply hasDerivAt_pi.2
      intro i
      fin_cases i
      · exact hX.dA t (hT t ht).2
      · exact hX.dB t (hT t ht).2
      · exact hX.dz t (hT t ht).2
      · exact hX.dH t (hT t ht).2)
    (by
      intro t ht
      simpa only [decode_encodeState] using
        trajectory_energy_derivative e p he he' X hX t (hT t ht).2 (hT t ht).1)
  simpa only [decode_encodeState] using hh

end CoreCouplingGlobal
