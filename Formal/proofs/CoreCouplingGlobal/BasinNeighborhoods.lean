import proofs.CoreCouplingGlobal.NonemptySelector
import proofs.CoreCouplingGlobal.FlowContinuity

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem statePotential_continuousAt (e : ℝ) (p : PotentialPrimitives e)
    (x : ResponseVector) (hz : 0 ≤ x 2) :
    ContinuousAt (fun y : ResponseVector => statePotential e p (decodeState y)) x := by
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
  unfold statePotential responsePotential responseTotal responseLog decodeState
  dsimp only
  have h₀ := (continuous_apply (0 : Fin 4) : Continuous (fun y : ResponseVector => y 0)).continuousAt (x := x)
  have h₁ := (continuous_apply (1 : Fin 4) : Continuous (fun y : ResponseVector => y 1)).continuousAt (x := x)
  have h₃ := (continuous_apply (3 : Fin 4) : Continuous (fun y : ResponseVector => y 3)).continuousAt (x := x)
  exact ((((((h₁.mul hl₂).sub ((h₁.add hAc).mul (hl₁.sub hl₂))).add hUc).sub
    ((continuousAt_const.mul h₃).mul (hl₁.sub hl₂))).add hPc).add hRc).add
    ((((h₀.add h₁).sub (h₁.add hAc)).pow 2).div_const 2)


theorem stationary_selector_neighborhood (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (s mid : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s)
    (henergy : statePotential e p s < statePotential e p mid) (hside : s.B ≠ mid.B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : State, dist (encodeState x) (encodeState s) < δ →
      InSelectionRegion x ∧ statePotential e p x < statePotential e p mid ∧
      (x.B < mid.B ↔ s.B < mid.B) := by
  have habs := trajectory_eventually_absorbing e he hu (fun _ => s)
    (stationary_positive_trajectory e s hs hss)
  obtain ⟨hS,hW,hz,hB⟩ := habs.exists.choose_spec
  have hSc : Continuous (fun x : ResponseVector => x 0+x 1) := by fun_prop
  have hWc : Continuous (fun x : ResponseVector => x 2+(7/4:ℝ)*x 3) := by fun_prop
  have hSe : ∀ᶠ x in 𝓝 (encodeState s), x 0+x 1 < 34 :=
    Filter.Tendsto.eventually_lt_const hS hSc.continuousAt
  have hWe : ∀ᶠ x in 𝓝 (encodeState s), x 2+(7/4:ℝ)*x 3 < 384 :=
    Filter.Tendsto.eventually_lt_const hW hWc.continuousAt
  have hze : ∀ᶠ x in 𝓝 (encodeState s), x 2 < 12 :=
    Filter.Tendsto.eventually_lt_const hz (continuous_apply (2:Fin 4)).continuousAt
  have hBe : ∀ᶠ x in 𝓝 (encodeState s), 2 < x 1 :=
    Filter.Tendsto.eventually_const_lt hB (continuous_apply (1:Fin 4)).continuousAt
  have hVe : ∀ᶠ x in 𝓝 (encodeState s), statePotential e p (decodeState x) < statePotential e p mid :=
    Filter.Tendsto.eventually_lt_const (by simpa only [decode_encodeState] using henergy)
      (statePotential_continuousAt e p (encodeState s) hs.2.2.1.le)
  have hsideE : ∀ᶠ x in 𝓝 (encodeState s), (x 1 < mid.B ↔ s.B < mid.B) := by
    rcases lt_or_gt_of_ne hside with hlt | hgt
    · filter_upwards [Filter.Tendsto.eventually_lt_const hlt
        (continuous_apply (1:Fin 4)).continuousAt] with x hx
      exact iff_of_true hx hlt
    · filter_upwards [Filter.Tendsto.eventually_const_lt hgt
        (continuous_apply (1:Fin 4)).continuousAt] with x hx
      exact iff_of_false (not_lt.mpr hx.le) (not_lt.mpr hgt.le)
  have hall : ∀ᶠ x in 𝓝 (encodeState s), InSelectionRegion (decodeState x) ∧
      statePotential e p (decodeState x) < statePotential e p mid ∧
      (x 1 < mid.B ↔ s.B < mid.B) := by
    filter_upwards [hSe,hWe,hze,hBe,hVe,hsideE] with x hxS hxW hxz hxB hxV hxside
    exact ⟨⟨hxS.le,hxW.le,hxz.le,hxB.le⟩,hxV,hxside⟩
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.1 hall
  refine ⟨δ,hδ,?_⟩
  intro x hx
  simpa only [decode_encodeState] using hbound hx

end CoreCouplingGlobal
