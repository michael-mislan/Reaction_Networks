import proofs.CoreCouplingGlobal.ExitSelectionRegion
import proofs.CoreCouplingGlobal.PositiveFlow

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem stationary_response_center (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s) :
    s.B = 60/(s.z+2) ∧
    saddleCoordinates e s = ![60/(s.z+2),s.z,(16*s.z+2*s.z^2)/(20001/10000),0] ∧
    responseTotal e (60/(s.z+2))-(1+s.z)*(60/(s.z+2))-16*s.z-4*s.z^2+
      3*((16*s.z+2*s.z^2)/(20001/10000)) = 0 := by
  obtain ⟨hr,hH,hZ⟩ := positive_stationary_barrier_identities e he hu s hs hss
  have hA := hss.1
  have hB := hss.2.1
  dsimp [fA,fB,flagshipRates] at hA hB
  have hfork : 60-(2+s.z)*s.B = 0 := by linear_combination hA+2*hB
  have hBs : s.B = 60/(s.z+2) := by
    apply (eq_div_iff (by linarith [hs.2.2.1] : s.z+2 ≠ 0)).2
    nlinarith only [hfork]
  refine ⟨hBs,?_,?_⟩
  · rw [hBs] at hr
    ext i
    fin_cases i <;> simp [saddleCoordinates,hr,hH,naturalH,hBs]
  · rw [← hBs]
    unfold reducedZ at hZ
    nlinarith only [hZ]

/-- Negative-cone perturbations of a sufficiently close reference trajectory
select the two classified outer equilibria according to their initial B side. -/
theorem middle_cone_departures_select (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      mid.z ∈ Icc (19/10:ℝ) (21/10) ∧
      ∃ α δ θ : ℝ, 0 < α ∧ 0 < δ ∧ 0 < θ ∧
      perturbedSaddleQuadratic e mid.z α
        ![-(60/(mid.z+2))/(mid.z+2),1,(16+4*mid.z)/(20001/10000),0] < 0 ∧
      ∀ r : ℝ, 0 < r → r < δ → ∀ X Y : ℝ → State,
      IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      (∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) (saddleCoordinates e mid) < θ*r) →
      dist (saddleCoordinates e (Y 0)) (saddleCoordinates e mid) < r →
      pairConeValue e mid.z α X Y 0 < 0 →
      ((Y 0).B < (X 0).B → Tendsto (fun t => encodeState (Y t)) atTop (𝓝 (encodeState high))) ∧
      ((X 0).B < (Y 0).B → Tendsto (fun t => encodeState (Y t)) atTop (𝓝 (encodeState low))) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨P,hP⟩ := extendedPotentialPrimitives_nonempty e he hu
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,_hbl,hbm,_hbh,hall⟩ :=
    exactly_three_bracketed_equilibria e hl hu
  have heq : varyRates e = flagshipRates e := rfl
  rw [heq] at hslo hsm hshi hall
  obtain ⟨hBmid,hcenter,hZ⟩ := stationary_response_center e he hu mid hm hsm
  obtain ⟨α,δ,θ,hα,hδ,hθ,_hθh,hv,hexit⟩ :=
    middle_actual_exit_selector_conditions e mid.z P he hu hbm hZ
  have hbar : ∀ x : State, InResponseBox x → x.B = mid.B →
      statePotential e P mid ≤ statePotential e P x := by
    intro x hx hxB
    exact stationary_energy_barrier e P hP he hu mid hm hsm
      (stationary_B_ge_eight e mid hm hsm (by linarith [hbm.2])) x hx hxB
  have hBlo := stationary_B_reverse_order e low mid hlo hslo hsm hlm
  have hBhi := stationary_B_reverse_order e mid high hm hsm hshi hmh
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hbm,α,δ,θ,hα,hδ,hθ,hv,?_⟩
  intro r hr hrd X Y hX hY hstay hY0 hstart
  rw [hcenter] at hstay hY0
  obtain ⟨τ,hτ,_hlevel,hregion,henergy,hleft,hright⟩ :=
    hexit r hr hrd X Y hX hY hstay hY0 hstart
  have hEmid : statePotential e P mid =
      responsePotential e P (60/(mid.z+2)) mid.z ((16*mid.z+2*mid.z^2)/(20001/10000)) 0 := by
    have hh := congrArg (fun x : SaddleVector => responsePotential e P (x 0) (x 1) (x 2) (x 3)) hcenter
    exact hh
  have hE : statePotential e P (Y τ) < statePotential e P mid := by
    rw [hEmid]
    exact henergy
  have hshift := positive_trajectory_time_shift e Y hY τ hτ.le
  have hforward := selection_region_forward e he hu (fun t => Y (t+τ)) hshift
    (by simpa only [zero_add] using hregion)
  have hbox : ∀ t ∈ Ici τ, InResponseBox (Y t) := by
    intro t ht
    simpa only [sub_add_cancel] using (hforward (t-τ) (sub_nonneg.mpr ht)).2
  obtain ⟨s,hs,hss,hlim,hsne,hside⟩ := sublevel_limit_side e P hl hu mid hbar Y hY τ hτ.le hbox hE
  have hcases := (hall s hs hss).1
  have hleft' : (Y τ).B < mid.B ↔ (Y 0).B < (X 0).B := by
    rw [hBmid]
    exact hleft
  have hright' : mid.B < (Y τ).B ↔ (X 0).B < (Y 0).B := by
    rw [hBmid]
    exact hright
  constructor
  · intro hinit
    have hslt := hside.2 (hleft'.2 hinit)
    rcases hcases with h | h | h
    · rw [h] at hslt
      linarith
    · rw [h] at hsne
      exact False.elim (hsne rfl)
    · simpa only [h] using hlim
  · intro hinit
    have hgt := hright'.2 hinit
    rcases hcases with h | h | h
    · simpa only [h] using hlim
    · rw [h] at hsne
      exact False.elim (hsne rfl)
    · have hslt : s.B < mid.B := by rw [h]; exact hBhi
      have hh := hside.1 hslt
      linarith

end CoreCouplingGlobal
