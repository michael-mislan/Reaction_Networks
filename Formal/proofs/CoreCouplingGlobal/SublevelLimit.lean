import proofs.CoreCouplingGlobal.EquilibriumBarrier
import proofs.CoreCouplingGlobal.GlobalConvergence

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem trajectory_limit_energy_le (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Ici T, InResponseBox (X t))
    (s : State) (hs : InResponseBox s)
    (hlim : Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s))) :
    statePotential e p s ≤ statePotential e p (X T) := by
  have hmem : ∀ᶠ t in atTop, encodeState (X t) ∈ responseBox := by
    filter_upwards [eventually_ge_atTop T] with t ht
    apply (responseBox_iff _).2
    simpa only [decode_encodeState] using hb t ht
  have hsmem : encodeState s ∈ responseBox := by
    apply (responseBox_iff _).2
    simpa only [decode_encodeState] using hs
  have hwithin : Tendsto (fun t => encodeState (X t)) atTop (𝓝[responseBox] (encodeState s)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim,hmem⟩
  have hv := ((statePotential_continuousOn e p) _ hsmem).tendsto.comp hwithin
  have hmono := trajectory_potential_antitone e p he hu X hX T hT hb
  apply le_of_tendsto (show Tendsto (fun t => statePotential e p (X t)) atTop
    (𝓝 (statePotential e p s)) from by simpa only [Function.comp_apply,decode_encodeState] using hv)
  filter_upwards [eventually_ge_atTop T] with t ht
  exact hmono (by simp) ht ht

/-- Below an equilibrium's plane barrier, the limiting equilibrium is strictly on
the initial side. No convergence or plane-avoidance hypothesis is imposed. -/
theorem sublevel_limit_side (e : ℝ) (p : PotentialPrimitives e)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (mid : State)
    (hbar : ∀ x : State, InResponseBox x → x.B = mid.B → statePotential e p mid ≤ statePotential e p x)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) (T : ℝ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Ici T, InResponseBox (X t))
    (henergy : statePotential e p (X T) < statePotential e p mid) :
    ∃ s : State, s.Positive ∧ Stationary (flagshipRates e) s ∧
      Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s)) ∧
      s.B ≠ mid.B ∧ (s.B < mid.B ↔ (X T).B < mid.B) := by
  have he : 0 ≤ e := by linarith
  have hmono := trajectory_potential_antitone e p he hu X hX T hT hb
  have havoid : ∀ t ∈ Ici T, (X t).B ≠ mid.B := by
    intro t ht heq
    have hbar' := hbar (X t) (hb t ht) heq
    have hdec := hmono (by simp) ht ht
    linarith
  have hside := continuous_plane_side_preserved (fun t => (X t).B) T mid.B
    (fun t ht => (hX.dB t (le_trans hT ht)).continuousAt.continuousWithinAt) havoid
  obtain ⟨s,hs,hss,hlim⟩ := trajectory_converges_to_positive_equilibrium e hl hu X hX
  have hsbox := positive_stationary_in_responseBox e he hu s hs hss
  have hle := trajectory_limit_energy_le e p he hu X hX T hT hb s hsbox hlim
  have hsne : s.B ≠ mid.B := by
    intro heq
    have hbar' := hbar s hsbox heq
    linarith
  have hBlim : Tendsto (fun t => (X t).B) atTop (𝓝 s.B) := by
    simpa [encodeState] using (continuous_apply (1 : Fin 4)).tendsto (encodeState s) |>.comp hlim
  refine ⟨s,hs,hss,hlim,hsne,?_⟩
  constructor
  · intro hslt
    by_contra hn
    have hall : ∀ᶠ t in atTop, mid.B ≤ (X t).B := by
      filter_upwards [eventually_ge_atTop T] with t ht
      exact le_of_not_gt (fun hlt => hn ((hside t ht).1 hlt))
    have hge := ge_of_tendsto hBlim hall
    linarith
  · intro hlt
    have hall : ∀ᶠ t in atTop, (X t).B ≤ mid.B := by
      filter_upwards [eventually_ge_atTop T] with t ht
      exact ((hside t ht).2 hlt).le
    exact lt_of_le_of_ne (le_of_tendsto hBlim hall) hsne

theorem stationary_B_reverse_order (e : ℝ) (x y : State) (hx : x.Positive)
    (hsx : Stationary (flagshipRates e) x) (hsy : Stationary (flagshipRates e) y)
    (hxy : x.z < y.z) : y.B < x.B := by
  have hxa := hsx.1
  have hxb := hsx.2.1
  have hya := hsy.1
  have hyb := hsy.2.1
  dsimp [fA,fB,flagshipRates] at hxa hxb hya hyb
  have hxe : (2+x.z)*x.B = 60 := by linear_combination -hxa-2*hxb
  have hye : (2+y.z)*y.B = 60 := by linear_combination -hya-2*hyb
  by_contra hn
  have hdiff : 0 ≤ y.B-x.B := by linarith
  have hyp : 0 < 2+y.z := by linarith [hx.2.2.1]
  have hprod := mul_nonneg hdiff hyp.le
  have hstrict := mul_pos hx.2.1 (sub_pos.mpr hxy)
  nlinarith

/-- A literal sublevel selector: the two sides select opposite z-ordered outer states.
The forward-box hypothesis remains explicit; the full basin boundary is separate. -/
theorem classified_sublevel_selector (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) :
    ∃ p : PotentialPrimitives e, ∃ low mid high : State,
      low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      ∀ X : ℝ → State, IsPositiveTrajectory e X → ∀ T : ℝ, 0 ≤ T →
        (∀ t ∈ Ici T, InResponseBox (X t)) →
        statePotential e p (X T) < statePotential e p mid →
        ((X T).B < mid.B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high))) ∧
        (mid.B < (X T).B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low))) := by
  obtain ⟨p,low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hall,hbar⟩ :=
    classified_middle_energy_barrier e hl hu
  have hBlo := stationary_B_reverse_order e low mid hlo hslo hsm hlm
  have hBhi := stationary_B_reverse_order e mid high hm hsm hshi hmh
  refine ⟨p,low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,?_⟩
  intro X hX T hT hb henergy
  obtain ⟨s,hs,hss,hlim,hsne,hside⟩ := sublevel_limit_side e p hl hu mid hbar X hX T hT hb henergy
  have hcases := hall s hs hss
  constructor
  · intro hlt
    have hslt := hside.2 hlt
    rcases hcases with heq | heq | heq
    · rw [heq] at hslt
      linarith
    · rw [heq] at hsne
      exact False.elim (hsne rfl)
    · simpa only [heq] using hlim
  · intro hgt
    rcases hcases with heq | heq | heq
    · simpa only [heq] using hlim
    · rw [heq] at hsne
      exact False.elim (hsne rfl)
    · have hlt : s.B < mid.B := by rw [heq]; exact hBhi
      have hbad := hside.1 hlt
      linarith

end CoreCouplingGlobal
