import proofs.CoreCouplingGlobal.MiddleAdmissibility

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

/-- The middle equilibrium itself is on both outer basin boundaries, witnessed
by response-curve points approaching it from opposite directions. -/
theorem middle_equilibrium_common_frontier (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      encodeState mid ∈ frontier (positiveBasin e low) ∧
      encodeState mid ∈ frontier (positiveBasin e high) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨p,hp⟩ := extendedPotentialPrimitives_nonempty e he hu
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hbl,hbm,hbh,hall⟩ :=
    exactly_three_bracketed_equilibria e hl hu
  have heq : varyRates e = flagshipRates e := rfl
  rw [heq] at hslo hsm hshi hall
  have hall' : ∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high :=
    fun s hs hss => (hall s hs hss).1
  have hrates := varyRates_positive e (by linarith)
  have hsl : residual (varyRates e) low.z = 0 := positive_stationary_residual _ hrates low hlo (by simpa only [heq] using hslo)
  have hsr : residual (varyRates e) mid.z = 0 := positive_stationary_residual _ hrates mid hm (by simpa only [heq] using hsm)
  have hsh : residual (varyRates e) high.z = 0 := positive_stationary_residual _ hrates high hhi (by simpa only [heq] using hshi)
  obtain ⟨hpos,hneg⟩ := residual_between_bracketed_roots e hl hu low mid high hbl hbm hbh hsl hsr hsh
    (by simpa only [heq] using hall')
  have hBlo := stationary_B_reverse_order e low mid hlo hslo hsm hlm
  have hBhi := stationary_B_reverse_order e mid high hm hsm hshi hmh
  have hbar : ∀ x : State, InResponseBox x → x.B = mid.B → statePotential e p mid ≤ statePotential e p x :=
    fun x hx hplane => stationary_energy_barrier e p hp he hu mid hm hsm
      (stationary_B_ge_eight e mid hm hsm (by linarith [hbm.2])) x hx hplane
  obtain ⟨δ,hδ,hadm⟩ := stationary_curve_admissible e he hu mid hm hsm
  have hcenter := responseCurveState_stationary e he hu mid hm hsm
  have hBmid : 60/(mid.z+2) = mid.B := congrArg State.B hcenter
  let a := max low.z (mid.z-δ/2)
  let b := min high.z (mid.z+δ/2)
  have ha : a < mid.z := max_lt hlm (by linarith)
  have hb : mid.z < b := lt_min hmh (by linarith)
  have hleft : MapsTo (fun z => encodeState (responseCurveState e z)) (Ioo a mid.z) (positiveBasin e low) := by
    intro z hz
    have hzl : low.z < z := lt_of_le_of_lt (le_max_left _ _) hz.1
    have hzd : dist z mid.z < δ := by
      rw [Real.dist_eq,abs_of_neg (sub_neg.mpr hz.2)]
      have hza : mid.z-δ/2 ≤ a := le_max_right _ _
      linarith [hz.1]
    obtain ⟨hzp,hreg⟩ := hadm z hzd
    have hE : statePotential e p (responseCurveState e z) < statePotential e p mid := by
      rw [responseCurveState_energy,stationary_curve_energy e p he hu mid hm hsm]
      apply curveEnergy_strict_increase e p he hu z mid.z (by linarith [hbl.1]) (by linarith [hbm.2]) hz.2
      intro t ht
      exact hpos t ⟨hzl.trans ht.1,ht.2⟩
    have hB : mid.B < (responseCurveState e z).B := by
      change mid.B < 60/(z+2)
      rw [← hBmid]
      exact responseCurve_B_reverse (by linarith [hbl.1]) hz.2
    exact (sublevel_outer_basin_membership e p hl hu low mid high hBlo hBhi hall' hbar
      (responseCurveState e z) hzp hreg hE).2 hB
  have hright : MapsTo (fun z => encodeState (responseCurveState e z)) (Ioo mid.z b) (positiveBasin e high) := by
    intro z hz
    have hzh : z < high.z := lt_of_lt_of_le hz.2 (min_le_left _ _)
    have hzd : dist z mid.z < δ := by
      rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hz.1)]
      have hzb : b ≤ mid.z+δ/2 := min_le_right _ _
      linarith [hz.2]
    obtain ⟨hzp,hreg⟩ := hadm z hzd
    have hE : statePotential e p (responseCurveState e z) < statePotential e p mid := by
      rw [responseCurveState_energy,stationary_curve_energy e p he hu mid hm hsm]
      apply curveEnergy_strict_decrease e p he hu mid.z z (by linarith [hbm.1]) (by linarith [hbh.2]) hz.1
      intro t ht
      exact hneg t ⟨ht.1,ht.2.trans hzh⟩
    have hB : (responseCurveState e z).B < mid.B := by
      change 60/(z+2) < mid.B
      rw [← hBmid]
      exact responseCurve_B_reverse hm.2.2.1.le hz.1
    exact (sublevel_outer_basin_membership e p hl hu low mid high hBlo hBhi hall' hbar
      (responseCurveState e z) hzp hreg hE).1 hB
  have hc := responseCurveState_continuousAt e mid.z hm.2.2.1.le
  have hcl : encodeState mid ∈ closure (positiveBasin e low) := by
    have hx : mid.z ∈ closure (Ioo a mid.z) := by
      rw [closure_Ioo ha.ne]
      exact ⟨ha.le,le_rfl⟩
    simpa only [hcenter] using hc.continuousWithinAt.mem_closure hx hleft
  have hch : encodeState mid ∈ closure (positiveBasin e high) := by
    have hx : mid.z ∈ closure (Ioo mid.z b) := by
      rw [closure_Ioo hb.ne]
      exact ⟨le_rfl,hb.le⟩
    simpa only [hcenter] using hc.continuousWithinAt.mem_closure hx hright
  have hmm : encodeState mid ∈ positiveBasin e mid := by
    refine ⟨fun _ => mid,stationary_positive_trajectory e mid hm hsm,?_,tendsto_const_nhds⟩
    exact (decode_encodeState mid).symm
  have hnlow : mid ≠ low := by intro h; rw [h] at hlm; exact lt_irrefl _ hlm
  have hnhigh : mid ≠ high := by intro h; rw [h] at hmh; exact lt_irrefl _ hmh
  have hnL : encodeState mid ∉ positiveBasin e low :=
    fun h => Set.disjoint_left.1 (positiveBasins_disjoint e mid low hnlow) hmm h
  have hnH : encodeState mid ∉ positiveBasin e high :=
    fun h => Set.disjoint_left.1 (positiveBasins_disjoint e mid high hnhigh) hmm h
  exact ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,
    ⟨hcl,fun h => hnL (interior_subset h)⟩,⟨hch,fun h => hnH (interior_subset h)⟩⟩

end CoreCouplingGlobal
