import proofs.CoreCouplingGlobal.MiddleCurve

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

def strictSelectionDomain : Set ResponseVector := positiveDomain ∩
  ({x | x 0+x 1 < 34} ∩ ({x | x 2+(7/4:ℝ)*x 3 < 384} ∩ ({x | x 2 < 12} ∩ {x | 2 < x 1})))

theorem strictSelectionDomain_isOpen : IsOpen strictSelectionDomain := by
  exact positiveDomain_isOpen.inter ((isOpen_lt (by fun_prop) continuous_const).inter
    ((isOpen_lt (by fun_prop) continuous_const).inter
      ((isOpen_lt (continuous_apply 2) continuous_const).inter (isOpen_lt continuous_const (continuous_apply 1)))))

theorem stationary_curve_admissible (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, dist z s.z < δ →
      (responseCurveState e z).Positive ∧ InSelectionRegion (responseCurveState e z) := by
  have habs := trajectory_eventually_absorbing e he hu (fun _ => s)
    (stationary_positive_trajectory e s hs hss)
  obtain ⟨hS,hW,hz,hB⟩ := habs.exists.choose_spec
  have hm : encodeState s ∈ strictSelectionDomain := by
    exact ⟨by simpa only [positiveDomain,Set.mem_setOf_eq,decode_encodeState] using hs,hS,hW,hz,hB⟩
  have hcurve := responseCurveState_continuousAt e s.z hs.2.2.1.le
  have hcenter := responseCurveState_stationary e he hu s hs hss
  have hev : ∀ᶠ z in 𝓝 s.z, encodeState (responseCurveState e z) ∈ strictSelectionDomain :=
    hcurve.eventually (strictSelectionDomain_isOpen.mem_nhds (by simpa only [hcenter] using hm))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ,hδ,?_⟩
  intro z hz
  obtain ⟨hp,hS,hW,hz',hB⟩ := hball hz
  refine ⟨?_,hS.le,hW.le,hz'.le,hB.le⟩
  simpa only [positiveDomain,Set.mem_setOf_eq,decode_encodeState] using hp

theorem responseCurve_B_reverse {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    60/(y+2) < 60/(x+2) := by
  apply (div_lt_div_iff₀ (by linarith : 0 < y+2) (by linarith : 0 < x+2)).2
  linarith

theorem sublevel_outer_basin_membership (e : ℝ) (p : PotentialPrimitives e)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) (low mid high : State)
    (hBlo : mid.B < low.B) (hBhi : high.B < mid.B)
    (hall : ∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high)
    (hbar : ∀ x : State, InResponseBox x → x.B = mid.B → statePotential e p mid ≤ statePotential e p x)
    (x : State) (hx : x.Positive) (hreg : InSelectionRegion x)
    (henergy : statePotential e p x < statePotential e p mid) :
    (x.B < mid.B → encodeState x ∈ positiveBasin e high) ∧
    (mid.B < x.B → encodeState x ∈ positiveBasin e low) := by
  obtain ⟨X,hX0,hX⟩ := positive_global_solution e (by linarith) hu x hx
  have hbox : ∀ t ∈ Ici (0:ℝ), InResponseBox (X t) :=
    fun t ht => (selection_region_forward e (by linarith) hu X hX (by simpa only [hX0] using hreg) t ht).2
  obtain ⟨s,hs,hss,hlim,hsne,hside⟩ := sublevel_limit_side e p hl hu mid hbar X hX 0
    (by norm_num) hbox (by simpa only [hX0] using henergy)
  rw [hX0] at hside
  have hinit : X 0 = decodeState (encodeState x) := by simpa only [decode_encodeState] using hX0
  constructor
  · intro hlt
    have hsl := hside.2 hlt
    rcases hall s hs hss with h | h | h
    · rw [h] at hsl
      linarith
    · exact False.elim (hsne (by rw [h]))
    · exact ⟨X,hX,hinit,by simpa only [h] using hlim⟩
  · intro hgt
    rcases hall s hs hss with h | h | h
    · exact ⟨X,hX,hinit,by simpa only [h] using hlim⟩
    · exact False.elim (hsne (by rw [h]))
    · have hsl : s.B < mid.B := by rw [h]; exact hBhi
      have hbad := hside.1 hsl
      linarith

end CoreCouplingGlobal
