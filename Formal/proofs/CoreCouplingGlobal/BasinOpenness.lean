import proofs.CoreCouplingGlobal.BasinNeighborhoods

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

def HasAttractingNeighborhood (e : ℝ) (s : State) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ → State, IsPositiveTrajectory e X →
    dist (encodeState (X 0)) (encodeState s) < δ →
    Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s))

theorem attracting_neighborhood_from_barrier (e : ℝ) (p : PotentialPrimitives e)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) (s mid : State)
    (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (henergy : statePotential e p s < statePotential e p mid) (hside : s.B ≠ mid.B)
    (hbar : ∀ x : State, InResponseBox x → x.B = mid.B → statePotential e p mid ≤ statePotential e p x)
    (hunique : ∀ w : State, w.Positive → Stationary (flagshipRates e) w →
      w.B ≠ mid.B → (w.B < mid.B ↔ s.B < mid.B) → w = s) : HasAttractingNeighborhood e s := by
  obtain ⟨δ,hδ,hnear⟩ := stationary_selector_neighborhood e p (by linarith) hu s mid hs hss henergy hside
  refine ⟨δ,hδ,?_⟩
  intro X hX hdist
  obtain ⟨hreg,hE,hBs⟩ := hnear (X 0) hdist
  have hbox : ∀ t ∈ Ici (0:ℝ), InResponseBox (X t) :=
    fun t ht => (selection_region_forward e (by linarith) hu X hX hreg t ht).2
  obtain ⟨w,hw,hws,hlim,hwB,hwside⟩ := sublevel_limit_side e p hl hu mid hbar X hX 0
    (by norm_num) hbox hE
  have heq := hunique w hw hws hwB (hwside.trans hBs)
  simpa only [heq] using hlim

/-- Every point whose trajectory tends to a locally attracting equilibrium has
a whole neighborhood of positive initial states with the same limit. -/
theorem basin_neighborhood_of_convergence (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hlocal : HasAttractingNeighborhood e s)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X)
    (hlim : Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℝ → State, IsPositiveTrajectory e Y →
      dist (encodeState (Y 0)) (encodeState (X 0)) < δ →
      Tendsto (fun t => encodeState (Y t)) atTop (𝓝 (encodeState s)) := by
  obtain ⟨r,hr,hattr⟩ := hlocal
  have hevent : ∀ᶠ t in atTop, dist (encodeState (X t)) (encodeState s) < r/2 :=
    hlim.eventually (Metric.ball_mem_nhds _ (by linarith))
  obtain ⟨T,hT,hnear⟩ := (Filter.eventually_ge_atTop (0:ℝ)).and hevent |>.exists
  obtain ⟨δ,hδ,hcont⟩ := positive_trajectories_continuous_initial_data e he hu X hX T hT
    (r/2) (by linarith)
  refine ⟨δ,hδ,?_⟩
  intro Y hY hdist
  have hclose := hcont Y hY hdist
  have hYT : dist (encodeState (Y T)) (encodeState s) < r := by
    have htri := dist_triangle (encodeState (Y T)) (encodeState (X T)) (encodeState s)
    linarith
  have hshift := hattr (fun t => Y (t+T)) (positive_trajectory_time_shift e Y hY T hT)
    (by simpa only [zero_add] using hYT)
  have hmap : Tendsto (fun t => encodeState (Y t)) (Filter.map (fun t : ℝ => t+T) atTop)
      (𝓝 (encodeState s)) := by
    exact (tendsto_map'_iff).2 hshift
  simpa only [map_add_atTop_eq] using hmap

theorem two_outer_attracting_neighborhoods (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      (∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high) ∧
      HasAttractingNeighborhood e low ∧ HasAttractingNeighborhood e high := by
  have he : 0 ≤ e := by linarith
  obtain ⟨p,hp⟩ := extendedPotentialPrimitives_nonempty e he hu
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hbl,hbm,hbh,hall⟩ :=
    exactly_three_bracketed_equilibria e hl hu
  have heq : varyRates e = flagshipRates e := rfl
  rw [heq] at hslo hsm hshi hall
  have hall' : ∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high :=
    fun s hs hss => (hall s hs hss).1
  obtain ⟨hEl,hEh⟩ := bracketed_well_energy e p hl hu low mid high hlo hm hhi hslo hsm hshi hbl hbm hbh hall'
  have hBlo := stationary_B_reverse_order e low mid hlo hslo hsm hlm
  have hBhi := stationary_B_reverse_order e mid high hm hsm hshi hmh
  have hbar : ∀ x : State, InResponseBox x → x.B = mid.B → statePotential e p mid ≤ statePotential e p x :=
    fun x hx hplane => stationary_energy_barrier e p hp he hu mid hm hsm
      (stationary_B_ge_eight e mid hm hsm (by linarith [hbm.2])) x hx hplane
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hall',?_,?_⟩
  · apply attracting_neighborhood_from_barrier e p hl hu low mid hlo hslo hEl (ne_of_gt hBlo) hbar
    intro w hw hws hwB hwside
    rcases hall' w hw hws with h | h | h
    · exact h
    · exact False.elim (hwB (by rw [h]))
    · have hlt : w.B < mid.B := by rw [h]; exact hBhi
      have hbad := hwside.1 hlt
      linarith
  · apply attracting_neighborhood_from_barrier e p hl hu high mid hhi hshi hEh (ne_of_lt hBhi) hbar
    intro w hw hws hwB hwside
    rcases hall' w hw hws with h | h | h
    · have hlt := hwside.2 hBhi
      rw [h] at hlt
      linarith
    · exact False.elim (hwB (by rw [h]))
    · exact h

end CoreCouplingGlobal
