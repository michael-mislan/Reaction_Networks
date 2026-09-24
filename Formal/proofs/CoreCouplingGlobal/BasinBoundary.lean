import proofs.CoreCouplingGlobal.FinitePullback

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem positive_basin_at_initial_of_endpoint (e : ℝ) (s : State)
    (Y : ℝ → State) (hY : IsPositiveTrajectory e Y) (T : ℝ) (hT : 0 ≤ T)
    (hend : encodeState (Y T) ∈ positiveBasin e s) :
    encodeState (Y 0) ∈ positiveBasin e s := by
  obtain ⟨Z,hZ,hZ0,hlim⟩ := hend
  have hinit : (fun t => Y (t+T)) 0 = Z 0 := by
    simpa only [zero_add,decode_encodeState] using hZ0.symm
  have heq := positive_trajectory_unique e (fun t => Y (t+T)) Z
    (positive_trajectory_time_shift e Y hY T hT) hZ hinit
  have hshift : Tendsto (fun t => encodeState (Y (t+T))) atTop (𝓝 (encodeState s)) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact congrArg encodeState (heq t ht).symm
  have hback := hshift.comp (tendsto_atTop_add_const_right atTop (-T) tendsto_id)
  refine ⟨Y,hY,(decode_encodeState (Y 0)).symm,?_⟩
  simpa only [Function.comp_def,neg_add_cancel_right] using hback

theorem positive_basin_closure_pullback (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (X : ℝ → State) (hX : IsPositiveTrajectory e X)
    (T : ℝ) (hT : 0 ≤ T)
    (hend : encodeState (X T) ∈ closure (positiveBasin e s)) :
    encodeState (X 0) ∈ closure (positiveBasin e s) := by
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨δ,hδ,hpull⟩ := positive_trajectory_finite_pullback e he hu X hX T hT ε hε
  obtain ⟨z,hz,hzδ⟩ := Metric.mem_closure_iff.1 hend δ hδ
  obtain ⟨Y,hY,hYT,hYε⟩ := hpull (decodeState z) (by
    simpa only [encode_decodeState,dist_comm] using hzδ)
  have hYe : encodeState (Y T) ∈ positiveBasin e s := by
    simpa only [hYT,encode_decodeState] using hz
  exact ⟨encodeState (Y 0),positive_basin_at_initial_of_endpoint e s Y hY T hT hYe,
    by simpa only [dist_comm] using hYε⟩

theorem middle_basin_in_both_frontiers (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      positiveBasin e mid ⊆ frontier (positiveBasin e low) ∩ frontier (positiveBasin e high) := by
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,htail⟩ :=
    middle_trajectory_eventually_two_basin_closures e hl hu
  have hlne : low ≠ mid := by intro h; rw [h] at hlm; exact lt_irrefl _ hlm
  have hhne : high ≠ mid := by intro h; rw [h] at hmh; exact lt_irrefl _ hmh
  have hdl := positiveBasins_disjoint e low mid hlne
  have hdh := positiveBasins_disjoint e high mid hhne
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,?_⟩
  intro x hx
  obtain ⟨X,hX,hX0,hlim⟩ := hx
  obtain ⟨T,hT,hclose⟩ := htail X hX hlim
  have hcl := positive_basin_closure_pullback e (by linarith) hu low X hX T hT (hclose T le_rfl).1
  have hch := positive_basin_closure_pullback e (by linarith) hu high X hX T hT (hclose T le_rfl).2
  rw [hX0,encode_decodeState] at hcl hch
  have hxmid : x ∈ positiveBasin e mid := ⟨X,hX,hX0,hlim⟩
  exact ⟨⟨hcl,fun hi => Set.disjoint_left.1 hdl (interior_subset hi) hxmid⟩,
    ⟨hch,fun hi => Set.disjoint_left.1 hdh (interior_subset hi) hxmid⟩⟩

theorem ordered_equilibrium_triple_identification (a b c u v w : State)
    (hab : a.z < b.z) (hbc : b.z < c.z) (huv : u.z < v.z) (hvw : v.z < w.z)
    (hu : u = a ∨ u = b ∨ u = c) (hv : v = a ∨ v = b ∨ v = c)
    (hw : w = a ∨ w = b ∨ w = c) : u = a ∧ v = b ∧ w = c := by
  rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl
  all_goals first | exact ⟨rfl,rfl,rfl⟩ | exfalso; linarith

/-- Throughout the flagship interval, each outer basin has the middle basin as
its entire boundary inside the positive physical concentration domain. -/
theorem outer_basin_boundaries_equal_middle (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      IsOpen (positiveBasin e low) ∧ IsOpen (positiveBasin e high) ∧
      Disjoint (positiveBasin e low) (positiveBasin e high) ∧
      frontier (positiveBasin e low) ∩ positiveDomain = positiveBasin e mid ∧
      frontier (positiveBasin e high) ∩ positiveDomain = positiveBasin e mid := by
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hall,hlattr,hhattr⟩ :=
    two_outer_attracting_neighborhoods e hl hu
  obtain ⟨u,v,w,huP,hvP,hwP,huS,hvS,hwS,huv,hvw,hrev⟩ :=
    middle_basin_in_both_frontiers e hl hu
  obtain ⟨heu,hev,hew⟩ := ordered_equilibrium_triple_identification low mid high u v w hlm hmh huv hvw
    (hall u huP huS) (hall v hvP hvS) (hall w hwP hwS)
  subst u
  subst v
  subst w
  have hlopen := positiveBasin_isOpen e (by linarith) hu low hlattr
  have hhopen := positiveBasin_isOpen e (by linarith) hu high hhattr
  have hne : low ≠ high := by intro h; have hh := hlm.trans hmh; rw [h] at hh; exact lt_irrefl _ hh
  have hdis := positiveBasins_disjoint e low high hne
  have hpart := positive_basin_partition e hl hu low mid high hall
  have hfl : frontier (positiveBasin e low) ∩ positiveDomain ⊆ positiveBasin e mid := by
    apply frontier_in_third_of_open_partition hlopen hhopen hdis
    intro x hx
    rcases hpart x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hfh : frontier (positiveBasin e high) ∩ positiveDomain ⊆ positiveBasin e mid := by
    apply frontier_in_third_of_open_partition hhopen hlopen hdis.symm
    intro x hx
    rcases hpart x hx with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hlopen,hhopen,hdis,
    Set.Subset.antisymm hfl ?_,Set.Subset.antisymm hfh ?_⟩
  · intro x hx
    exact ⟨(hrev hx).1,positiveBasin_subset_domain e mid hx⟩
  · intro x hx
    exact ⟨(hrev hx).2,positiveBasin_subset_domain e mid hx⟩

end CoreCouplingGlobal
