import proofs.CoreCouplingGlobal.BasinOpenness

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem encode_decodeState (x : ResponseVector) : encodeState (decodeState x) = x := by
  funext i
  fin_cases i <;> rfl

def positiveDomain : Set ResponseVector := {x | (decodeState x).Positive}

theorem positiveDomain_isOpen : IsOpen positiveDomain := by
  change IsOpen ({x : ResponseVector | 0 < x 0} ∩
    ({x : ResponseVector | 0 < x 1} ∩ ({x : ResponseVector | 0 < x 2} ∩ {x : ResponseVector | 0 < x 3})))
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter (isOpen_lt continuous_const (continuous_apply 3))))

def positiveBasin (e : ℝ) (s : State) : Set ResponseVector :=
  {x | ∃ X : ℝ → State, IsPositiveTrajectory e X ∧ X 0 = decodeState x ∧
    Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s))}

theorem positiveBasin_subset_domain (e : ℝ) (s : State) : positiveBasin e s ⊆ positiveDomain := by
  rintro x ⟨X,hX,h0,_⟩
  have hp := hX.positive 0 (by norm_num)
  simpa only [h0] using hp

theorem positiveBasin_isOpen (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hlocal : HasAttractingNeighborhood e s) : IsOpen (positiveBasin e s) := by
  apply Metric.isOpen_iff.2
  rintro x hx
  obtain ⟨X,hX,hX0,hlim⟩ := hx
  obtain ⟨δ,hδ,hnear⟩ := basin_neighborhood_of_convergence e he hu s hlocal X hX hlim
  have hxD : x ∈ positiveDomain := positiveBasin_subset_domain e s ⟨X,hX,hX0,hlim⟩
  obtain ⟨r,hr,hrball⟩ := Metric.isOpen_iff.1 positiveDomain_isOpen x hxD
  refine ⟨min δ r,lt_min hδ hr,?_⟩
  intro y hy
  have hyd : dist y x < min δ r := hy
  have hyD : y ∈ positiveDomain := hrball (lt_of_lt_of_le hyd (min_le_right _ _))
  obtain ⟨Y,hY0,hY⟩ := positive_global_solution e he hu (decodeState y) hyD
  refine ⟨Y,hY,hY0,hnear Y hY ?_⟩
  rw [hY0,hX0,encode_decodeState,encode_decodeState]
  exact lt_of_lt_of_le hyd (min_le_left _ _)

theorem positiveBasins_disjoint (e : ℝ) (s w : State) (hsw : s ≠ w) :
    Disjoint (positiveBasin e s) (positiveBasin e w) := by
  apply Set.disjoint_left.2
  rintro x ⟨X,hX,hX0,hXs⟩ ⟨Y,hY,hY0,hYw⟩
  have heq := positive_trajectory_unique e X Y hX hY (hX0.trans hY0.symm)
  have hevent : (fun t => encodeState (X t)) =ᶠ[atTop] (fun t => encodeState (Y t)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [heq t ht]
  have hXw := hYw.congr' hevent.symm
  have hv := tendsto_nhds_unique hXs hXw
  have hsw' := congrArg decodeState hv
  exact hsw (by simpa only [decode_encodeState] using hsw')

theorem positive_basin_partition (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (low mid high : State)
    (hall : ∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high) :
    ∀ x ∈ positiveDomain, x ∈ positiveBasin e low ∨ x ∈ positiveBasin e mid ∨ x ∈ positiveBasin e high := by
  intro x hx
  obtain ⟨X,hX0,hX⟩ := positive_global_solution e (by linarith) hu (decodeState x) hx
  obtain ⟨s,hs,hss,hlim⟩ := trajectory_converges_to_positive_equilibrium e hl hu X hX
  rcases hall s hs hss with heq | heq | heq
  · exact Or.inl ⟨X,hX,hX0,by simpa only [heq] using hlim⟩
  · exact Or.inr (Or.inl ⟨X,hX,hX0,by simpa only [heq] using hlim⟩)
  · exact Or.inr (Or.inr ⟨X,hX,hX0,by simpa only [heq] using hlim⟩)

theorem frontier_in_third_of_open_partition {D A B C : Set ResponseVector}
    (hA : IsOpen A) (hB : IsOpen B) (hdis : Disjoint A B)
    (hcover : ∀ x ∈ D, x ∈ A ∨ x ∈ B ∨ x ∈ C) : frontier A ∩ D ⊆ C := by
  rintro x ⟨hxF,hxD⟩
  rcases hcover x hxD with hxA | hxB | hxC
  · have hn : x ∉ interior A := hxF.2
    exact False.elim (hn (by simpa only [hA.interior_eq] using hxA))
  · obtain ⟨y,hyB,hyA⟩ := mem_closure_iff.1 (frontier_subset_closure hxF) B hB hxB
    exact False.elim (Set.disjoint_left.1 hdis hyA hyB)
  · exact hxC

/-- The two outer basins are disjoint and open. Their positive-domain boundary
points converge to the middle equilibrium. The reverse inclusion is not asserted. -/
theorem outer_basin_boundary_in_middle (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      IsOpen (positiveBasin e low) ∧ IsOpen (positiveBasin e high) ∧
      Disjoint (positiveBasin e low) (positiveBasin e high) ∧
      (frontier (positiveBasin e low) ∩ positiveDomain ⊆ positiveBasin e mid) ∧
      (frontier (positiveBasin e high) ∩ positiveDomain ⊆ positiveBasin e mid) := by
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hall,hlattr,hhattr⟩ :=
    two_outer_attracting_neighborhoods e hl hu
  have hlopen := positiveBasin_isOpen e (by linarith) hu low hlattr
  have hhopen := positiveBasin_isOpen e (by linarith) hu high hhattr
  have hne : low ≠ high := by intro heq; have hh := hlm.trans hmh; rw [heq] at hh; exact lt_irrefl _ hh
  have hdis := positiveBasins_disjoint e low high hne
  have hpart := positive_basin_partition e hl hu low mid high hall
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hlopen,hhopen,hdis,?_,?_⟩
  · apply frontier_in_third_of_open_partition hlopen hhopen hdis
    intro x hx
    rcases hpart x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · apply frontier_in_third_of_open_partition hhopen hlopen hdis.symm
    intro x hx
    rcases hpart x hx with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

end CoreCouplingGlobal
