import proofs.CoreCouplingGlobal.SelectionRegion

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

def perturbA (s : State) (ε : ℝ) : State := ⟨s.A+ε,s.B,s.z,s.H⟩

/-- A strict energy inequality at a positive equilibrium certifies a whole interval
of distinct positive initial states in the same selection region. -/
theorem sublevel_perturbations (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (s mid : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s)
    (henergy : statePotential e p s < statePotential e p mid) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo (0:ℝ) δ,
      (perturbA s ε).Positive ∧ InSelectionRegion (perturbA s ε) ∧
      statePotential e p (perturbA s ε) < statePotential e p mid ∧
      perturbA s ε ≠ s ∧ (perturbA s ε).B = s.B := by
  have habs := trajectory_eventually_absorbing e he hu (fun _ => s)
    (stationary_positive_trajectory e s hs hss)
  obtain ⟨hS,hW,hz,hB⟩ := habs.exists.choose_spec
  have hv : Continuous (fun ε : ℝ => statePotential e p (perturbA s ε)) := by
    dsimp [statePotential,responsePotential,perturbA]
    fun_prop
  have hzero : statePotential e p (perturbA s 0) = statePotential e p s := by
    congr 1
    cases s
    simp [perturbA]
  have hevent : ∀ᶠ ε in 𝓝 (0:ℝ), statePotential e p (perturbA s ε) < statePotential e p mid :=
    hv.continuousAt.eventually (isOpen_Iio.mem_nhds (by simpa only [hzero] using henergy))
  obtain ⟨η,hη,hηbound⟩ := Metric.eventually_nhds_iff.1 hevent
  refine ⟨min η (34-(s.A+s.B)),lt_min hη (by linarith),?_⟩
  intro ε hε
  have hεη : ε < η := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεS : ε < 34-(s.A+s.B) := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have hV := hηbound (show dist ε 0 < η by simpa [Real.dist_eq,abs_of_pos hε.1] using hεη)
  refine ⟨?_,?_,hV,?_,rfl⟩
  · exact ⟨by dsimp [perturbA]; linarith [hs.1,hε.1],hs.2⟩
  · exact ⟨by dsimp [perturbA]; linarith,hW.le,hz.le,hB.le⟩
  · intro hEq
    have ha := congrArg State.A hEq
    dsimp [perturbA] at ha
    linarith [hε.1]

end CoreCouplingGlobal
