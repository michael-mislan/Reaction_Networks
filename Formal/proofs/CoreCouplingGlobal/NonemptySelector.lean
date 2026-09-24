import proofs.CoreCouplingGlobal.WellEnergy
import proofs.CoreCouplingGlobal.SublevelPerturbation

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

/-- Both sides contain intervals of distinct initial concentrations below the
same classified middle barrier. The energy comparison is exact, not quadrature. -/
theorem two_nonempty_sublevel_families (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ p : PotentialPrimitives e, ∃ low mid high : State,
      low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      (∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high) ∧
      (∀ x : State, InResponseBox x → x.B = mid.B → statePotential e p mid ≤ statePotential e p x) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo (0:ℝ) δ,
        (perturbA low ε).Positive ∧ InSelectionRegion (perturbA low ε) ∧
        statePotential e p (perturbA low ε) < statePotential e p mid ∧ perturbA low ε ≠ low ∧
        mid.B < (perturbA low ε).B ∧
        (perturbA high ε).Positive ∧ InSelectionRegion (perturbA high ε) ∧
        statePotential e p (perturbA high ε) < statePotential e p mid ∧ perturbA high ε ≠ high ∧
        (perturbA high ε).B < mid.B := by
  have he : 0 ≤ e := by linarith
  obtain ⟨p,hp⟩ := extendedPotentialPrimitives_nonempty e he hu
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hbl,hbm,hbh,hall⟩ :=
    exactly_three_bracketed_equilibria e hl hu
  have heq : varyRates e = flagshipRates e := rfl
  rw [heq] at hslo hsm hshi hall
  have hall' : ∀ s : State, s.Positive → Stationary (flagshipRates e) s → s = low ∨ s = mid ∨ s = high :=
    fun s hs hss => (hall s hs hss).1
  obtain ⟨hEl,hEh⟩ := bracketed_well_energy e p hl hu low mid high hlo hm hhi hslo hsm hshi hbl hbm hbh hall'
  obtain ⟨δl,hδl,hpl⟩ := sublevel_perturbations e p he hu low mid hlo hslo hEl
  obtain ⟨δh,hδh,hph⟩ := sublevel_perturbations e p he hu high mid hhi hshi hEh
  have hBlo := stationary_B_reverse_order e low mid hlo hslo hsm hlm
  have hBhi := stationary_B_reverse_order e mid high hm hsm hshi hmh
  refine ⟨p,low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hall',?_,
    min δl δh,lt_min hδl hδh,?_⟩
  · intro x hx hplane
    exact stationary_energy_barrier e p hp he hu mid hm hsm
      (stationary_B_ge_eight e mid hm hsm (by linarith [hbm.2])) x hx hplane
  · intro ε hε
    obtain ⟨hlp,hlr,hle,hln,hlB⟩ := hpl ε ⟨hε.1,lt_of_lt_of_le hε.2 (min_le_left _ _)⟩
    obtain ⟨hhp,hhr,hhe,hhn,hhB⟩ := hph ε ⟨hε.1,lt_of_lt_of_le hε.2 (min_le_right _ _)⟩
    exact ⟨hlp,hlr,hle,hln,by rw [hlB]; exact hBlo,hhp,hhr,hhe,hhn,by rw [hhB]; exact hBhi⟩

/-- The nonempty families are selected by the literal dynamics, not merely
classified by an energy inequality. -/
theorem nontrivial_selected_families (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ low high : State, low.Positive ∧ high.Positive ∧ low.z < high.z ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo (0:ℝ) δ,
        (perturbA low ε).Positive ∧ perturbA low ε ≠ low ∧
        (perturbA high ε).Positive ∧ perturbA high ε ≠ high ∧
        (∀ X : ℝ → State, IsPositiveTrajectory e X → X 0 = perturbA low ε →
          Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low))) ∧
        (∀ X : ℝ → State, IsPositiveTrajectory e X → X 0 = perturbA high ε →
          Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high))) := by
  obtain ⟨p,low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hall,hbar,δ,hδ,hfam⟩ :=
    two_nonempty_sublevel_families e hl hu
  have hBlo := stationary_B_reverse_order e low mid hlo hslo hsm hlm
  have hBhi := stationary_B_reverse_order e mid high hm hsm hshi hmh
  refine ⟨low,high,hlo,hhi,hlm.trans hmh,δ,hδ,?_⟩
  intro ε hε
  obtain ⟨hlp,hlr,hle,hln,hlB,hhp,hhr,hhe,hhn,hhB⟩ := hfam ε hε
  refine ⟨hlp,hln,hhp,hhn,?_,?_⟩
  · intro X hX h0
    have hreg : InSelectionRegion (X 0) := by simpa only [h0] using hlr
    have hbox : ∀ t ∈ Ici (0:ℝ), InResponseBox (X t) :=
      fun t ht => (selection_region_forward e (by linarith) hu X hX hreg t ht).2
    obtain ⟨s,hs,hss,hlim,hsne,hside⟩ := sublevel_limit_side e p hl hu mid hbar X hX 0
      (by norm_num) hbox (by simpa only [h0] using hle)
    rcases hall s hs hss with h | h | h
    · simpa only [h] using hlim
    · exact False.elim (hsne (by rw [h]))
    · have hlt : s.B < mid.B := by rw [h]; exact hBhi
      have hbad := hside.1 hlt
      rw [h0] at hbad
      linarith
  · intro X hX h0
    have hreg : InSelectionRegion (X 0) := by simpa only [h0] using hhr
    have hbox : ∀ t ∈ Ici (0:ℝ), InResponseBox (X t) :=
      fun t ht => (selection_region_forward e (by linarith) hu X hX hreg t ht).2
    obtain ⟨s,hs,hss,hlim,hsne,hside⟩ := sublevel_limit_side e p hl hu mid hbar X hX 0
      (by norm_num) hbox (by simpa only [h0] using hhe)
    have hslt := hside.2 (by simpa only [h0] using hhB)
    rcases hall s hs hss with h | h | h
    · rw [h] at hslt
      linarith
    · exact False.elim (hsne (by rw [h]))
    · simpa only [h] using hlim

end CoreCouplingGlobal
