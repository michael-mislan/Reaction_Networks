import proofs.CoreCouplingGlobal.UnstableSublevel
import proofs.CoreCouplingGlobal.UnstableSides

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

theorem sublevel_signed_initial_destinations (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) (p : PotentialPrimitives e) (low mid high : State)
    (hBlo : mid.B < low.B) (hBhi : high.B < mid.B)
    (hall : ∀ s : State, s.Positive → Stationary (flagshipRates e) s →
      s=low ∨ s=mid ∨ s=high)
    (hbar : ∀ x : State, InResponseBox x → x.B=mid.B → statePotential e p mid ≤ statePotential e p x)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X)
    (hreg : InSelectionRegion (X 0))
    (henergy : statePotential e p (X 0) < statePotential e p mid) :
    (mid.B < (X 0).B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low))) ∧
    ((X 0).B < mid.B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high))) := by
  have hbox : ∀ t ∈ Ici (0:ℝ), InResponseBox (X t) :=
    fun t ht => (selection_region_forward e (by linarith) hu X hX hreg t ht).2
  obtain ⟨s,hs,hss,hlim,hsne,hside⟩ := sublevel_limit_side e p hl hu mid hbar X hX 0
    (by norm_num) hbox henergy
  constructor
  · intro hB
    rcases hall s hs hss with h | h | h
    · simpa only [h] using hlim
    · exact False.elim (hsne (by rw [h]))
    · have hh := hside.1 (by simpa only [h] using hBhi)
      linarith
  · intro hB
    have hh := hside.2 hB
    rcases hall s hs hss with h | h | h
    · rw [h] at hh
      linarith
    · exact False.elim (hsne (by rw [h]))
    · simpa only [h] using hlim

/-- Actual local unstable branches of the flagship middle saddle have opposite
outer destinations. Both the backward paths and global positive forward paths
are constructed; no eigenvector seed or assumed unstable manifold is used. -/
theorem middle_actual_unstable_branch_destinations (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
      MiddlePerronCoordinates e mid μ C ∧ ∃ φ : ℝ → ResponseVector, ∃ r δ b : ℝ,
        0 < r ∧ 0 < δ ∧ b ≠ 0 ∧ b=C (unstableInclusion 1) 1 ∧ φ 0=encodeState mid ∧
        HasFDerivAt φ (C.toContinuousLinearMap.comp unstableInclusion) 0 ∧
        ContDiffOn ℝ ω φ (Ioo (-r) r) ∧ InjOn φ (Ioo (-r) r) ∧
        (∀ a ∈ Ioo (-r) r, C.symm (φ a-encodeState mid) 3=a) ∧
        (∀ a ∈ Ioo (-r) r, ∃ Y : ℝ → ResponseVector, Y 0=φ a ∧
          (∀ t, t ≤ 0 → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
          (∀ t, t ≤ 0 → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState mid)‖ < δ) ∧
          Tendsto (fun t => Y (-t)) atTop (𝓝 (encodeState mid))) ∧
        (∀ a ∈ Ioo (-r) r, a ≠ 0 → ∃ X : ℝ → State,
          X 0=decodeState (φ a) ∧ IsPositiveTrajectory e X ∧
          (0 < a*b → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low))) ∧
          (a*b < 0 → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high)))) ∧
        ∀ Z : ℝ → ResponseVector,
          (∀ t, t ≤ 0 → HasDerivAt Z (responseVectorField e (Z t)) t) →
          (∀ t, t ≤ 0 → ‖C.symm (Z t-encodeState mid)‖ < δ) →
          ∀ T, T ≤ 0 → C.symm (Z T-encodeState mid) 3 ∈ Ioo (-r) r →
            Z T=φ (C.symm (Z T-encodeState mid) 3) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨p,hp⟩ := extendedPotentialPrimitives_nonempty e he hu
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,_hbl,hbm,_hbh,hall⟩ :=
    exactly_three_bracketed_equilibria e hl hu
  have heq : varyRates e=flagshipRates e := rfl
  rw [heq] at hslo hsm hshi hall
  obtain ⟨μ,C,hstable,hu0,_hu1,hcoord⟩ := middle_exact_quadratic_coordinates e he hu mid hm hsm hbm
  let hC : MiddlePerronCoordinates e mid μ C := ⟨hstable,hu0,hcoord⟩
  obtain ⟨φ,U,δ,hU,hU0,hδ,hφ0,hder,hcd,hinj,hleft,henergy,hpast,hcoverage⟩ :=
    middle_unstable_patch_sublevel e he hu p mid hm hsm hbm μ C hC
  obtain ⟨hb,hside⟩ := physical_unstable_chart_sides e he mid hm hsm μ C hC φ hφ0 hder
  let b := C (unstableInclusion 1) 1
  change b ≠ 0 at hb
  change ∀ᶠ a in 𝓝 (0:ℝ), a ≠ 0 → 0 < (φ a 1-mid.B)*(a*b) at hside
  have hUnhds : ∀ᶠ a in 𝓝 (0:ℝ), a ∈ U := hU.mem_nhds hU0
  have hboth : ∀ᶠ a in 𝓝 (0:ℝ), a ∈ U ∧ (a ≠ 0 → 0 < (φ a 1-mid.B)*(a*b)) :=
    hUnhds.and hside
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.1 hboth
  have hsmall : ∀ a ∈ Ioo (-r) r, a ∈ U ∧ (a ≠ 0 → 0 < (φ a 1-mid.B)*(a*b)) := by
    intro a ha
    apply hball
    simpa [Metric.mem_ball,Real.dist_eq] using abs_lt.mpr ha
  have hBlo := stationary_B_reverse_order e low mid hlo hslo hsm hlm
  have hBhi := stationary_B_reverse_order e mid high hm hsm hshi hmh
  have hbar : ∀ x : State, InResponseBox x → x.B=mid.B → statePotential e p mid ≤ statePotential e p x :=
    stationary_energy_barrier e p hp he hu mid hm hsm
      (stationary_B_ge_eight e mid hm hsm (by linarith [hbm.2]))
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,μ,C,hC,φ,r,δ,b,
    hr,hδ,hb,rfl,hφ0,hder,hcd.mono (fun a ha => (hsmall a ha).1),
    hinj.mono (fun a ha => (hsmall a ha).1),
    fun a ha => hleft a (hsmall a ha).1,fun a ha => hpast a (hsmall a ha).1,?_,?_⟩
  · intro a ha hane
    obtain ⟨hpos,hreg,hE⟩ := henergy a (hsmall a ha).1
    obtain ⟨X,h0,hX⟩ := positive_global_solution e he hu (decodeState (φ a)) hpos
    have hdest := sublevel_signed_initial_destinations e hl hu p low mid high hBlo hBhi
      (fun s hs hss => (hall s hs hss).1) hbar X hX
      (by simpa only [h0] using hreg) (by simpa only [h0] using hE hane)
    have hsign := (hsmall a ha).2 hane
    refine ⟨X,h0,hX,?_,?_⟩
    · intro hab
      apply hdest.1
      rw [h0]
      change mid.B < φ a 1
      have hh := (mul_pos_iff.mp hsign)
      rcases hh with hh | hh
      · linarith [hh.1]
      · linarith [hh.2]
    · intro hab
      apply hdest.2
      rw [h0]
      change φ a 1 < mid.B
      rcases mul_pos_iff.mp hsign with hh | hh
      · linarith [hh.2]
      · linarith [hh.1]
  · intro Z hZ hZt T hT hproj
    exact hcoverage Z hZ hZt T hT (hsmall _ hproj).1

end CoreCouplingGlobal
