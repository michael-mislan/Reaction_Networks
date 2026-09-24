import proofs.CoreCouplingGlobal.UnstableCoverage
import proofs.CoreCouplingGlobal.ReverseEnergy
import proofs.CoreCouplingGlobal.VectorUniqueness

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

theorem positive_selection_response_box (x : State) (hp : x.Positive)
    (hr : InSelectionRegion x) : InResponseBox x := by
  obtain ⟨hA,hB,hz,hH⟩ := hp
  obtain ⟨hS,hW,hzu,hBl⟩ := hr
  exact ⟨hA.le,by linarith,hBl,by linarith,hz.le,hzu,hH.le,by linarith⟩

theorem middle_physical_selection_neighborhood (e : ℝ) (he : 0 ≤ e)
    (hu : e ≤ 1/50000) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ResponseVector, dist x (encodeState s) < ε →
      InSelectionRegion (decodeState x) := by
  obtain ⟨_hB,hcenter,_hZ⟩ := stationary_response_center e he hu s hs hss
  obtain ⟨ε,hε,hclose⟩ := Metric.continuousAt_iff.1
    (saddleCoordinates_decode_continuous e).continuousAt (1/2) (by norm_num)
  refine ⟨ε,hε,?_⟩
  intro x hx
  apply middle_response_neighborhood_selection_region e s.z he hu hz (decodeState x)
  have hh := hclose hx
  simpa only [decode_encodeState,hcenter] using hh

/-- Actual analytic unstable initial states lie in the certified selection
region, and every nonzero parameter lies strictly below the middle energy.
The same chart retains past coverage and its actual spectral tangent. -/
theorem middle_unstable_patch_sublevel (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (p : PotentialPrimitives e) (s : State) (hs : s.Positive)
    (hss : Stationary (flagshipRates e) s) (hz : s.z ∈ Icc (19/10:ℝ) (21/10))
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) :
    ∃ φ : ℝ → ResponseVector, ∃ U : Set ℝ, ∃ δ : ℝ,
      IsOpen U ∧ 0 ∈ U ∧ 0 < δ ∧ φ 0=encodeState s ∧
      HasFDerivAt φ (C.toContinuousLinearMap.comp unstableInclusion) 0 ∧
      ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
      (∀ a ∈ U, C.symm (φ a-encodeState s) 3=a) ∧
      (∀ a ∈ U, φ a ∈ positiveDomain ∧ InSelectionRegion (decodeState (φ a)) ∧
        (a ≠ 0 → statePotential e p (decodeState (φ a)) < statePotential e p s)) ∧
      (∀ a ∈ U, ∃ Y : ℝ → ResponseVector, Y 0=φ a ∧
        (∀ t, t ≤ 0 → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
        (∀ t, t ≤ 0 → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState s)‖ < δ) ∧
        Tendsto (fun t => Y (-t)) atTop (𝓝 (encodeState s))) ∧
      ∀ Z : ℝ → ResponseVector,
        (∀ t, t ≤ 0 → HasDerivAt Z (responseVectorField e (Z t)) t) →
        (∀ t, t ≤ 0 → ‖C.symm (Z t-encodeState s)‖ < δ) →
        ∀ T, T ≤ 0 → C.symm (Z T-encodeState s) 3 ∈ U →
          Z T=φ (C.symm (Z T-encodeState s) 3) := by
  obtain ⟨ε,hε,hregion⟩ := middle_physical_selection_neighborhood e he hu s hs hss hz
  obtain ⟨φ,U,δ,hU,hU0,hδ,hφ0,hder,hcd,hinj,hleft,htraj,hcoverage⟩ :=
    middle_unstable_patch_coverage e s hs μ C hC ε hε
  refine ⟨φ,U,δ,hU,hU0,hδ,hφ0,hder,hcd,hinj,hleft,?_,?_,hcoverage⟩
  · intro a ha
    obtain ⟨Y,h0,hY,hp,hl⟩ := htraj a ha
    have hreg : ∀ t, t ≤ 0 → InSelectionRegion (decodeState (Y t)) :=
      fun t ht => hregion _ (hp t ht).2.2
    have hbox : ∀ t, t ≤ 0 → InResponseBox (decodeState (Y t)) :=
      fun t ht => positive_selection_response_box _ (hp t ht).1 (hreg t ht)
    refine ⟨by simpa only [h0] using (hp 0 le_rfl).1,
      by simpa only [h0] using hreg 0 le_rfl,?_⟩
    intro hane
    have hne : Y 0 ≠ encodeState s := by
      intro heq
      have hh := hleft a ha
      rw [← h0,heq,sub_self,map_zero] at hh
      exact hane hh.symm
    have hrev : ∀ t, 0 ≤ t → HasDerivAt (fun u => Y (-u))
        (-responseVectorField e (Y (-t))) t := by
      simpa only [zero_sub] using past_trajectory_reversed_shift e Y hY 0 le_rfl
    have hns := reversed_convergent_nonstationary e (fun t => Y (-t)) hrev s hl
      (by simpa only [neg_zero] using hne)
    have henergy := reversed_trajectory_strict_sublevel e p he hu (fun t => Y (-t))
      hrev (fun t ht => hbox (-t) (neg_nonpos.mpr ht)) s
      (positive_stationary_in_responseBox e he hu s hs hss) hl hns
    simpa only [neg_zero,h0] using henergy
  · intro a ha
    obtain ⟨Y,h0,hY,hp,hl⟩ := htraj a ha
    exact ⟨Y,h0,hY,fun t ht => ⟨(hp t ht).1,(hp t ht).2.1⟩,hl⟩

end CoreCouplingGlobal
