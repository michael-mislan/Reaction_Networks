import proofs.DynamicSharedResource.FastUniqueness
import proofs.DynamicSharedResource.EnlargedPreparation

namespace DynamicSharedResource.Certificate
noncomputable section

theorem every_fast_source_trajectory (u : ℝ → State)
    (h0 : InRect recoveryR (coordinates (u 0)))
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t) :
    (∀ t, 0 ≤ t → Physical (u t) ∧ InRect recoveryR (coordinates (u t)) ∧
      (207/20:ℝ) ≤ HG (u t) ∧ (391/100:ℝ) ≤ HT (u t)) ∧
    ∀ t, 1/250 ≤ t → InRect serviceR (coordinates (u t)) ∧ (401/100:ℝ) ≤ HT (u t) := by
  let a := fun t => coordinates (u t)
  have ha : ∀ t, 0 ≤ t → HasDerivAt a (modalField (a t)) t := by
    intro t ht
    have h := mulVec_hasDerivAt inverse (fun s => u s-center) (nominal (u t)) t
      ((hu t ht).sub_const center)
    change HasDerivAt (fun s => coordinates (u s))
      (inverse.mulVec (nominal (reconstruct (coordinates (u t))))) t
    rw [reconstruct_coordinates]
    exact h
  have hr := fast_modal_trajectory a ha h0
  constructor
  · intro t ht
    have hp := outer_physical (a t) (fun i => (hr.1 t ht i).trans (rect_radii i).2.2)
    have hs := recovery_outputs (a t) (hr.1 t ht)
    refine ⟨?_,hr.1 t ht,?_⟩
    · simpa only [a,reconstruct_coordinates] using hp
    · simpa only [a,reconstruct_coordinates] using hs
  · intro t ht
    have hs := service_outputs (a t) (hr.2 t ht)
    exact ⟨hr.2 t ht,by simpa only [a,reconstruct_coordinates] using hs.2⟩

/-- The literal source theorem covers the entire correlated recovery rectangle. -/
theorem operational_recovery (u₀ : State) (h₀ : InRect recoveryR (coordinates u₀)) :
    ∃ u : ℝ → State, u 0=u₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t) ∧
      (∀ v : ℝ → State, v 0=u₀ →
        (∀ t, 0 ≤ t → HasDerivAt v (nominal (v t)) t) →
        ∀ t, 0 ≤ t → v t=u t) ∧
      (∀ t, 0 ≤ t → Physical (u t) ∧ InRect recoveryR (coordinates (u t)) ∧
        (207/20:ℝ) ≤ HG (u t) ∧ (391/100:ℝ) ≤ HT (u t)) ∧
      (∀ t, 1/250 ≤ t → InRect serviceR (coordinates (u t)) ∧ (401/100:ℝ) ≤ HT (u t)) := by
  obtain ⟨u,hzero,hflow,_⟩ := fast_source_solution u₀ h₀
  have hu := fun t ht => (hflow t ht).1
  have hp : InRect recoveryR (coordinates (u 0)) := by simpa only [hzero] using h₀
  have hs := every_fast_source_trajectory u hp hu
  refine ⟨u,hzero,hu,?_,hs⟩
  intro v hv0 hv
  exact recovery_source_unique v u (by simpa only [hv0] using h₀)
    (hv0.trans hzero.symm) hv hu

theorem original_preparation_fast (u : ℝ → State) (h0 : Prepared (u 0))
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t) :
    ∀ t, 1/250 ≤ t → (207/20:ℝ) ≤ HG (u t) ∧ (401/100:ℝ) ≤ HT (u t) := by
  have hs := every_fast_source_trajectory u
    (enlarged_prepared_in_recovery (u 0) (old_prepared_enlarged (u 0) h0)) hu
  intro t ht
  exact ⟨(hs.1 t (by linarith)).2.2.1,(hs.2 t ht).2⟩

end
end DynamicSharedResource.Certificate
