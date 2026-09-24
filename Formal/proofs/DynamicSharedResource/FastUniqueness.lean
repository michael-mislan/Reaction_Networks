import proofs.DynamicSharedResource.FastRecovery

namespace DynamicSharedResource.Certificate
noncomputable section
open Set Metric

theorem recovery_source_unique (u v : ℝ → State)
    (h0 : InRect recoveryR (coordinates (u 0))) (hinit : u 0 = v 0)
    (hu : ∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t)
    (hv : ∀ t, 0 ≤ t → HasDerivAt v (nominal (v t)) t) :
    ∀ t, 0 ≤ t → u t = v t := by
  let a := fun t => coordinates (u t)
  let b := fun t => coordinates (v t)
  have transform (w : ℝ → State)
      (hw : ∀ t, 0 ≤ t → HasDerivAt w (nominal (w t)) t) :
      ∀ t, 0 ≤ t → HasDerivAt (fun s => coordinates (w s))
        (modalField (coordinates (w t))) t := by
    intro t ht
    have h := mulVec_hasDerivAt inverse (fun s => w s-center) (nominal (w t)) t
      ((hw t ht).sub_const center)
    change HasDerivAt (fun s => coordinates (w s))
      (inverse.mulVec (nominal (reconstruct (coordinates (w t))))) t
    rw [reconstruct_coordinates]
    exact h
  have ha := transform u hu
  have hb := transform v hv
  have outer (w : ℝ → State) (hw0 : InCube 1 (w 0))
      (hw : ∀ t, 0 ≤ t → HasDerivAt w (modalField (w t)) t) :
      ∀ t, 0 ≤ t → w t ∈ closedBall (0:State) 1 := by
    intro t ht
    have hc := moving_cube modalField nominal_face_decay w (fun s => modalField (w s))
      0 t (fun _ => 1) (fun _ => 0) (fun s hs => hw s hs.1)
      (fun _ _ _ => rfl) (by intro s hs; norm_num)
      (fun s _ => hasDerivAt_const s 1) (by intro s hs; norm_num)
      hw0 t ⟨ht,le_rfl⟩
    simpa only [mem_closedBall,dist_zero_right] using
      (cube_iff_norm 1 (by norm_num) (w t)).mp hc
  have hao := outer a (fun i => (h0 i).trans (rect_radii i).2.2) ha
  have hbo := outer b (by
    change InCube 1 (coordinates (v 0))
    rw [← hinit]
    exact fun i => (h0 i).trans (rect_radii i).2.2) hb
  obtain ⟨K,hK⟩ := modal_smooth.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall 0 1) (isCompact_closedBall 0 1)
  intro t ht
  have he := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => modalField) (s := fun _ => closedBall (0:State) 1)
    (a := 0) (b := t) (K := K)
    (fun _ _ => hK)
    (fun s hs => (ha s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (ha s hs.1).hasDerivWithinAt)
    (fun s hs => hao s hs.1)
    (fun s hs => (hb s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hb s hs.1).hasDerivWithinAt)
    (fun s hs => hbo s hs.1)
    (congrArg coordinates hinit) ⟨ht,le_rfl⟩
  have hr := congrArg reconstruct he
  simpa only [reconstruct_coordinates] using hr

end
end DynamicSharedResource.Certificate
