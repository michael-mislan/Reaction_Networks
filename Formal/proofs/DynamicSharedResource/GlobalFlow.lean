import proofs.DynamicSharedResource.BoxFlow

namespace DynamicSharedResource
noncomputable section
open Set Metric

def clip (a : State) : State := fun i => max (-1) (min 1 (a i))

theorem clip_cube (a : State) : InCube 1 (clip a) := by
  intro i
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clip_eq (a : State) (ha : InCube 1 a) : clip a=a := by
  funext i
  have hi := abs_le.mp (ha i)
  simp [clip,min_eq_right hi.2,max_eq_right hi.1]

theorem cube_iff_norm (q : ℝ) (hq : 0 ≤ q) (a : State) :
    InCube q a ↔ ‖a‖ ≤ q := by
  simpa only [InCube,Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hq : ‖a‖ ≤ q ↔ ∀ i, ‖a i‖ ≤ q).symm

theorem clip_lipschitz : LipschitzWith 1 clip := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).2
  intro i
  have h := (((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_min 1).const_max (-1)).dist_le_mul (a i) (b i)
  have hh : dist (clip a i) (clip b i) ≤ dist (a i) (b i) := by
    simpa only [clip,id_eq,NNReal.coe_one,one_mul] using h
  exact hh.trans (dist_le_pi_dist a b i)

theorem cube_global_extension (f : State → State)
    (hf : ContDiffOn ℝ 1 f (closedBall 0 1)) :
    ∃ ext : State → State, (∀ a, InCube 1 a → ext a=f a) ∧
      ∀ a₀, ∃ a : ℝ → State, a 0=a₀ ∧ ∀ t, HasDerivAt a (ext (a t)) t := by
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_closedBall 0 1)
    (isCompact_closedBall 0 1)
  obtain ⟨g,hg,heq⟩ := hK.extend_pi
  let ext : State → State := g ∘ clip
  have hlip : LipschitzWith K ext := by simpa only [mul_one] using hg.comp clip_lipschitz
  have hbound : ∀ a, ‖ext a‖ ≤ (‖g 0‖₊+K : NNReal) := by
    intro a
    have hc : ‖clip a‖ ≤ 1 := (cube_iff_norm 1 (by norm_num) _).mp (clip_cube a)
    have hd := hg.dist_le_mul (clip a) 0
    rw [dist_zero_right] at hd
    have htri : ‖g (clip a)‖ ≤ dist (g (clip a)) (g 0)+‖g 0‖ := by
      simpa only [dist_zero_right] using dist_triangle (g (clip a)) (g 0) 0
    change ‖g (clip a)‖ ≤ ‖g 0‖+(K:ℝ)
    nlinarith [K.coe_nonneg]
  refine ⟨ext,?_,?_⟩
  · intro a ha
    dsimp [ext,Function.comp_def]
    rw [clip_eq a ha]
    exact (heq (by simpa only [mem_closedBall,dist_zero_right] using
      (cube_iff_norm 1 (by norm_num) a).mp ha)).symm
  · intro a₀
    exact CoreCouplingCAC.bounded_lipschitz_global_solution ext K (‖g 0‖₊+K) hlip hbound a₀

theorem exists_captured_solution (f : State → State)
    (hsmooth : ContDiffOn ℝ 1 f (closedBall 0 1)) (hface : FaceDecay f)
    (a₀ : State) (ha₀ : InCube 1 a₀) :
    ∃ a : ℝ → State, a 0=a₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt a (f (a t)) t ∧ InCube 1 (a t)) ∧
      ∀ t, 2000 ≤ t → InCube (1/2) (a t) := by
  obtain ⟨ext,hext,hglobal⟩ := cube_global_extension f hsmooth
  obtain ⟨a,hzero,hd⟩ := hglobal a₀
  have hb := cube_capture f ext hface hext a hd (by simpa only [hzero] using ha₀)
  exact ⟨a,hzero,fun t ht => ⟨hb.2.2 t ht,hb.1 t ht⟩,hb.2.1⟩

end
end DynamicSharedResource
