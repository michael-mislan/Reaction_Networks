import proofs.OverlappingSiphonInvasion.NormalizedFlow
import proofs.OverlappingSiphonInvasion.NormalizedGrowth

noncomputable section
open Set
namespace OverlappingSiphonInvasion

abbrev GrowthState := LiftState × ℝ

theorem globally_lipschitz_ode_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (K : NNReal) (hK : LipschitzWith K f) (X Y : ℝ → E)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (f (X t)) t)
    (hY : ∀ t, 0 ≤ t → HasDerivAt Y (f (Y t)) t) (t : ℝ) (ht : 0 ≤ t) :
    dist (X t) (Y t) ≤ dist (X 0) (Y 0)*Real.exp (K*t) := by
  have hh := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f)
    (s := fun _ => univ) (fun _ _ => hK.lipschitzOnWith)
    (fun s hs => (hX s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hX s hs.1).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (fun s hs => (hY s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hY s hs.1).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (le_refl (dist (X 0) (Y 0))) t ⟨ht,le_rfl⟩
  simpa only [sub_zero] using hh

/-- A bounded globally Lipschitz extension of the source lift with one
accumulated-growth coordinate. The vector field is independent of that new
coordinate, which will give exact additive time composition by uniqueness. -/
theorem growth_extension (p : Rates) (ru rv rj R : ℝ) (k : ℕ) :
    ∃ H : LiftState → GrowthState, ∃ K : NNReal, ∃ Ψ : GrowthState → ℝ → GrowthState,
      LipschitzWith K H ∧
      (∀ z, ‖z‖ ≤ max R 1 → H z = (normalizedField p ru rv rj z,normalGrowth p ru rv rj k z)) ∧
      (∀ w, Ψ w 0 = w) ∧
      (∀ w t, HasDerivAt (Ψ w) (H (Ψ w t).1) t) ∧
      (∀ t, 0 ≤ t → Continuous (fun w => Ψ w t)) := by
  let S := max R 1
  have hS : 0 < S := (by norm_num : (0:ℝ) < 1).trans_le (le_max_right _ _)
  let q : ContDiffBump (0:LiftState) := ⟨S,2*S,hS,by linarith⟩
  let H : LiftState → GrowthState := fun z => q z •
    (normalizedField p ru rv rj z,normalGrowth p ru rv rj k z)
  have hs : HasCompactSupport H := q.hasCompactSupport.smul_right
  have hG : ContDiff ℝ 1 (normalGrowth p ru rv rj k) := by
    unfold normalGrowth normalHU normalHV normalHJ privateA privateB sharedC
    fun_prop
  have hd : ContDiff ℝ 1 H := q.contDiff.smul ((normalizedField_contDiff p ru rv rj).prodMk hG)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  let L : NNReal := ⟨max C 0,le_max_right _ _⟩
  let F : GrowthState → GrowthState := fun w => H w.1
  have hF : LipschitzWith K F := by simpa using hK.comp LipschitzWith.prod_fst
  have hL : ∀ w, ‖F w‖ ≤ L := fun w => (hC w.1).trans (le_max_left _ _)
  choose Ψ hΨ0 hΨd using (fun w => CoreCouplingCAC.bounded_lipschitz_global_solution F K L hF hL w)
  refine ⟨H,K,Ψ,hK,?_,hΨ0,hΨd,?_⟩
  · intro z hz
    have hq : q z = 1 := q.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    simp only [H,hq,one_smul]
  · intro t ht
    have hlip : LipschitzWith ⟨Real.exp (K*t),(Real.exp_pos _).le⟩ (fun w => Ψ w t) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      simpa only [hΨ0,mul_comm] using globally_lipschitz_ode_distance F K hF (Ψ z) (Ψ w)
        (fun s _ => hΨd z s) (fun s _ => hΨd w s) t ht
    exact hlip.continuous

end OverlappingSiphonInvasion
