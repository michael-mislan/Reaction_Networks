import proofs.OscillatoryCores.LongFlow

namespace OscillatoryCores

open Filter
open scoped NNReal Topology

theorem global_flow_joint_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (hc : ContDiff ℝ 1 f) (M K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ M) (hf : LipschitzWith K f) :
    Continuous (fun p : ℝ × E => BressanJump.globalLipschitzFlow f hc M K hbound hf p.1 p.2) := by
  let Φ := BressanJump.globalLipschitzFlow f hc M K hbound hf
  have htime (x : E) : Continuous (fun t => Φ t x) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (BressanJump.globalLipschitzFlow_isIntegralCurve f hc M K hbound hf x t).continuousAt)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t,x⟩
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  let B : ℝ × E → ℝ := fun p =>
    Real.exp ((K : ℝ)*|p.1|)*dist p.2 x + dist (Φ p.1 x) (Φ t x)
  have hBc : Continuous B := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_fst.abs)).mul
      (continuous_snd.dist continuous_const)).add
        (((htime x).comp continuous_fst).dist continuous_const)
  have hBlim : Tendsto B (𝓝 (t,x)) (𝓝 0) := by simpa [B] using hBc.tendsto (t,x)
  apply squeeze_zero (fun _ => dist_nonneg) (fun p => ?_) hBlim
  calc
    dist (Φ p.1 p.2) (Φ t x) ≤ dist (Φ p.1 p.2) (Φ p.1 x) + dist (Φ p.1 x) (Φ t x) :=
      dist_triangle _ _ _
    _ ≤ B p := add_le_add
      (BressanJump.globalLipschitzFlow_dist_le f hc M K hbound hf p.1 p.2 x) le_rfl

end OscillatoryCores
