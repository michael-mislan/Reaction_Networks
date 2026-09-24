import proofs.OscillatoryCores.JointFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace OscillatoryCores

open Set Function
open scoped NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
private theorem compact_nnnorm_bound
    {F : Type*} [NormedAddCommGroup F] {g : E → F}
    (hg : HasCompactSupport g) (hc : Continuous g) :
    ∃ M : ℝ≥0, ∀ x, ‖g x‖₊ ≤ M := by
  obtain ⟨C,hC⟩ := hg.exists_bound_of_continuous hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  exact ⟨⟨C,hC0⟩,fun x => by exact_mod_cast hC x⟩

theorem compact_field_lipschitz (f : E → E) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : ∃ K : ℝ≥0, LipschitzWith K f := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  obtain ⟨K,hK⟩ := compact_nnnorm_bound (hs.fderiv ℝ) hd.continuous
  exact ⟨K,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) hK⟩

/-- A smooth compactly supported field produces actual global trajectories
with C1 dependence on initial data at every nonnegative time. -/
theorem compact_field_c1_flow [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∃ Φ : ℝ → E → E,
      (∀ x, Φ 0 x = x) ∧
      (∀ x t, HasDerivAt (fun s => Φ s x) (f (Φ t x)) t) ∧
      (∀ T : ℝ≥0, ContDiff ℝ 1 (Φ T)) ∧
      (∀ s t x, Φ s (Φ t x) = Φ (t+s) x) ∧
      Continuous (fun p : ℝ × E => Φ p.1 p.2) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hd.fderiv_right (by simp)
  obtain ⟨M,hM⟩ := compact_nnnorm_bound hs hf.continuous
  have hsd : HasCompactSupport (fderiv ℝ f) := hs.fderiv ℝ
  have hsdd : HasCompactSupport (fderiv ℝ (fderiv ℝ f)) := hsd.fderiv ℝ
  obtain ⟨K,hK⟩ := compact_nnnorm_bound hsd hd.continuous
  obtain ⟨L,hL⟩ := compact_nnnorm_bound hsdd hdd.continuous
  have hlip : LipschitzWith K f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by simp)) hK
  have hdlip : LipschitzWith L (fderiv ℝ f) := lipschitzWith_of_nnnorm_fderiv_le
    (hd.differentiable (by simp)) hL
  have hbound (x) : ‖f x‖ ≤ (M : ℝ) := by exact_mod_cast hM x
  have hc : ContDiff ℝ 1 f := hf.of_le (by simp)
  let Φ := BressanJump.globalLipschitzFlow f hc M K hbound hlip
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact BressanJump.globalLipschitzFlow_zero f hc M K hbound hlip
  · exact BressanJump.globalLipschitzFlow_isIntegralCurve f hc M K hbound hlip
  · intro T
    exact global_flow_contDiff f (fderiv ℝ f) K L M hlip hdlip
      (fun x => (hf.differentiable (by simp) x).hasFDerivAt) hbound hc T
  · exact BressanJump.globalLipschitzFlow_add f hc M K hbound hlip
  · exact global_flow_joint_continuous f hc M K hbound hlip

/-- Localization keeps the exact field throughout a prescribed ball and
constructs a C1 global endpoint map for the compactly supported extension. -/
theorem smooth_field_cutoff_c1_flow [FiniteDimensional ℝ E]
    (f : E → E) (hf : ContDiff ℝ ∞ f) (c : E) {R : ℝ} (hR : 0 < R) :
    ∃ g : E → E, (∀ x ∈ Metric.closedBall c R, g x = f x) ∧
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∃ Φ : ℝ → E → E,
        (∀ x, Φ 0 x = x) ∧
        (∀ x t, HasDerivAt (fun s => Φ s x) (g (Φ t x)) t) ∧
        (∀ T : ℝ≥0, ContDiff ℝ 1 (Φ T)) ∧
        (∀ s t x, Φ s (Φ t x) = Φ (t+s) x) ∧
        Continuous (fun p : ℝ × E => Φ p.1 p.2) := by
  let b : ContDiffBump c := ⟨R,R+1,hR,by linarith⟩
  let g : E → E := fun x => b x • f x
  have hg : ContDiff ℝ ∞ g := b.contDiff.smul hf
  have hs : HasCompactSupport g := b.hasCompactSupport.smul_right
  refine ⟨g,?_,hg,hs,compact_field_c1_flow g hg hs⟩
  intro x hx
  have hb : b x = 1 := b.one_of_mem_closedBall hx
  simp only [g,hb,one_smul]

end OscillatoryCores
