import proofs.FiniteCopyReactor.PhaseProbability
import proofs.FiniteCopyReactor.CollectionResidence

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem residence_step_eq (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').step f N =
      if residenceActive V N then
        (materialKernel V r d hV (by linarith) hr' hd hd').step f N else f N := by
  unfold residenceKernel materialKernel
  rw [FiniteJumpModel.uniformize_step,FiniteJumpModel.uniformize_step]
  by_cases h : residenceActive V N
  · simp only [if_pos h,FiniteJumpModel.generator,residenceModel,materialModel,if_pos h.1]
  · simp only [if_neg h,FiniteJumpModel.generator,residenceModel,zero_mul,
      Finset.sum_const_zero,zero_div,add_zero]

def residencePhaseTest (V : ℕ) (s : ℝ) (w : PhaseWeights) (N : BoxCounts V) : ℝ :=
  if residenceActive V N then Real.exp (-s*w.obs (boxCounts N)) else 0

theorem residence_phase_step (V : ℕ) (r d s : ℝ) (w : PhaseWeights)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hw : w.Nonneg) (hm : w.mass ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1/100) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').step (residencePhaseTest V s w) N ≤
      Real.exp ((12/5)*s^2)*residencePhaseTest V s (phaseWeightStep (3000*(V:ℝ)) w) N := by
  let R := residenceKernel V r d hV (by linarith) hr' hd hd'
  have hle (X) : residencePhaseTest V s w X ≤ phaseTest V s w X := by
    by_cases hx : residenceActive V X
    · simp only [residencePhaseTest,phaseTest,if_pos hx,if_pos hx.1,le_refl]
    · simp only [residencePhaseTest,if_neg hx]
      unfold phaseTest
      split_ifs <;> positivity
  by_cases h : residenceActive V N
  · have hh := R.step_mono hle N
    rw [residence_step_eq V r d hV hr hr' hd hd' (phaseTest V s w) N,if_pos h] at hh
    have ht := phase_step_transfer V r d s w hV hr hr' hd hd' hw hm hs hs' N
    have hb := hh.trans ht
    simpa only [phaseTest,residencePhaseTest,if_pos h,if_pos h.1] using hb
  · rw [residence_step_eq V r d hV hr hr' hd hd',if_neg h]
    simp only [residencePhaseTest,if_neg h,mul_zero,le_refl]

theorem residence_phase_steps (V : ℕ) (r d s : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hs : 0 ≤ s) (hs' : s ≤ 1/100) (n : ℕ) (N : BoxCounts V) :
    (residenceKernel V r d hV (by linarith) hr' hd hd').steps n
      (residencePhaseTest V s (phaseWeights (3000*(V:ℝ)) 0)) N ≤
      Real.exp ((n:ℝ)*(12/5)*s^2)*residencePhaseTest V s (phaseWeights (3000*(V:ℝ)) n) N := by
  let R := residenceKernel V r d hV (by linarith) hr' hd hd'
  have hv1 : (1:ℝ) ≤ V := by
    have hv : 0 < V := by exact_mod_cast hV
    exact_mod_cast (show 1 ≤ V by omega)
  have hq70 : (70:ℝ) ≤ 3000*V := by linarith
  induction n generalizing N with
  | zero => simp only [FiniteKernel.steps,Nat.cast_zero,zero_mul,Real.exp_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := R.step_mono ih N
    rw [R.step_scale] at hh
    have hb := phase_weights_bounds (3000*(V:ℝ)) (by positivity) hq70 n
    have ht := residence_phase_step V r d s (phaseWeights (3000*(V:ℝ)) n)
      hV hr hr' hd hd' hb.1 hb.2 hs hs' N
    have h := hh.trans (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)
    rw [← mul_assoc,← Real.exp_add] at h
    convert h using 1
    congr 2
    push_cast
    ring

end
end FiniteCopyReactor
