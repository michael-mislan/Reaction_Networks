import proofs.FiniteCopyReactor.PhaseExponential

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

def phaseTest (V : ℕ) (s : ℝ) (w : PhaseWeights) (N : BoxCounts V) : ℝ :=
  if resourceGood (boxCounts N) V then Real.exp (-s*w.obs (boxCounts N)) else 0

theorem phase_test_generator (V : ℕ) (r d s : ℝ) (w : PhaseWeights)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hw : w.Nonneg) (hm : w.mass ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1/100)
    (N : BoxCounts V) (hc : resourceGood (boxCounts N) V) :
    (materialModel V r d hV (by linarith) hd).generator (phaseTest V s w) N ≤
      Real.exp (-s*w.obs (boxCounts N))*(-s*phaseDriftLower w (boxCounts N)+7200*(V:ℝ)*s^2) := by
  have hh := (materialModel V r d hV (by linarith) hd).generator_mono_at
    (phaseTest V s w) (fun X => Real.exp (-s*w.obs (boxCounts X))) N
    (by simp only [phaseTest,if_pos hc])
    (fun j => by unfold phaseTest; split_ifs <;> first | exact le_rfl | positivity)
  rw [material_model_inside V r d hV _ hd N (fun X : Counts => Real.exp (-s*w.obs X)) hc] at hh
  exact hh.trans (phase_exponential_generator w hw hm (boxCounts N) V r d s hV hr hr' hd hd' hs hs' hc)

theorem phase_step_transfer (V : ℕ) (r d s : ℝ) (w : PhaseWeights)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hw : w.Nonneg) (hm : w.mass ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1/100) (N : BoxCounts V) :
    (materialKernel V r d hV (by linarith) hr' hd hd').step (phaseTest V s w) N ≤
      Real.exp ((12/5)*s^2)*phaseTest V s (phaseWeightStep (3000*(V:ℝ)) w) N := by
  unfold materialKernel
  rw [FiniteJumpModel.uniformize_step]
  by_cases hc : resourceGood (boxCounts N) V
  · have hg := div_le_div_of_nonneg_right
      (phase_test_generator V r d s w hV hr hr' hd hd' hw hm hs hs' N hc)
      (show 0 ≤ 3000*(V:ℝ) by positivity)
    simp only [phaseTest,if_pos hc]
    have he : Real.exp (-s*w.obs (boxCounts N))+
        Real.exp (-s*w.obs (boxCounts N))*(-s*phaseDriftLower w (boxCounts N)+7200*(V:ℝ)*s^2)/(3000*(V:ℝ)) =
        Real.exp (-s*w.obs (boxCounts N))*(1+(-s*phaseDriftLower w (boxCounts N)/(3000*(V:ℝ))+(12/5)*s^2)) := by
      field_simp
      ring
    apply (add_le_add le_rfl hg).trans
    rw [he]
    have heuler := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (-s*phaseDriftLower w (boxCounts N)/(3000*(V:ℝ))+(12/5)*s^2))
      (Real.exp_pos (-s*w.obs (boxCounts N))).le
    rw [add_comm] at heuler
    apply heuler.trans_eq
    rw [← Real.exp_add,← Real.exp_add,phase_step_obs]
    congr 1
    ring
  · rw [material_model_outside V r d hV _ hd N _ hc]
    simp only [phaseTest,if_neg hc,zero_div,add_zero,mul_zero,le_refl]

theorem phase_steps_transfer (V : ℕ) (r d s : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hs : 0 ≤ s) (hs' : s ≤ 1/100) (n : ℕ) (N : BoxCounts V) :
    (materialKernel V r d hV (by linarith) hr' hd hd').steps n
      (phaseTest V s (phaseWeights (3000*(V:ℝ)) 0)) N ≤
      Real.exp ((n:ℝ)*(12/5)*s^2)*phaseTest V s (phaseWeights (3000*(V:ℝ)) n) N := by
  let P := materialKernel V r d hV (by linarith) hr' hd hd'
  have hv1 : (1:ℝ) ≤ V := by
    have hv : 0 < V := by exact_mod_cast hV
    exact_mod_cast (show 1 ≤ V by omega)
  have hq70 : (70:ℝ) ≤ 3000*V := by linarith
  induction n generalizing N with
  | zero => simp only [FiniteKernel.steps,Nat.cast_zero,zero_mul,Real.exp_zero,one_mul,le_refl]
  | succ n ih =>
    have hh := P.step_mono ih N
    rw [P.step_scale] at hh
    have hb := phase_weights_bounds (3000*(V:ℝ)) (by positivity) hq70 n
    have ht := phase_step_transfer V r d s (phaseWeights (3000*(V:ℝ)) n)
      hV hr hr' hd hd' hb.1 hb.2 hs hs' N
    have h := hh.trans (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)
    rw [← mul_assoc,← Real.exp_add] at h
    convert h using 1
    congr 2
    push_cast
    ring

end
end FiniteCopyReactor
