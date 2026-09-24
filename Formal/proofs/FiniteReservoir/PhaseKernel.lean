import proofs.FiniteReservoir.PhaseExponential
import proofs.FiniteReservoir.MaterialControl

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

def phaseTest (V M : ℕ) (s : ℝ) (w : PhaseWeights) (N : BoxState V M) : ℝ :=
  if resourceGood (boxCounts N.1) V then Real.exp (-s*w.obs (boxCounts N.1)) else 0

theorem phase_test_generator (V M : ℕ) (p : Parameters M) (s : ℝ) (w : PhaseWeights)
    (hV : 0 < (V:ℝ)) 
    (hw : w.Nonneg) (hm : w.mass ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1/100)
    (N : BoxState V M) (hc : resourceGood (boxCounts N.1) V) :
    (materialModel V M p hV).generator (phaseTest V M s w) N ≤
      Real.exp (-s*w.obs (boxCounts N.1))*(-s*phaseDriftLower w (boxCounts N.1)+7200*(V:ℝ)*s^2) := by
  have hh := (materialModel V M p hV).generator_mono_at
    (phaseTest V M s w) (fun X => Real.exp (-s*w.obs (boxCounts X.1))) N
    (by simp only [phaseTest,if_pos hc])
    (fun j => by unfold phaseTest; split_ifs <;> first | exact le_rfl | positivity)
  rw [show (materialModel V M p hV).generator _ N = _ from
    model_inside V M p hV _ N hc hc (fun X : Counts => Real.exp (-s*w.obs X))] at hh
  exact hh.trans (phase_exponential_generator w hw hm (boxCounts N.1) V p.release _ _ s hV
    p.release_lower p.release_upper (parameters_box p N.2) hs hs' hc)

theorem phase_step_transfer (V M : ℕ) (p : Parameters M) (s : ℝ) (w : PhaseWeights)
    (hV : 0 < (V:ℝ)) 
    (hw : w.Nonneg) (hm : w.mass ≤ 1) (hs : 0 ≤ s) (hs' : s ≤ 1/100) (N : BoxState V M) :
    (materialKernel V M p hV).step (phaseTest V M s w) N ≤
      Real.exp ((12/5)*s^2)*phaseTest V M s (phaseWeightStep (3000*(V:ℝ)) w) N := by
  unfold materialKernel
  rw [FiniteJumpModel.uniformize_step]
  by_cases hc : resourceGood (boxCounts N.1) V
  · have hg := div_le_div_of_nonneg_right
      (phase_test_generator V M p s w hV hw hm hs hs' N hc)
      (show 0 ≤ 3000*(V:ℝ) by positivity)
    simp only [phaseTest,if_pos hc]
    have he : Real.exp (-s*w.obs (boxCounts N.1))+
        Real.exp (-s*w.obs (boxCounts N.1))*(-s*phaseDriftLower w (boxCounts N.1)+7200*(V:ℝ)*s^2)/(3000*(V:ℝ)) =
        Real.exp (-s*w.obs (boxCounts N.1))*(1+(-s*phaseDriftLower w (boxCounts N.1)/(3000*(V:ℝ))+(12/5)*s^2)) := by
      field_simp
      ring
    apply (add_le_add le_rfl hg).trans
    rw [he]
    have heuler := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (-s*phaseDriftLower w (boxCounts N.1)/(3000*(V:ℝ))+(12/5)*s^2))
      (Real.exp_pos (-s*w.obs (boxCounts N.1))).le
    rw [add_comm] at heuler
    apply heuler.trans_eq
    rw [← Real.exp_add,← Real.exp_add,phase_step_obs]
    congr 1
    ring
  · rw [show (materialModel V M p hV).generator _ N = 0 from
      model_outside V M p hV _ N hc _]
    simp only [phaseTest,if_neg hc,zero_div,add_zero,mul_zero,le_refl]

theorem phase_steps_transfer (V M : ℕ) (p : Parameters M) (s : ℝ)
    (hV : 0 < (V:ℝ)) 
    (hs : 0 ≤ s) (hs' : s ≤ 1/100) (n : ℕ) (N : BoxState V M) :
    (materialKernel V M p hV).steps n
      (phaseTest V M s (phaseWeights (3000*(V:ℝ)) 0)) N ≤
      Real.exp ((n:ℝ)*(12/5)*s^2)*phaseTest V M s (phaseWeights (3000*(V:ℝ)) n) N := by
  let P := materialKernel V M p hV
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
    have ht := phase_step_transfer V M p s (phaseWeights (3000*(V:ℝ)) n)
      hV hb.1 hb.2 hs hs' N
    have h := hh.trans (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)
    rw [← mul_assoc,← Real.exp_add] at h
    convert h using 1
    congr 2
    push_cast
    ring

end
end FiniteReservoir
