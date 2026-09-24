import proofs.FiniteCopyReactor.LogarithmicScale
import proofs.FiniteCopyReactor.SynthesisCorollaries
import proofs.FiniteCopyReactor.OperationalCorollaries

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

theorem publication_budget (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N)
    (m : ℕ) (δ : ℝ) (hb : (m:ℝ)*oneCycleError V ≤ δ) :
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy) m []
        (OperationalSuccess N V m policy) :=
  (ENNReal.ofReal_le_ofReal (by linarith : 1-δ ≤ 1-(m:ℝ)*oneCycleError V)).trans
    (finite_copy_reactor_horizon N V r d hV hr hr' hd hd' policy hscale hN m)

theorem publication_logarithmic (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ)
    (N : Counts) (hN : Restart (logarithmicVolume m δ) N) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 1/50 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) :
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep N (logarithmicVolume m δ) r d
        (by have hs : 200000000000 ≤ logarithmicVolume m δ := le_max_left _ _
            exact_mod_cast (show 0 < logarithmicVolume m δ by omega))
        (by linarith) (by linarith) policy) m [] (OperationalSuccess N (logarithmicVolume m δ) m policy) := by
  apply publication_budget N _ r d _ hr hr' _ hd' policy (le_max_left _ _) hN m δ
  exact logarithmic_volume_error m hm δ hδ

theorem publication_48000 (N : Counts) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 1/50 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hN : Restart 200000000000 N) :
    ENNReal.ofReal (99/100:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep N 200000000000 r d (by norm_num) (by linarith) (by linarith) policy)
        48000 [] (OperationalSuccess N 200000000000 48000 policy) := by
  convert publication_budget N 200000000000 r d (by norm_num) hr hr' (by linarith) hd'
    policy (by norm_num) hN 48000 (1/100) mission_48000_budget using 1
  norm_num

theorem publication_hundred (N : Counts) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 1/50 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hN : Restart 200000000000 N) :
    ENNReal.ofReal (999979/1000000:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep N 200000000000 r d (by norm_num) (by linarith) (by linarith) policy)
        100 [] (OperationalSuccess N 200000000000 100 policy) := by
  convert publication_budget N 200000000000 r d (by norm_num) hr hr' (by linarith) hd'
    policy (by norm_num) hN 100 (21/1000000) hundred_sharp_budget using 1
  norm_num

theorem certified_mission_budget (V : ℝ) (hV : 200000000000 ≤ V) (m : ℕ) (δ : ℝ)
    (hm : (m:ℝ) ≤ δ/101*Real.exp (V/10000000000)) : (m:ℝ)*oneCycleError V ≤ δ := by
  have he := mul_le_mul_of_nonneg_left (one_cycle_single_exponential V hV) (Nat.cast_nonneg (α:=ℝ) m)
  have hp := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ 101*Real.exp (-V/10000000000))
  have hid : (δ/101*Real.exp (V/10000000000))*(101*Real.exp (-V/10000000000))=δ := by
    rw [show -V/10000000000=-(V/10000000000) by ring]
    calc
      _ = δ*(Real.exp (V/10000000000)*Real.exp (-(V/10000000000))) := by ring
      _ = δ := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
  rw [hid] at hp
  exact he.trans hp

end
end FiniteCopyReactor
