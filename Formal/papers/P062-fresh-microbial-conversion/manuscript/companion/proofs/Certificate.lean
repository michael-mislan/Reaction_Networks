import proofs.MicrobialFunctionAssay.Source

namespace MicrobialFunctionAssay

def lower (q1 q2 B e s J H : ℝ) : ℝ :=
  max 0 (max (q1-B) (max (q1+q2-B-H)
    (max (e*q1+q2-e*B-(s-e)*J-H) (s*q1+q2-s*B-H))))

theorem lower_sound (q1 q2 B e s J H f1 f2 p r : ℝ)
    (hf1 : 0 ≤ f1) (hf2 : 0 ≤ f2) (hp : 0 ≤ p) (hr : 0 ≤ r)
    (he : 0 ≤ e) (hes : e ≤ s) (hs : s ≤ 1)
    (h1 : q1+p+r ≤ B+f1) (h2 : q2 ≤ e*p+s*r+H+f2)
    (hj : r ≤ J) : lower q1 q2 B e s J H ≤ f1+f2 := by
  have hs0 : 0 ≤ s := le_trans he hes
  have he1 : e ≤ 1 := le_trans hes hs
  have ep : e*p ≤ p := mul_le_of_le_one_left hp he1
  have sr : s*r ≤ r := mul_le_of_le_one_left hr hs
  have ep' : e*p ≤ s*p := mul_le_mul_of_nonneg_right hes hp
  have ef : e*f1 ≤ f1 := mul_le_of_le_one_left hf1 he1
  have sf : s*f1 ≤ f1 := mul_le_of_le_one_left hf1 hs
  have ee := mul_le_mul_of_nonneg_left h1 he
  have ss := mul_le_mul_of_nonneg_left h1 hs0
  have jj := mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr hes)
  unfold lower
  repeat' apply max_le
  all_goals nlinarith

theorem observed_source_bound (h : History) (q1 q2 B J H : ℝ)
    (hobs1 : q1 ≤ h.first.collect) (hobs2 : q2 ≤ h.second.collect)
    (hB : h.first.p0+h.first.r0 ≤ B) (hJ : h.first.r ≤ J)
    (hH : h.inputP+h.inputR ≤ H) :
    lower q1 q2 B h.e h.s J H ≤ h.first.fresh+h.second.fresh := by
  apply lower_sound
  · exact h.first.nonneg.2.2.1
  · exact h.second.nonneg.2.2.1
  · exact (pool_nonneg h.first).1
  · exact (pool_nonneg h.first).2
  · exact h.fractions.1
  · exact h.fractions.2.1
  · exact h.fractions.2.2
  · linarith [source_account h.first]
  · linarith [recovery_account h]
  · exact hJ

theorem noisy_observation (actual measured error : ℝ)
    (h : |actual-measured| ≤ error) : measured-error ≤ actual := by
  have hh := (abs_le.mp h).1
  linarith

/-- e and s are certified upper retention maps in History; uncertainty in their
calibration is handled by expanding actual post-recovery amounts to these maps. -/
theorem reporting (h : History) (y1 y2 eps1 eps2 B J H threshold : ℝ)
    (ho1 : |h.first.collect-y1| ≤ eps1)
    (ho2 : |h.second.collect-y2| ≤ eps2)
    (hB : h.first.p0+h.first.r0 ≤ B) (hJ : h.first.r ≤ J)
    (hH : h.inputP+h.inputR ≤ H)
    (issued : threshold ≤ lower (y1-eps1) (y2-eps2) B h.e h.s J H) :
    threshold ≤ h.first.fresh+h.second.fresh := by
  exact le_trans issued (observed_source_bound h _ _ B J H
    (noisy_observation _ _ _ ho1) (noisy_observation _ _ _ ho2) hB hJ hH)

theorem wash_signal_cancellation (e p s r f loss J H : ℝ) :
    (e*p+s*r+f-loss) - e*p-s*J-H = f-loss-s*(J-r)-H := by ring

theorem second_window_bound (h : History) (pBound jBound hBound q : ℝ)
    (hp : h.first.p ≤ pBound) (hr : h.first.r ≤ jBound)
    (hi : h.inputP+h.inputR ≤ hBound) (ho : q ≤ h.second.collect) :
    q-h.e*pBound-h.s*jBound-hBound ≤ h.second.fresh := by
  have he := mul_le_mul_of_nonneg_left hp h.fractions.1
  have hs := mul_le_mul_of_nonneg_left hr (le_trans h.fractions.1 h.fractions.2.1)
  linarith [recovery_account h]

end MicrobialFunctionAssay
