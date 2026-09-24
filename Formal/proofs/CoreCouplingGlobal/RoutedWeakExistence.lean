import proofs.CoreCouplingGlobal.RoutedWeakCoupling

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

noncomputable def routedResponseState (e g z : ℝ) : State :=
  ⟨responseA e (60/routedDen g z),60/routedDen g z,z,
    (16*z+2*z^2)/(20001/10000)⟩

noncomputable def routedFeedbackResidual (e g z : ℝ) : ℝ :=
  g*((routedResponseState e g z).A-z*(routedResponseState e g z).B)-routedK z

theorem routed_weak_response_bounds (e g z : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : 0 ≤ g) (hgu : g ≤ 1/10) (hz : z ∈ Icc (4:ℝ) 8) :
    0 < routedDen g z ∧ (16:ℝ) ≤ 60/routedDen g z ∧
    60/routedDen g z ≤ 30 ∧ 0 < responseA e (60/routedDen g z) ∧
    responseA e (60/routedDen g z) ≤ 33 := by
  have hdlo : 2 ≤ routedDen g z := by
    dsimp [routedDen]
    nlinarith [mul_nonneg hg (show 0 ≤ z-1 by linarith [hz.1])]
  have hdhi : routedDen g z ≤ 37/10 := by
    dsimp [routedDen]
    nlinarith [mul_nonneg hg (sub_nonneg.mpr hz.2),
      mul_nonneg (sub_nonneg.mpr hgu) (show 0 ≤ z-1 by linarith [hz.1])]
  have hd : 0 < routedDen g z := by linarith
  have hb : (16:ℝ) ≤ 60/routedDen g z := (le_div_iff₀ hd).2 (by linarith)
  have hbu : 60/routedDen g z ≤ (30:ℝ) := (div_le_iff₀ hd).2 (by linarith)
  have ha : 0 < responseA e (60/routedDen g z) := by
    have hq : 0 < 33-60/routedDen g z+e*(60/routedDen g z) := by
      have hm := mul_nonneg he (show 0 ≤ 60/routedDen g z by positivity)
      linarith
    dsimp [responseA]
    positivity
  exact ⟨hd,hb,hbu,ha,(response_bounds e (60/routedDen g z) he heu
    (by linarith) (by linarith)).2⟩

theorem routed_weak_response_continuous (e g : ℝ) (he : 0 ≤ e)
    (heu : e ≤ 1/50000) (hg : 0 ≤ g) (hgu : g ≤ 1/10) :
    ContinuousOn (routedFeedbackResidual e g) (Icc (4:ℝ) 8) := by
  have hd : ∀ z ∈ Icc (4:ℝ) 8, routedDen g z ≠ 0 := by
    intro z hz
    exact ne_of_gt (routed_weak_response_bounds e g z he heu hg hgu hz).1
  have hD : ContinuousOn (routedDen g) (Icc (4:ℝ) 8) := by unfold routedDen; fun_prop
  have hB : ContinuousOn (fun z => (60:ℝ)/routedDen g z) (Icc (4:ℝ) 8) :=
    continuousOn_const.div hD hd
  have hq : ContinuousOn (fun z => 33-60/routedDen g z+e*(60/routedDen g z))
      (Icc (4:ℝ) 8) := (continuousOn_const.sub hB).add (continuousOn_const.mul hB)
  have hs : ContinuousOn (fun z => Real.sqrt (1+4*e*(33-60/routedDen g z+e*(60/routedDen g z))))
      (Icc (4:ℝ) 8) := (continuousOn_const.add (continuousOn_const.mul hq)).sqrt
  have ha : ContinuousOn (fun z => responseA e (60/routedDen g z)) (Icc (4:ℝ) 8) := by
    unfold responseA
    exact (continuousOn_const.mul hq).div (continuousOn_const.add hs)
      (fun z _ => by positivity)
  have hk : ContinuousOn routedK (Icc (4:ℝ) 8) := by unfold routedK; fun_prop
  exact (continuousOn_const.mul (ha.sub (continuousOn_id.mul hB))).sub hk

theorem routed_weak_response_root (e g z : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : 0 ≤ g) (hgu : g ≤ 1/10) (hz : z ∈ Icc (4:ℝ) 8)
    (hr : routedFeedbackResidual e g z=0) :
    (routedResponseState e g z).Positive ∧ RoutedStationary e g (routedResponseState e g z) := by
  obtain ⟨hd,hb,hbu,ha,_⟩ := routed_weak_response_bounds e g z he heu hg hgu hz
  have hq := response_quadratic e (60/routedDen g z) he heu (by linarith) (by linarith)
  have hB : (60/routedDen g z)*routedDen g z=60 := div_mul_cancel₀ _ (ne_of_gt hd)
  have hpos : (routedResponseState e g z).Positive :=
    ⟨ha,by dsimp [routedResponseState]; positivity,by exact lt_of_lt_of_le (by norm_num) hz.1,
      by
        dsimp [routedResponseState]
        have hzp : 0 < z := by linarith [hz.1]
        positivity⟩
  refine ⟨hpos,?_,?_,?_,?_⟩
  · dsimp [fA,flagshipRates,routedResponseState]
    dsimp [routedDen] at hB hq ⊢
    linear_combination -2*hq+hB
  · dsimp [fB,flagshipRates,routedResponseState]
    dsimp [routedDen] at hB hq ⊢
    linear_combination hq-hB
  · dsimp [routedFeedbackResidual,routedResponseState,routedK] at hr
    dsimp [routedZ,routedResponseState]
    linear_combination hr
  · dsimp [fH,flagshipRates,routedResponseState]
    ring

theorem routed_weak_exists (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : 0 ≤ g) (hgu : g ≤ 1/10) :
    ∃ x : State, x.Positive ∧ RoutedStationary e g x := by
  obtain ⟨_,_,hb,ha,_⟩ := routed_weak_response_bounds e g 4 he heu hg hgu (by norm_num)
  have hlo : 0 < routedFeedbackResidual e g 4 := by
    have hgb : g*(60/routedDen g 4) ≤ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hgu) (show 0 ≤ 60/routedDen g 4 by linarith)]
    have hga := mul_nonneg hg ha.le
    dsimp [routedFeedbackResidual,routedResponseState,routedK]
    nlinarith
  obtain ⟨_,hb,_,_,ha⟩ := routed_weak_response_bounds e g 8 he heu hg hgu (by norm_num)
  have hhi : routedFeedbackResidual e g 8 < 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos hg
      (show responseA e (60/routedDen g 8)-8*(60/routedDen g 8) ≤ 0 by linarith)
    dsimp [routedFeedbackResidual,routedResponseState,routedK]
    linarith
  obtain ⟨z,hz,hr⟩ := intermediate_value_Icc' (by norm_num : (4:ℝ) ≤ 8)
    (routed_weak_response_continuous e g he heu hg hgu)
    (show (0:ℝ) ∈ Icc (routedFeedbackResidual e g 8) (routedFeedbackResidual e g 4) from
      ⟨hhi.le,hlo.le⟩)
  exact ⟨routedResponseState e g z,routed_weak_response_root e g z he heu hg hgu hz hr⟩

/-- A positive uniqueness regime with genuine nonzero coupling and the same
intrinsic rates and positive isolated modules as the bistable example. -/
theorem routed_weak_exactly_one (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : 0 ≤ g) (hgu : g ≤ 1/10) :
    ∃! x : State, x.Positive ∧ RoutedStationary e g x := by
  obtain ⟨x,hx,hsx⟩ := routed_weak_exists e g he heu hg hgu
  exact ⟨x,⟨hx,hsx⟩,fun y hy => routed_small_unique e g he hg hgu y x hy.1 hx hy.2 hsx⟩

end CoreCouplingGlobal
