import proofs.CoreCouplingGlobal.EquilibriumBrackets

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem positive_on_zero_free_interval (f : ℝ → ℝ) (l u c : ℝ)
    (hf : ContinuousOn f (Ioo l u)) (hc : c ∈ Ioo l u) (hfc : 0 < f c)
    (hn : ∀ x ∈ Ioo l u, f x ≠ 0) : ∀ x ∈ Ioo l u, 0 < f x := by
  intro x hx
  by_contra hnot
  have hle : f x ≤ 0 := le_of_not_gt hnot
  rcases le_total x c with hxc | hcx
  · have hcont : ContinuousOn f (Icc x c) := hf.mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1,lt_of_le_of_lt ht.2 hc.2⟩)
    obtain ⟨t,ht,hft⟩ := intermediate_value_Icc hxc hcont ⟨hle,hfc.le⟩
    exact hn t ⟨lt_of_lt_of_le hx.1 ht.1,lt_of_le_of_lt ht.2 hc.2⟩ hft
  · have hcont : ContinuousOn f (Icc c x) := hf.mono (by
      intro t ht
      exact ⟨lt_of_lt_of_le hc.1 ht.1,lt_of_le_of_lt ht.2 hx.2⟩)
    obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' hcx hcont ⟨hle,hfc.le⟩
    exact hn t ⟨lt_of_lt_of_le hc.1 ht.1,lt_of_le_of_lt ht.2 hx.2⟩ hft

theorem residual_positive_root_exhaustion (e : ℝ) (low mid high : State)
    (hall : ∀ s : State, s.Positive → Stationary (varyRates e) s → s = low ∨ s = mid ∨ s = high)
    (z : ℝ) (hz : z ∈ Icc (9/10:ℝ) (31/10))
    (hroot : residual (varyRates e) z = 0) : z = low.z ∨ z = mid.z ∨ z = high.z := by
  have hz0 : 0 < z := by linarith [hz.1]
  have hs := lift_stationary (varyRates e) z (by positivity)
    (by norm_num [varyRates,witnessRates]) hroot
  have hp : (lift (varyRates e) z).Positive := witness_lift_positive z hz0 (by linarith [hz.2])
  rcases hall _ hp hs with h | h | h
  · exact Or.inl (congrArg State.z h)
  · exact Or.inr (Or.inl (congrArg State.z h))
  · exact Or.inr (Or.inr (congrArg State.z h))

theorem residual_between_bracketed_roots (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (low mid high : State)
    (hlo : low.z ∈ Icc (9/10:ℝ) (11/10)) (hm : mid.z ∈ Icc (19/10:ℝ) (21/10))
    (hhi : high.z ∈ Icc (29/10:ℝ) (31/10))
    (hsl : residual (varyRates e) low.z = 0) (hsm : residual (varyRates e) mid.z = 0)
    (_hsh : residual (varyRates e) high.z = 0)
    (hall : ∀ s : State, s.Positive → Stationary (varyRates e) s → s = low ∨ s = mid ∨ s = high) :
    (∀ z ∈ Ioo low.z mid.z, 0 < residual (varyRates e) z) ∧
    (∀ z ∈ Ioo mid.z high.z, residual (varyRates e) z < 0) := by
  obtain ⟨_,hsignL,_,hsignR,_,_⟩ := creation_interval_signs e hl hu
  have hlo' : low.z < 11/10 := by
    apply lt_of_le_of_ne hlo.2
    intro heq
    rw [heq] at hsl
    linarith
  have hm' : mid.z < 21/10 := by
    apply lt_of_le_of_ne hm.2
    intro heq
    rw [heq] at hsm
    linarith
  have hcont := vary_residual_continuousOn e (9/10) (31/10) (by norm_num)
  constructor
  · apply positive_on_zero_free_interval _ low.z mid.z (11/10)
      (hcont.mono (by intro z hz; exact ⟨by linarith [hz.1,hlo.1],by linarith [hz.2,hm.2]⟩))
      ⟨hlo',by linarith [hm.1]⟩ hsignL
    intro z hz hzero
    have hcases := residual_positive_root_exhaustion e low mid high hall z
      ⟨by linarith [hz.1,hlo.1],by linarith [hz.2,hm.2]⟩ hzero
    rcases hcases with heq | heq | heq <;> linarith [hz.1,hz.2,hhi.1,hm.2]
  · have hn := positive_on_zero_free_interval (fun z => -residual (varyRates e) z)
      mid.z high.z (21/10) (hcont.neg.mono (by
        intro z hz
        exact ⟨by linarith [hz.1,hm.1],by linarith [hz.2,hhi.2]⟩))
      ⟨hm',by linarith [hhi.1]⟩ (by linarith : 0 < -residual (varyRates e) (21/10))
    have hno : ∀ z ∈ Ioo mid.z high.z, -residual (varyRates e) z ≠ 0 := by
      intro z hz hzero
      have hcases := residual_positive_root_exhaustion e low mid high hall z
        ⟨by linarith [hz.1,hm.1],by linarith [hz.2,hhi.2]⟩ (by linarith)
      rcases hcases with heq | heq | heq <;> linarith [hz.1,hz.2,hlo.2,hm.1]
    intro z hz
    have hpos := hn hno z hz
    linarith

end CoreCouplingGlobal
