import proofs.DisguisedToricAssemblies.CACLocusAnalysis

namespace DisguisedToricAssemblies
open CoreCouplingCAC

theorem residual_zero_negative (p : Rates) (hp : p.Positive) : residual p 0 < 0 := by
  have hid : residual p 0 = -p.a/2-p.e*(p.a+2*p.b)/2 := by
    simp [CoreCouplingCAC.residual,reducedA,reducedB,reducedK]
    ring
  rw [hid]
  have ha := hp.1
  have hb := hp.2.1
  have he := hp.2.2.2.2.1
  have hh : 0 < p.e*(p.a+2*p.b)/2 := by positivity
  linarith

theorem residual_continuous (p : Rates) (hp : p.Positive) (l r : ℝ) (hl : 0 ≤ l) :
    ContinuousOn (residual p) (Set.Icc l r) := by
  have hden : ∀ z ∈ Set.Icc l r, z+2 ≠ (0:ℝ) := by intro z hz; linarith [hz.1]
  have hd : 2+p.d ≠ 0 := by have := hp.2.2.2.2.2; positivity
  unfold CoreCouplingCAC.residual reducedA reducedB reducedK
  apply ContinuousOn.add
  · apply ContinuousOn.add
    · exact continuousOn_const.sub (continuousOn_const.mul
        (continuousOn_const.div (continuousOn_id.add continuousOn_const) hden))
    · exact (by fun_prop : ContinuousOn (fun z : ℝ => p.v*(1+2*p.d)*z^2-p.u*(1-p.d)*z) _).div
        continuousOn_const (fun _ _ => hd)
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.pow
    exact (continuousOn_id.mul (continuousOn_const.div
      (continuousOn_id.add continuousOn_const) hden)).add
      ((by fun_prop : ContinuousOn (fun z : ℝ => p.v*(1+2*p.d)*z^2-p.u*(1-p.d)*z) _).div
        continuousOn_const (fun _ _ => hd))

theorem admissible_root_exists (p : Rates) (hp : p.Positive)
    (he : residual p (admissibleCut p) ≤ 0) :
    ∃ z, 0 < z ∧ admissibleCut p ≤ z ∧ residual p z = 0 := by
  have ha := hp.1
  have hb := hp.2.1
  have hep := hp.2.2.2.2.1
  have hc := cut_nonneg p
  let R := admissibleCut p+1+(1+p.e)*(p.a+2*p.b)/p.b
  have hR : admissibleCut p < R := by
    have ht : 0 < (1+p.e)*(p.a+2*p.b)/p.b := by positivity
    dsimp [R]
    linarith
  have hRden : 0 < R+2 := by linarith
  have hBR : (1+p.e)*reducedB p R < p.b := by
    rw [reducedB, ← mul_div_assoc]
    apply (div_lt_iff₀ hRden).2
    dsimp [R]
    field_simp
    nlinarith [mul_nonneg hc hb.le]
  have heR : 0 < residual p R := by
    have hk := admissible_K_nonneg p hp R hR.le
    have hsq : 0 ≤ p.e*(reducedA p R)^2 := by positivity
    unfold CoreCouplingCAC.residual
    linarith only [hBR,hk,hsq]
  obtain ⟨z,hz,hez⟩ := intermediate_value_Icc hR.le
    (residual_continuous p hp _ R hc) ⟨he,heR.le⟩
  have hzp : 0 < z := by
    by_contra hn
    have hz0 : z = 0 := by linarith [hz.1]
    have hneg := residual_zero_negative p hp
    rw [hz0] at hez
    linarith
  exact ⟨z,hzp,hz.1,hez⟩

theorem admissible_root_cut_sign (p : Rates) (hp : p.Positive) (z : ℝ)
    (hz : admissibleCut p ≤ z) (he : residual p z = 0) :
    residual p (admissibleCut p) ≤ 0 := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [h,he]
  · have hi := (admissible_increasing p hp _ z le_rfl h).2
    linarith

end DisguisedToricAssemblies
