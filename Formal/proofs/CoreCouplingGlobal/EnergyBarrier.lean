import proofs.CoreCouplingGlobal.ResponsePotential

namespace CoreCouplingGlobal
open Set

/-- The natural H response, also used outside the absorbing box for comparisons. -/
noncomputable def naturalH (z : ℝ) : ℝ := (16*z+2*z^2)/(20001/10000)

theorem naturalH_bounds (z : ℝ) (hz : z ∈ Icc (0:ℝ) 12) :
    naturalH z ∈ Icc (0:ℝ) 256 := by
  unfold naturalH
  have hz0 := hz.1
  constructor
  · positivity
  · apply (div_le_iff₀ (by norm_num : (0:ℝ) < 20001/10000)).2
    nlinarith [hz.1, hz.2, sq_nonneg (z-12)]

theorem responsePhi_naturalH (z : ℝ) (hz : 0 ≤ z) :
    responsePhi (naturalH z) = z := by
  have hn : 0 ≤ naturalH z := by unfold naturalH; positivity
  have hp : 0 ≤ responsePhi (naturalH z) := by unfold responsePhi; positivity
  have hq := responsePhi_quadratic (naturalH z) hn
  have hid : (20001/10000:ℝ)*naturalH z = 16*z+2*z^2 := by
    unfold naturalH
    ring
  rw [hid] at hq
  nlinarith [sq_nonneg (responsePhi (naturalH z)-z)]

/-- The potential can use its natural H primitive on the larger comparison interval. -/
theorem extendedPotentialPrimitives_nonempty (e : ℝ) (he : 0 ≤ e)
    (he' : e ≤ 1/50000) :
    ∃ p : PotentialPrimitives e, ∀ H ∈ Icc (0:ℝ) 256,
      HasDerivAt p.R (3*responseLog (responsePhi H)) H := by
  obtain ⟨p⟩ := potentialPrimitives_nonempty e he he'
  have hphi : Continuous responsePhi := by
    unfold responsePhi
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    positivity
  have hR : ContinuousOn (fun H => 3*responseLog (responsePhi H)) (Icc (0:ℝ) 256) := by
    intro H hH
    have hH0 := hH.1
    have hp : 0 ≤ responsePhi H := by unfold responsePhi; positivity
    exact (continuousAt_const.mul ((responseLog_hasDerivAt _ (by linarith)).continuousAt.comp
      (f := responsePhi) hphi.continuousAt)).continuousWithinAt
  obtain ⟨R,hRc,hRd⟩ := primitive_on_Icc _ 0 256 (by norm_num) hR
  refine ⟨{p with R := R, continuousR := hRc, derivR := ?_}, hRd⟩
  intro H hH
  exact hRd H ⟨hH.1, by linarith [hH.2]⟩

/-- A derivative pointing away from a point makes that point a minimum. -/
theorem minimum_of_derivative_sign (f df : ℝ → ℝ) (l m u : ℝ)
    (hm : m ∈ Icc l u)
    (hd : ∀ x ∈ Icc l u, HasDerivAt f (df x) x)
    (hleft : ∀ x ∈ Icc l m, df x ≤ 0)
    (hright : ∀ x ∈ Icc m u, 0 ≤ df x) :
    ∀ x ∈ Icc l u, f m ≤ f x := by
  intro x hx
  rcases lt_trichotomy x m with hxm | hxm | hmx
  · obtain ⟨t,ht,heq⟩ := exists_hasDerivAt_eq_slope f df hxm
      (fun t ht => (hd t ⟨le_trans hx.1 ht.1,le_trans ht.2 hm.2⟩).continuousAt.continuousWithinAt)
      (fun t ht => hd t ⟨by linarith [ht.1,hx.1],by linarith [ht.2,hm.2]⟩)
    have hn := hleft t ⟨by linarith [ht.1,hx.1],le_of_lt ht.2⟩
    have he := (eq_div_iff (by linarith : m-x ≠ 0)).1 heq
    nlinarith
  · subst x
    exact le_rfl
  · obtain ⟨t,ht,heq⟩ := exists_hasDerivAt_eq_slope f df hmx
      (fun t ht => (hd t ⟨le_trans hm.1 ht.1,le_trans ht.2 hx.2⟩).continuousAt.continuousWithinAt)
      (fun t ht => hd t ⟨by linarith [ht.1,hm.1],by linarith [ht.2,hx.2]⟩)
    have hn := hright t ⟨le_of_lt ht.1,by linarith [ht.2,hx.2]⟩
    have he := (eq_div_iff (by linarith : x-m ≠ 0)).1 heq
    nlinarith

theorem responseLog_mono_nonnegative {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    responseLog x ≤ responseLog y := by
  rcases eq_or_lt_of_le hxy with he | he
  · rw [he]
  obtain ⟨t,ht,heq⟩ := exists_hasDerivAt_eq_slope responseLog
    (fun t => 1/((t+1)*(t+2))) he
    (fun t ht => (responseLog_hasDerivAt t (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => responseLog_hasDerivAt t (by linarith [ht.1]))
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hp : 0 ≤ 1/((t+1)*(t+2)) := by positivity
  have he' := (eq_div_iff (by linarith : y-x ≠ 0)).1 heq
  nlinarith

theorem responsePhi_le_natural {H z : ℝ} (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hle : H ≤ naturalH z) : responsePhi H ≤ z := by
  have hp : 0 ≤ responsePhi H := by unfold responsePhi; positivity
  have hq := responsePhi_quadratic H hH
  unfold naturalH at hle
  have hb := (le_div_iff₀ (by norm_num : (0:ℝ) < 20001/10000)).1 hle
  nlinarith [sq_nonneg (responsePhi H-z)]

theorem natural_le_responsePhi {H z : ℝ} (hH : 0 ≤ H) (hz : 0 ≤ z)
    (hle : naturalH z ≤ H) : z ≤ responsePhi H := by
  have hp : 0 ≤ responsePhi H := by unfold responsePhi; positivity
  have hq := responsePhi_quadratic H hH
  unfold naturalH at hle
  have hb := (div_le_iff₀ (by norm_num : (0:ℝ) < 20001/10000)).1 hle
  nlinarith [sq_nonneg (responsePhi H-z)]

/-- Minimizing in H is valid on the enlarged primitive interval. -/
theorem potential_H_minimum (e : ℝ) (p : PotentialPrimitives e)
    (hp : ∀ H ∈ Icc (0:ℝ) 256, HasDerivAt p.R (3*responseLog (responsePhi H)) H)
    (B z H r : ℝ) (hz : z ∈ Icc (0:ℝ) 12) (hH : H ∈ Icc (0:ℝ) 256) :
    responsePotential e p B z (naturalH z) r ≤ responsePotential e p B z H r := by
  let f : ℝ → ℝ := fun x => responsePotential e p B z x r
  let df : ℝ → ℝ := fun x => 3*(responseLog (responsePhi x)-responseLog z)
  have hd : ∀ x ∈ Icc (0:ℝ) 256, HasDerivAt f (df x) x := by
    intro x hx
    convert (((hasDerivAt_const x (B*Real.log (z+2)-responseTotal e B*responseLog z+p.U z)).sub
      (((hasDerivAt_id x).const_mul 3).mul_const (responseLog z))).add_const (p.P B)).add
      (hp x hx) |>.add_const (r^2/2) using 1
    dsimp [f,df,responsePotential]
    ring
  apply minimum_of_derivative_sign f df 0 (naturalH z) 256 (naturalH_bounds z hz) hd ?_ ?_ H hH
  · intro x hx
    have hpz := responsePhi_le_natural hx.1 hz.1 hx.2
    have hpx : 0 ≤ responsePhi x := by unfold responsePhi; have := hx.1; positivity
    have hlog := responseLog_mono_nonnegative hpx hpz
    dsimp [df]
    linarith
  · intro x hx
    have hx0 : 0 ≤ x := le_trans (naturalH_bounds z hz).1 hx.1
    have hpz := natural_le_responsePhi hx0 hz.1 hx.1
    have hlog := responseLog_mono_nonnegative hz.1 hpz
    dsimp [df]
    linarith

noncomputable def reducedZ (e B z : ℝ) : ℝ :=
  responseTotal e B-B+(159984/20001-B)*z-(20004/20001)*z^2

theorem reducedZ_antitone (e B : ℝ) (hB : 8 ≤ B) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : reducedZ e B y ≤ reducedZ e B x := by
  have hprod := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ B-8 by linarith)
  dsimp [reducedZ]
  nlinarith [sq_nonneg (y-x)]

theorem reducedPotential_hasDerivAt (e : ℝ) (p : PotentialPrimitives e)
    (hp : ∀ H ∈ Icc (0:ℝ) 256, HasDerivAt p.R (3*responseLog (responsePhi H)) H)
    (B z : ℝ) (hz : z ∈ Icc (0:ℝ) 12) :
    HasDerivAt (fun t => responsePotential e p B t (naturalH t) 0)
      (-reducedZ e B z/((z+1)*(z+2))) z := by
  have hz1 : z+1 ≠ 0 := by linarith [hz.1]
  have hz2 : z+2 ≠ 0 := by linarith [hz.1]
  have dl := responseLog_hasDerivAt z (by linarith [hz.1])
  have dh : HasDerivAt naturalH ((16+4*z)/(20001/10000)) z := by
    convert (((hasDerivAt_id z).const_mul 16).add
      (((hasDerivAt_id z).pow 2).const_mul 2)).div_const (20001/10000) using 1
    dsimp [naturalH]
    ring
  have dr := (hp (naturalH z) (naturalH_bounds z hz)).comp z dh
  rw [responsePhi_naturalH z hz.1] at dr
  have hv := ((((((hasDerivAt_id z).add_const 2).log hz2).const_mul B).sub
    (dl.const_mul (responseTotal e B))).add (p.derivU z hz)).sub
      ((dh.const_mul 3).mul dl)
  have hv' := (hv.add_const (p.P B)).add dr |>.add_const ((0:ℝ)^2/2)
  convert hv' using 1
  dsimp [reducedZ,naturalH]
  field_simp
  ring

/-- The saddle-plane barrier; the root and location hypotheses are explicit. -/
theorem saddle_plane_energy_barrier (e : ℝ) (p : PotentialPrimitives e)
    (hp : ∀ H ∈ Icc (0:ℝ) 256, HasDerivAt p.R (3*responseLog (responsePhi H)) H)
    (B zs z H r : ℝ) (hB : 8 ≤ B) (hs : zs ∈ Icc (0:ℝ) 12)
    (hroot : reducedZ e B zs = 0) (hz : z ∈ Icc (0:ℝ) 12)
    (hH : H ∈ Icc (0:ℝ) 256) :
    responsePotential e p B zs (naturalH zs) 0 ≤ responsePotential e p B z H r := by
  have hmin : responsePotential e p B zs (naturalH zs) 0 ≤
      responsePotential e p B z (naturalH z) 0 := by
    apply minimum_of_derivative_sign
      (fun t => responsePotential e p B t (naturalH t) 0)
      (fun t => -reducedZ e B t/((t+1)*(t+2))) 0 zs 12 hs
      (fun t ht => reducedPotential_hasDerivAt e p hp B t ht) ?_ ?_ z hz
    · intro t ht
      have hm := reducedZ_antitone e B hB ht.1 ht.2
      rw [hroot] at hm
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) (by have := ht.1; positivity)
    · intro t ht
      have hm := reducedZ_antitone e B hB hs.1 ht.1
      rw [hroot] at hm
      have ht0 : 0 ≤ t := le_trans hs.1 ht.1
      exact div_nonneg (neg_nonneg.mpr hm) (by positivity)
  have hHmin := potential_H_minimum e p hp B z H 0 hz hH
  have hr : responsePotential e p B z H 0 ≤ responsePotential e p B z H r := by
    dsimp [responsePotential]
    nlinarith [sq_nonneg r]
  exact le_trans hmin (le_trans hHmin hr)

end CoreCouplingGlobal
