import proofs.DisguisedToricAssemblies.CACRootExistence

namespace DisguisedToricAssemblies
open CoreCouplingCAC

theorem residual_reservoir_identity (p : Rates) (z : ℝ) (hz : z+2 ≠ 0) :
    residual p z = reducedA p z-(p.a+p.b)+(1-p.e)*reducedB p z+p.e*(reducedA p z)^2 := by
  have ht := port_identity p z hz
  unfold CoreCouplingCAC.residual reducedA
  linear_combination -ht

theorem root_threshold_comparison (p : Rates) (hp : p.Positive) (z : ℝ)
    (hz : admissibleCut p ≤ z) (he : residual p z = 0) :
    reducedA p z ≤ p.a+p.b ↔ threshold p ≤ z := by
  have hz0 := (cut_nonneg p).trans hz
  have hd : 0 < z+2 := by linarith
  have ha := hp.1
  have hb := hp.2.1
  have hep := hp.2.2.2.2.1
  have hA := admissible_A_nonneg p hp z hz
  have hs : 0 < p.a+p.b := by positivity
  have hD : 0 < p.e*(p.a+p.b)^2 := by positivity
  have hf : 0 < 1+p.e*(reducedA p z+(p.a+p.b)) := by positivity
  have hid := residual_reservoir_identity p z hd.ne'
  have hfac : (reducedA p z-(p.a+p.b))*(1+p.e*(reducedA p z+(p.a+p.b))) =
      (p.e-1)*reducedB p z-p.e*(p.a+p.b)^2 := by
    linear_combination he-hid
  have hsign : reducedA p z ≤ p.a+p.b ↔ (p.e-1)*reducedB p z ≤ p.e*(p.a+p.b)^2 := by
    constructor
    · intro h
      have hn := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hf.le
      rw [hfac] at hn
      linarith
    · intro h
      have hn : (reducedA p z-(p.a+p.b))*(1+p.e*(reducedA p z+(p.a+p.b))) ≤ 0 := by
        rw [hfac]
        linarith
      have hn' : (reducedA p z-(p.a+p.b))*(1+p.e*(reducedA p z+(p.a+p.b))) ≤
          0*(1+p.e*(reducedA p z+(p.a+p.b))) := by simpa using hn
      exact sub_nonpos.mp ((mul_le_mul_iff_of_pos_right hf).mp hn')
  rw [hsign, reducedB, ← mul_div_assoc, div_le_iff₀ hd]
  unfold threshold
  rw [sub_le_iff_le_add, div_le_iff₀ hD]
  constructor <;> intro h <;> nlinarith only [h]

theorem threshold_reservoir_identity (p : Rates) (hp : p.Positive)
    (ht : 0 ≤ threshold p) :
    (p.e-1)*reducedB p (threshold p) = p.e*(p.a+p.b)^2 := by
  have hs : 0 < p.a+p.b := by have := hp.1; have := hp.2.1; positivity
  have hD : p.e*(p.a+p.b)^2 ≠ 0 := by have := hp.2.2.2.2.1; positivity
  have hd : threshold p+2 ≠ 0 := by linarith
  have hB : reducedB p (threshold p)*(threshold p+2) = p.a+2*p.b := by
    unfold reducedB
    exact div_mul_cancel₀ _ hd
  have hT : (threshold p+2)*(p.e*(p.a+p.b)^2) = (p.a+2*p.b)*(p.e-1) := by
    dsimp only [threshold]
    rw [sub_add_cancel]
    exact div_mul_cancel₀ _ hD
  apply (mul_right_injective₀ hd)
  linear_combination (p.e-1)*hB-hT

theorem threshold_residual_sign (p : Rates) (hp : p.Positive)
    (ht : admissibleCut p ≤ threshold p) :
    residual p (threshold p) ≤ 0 ↔ reducedA p (threshold p) ≤ p.a+p.b := by
  have ht0 := (cut_nonneg p).trans ht
  have hd : threshold p+2 ≠ 0 := by linarith
  have hA := admissible_A_nonneg p hp _ ht
  have hs : 0 < p.a+p.b := by have := hp.1; have := hp.2.1; positivity
  have he := hp.2.2.2.2.1
  have hf : 0 < 1+p.e*(reducedA p (threshold p)+(p.a+p.b)) := by positivity
  have hi := residual_reservoir_identity p (threshold p) hd
  have hb := threshold_reservoir_identity p hp ht0
  have hfac : residual p (threshold p) =
      (reducedA p (threshold p)-(p.a+p.b))*(1+p.e*(reducedA p (threshold p)+(p.a+p.b))) := by
    linear_combination hi-hb
  rw [hfac]
  have hsign : (reducedA p (threshold p)-(p.a+p.b))*(1+p.e*(reducedA p (threshold p)+(p.a+p.b))) ≤ 0 ↔
      reducedA p (threshold p)-(p.a+p.b) ≤ 0 := by
    simpa using (mul_le_mul_iff_of_pos_right hf :
      (reducedA p (threshold p)-(p.a+p.b))*(1+p.e*(reducedA p (threshold p)+(p.a+p.b))) ≤
      0*(1+p.e*(reducedA p (threshold p)+(p.a+p.b))) ↔ _)
  rw [hsign, sub_nonpos]

theorem root_sign_comparison (p : Rates) (hp : p.Positive) (z t : ℝ)
    (hz : admissibleCut p ≤ z) (ht : admissibleCut p ≤ t) (he : residual p z = 0) :
    residual p t ≤ 0 ↔ t ≤ z := by
  constructor
  · intro hs
    by_contra hn
    have hi := (admissible_increasing p hp z t hz (lt_of_not_ge hn)).2
    linarith
  · intro h
    rcases eq_or_lt_of_le h with h | h
    · rw [h,he]
    · have hi := (admissible_increasing p hp t z ht h).2
      linarith

theorem small_e_threshold (p : Rates) (hp : p.Positive) (he : p.e ≤ 1) :
    threshold p ≤ admissibleCut p := by
  have ha := hp.1
  have hb := hp.2.1
  have hep := hp.2.2.2.2.1
  have hn : (p.a+2*p.b)*(p.e-1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hdiv : (p.a+2*p.b)*(p.e-1)/(p.e*(p.a+p.b)^2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hn (by positivity)
  have hc := cut_nonneg p
  unfold threshold
  linarith

end DisguisedToricAssemblies
