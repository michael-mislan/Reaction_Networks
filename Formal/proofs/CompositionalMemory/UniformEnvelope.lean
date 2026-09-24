import proofs.HeritableCompositions.GrowingEnvelope

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

/-- A fixed noise budget keeps the exponential constants independent of k and
of the actual positive growth rate (the latter still sets the clock). -/
theorem fixed_noise_budget (γ κ : ℝ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000) :
    1200000000*(γ+κ)^2 ≤ 8000000000*(1/100000000000 : ℝ)^2 := by
  have hs : (γ+κ)^2 ≤ (2/100000000000 : ℝ)^2 := by
    nlinarith only [hγ,hγmax,hκ,hκmax]
  nlinarith only [hs]

theorem uniform_envelope (N γ κ v E L : ℝ) (hN : 0 ≤ N) (hv : 0 ≤ v)
    (hE : E ≤ 42*v)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hL : L ≤ localAlpha*Real.exp (N*localAlpha*E)*
      (-N*v/4+200000000+1200000000*N*(γ+κ)^2)) :
    L ≤ growingCeiling N (1/100000000000) := by
  have hb := mul_le_mul_of_nonneg_left (fixed_noise_budget γ κ hγ hγmax hκ hκmax) hN
  have hp : 0 ≤ localAlpha*Real.exp (N*localAlpha*E) := by
    unfold localAlpha; positivity
  have hbr : -N*v/4+200000000+1200000000*N*(γ+κ)^2 ≤
      -N/4*v+200000000+8000000000*N*(1/100000000000 : ℝ)^2 := by
    nlinarith only [hb]
  exact (hL.trans (mul_le_mul_of_nonneg_left hbr hp)).trans
    (growing_global_envelope N (1/100000000000) v E hN hv hE)

theorem uniform_affine_recovery (N γ κ v E L : ℝ)
    (hN : 140000000000000000000 ≤ N) (hv : 0 ≤ v) (hE : E ≤ 42*v)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (hL : L ≤ localAlpha*Real.exp (N*localAlpha*E)*
      (-N*v/4+200000000+1200000000*N*(γ+κ)^2)) :
    L ≤ -(N*localAlpha*innerEnergy/672)*Real.exp (N*localAlpha*E)+
      (N*localAlpha*innerEnergy/672)*(2*Real.exp (N*localAlpha*innerEnergy/2)) := by
  have hNs : 0 ≤ N := by linarith only [hN]
  have hb := mul_le_mul_of_nonneg_left (fixed_noise_budget γ κ hγ hγmax hκ hκmax) hNs
  have hp : 0 ≤ localAlpha*Real.exp (N*localAlpha*E) := by
    unfold localAlpha; positivity
  have hbr : -N*v/4+200000000+1200000000*N*(γ+κ)^2 ≤
      -N/4*v+200000000+8000000000*N*(1/100000000000 : ℝ)^2 := by
    nlinarith only [hb]
  exact (hL.trans (mul_le_mul_of_nonneg_left hbr hp)).trans
    (growing_affine_recovery N (1/100000000000) v E hN (by norm_num)
      (by norm_num) hv hE)

end CompositionalMemory
