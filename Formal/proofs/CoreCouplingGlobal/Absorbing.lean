import proofs.CoreCouplingCAC.Source

namespace CoreCouplingGlobal
open CoreCouplingCAC

noncomputable def flagshipRates (e : ℝ) : Rates := ⟨6,27,16,2,e,1/10000⟩

theorem total_upper_comparison (A B z e : ℝ) (hA : 0 ≤ A) (he : 0 ≤ e) :
    fA (flagshipRates e) A B z + fB (flagshipRates e) A B z ≤
      33-(1-e)*(A+B) := by
  have h₁ := mul_nonneg he hA
  have h₂ := mul_nonneg he (sq_nonneg A)
  dsimp [fA,fB,flagshipRates]
  nlinarith only [h₁,h₂]

/-- W=z+7H/4 yields a bound independent of the small degradation rate. -/
theorem weighted_upper_comparison (A B z H e : ℝ)
    (hAM : A ≤ 34) (hB : 0 ≤ B) (hz : 0 ≤ z) (hH : 0 ≤ H) :
    fZ (flagshipRates e) A B z H + (7/4:ℝ)*fH (flagshipRates e) z H ≤
      5364/49-(2/7:ℝ)*(z+(7/4:ℝ)*H) := by
  have hBZ := mul_nonneg hB hz
  have hs := sq_nonneg (z-86/7)
  dsimp [fZ,fH,flagshipRates]
  nlinarith only [hAM,hBZ,hH,hs]

theorem z_entry_drift (A B z H e : ℝ)
    (hAM : A ≤ 34) (hB : 0 ≤ B) (hz : 12 ≤ z)
    (hW : z+(7/4:ℝ)*H ≤ 384) :
    fZ (flagshipRates e) A B z H ≤ -(674/7:ℝ) := by
  have hBZ : 0 ≤ B*z := mul_nonneg hB (by linarith)
  have hs : 144 ≤ z^2 := by nlinarith only [hz,sq_nonneg (z-12)]
  dsimp [fZ,flagshipRates]
  nlinarith only [hAM,hBZ,hz,hW,hs]

theorem B_entry_drift (A B z e : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hBM : B ≤ 2) (hzM : z ≤ 12)
    (he : 0 ≤ e) (heM : e ≤ 1/50000) :
    (24999/25000:ℝ) ≤ fB (flagshipRates e) A B z := by
  have hBZ : B*z ≤ 24 := by
    calc
      B*z ≤ B*12 := mul_le_mul_of_nonneg_left hzM hB
      _ ≤ 24 := by linarith
  have heB : e*B ≤ (1/25000:ℝ) := by
    calc
      e*B ≤ (1/50000:ℝ)*2 := mul_le_mul heM hBM hB (by norm_num)
      _ = _ := by norm_num
  have hAA := mul_nonneg he (sq_nonneg A)
  dsimp [fB,flagshipRates]
  nlinarith only [hA,hBM,hBZ,heB,hAA]

theorem z_linear_comparison (A B z H e : ℝ)
    (hAM : A ≤ 34) (hB : 0 ≤ B) (hz : 0 ≤ z)
    (hW : z+(7/4:ℝ)*H ≤ 384) :
    fZ (flagshipRates e) A B z H ≤ (8878/7:ℝ)-(796/7:ℝ)*z := by
  have hBZ := mul_nonneg hB hz
  have hs := sq_nonneg (z-12)
  dsimp [fZ,flagshipRates]
  nlinarith only [hAM,hBZ,hW,hs]

theorem B_linear_comparison (A B z e : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hzM : z ≤ 12) (he : 0 ≤ e) :
    -fB (flagshipRates e) A B z ≤ -27-(13+e)*(-B) := by
  have hBZ := mul_le_mul_of_nonneg_left hzM hB
  have hAA := mul_nonneg he (sq_nonneg A)
  dsimp [fB,flagshipRates]
  nlinarith only [hA,hBZ,hAA]

end CoreCouplingGlobal
