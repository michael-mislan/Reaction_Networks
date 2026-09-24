import proofs.FiniteCopyReactor.SupplyKernel
import proofs.FiniteCopyReactor.ThreeStageUpper
import proofs.FiniteCopyReactor.FreeRow

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

def supplyCycle (k : SupplyKind) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ → ℝ) (N : BoxCounts V) (z : ℝ) : ℝ :=
  threeStage (supplyKernel false k V r d hV hr hr' hd hd')
    (supplyKernel true k V r d hV hr hr' hd hd') (supplyKernel true k V r d hV hr hr' hd hd')
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) f N z

theorem supply_cycle_upper (k : SupplyKind) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (s K : ℝ) (hs : 0 ≤ s) (N : BoxCounts V) (z : ℝ) :
    supplyCycle k V r d hV hr hr' hd hd' (MarkedKernel.eventIndicator {a | K ≤ a.2}) N z ≤
      Real.exp (-s*K+4*supplyRateCap k*(V:ℝ)*(Real.exp s-1)+s*z) := by
  have hp : 0 ≤ 1+supplyRateCap k/3000*(Real.exp s-1) := by
    have he := Real.one_le_exp_iff.mpr hs
    have hc := supply_rate_cap_nonneg k
    positivity
  have h := three_stage_upper (supplyKernel false k V r d hV hr hr' hd hd')
    (supplyKernel true k V r d hV hr hr' hd hd') (supplyKernel true k V r d hV hr hr' hd hd')
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) s
    (1+supplyRateCap k/3000*(Real.exp s-1)) K hs hp
    (supply_exponential_step false k V r d hV hr hr' hd hd' s hs)
    (supply_exponential_step true k V r d hV hr hr' hd hd' s hs)
    (supply_exponential_step true k V r d hV hr hr' hd hd' s hs) N z
  apply h.trans_eq
  congr 1
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
  ring

theorem food_cycle_upper (k : SupplyKind) (hk : k=.foodU ∨ k=.foodW)
    (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (z : ℝ) (hz : z ≤ (151/200)*(V:ℝ)) :
    supplyCycle k V r d hV hr hr' hd hd'
      (MarkedKernel.eventIndicator {a | 5*(V:ℝ) ≤ a.2}) N z ≤ Real.exp (-(V:ℝ)/300) := by
  have hc : supplyRateCap k=1 := by rcases hk with h|h <;> subst k <;> rfl
  have h := supply_cycle_upper k V r d hV hr hr' hd hd' (1/50) (5*(V:ℝ)) (by norm_num) N z
  apply h.trans
  apply Real.exp_le_exp.mpr
  rw [hc]
  have he := exp_small_quadratic (1/50:ℝ) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left he hV.le
  nlinarith

theorem gross_cycle_upper (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V) :
    supplyCycle .gross V r d hV hr hr' hd hd'
      (MarkedKernel.eventIndicator {a | (V:ℝ)/5 ≤ a.2}) N 0 ≤ Real.exp (-(V:ℝ)/2000) := by
  have h := supply_cycle_upper .gross V r d hV hr hr' hd hd' (1/20) ((V:ℝ)/5) (by norm_num) N 0
  apply h.trans
  apply Real.exp_le_exp.mpr
  dsimp [supplyRateCap]
  have he := exp_small_quadratic (1/20:ℝ) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left he hV.le
  nlinarith

end
end FiniteCopyReactor
