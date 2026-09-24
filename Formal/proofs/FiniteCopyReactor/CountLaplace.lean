import proofs.FiniteCopyReactor.CountTrajectory
import proofs.RandomViability.JumpStateLaplace

namespace FiniteCopyReactor
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped BigOperators
noncomputable section

theorem reactorTrajectory_transition (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) (k : ℕ) :
    (reactorTrajectory V r d hV hr hd N).map (Preorder.frestrictLe k) ⊗ₘ
      jumpHistoryKernel reactorNext (reactorRate V r d)
        (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd) k =
    (reactorTrajectory V r d hV hr hd N).map
      (fun x => (Preorder.frestrictLe k x,x (k+1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

theorem reactor_food_exponential_intensity (V r d : ℝ) (N : Counts) :
    (∑ ch,reactorRate V r d N ch*((2:ℝ)^reactorFood ch-1))=2*V := by
  norm_num [Fintype.sum_sum_type,reactorRate,reactorFood,competitionRate,
    countRate,Fin.sum_univ_succ,Fin.ext_iff]
  ring

theorem reactor_food_laplace_factor (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) :
    (∑ ch,reactorRate V r d N ch*(2:ℝ)^reactorFood ch)/
      ((∑ ch,reactorRate V r d N ch)+2*V)=1 := by
  have h := reactor_food_exponential_intensity V r d N
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib] at h
  have ht := reactor_total_pos V r d hV hr hd N
  apply (div_eq_one_iff_eq (by positivity : (∑ ch,reactorRate V r d N ch)+2*V ≠ 0)).mpr
  linarith

theorem reactor_food_multiplier_integral (V r d : ℝ) (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (N : Counts) :
    ∫⁻ y,jumpMultiplier (fun ch => (2:ℝ)^reactorFood ch) (2*V) y ∂
      jumpStateKernel reactorNext (reactorRate V r d)
        (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd) N = 1 := by
  rw [jumpState_weight_laplace reactorNext (reactorRate V r d)
    (reactor_rate_nonneg V r d hV hr hd) (reactor_total_pos V r d hV hr hd)
    (fun ch => (2:ℝ)^reactorFood ch) (fun _ => by positivity) (2*V) N
    (by have ht := reactor_total_pos V r d hV hr hd N; positivity)]
  rw [reactor_food_laplace_factor V r d hV hr hd N,ENNReal.ofReal_one]

end
end FiniteCopyReactor
