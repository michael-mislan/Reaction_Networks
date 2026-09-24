import proofs.FiniteCopyReactor.CountLaplace
import proofs.FiniteReservoir.PhysicalTrajectory
import proofs.RandomViability.JumpStateLaplace

namespace FiniteReservoir
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped BigOperators
noncomputable section
open FiniteCopyReactor (reactorFood)

theorem reactorTrajectory_transition (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) (k : ℕ) :
    (reactorTrajectory M p V hV N).map (Preorder.frestrictLe k) ⊗ₘ
      jumpHistoryKernel reactorNext (reactorRate M p V)
        (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV) k =
    (reactorTrajectory M p V hV N).map
      (fun x => (Preorder.frestrictLe k x,x (k+1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

theorem reactor_food_exponential_intensity (M : ℕ) (p : Parameters M) (V : ℝ) (N : CountState M) :
    (∑ ch,reactorRate M p V N ch*((2:ℝ)^reactorFood ch-1))=2*V := by
  have he : (∑ ch,reactorRate M p V N ch*((2:ℝ)^reactorFood ch-1)) =
      ∑ ch,FiniteCopyReactor.reactorRate V p.release 0 N.1 ch*((2:ℝ)^reactorFood ch-1) := by
    apply Finset.sum_congr rfl
    intro j _
    cases j with
    | inl j =>
      unfold reactorRate
      rw [rate_binding]
      rfl
    | inr j => simp only [reactorFood,pow_zero,sub_self,mul_zero]
  rw [he]
  exact FiniteCopyReactor.reactor_food_exponential_intensity V p.release 0 N.1


theorem reactor_food_laplace_factor (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) :
    (∑ ch,reactorRate M p V N ch*(2:ℝ)^reactorFood ch)/
      ((∑ ch,reactorRate M p V N ch)+2*V)=1 := by
  have h := reactor_food_exponential_intensity M p V N
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib] at h
  have ht := reactor_total_pos M p V hV N
  apply (div_eq_one_iff_eq (by positivity : (∑ ch,reactorRate M p V N ch)+2*V ≠ 0)).mpr
  linarith

theorem reactor_food_multiplier_integral (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) 
    (N : CountState M) :
    ∫⁻ y,jumpMultiplier (fun ch => (2:ℝ)^reactorFood ch) (2*V) y ∂
      jumpStateKernel reactorNext (reactorRate M p V)
        (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV) N = 1 := by
  rw [jumpState_weight_laplace reactorNext (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)
    (fun ch => (2:ℝ)^reactorFood ch) (fun _ => by positivity) (2*V) N
    (by have ht := reactor_total_pos M p V hV N; positivity)]
  rw [reactor_food_laplace_factor M p V hV N,ENNReal.ofReal_one]

end
end FiniteReservoir
