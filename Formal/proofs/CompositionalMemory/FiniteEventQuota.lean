import proofs.CompositionalMemory.FiniteEventBudget
import Mathlib.Analysis.Complex.ExponentialBounds

namespace CompositionalMemory
open FiniteCopy HeritableCompositions
noncomputable section

def quotaFailure {α : Type*} (J : Nat) (z : α × Fin (J+1)) : ℝ :=
  if z.2.val < J then 0 else 1

/-- Exponential uniformization comparison, including counted self-events. -/
theorem quota_exponential_bound {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (J : Nat) (L a : ℝ)
    (hL : 0 ≤ L) (ha : 1 ≤ a) (hrate : ∀ x, M.total x ≤ L)
    (T : NNReal) (x : α) :
    finiteTimeExpectation (eventBudgetModel M J) T (quotaFailure J) (x,0) ≤
      Real.exp (L*(a-1)*(T : ℝ))/a^J := by
  have hap : 0 < a := by linarith
  let f : α × Fin (J+1) → ℝ := fun z => a^z.2.val/a^J
  have hg (z : α × Fin (J+1)) :
      (eventBudgetModel M J).generator f z ≤ L*(a-1)*f z := by
    rcases z with ⟨y,c⟩
    by_cases hc : c.val < J
    · have he : min (c.val+1) J=c.val+1 := Nat.min_eq_left (by omega)
      have hid : (eventBudgetModel M J).generator f (y,c)=M.total y*(a-1)*f (y,c) := by
        simp only [FiniteJumpModel.generator,eventBudgetModel,hc,if_true,f,budgetIndex,he,pow_succ]
        calc
          _ = ∑ r, M.rate y r*((a-1)*(a^c.val/a^J)) := by
            apply Finset.sum_congr rfl
            intro r _
            ring
          _ = _ := by rw [← Finset.sum_mul]; unfold FiniteJumpModel.total; ring
      rw [hid]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hrate y) (sub_nonneg.mpr ha)) (by dsimp [f]; positivity)
    · have hz : (eventBudgetModel M J).generator f (y,c)=0 := by
        simp [FiniteJumpModel.generator,eventBudgetModel,hc]
      rw [hz]
      exact mul_nonneg (mul_nonneg hL (sub_nonneg.mpr ha)) (by dsimp [f]; positivity)
  have hh := finite_time_decay_signed (eventBudgetModel M J) T f (-(L*(a-1)))
    (fun z => by simpa only [neg_neg] using hg z) (x,0)
  have hm (z : α × Fin (J+1)) : quotaFailure J z ≤ f z := by
    by_cases hz : z.2.val < J
    · simp only [quotaFailure,hz,if_true]; dsimp [f]; positivity
    · have he : z.2.val=J := by omega
      simp [quotaFailure,f,he,ne_of_gt hap]
  obtain ⟨q,hq,_,hb⟩ := (eventBudgetModel M J).exists_clock 0
  have hm' := poisson_mono ((eventBudgetModel M J).uniformize q hq hb) (q*T)
    (quotaFailure J) f hm (x,0)
  rw [← finite_time_eq_uniformized,← finite_time_eq_uniformized] at hm'
  exact hm'.trans (by simpa [f,div_eq_mul_inv] using hh)

theorem quota_concrete_constant :
    Real.exp (4000000*((1000001/1000000 : ℝ)-1)*20)/
      (1000001/1000000 : ℝ)^100000000 ≤ 1/5000000 := by
  have hsmall := one_add_mul_le_pow (a := (1/1000000 : ℝ)) (by norm_num) 10000
  norm_num only [Nat.cast_ofNat] at hsmall
  have hb : (101/100 : ℝ) ≤ (1000001/1000000 : ℝ)^10000 := by
    convert hsmall using 1
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 101/100) hb 100
  have hrat : (27/10 : ℝ) ≤ (101/100 : ℝ)^100 := by norm_num
  have hbase : (27/10 : ℝ) ≤ (1000001/1000000 : ℝ)^1000000 := by
    simpa only [← pow_mul] using hrat.trans hpow
  have hden := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10) hbase 100
  rw [← pow_mul] at hden
  have he : Real.exp 1 ≤ (11/4 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hen := pow_le_pow_left₀ (Real.exp_pos 1).le he 80
  rw [← Real.exp_nat_mul] at hen
  simp only [Nat.cast_ofNat,mul_one] at hen
  have hc : (11/4 : ℝ)^80 ≤ (1/5000000)*(27/10)^100 := by norm_num
  have hd := mul_le_mul_of_nonneg_left hden (by norm_num : (0 : ℝ) ≤ 1/5000000)
  rw [show 4000000*((1000001/1000000 : ℝ)-1)*20=80 by norm_num]
  apply (div_le_iff₀ (by positivity)).mpr
  exact hen.trans (hc.trans hd)

/-- Deadline certificate with a sharp exhaustion charge, without rerunning
the chemical backward solve. Frozen exhausted states retain the lifted value. -/
theorem event_quota_deadline {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (h v w : α → ℝ) (δ η s : ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hs : 0 < s)
    (hvu : ∀ x, v x ≤ 1) (hwn : ∀ x, 0 ≤ w x)
    (hrate : ∀ x, M.total x ≤ 4000000)
    (hv : ∀ x, -δ ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -s*w x+η)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α) :
    v x-20*δ-Real.exp (-s*20)*w x-η/s-1/5000000 ≤
      finiteTimeExpectation (eventBudgetModel M 100000000) 20
        (budgetObservable 100000000 h) (x,0) := by
  let B := eventBudgetModel M 100000000
  let V : α × Fin (100000000+1) → ℝ := fun z => v z.1
  have hg (z : α × Fin (100000000+1)) : -δ ≤ B.generator V z := by
    by_cases hz : z.2.val < 100000000
    · simpa [B,V,FiniteJumpModel.generator,eventBudgetModel,hz] using hv z.1
    · simpa [B,FiniteJumpModel.generator,eventBudgetModel,hz] using neg_nonpos.mpr hδ
  have hwg := (event_budget_generators M 100000000 (by norm_num) v w δ η s 4000000
    hδ hη (by norm_num) hvu hwn hrate hv hw).2
  have hc (z : α × Fin (100000000+1)) : V z ≤
      (budgetObservable 100000000 h z+quotaFailure 100000000 z)+budgetObservable 100000000 w z := by
    by_cases hz : z.2.val < 100000000
    · simpa [V,budgetObservable,quotaFailure,hz] using hcover z.1
    · simpa [V,budgetObservable,quotaFailure,hz] using hvu z.1
  have hh := finite_deadline_residual_certificate B 20
    (fun z => budgetObservable 100000000 h z+quotaFailure 100000000 z) V
    (budgetObservable 100000000 w) s δ η hs hη hg hwg hc (x,0)
  have hq := (quota_exponential_bound M 100000000 4000000 (1000001/1000000)
    (by norm_num) (by norm_num) hrate 20 x).trans quota_concrete_constant
  obtain ⟨q,hqp,_,hqb⟩ := B.exists_clock 0
  have hadd : finiteTimeExpectation B 20
      (fun z => budgetObservable 100000000 h z+quotaFailure 100000000 z) (x,0)=
      finiteTimeExpectation B 20 (budgetObservable 100000000 h) (x,0)+
      finiteTimeExpectation B 20 (quotaFailure 100000000) (x,0) := by
    simp only [finite_time_eq_uniformized B q 20 hqp hqb,poisson_additive]
  rw [hadd] at hh
  simp only [V,budgetObservable,Fin.val_zero,show (0 : Nat)<100000000 by decide,
    if_true,NNReal.coe_ofNat] at hh
  change finiteTimeExpectation B 20 (quotaFailure 100000000) (x,0) ≤ _ at hq
  linarith

end
end CompositionalMemory
