import proofs.RAF1519.Refinement.GraphGrowthBarrier
import proofs.RAF1519.Refinement.CappedExponential
import proofs.RAF1519.Refinement.CompensatedMaterial
import proofs.RAF1519.Refinement.CountNoiseScale

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def stockFence (t : ℝ) := cappedExponential (119/10000) (3/5) (59/1000) t
def stockFenceRate (t : ℝ) :=
  if (119/10000)*Real.exp ((3/5)*t) < 59/1000 then (3/5)*(119/10000)*Real.exp ((3/5)*t) else 0

theorem stockFence_bounds (t : ℝ) (ht : 0 ≤ t) :
    119/10000 ≤ stockFence t ∧ stockFence t ≤ 59/1000 ∧ stockFenceRate t ≤ (3/5)*stockFence t := by
  have he : 1 ≤ Real.exp ((3/5)*t) := Real.one_le_exp_iff.mpr (by linarith)
  have hlow : (119/10000:ℝ) ≤ (119/10000)*Real.exp ((3/5)*t) := by linarith
  constructor
  · exact le_min hlow (by norm_num)
  constructor
  · exact min_le_right _ _
  · unfold stockFenceRate stockFence cappedExponential
    split_ifs with h
    · rw [min_eq_left h.le]
      ring_nf
      exact le_rfl
    · rw [min_eq_right (le_of_not_gt h)]
      norm_num

theorem stock_noise_allowance (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (11/2)*countTolerance Δ ≤ 11/200000 ∧
    (2*Δ+2/3)*((11/2)*countTolerance Δ) ≤ 11/100000 := by
  have hp : 0 < 100000*(1+Δ) := by positivity
  unfold countTolerance
  constructor
  · rw [show (11/2)*(1/(100000*(1+Δ))) = (11/2)/(100000*(1+Δ)) by ring]
    apply (div_le_iff₀ hp).mpr
    linarith
  · rw [show (2*Δ+2/3)*((11/2)*(1/(100000*(1+Δ)))) =
        ((2*Δ+2/3)*(11/2))/(100000*(1+Δ)) by ring]
    apply (div_le_iff₀ hp).mpr
    linarith

/-- A compensated low-stock comparison, requiring the drift bound only in its
    valid low-stock region. Positive violations automatically lie there. -/
theorem compensated_stock_fence {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (Y F v : ℝ → ι → ℝ) (T : ℝ)
    (hc : ∀ i, ContinuousOn (fun t => F t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => F u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, 12/1000 ≤ F 0 i)
    (hn : ∀ t ∈ Set.Ico 0 T, ∀ i, |Y t i-F t i| ≤ (11/2)*countTolerance Δ)
    (hg : ∀ t ∈ Set.Ico 0 T, ∀ i, Y t i ≤ 3/50 →
      (2/3)*Y t i+graphDiffusion k (Y t) i ≤ v t i) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, stockFence t ≤ F t i := by
  have hf : Continuous stockFence := cappedExponential_continuous _ _ _
  have hfd (t : ℝ) : HasDerivWithinAt stockFence (stockFenceRate t) (Set.Ici t) t :=
    cappedExponential_right_derivative _ _ _ t (by norm_num) (by norm_num)
  have hη := mul_nonneg (by norm_num : (0:ℝ) ≤ 11/2) (count_tolerance_positive Δ hΔ).le
  have hallow := stock_noise_allowance Δ hΔ
  have hb := graph_right_barrier_growth k hk hsym (fun t i => stockFence t-F t i)
    (fun t i => stockFenceRate t-v t i) T (2/3)
    (fun i => hf.continuousOn.sub (hc i)) (fun t ht i => (hfd t).sub (hd t ht i))
    (fun i => by have hi := h0 i; norm_num [stockFence,cappedExponential] at *; linarith) (by
      intro t ht i hi
      have hfB := stockFence_bounds t ht.1
      have hy := (abs_le.mp (hn t ht i)).2
      have hsmall : Y t i ≤ 3/50 := by linarith
      have hgi := hg t ht i hsmall
      have hm : ∀ j, |F t j-Y t j| ≤ (11/2)*countTolerance Δ := by
        intro j
        rw [abs_sub_comm]
        exact hn t ht j
      have hD := graphDiffusion_noise_bound k hk Δ ((11/2)*countTolerance Δ) hη hdegree
        (fun j => F t j-Y t j) hm i
      rw [graphDiffusion_sub] at hD
      have hD' := (abs_le.mp hD).2
      have hFi := (abs_le.mp (hm i)).2
      change stockFenceRate t-v t i ≤ graphDiffusion k (fun j => stockFence t-F t j) i+
        (2/3)*(stockFence t-F t i)
      have he : graphDiffusion k (fun j => stockFence t-F t j) i = -graphDiffusion k (F t) i := by
        unfold graphDiffusion
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      nlinarith [hallow.2])
  intro t ht i
  have hi := hb t ht i
  linarith

end
end RAF1519.Refinement
