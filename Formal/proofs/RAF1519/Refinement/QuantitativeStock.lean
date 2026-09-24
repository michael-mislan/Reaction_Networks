import proofs.RAF1519.Refinement.CompensatedStockFence

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

theorem compensated_stock_margin {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (Δ η a cap rate : ℝ) (hη : 0 ≤ η) (ha : 0 ≤ a) (har : 0 ≤ rate)
    (hcap : a ≤ cap) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (hsmall : cap+η ≤ 3/50) (hrate : rate ≤ 2/3)
    (hslack : (2*Δ+2/3)*η ≤ (2/3-rate)*a)
    (Y F v : ℝ → ι → ℝ) (T : ℝ)
    (hc : ∀ i, ContinuousOn (fun t => F t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => F u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, a ≤ F 0 i)
    (hn : ∀ t ∈ Set.Ico 0 T, ∀ i, |Y t i-F t i| ≤ η)
    (hg : ∀ t ∈ Set.Ico 0 T, ∀ i, Y t i ≤ 3/50 →
      (2/3)*Y t i+graphDiffusion k (Y t) i ≤ v t i) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, cappedExponential a rate cap t ≤ F t i := by
  let f := cappedExponential a rate cap
  let g := fun t => if a*Real.exp (rate*t)<cap then rate*a*Real.exp (rate*t) else 0
  have hf : Continuous f := cappedExponential_continuous _ _ _
  have hfd (t : ℝ) : HasDerivWithinAt f (g t) (Set.Ici t) t :=
    cappedExponential_right_derivative _ _ _ t ha har
  have hbounds (t : ℝ) (ht : 0 ≤ t) : a ≤ f t ∧ f t ≤ cap ∧ g t ≤ rate*f t := by
    have he := Real.one_le_exp_iff.mpr (mul_nonneg har ht)
    have hlo : a ≤ a*Real.exp (rate*t) := by nlinarith
    refine ⟨le_min hlo hcap,min_le_right _ _,?_⟩
    dsimp [g,f,cappedExponential]
    split_ifs with h
    · rw [min_eq_left h.le]; ring_nf; exact le_rfl
    · rw [min_eq_right (le_of_not_gt h)]; exact mul_nonneg har (ha.trans hcap)
  have hb := graph_right_barrier_growth k hk hsym (fun t i => f t-F t i)
    (fun t i => g t-v t i) T (2/3)
    (fun i => hf.continuousOn.sub (hc i)) (fun t ht i => (hfd t).sub (hd t ht i))
    (fun i => by have hi := h0 i; simpa [f,cappedExponential,min_eq_left hcap] using sub_nonpos.mpr hi) (by
      intro t ht i hi
      have hfB := hbounds t ht.1
      have hy := (abs_le.mp (hn t ht i)).2
      have hlow : Y t i ≤ 3/50 := by linarith
      have hgi := hg t ht i hlow
      have hm : ∀ j, |F t j-Y t j| ≤ η := by
        intro j; rw [abs_sub_comm]; exact hn t ht j
      have hD := graphDiffusion_noise_bound k hk Δ η hη hdegree (fun j => F t j-Y t j) hm i
      rw [graphDiffusion_sub] at hD
      have hD' := (abs_le.mp hD).2
      have hFi := (abs_le.mp (hm i)).2
      change g t-v t i ≤ graphDiffusion k (fun j => f t-F t j) i+(2/3)*(f t-F t i)
      have he : graphDiffusion k (fun j => f t-F t j) i = -graphDiffusion k (F t) i := by
        unfold graphDiffusion
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _; ring
      rw [he]
      nlinarith [mul_nonneg (sub_nonneg.mpr hrate) (sub_nonneg.mpr hfB.1)])
  intro t ht i
  have hi := hb t ht i
  linarith

def relaxedTolerance (Δ : ℝ) : ℝ := 1/(10000*(1+Δ))
def relaxedFence (t : ℝ) : ℝ := cappedExponential (59/5000) (11/20) (13/250) t

theorem relaxed_stock_margins (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (11/2)*relaxedTolerance Δ ≤ 11/20000 ∧
    (2*Δ+2/3)*((11/2)*relaxedTolerance Δ) ≤ (2/3-11/20)*(59/5000) := by
  have hp : 0 < 10000*(1+Δ) := by positivity
  unfold relaxedTolerance
  constructor
  · rw [show (11/2)*(1/(10000*(1+Δ)))=(11/2)/(10000*(1+Δ)) by ring]
    apply (div_le_iff₀ hp).mpr
    linarith
  · rw [show (2*Δ+2/3)*((11/2)*(1/(10000*(1+Δ))))=((2*Δ+2/3)*(11/2))/(10000*(1+Δ)) by ring]
    apply (div_le_iff₀ hp).mpr
    linarith

theorem relaxed_fence_saturated (t : ℝ) (ht : 11/4 ≤ t) : relaxedFence t=13/250 := by
  have he : (13/250:ℝ) ≤ (59/5000)*Real.exp (121/80) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 121/80) 5
    norm_num [Finset.sum_range_succ,Nat.factorial] at h
    linarith
  exact min_eq_right (he.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (show (121/80:ℝ) ≤ (11/20)*t by linarith)) (by norm_num)))

theorem relaxed_output_margins :
    (13/250-11/20000:ℝ)>1/20 ∧
    (5/7:ℝ)*(13/250-11/20000)-1/1000 > 1/56+1/10000 ∧
    ((13/250:ℝ)-11/20000)/8-8/10000-1/1000 > 1/1080+1/10000 := by norm_num

end
end RAF1519.Refinement
