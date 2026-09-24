import proofs.MultiConsumerPermanence.ReferencePermanence

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology Set
open scoped BigOperators

/-- Scalar multiplicative dynamics preserve the zero face, with no sign
assumption on a competing trajectory. -/
theorem homogeneous_zero_preserved (x a : ℝ → ℝ) (ha : ContinuousOn a (Ici 0))
    (hd : ∀ t, 0 ≤ t → HasDerivAt x (a t*x t) t) (hx0 : x 0 = 0) :
    ∀ t, 0 ≤ t → x t = 0 := by
  intro t ht
  have hb := (isCompact_Icc : IsCompact (Icc (0:ℝ) t)).bddAbove_image
    ((continuous_norm.comp_continuousOn ha).mono (fun _ h => h.1))
  obtain ⟨K,hK⟩ := hb
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K)
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hd s hs.1).hasDerivWithinAt) hx0 ?_ t ⟨ht,le_rfl⟩
  intro s hs
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact hK ⟨s,⟨hs.1,hs.2.le⟩,rfl⟩

theorem reference_consumer_zero_face {n : ℕ} (Y : ℝ → State) (x : ℝ → Fin n → ℝ)
    (hY : ContinuousOn (fun t => (Y t).z) (Ici 0)) (hx : ∀ i, ContinuousOn (fun t => x t i) (Ici 0))
    (hd : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => x s i)
      (x t i*((Y t).z-1/2-(n:ℝ)*x t i)) t)
    (i : Fin n) (h0 : x 0 i = 0) : ∀ t, 0 ≤ t → x t i = 0 := by
  apply homogeneous_zero_preserved (fun t => x t i) (fun t => (Y t).z-1/2-(n:ℝ)*x t i)
    ((hY.sub continuousOn_const).sub ((hx i).const_mul (n:ℝ))) _ h0
  intro t ht
  simpa only [mul_comm] using hd t ht i

theorem equal_composition_total {n : ℕ} (hn : 0 < n) (S : ℝ) :
    total (fun _ : Fin n => S/(n:ℝ)) = S := by
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [total,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

/-- The diagonal lift of the original five-species source is an exact source
solution with n distinct consumers and their own quadratic losses. -/
theorem equal_composition_lift {n : ℕ} (hn : 0 < n) (e : ℝ) (Y : ℝ → State) (S : ℝ → ℝ)
    (h : IsConsumerTrajectory e Y S) :
    IsMultiTrajectory n e Y (fun t _ => S t/(n:ℝ)) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hsum := fun t => equal_composition_total hn (S t)
  refine {
    positive := h.positive
    load_nonnegative := ?_
    dA := h.dA
    dB := h.dB
    dz := ?_
    dH := h.dH
    consumer_positive := ?_
    dx := ?_ }
  · intro t ht
    rw [hsum]
    exact (h.consumer_positive t ht).le
  · intro t ht
    simpa only [hsum] using h.dz t ht
  · intro t ht _
    exact div_pos (h.consumer_positive t ht) hnR
  · intro t ht _
    convert (h.dx t ht).div_const (n:ℝ) using 1
    field_simp

theorem reference_pairwise_ratio_limit {n : ℕ} (hn : 0 < n) (e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (Y : ℝ → State) (x : ℝ → Fin n → ℝ)
    (h : IsMultiTrajectory n e Y x) (i j : Fin n) :
    Tendsto (fun t => x t i/x t j) atTop (𝓝 1) := by
  obtain ⟨eta,heta,hfloor⟩ := reference_trajectory_permanence hn
  have hf := hfloor e he he' Y x h
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hf.and (eventually_ge_atTop (0:ℝ)))
  let E := fun t => (x t i/x t j-1)^2
  have hE : ∀ t, T ≤ t → HasDerivAt E (-2*(n:ℝ)*x t i*E t) t := by
    intro t ht
    have h0 := (hT t ht).2
    have hj : x t j ≠ 0 := ne_of_gt (h.consumer_positive t h0 j)
    have hq := (h.dx t h0 i).div (h.dx t h0 j) hj
    convert ((hq.sub_const 1).pow 2) using 1
    dsimp [E]
    field_simp
    ring
  have hsmall : ∀ eps : ℝ, 0 < eps → ∀ᶠ t in atTop, E t < eps^2 := by
    intro eps heps
    apply eventual_upper_of_linear_drift E (fun t => -2*(n:ℝ)*x t i*E t)
      T 0 (2*(n:ℝ)*eta) (eps^2) (by have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn; positivity)
      (by simp only [zero_div]; positivity) hE
    intro t ht
    have hx := (hT t ht).1.2.2.2.2 i
    have hm := mul_le_mul_of_nonneg_right hx (sq_nonneg (x t i/x t j-1))
    have hmn := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    dsimp [E]
    nlinarith only [hmn]
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hsmall (1-a) (by linarith)] with t ht
    dsimp [E] at ht
    nlinarith only [ht,ha]
  · intro b hb
    filter_upwards [hsmall (b-1) (by linarith)] with t ht
    dsimp [E] at ht
    nlinarith only [ht,hb]

theorem permanent_copying_and_loss_throughput {n : ℕ} (hn : 0 < n) (e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (Y : ℝ → State) (x : ℝ → Fin n → ℝ)
    (h : IsMultiTrajectory n e Y x) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop, ∀ i,
      q ≤ (Y t).z*x t i ∧ q ≤ (1/2)*x t i+(n:ℝ)*(x t i)^2 := by
  obtain ⟨eta,heta,hfloor⟩ := reference_trajectory_permanence hn
  refine ⟨min (eta^2) (eta/2),lt_min (by positivity) (by positivity),?_⟩
  filter_upwards [hfloor e he he' Y x h] with t ht
  intro i
  have hx := ht.2.2.2.2 i
  have hz := ht.2.2.1
  have hp := mul_le_mul hz hx heta.le (heta.le.trans hz)
  have hq := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg (x t i))
  constructor
  · have hm : min (eta^2) (eta/2) ≤ eta^2 := min_le_left _ _
    nlinarith only [hp,hm]
  · have hm : min (eta^2) (eta/2) ≤ eta/2 := min_le_right _ _
    linarith only [hx,hq,hm]

end MultiConsumerPermanence
