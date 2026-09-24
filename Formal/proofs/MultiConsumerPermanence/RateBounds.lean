import proofs.MultiConsumerPermanence.RateSource

namespace MultiConsumerPermanence
open RobustPermanence
open scoped BigOperators

theorem copying_load_upper {n : ℕ} (r : Rates n) (x : Fin n → ℝ) (delta : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hk : ∀ i, |r.k i-1| ≤ delta) :
    copyingLoad r x ≤ (1+delta)*total x := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (show r.k i ≤ 1+delta by linarith [(abs_le.mp (hk i)).2]) (hx i))
  simpa only [copyingLoad,total,Finset.mul_sum] using hh

theorem consumer_error {n : ℕ} (r : Rates n) (delta z : ℝ)
    (hd : 0 ≤ delta) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hk : ∀ i, |r.k i-1| ≤ delta) (hm : ∀ i, |r.mu i-1/2| ≤ delta) (i : Fin n) :
    |(r.k i*z-r.mu i)-(z-1/2)| ≤ 13*delta := by
  obtain ⟨hkL,hkU⟩ := abs_le.mp (hk i)
  obtain ⟨hmL,hmU⟩ := abs_le.mp (hm i)
  have hL := mul_le_mul_of_nonneg_right hkL hz
  have hU := mul_le_mul_of_nonneg_right hkU hz
  have hdz := mul_le_mul_of_nonneg_left hz' hd
  apply abs_le.mpr
  constructor <;> nlinarith only [hL,hU,hmL,hmU,hdz]

theorem loss_total_upper {n : ℕ} (r : Rates n) (x : Fin n → ℝ) (delta : ℝ)
    (hd : 0 ≤ delta) (hx : ∀ i, 0 ≤ x i) (hr : ∀ i, |r.rho i-(n:ℝ)| ≤ delta) :
    lossTotal r x ≤ ((n:ℝ)+delta)*(total x)^2 := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right
      (show r.rho i ≤ (n:ℝ)+delta by linarith [(abs_le.mp (hr i)).2]) (sq_nonneg (x i)))
  have hh' : lossTotal r x ≤ ((n:ℝ)+delta)*squares x := by
    simpa only [lossTotal,squares,Finset.mul_sum] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_left (squares_bounds x hx).1 (by positivity))

theorem loss_total_lower {n : ℕ} (hn : 0 < n) (r : Rates n) (x : Fin n → ℝ)
    (delta : ℝ) (hd : delta ≤ rateRadius) (hx : ∀ i, 0 ≤ x i)
    (hr : ∀ i, |r.rho i-(n:ℝ)| ≤ delta) :
    (999/1000:ℝ)*(total x)^2 ≤ lossTotal r x := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hrl (i : Fin n) : (999/1000:ℝ)*(n:ℝ) ≤ r.rho i := by
    have h := (abs_le.mp (hr i)).1
    dsimp [rateRadius] at hd
    linarith only [h,hd,hn1]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hrl i) (sq_nonneg (x i)))
  have hh' : (999/1000:ℝ)*(n:ℝ)*squares x ≤ lossTotal r x := by
    simpa only [lossTotal,squares,Finset.mul_sum] using hh
  have hc := (squares_bounds x hx).2
  linarith only [hh',hc]

theorem growth_total_bounds {n : ℕ} (r : Rates n) (x : Fin n → ℝ) (z delta : ℝ)
    (hd : 0 ≤ delta) (hx : ∀ i, 0 ≤ x i) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hk : ∀ i, |r.k i-1| ≤ delta) (hm : ∀ i, |r.mu i-1/2| ≤ delta) :
    (z-1/2-13*delta)*total x ≤ growthTotal r z x ∧
      growthTotal r z x ≤ (z-1/2+13*delta)*total x := by
  have he := fun i => abs_le.mp (consumer_error r delta z hd hz hz' hk hm i)
  constructor
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (show z-1/2-13*delta ≤ r.k i*z-r.mu i by linarith [(he i).1]) (hx i))
    simpa only [growthTotal,total,Finset.sum_mul,mul_comm] using hh
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (show r.k i*z-r.mu i ≤ z-1/2+13*delta by linarith [(he i).2]) (hx i))
    simpa only [growthTotal,total,Finset.sum_mul,mul_comm] using hh

theorem perturbed_aggregate_upper_drift {n : ℕ} (hn : 0 < n) (e delta : ℝ)
    (r : Rates n) (h : Near e delta r) (hd : 0 ≤ delta) (hd' : delta ≤ rateRadius)
    (z : ℝ) (x : Fin n → ℝ) (hz : 0 ≤ z) (hz' : z ≤ 12) (hx : ∀ i, 0 ≤ x i) :
    growthTotal r z x-lossTotal r x ≤ 139-12*total x := by
  have hg := (growth_total_bounds r x z delta hd hx hz hz' h.k h.mu).2
  have hl := loss_total_lower hn r x delta hd' hx h.rho
  have ha : z-1/2+13*delta ≤ 1151/100 := by
    dsimp [rateRadius] at hd'
    linarith only [hz',hd']
  have hg' := hg.trans (mul_le_mul_of_nonneg_right ha (total_nonneg x hx))
  nlinarith only [hg',hl,sq_nonneg (total x-11755/999)]

end MultiConsumerPermanence
