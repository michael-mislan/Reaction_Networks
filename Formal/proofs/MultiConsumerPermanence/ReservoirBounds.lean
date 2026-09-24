import proofs.MultiConsumerPermanence.ReservoirSource
import proofs.MultiConsumerPermanence.TotalPersistence

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology Set

theorem reservoir_eventually_upper {n : ℕ} (e d : ℝ) (hd : 0 < d)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e d d Y x R) : ∀ᶠ t in atTop, R t < 2 := by
  apply eventual_upper_of_linear_drift R
    (fun t => d-d*R t-R t*(Y t).z*total (x t)) 0 d d 2 hd (by rw [div_self (ne_of_gt hd)]; norm_num)
  · exact h.dR
  · intro t ht
    have hp := mul_nonneg ((h.reservoir_positive t ht).le)
      (mul_nonneg (h.positive t ht).2.2.1.le
        (total_nonneg (x t) (fun i => (h.consumer_positive t ht i).le)))
    nlinarith only [hp]

theorem reservoir_total_upper {n : ℕ} (e d : ℝ) (hd : 0 < d)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e d d Y x R) : ∀ᶠ t in atTop, total (x t) < 24 := by
  have hb := loaded_eventually_resident_absorbing e he he' Y _ h.toIsLoadedResidentTrajectory
  have hr := reservoir_eventually_upper e d hd Y x R h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ (Y t).z ≤ 12 ∧ R t ≤ 2 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hb,hr] with t ht hb hr
    exact ⟨ht,hb.2.2.1.le,hr.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  apply eventual_upper_of_linear_drift (fun t => total (x t))
    (fun t => (R t*(Y t).z-1/2)*total (x t)-(n:ℝ)*squares (x t))
    T (9025/16) 24 24 (by norm_num) (by norm_num)
  · intro t ht
    exact reservoir_total_deriv e d d Y x R h t (hT t ht).1
  · intro t ht
    obtain ⟨h0,hz,hr⟩ := hT t ht
    have hx := fun i => (h.consumer_positive t h0 i).le
    have hS := total_nonneg (x t) hx
    have hQ := (squares_bounds (x t) hx).2
    have hRz : R t*(Y t).z ≤ 24 := by
      have hh := mul_le_mul_of_nonneg_right hr (h.positive t h0).2.2.1.le
      linarith only [hh,hz]
    have hh := mul_le_mul_of_nonneg_right hRz hS
    nlinarith only [hQ,hh,sq_nonneg (total (x t)-95/4)]

theorem reservoir_eventually_lower {n : ℕ} (e d dmin dmax : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ d) (hd' : d ≤ dmax)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e d d Y x R) :
    ∀ᶠ t in atTop, dmin/(2*(dmax+288)) < R t := by
  have hd0 : 0 < d := lt_of_lt_of_le hdmin hd
  have hc : 0 < dmax+288 := by linarith
  have hb := loaded_eventually_resident_absorbing e he he' Y _ h.toIsLoadedResidentTrajectory
  have hs := reservoir_total_upper e d hd0 he he' Y x R h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ (Y t).z ≤ 12 ∧ total (x t) ≤ 24 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hb,hs] with t ht hb hs
    exact ⟨ht,hb.2.2.1.le,hs.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hh : ∀ᶠ t in atTop, -R t < -(dmin/(2*(dmax+288))) := by
    apply eventual_upper_of_linear_drift (fun t => -R t)
      (fun t => -(d-d*R t-R t*(Y t).z*total (x t)))
      T (-dmin) (dmax+288) (-(dmin/(2*(dmax+288)))) hc
    · field_simp
      nlinarith only [hdmin]
    · intro t ht
      exact (h.dR t (hT t ht).1).neg
    · intro t ht
      obtain ⟨h0,hz,hs⟩ := hT t ht
      have hR := (h.reservoir_positive t h0).le
      have hzS : (Y t).z*total (x t) ≤ 288 :=
        (mul_le_mul hz hs (total_nonneg (x t) (fun i => (h.consumer_positive t h0 i).le))
          (by norm_num)).trans (by norm_num)
      have hprod := mul_le_mul_of_nonneg_left hzS hR
      have hw := mul_le_mul_of_nonneg_right hd' hR
      nlinarith only [hprod,hw,hd]
  filter_upwards [hh] with t ht
  linarith only [ht]

end MultiConsumerPermanence
