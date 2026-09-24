import proofs.MultiConsumerPermanence.RateTotalPersistence
import proofs.MultiConsumerPermanence.RateComposition
import proofs.MultiConsumerPermanence.RateResidentFloors

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology

theorem ratio_damping_species_floor (S x v : ℝ → ℝ) (T s C k : ℝ)
    (hC : 0 < C) (hk : 0 < k)
    (hx : ∀ t, T ≤ t → 0 < x t) (hS : ∀ t, T ≤ t → s ≤ S t)
    (du : ∀ t, T ≤ t → HasDerivAt (fun t => S t/x t) (v t) t)
    (hu : ∀ t, T ≤ t → v t ≤ C-k*(S t/x t)) :
    ∀ᶠ t in atTop, s*k/(2*C) < x t := by
  have hr : ∀ᶠ t in atTop, S t/x t < 2*C/k := by
    apply eventual_upper_of_linear_drift _ v T C k (2*C/k) hk _ du hu
    apply (div_lt_div_iff_of_pos_right hk).2
    linarith only [hC]
  filter_upwards [hr,eventually_ge_atTop T] with t ht htT
  have hh := (div_lt_iff₀ (hx t htT)).mp ht
  have hm := mul_lt_mul_of_pos_right ((hS t htT).trans_lt hh) hk
  apply (div_lt_iff₀ (mul_pos (by norm_num) hC)).2
  field_simp at hm
  nlinarith only [hm]

/-- One physical floor for the entire full independent-rate cube, for all
source-positive trajectories. Existence is discharged by the separate flow module. -/
theorem robust_trajectory_floor {n : ℕ} (hn : 0 < n) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ e : ℝ, 1/200000 ≤ e → e ≤ 1/50000 →
      ∀ r : Rates n, Near e (robustRadius n) r →
      ∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ), IsPerturbedTrajectory r Y x →
      ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
        eta ≤ (Y t).H ∧ ∀ i, eta ≤ x t i := by
  let s := robustTotalFloor n
  have hs : 0 < s := robustTotalFloor_pos n
  let etaX : ℝ := s*(s/4)/(2*(((n:ℝ)+1)*12))
  have hetaX : 0 < etaX := by dsimp [etaX]; positivity
  refine ⟨min (1/250) etaX,lt_min (by norm_num) hetaX,?_⟩
  intro e he he' r hr Y x h
  have hd : 0 ≤ robustRadius n := (robustRadius_pos n).le
  have hd' : robustRadius n ≤ rateRadius := min_le_left _ _
  have hds : robustRadius n ≤ s/1000 := min_le_right _ _
  have hl := perturbed_total_lower hn e _ r hr hd hd' he he' Y x h
  have hu := perturbed_total_upper hn e _ r hr hd hd' he he' Y x h
  have hb := perturbed_resident_box e _ r hr hd' he he' Y x h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ s ≤ total (x t) ∧ total (x t) ≤ 12 ∧
      0 ≤ (Y t).z ∧ (Y t).z ≤ 12 := by
    filter_upwards [hl,hu,hb] with t hlt hut hbt
    exact ⟨hbt.1,hlt.le,by linarith,hbt.2.2.2.1⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hi (i : Fin n) : ∀ᶠ t in atTop, etaX < x t i := by
    apply ratio_damping_species_floor (fun t => total (x t)) (fun t => x t i)
      (fun t => ((growthTotal r (Y t).z (x t)-lossTotal r (x t))*x t i-
        total (x t)*(x t i*(r.k i*(Y t).z-r.mu i-r.rho i*x t i)))/(x t i)^2)
      T s (((n:ℝ)+1)*12) (s/4) (by positivity) (by positivity)
    · intro t ht
      exact h.consumer_positive t (hT t ht).1 i
    · intro t ht
      exact (hT t ht).2.1
    · intro t ht
      exact (perturbed_total_deriv r Y x h t (hT t ht).1).div
        (h.dx t (hT t ht).1 i) (ne_of_gt (h.consumer_positive t (hT t ht).1 i))
    · intro t ht
      obtain ⟨h0,hSl,hSu,hz,hz'⟩ := hT t ht
      have hx := fun j => (h.consumer_positive t h0 j).le
      have herror := consumer_error r (robustRadius n) (Y t).z hd hz hz' hr.k hr.mu
      have hA := weighted_growth_error (x t) (fun j => r.k j*(Y t).z-r.mu j)
        ((Y t).z-1/2) (13*robustRadius n) hx herror i
      have hH := loss_total_lower hn r (x t) (robustRadius n) hd' hx hr.rho
      have hrho : r.rho i ≤ (n:ℝ)+1 := by
        have hh := (abs_le.mp (hr.rho i)).2
        dsimp [rateRadius] at hd'
        linarith only [hh,hd']
      apply heterogeneous_ratio_drift _ _ _ _ _ _ ((n:ℝ)+1) (13*robustRadius n) s 12
        (h.consumer_positive t h0 i) hs hSl hSu (by positivity) hrho
      · linarith only [hds,hs]
      · exact hA
      · nlinarith only [hH,sq_nonneg (total (x t))]
  have hall : ∀ᶠ t in atTop, ∀ i, etaX < x t i := Filter.eventually_all.2 hi
  have hresident := rate_loaded_eventually_resident_floors (baseRates r)
    (RateNeighborhood.box e _ he he' (near_base e _ r hr hd')) Y _ h.toIsRateLoadedTrajectory
    (perturbed_load_upper hn e _ r hr hd hd' he he' Y x h)
  filter_upwards [hresident,hall] with t ht hx
  have hm : min (1/250:ℝ) etaX ≤ 1/250 := min_le_left _ _
  refine ⟨by linarith [ht.1],by linarith [ht.2.1],by linarith [ht.2.2.1],
    by linarith [ht.2.2.2],fun i => (min_le_right _ _).trans (hx i).le⟩

end MultiConsumerPermanence
