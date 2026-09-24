import proofs.MultiConsumerPermanence.SharpRecovery
import proofs.MultiConsumerPermanence.ReservoirRecovery
import proofs.MultiConsumerPermanence.ReservoirRateRecovery

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology

theorem sharp_reference_source_floor {n : ℕ} (hn : 0 < n)
    (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (h : IsMultiTrajectory n e Y x) :
    ∀ᶠ t in atTop, ∀ i, totalFloor n/(2*(n:ℝ)) < x t i := by
  let s := totalFloor n
  have hs : 0 < s := totalFloor_pos n
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let etaX := s/(2*(n:ℝ))
  have hl := total_eventually_lower hn e he he' Y x h
  have hu := total_eventually_upper hn e he he' Y x h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ s ≤ total (x t) ∧ total (x t) ≤ 12 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hl,hu] with t h0 hl hu
    exact ⟨h0,hl.le,hu.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hi (i : Fin n) : ∀ᶠ t in atTop, etaX < x t i := by
    exact sharp_reference_recovery (fun t => total (x t)) (fun t => squares (x t))
      (fun t => x t i) (fun t => (Y t).z-1/2) T n s hnR hs
      (fun t ht => h.consumer_positive t (hT t ht).1 i)
      (fun t ht => (hT t ht).2.1)
      (fun t ht => (squares_bounds (x t)
        (fun j => (h.consumer_positive t (hT t ht).1 j).le)).2)
      (fun t ht => total_hasDerivAt e Y x h t (hT t ht).1)
      (fun t ht => h.dx t (hT t ht).1 i)
  exact Filter.eventually_all.2 hi

theorem sharp_reservoir_source_floor {n : ℕ} (hn : 0 < n)
    (e d dmin : ℝ) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ) (h : IsReservoirTrajectory n e d d Y x R) :
    ∀ᶠ t in atTop, ∀ i, reservoirTotalFloor n dmin/(2*(n:ℝ)) < x t i := by
  let s := reservoirTotalFloor n dmin
  have hs : 0 < s := reservoirTotalFloor_pos n dmin hdmin
  have hd0 := lt_of_lt_of_le hdmin hd
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let etaX := s/(2*(n:ℝ))
  have hl := reservoir_total_lower hn e d dmin hdmin hd he he' Y x R h
  have hu := reservoir_total_upper e d hd0 he he' Y x R h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ s ≤ total (x t) ∧ total (x t) ≤ 24 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hl,hu] with t h0 hl hu
    exact ⟨h0,hl.le,hu.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hi (i : Fin n) : ∀ᶠ t in atTop, etaX < x t i := by
    exact sharp_reference_recovery (fun t => total (x t)) (fun t => squares (x t))
      (fun t => x t i) (fun t => R t*(Y t).z-1/2) T n s hnR hs
      (fun t ht => h.consumer_positive t (hT t ht).1 i)
      (fun t ht => (hT t ht).2.1)
      (fun t ht => (squares_bounds (x t)
        (fun j => (h.consumer_positive t (hT t ht).1 j).le)).2)
      (fun t ht => reservoir_total_deriv e d d Y x R h t (hT t ht).1)
      (fun t ht => h.dx t (hT t ht).1 i)
  exact Filter.eventually_all.2 hi

theorem sharp_robust_source_floor {n : ℕ} (hn : 0 < n)
    (e : ℝ) (he : 1/200000 ≤ e) (he' : e ≤ 1/50000) (r : Rates n)
    (hr : Near e (robustRadius n) r) (Y : ℝ → State) (x : ℝ → Fin n → ℝ)
    (h : IsPerturbedTrajectory r Y x) :
    ∀ᶠ t in atTop, ∀ i, robustTotalFloor n/(8*((n:ℝ)+1)) < x t i := by
  let s := robustTotalFloor n
  have hs : 0 < s := robustTotalFloor_pos n
  let etaX := s/(8*((n:ℝ)+1))
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
    have heq : etaX = s*(1/4)/(2*((n:ℝ)+1)) := by dsimp [etaX]; field_simp; ring
    rw [heq]
    apply sharp_species_floor (fun t => total (x t)) (fun t => x t i)
      (fun t => ((growthTotal r (Y t).z (x t)-lossTotal r (x t))*x t i-
        total (x t)*(x t i*(r.k i*(Y t).z-r.mu i-r.rho i*x t i)))/(x t i)^2)
      T ((n:ℝ)+1) (1/4) s (by positivity) (by norm_num) hs
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
      have hquarter : (1/4:ℝ)*(total (x t)/x t i) = (total (x t)/x t i)/4 := by ring
      rw [hquarter]
      apply sharp_perturbed_ratio_drift _ _ _ _ _ _ ((n:ℝ)+1) (13*robustRadius n) s
        (h.consumer_positive t h0 i) hs hSl hrho
      · linarith only [hds,hs]
      · exact hA
      · nlinarith only [hH,sq_nonneg (total (x t))]
  exact Filter.eventually_all.2 hi

theorem sharp_robust_reservoir_source_floor {n : ℕ} (hn : 0 < n)
    (e d dmin : ℝ) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000) (r : ReservoirRates n)
    (hr : ReservoirNear e d (reservoirRobustRadius n dmin) r)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) :
    ∀ᶠ t in atTop, ∀ i, reservoirRobustFloor n dmin/(8*((n:ℝ)+1)) < x t i := by
  let s := reservoirRobustFloor n dmin
  have hs : 0 < s := reservoirRobustFloor_pos n dmin hdmin
  let etaX := s/(8*((n:ℝ)+1))
  let delta := reservoirRobustRadius n dmin
  have hdelta : 0 ≤ delta := (reservoirRobustRadius_pos n dmin hdmin).le
  have hd0 : delta ≤ rateRadius := min_le_left _ _
  have hd1 : delta ≤ dmin/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hd2 : delta ≤ 1/(1000*(1+reservoirWeight dmin)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd3 : delta ≤ s/1000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hl := reservoir_rate_total_lower hn e d dmin delta r hr hdmin hd hdelta hd0 hd1 hd2 he he' Y x R h
  have hu := reservoir_rate_total_upper hn e d dmin delta r hr hdmin hd hdelta hd0 hd1 he he' Y x R h
  have hb := reservoir_rate_resident_box e d delta r hr hd0 he he' Y x R h
  have hRu := reservoir_rate_upper e d dmin delta r hr hdmin hd hd1 Y x R h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ s ≤ total (x t) ∧ total (x t) ≤ 25 ∧
      0 ≤ R t*(Y t).z ∧ R t*(Y t).z ≤ 24 := by
    filter_upwards [hl,hu,hb,hRu] with t hl hu hb hR
    have hz := hb.2.2.2.1
    exact ⟨hb.1,hl.le,hu.le,mul_nonneg (h.reservoir_positive t hb.1).le hz.1,
      by nlinarith [hz.2,mul_le_mul_of_nonneg_right hR.le hz.1]⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hi (i : Fin n) : ∀ᶠ t in atTop, etaX < x t i := by
    have heq : etaX = s*(1/4)/(2*((n:ℝ)+1)) := by dsimp [etaX]; field_simp; ring
    rw [heq]
    apply sharp_species_floor (fun t => total (x t)) (fun t => x t i)
      (fun t => ((growthTotal r.reactions (R t*(Y t).z) (x t)-lossTotal r.reactions (x t))*x t i-
        total (x t)*(x t i*(r.reactions.k i*(R t*(Y t).z)-r.reactions.mu i-r.reactions.rho i*x t i)))/(x t i)^2)
      T ((n:ℝ)+1) (1/4) s (by positivity) (by norm_num) hs
    · intro t ht
      exact h.consumer_positive t (hT t ht).1 i
    · intro t ht
      exact (hT t ht).2.1
    · intro t ht
      exact (reservoir_rate_total_deriv r Y x R h t (hT t ht).1).div
        (h.dx t (hT t ht).1 i) (ne_of_gt (h.consumer_positive t (hT t ht).1 i))
    · intro t ht
      obtain ⟨h0,hSl,hSu,hz,hz'⟩ := hT t ht
      have hx := fun j => (h.consumer_positive t h0 j).le
      have herror := consumer_error_24 r.reactions delta (R t*(Y t).z) hdelta hz hz' hr.reactions.k hr.reactions.mu
      have hA := weighted_growth_error (x t) (fun j => r.reactions.k j*(R t*(Y t).z)-r.reactions.mu j)
        (R t*(Y t).z-1/2) (25*delta) hx herror i
      have hH := loss_total_lower hn r.reactions (x t) delta hd0 hx hr.reactions.rho
      have hrho := (near_consumer_box hn e delta r.reactions hr.reactions hd0 i).2.2.2
      have hquarter : (1/4:ℝ)*(total (x t)/x t i) = (total (x t)/x t i)/4 := by ring
      rw [hquarter]
      apply sharp_perturbed_ratio_drift _ _ _ _ _ _ ((n:ℝ)+1) (25*delta) s
        (h.consumer_positive t h0 i) hs hSl hrho
      · linarith only [hd3,hs]
      · exact hA
      · nlinarith only [hH,sq_nonneg (total (x t))]
  exact Filter.eventually_all.2 hi

end MultiConsumerPermanence

