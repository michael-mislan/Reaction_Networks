import proofs.MultiConsumerPermanence.ReservoirRatePersistence
import proofs.MultiConsumerPermanence.ReservoirRateResidentFloors
import proofs.MultiConsumerPermanence.RateRecovery

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology

theorem reservoir_rate_lower {n : ℕ} (hn : 0 < n) (e d dmin dmax delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hdmin : 0 < dmin) (hd : dmin ≤ d) (hd' : d ≤ dmax)
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ rateRadius) (hsmall : delta ≤ dmin/4)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) :
    ∀ᶠ t in atTop, dmin/(4*(dmax+302)) < R t := by
  have hc : 0 < dmax+302 := by linarith
  have hsupply := reservoir_rate_supply_box e d dmin delta r hr hdmin hd hsmall
  have hb := reservoir_rate_resident_box e d delta r hr hdelta' he he' Y x R h
  have hs := reservoir_rate_total_upper hn e d dmin delta r hr hdmin hd hdelta hdelta' hsmall he he' Y x R h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ (Y t).z ≤ 12 ∧ total (x t) ≤ 25 := by
    filter_upwards [hb,hs] with t hb hs
    exact ⟨hb.1,hb.2.2.2.1.2,hs.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hh : ∀ᶠ t in atTop, -R t < -(dmin/(4*(dmax+302))) := by
    apply eventual_upper_of_linear_drift (fun t => -R t)
      (fun t => -(r.feed-r.wash*R t-R t*(Y t).z*copyingLoad r.reactions (x t)))
      T (-(dmin/2)) (dmax+302) (-(dmin/(4*(dmax+302)))) hc
    · field_simp
      nlinarith only [hdmin]
    · intro t ht
      exact (h.dR t (hT t ht).1).neg
    · intro t ht
      obtain ⟨h0,hz,hs⟩ := hT t ht
      have hR := (h.reservoir_positive t h0).le
      have hK := copying_load_upper r.reactions (x t) delta
        (fun i => (h.consumer_positive t h0 i).le) hr.reactions.k
      have hK' := hK.trans (mul_le_mul_of_nonneg_left hs (by linarith : 0 ≤ 1+delta))
      have hzK := mul_le_mul_of_nonneg_left hK' (h.positive t h0).2.2.1.le
      have hzK' := mul_le_mul_of_nonneg_right hz (show 0 ≤ (1+delta)*25 by positivity)
      have hzK301 : (Y t).z*copyingLoad r.reactions (x t) ≤ 301 := by
        dsimp [rateRadius] at hdelta'
        nlinarith only [hzK,hzK',hdelta']
      have hprod := mul_le_mul_of_nonneg_left hzK301 hR
      have hw : r.wash ≤ dmax+1 := by
        have hh := (abs_le.mp hr.wash).2
        dsimp [rateRadius] at hdelta'
        linarith only [hh,hd',hdelta']
      have hwR := mul_le_mul_of_nonneg_right hw hR
      nlinarith only [hprod,hwR,hsupply.2.1]
  filter_upwards [hh] with t ht
  linarith only [ht]

theorem reservoir_robust_trajectory_floor {n : ℕ} (hn : 0 < n)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hinterval : dmin ≤ dmax) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ e d : ℝ, 1/200000 ≤ e → e ≤ 1/50000 →
      dmin ≤ d → d ≤ dmax →
      ∀ r : ReservoirRates n, ReservoirNear e d (reservoirRobustRadius n dmin) r →
      ∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ), IsReservoirRateTrajectory r Y x R →
      ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
        eta ≤ (Y t).H ∧ eta ≤ R t ∧ ∀ i, eta ≤ x t i := by
  let s := reservoirRobustFloor n dmin
  have hs : 0 < s := reservoirRobustFloor_pos n dmin hdmin
  let etaX : ℝ := s*(s/4)/(2*(((n:ℝ)+1)*25))
  let etaR : ℝ := dmin/(4*(dmax+302))
  have hetaX : 0 < etaX := by dsimp [etaX]; positivity
  have hetaR : 0 < etaR := by dsimp [etaR]; apply div_pos hdmin; linarith
  refine ⟨min (1/500) (min etaR etaX),lt_min (by norm_num) (lt_min hetaR hetaX),?_⟩
  intro e d he he' hd hd' r hr Y x R h
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
    apply ratio_damping_species_floor (fun t => total (x t)) (fun t => x t i)
      (fun t => ((growthTotal r.reactions (R t*(Y t).z) (x t)-lossTotal r.reactions (x t))*x t i-
        total (x t)*(x t i*(r.reactions.k i*(R t*(Y t).z)-r.reactions.mu i-r.reactions.rho i*x t i)))/(x t i)^2)
      T s (((n:ℝ)+1)*25) (s/4) (by positivity) (by positivity)
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
      apply heterogeneous_ratio_drift _ _ _ _ _ _ ((n:ℝ)+1) (25*delta) s 25
        (h.consumer_positive t h0 i) hs hSl hSu (by positivity) hrho
      · linarith only [hd3,hs]
      · exact hA
      · nlinarith only [hH,sq_nonneg (total (x t))]
  have hall : ∀ᶠ t in atTop, ∀ i, etaX < x t i := Filter.eventually_all.2 hi
  have hresident := reservoir_rate_loaded_resident_floors (baseRates r.reactions)
    (RateNeighborhood.box e _ he he' (near_base e delta r.reactions hr.reactions hd0)) Y _ h.toIsRateLoadedTrajectory
    (reservoir_rate_load_upper hn e d dmin delta r hr hdmin hd hdelta hd0 hd1 he he' Y x R h)
  have hRl := reservoir_rate_lower hn e d dmin dmax delta r hr hdmin hd hd' hdelta hd0 hd1 he he' Y x R h
  filter_upwards [hresident,hRl,hall] with t ht hR hx
  have hm : min (1/500:ℝ) (min etaR etaX) ≤ 1/500 := min_le_left _ _
  have hmR : min (1/500:ℝ) (min etaR etaX) ≤ etaR := (min_le_right _ _).trans (min_le_left _ _)
  have hmX : min (1/500:ℝ) (min etaR etaX) ≤ etaX := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨by linarith [ht.1],by linarith [ht.2.1],by linarith [ht.2.2.1],
    by linarith [ht.2.2.2],hmR.trans hR.le,fun i => hmX.trans (hx i).le⟩

end MultiConsumerPermanence
