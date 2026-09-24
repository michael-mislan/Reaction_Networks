import proofs.MultiConsumerPermanence.ReservoirRateAlgebra
import proofs.MultiConsumerPermanence.RateFlow

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology Set

theorem reservoir_rate_supply_box {n : ℕ} (e d dmin delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hdelta : delta ≤ dmin/4) :
    0 < r.wash ∧ dmin/2 ≤ r.feed ∧ r.feed/r.wash < 2 := by
  have hf := abs_le.mp hr.feed
  have hw := abs_le.mp hr.wash
  have hw0 : 0 < r.wash := by linarith only [hw.1,hd,hdmin,hdelta]
  refine ⟨hw0,by linarith only [hf.1,hd,hdelta,hdmin],?_⟩
  apply (div_lt_iff₀ hw0).2
  linarith only [hf.2,hw.1,hd,hdmin,hdelta]

theorem reservoir_rate_resident_box {n : ℕ} (e d delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hd : delta ≤ rateRadius)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) :
    ∀ᶠ t in atTop, 0 ≤ t ∧
      (Y t).A ∈ Icc (0:ℝ) 34 ∧ (Y t).B ∈ Icc (2:ℝ) 34 ∧
      (Y t).z ∈ Icc (0:ℝ) 12 ∧ (Y t).H ∈ Icc (0:ℝ) (1536/7) := by
  have habs := rate_loaded_eventually_resident_absorbing (baseRates r.reactions)
    (RateNeighborhood.box e _ he he' (near_base e delta r.reactions hr.reactions hd))
    Y _ h.toIsRateLoadedTrajectory
  filter_upwards [habs,eventually_ge_atTop (0:ℝ)] with t ht h0
  have hp := h.positive t h0
  exact ⟨h0,⟨hp.1.le,by linarith [ht.1,hp.2.1]⟩,
    ⟨ht.2.2.2.le,by linarith [ht.1,hp.1]⟩,⟨hp.2.2.1.le,ht.2.2.1.le⟩,
    ⟨hp.2.2.2.le,by linarith [ht.2.1,hp.2.2.1]⟩⟩

theorem reservoir_rate_upper {n : ℕ} (e d dmin delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hdelta : delta ≤ dmin/4) (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) : ∀ᶠ t in atTop, R t < 2 := by
  have hs := reservoir_rate_supply_box e d dmin delta r hr hdmin hd hdelta
  apply eventual_upper_of_linear_drift R
    (fun t => r.feed-r.wash*R t-R t*(Y t).z*copyingLoad r.reactions (x t))
    0 r.feed r.wash 2 hs.1 hs.2.2 h.dR
  intro t ht
  have hh := mul_nonneg (h.positive t ht).2.2.1.le (h.load_nonnegative t ht)
  nlinarith only [hh]

theorem reservoir_rate_total_upper {n : ℕ} (hn : 0 < n) (e d dmin delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ rateRadius) (hsmall : delta ≤ dmin/4)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) : ∀ᶠ t in atTop, total (x t) < 25 := by
  have hb := reservoir_rate_resident_box e d delta r hr hdelta' he he' Y x R h
  have hR := reservoir_rate_upper e d dmin delta r hr hdmin hd hsmall Y x R h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ (Y t).z ≤ 12 ∧ R t ≤ 2 := by
    filter_upwards [hb,hR] with t hb hR
    exact ⟨hb.1,hb.2.2.2.1.2,hR.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  apply eventual_upper_of_linear_drift (fun t => total (x t))
    (fun t => growthTotal r.reactions (R t*(Y t).z) (x t)-lossTotal r.reactions (x t))
    T 601 25 25 (by norm_num) (by norm_num)
  · intro t ht
    exact reservoir_rate_total_deriv r Y x R h t (hT t ht).1
  · intro t ht
    obtain ⟨h0,hz,hR⟩ := hT t ht
    have hx := fun i => (h.consumer_positive t h0 i).le
    have hS := total_nonneg (x t) hx
    have hRz : R t*(Y t).z ≤ 24 := by
      nlinarith [mul_le_mul_of_nonneg_right hR (h.positive t h0).2.2.1.le]
    have hg := (growth_total_bounds_24 r.reactions (x t) (R t*(Y t).z) delta hdelta hx
      (mul_nonneg (h.reservoir_positive t h0).le (h.positive t h0).2.2.1.le)
      hRz hr.reactions.k hr.reactions.mu).2
    have hl := loss_total_lower hn r.reactions (x t) delta hdelta' hx hr.reactions.rho
    have hg0 : R t*(Y t).z-1/2+25*delta ≤ 24 := by
      dsimp [rateRadius] at hdelta'
      linarith only [hRz,hdelta']
    have hg' := hg.trans (mul_le_mul_of_nonneg_right hg0 hS)
    nlinarith only [hg',hl,sq_nonneg (total (x t)-24500/999)]

theorem reservoir_rate_load_upper {n : ℕ} (hn : 0 < n) (e d dmin delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ rateRadius) (hsmall : delta ≤ dmin/4)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) :
    ∀ᶠ t in atTop, R t*copyingLoad r.reactions (x t) < 51 := by
  have hS := reservoir_rate_total_upper hn e d dmin delta r hr hdmin hd hdelta hdelta' hsmall he he' Y x R h
  have hR := reservoir_rate_upper e d dmin delta r hr hdmin hd hsmall Y x R h
  filter_upwards [eventually_ge_atTop (0:ℝ),hS,hR] with t h0 hS hR
  have hk := copying_load_upper r.reactions (x t) delta
    (fun i => (h.consumer_positive t h0 i).le) hr.reactions.k
  have hk' : copyingLoad r.reactions (x t) < (1+delta)*25 :=
    hk.trans_lt (mul_lt_mul_of_pos_left hS (by linarith))
  have hp := mul_lt_mul_of_pos_left hk' (h.reservoir_positive t h0)
  have hp' := mul_lt_mul_of_pos_right hR (show 0 < (1+delta)*25 by positivity)
  have hc : 2*((1+delta)*25) < 51 := by dsimp [rateRadius] at hdelta'; linarith only [hdelta']
  exact hp.trans (hp'.trans hc)

end MultiConsumerPermanence
