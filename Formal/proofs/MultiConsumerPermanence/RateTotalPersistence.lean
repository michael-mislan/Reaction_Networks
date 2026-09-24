import proofs.MultiConsumerPermanence.RateLoadedPotential

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology Set

noncomputable def robustTotalFloor (n : ℕ) : ℝ :=
  (1/8:ℝ)/(2*(((n:ℝ)+60000001)*Real.exp (150000*1000000))) *
    Real.exp (150000*(-1000000))

theorem robustTotalFloor_pos (n : ℕ) : 0 < robustTotalFloor n := by
  unfold robustTotalFloor
  positivity

noncomputable def robustRadius (n : ℕ) : ℝ := min rateRadius (robustTotalFloor n/1000)

theorem robustRadius_pos (n : ℕ) : 0 < robustRadius n :=
  lt_min (by norm_num [rateRadius]) (div_pos (robustTotalFloor_pos n) (by norm_num))

theorem perturbed_total_positive {n : ℕ} (hn : 0 < n) (r : Rates n) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (h : IsPerturbedTrajectory r Y x) (t : ℝ) (ht : 0 ≤ t) :
    0 < total (x t) := by
  exact Finset.sum_pos' (fun i _ => (h.consumer_positive t ht i).le)
    ⟨⟨0, hn⟩, Finset.mem_univ _, h.consumer_positive t ht ⟨0, hn⟩⟩

theorem perturbed_resident_box {n : ℕ} (e delta : ℝ) (r : Rates n)
    (hr : Near e delta r) (hd : delta ≤ rateRadius)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (h : IsPerturbedTrajectory r Y x) :
    ∀ᶠ t in atTop, 0 ≤ t ∧
      (Y t).A ∈ Icc (0:ℝ) 34 ∧ (Y t).B ∈ Icc (2:ℝ) 34 ∧
      (Y t).z ∈ Icc (0:ℝ) 12 ∧ (Y t).H ∈ Icc (0:ℝ) (1536/7) := by
  have habs := rate_loaded_eventually_resident_absorbing (baseRates r)
    (RateNeighborhood.box e _ he he' (near_base e delta r hr hd))
    Y _ h.toIsRateLoadedTrajectory
  filter_upwards [habs,eventually_ge_atTop (0:ℝ)] with t ht h0
  have hp := h.positive t h0
  exact ⟨h0,⟨hp.1.le,by linarith [ht.1,hp.2.1]⟩,
    ⟨ht.2.2.2.le,by linarith [ht.1,hp.1]⟩,⟨hp.2.2.1.le,ht.2.2.1.le⟩,
    ⟨hp.2.2.2.le,by linarith [ht.2.1,hp.2.2.1]⟩⟩

theorem perturbed_total_upper {n : ℕ} (hn : 0 < n) (e delta : ℝ) (r : Rates n)
    (hr : Near e delta r) (hd : 0 ≤ delta) (hd' : delta ≤ rateRadius)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (h : IsPerturbedTrajectory r Y x) :
    ∀ᶠ t in atTop, total (x t) < 119/10 := by
  obtain ⟨T,hT⟩ := eventually_atTop.1 (perturbed_resident_box e delta r hr hd' he he' Y x h)
  apply eventual_upper_of_linear_drift (fun t => total (x t))
    (fun t => growthTotal r (Y t).z (x t)-lossTotal r (x t))
    T 139 12 (119/10) (by norm_num) (by norm_num)
  · intro t ht
    exact perturbed_total_deriv r Y x h t (hT t ht).1
  · intro t ht
    obtain ⟨h0,_,_,hz,_⟩ := hT t ht
    exact perturbed_aggregate_upper_drift hn e delta r hr hd hd' _ _ hz.1 hz.2
      (fun i => (h.consumer_positive t h0 i).le)

theorem perturbed_load_upper {n : ℕ} (hn : 0 < n) (e delta : ℝ) (r : Rates n)
    (hr : Near e delta r) (hd : 0 ≤ delta) (hd' : delta ≤ rateRadius)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (h : IsPerturbedTrajectory r Y x) :
    ∀ᶠ t in atTop, copyingLoad r (x t) < 12 := by
  have hu := perturbed_total_upper hn e delta r hr hd hd' he he' Y x h
  filter_upwards [hu,eventually_ge_atTop (0:ℝ)] with t ht h0
  have hl := copying_load_upper r (x t) delta (fun i => (h.consumer_positive t h0 i).le) hr.k
  have hm := mul_lt_mul_of_pos_left ht (show 0 < 1+delta by linarith)
  have hc : (1+delta)*(119/10:ℝ) < 12 := by
    dsimp [rateRadius] at hd'
    linarith only [hd']
  exact hl.trans_lt (hm.trans hc)

theorem perturbed_total_lower {n : ℕ} (hn : 0 < n) (e delta : ℝ) (r : Rates n)
    (hr : Near e delta r) (hd : 0 ≤ delta) (hd' : delta ≤ rateRadius)
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (h : IsPerturbedTrajectory r Y x) :
    ∀ᶠ t in atTop, robustTotalFloor n < total (x t) := by
  have he0 : 0 ≤ e := by linarith
  obtain ⟨p⟩ := potentialPrimitives_nonempty e he0 he'
  let center := responsePotential e p 2 0 0 (2-responseTotal e 2)
  obtain ⟨T,hT⟩ := eventually_atTop.1 (perturbed_resident_box e delta r hr hd' he he' Y x h)
  apply bounded_corrector_eventual_floor (fun t => total (x t))
    (fun t => growthTotal r (Y t).z (x t)-lossTotal r (x t))
    (fun t => trajectoryPotential e p Y t-center)
    (fun t => ratePotentialRate e (baseRates r) (Y t).A (Y t).B (Y t).z (Y t).H (copyingLoad r (x t)))
    T 150000 (1/8) ((n:ℝ)+60000001) (-1000000) 1000000
    (by norm_num) (by norm_num) (by positivity)
  · intro t ht
    exact perturbed_total_positive hn r Y x h t (hT t ht).1
  · intro t ht
    obtain ⟨_,hA,hB,hz,hH⟩ := hT t ht
    exact abs_le.1 (uniform_potential_center_bound e p he0 he' _ _ _ _
      hA.1 hA.2 hB.1 hB.2 hz.1 hz.2 hH.1 hH.2)
  · intro t ht
    exact perturbed_total_deriv r Y x h t (hT t ht).1
  · intro t ht
    obtain ⟨h0,_,hB,hz,hH⟩ := hT t ht
    exact (rate_loaded_potential_hasDerivAt e p he0 he' (baseRates r) Y _
      h.toIsRateLoadedTrajectory t h0 hB hz hH).sub_const center
  · intro t ht
    obtain ⟨h0,hA,hB,hz,hH⟩ := hT t ht
    exact perturbed_corrected_growth e delta r hr hd hd' _ _ _ _ _ he0 he'
      hA.1 hA.2 hB.1 hB.2 hz.1 hz.2 hH.1 hH.2
      (fun i => (h.consumer_positive t h0 i).le) (h.load_nonnegative t h0)

end MultiConsumerPermanence
