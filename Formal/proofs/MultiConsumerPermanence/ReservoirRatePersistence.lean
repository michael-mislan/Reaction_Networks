import proofs.MultiConsumerPermanence.ReservoirRateBounds

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology Set

noncomputable def reservoirRobustFloor (n : ℕ) (dmin : ℝ) : ℝ :=
  (1/16:ℝ)/(2*(((n:ℝ)+120000002+6*reservoirWeight dmin)*
    Real.exp (150000*(1000000+reservoirWeight dmin/300000)))) *
    Real.exp (150000*(-1000000))

theorem reservoirRobustFloor_pos (n : ℕ) (dmin : ℝ) (hdmin : 0 < dmin) :
    0 < reservoirRobustFloor n dmin := by
  dsimp [reservoirRobustFloor,reservoirWeight]
  positivity

noncomputable def reservoirRobustRadius (n : ℕ) (dmin : ℝ) : ℝ :=
  min rateRadius (min (dmin/4) (min (1/(1000*(1+reservoirWeight dmin)))
    (reservoirRobustFloor n dmin/1000)))

theorem reservoirRobustRadius_pos (n : ℕ) (dmin : ℝ) (hdmin : 0 < dmin) :
    0 < reservoirRobustRadius n dmin := by
  have hs := reservoirRobustFloor_pos n dmin hdmin
  dsimp [reservoirRobustRadius,reservoirWeight,rateRadius]
  positivity

theorem reservoir_rate_total_lower {n : ℕ} (hn : 0 < n) (e d dmin delta : ℝ) (r : ReservoirRates n)
    (hr : ReservoirNear e d delta r) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ rateRadius) (hsmall : delta ≤ dmin/4)
    (hsmall' : delta ≤ 1/(1000*(1+reservoirWeight dmin)))
    (he : 1/200000 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) :
    ∀ᶠ t in atTop, reservoirRobustFloor n dmin < total (x t) := by
  have he0 : 0 ≤ e := by linarith
  obtain ⟨p⟩ := potentialPrimitives_nonempty e he0 he'
  let center := responsePotential e p 2 0 0 (2-responseTotal e 2)
  have hb : 0 ≤ reservoirWeight dmin := by dsimp [reservoirWeight]; positivity
  have habs := reservoir_rate_resident_box e d delta r hr hdelta' he he' Y x R h
  have hRu := reservoir_rate_upper e d dmin delta r hr hdmin hd hsmall Y x R h
  have hbox : ∀ᶠ t in atTop, 0 ≤ t ∧
      (Y t).A ∈ Icc (0:ℝ) 34 ∧ (Y t).B ∈ Icc (2:ℝ) 34 ∧
      (Y t).z ∈ Icc (0:ℝ) 12 ∧ (Y t).H ∈ Icc (0:ℝ) (1536/7) ∧
      R t ∈ Icc (0:ℝ) 2 := by
    filter_upwards [habs,hRu] with t ht hR
    exact ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2,
      (h.reservoir_positive t ht.1).le,hR.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hbox
  apply bounded_corrector_eventual_floor (fun t => total (x t))
    (fun t => growthTotal r.reactions (R t*(Y t).z) (x t)-lossTotal r.reactions (x t))
    (fun t => trajectoryPotential e p Y t-center+
      (reservoirWeight dmin/150000)*reservoirPotential (R t))
    (fun t => ratePotentialRate e (baseRates r.reactions) (Y t).A (Y t).B (Y t).z (Y t).H
      (R t*copyingLoad r.reactions (x t))+(reservoirWeight dmin/150000)*
      ((R t-1)*(r.feed-r.wash*R t-R t*(Y t).z*copyingLoad r.reactions (x t))))
    T 150000 (1/16) ((n:ℝ)+120000002+6*reservoirWeight dmin)
    (-1000000) (1000000+reservoirWeight dmin/300000)
    (by norm_num) (by norm_num) (by positivity)
  · intro t ht
    exact reservoir_rate_total_positive hn r Y x R h t (hT t ht).1
  · intro t ht
    obtain ⟨_,hA,hB,hz,hH,hR⟩ := hT t ht
    have hv := abs_le.1 (uniform_potential_center_bound e p he0 he' _ _ _ _
      hA.1 hA.2 hB.1 hB.2 hz.1 hz.2 hH.1 hH.2)
    have hp := reservoir_potential_bounds (R t) hR.1 hR.2
    have hp0 := mul_nonneg hb hp.1
    have hp1 := mul_le_mul_of_nonneg_left hp.2 hb
    constructor <;> dsimp [trajectoryPotential,center] at * <;> linarith only [hv.1,hv.2,hp0,hp1]
  · intro t ht
    exact reservoir_rate_total_deriv r Y x R h t (hT t ht).1
  · intro t ht
    obtain ⟨h0,_,hB,hz,hH,_⟩ := hT t ht
    exact ((rate_loaded_potential_hasDerivAt e p he0 he' _ Y _ h.toIsRateLoadedTrajectory
      t h0 hB hz hH).sub_const center).add
      ((reservoir_potential_hasDerivAt R t _ (h.dR t h0)).const_mul (reservoirWeight dmin/150000))
  · intro t ht
    obtain ⟨h0,hA,hB,hz,hH,hR⟩ := hT t ht
    apply reservoir_rate_corrected_growth e d dmin delta r hr hdmin hd hdelta hdelta' hsmall'
      _ _ _ _ _ _ he0 he' hA.1 hA.2 hB.1 hB.2 hz.1 hz.2 hH.1 hH.2 hR.1 hR.2
      (fun i => (h.consumer_positive t h0 i).le)
    apply copying_load_nonneg _ _ _ (fun i => (h.consumer_positive t h0 i).le)
    intro i
    have hh := (near_consumer_box hn e delta r.reactions hr.reactions hdelta' i).1.1
    linarith

end MultiConsumerPermanence
