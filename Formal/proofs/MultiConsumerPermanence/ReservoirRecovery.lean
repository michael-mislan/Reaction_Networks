import proofs.MultiConsumerPermanence.ReservoirPersistence
import proofs.MultiConsumerPermanence.ReservoirResidentFloors
import proofs.MultiConsumerPermanence.CompositionRecovery

namespace MultiConsumerPermanence
open CoreCouplingCAC Filter Topology

theorem reservoir_trajectory_permanence {n : ℕ} (hn : 0 < n)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hinterval : dmin ≤ dmax) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ e d : ℝ, 0 ≤ e → e ≤ 1/50000 →
      dmin ≤ d → d ≤ dmax →
      ∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ),
      IsReservoirTrajectory n e d d Y x R →
      ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
        eta ≤ (Y t).H ∧ eta ≤ R t ∧ ∀ i, eta ≤ x t i := by
  let s := reservoirTotalFloor n dmin
  have hs : 0 < s := reservoirTotalFloor_pos n dmin hdmin
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let etaX : ℝ := s^2/(2*(n:ℝ)*24)
  let etaR : ℝ := dmin/(2*(dmax+288))
  have heX : 0 < etaX := by dsimp [etaX]; positivity
  have heR : 0 < etaR := by dsimp [etaR]; apply div_pos hdmin; linarith
  refine ⟨min (1/300) (min etaR etaX),lt_min (by norm_num) (lt_min heR heX),?_⟩
  intro e d he he' hd hd' Y x R h
  have hd0 := lt_of_lt_of_le hdmin hd
  have hl := reservoir_total_lower hn e d dmin hdmin hd he he' Y x R h
  have hu := reservoir_total_upper e d hd0 he he' Y x R h
  have hR := reservoir_eventually_upper e d hd0 Y x R h
  have hRl := reservoir_eventually_lower e d dmin dmax hdmin hd hd' he he' Y x R h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ s ≤ total (x t) ∧ total (x t) ≤ 24 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hl,hu] with t h0 hl hu
    exact ⟨h0,hl.le,hu.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hi (i : Fin n) : ∀ᶠ t in atTop, etaX < x t i := by
    exact individual_floor_from_total (fun t => total (x t)) (fun t => squares (x t))
      (fun t => x t i) (fun t => R t*(Y t).z-1/2) T n s 24 hnR hs (by norm_num)
      (fun t ht => h.consumer_positive t (hT t ht).1 i)
      (fun t ht => (hT t ht).2)
      (fun t ht => (squares_bounds (x t)
        (fun j => (h.consumer_positive t (hT t ht).1 j).le)).2)
      (fun t ht => reservoir_total_deriv e d d Y x R h t (hT t ht).1)
      (fun t ht => h.dx t (hT t ht).1 i)
  have hall : ∀ᶠ t in atTop, ∀ i, etaX < x t i := Filter.eventually_all.2 hi
  have hload : ∀ᶠ t in atTop, R t*total (x t) < 48 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hu,hR] with t ht hs hr
    have hp := mul_lt_mul_of_pos_right hr (reservoir_total_positive hn e d d Y x R h t ht)
    linarith only [hp,hs]
  have hresident := reservoir_loaded_resident_floors e he he' Y _ h.toIsLoadedResidentTrajectory hload
  filter_upwards [hresident,hRl,hall] with t hr hR hx
  have hm : min (1/300:ℝ) (min etaR etaX) ≤ 1/300 := min_le_left _ _
  have hmR : min (1/300:ℝ) (min etaR etaX) ≤ etaR := (min_le_right _ _).trans (min_le_left _ _)
  have hmX : min (1/300:ℝ) (min etaR etaX) ≤ etaX := (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨by linarith [hr.1],by linarith [hr.2.1],by linarith [hr.2.2.1],
    by linarith [hr.2.2.2],hmR.trans hR.le,fun i => hmX.trans (hx i).le⟩

end MultiConsumerPermanence
