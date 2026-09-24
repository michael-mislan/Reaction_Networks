import proofs.MultiConsumerPermanence.TotalPersistence
import proofs.MultiConsumerPermanence.CompositionRecovery
import proofs.MultiConsumerPermanence.ResidentFloors

namespace MultiConsumerPermanence
open CoreCouplingCAC Filter Topology

/-- Source-instantiated reference species recovery. Global existence is a
separate obligation; this theorem is not the public Root A endpoint. -/
theorem reference_trajectory_permanence {n : ℕ} (hn : 0 < n) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ e : ℝ, 0 ≤ e → e ≤ 1/50000 →
      ∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ), IsMultiTrajectory n e Y x →
      ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
        eta ≤ (Y t).H ∧ ∀ i, eta ≤ x t i := by
  let s := totalFloor n
  have hs : 0 < s := totalFloor_pos n
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let etaX : ℝ := s^2/(2*(n:ℝ)*12)
  have heX : 0 < etaX := by dsimp [etaX]; positivity
  refine ⟨min (1/220) etaX, lt_min (by norm_num) heX, ?_⟩
  intro e he he' Y x h
  have hl := total_eventually_lower hn e he he' Y x h
  have hu := total_eventually_upper hn e he he' Y x h
  have hready : ∀ᶠ t in atTop, 0 ≤ t ∧ s ≤ total (x t) ∧ total (x t) ≤ 12 := by
    filter_upwards [eventually_ge_atTop (0:ℝ),hl,hu] with t h0 hl hu
    exact ⟨h0,hl.le,hu.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hready
  have hi (i : Fin n) : ∀ᶠ t in atTop, etaX < x t i := by
    exact individual_floor_from_total (fun t => total (x t)) (fun t => squares (x t))
      (fun t => x t i) (fun t => (Y t).z-1/2) T n s 12 hnR hs (by norm_num)
      (fun t ht => h.consumer_positive t (hT t ht).1 i)
      (fun t ht => (hT t ht).2)
      (fun t ht => (squares_bounds (x t)
        (fun j => (h.consumer_positive t (hT t ht).1 j).le)).2)
      (fun t ht => total_hasDerivAt e Y x h t (hT t ht).1)
      (fun t ht => h.dx t (hT t ht).1 i)
  have hall : ∀ᶠ t in atTop, ∀ i, etaX < x t i := Filter.eventually_all.2 hi
  have hresident := loaded_eventually_resident_floors e he he' Y _ h.toIsLoadedResidentTrajectory hu
  filter_upwards [hresident,hall] with t hr hx
  have hm : min (1/220:ℝ) etaX ≤ 1/220 := min_le_left _ _
  refine ⟨by linarith [hr.1],by linarith [hr.2.1],by linarith [hr.2.2.1],
    by linarith [hr.2.2.2],fun i => (min_le_right _ _).trans (hx i).le⟩

end MultiConsumerPermanence
