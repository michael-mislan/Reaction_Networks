import proofs.MultiConsumerPermanence.RateSource
import proofs.MultiConsumerPermanence.ReservoirSource

namespace MultiConsumerPermanence
open CoreCouplingCAC
open scoped BigOperators

/-- Exactly 15+3n independently varying directed reaction rates. -/
structure ReservoirRates (n : ℕ) where
  reactions : Rates n
  feed : ℝ
  wash : ℝ

structure ReservoirNear {n : ℕ} (e d delta : ℝ) (r : ReservoirRates n) : Prop where
  reactions : Near e delta r.reactions
  feed : |r.feed-d| ≤ delta
  wash : |r.wash-d| ≤ delta

structure IsReservoirRateTrajectory {n : ℕ} (r : ReservoirRates n) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ) : Prop extends
    IsRateLoadedTrajectory (baseRates r.reactions) Y (fun t => R t*copyingLoad r.reactions (x t)) where
  consumer_positive : ∀ t, 0 ≤ t → ∀ i, 0 < x t i
  reservoir_positive : ∀ t, 0 ≤ t → 0 < R t
  dx : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => x s i)
    (x t i*(r.reactions.k i*(R t*(Y t).z)-r.reactions.mu i-r.reactions.rho i*x t i)) t
  dR : ∀ t, 0 ≤ t → HasDerivAt R
    (r.feed-r.wash*R t-R t*(Y t).z*copyingLoad r.reactions (x t)) t

theorem reservoir_rate_total_deriv {n : ℕ} (r : ReservoirRates n) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ) (h : IsReservoirRateTrajectory r Y x R)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => total (x s))
      (growthTotal r.reactions (R t*(Y t).z) (x t)-lossTotal r.reactions (x t)) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h.dx t ht i)
  have hid : (∑ i, x t i*(r.reactions.k i*(R t*(Y t).z)-r.reactions.mu i-r.reactions.rho i*x t i)) =
      growthTotal r.reactions (R t*(Y t).z) (x t)-lossTotal r.reactions (x t) := by
    simp only [growthTotal,lossTotal,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [hid,total] using hh

theorem reservoir_rate_total_positive {n : ℕ} (hn : 0 < n) (r : ReservoirRates n)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirRateTrajectory r Y x R) (t : ℝ) (ht : 0 ≤ t) : 0 < total (x t) := by
  exact Finset.sum_pos' (fun i _ => (h.consumer_positive t ht i).le)
    ⟨⟨0,hn⟩,Finset.mem_univ _,h.consumer_positive t ht ⟨0,hn⟩⟩

end MultiConsumerPermanence
