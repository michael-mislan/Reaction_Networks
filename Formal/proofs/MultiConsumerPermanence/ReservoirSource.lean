import proofs.MultiConsumerPermanence.Source
import proofs.MultiConsumerPermanence.ReservoirDeficit

namespace MultiConsumerPermanence
open CoreCouplingCAC
open scoped BigOperators

/-- The reservoir is consumed in the copying channel, and its feed and washout
are separate coordinates. Reference replenishment uses feed = washout = d. -/
structure IsReservoirTrajectory (n : ℕ) (e feed washout : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ) : Prop extends
    IsLoadedResidentTrajectory e Y (fun t => R t*total (x t)) where
  consumer_positive : ∀ t, 0 ≤ t → ∀ i, 0 < x t i
  reservoir_positive : ∀ t, 0 ≤ t → 0 < R t
  dx : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => x s i)
    (x t i*(R t*(Y t).z-1/2-(n:ℝ)*x t i)) t
  dR : ∀ t, 0 ≤ t → HasDerivAt R
    (feed-washout*R t-R t*(Y t).z*total (x t)) t

theorem reservoir_total_deriv {n : ℕ} (e feed washout : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ) (h : IsReservoirTrajectory n e feed washout Y x R)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => total (x s))
      ((R t*(Y t).z-1/2)*total (x t)-(n:ℝ)*squares (x t)) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h.dx t ht i)
  simpa only [aggregate_identity,total] using hh

theorem reservoir_total_positive {n : ℕ} (hn : 0 < n) (e feed washout : ℝ)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e feed washout Y x R) (t : ℝ) (ht : 0 ≤ t) :
    0 < total (x t) := by
  exact Finset.sum_pos' (fun i _ => (h.consumer_positive t ht i).le)
    ⟨⟨0,hn⟩,Finset.mem_univ _,h.consumer_positive t ht ⟨0,hn⟩⟩

theorem reservoir_supply_balance {n : ℕ} (e feed washout : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ) (h : IsReservoirTrajectory n e feed washout Y x R)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => R s+total (x s))
      (feed-washout*R t-(1/2)*total (x t)-(n:ℝ)*squares (x t)) t := by
  convert (h.dR t ht).add (reservoir_total_deriv e feed washout Y x R h t ht) using 1
  ring

end MultiConsumerPermanence
