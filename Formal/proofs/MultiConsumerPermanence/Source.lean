import proofs.MultiConsumerPermanence.DonorLoad
import proofs.MultiConsumerPermanence.AggregateIdentities

namespace MultiConsumerPermanence
open CoreCouplingCAC
open scoped BigOperators

/-- Reference multi-consumer equations. Existence is proved separately, never
inferred from this predicate. Each consumer has its own quadratic loss. -/
structure IsMultiTrajectory (n : ℕ) (e : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) : Prop extends
    IsLoadedResidentTrajectory e Y (fun t => total (x t)) where
  consumer_positive : ∀ t, 0 ≤ t → ∀ i, 0 < x t i
  dx : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => x s i)
    (x t i*((Y t).z-1/2-(n:ℝ)*x t i)) t

theorem total_hasDerivAt {n : ℕ} (e : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (h : IsMultiTrajectory n e Y x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => total (x s))
      (((Y t).z-1/2)*total (x t)-(n:ℝ)*squares (x t)) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h.dx t ht i)
  simpa only [aggregate_identity, total] using hh

theorem total_positive {n : ℕ} (hn : 0 < n) (e : ℝ) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (h : IsMultiTrajectory n e Y x) (t : ℝ) (ht : 0 ≤ t) :
    0 < total (x t) := by
  exact Finset.sum_pos' (fun i _ => (h.consumer_positive t ht i).le)
    ⟨⟨0, hn⟩, Finset.mem_univ _, h.consumer_positive t ht ⟨0, hn⟩⟩

end MultiConsumerPermanence
