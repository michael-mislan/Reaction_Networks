import proofs.MultiConsumerPermanence.LiteralSource
import proofs.MultiConsumerPermanence.RateDonorLoad
import proofs.RobustPermanence.RatePotential

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence
open scoped BigOperators

/-- Exactly 13+3n independently varying directed rates. -/
structure Rates (n : ℕ) where
  resident : Fin 13 → ℝ
  k : Fin n → ℝ
  mu : Fin n → ℝ
  rho : Fin n → ℝ

/-- The last three donor fields are fixed adapters, not additional parameters. -/
noncomputable def baseRates {n : ℕ} (r : Rates n) : AssemblyRates :=
  ⟨r.resident 0,r.resident 1,r.resident 2,r.resident 3,r.resident 4,r.resident 5,
    r.resident 6,r.resident 7,r.resident 8,r.resident 9,r.resident 10,r.resident 11,
    r.resident 12,1,1/2,1⟩

structure Near {n : ℕ} (e delta : ℝ) (r : Rates n) : Prop where
  resident : ∀ j, |r.resident j-residentRates e j| ≤ delta
  k : ∀ i, |r.k i-1| ≤ delta
  mu : ∀ i, |r.mu i-1/2| ≤ delta
  rho : ∀ i, |r.rho i-(n:ℝ)| ≤ delta

theorem near_base {n : ℕ} (e delta : ℝ) (r : Rates n)
    (h : Near e delta r) (hd : delta ≤ rateRadius) : RateNeighborhood e (baseRates r) := by
  constructor
  · simpa [baseRates,residentRates] using (h.resident 0).trans hd
  · simpa [baseRates,residentRates] using (h.resident 1).trans hd
  · simpa [baseRates,residentRates] using (h.resident 2).trans hd
  · simpa [baseRates,residentRates] using (h.resident 3).trans hd
  · simpa [baseRates,residentRates] using (h.resident 4).trans hd
  · simpa [baseRates,residentRates] using (h.resident 5).trans hd
  · simpa [baseRates,residentRates] using (h.resident 6).trans hd
  · simpa [baseRates,residentRates] using (h.resident 7).trans hd
  · simpa [baseRates,residentRates] using (h.resident 8).trans hd
  · simpa [baseRates,residentRates] using (h.resident 9).trans hd
  · simpa [baseRates,residentRates] using (h.resident 10).trans hd
  · simpa [baseRates,residentRates] using (h.resident 11).trans hd
  · simpa [baseRates,residentRates] using (h.resident 12).trans hd
  · norm_num [baseRates,rateRadius]
  · norm_num [baseRates,rateRadius]
  · norm_num [baseRates,rateRadius]

noncomputable def copyingLoad {n : ℕ} (r : Rates n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, r.k i*x i

noncomputable def lossTotal {n : ℕ} (r : Rates n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, r.rho i*(x i)^2

noncomputable def growthTotal {n : ℕ} (r : Rates n) (z : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i*(r.k i*z-r.mu i)

structure IsPerturbedTrajectory {n : ℕ} (r : Rates n) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) : Prop extends
    IsRateLoadedTrajectory (baseRates r) Y (fun t => copyingLoad r (x t)) where
  consumer_positive : ∀ t, 0 ≤ t → ∀ i, 0 < x t i
  dx : ∀ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => x s i)
    (x t i*(r.k i*(Y t).z-r.mu i-r.rho i*x t i)) t

theorem perturbed_total_deriv {n : ℕ} (r : Rates n) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (h : IsPerturbedTrajectory r Y x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => total (x s))
      (growthTotal r (Y t).z (x t)-lossTotal r (x t)) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h.dx t ht i)
  have hi : (∑ i, x t i*(r.k i*(Y t).z-r.mu i-r.rho i*x t i)) =
      growthTotal r (Y t).z (x t)-lossTotal r (x t) := by
    simp only [growthTotal,lossTotal,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [hi,total] using hh

end MultiConsumerPermanence
