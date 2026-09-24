import Mathlib.Tactic

namespace MemoryPrediction
noncomputable section
open Finset

/-- Terminal masses proposed by the dormant and Yule source. Identification
with the chronological process is a separate theorem, not assumed here. -/
def slowMass (n : ℕ) : ℝ := if n = 1 then 1 else 0
def fastMass (n : ℕ) : ℝ := if n = 0 then 0 else (1/2 : ℝ)^n
def mixtureMass (n : ℕ) : ℝ := (slowMass n + fastMass n)/2
def independentMass (n m : ℕ) : ℝ := mixtureMass n * mixtureMass m
def sharedMass (n m : ℕ) : ℝ := (slowMass n * slowMass m + fastMass n * fastMass m)/2
def pairCDF (w : ℕ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ range (k+1), ∑ m ∈ range (k+1), if n+m ≤ k then w n m else 0

theorem independentMass_nonneg (n m : ℕ) : 0 ≤ independentMass n m := by
  unfold independentMass mixtureMass slowMass fastMass
  positivity

theorem sharedMass_nonneg (n m : ℕ) : 0 ≤ sharedMass n m := by
  unfold sharedMass slowMass fastMass
  positivity

theorem low_count_separation :
    pairCDF independentMass 2 = 9/16 ∧ pairCDF sharedMass 2 = 5/8 := by
  norm_num [pairCDF, independentMass, sharedMass, mixtureMass, slowMass, fastMass,
    sum_range_succ]

theorem exact_endpoint_witness :
    pairCDF independentMass 5 = 59/64 ∧ pairCDF independentMass 6 = 245/256 ∧
    pairCDF sharedMass 6 = 121/128 ∧ pairCDF sharedMass 7 = 31/32 := by
  norm_num [pairCDF, independentMass, sharedMass, mixtureMass, slowMass, fastMass,
    sum_range_succ]

theorem endpoint_three_blind : pairCDF independentMass 3 = pairCDF sharedMass 3 := by
  norm_num [pairCDF, independentMass, sharedMass, mixtureMass, slowMass, fastMass,
    sum_range_succ]

theorem adjacent_thresholds :
    pairCDF independentMass 5 < 19/20 ∧ 19/20 < pairCDF independentMass 6 ∧
    pairCDF sharedMass 6 < 19/20 ∧ 19/20 < pairCDF sharedMass 7 := by
  rcases exact_endpoint_witness with ⟨h1,h2,h3,h4⟩
  rw [h1,h2,h3,h4]
  norm_num

/-- Deterministic separation on the event where the empirical mean is accurate.
The probability of that event must be proved by a statistical theorem. -/
theorem confidence_intervals_disjoint (x ε : ℝ) (hε : ε < 1/32)
    (hI : |x-9/16| ≤ ε) : ¬ |x-5/8| ≤ ε := by
  intro hW
  rcases abs_le.mp hI with ⟨_,hi⟩
  rcases abs_le.mp hW with ⟨hw,_⟩
  linarith

end
end MemoryPrediction
