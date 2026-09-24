import proofs.SpecimenReliability.GateTradeoff

namespace SpecimenReliability
noncomputable section
open scoped BigOperators

/-- One reference campaign of `m` pairs is reused for `T` independent future
specimens drawn from the same recovery population.  A specimen reads all-negative
with probability `R`; the batch event is that at least one of the `T` specimens
does so. -/
def atLeastOneNegative (R : ℝ) (T : ℕ) : ℝ :=
  ∑ h : Fin T → Bool,
    if (∃ i, h i = true) then ∏ i, (if h i then R else 1-R) else 0

theorem atLeastOne_law (R : ℝ) (T : ℕ) :
    atLeastOneNegative R T = 1-(1-R)^T := by
  classical
  have key : ∀ h : Fin T → Bool,
      (if (∃ i, h i = true) then ∏ i, (if h i then R else 1-R) else 0)
        = (∏ i, (if h i then R else 1-R))
          - (if h = (fun _ => false) then (1-R)^T else 0) := by
    intro h
    by_cases hh : h = fun _ => false
    · subst hh; simp
    · have hex : ∃ i, h i = true := by
        by_contra hc
        refine hh (funext fun i => ?_)
        cases hi : h i with
        | false => rfl
        | true => exact absurd ⟨i, hi⟩ hc
      simp [hex, hh]
  have hfull : (∑ h : Fin T → Bool, ∏ i, (if h i then R else 1-R)) = 1 := by
    rw [← Fintype.sum_pow (fun b : Bool => if b then R else 1-R) T]
    have : (∑ b : Bool, if b then R else 1-R) = 1 := by
      simp
    rw [this, one_pow]
  unfold atLeastOneNegative
  simp only [key]
  rw [Finset.sum_sub_distrib, hfull, Finset.sum_ite_eq' Finset.univ
    (fun _ : Fin T => false) (fun _ => (1-R)^T)]
  simp

/-- Familywise false-certificate probability: the gate passes on the shared
reference campaign and at least one of the `T` future specimens reads
all-negative. -/
def batchRisk {S : Type*} [Fintype S] (μ x y : S → ℝ) (a b : ℝ) (n m T : ℕ) : ℝ :=
  (mean μ x + mean μ y - mean μ (fun s => x s*y s))^m *
    atLeastOneNegative (sourceRisk μ x y a b n) T

theorem batch_identity {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (a b : ℝ) (n m T : ℕ) :
    batchRisk μ x y a b n m T =
      (mean μ x+mean μ y-mean μ (fun s => x s*y s))^m *
        (1-(1-sourceRisk μ x y a b n)^T) := by
  unfold batchRisk
  rw [atLeastOne_law]

theorem batch_witness (a : ℝ) (k T m : ℕ) :
    batchRisk (corners (1/2) (1/2) 0) cornerX cornerY a a k m T
      = 1-(1-(1-a)^k)^T := by
  have hm := corners_moments (1/2 : ℝ) (1/2) 0
  have hsrc : sourceRisk (corners (1/2:ℝ) (1/2) 0) cornerX cornerY a a k
      = (1-a)^k := by
    rw [envelope_attained]
    unfold envelope
    ring
  unfold batchRisk
  simp only [mean, hm.1, hm.2.1, hm.2.2, hsrc, atLeastOne_law]
  norm_num

/-- Impossibility: with `K = 6` targets, per-preparation recovery `a = 9/20`
and only `T = 2` future specimens, the familywise level `1/20` is unreachable
no matter how many reference pairs are collected — the gate factor is at most
one and the batch floor already exceeds the level. -/
theorem batch_floor_exceeds : (1:ℝ)-(1-(1-(9/20:ℝ))^6)^2 > 1/20 := by norm_num

theorem batch_witness_valid :
    (∀ i, 0 ≤ corners (1/2:ℝ) (1/2) 0 i) ∧
      ∑ i, corners (1/2:ℝ) (1/2) 0 i = 1 :=
  ⟨corners_nonneg _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
   corners_normalized _ _ _⟩

end
end SpecimenReliability
