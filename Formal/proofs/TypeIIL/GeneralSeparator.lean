import Mathlib
import proofs.TypeII3.Network.TwoRootKernel

namespace TypeIIL

open Finset

variable {Species Reaction : Type*}
variable [Fintype Species] [Fintype Reaction]

def separatorP (N : Species → Reaction → ℝ) (alpha : Reaction → ℝ)
    (u v : Species → ℝ) (j : Reaction) : ℝ :=
  ∑ i, u i * N i j + ∑ i, v i * N i j * alpha j

def separatorQ (N : Species → Reaction → ℝ) (beta : Reaction → ℝ)
    (u v : Species → ℝ) (j : Reaction) : ℝ :=
  -(∑ i, u i * N i j) - ∑ i, v i * N i j * beta j

def separatorE (rho u v : Species → ℝ) (i : Species) : ℝ :=
  -u i - v i * rho i

/-- A Gordan dual certificate for the stacked base/ratio balance matrix. -/
structure KernelSeparator
    (N : Species → Reaction → ℝ) (alpha beta : Reaction → ℝ)
    (rho : Species → ℝ) where
  u : Species → ℝ
  v : Species → ℝ
  p_nonneg : ∀ j, 0 ≤ separatorP N alpha u v j
  q_nonneg : ∀ j, 0 ≤ separatorQ N beta u v j
  e_nonneg : ∀ i, 0 ≤ separatorE rho u v i
  strict :
    (∃ j, 0 < separatorP N alpha u v j) ∨
    (∃ j, 0 < separatorQ N beta u v j) ∨
    (∃ i, 0 < separatorE rho u v i)
  annihilates : ∀ (p q : Reaction → ℝ) (e : Species → ℝ),
    TypeII3.BaseFluxBalance N p q e →
    TypeII3.RatioFluxBalance N alpha beta rho p q e →
    (∑ j, separatorP N alpha u v j * p j) +
      (∑ j, separatorQ N beta u v j * q j) +
      (∑ i, separatorE rho u v i * e i) = 0

theorem no_positive_kernel_of_separator
    (N : Species → Reaction → ℝ) (alpha beta : Reaction → ℝ)
    (rho : Species → ℝ) (p q : Reaction → ℝ) (e : Species → ℝ)
    (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 < q j) (he : ∀ i, 0 < e i)
    (hB : TypeII3.BaseFluxBalance N p q e)
    (hR : TypeII3.RatioFluxBalance N alpha beta rho p q e)
    (s : KernelSeparator N alpha beta rho) : False := by
  have hpSum : 0 ≤ ∑ j, separatorP N alpha s.u s.v j * p j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (s.p_nonneg j) (le_of_lt (hp j))
  have hqSum : 0 ≤ ∑ j, separatorQ N beta s.u s.v j * q j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (s.q_nonneg j) (le_of_lt (hq j))
  have heSum : 0 ≤ ∑ i, separatorE rho s.u s.v i * e i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (s.e_nonneg i) (le_of_lt (he i))
  have hpositive : 0 <
      (∑ j, separatorP N alpha s.u s.v j * p j) +
      (∑ j, separatorQ N beta s.u s.v j * q j) +
      (∑ i, separatorE rho s.u s.v i * e i) := by
    rcases s.strict with hpStrict | hqStrict | heStrict
    · rcases hpStrict with ⟨j, hj⟩
      have hsp : 0 < ∑ k, separatorP N alpha s.u s.v k * p k := by
        apply Finset.sum_pos'
        · intro k hk
          exact mul_nonneg (s.p_nonneg k) (le_of_lt (hp k))
        · exact ⟨j, Finset.mem_univ j, mul_pos hj (hp j)⟩
      positivity
    · rcases hqStrict with ⟨j, hj⟩
      have hsq : 0 < ∑ k, separatorQ N beta s.u s.v k * q k := by
        apply Finset.sum_pos'
        · intro k hk
          exact mul_nonneg (s.q_nonneg k) (le_of_lt (hq k))
        · exact ⟨j, Finset.mem_univ j, mul_pos hj (hq j)⟩
      positivity
    · rcases heStrict with ⟨i, hi⟩
      have hse : 0 < ∑ k, separatorE rho s.u s.v k * e k := by
        apply Finset.sum_pos'
        · intro k hk
          exact mul_nonneg (s.e_nonneg k) (le_of_lt (he k))
        · exact ⟨i, Finset.mem_univ i, mul_pos hi (he i)⟩
      positivity
  have hzero := s.annihilates p q e hB hR
  linarith

end TypeIIL
