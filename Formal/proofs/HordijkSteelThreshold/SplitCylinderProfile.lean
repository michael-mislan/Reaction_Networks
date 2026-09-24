import proofs.HordijkSteelThreshold.SplitOverlapMoments

namespace HordijkSteelThreshold

/-- Targets whose viable-split count lies at least `d` below the reference
count `c`. -/
def splitIncidenceLowTail {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ι → Finset α) (c d : Nat) : Finset α :=
  Finset.univ.filter fun x => splitIncidenceCount A x + d ≤ c

/-- The unnormalized squared cylinder discrepancy of the split-incidence
profile around an integer reference count. -/
noncomputable def splitIncidenceSquaredDeviation {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α]
    (A : ι → Finset α) (c : Nat) : ℝ :=
  ∑ x, ((splitIncidenceCount A x : ℝ) - c) ^ 2

/-- Deterministic Chebyshev inequality for a split-incidence profile. This is
the exact interface needed to supplement constant layer density by cylinder
mixing. -/
theorem sq_mul_card_splitIncidenceLowTail_le_deviation
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : ι → Finset α) (c d : Nat) :
    (d : ℝ) ^ 2 * (splitIncidenceLowTail A c d).card ≤
      splitIncidenceSquaredDeviation A c := by
  classical
  rw [splitIncidenceSquaredDeviation]
  calc
    (d : ℝ) ^ 2 * (splitIncidenceLowTail A c d).card =
        ∑ _x ∈ splitIncidenceLowTail A c d, (d : ℝ) ^ 2 := by
      simp [mul_comm]
    _ ≤ ∑ x ∈ splitIncidenceLowTail A c d,
        ((splitIncidenceCount A x : ℝ) - c) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      have hlow : splitIncidenceCount A x + d ≤ c :=
        (Finset.mem_filter.mp hx).2
      have hreal : (splitIncidenceCount A x : ℝ) + d ≤ c := by
        exact_mod_cast hlow
      nlinarith [sq_nonneg ((splitIncidenceCount A x : ℝ) - c + d)]
    _ ≤ ∑ x, ((splitIncidenceCount A x : ℝ) - c) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- The squared discrepancy expands into the exact first and second split
moments, so pairwise cylinder intersections are the only additional state. -/
theorem splitIncidenceSquaredDeviation_eq_moments
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : ι → Finset α) (c : Nat) :
    splitIncidenceSquaredDeviation A c =
      (∑ x, (splitIncidenceCount A x : ℝ) ^ 2) -
        2 * c * (∑ x, (splitIncidenceCount A x : ℝ)) +
          Fintype.card α * (c : ℝ) ^ 2 := by
  classical
  rw [splitIncidenceSquaredDeviation]
  simp_rw [sub_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]
  simp
  apply Finset.sum_congr rfl
  intro x hx
  ring

end HordijkSteelThreshold
