import proofs.HordijkSteelThreshold.SplitOverlapMoments

namespace HordijkSteelThreshold

/-- Number of split families that miss a target. -/
def splitMissingCount {ι α : Type*} [Fintype ι] [DecidableEq α]
    (A : ι → Finset α) (x : α) : Nat :=
  ∑ i, if x ∈ A i then 0 else 1

/-- Viable and missing split counts partition the split positions exactly. -/
theorem splitIncidenceCount_add_missing {ι α : Type*} [Fintype ι]
    [DecidableEq α] (A : ι → Finset α) (x : α) :
    splitIncidenceCount A x + splitMissingCount A x = Fintype.card ι := by
  classical
  simp only [splitIncidenceCount, splitMissingCount, ← Finset.sum_add_distrib]
  calc
    (∑ i : ι, ((if x ∈ A i then 1 else 0) +
      if x ∈ A i then 0 else 1)) = ∑ _i : ι, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x ∈ A i <;> simp [hi]
    _ = Fintype.card ι := by simp

/-- Exact first moment of missing-split counts. -/
theorem sum_splitMissingCount {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ι → Finset α) :
    ∑ x, splitMissingCount A x =
      ∑ i, ((Finset.univ : Finset α) \ A i).card := by
  classical
  simp only [splitMissingCount]
  rw [Finset.sum_comm]
  congr 1
  funext i
  simpa [Finset.sdiff_eq_filter] using
    (Finset.sum_boole (fun x : α => x ∉ A i) (Finset.univ : Finset α) :
      (∑ x ∈ (Finset.univ : Finset α), if x ∉ A i then 1 else 0) = _)

/-- Targets missing at least `d` of their candidate split families. -/
def splitMissingTail {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ι → Finset α) (d : Nat) : Finset α :=
  Finset.univ.filter fun x => d ≤ splitMissingCount A x

/-- Deterministic Markov bound for the lower tail of viable split counts. -/
theorem threshold_mul_card_splitMissingTail_le_sum {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α]
    (A : ι → Finset α) (d : Nat) :
    d * (splitMissingTail A d).card ≤ ∑ x, splitMissingCount A x := by
  classical
  calc
    d * (splitMissingTail A d).card =
        ∑ _x ∈ splitMissingTail A d, d := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ splitMissingTail A d, splitMissingCount A x := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x, splitMissingCount A x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- Uniform overlap-safe lower-tail bound. If every split family misses at
most `b` targets, at most `(number of splits)*b/d` targets can miss `d` or
more splits. No independence among factor-generation events is assumed. -/
theorem threshold_mul_card_splitMissingTail_le_uniform {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α]
    (A : ι → Finset α) (b d : Nat)
    (hA : ∀ i, ((Finset.univ : Finset α) \ A i).card ≤ b) :
    d * (splitMissingTail A d).card ≤ Fintype.card ι * b := by
  calc
    d * (splitMissingTail A d).card ≤ ∑ x, splitMissingCount A x :=
      threshold_mul_card_splitMissingTail_le_sum A d
    _ = ∑ i, ((Finset.univ : Finset α) \ A i).card :=
      sum_splitMissingCount A
    _ ≤ ∑ _i : ι, b := by
      exact Finset.sum_le_sum fun i _ => hA i
    _ = Fintype.card ι * b := by simp

/-- Outside the missing-split tail, a target has more than
`number of splits - d` viable splits. -/
theorem many_viable_splits_of_not_mem_tail {ι α : Type*} [Fintype ι]
    [Fintype α] [DecidableEq α] (A : ι → Finset α) (d : Nat) {x : α}
    (hx : x ∉ splitMissingTail A d) :
    Fintype.card ι < splitIncidenceCount A x + d := by
  classical
  have hmissing : splitMissingCount A x < d := by
    simpa [splitMissingTail] using hx
  have hpartition := splitIncidenceCount_add_missing A x
  omega

end HordijkSteelThreshold
