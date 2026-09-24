import Mathlib

namespace HordijkSteelThreshold

/-- Number of candidate split families containing a target.  In the polymer
application, `A i` is the set of words whose split at position `i` has both
factors in the current marked language. -/
def splitIncidenceCount {ι α : Type*} [Fintype ι] [DecidableEq α]
    (A : ι → Finset α) (x : α) : Nat :=
  ∑ i, if x ∈ A i then 1 else 0

/-- The first moment of viable-split counts loses no mass: it is the sum of
the sizes of the individual split families. -/
theorem sum_splitIncidenceCount {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ι → Finset α) :
    ∑ x, splitIncidenceCount A x = ∑ i, (A i).card := by
  classical
  simp only [splitIncidenceCount]
  rw [Finset.sum_comm]
  congr 1
  funext i
  simp [Finset.inter_comm]

/-- Exact overlap correction for the second moment.  The diagonal terms are
single-split masses and every off-diagonal term is the literal intersection of
two split cones; no independence assumption is present. -/
theorem sum_sq_splitIncidenceCount {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ι → Finset α) :
    ∑ x, (splitIncidenceCount A x) ^ 2 =
      ∑ i, ∑ j, ((A i) ∩ (A j)).card := by
  classical
  simp only [splitIncidenceCount, pow_two]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  rw [Finset.sum_comm]
  congr 1
  funext j
  simp [Finset.inter_comm]

/-- A target with zero viable splits belongs to none of the split families. -/
theorem splitIncidenceCount_eq_zero_iff {ι α : Type*} [Fintype ι]
    [DecidableEq α] (A : ι → Finset α) (x : α) :
    splitIncidenceCount A x = 0 ↔ ∀ i, x ∉ A i := by
  classical
  simp [splitIncidenceCount]

/-- Targets carrying at least one viable split. -/
def splitPositiveTargets {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : ι → Finset α) : Finset α :=
  Finset.univ.filter fun x => 0 < splitIncidenceCount A x

/-- Finite Paley--Zygmund/Cauchy--Schwarz interface.  A small pair-overlap
second moment forces many targets to have at least one viable split. -/
theorem sq_total_splitIncidence_le_positive_mul_second {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] (A : ι → Finset α) :
    (∑ x, splitIncidenceCount A x) ^ 2 ≤
      (splitPositiveTargets A).card *
        ∑ x, (splitIncidenceCount A x) ^ 2 := by
  classical
  let S := splitPositiveTargets A
  have hzero : ∀ x ∈ (Finset.univ : Finset α), x ∉ S →
      splitIncidenceCount A x = 0 := by
    intro x _ hx
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hpos⟩)
  have hsum : (∑ x, splitIncidenceCount A x) =
      ∑ x ∈ S, splitIncidenceCount A x := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  have hsq : (∑ x, (splitIncidenceCount A x) ^ 2) =
      ∑ x ∈ S, (splitIncidenceCount A x) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hxS
    rw [hzero x hx hxS]
    simp
  rw [hsum, hsq]
  exact sq_sum_le_card_mul_sum_sq

/-- Density-only survival bound. If every split family contains at least `a`
targets, then arbitrary overlap still cannot concentrate all viable incidences
on fewer targets than permitted by this inequality. No cylinder-mixing or
independence hypothesis is used. -/
theorem sq_uniform_split_mass_le_positive {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] (A : ι → Finset α) (a : Nat)
    (hA : ∀ i, a ≤ (A i).card) :
    (Fintype.card ι * a) ^ 2 ≤
      (splitPositiveTargets A).card *
        (Fintype.card ι * Fintype.card ι * Fintype.card α) := by
  classical
  have hfirst : Fintype.card ι * a ≤ ∑ x, splitIncidenceCount A x := by
    rw [sum_splitIncidenceCount]
    simpa using Finset.sum_le_sum fun i _ => hA i
  have hsecond : (∑ x, (splitIncidenceCount A x) ^ 2) ≤
      Fintype.card ι * Fintype.card ι * Fintype.card α := by
    rw [sum_sq_splitIncidenceCount]
    calc
      (∑ i, ∑ j, ((A i) ∩ (A j)).card) ≤
          ∑ _i : ι, ∑ _j : ι, Fintype.card α := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact Finset.card_le_univ _
      _ = Fintype.card ι * Fintype.card ι * Fintype.card α := by
        simp
        ring
  calc
    (Fintype.card ι * a) ^ 2 ≤
        (∑ x, splitIncidenceCount A x) ^ 2 := Nat.pow_le_pow_left hfirst 2
    _ ≤ (splitPositiveTargets A).card *
        ∑ x, (splitIncidenceCount A x) ^ 2 :=
      sq_total_splitIncidence_le_positive_mul_second A
    _ ≤ (splitPositiveTargets A).card *
        (Fintype.card ι * Fintype.card ι * Fintype.card α) :=
      Nat.mul_le_mul_left _ hsecond

end HordijkSteelThreshold
