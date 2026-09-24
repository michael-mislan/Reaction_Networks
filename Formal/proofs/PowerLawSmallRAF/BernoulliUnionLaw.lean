import proofs.PowerLawSmallRAF.BernoulliRowColumnLaw

namespace PowerLawSmallRAF
open scoped BigOperators
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def bernoulliUnionParameter (p : I → ℝ) : ℝ := 1-∏ i, (1-p i)

omit [Fintype J] [DecidableEq J] in
theorem inhomogeneousSubsetWeight_nonempty_sum (p : I → ℝ) :
    (∑ A : Finset I, if A.Nonempty then inhomogeneousSubsetWeight p A else 0) =
      bernoulliUnionParameter p := by
  have hs : (∑ A : Finset I, if A.Nonempty then inhomogeneousSubsetWeight p A else 0)+
      (∑ A : Finset I, if A = ∅ then inhomogeneousSubsetWeight p A else 0) =
      ∑ A : Finset I, inhomogeneousSubsetWeight p A := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A _
    by_cases h : A = ∅ <;> simp [h, Finset.nonempty_iff_ne_empty]
  have he : (∑ A : Finset I, if A = ∅ then inhomogeneousSubsetWeight p A else 0) =
      inhomogeneousSubsetWeight p ∅ := by simp
  rw [he, inhomogeneousSubsetWeight_empty, inhomogeneousSubsetWeight_sum] at hs
  unfold bernoulliUnionParameter
  linarith

omit [Fintype J] [DecidableEq J] in
theorem inhomogeneousSubsetWeight_presence_sum (p : I → ℝ) (present : Prop) [Decidable present] :
    (∑ A : Finset I, if (A.Nonempty ↔ present) then inhomogeneousSubsetWeight p A else 0) =
      if present then bernoulliUnionParameter p else 1-bernoulliUnionParameter p := by
  by_cases h : present
  · simpa only [h, iff_true, if_true] using inhomogeneousSubsetWeight_nonempty_sum p
  · simp only [h, iff_false, if_false, Finset.not_nonempty_iff_eq_empty]
    simp [inhomogeneousSubsetWeight_empty, bernoulliUnionParameter]

def bernoulliRowsUnion (B : I → Finset J) : Finset J := Finset.univ.biUnion B

omit [DecidableEq I] [Fintype J] in
theorem bernoulliRowsUnion_eq_iff (B : I → Finset J) (S : Finset J) :
    bernoulliRowsUnion B = S ↔ ∀ j, (bernoulliRowTranspose B j).Nonempty ↔ j ∈ S := by
  have hm (j : J) : (bernoulliRowTranspose B j).Nonempty ↔ j ∈ bernoulliRowsUnion B := by
    simp [bernoulliRowTranspose, bernoulliRowsUnion, Finset.filter_nonempty_iff]
  constructor
  · intro h j
    rw [hm, h]
  · intro h
    ext j
    exact (hm j).symm.trans (h j)

/-- Exact iid channel law for the union of independent Bernoulli owner rows.
The parameter vector is fixed; degree mixing must occur after using this law. -/
theorem bernoulliRows_union_mass (p : I → ℝ) (S : Finset J) :
    (∑ B : I → Finset J, if bernoulliRowsUnion B = S then bernoulliRowsWeight p B else 0) =
      bernoulliSubsetRowWeight (bernoulliUnionParameter p) S := by
  calc
    _ = ∑ C : J → Finset I,
        if ∀ j, (C j).Nonempty ↔ j ∈ S then ∏ j, inhomogeneousSubsetWeight p (C j) else 0 := by
      apply Fintype.sum_equiv bernoulliRowColumnEquiv
      intro B
      simp only [bernoulliRowsUnion_eq_iff, bernoulliRowsWeight_transpose]
      rfl
    _ = ∏ j : J, ∑ A : Finset I,
        if (A.Nonempty ↔ j ∈ S) then inhomogeneousSubsetWeight p A else 0 := by
      simp_rw [← Fintype.prod_ite_zero]
      exact (Fintype.prod_sum (fun j (A : Finset I) =>
        if (A.Nonempty ↔ j ∈ S) then inhomogeneousSubsetWeight p A else 0)).symm
    _ = ∏ j : J, if j ∈ S then bernoulliUnionParameter p else 1-bernoulliUnionParameter p := by
      apply Finset.prod_congr rfl
      intro j _
      exact inhomogeneousSubsetWeight_presence_sum p (j ∈ S)
    _ = _ := by
      rw [← inhomogeneousSubsetWeight_eq_prod, inhomogeneousSubsetWeight_const]

theorem bernoulliRows_union_expectation (p : I → ℝ) (F : Finset J → ℝ) :
    (∑ B : I → Finset J, bernoulliRowsWeight p B * F (bernoulliRowsUnion B)) =
      ∑ S : Finset J, bernoulliSubsetRowWeight (bernoulliUnionParameter p) S * F S := by
  calc
    _ = ∑ B : I → Finset J, ∑ S : Finset J,
        (if bernoulliRowsUnion B = S then bernoulliRowsWeight p B else 0)*F S := by
      apply Finset.sum_congr rfl
      intro B _
      simp
    _ = ∑ S : Finset J, (∑ B : I → Finset J,
        if bernoulliRowsUnion B = S then bernoulliRowsWeight p B else 0)*F S := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp_rw [bernoulliRows_union_mass]

end
end PowerLawSmallRAF
