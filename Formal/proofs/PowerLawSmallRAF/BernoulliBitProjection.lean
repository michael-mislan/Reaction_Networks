import proofs.PowerLawSmallRAF.BernoulliRowColumnLaw
import proofs.PowerLawSmallRAF.LigationRawRowLaw

namespace PowerLawSmallRAF
open scoped BigOperators
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
set_option maxHeartbeats 100000

theorem bernoulliBit_partition_expectation (p : ℝ) (cut : J → Prop) [DecidablePred cut]
    (F : ({j // cut j} → Bool) → ℝ) :
    (∑ B : J → Bool, bernoulliFullRowWeight p B * F (fun j => B j.val)) =
      ∑ A : {j // cut j} → Bool, bernoulliFullRowWeight p A * F A := by
  classical
  calc
    _ = ∑ pair : ({j // cut j} → Bool) × ({j // ¬cut j} → Bool),
        bernoulliFullRowWeight p pair.1 * bernoulliFullRowWeight p pair.2 * F pair.1 := by
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd cut (fun _ : J => Bool))
      intro B
      change (∏ j, bernoulliBitWeight p (B j))*F (fun j => B j.val) =
        ((∏ j : {j // cut j}, bernoulliBitWeight p (B j.val))*
          (∏ j : {j // ¬cut j}, bernoulliBitWeight p (B j.val)))*F (fun j => B j.val)
      rw [Fintype.prod_subtype_mul_prod_subtype cut (fun j => bernoulliBitWeight p (B j))]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro A _
      simp only [mul_assoc, mul_left_comm (bernoulliFullRowWeight p A),
        ← Finset.sum_mul, sum_bernoulliFullRowWeight, one_mul]

theorem bernoulliBit_equiv_expectation (p : ℝ) (e : I ≃ J) (F : (I → Bool) → ℝ) :
    (∑ B : J → Bool, bernoulliFullRowWeight p B * F (fun i => B (e i))) =
      ∑ A : I → Bool, bernoulliFullRowWeight p A * F A := by
  let E : (J → Bool) ≃ (I → Bool) :=
    { toFun := fun B i => B (e i)
      invFun := fun A j => A (e.symm j)
      left_inv := by intro B; funext j; simp
      right_inv := by intro A; funext i; simp }
  apply Fintype.sum_equiv E
  intro B
  change bernoulliFullRowWeight p B * F (fun i => B (e i)) =
    bernoulliFullRowWeight p (fun i => B (e i)) * F (fun i => B (e i))
  congr 1
  exact (Fintype.prod_equiv e (fun i => bernoulliBitWeight p (B (e i)))
    (fun j => bernoulliBitWeight p (B j)) (fun _ => rfl)).symm

/-- Unqueried coordinates integrate to one; an injective projection retains
the exact iid law on the queried coordinates. -/
theorem bernoulliBit_embedding_expectation (p : ℝ) (e : I ↪ J) (F : (I → Bool) → ℝ) :
    (∑ B : J → Bool, bernoulliFullRowWeight p B * F (fun i => B (e i))) =
      ∑ A : I → Bool, bernoulliFullRowWeight p A * F A := by
  classical
  let er : I ≃ Set.range e := Equiv.ofInjective e e.injective
  have h := bernoulliBit_partition_expectation p (fun j => j ∈ Set.range e)
    (fun A => F (fun i => A (er i)))
  exact h.trans (@bernoulliBit_equiv_expectation I {j : J // j ∈ Set.range e}
    _ _ (Subtype.fintype (fun j => j ∈ Set.range e)) _ p er F)

def subsetBitEquiv : Finset J ≃ (J → Bool) where
  toFun H j := decide (j ∈ H)
  invFun B := Finset.univ.filter fun j => B j = true
  left_inv H := by ext j; simp
  right_inv B := by funext j; simp

theorem bernoulliSubset_bit_weight (p : ℝ) (H : Finset J) :
    bernoulliSubsetRowWeight p H = bernoulliFullRowWeight p (subsetBitEquiv H) := by
  rw [← inhomogeneousSubsetWeight_const, inhomogeneousSubsetWeight_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp [subsetBitEquiv, bernoulliBitWeight]

theorem bernoulliSubset_bit_expectation (p : ℝ) (F : (J → Bool) → ℝ) :
    (∑ H : Finset J, bernoulliSubsetRowWeight p H * F (subsetBitEquiv H)) =
      ∑ B : J → Bool, bernoulliFullRowWeight p B * F B := by
  apply Fintype.sum_equiv subsetBitEquiv
  intro H
  rw [bernoulliSubset_bit_weight]

theorem bernoulliSubset_embedding_expectation (p : ℝ)
    (e : I ↪ J) (F : (I → Bool) → ℝ) :
    (∑ H : Finset J, bernoulliSubsetRowWeight p H * F (fun i => decide (e i ∈ H))) =
      ∑ A : I → Bool, bernoulliFullRowWeight p A * F A :=
  (bernoulliSubset_bit_expectation p (fun B => F (fun i => B (e i)))).trans
    (bernoulliBit_embedding_expectation p e F)

end
end PowerLawSmallRAF
