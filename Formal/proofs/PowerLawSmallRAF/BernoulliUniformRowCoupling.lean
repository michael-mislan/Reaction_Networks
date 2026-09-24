import proofs.PowerLawSmallRAF.UniformRowCoupling

namespace PowerLawSmallRAF

open scoped BigOperators

noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def bernoulliSubsetRowWeight (p : ℝ) (B : Finset J) : ℝ :=
  p^B.card * (1-p)^(Fintype.card J-B.card)

omit [DecidableEq J] in
theorem bernoulliSubsetRowWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (B : Finset J) : 0 ≤ bernoulliSubsetRowWeight p B := by
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (sub_nonneg.mpr hp1) _)

omit [DecidableEq J] in
theorem sum_bernoulliSubsetRowWeight (p : ℝ) :
    (∑ B : Finset J, bernoulliSubsetRowWeight p B) = 1 := by
  classical
  unfold bernoulliSubsetRowWeight
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun b => p^b * (1-p)^(Fintype.card J-b))]
  simp only [Finset.card_univ, nsmul_eq_mul]
  have h := add_pow p (1-p) (Fintype.card J)
  have hbase : p + (1-p) = 1 := by ring
  rw [hbase, one_pow] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

def bernoulliUniformRowJointWeight (p : ℝ) (d : Nat) (B T : Finset J) : ℝ :=
  bernoulliSubsetRowWeight p B * uniformRowCompletionKernel d B T

def uniformFixedRowWeight (d : Nat) (T : Finset J) : ℝ :=
  if T.card = d then (Nat.choose (Fintype.card J) d : ℝ)⁻¹ else 0

theorem bernoulliUniformRowJointWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (d : Nat) (B T : Finset J) : 0 ≤ bernoulliUniformRowJointWeight p d B T := by
  exact mul_nonneg (bernoulliSubsetRowWeight_nonneg hp hp1 B)
    (uniformRowCompletionKernel_nonneg d B T)

theorem bernoulliUniformRowJointWeight_left_marginal (p : ℝ)
    (d : Nat) (hd : d ≤ Fintype.card J) (B : Finset J) :
    (∑ T : Finset J, bernoulliUniformRowJointWeight p d B T) =
      bernoulliSubsetRowWeight p B := by
  unfold bernoulliUniformRowJointWeight
  rw [← Finset.mul_sum, sum_uniformRowCompletionKernel d hd B, mul_one]

theorem bernoulliUniformRowJointWeight_right_marginal (p : ℝ)
    (d : Nat) (hd : d ≤ Fintype.card J) (T : Finset J) :
    (∑ B : Finset J, bernoulliUniformRowJointWeight p d B T) = uniformFixedRowWeight d T := by
  by_cases hT : T.card = d
  · unfold bernoulliUniformRowJointWeight bernoulliSubsetRowWeight
    rw [uniformRowCompletionKernel_radial_marginal d hd
      (fun b => p^b * (1-p)^(Fintype.card J-b)) (sum_bernoulliSubsetRowWeight p) T hT]
    simp only [uniformFixedRowWeight, hT, ↓reduceIte]
  · simp [bernoulliUniformRowJointWeight, uniformRowCompletionKernel, uniformFixedRowWeight, hT]

theorem sum_bernoulliUniformRowJointWeight (p : ℝ)
    (d : Nat) (hd : d ≤ Fintype.card J) :
    (∑ B : Finset J, ∑ T : Finset J, bernoulliUniformRowJointWeight p d B T) = 1 := by
  simp_rw [bernoulliUniformRowJointWeight_left_marginal p d hd]
  exact sum_bernoulliSubsetRowWeight p

theorem uniformRowCompletionKernel_not_subset_sum (d : Nat)
    (hd : d ≤ Fintype.card J) (B : Finset J) :
    (∑ T : Finset J, if ¬ B ⊆ T then uniformRowCompletionKernel d B T else 0) =
      if d < B.card then 1 else 0 := by
  by_cases hbd : B.card ≤ d
  · have hzero : ∀ T : Finset J,
        (if ¬ B ⊆ T then uniformRowCompletionKernel d B T else 0) = 0 := by
      intro T
      by_cases hs : B ⊆ T <;> simp [uniformRowCompletionKernel, hbd, hs]
    simp only [hzero, Finset.sum_const_zero, if_neg (by omega : ¬d < B.card)]
  · have heq : ∀ T : Finset J,
        (if ¬ B ⊆ T then uniformRowCompletionKernel d B T else 0) =
          uniformRowCompletionKernel d B T := by
      intro T
      by_cases hs : B ⊆ T
      · have hT : T.card ≠ d := by
          have := Finset.card_le_card hs
          omega
        simp [uniformRowCompletionKernel, hs, hT]
      · simp [hs]
    simp only [heq, sum_uniformRowCompletionKernel d hd B, if_pos (by omega : d < B.card)]

/-- The coupling's entire failure mass is exactly the upper tail of the
Bernoulli input cardinality; it is not an unspecified coupling defect. -/
theorem bernoulliUniformRowJointWeight_containment_failure (p : ℝ)
    (d : Nat) (hd : d ≤ Fintype.card J) :
    (∑ B : Finset J, ∑ T : Finset J,
      if ¬ B ⊆ T then bernoulliUniformRowJointWeight p d B T else 0) =
      ∑ B : Finset J, if d < B.card then bernoulliSubsetRowWeight p B else 0 := by
  apply Finset.sum_congr rfl
  intro B _
  have heq : ∀ T : Finset J,
      (if ¬ B ⊆ T then bernoulliUniformRowJointWeight p d B T else 0) =
        bernoulliSubsetRowWeight p B *
          (if ¬ B ⊆ T then uniformRowCompletionKernel d B T else 0) := by
    intro T
    by_cases hs : B ⊆ T <;> simp [bernoulliUniformRowJointWeight, hs]
  simp_rw [heq]
  rw [← Finset.mul_sum, uniformRowCompletionKernel_not_subset_sum d hd B]
  split_ifs <;> simp

end
end PowerLawSmallRAF
