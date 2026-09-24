import proofs.PowerLawSmallRAF.BernoulliRowCouplingTail

namespace PowerLawSmallRAF

open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def rowCouplingProductWeight (p : I → ℝ) (d : I → Nat)
    (B T : I → Finset J) : ℝ := ∏ i, bernoulliUniformRowJointWeight (p i) (d i) (B i) (T i)

def bernoulliRowsWeight (p : I → ℝ) (B : I → Finset J) : ℝ :=
  ∏ i, bernoulliSubsetRowWeight (p i) (B i)

def uniformFixedRowsWeight (d : I → Nat) (T : I → Finset J) : ℝ :=
  ∏ i, uniformFixedRowWeight (d i) (T i)

omit [DecidableEq I] in
theorem rowCouplingProductWeight_nonneg (p : I → ℝ) (d : I → Nat)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (B T : I → Finset J) :
    0 ≤ rowCouplingProductWeight p d B T := by
  apply Finset.prod_nonneg
  intro i _
  exact bernoulliUniformRowJointWeight_nonneg (hp i) (hp1 i) (d i) (B i) (T i)

theorem rowCouplingProductWeight_left_marginal (p : I → ℝ) (d : I → Nat)
    (hd : ∀ i, d i ≤ Fintype.card J) (B : I → Finset J) :
    (∑ T : I → Finset J, rowCouplingProductWeight p d B T) = bernoulliRowsWeight p B := by
  unfold rowCouplingProductWeight bernoulliRowsWeight
  rw [← Fintype.prod_sum (fun i (T : Finset J) => bernoulliUniformRowJointWeight (p i) (d i) (B i) T)]
  apply Finset.prod_congr rfl
  intro i _
  exact bernoulliUniformRowJointWeight_left_marginal (p i) (d i) (hd i) (B i)

theorem rowCouplingProductWeight_right_marginal (p : I → ℝ) (d : I → Nat)
    (hd : ∀ i, d i ≤ Fintype.card J) (T : I → Finset J) :
    (∑ B : I → Finset J, rowCouplingProductWeight p d B T) = uniformFixedRowsWeight d T := by
  unfold rowCouplingProductWeight uniformFixedRowsWeight
  rw [← Fintype.prod_sum (fun i (B : Finset J) => bernoulliUniformRowJointWeight (p i) (d i) B (T i))]
  apply Finset.prod_congr rfl
  intro i _
  exact bernoulliUniformRowJointWeight_right_marginal (p i) (d i) (hd i) (T i)

private theorem sum_pair_product {A C : Type*} [Fintype A] [Fintype C]
    (f : I → A → C → ℝ) :
    (∑ a : I → A, ∑ c : I → C, ∏ i, f i (a i) (c i)) = ∏ i, ∑ a : A, ∑ c : C, f i a c := by
  calc
    _ = ∑ a : I → A, ∏ i, ∑ c : C, f i (a i) c := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Fintype.prod_sum (fun i (c : C) => f i (a i) c)).symm
    _ = _ := (Fintype.prod_sum (fun i (a : A) => ∑ c : C, f i a c)).symm

private theorem sum_pair_product_coordinate {A C : Type*} [Fintype A] [Fintype C]
    (f : I → A → C → ℝ) (hf : ∀ i, (∑ a : A, ∑ c : C, f i a c) = 1)
    (i : I) (P : A → C → Prop) [DecidableRel P] :
    (∑ a : I → A, ∑ c : I → C,
      if P (a i) (c i) then ∏ j, f j (a j) (c j) else 0) =
      ∑ a : A, ∑ c : C, if P a c then f i a c else 0 := by
  classical
  let g := fun (j : I) (a : A) (c : C) => if j = i then (if P a c then f j a c else 0) else f j a c
  have hpoint : ∀ (a : I → A) (c : I → C),
      (if P (a i) (c i) then ∏ j, f j (a j) (c j) else 0) = ∏ j, g j (a j) (c j) := by
    intro a c
    by_cases hP : P (a i) (c i)
    · rw [if_pos hP]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i <;> simp [g, hji, hP]
    · rw [if_neg hP]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [g, hP]
  simp_rw [hpoint]
  rw [sum_pair_product]
  rw [Finset.prod_eq_single i]
  · simp only [g, ↓reduceIte]
  · intro j _ hji
    simp only [g, hji, ↓reduceIte]
    exact hf j
  · simp

theorem rowCouplingProductWeight_coordinate_failure (p : I → ℝ) (d : I → Nat)
    (hd : ∀ i, d i ≤ Fintype.card J) (i : I) :
    (∑ B : I → Finset J, ∑ T : I → Finset J,
      if ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) =
      bernoulliRowOverflowMass (J := J) (p i) (d i) := by
  have h := sum_pair_product_coordinate
    (fun j (B T : Finset J) => bernoulliUniformRowJointWeight (p j) (d j) B T)
    (fun j => sum_bernoulliUniformRowJointWeight (p j) (d j) (hd j)) i (fun B T => ¬ B ⊆ T)
  rw [bernoulliUniformRowJointWeight_containment_failure (p i) (d i) (hd i)] at h
  exact h

theorem rowCouplingProductWeight_failure_le_sum (p : I → ℝ) (d : I → Nat)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hd : ∀ i, d i ≤ Fintype.card J) :
    (∑ B : I → Finset J, ∑ T : I → Finset J,
      if ∃ i, ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) ≤
      ∑ i, bernoulliRowOverflowMass (J := J) (p i) (d i) := by
  classical
  have hswap : (∑ i, ∑ B : I → Finset J, ∑ T : I → Finset J,
      if ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) =
      ∑ B : I → Finset J, ∑ T : I → Finset J, ∑ i,
        if ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B _
    rw [Finset.sum_comm]
  have hu : (∑ B : I → Finset J, ∑ T : I → Finset J,
      if ∃ i, ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) ≤
      ∑ i, ∑ B : I → Finset J, ∑ T : I → Finset J,
        if ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0 := by
    rw [hswap]
    apply Finset.sum_le_sum
    intro B _
    apply Finset.sum_le_sum
    intro T _
    have hn : ∀ i ∈ (Finset.univ : Finset I),
        0 ≤ (if ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) := by
      intro i _
      by_cases hi : B i ⊆ T i
      · simp [hi]
      · simpa only [hi, not_false_eq_true, ↓reduceIte] using
          rowCouplingProductWeight_nonneg p d hp hp1 B T
    split_ifs with hbad
    · obtain ⟨i, hi⟩ := hbad
      have hle := Finset.single_le_sum hn (Finset.mem_univ i)
      simpa only [if_pos hi] using hle
    · exact Finset.sum_nonneg hn
  simpa only [rowCouplingProductWeight_coordinate_failure p d hd] using hu

/-- Independent molecule rows can be coupled simultaneously; the entire
failure probability is paid once by the explicit row-tail sum. -/
theorem rowCouplingProductWeight_failure_le_exp (p : I → ℝ) (d : I → Nat)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hd : ∀ i, d i ≤ Fintype.card J)
    (eps : I → ℝ) (heps : ∀ i, 0 ≤ eps i)
    (hmean : ∀ i, (Fintype.card J : ℝ)*p i ≤ (1-eps i)*(d i : ℝ)) :
    (∑ B : I → Finset J, ∑ T : I → Finset J,
      if ∃ i, ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) ≤
      ∑ i, Real.exp (-(eps i)^2*(d i : ℝ)/4) := by
  apply (rowCouplingProductWeight_failure_le_sum p d hp hp1 hd).trans
  apply Finset.sum_le_sum
  intro i _
  exact bernoulliRowOverflowMass_le_exp_slack (hp i) (hp1 i) (d i) (eps i) (heps i) (hmean i)

/-- Every increasing event transfers from independent Bernoulli molecule rows
to independent uniform fixed-degree rows, paying the explicit coupling error. -/
theorem bernoulliRows_increasing_event_le_uniform_tail (p : I → ℝ) (d : I → Nat)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hd : ∀ i, d i ≤ Fintype.card J)
    (F : (I → Finset J) → Prop) [DecidablePred F]
    (hmono : ∀ B T, (∀ i, B i ⊆ T i) → F B → F T) :
    (∑ B : I → Finset J, if F B then bernoulliRowsWeight p B else 0) ≤
      (∑ T : I → Finset J, if F T then uniformFixedRowsWeight d T else 0) +
        ∑ i, bernoulliRowOverflowMass (J := J) (p i) (d i) := by
  classical
  have hleft : (∑ B : I → Finset J, if F B then bernoulliRowsWeight p B else 0) =
      ∑ B : I → Finset J, ∑ T : I → Finset J,
        if F B then rowCouplingProductWeight p d B T else 0 := by
    apply Finset.sum_congr rfl
    intro B _
    by_cases hB : F B
    · simp only [hB, ↓reduceIte]
      exact (rowCouplingProductWeight_left_marginal p d hd B).symm
    · simp only [hB, ↓reduceIte, Finset.sum_const_zero]
  have hright : (∑ B : I → Finset J, ∑ T : I → Finset J,
      if F T then rowCouplingProductWeight p d B T else 0) =
      ∑ T : I → Finset J, if F T then uniformFixedRowsWeight d T else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : F T
    · simp only [hT, ↓reduceIte]
      exact rowCouplingProductWeight_right_marginal p d hd T
    · simp only [hT, ↓reduceIte, Finset.sum_const_zero]
  have hpoint : ∀ (B T : I → Finset J),
      (if F B then rowCouplingProductWeight p d B T else 0) ≤
        (if F T then rowCouplingProductWeight p d B T else 0) +
        (if ∃ i, ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) := by
    intro B T
    have hn := rowCouplingProductWeight_nonneg p d hp hp1 B T
    by_cases hB : F B
    · by_cases hT : F T
      · simp only [if_pos hB, if_pos hT]
        split_ifs <;> linarith only [hn]
      · have hbad : ∃ i, ¬ B i ⊆ T i := by
          by_contra h
          apply hT
          apply hmono B T _ hB
          intro i
          by_contra hi
          exact h ⟨i, hi⟩
        simp only [if_pos hB, if_neg hT, if_pos hbad, zero_add]
        exact le_rfl
    · simp only [if_neg hB]
      split_ifs <;> linarith only [hn]
  rw [hleft]
  calc
    _ ≤ ∑ B : I → Finset J, ∑ T : I → Finset J,
        ((if F T then rowCouplingProductWeight p d B T else 0) +
         (if ∃ i, ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0)) := by
      apply Finset.sum_le_sum
      intro B _
      apply Finset.sum_le_sum
      intro T _
      exact hpoint B T
    _ = (∑ B : I → Finset J, ∑ T : I → Finset J,
          if F T then rowCouplingProductWeight p d B T else 0) +
        (∑ B : I → Finset J, ∑ T : I → Finset J,
          if ∃ i, ¬ B i ⊆ T i then rowCouplingProductWeight p d B T else 0) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (le_of_eq hright)
      (rowCouplingProductWeight_failure_le_sum p d hp hp1 hd)

theorem bernoulliRows_increasing_event_le_uniform (p : I → ℝ) (d : I → Nat)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hd : ∀ i, d i ≤ Fintype.card J)
    (eps : I → ℝ) (heps : ∀ i, 0 ≤ eps i)
    (hmean : ∀ i, (Fintype.card J : ℝ)*p i ≤ (1-eps i)*(d i : ℝ))
    (F : (I → Finset J) → Prop) [DecidablePred F]
    (hmono : ∀ B T, (∀ i, B i ⊆ T i) → F B → F T) :
    (∑ B : I → Finset J, if F B then bernoulliRowsWeight p B else 0) ≤
      (∑ T : I → Finset J, if F T then uniformFixedRowsWeight d T else 0) +
        ∑ i, Real.exp (-(eps i)^2*(d i : ℝ)/4) := by
  apply (bernoulliRows_increasing_event_le_uniform_tail p d hp hp1 hd F hmono).trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  exact bernoulliRowOverflowMass_le_exp_slack (hp i) (hp1 i) (d i) (eps i) (heps i) (hmean i)

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem bernoulliRowOverflowMass_zero (d : Nat) :
    bernoulliRowOverflowMass (J := J) 0 d = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro B _
  by_cases h : d < B.card
  · have hb : B.card ≠ 0 := by omega
    simp [h, bernoulliSubsetRowWeight, hb]
  · simp [h]

end
end PowerLawSmallRAF
