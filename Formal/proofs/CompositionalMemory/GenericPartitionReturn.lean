import proofs.CompositionalMemory.GenericPartitionLaw
import proofs.CompositionalMemory.GenericPartitionGeometry

namespace CompositionalMemory

noncomputable def generalBothReturn {k d : ℕ} (N : ℕ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (birth : ℝ)
    (n : Fin k → Fin d → ℕ) (x : GeneralDraw k d) : Prop :=
  ∀ i, Q i (fun a => (x (i,a):ℝ)/(N:ℝ)-center i a)
      (fun a => (x (i,a):ℝ)/(N:ℝ)-center i a) < birth ∧
    Q i (fun a => ((n i a-x (i,a):ℕ):ℝ)/(N:ℝ)-center i a)
      (fun a => ((n i a-x (i,a):ℕ):ℝ)/(N:ℝ)-center i a) < birth

noncomputable instance {k d : ℕ} (N : ℕ)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (center : Fin k → Fin d → ℝ) (birth : ℝ)
    (n : Fin k → Fin d → ℕ) (x : GeneralDraw k d) :
    Decidable (generalBothReturn N Q center birth n x) := Classical.propDecidable _

theorem general_partition_return {k d : ℕ} (N : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hQ : ∀ i x y, Q i x y=Q i y x) (center : Fin k → Fin d → ℝ)
    (c L r δ parent birth : ℝ) (hc : 0 < c) (hL : 0 ≤ L) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y) (hop : ∀ i x y, |Q i x y| ≤ L*‖x‖*‖y‖)
    (hsize : parent ≤ c*r^2) (hbudget : parent+2*L*r*δ+L*δ^2 < birth)
    (n : Fin k → Fin d → ℕ)
    (hparent : ∀ i, Q i (fun a => (n i a:ℝ)/(2*(N:ℝ))-center i a)
      (fun a => (n i a:ℝ)/(2*(N:ℝ))-center i a) ≤ parent)
    (x : GeneralDraw k d) (hx : x ∈ generalDraws n)
    (hgood : ∀ j : Fin k × Fin d, |(x j:ℝ)-(n j.1 j.2:ℝ)/2| < (N:ℝ)*δ) :
    generalBothReturn N Q center birth n x := by
  intro i
  apply general_both_daughters_return (Q i) (hQ i) c L r δ parent birth hc hL hr hδ
    (hcoerc i) (hop i) hsize hbudget (n i) (fun a => x (i,a)) _ N hN (center i)
    (hparent i) (fun a => hgood (i,a))
  intro a
  exact Nat.le_of_lt_succ (Finset.mem_range.mp ((Fintype.mem_piFinset.mp hx) (i,a)))

/-- The probability that either daughter leaves its inherited birth region.
The complement is evaluated under a single normalized joint allocation law. -/
theorem general_partition_failure {k d : ℕ} (N : ℕ) (hN : 0 < N)
    (Q : Fin k → (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (hQ : ∀ i x y, Q i x y=Q i y x) (center : Fin k → Fin d → ℝ)
    (c L r δ parent birth C : ℝ) (hc : 0 < c) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hδ : 0 < δ) (hC : 0 < C)
    (hcoerc : ∀ i y, c*‖y‖^2 ≤ Q i y y) (hop : ∀ i x y, |Q i x y| ≤ L*‖x‖*‖y‖)
    (hsize : parent ≤ c*r^2) (hbudget : parent+2*L*r*δ+L*δ^2 < birth)
    (n : Fin k → Fin d → ℕ) (hn : ∀ i a, (n i a:ℝ) ≤ C*(N:ℝ))
    (hparent : ∀ i, Q i (fun a => (n i a:ℝ)/(2*(N:ℝ))-center i a)
      (fun a => (n i a:ℝ)/(2*(N:ℝ))-center i a) ≤ parent) :
    (∑ x ∈ generalDraws n, generalDrawWeight n x*
      (if ¬ generalBothReturn N Q center birth n x then 1 else 0)) ≤
      2*(k:ℝ)*(d:ℝ)*Real.exp (-2*(N:ℝ)*δ^2/C) := by
  classical
  have hpoint (x : GeneralDraw k d) (hx : x ∈ generalDraws n) :
      generalDrawWeight n x*(if ¬ generalBothReturn N Q center birth n x then 1 else 0) ≤
      generalDrawWeight n x*(if ∃ i : Fin k × Fin d, (N:ℝ)*δ ≤ |(x i:ℝ)-(n i.1 i.2:ℝ)/2| then 1 else 0) := by
    by_cases hbad : ∃ i : Fin k × Fin d, (N:ℝ)*δ ≤ |(x i:ℝ)-(n i.1 i.2:ℝ)/2|
    · rw [if_pos hbad,mul_one]
      split_ifs
      · simpa only [mul_zero] using general_draw_weight_nonneg n x
      · simp
    · have hg (i : Fin k × Fin d) : |(x i:ℝ)-(n i.1 i.2:ℝ)/2| < (N:ℝ)*δ :=
        lt_of_not_ge (fun hi => hbad ⟨i,hi⟩)
      have hreturn := general_partition_return N hN Q hQ center c L r δ parent birth
        hc hL hr hδ.le hcoerc hop hsize hbudget n hparent x hx hg
      rw [if_neg (not_not.mpr hreturn),mul_zero]
      exact mul_nonneg (general_draw_weight_nonneg n x) (by positivity)
  exact (Finset.sum_le_sum (fun x hx => hpoint x hx)).trans
    (general_draw_joint_tail n N hN C δ hC hδ hn)

end CompositionalMemory
