import proofs.RandomViability.CollectiveCountJumps

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

def physicalNonfoodQuadraticRate {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) : ℝ :=
  ∑ ch, unboundedPhysicalRate c V 1 basal cat N ch *
    (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)^2

/-- Actual physical quadratic rate: internal chemistry has a constant jump
bound, while only dilution contributes polymer horizon n. -/
theorem physical_nonfood_quadratic_rate_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    physicalNonfoodQuadraticRate c V basal cat N ≤
      16*(∑ ch,unboundedPhysicalRate c V 1 basal cat N ch)+(n : ℝ)*countMass N := by
  let R := unboundedPhysicalRate c V 1 basal cat N
  let A := fun ch => (countNonfoodMass (unboundedPhysicalNext N ch)-countNonfoodMass N)^2
  have hr (ch) : 0 ≤ R ch := unboundedPhysicalRate_nonneg c V 1 basal cat N ch
  have hfeed : (∑ f : ↥(binaryFood n 2), R (.inl (.inl f))*A (.inl (.inl f))) = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    simp only [A,unbounded_feed_nonfood_jump,zero_pow (by decide : 2 ≠ 0),mul_zero]
  have hout : (∑ x : Molecule n, R (.inl (.inr x))*A (.inl (.inr x))) ≤
      (n : ℝ)*countMass N := by
    have he (x : Molecule n) : R (.inl (.inr x)) = (N x : ℝ) := by
      have hh := bounded_outflow_rate c V 1 hV basal cat (countsAtOwnMass N) x
      change R (.inl (.inr x)) = (1 : ℝ)*(N x : ℝ) at hh
      simpa only [one_mul] using hh
    calc
      _ ≤ ∑ x : Molecule n, (N x : ℝ)*((n : ℝ)*molLength x) := by
        apply Finset.sum_le_sum
        intro x _
        rw [he]
        exact mul_le_mul_of_nonneg_left (unbounded_outflow_nonfood_jump_sq N x) (by positivity)
      _ = _ := by
        simp only [countMass,Nat.cast_sum,Nat.cast_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  have hb : (∑ r : Reaction n, ∑ d : Bool, R (.inr (.inl (r,d)))*A (.inr (.inl (r,d)))) ≤
      16*(∑ r : Reaction n, ∑ d : Bool, R (.inr (.inl (r,d)))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    apply Finset.sum_le_sum
    intro d _
    calc
      _ ≤ R (.inr (.inl (r,d)))*16 := mul_le_mul_of_nonneg_left
        (unbounded_basal_nonfood_jump_sq N r d) (hr (.inr (.inl (r,d))))
      _ = _ := mul_comm _ _
  have hc : (∑ r : Reaction n, ∑ x : Molecule n, ∑ d : Bool,
      R (.inr (.inr (r,x,d)))*A (.inr (.inr (r,x,d)))) ≤
      16*(∑ r : Reaction n, ∑ x : Molecule n, ∑ d : Bool, R (.inr (.inr (r,x,d)))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro d _
    calc
      _ ≤ R (.inr (.inr (r,x,d)))*16 := mul_le_mul_of_nonneg_left
        (unbounded_catalytic_nonfood_jump_sq N r x d) (hr (.inr (.inr (r,x,d))))
      _ = _ := mul_comm _ _
  have hf0 : 0 ≤ ∑ f : ↥(binaryFood n 2), R (.inl (.inl f)) :=
    Finset.sum_nonneg (fun f _ => hr _)
  have ho0 : 0 ≤ ∑ x : Molecule n, R (.inl (.inr x)) :=
    Finset.sum_nonneg (fun x _ => hr _)
  change (∑ ch,R ch*A ch) ≤ 16*(∑ ch,R ch)+(n : ℝ)*countMass N
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type]
  rw [hfeed]
  linarith

end
end RandomViability
