import proofs.FiniteCopy.FiniteJump

namespace FiniteCopy
open scoped NNReal
namespace FiniteJumpModel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
  (M : FiniteJumpModel α β)

theorem uniformized_event_bound (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, M.total x ≤ q) (A : Set α) (V : α → ℝ) (a b : ℝ)
    (hV : ∀ x, 0 ≤ V x) (hA : ∀ x ∈ A, a ≤ V x)
    (hgen : ∀ x, M.generator V x ≤ b) (x : α) :
    a*(M.uniformize q hq hbound).poissonized (q*t) (FiniteKernel.eventIndicator A) x ≤
      V x+(t : ℝ)*b := by
  have h := (M.uniformize q hq hbound).poissonized_event_drift_bound (q*t) A V a
    (b/(q : ℝ)) hV hA (M.uniformize_drift q hq hbound V b hgen) x
  have he : ((q*t : ℝ≥0) : ℝ)*(b/(q : ℝ)) = (t : ℝ)*b := by
    rw [NNReal.coe_mul]
    field_simp
  simpa only [he] using h

theorem uniformized_decay_bound (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hbound : ∀ x, M.total x ≤ q) (W : α → ℝ) (hW : ∀ x, 0 ≤ W x)
    (k : ℝ) (hkq : k ≤ q) (hgen : ∀ x, M.generator W x ≤ -k*W x) (x : α) :
    (M.uniformize q hq hbound).poissonized (q*t) W x ≤ Real.exp (-k*(t : ℝ))*W x := by
  have hr : 0 ≤ 1-k/(q : ℝ) := sub_nonneg.mpr ((div_le_one hq).mpr hkq)
  have h := (M.uniformize q hq hbound).poissonized_decay_bound (q*t) W hW
    (1-k/(q : ℝ)) hr (M.uniformize_decay q hq hbound W k hgen) x
  have he : ((q*t : ℝ≥0) : ℝ)*((1-k/(q : ℝ))-1) = -k*(t : ℝ) := by
    rw [NNReal.coe_mul]
    field_simp
    ring
  simpa only [he] using h

omit [DecidableEq α] in
theorem exists_clock (k : ℝ) : ∃ q : ℝ≥0, 0 < (q : ℝ) ∧ k ≤ q ∧
    ∀ x, M.total x ≤ q := by
  have ht (x : α) : 0 ≤ M.total x := Finset.sum_nonneg (fun r _ => M.nonneg x r)
  have hs : 0 ≤ ∑ x, M.total x := Finset.sum_nonneg (fun x _ => ht x)
  let q : ℝ := 1+max k 0+∑ x, M.total x
  have hq : 0 < q := by dsimp [q]; linarith [le_max_right k 0]
  refine ⟨⟨q,hq.le⟩,hq,?_,?_⟩
  · change k ≤ q
    dsimp [q]
    linarith [le_max_left k 0]
  · intro x
    have hx : M.total x ≤ ∑ y, M.total y :=
      Finset.single_le_sum (fun y _ => ht y) (Finset.mem_univ x)
    change M.total x ≤ q
    dsimp [q]
    linarith [le_max_right k 0]

end FiniteJumpModel
end FiniteCopy
