import proofs.FiniteCopy.PoissonKernel

namespace FiniteCopy

structure FiniteJumpModel (α β : Type*) [Fintype α] [Fintype β] where
  next : α → β → α
  rate : α → β → ℝ
  nonneg : ∀ x r, 0 ≤ rate x r

namespace FiniteJumpModel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
  (M : FiniteJumpModel α β)

noncomputable def total (x : α) : ℝ := ∑ r, M.rate x r
noncomputable def generator (f : α → ℝ) (x : α) : ℝ :=
  ∑ r, M.rate x r*(f (M.next x r)-f x)

omit [DecidableEq α] in
theorem generator_mono_at (f g : α → ℝ) (x : α)
    (hx : f x=g x) (hnext : ∀ r, f (M.next x r) ≤ g (M.next x r)) :
    M.generator f x ≤ M.generator g x := by
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (M.nonneg x r)
  rw [hx]
  exact sub_le_sub_right (hnext r) _

noncomputable def uniformize (q : ℝ) (hq : 0 < q) (hbound : ∀ x, M.total x ≤ q) :
    FiniteKernel α where
  prob x y := (if x=y then 1-M.total x/q else 0)+
    ∑ r, if M.next x r=y then M.rate x r/q else 0
  nonneg x y := by
    apply add_nonneg
    · split_ifs
      · exact sub_nonneg.mpr ((div_le_one hq).mpr (hbound x))
      · rfl
    · apply Finset.sum_nonneg
      intro r _
      split_ifs
      · exact div_nonneg (M.nonneg x r) hq.le
      · rfl
  row_sum x := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp [← Finset.sum_div, total]

theorem uniformize_step (q : ℝ) (hq : 0 < q) (hbound : ∀ x, M.total x ≤ q)
    (f : α → ℝ) (x : α) :
    (M.uniformize q hq hbound).step f x = f x+M.generator f x/q := by
  simp only [FiniteKernel.step, uniformize, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hg : M.generator f x = (∑ r, M.rate x r*f (M.next x r))-M.total x*f x := by
    simp [generator, total, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hg]
  ring

theorem uniformize_drift (q : ℝ) (hq : 0 < q) (hbound : ∀ x, M.total x ≤ q)
    (V : α → ℝ) (b : ℝ) (hV : ∀ x, M.generator V x ≤ b) (x : α) :
    (M.uniformize q hq hbound).step V x ≤ V x+b/q := by
  rw [M.uniformize_step]
  have h := div_le_div_of_nonneg_right (hV x) hq.le
  linarith

theorem uniformize_decay (q : ℝ) (hq : 0 < q) (hbound : ∀ x, M.total x ≤ q)
    (V : α → ℝ) (k : ℝ) (hV : ∀ x, M.generator V x ≤ -k*V x) (x : α) :
    (M.uniformize q hq hbound).step V x ≤ (1-k/q)*V x := by
  rw [M.uniformize_step]
  have h := div_le_div_of_nonneg_right (hV x) hq.le
  calc
    V x+M.generator V x/q ≤ V x+(-k*V x)/q := by linarith
    _ = (1-k/q)*V x := by ring

end FiniteJumpModel
end FiniteCopy
