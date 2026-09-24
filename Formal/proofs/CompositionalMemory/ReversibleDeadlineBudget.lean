import proofs.CompositionalMemory.CoupledDeadline

namespace CompositionalMemory
open FiniteCopy

theorem reversible_deadline_from_generator {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (h v w : α → ℝ)
    (hv : ∀ x, -(2/1000000 : ℝ) ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -(5/8 : ℝ)*w x+1/50000)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α) (hwx : 0 ≤ w x)
    (hbirth : (495550 : ℝ) ≤ 500000*v x-2*w x) :
    (991/1000 : ℝ) ≤ finiteTimeExpectation M 20 h x := by
  have hh := finite_deadline_residual_certificate M 20 h v w (5/8) (2/1000000)
    (1/50000) (by norm_num) (by norm_num) hv hw hcover x
  norm_num at hh
  have ht := mul_le_mul_of_nonneg_right wide_deadline_exp_bound hwx
  nlinarith only [hh,ht,hbirth]

end CompositionalMemory
