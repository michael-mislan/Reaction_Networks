import proofs.CompositionalMemory.FiniteDeadlineCertificate

namespace CompositionalMemory
open FiniteCopy

/-- The affine lower envelope survives killing either component. -/
theorem coupled_exit_lower (a b : ℝ) (ha : a ≤ 1) (hb : b ≤ 1)
    (hexit : a=0 ∨ b=0) : a+b-1 ≤ 0 := by
  rcases hexit with h | h <;> linarith

/-- Complementary daughter success in both modules has this lower envelope. -/
theorem coupled_terminal_lower (a b : ℝ) (ha : a ≤ 1) (hb : b ≤ 1) :
    a+b-1 ≤ a*b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- Channelwise lower envelopes compose even when the modules share jumps. -/
theorem coupled_generator_lower {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (v : α → ℝ) (x : α)
    (a b : ℝ) (u z : β → ℝ)
    (hcurrent : v x=a+b-1)
    (hnext : ∀ r, u r+z r-1 ≤ v (M.next x r)) :
    (∑ r, M.rate x r*(u r-a))+(∑ r, M.rate x r*(z r-b)) ≤
      M.generator v x := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  have hh := mul_le_mul_of_nonneg_left (hnext r) (M.nonneg x r)
  rw [hcurrent]
  nlinarith only [hh]

/-- Averaging nonnegative time witnesses is compatible with joint killing. -/
theorem coupled_generator_upper {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (w : α → ℝ) (x : α)
    (a b : ℝ) (u z : β → ℝ)
    (hcurrent : w x=(a+b)/2)
    (hnext : ∀ r, w (M.next x r) ≤ (u r+z r)/2) :
    M.generator w x ≤
      ((∑ r, M.rate x r*(u r-a))+(∑ r, M.rate x r*(z r-b)))/2 := by
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro r _
  have hh := mul_le_mul_of_nonneg_left (hnext r) (M.nonneg x r)
  rw [hcurrent]
  nlinarith only [hh]

/-- Concrete two-module budget, conditional on the literal joint generator
checks. No independence of reaction histories is used. -/
theorem coupled_deadline_from_generator {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (h v w : α → ℝ)
    (hv : ∀ x, -(2/1000000 : ℝ) ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -(5/8 : ℝ)*w x+1/50000)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α) (hwx : 0 ≤ w x)
    (hbirth : (495100 : ℝ) ≤ 500000*v x-2*w x) :
    (9901/10000 : ℝ) ≤ finiteTimeExpectation M 20 h x := by
  have hh := finite_deadline_residual_certificate M 20 h v w (5/8) (2/1000000)
    (1/50000) (by norm_num) (by norm_num) hv hw hcover x
  norm_num at hh
  have ht := mul_le_mul_of_nonneg_right wide_deadline_exp_bound hwx
  nlinarith only [hh,ht,hbirth]

end CompositionalMemory
