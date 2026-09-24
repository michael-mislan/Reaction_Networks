import proofs.FiniteCopy.FiniteJump

namespace CompositionalMemory
open FiniteCopy

noncomputable def sixthRemainderCoefficient (D d : ℝ) : ℝ :=
  15*D^4+20*D^3*d+15*D^2*d^2+6*D*d^3+d^4

theorem sixth_increment_upper (D δ d : ℝ) (hD : 0 ≤ D) (hd : |δ| ≤ d) :
    (D+δ)^6-D^6 ≤ 6*D^5*δ+sixthRemainderCoefficient D d*δ^2 := by
  have hp (k : ℕ) : δ^k ≤ d^k := by
    calc
      _ ≤ |δ^k| := le_abs_self _
      _ = |δ|^k := abs_pow _ _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg δ) hd k
  have h1 := mul_le_mul_of_nonneg_left (hp 1) (show 0 ≤ 20*D^3*δ^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hp 2) (show 0 ≤ 15*D^2*δ^2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left (hp 3) (show 0 ≤ 6*D*δ^2 by positivity)
  have h4 := mul_le_mul_of_nonneg_left (hp 4) (sq_nonneg δ)
  dsimp [sixthRemainderCoefficient]
  nlinarith only [h1,h2,h3,h4]

/-- Preserve the negative quadratic restoring drift when lifting to the
sixth power; bound only the second and higher jump terms by absolute sizes. -/
theorem sixth_power_generator_bound {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (D dD : α → ℝ) (x : α)
    (d drift variance : ℝ) (hD : 0 ≤ D x) (hd : 0 ≤ d)
    (hjump : ∀ r,|D (M.next x r)-D x| ≤ d)
    (hfirst : dD x+M.generator D x ≤ drift)
    (hsecond : ∑ r,M.rate x r*(D (M.next x r)-D x)^2 ≤ variance) :
    6*(D x)^5*dD x+M.generator (fun y => (D y)^6) x ≤
      6*(D x)^5*drift+sixthRemainderCoefficient (D x) d*variance := by
  have hg : M.generator (fun y => (D y)^6) x ≤
      6*(D x)^5*M.generator D x+
        sixthRemainderCoefficient (D x) d*(∑ r,M.rate x r*(D (M.next x r)-D x)^2) := by
    unfold FiniteJumpModel.generator
    calc
      _ ≤ ∑ r,M.rate x r*(6*(D x)^5*(D (M.next x r)-D x)+
          sixthRemainderCoefficient (D x) d*(D (M.next x r)-D x)^2) := by
        apply Finset.sum_le_sum
        intro r _
        apply mul_le_mul_of_nonneg_left _ (M.nonneg x r)
        simpa only [add_sub_cancel] using sixth_increment_upper (D x) (D (M.next x r)-D x) d hD (hjump r)
      _ = _ := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        ring
  have hc : 0 ≤ sixthRemainderCoefficient (D x) d := by unfold sixthRemainderCoefficient; positivity
  have h1 := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 6*(D x)^5 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hsecond hc
  nlinarith only [hg,h1,h2]

end CompositionalMemory
