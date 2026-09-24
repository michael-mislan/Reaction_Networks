import Mathlib

namespace PhenotypeIdentification

/- Rectangular noisy-channel cancellation applies to the pair channel
after the conventional tensor-product left-inverse identity is established. -/
theorem rectangular_channel_recovery {s y k : Type*}
    [Fintype s] [Fintype y] [DecidableEq s]
    (L : Matrix s y ℝ) (F : Matrix y s ℝ) (K : Matrix s k ℝ)
    (h : L*F=1) : L*(F*K)=K := by
  rw [← Matrix.mul_assoc,h,Matrix.one_mul]

theorem delayed_upper_channel_left_inverse {s y : Type*}
    [Fintype s] [Fintype y] [DecidableEq s]
    (L : Matrix s y ℝ) (E : Matrix y s ℝ) (S V : Matrix s s ℝ)
    (hE : L*E=1) (hS : V*S.transpose=1) :
    (V*L)*(E*S.transpose)=1 := by
  calc
    (V*L)*(E*S.transpose) = V*(L*E)*S.transpose := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hE,Matrix.mul_one,hS]

end PhenotypeIdentification
