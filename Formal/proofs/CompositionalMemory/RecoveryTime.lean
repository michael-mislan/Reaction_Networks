import proofs.CompositionalMemory.UniformEnvelope

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

/-- The fixed recovery time cancels the entire 4A birth exponent. -/
theorem recovery_at_2688 (k : ℕ) (N p : ℝ) (hN : 0 ≤ N)
    (h : Real.exp (localAlpha*N*innerEnergy)*p ≤ (k : ℝ)*
      (Real.exp (-(N*localAlpha*innerEnergy/672)*2688)*
        Real.exp (localAlpha*N*(4*innerEnergy))+
        2*Real.exp (N*localAlpha*innerEnergy/2))) :
    p ≤ 3*(k : ℝ)*Real.exp (-N*localAlpha*innerEnergy/2) := by
  have hcancel : Real.exp (-(N*localAlpha*innerEnergy/672)*2688)*
      Real.exp (localAlpha*N*(4*innerEnergy)) = 1 := by
    rw [← Real.exp_add]
    have hz : -(N*localAlpha*innerEnergy/672)*2688+localAlpha*N*(4*innerEnergy)=0 := by ring
    rw [hz,Real.exp_zero]
  rw [hcancel] at h
  have hfloor : 1 ≤ Real.exp (N*localAlpha*innerEnergy/2) := by
    have hn : 0 ≤ N*localAlpha*innerEnergy/2 := by
      unfold localAlpha innerEnergy outerEnergy
      positivity
    simpa using Real.exp_le_exp.mpr hn
  have hsplit : Real.exp (localAlpha*N*innerEnergy)*
      Real.exp (-N*localAlpha*innerEnergy/2) = Real.exp (N*localAlpha*innerEnergy/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp : Real.exp (localAlpha*N*innerEnergy)*p ≤
      Real.exp (localAlpha*N*innerEnergy)*(3*(k : ℝ)*Real.exp (-N*localAlpha*innerEnergy/2)) := by
    calc
      _ ≤ 3*(k : ℝ)*Real.exp (N*localAlpha*innerEnergy/2) := by
        have hh := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg k)
        nlinarith only [h,hh]
      _ = _ := by rw [← hsplit]; ring
  nlinarith only [hp,Real.exp_pos (localAlpha*N*innerEnergy)]

end CompositionalMemory
