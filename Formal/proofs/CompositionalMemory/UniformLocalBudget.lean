import proofs.CompositionalMemory.PerturbationBudget
import proofs.CompositionalMemory.EnergyMoments
import proofs.CompositionalMemory.IncrementBounds

namespace CompositionalMemory

/-- This consumes bounds on literal jump sizes, not on transition kernels. -/
theorem perturbation_of_jump_sizes {ι : Type*} [Fintype ι]
    (rate δ d : ι → ℝ) (N r D V : ℝ)
    (hN : 1 ≤ N) (hr : 0 ≤ r) (hrmax : r ≤ 1/400)
    (hV : 0 ≤ V) (hVmax : V ≤ 1/1000000)
    (hrate : ∀ j, 0 ≤ rate j)
    (hd : ∀ j, 0 ≤ d j) (hdmax : ∀ j, d j ≤ 71/N)
    (hδ : ∀ j, |δ j| ≤ 84*r*d j+42*(d j)^2)
    (hfirst : ∑ j, rate j*d j ≤ D)
    (hsecond : ∑ j, rate j*(d j)^2 ≤ V/N) :
    ∑ j, rate j*(Real.exp ((1/1000000000000 : ℝ)*N*δ j)-1) ≤
      (1/1000000000000 : ℝ)*(N*r^2/4+2*N*(84*D)^2+1) := by
  have hNp : 0 < N := by linarith only [hN]
  have hs (j) : (d j)^2 ≤ (71 : ℝ)^2/N^2 := by
    have h := mul_self_le_mul_self (hd j) (hdmax j)
    simpa only [← pow_two,div_pow] using h
  exact perturbation_moment_budget rate δ N r (84*D) V hN hV hVmax hrate
    (fun j => birth_scaled_increment_small N r (d j) (δ j) hN hrmax (hd j) (hdmax j) (hδ j))
    (energy_first_moment rate δ d r D V N hr hrate hδ hfirst hsecond)
    (by simpa only [show (71 : ℝ)^2=5041 by norm_num] using
      energy_second_moment rate δ d N r V 71 hNp hrate hδ hs hsecond)

/-- The numeric J2 conclusion once resident and literal incident contributions
have been bounded. Their bounds come from separate reaction-level lemmas. -/
theorem combine_uniform_local_budget (N r γ κ W resident incident : ℝ)
    (hN : 0 ≤ N) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hW : 0 ≤ W)
    (hres : resident ≤ (1/1000000000000 : ℝ)*W*(-N*r^2/2+100000000))
    (hinc : incident ≤ (1/1000000000000 : ℝ)*W*
      (N*r^2/4+2*N*(84*(284*γ+8*κ))^2+1)) :
    resident+incident ≤ (1/1000000000000 : ℝ)*W*
      (-N*r^2/4+200000000+1200000000*N*(γ+κ)^2) := by
  have hf : 0 ≤ 84*(284*γ+8*κ) := by positivity
  have hfmax : 84*(284*γ+8*κ) ≤ 23856*(γ+κ) := by linarith only [hκ]
  have hsq : (84*(284*γ+8*κ))^2 ≤ (23856*(γ+κ))^2 := by
    simpa only [← pow_two] using mul_self_le_mul_self hf hfmax
  have hbound : 2*(84*(284*γ+8*κ))^2 ≤ 1200000000*(γ+κ)^2 := by
    nlinarith only [hsq,sq_nonneg (γ+κ)]
  have hscaled := mul_le_mul_of_nonneg_left hbound hN
  have hinner : -N*r^2/2+100000000+(N*r^2/4+2*N*(84*(284*γ+8*κ))^2+1) ≤
      -N*r^2/4+200000000+1200000000*N*(γ+κ)^2 := by nlinarith only [hscaled]
  have h := mul_le_mul_of_nonneg_left hinner (show 0 ≤ (1/1000000000000 : ℝ)*W by positivity)
  nlinarith only [hres,hinc,h]

end CompositionalMemory
