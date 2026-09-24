import proofs.HeritableCompositions.GrowthTracking
import proofs.HeritableCompositions.RecoveryRegions
import proofs.HeritableCompositions.GeneratorBinding

namespace HeritableCompositions
open FiniteCopy

theorem membrane_observable_bound (γ N m z r Eold Enew L Q : ℝ)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (hN : 0 ≤ N) (hm : 1 ≤ m) (hNm : N ≤ m)
    (hz : 0 ≤ z) (hz4 : z ≤ 4) (hr : r ≤ 1/400)
    (hL : |L| ≤ 14400*r) (hQ : 0 ≤ Q) (hQmax : Q ≤ 211722)
    (hE : Enew=Eold+(1/(m+1))*L+(1/(m+1))^2*Q) :
    γ*m*z*(Real.exp (N*localAlpha*Enew)-Real.exp (N*localAlpha*Eold)) ≤
      localAlpha*Real.exp (N*localAlpha*Eold)*(N*r^2/4+8000000000*N*γ^2+1) := by
  have heq : N*localAlpha*Enew=N*localAlpha*Eold+
      noiseAlpha*(N/(m+1))*(L+(1/(m+1))*Q) := by
    rw [hE]
    unfold localAlpha noiseAlpha
    ring
  have h := membrane_source_exp_bound γ N m z r L Q hγ hγmax hN hm hNm hz hz4 hr hL hQ hQmax
  have hh := mul_le_mul_of_nonneg_left h (Real.exp_pos (N*localAlpha*Eold)).le
  rw [heq, Real.exp_add]
  change _ ≤ noiseAlpha*Real.exp (N*localAlpha*Eold)*(N*r^2/4+8000000000*N*γ^2+1)
  nlinarith only [hh]

theorem membrane_vector_bounds (x : Point) (hx : ∀ i, |x i| ≤ 35) :
    (∀ i, |x i+membraneDirection i| ≤ 36) ∧
      normSq (fun i => x i+membraneDirection i) ≤ 5041 := by
  have hxs (i : Fin 4) : (x i)^2 ≤ (35 : ℝ)^2 := by
    have h := mul_le_mul (hx i) (hx i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 35)
    nlinarith only [h,sq_abs (x i)]
  have hv (i : Fin 4) : |x i+membraneDirection i| ≤ 36 := by
    have hd : |membraneDirection i| ≤ 1 := by
      fin_cases i <;> norm_num [membraneDirection,Matrix.cons_val_two,Matrix.cons_val_three]
    calc
      |x i+membraneDirection i| ≤ |x i|+|membraneDirection i| := abs_add_le _ _
      _ ≤ 35+1 := add_le_add (hx i) hd
      _ = 36 := by ring
  have hz : (x 2+1)^2 ≤ (36 : ℝ)^2 := by
    have h := mul_le_mul (hv 2) (hv 2) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 36)
    norm_num [membraneDirection,Matrix.cons_val_two,Matrix.cons_val_three] at h
    nlinarith only [h,sq_abs (x 2+1)]
  refine ⟨hv,?_⟩
  norm_num [normSq,membraneDirection,Matrix.cons_val_two,Matrix.cons_val_three]
  nlinarith only [hxs 0,hxs 1,hxs 3,hz]

end HeritableCompositions
