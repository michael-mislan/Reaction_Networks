import proofs.CoreCouplingCAC.Dynamics

namespace CoreCouplingGlobal
open CoreCouplingCAC

/-- Lexicographic exterior-pair order: 01,02,03,12,13,23. -/
noncomputable def compound₂ (J : Fin 4 → Fin 4 → ℝ) : Fin 6 → Fin 6 → ℝ :=
  ![![J 0 0+J 1 1,J 1 2,J 1 3,-J 0 2,-J 0 3,0],
    ![J 2 1,J 0 0+J 2 2,J 2 3,J 0 1,0,-J 0 3],
    ![J 3 1,J 3 2,J 0 0+J 3 3,0,J 0 1,J 0 2],
    ![-J 2 0,J 1 0,0,J 1 1+J 2 2,J 2 3,-J 1 3],
    ![-J 3 0,0,J 1 0,J 3 2,J 1 1+J 3 3,J 1 2],
    ![0,-J 3 0,J 2 0,-J 3 1,J 2 1,J 2 2+J 3 3]]

noncomputable def compoundMajorant (A B z e : ℝ) : Fin 6 → Fin 6 → ℝ :=
  ![![-3-z-e-4*e*A,B,0,0,0,0],
    ![1+z,-17-B-8*z-2*e*A,3,e*(1+2*A),0,0],
    ![0,16+4*z,-3-1/10000-2*e*A,0,e*(1+2*A),0],
    ![1,1+2*e*A,0,-18-B-9*z-e-2*e*A,3,0],
    ![0,0,1+2*e*A,16+4*z,-4-1/10000-z-e-2*e*A,B],
    ![0,0,1,0,1+z,-18-1/10000-B-8*z]]

noncomputable def compoundWeights : Fin 6 → ℝ := ![100000,113960,121511,217,259,170]

theorem compoundWeights_positive (i : Fin 6) : 0 < compoundWeights i := by
  fin_cases i <;> norm_num [compoundWeights]

/-- Uniform rational column estimate, stronger than checking spectra at equilibria. -/
theorem compound_column_bound (A B z e : ℝ)
    (hA : 0 ≤ A) (hAM : A ≤ 34) (hB : 2 ≤ B) (hBM : B ≤ 34)
    (hz : 0 ≤ z) (hzM : z ≤ 12) (he : 0 ≤ e) (heM : e ≤ 1/50000)
    (j : Fin 6) :
    (∑ i, compoundWeights i * compoundMajorant A B z e i j) ≤
      -(1/10:ℝ)*compoundWeights j := by
  have heA : 0 ≤ e*A := mul_nonneg he hA
  have heAM : e*A ≤ (34/50000:ℝ) := by
    calc
      e*A ≤ (1/50000:ℝ)*34 := mul_le_mul heM hAM hA (by norm_num)
      _ = _ := by norm_num
  fin_cases j <;>
    norm_num [compoundWeights,compoundMajorant,Fin.sum_univ_succ] <;>
    nlinarith only [hB,hBM,hz,hzM,he,heM,heA,heAM]

set_option maxHeartbeats 1600000 in
/-- The literal midpoint Jacobian has the stated absolute off-diagonal majorant. -/
theorem compound_majorant_literal (A B z H e : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hz : 0 ≤ z) (he : 0 ≤ e)
    (i j : Fin 6) :
    let p : Rates := ⟨6,27,16,2,e,1/10000⟩
    let t : Fin 4 → ℝ := ![A+B,-B,z,H]
    (if i=j then compound₂ (jacobian p t) i j
      else |compound₂ (jacobian p t) i j|) = compoundMajorant A B z e i j := by
  have h₁ : 0 ≤ e*(1+2*A) := by positivity
  have h₂ : 0 ≤ 1+2*e*A := by positivity
  have h₃ : 0 ≤ 1+z := by positivity
  have h₄ : 0 ≤ 16+4*z := by positivity
  have h₅ : -1-2*e*A ≤ 0 := by nlinarith [mul_nonneg he hA]
  have h₆ : 0 ≤ 1+2*A := by positivity
  fin_cases i <;> fin_cases j <;>
    norm_num [compound₂,jacobian,compoundMajorant,show A+B+-B=A by ring,
      Matrix.cons_val_two,Matrix.cons_val_three,
      abs_of_nonneg hB,abs_of_nonneg h₁,abs_of_nonneg h₂,
      abs_of_nonneg h₃,abs_of_nonneg h₄,abs_of_nonpos h₅,
      abs_mul,abs_of_nonneg he,abs_of_nonneg h₆] <;> ring

end CoreCouplingGlobal
