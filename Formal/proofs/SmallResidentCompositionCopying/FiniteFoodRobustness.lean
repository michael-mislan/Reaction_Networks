import proofs.SmallResidentCompositionCopying.FiniteFoodDrift

namespace SmallResidentCompositionCopying.FiniteFood
open FiniteCopy CompositionalMemory
noncomputable section

def OperatingBox (p : Rates) : Prop :=
  500 ≤ p.a ∧ p.a ≤ 1500 ∧ 1/2 ≤ p.b ∧ p.b ≤ 2 ∧ 1/20 ≤ p.c ∧ p.c ≤ 2/9

theorem robust_local (p : Rates) (hp : OperatingBox p) (x y : Fin 9) :
    localDrift p x y ≤ -1800*g x+279/32 := by
  rcases hp with ⟨ha,_,_,hb,_,hc⟩
  have hy : (y.val:ℝ) ≤ 8 := by exact_mod_cast (show y.val ≤ 8 by omega)
  have hy0 : (0:ℝ) ≤ y.val := Nat.cast_nonneg _
  have hcc := p.hc
  have hv0 : 0 ≤ 1+p.c*((y.val:ℝ)+1) := by positivity
  have hv1 : 1 ≤ 1+p.c*((y.val:ℝ)+1) := by nlinarith
  have hv3 : 1+p.c*((y.val:ℝ)+1) ≤ 3 := by nlinarith
  have hA := mul_le_mul_of_nonneg_right ha hv0
  have hB := mul_le_mul_of_nonneg_right hb hv0
  fin_cases x <;> norm_num [localDrift,birth,death,up,down,g] <;> nlinarith

theorem robust9 (p : Rates) (hp : OperatingBox p) (z : Counts 9) :
    (114080769:ℝ)/115203200 ≤ finiteTimeExpectation (model p 9) 20 reward z := by
  have h := deadline p 1800 (279/32) (by norm_num) (by norm_num) (robust_local p hp) z
  norm_num at h ⊢
  exact h

theorem positive_coefficients (p : Rates) (hp : OperatingBox p) :
    0<p.a ∧ 0<p.b ∧ 0<p.c ∧ 0<p.a*p.c ∧ 0<p.b*p.c := by
  rcases hp with ⟨ha,_,hb,_,hc,_⟩
  have ha' : 0<p.a := by linarith
  have hb' : 0<p.b := by linarith
  have hc' : 0<p.c := by linarith
  exact ⟨ha',hb',hc',mul_pos ha' hc',mul_pos hb' hc'⟩

theorem common_ratio (p : Rates) (hp : OperatingBox p) :
    (p.a*p.c)/(p.b*p.c)=p.a/p.b := by
  exact mul_div_mul_right _ _ (ne_of_gt (positive_coefficients p hp).2.2.1)

end
end SmallResidentCompositionCopying.FiniteFood
