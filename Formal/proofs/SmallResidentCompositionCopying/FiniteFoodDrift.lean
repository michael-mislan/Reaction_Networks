import proofs.SmallResidentCompositionCopying.FiniteFoodSource

namespace SmallResidentCompositionCopying.FiniteFood
open FiniteCopy CompositionalMemory
noncomputable section

def g {K : ℕ} (x : Fin K) : ℝ := (1/2:ℝ)^x.val
def H {K : ℕ} (z : Counts K) : ℝ := g z.1+g z.2
def reward {K : ℕ} (z : Counts K) : ℝ := (1-g z.1)*(1-g z.2)
def localDrift (p : Rates) {K : ℕ} (x y : Fin K) : ℝ :=
  birth p x y*(g (up x)-g x)+death p x y*(g (down x)-g x)

theorem g_bounds {K : ℕ} (x : Fin K) : 0 ≤ g x ∧ g x ≤ 1 := by
  constructor
  · exact pow_nonneg (by norm_num) _
  · exact pow_le_one₀ (by norm_num) (by norm_num)

theorem generator_H (p : Rates) {K : ℕ} (z : Counts K) :
    (model p K).generator H z=localDrift p z.1 z.2+localDrift p z.2 z.1 := by
  simp [FiniteJumpModel.generator,model,H,localDrift,Fin.sum_univ_succ]
  ring

theorem reward_cover {K : ℕ} (z : Counts K) : 1 ≤ reward z+H z := by
  have h := mul_nonneg (g_bounds z.1).1 (g_bounds z.2).1
  dsimp [reward,H]; nlinarith

theorem local9 (x y : Fin 9) : localDrift nominal x y ≤ -3900*g x+2523/160 := by
  have hy : (y.val:ℝ) ≤ 8 := by exact_mod_cast (show y.val ≤ 8 by omega)
  have hy0 : (0:ℝ) ≤ y.val := Nat.cast_nonneg _
  fin_cases x <;> norm_num [localDrift,birth,death,nominal,up,down,g] <;> nlinarith

theorem local20 (x y : Fin 20) : localDrift nominal x y ≤ -9000*g x+2535/131072 := by
  have hy : (y.val:ℝ) ≤ 19 := by exact_mod_cast (show y.val ≤ 19 by omega)
  have hy0 : (0:ℝ) ≤ y.val := Nat.cast_nonneg _
  fin_cases x <;> norm_num [localDrift,birth,death,nominal,up,down,g] <;> nlinarith

theorem exp_bound (s : ℝ) (hs : 0 ≤ s) : Real.exp (-s*20) ≤ 1/(20*s+1) := by
  have h := Real.add_one_le_exp (20*s)
  have hp : 0 < 20*s+1 := by positivity
  rw [show -s*20=-(20*s) by ring,Real.exp_neg]
  simpa only [one_div] using (one_div_le_one_div_of_le hp h)

theorem deadline {K : ℕ} (p : Rates) (s C : ℝ) (hs : 0<s) (hc : 0≤C)
    (hl : ∀ x y : Fin K, localDrift p x y ≤ -s*g x+C) (z : Counts K) :
    1-2/(20*s+1)-2*C/s ≤ finiteTimeExpectation (model p K) 20 reward z := by
  have hh := finite_deadline_residual_certificate (model p K) 20 reward (fun _ => 1) H s 0 (2*C)
    hs (by positivity)
    (by intro x; simp [FiniteJumpModel.generator])
    (by intro x; rw [generator_H]; dsimp [H]; linarith [hl x.1 x.2,hl x.2 x.1])
    reward_cover z
  have hH : 0 ≤ H z ∧ H z ≤ 2 := by
    dsimp [H]; constructor <;> linarith [(g_bounds z.1).1,(g_bounds z.2).1,(g_bounds z.1).2,(g_bounds z.2).2]
  have he := mul_le_mul_of_nonneg_right (exp_bound s hs.le) hH.1
  have hm := mul_le_mul_of_nonneg_left hH.2 (show 0 ≤ 1/(20*s+1) by positivity)
  rw [show 1/(20*s+1)*2=2/(20*s+1) by ring] at hm
  norm_num only [NNReal.coe_ofNat,mul_zero,sub_zero] at hh
  linarith

theorem nominal9 (z : Counts 9) : (8046297159:ℝ)/8112104000 ≤
    finiteTimeExpectation (model nominal 9) 20 reward z := by
  have h := deadline nominal 3900 (2523/160) (by norm_num) (by norm_num) local9 z
  norm_num at h ⊢
  exact h

theorem nominal20 (z : Counts 20) : (7077818258231:ℝ)/7077927321600 ≤
    finiteTimeExpectation (model nominal 20) 20 reward z := by
  have h := deadline nominal 9000 (2535/131072) (by norm_num) (by norm_num) local20 z
  norm_num at h ⊢
  exact h

end
end SmallResidentCompositionCopying.FiniteFood
