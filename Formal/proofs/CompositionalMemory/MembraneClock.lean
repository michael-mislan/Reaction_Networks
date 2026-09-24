import proofs.CompositionalMemory.RetainedModular
import proofs.HeritableCompositions.MembraneClock

namespace CompositionalMemory
open FiniteCopy

noncomputable def modularMembraneObservable {k : ℕ} (M : ℕ) (θ : ℝ)
    (s : ModularCountState k) : ℝ := Real.exp (θ*((s.2 : ℝ)-(M : ℝ)))

theorem exchange_membrane_unchanged {k : ℕ} (s : ModularCountState k) (i j : Fin k) :
    (modularNext s (.inr (.inl (i,j)))).2 = s.2 := by
  simp only [modularNext]
  split <;> rfl

theorem modular_membrane_generator {k : ℕ} (γ θ : ℝ) (w : Fin k → Fin k → ℝ)
    (M : ℕ) (s : ModularCountState k) :
    modularGenerator γ w (modularMembraneObservable M θ) s =
      (∑ i, γ*(s.1 i 2 : ℝ))*modularMembraneObservable M θ s*(Real.exp θ-1) := by
  have he : Real.exp (θ*((s.2 : ℝ)+1-(M : ℝ))) =
      Real.exp (θ*((s.2 : ℝ)-(M : ℝ)))*Real.exp θ := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [modularGenerator,Fintype.sum_sum_type,Fintype.sum_prod_type,
    modularMembraneObservable,exchange_membrane_unchanged]
  simp only [modularNext,modularRate,Nat.cast_add,Nat.cast_one,sub_self,mul_zero,
    Finset.sum_const_zero,zero_add]
  rw [he]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem modular_early_generator {k : ℕ} (γ b : ℝ) (hγ : 0 ≤ γ)
    (w : Fin k → Fin k → ℝ) (M : ℕ) (s : ModularCountState k)
    (hrate : ∑ i, γ*(s.1 i 2 : ℝ) ≤ 2*b*(M : ℝ)) :
    modularGenerator γ w (modularMembraneObservable M (1/5)) s ≤
      (12*b*(M : ℝ)/25)*modularMembraneObservable M (1/5) s := by
  rw [modular_membrane_generator]
  have hW : 0 ≤ modularMembraneObservable M (1/5) s := (Real.exp_pos _).le
  have hr0 : 0 ≤ ∑ i, γ*(s.1 i 2 : ℝ) := Finset.sum_nonneg (fun i _ => mul_nonneg hγ (Nat.cast_nonneg _))
  have hfirst := mul_le_mul_of_nonneg_left HeritableCompositions.early_clock_increment (mul_nonneg hr0 hW)
  have hsecond := mul_le_mul_of_nonneg_right hrate (by positivity : 0 ≤ modularMembraneObservable M (1/5) s*(6/25))
  nlinarith only [hfirst,hsecond]

theorem modular_late_generator {k : ℕ} (γ a : ℝ) (hγ : 0 ≤ γ)
    (w : Fin k → Fin k → ℝ) (M : ℕ) (s : ModularCountState k)
    (hrate : a*(M : ℝ) ≤ ∑ i, γ*(s.1 i 2 : ℝ)) :
    modularGenerator γ w (modularMembraneObservable M (-1/20)) s ≤
      -(19*a*(M : ℝ)/400)*modularMembraneObservable M (-1/20) s := by
  rw [modular_membrane_generator]
  have hW : 0 ≤ modularMembraneObservable M (-1/20) s := (Real.exp_pos _).le
  have hr0 : 0 ≤ ∑ i, γ*(s.1 i 2 : ℝ) := Finset.sum_nonneg (fun i _ => mul_nonneg hγ (Nat.cast_nonneg _))
  have hfirst := mul_le_mul_of_nonneg_left HeritableCompositions.late_clock_increment (mul_nonneg hr0 hW)
  have hsecond := mul_le_mul_of_nonneg_right hrate (by positivity : 0 ≤ modularMembraneObservable M (-1/20) s*(19/400))
  nlinarith only [hfirst,hsecond]

end CompositionalMemory
