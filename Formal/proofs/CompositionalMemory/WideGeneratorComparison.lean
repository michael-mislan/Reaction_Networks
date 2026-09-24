import proofs.CompositionalMemory.WideGeneratorBinding

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows
set_option maxHeartbeats 50000

theorem target_outside_mono (m : Nat) (v : Array Int) (x y : Int) (col : Nat)
    (a b : Int) (hab : a ≤ b) : target m v x y col a ≤ target m v x y col b := by
  unfold target
  split_ifs <;> omega

theorem wideLiteral_outside_mono (γ : ℝ) (m : Nat) (v next : Array Int)
    (i col : Nat) (a b : Int) (hab : a ≤ b) :
    wideLiteral γ m v next i col a ≤ wideLiteral γ m v next i col b := by
  have ht (x y : Int) :
      (target m v x y col a : ℝ)/(scale : ℝ) ≤
        (target m v x y col b : ℝ)/(scale : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by norm_num [scale])
    exact_mod_cast target_outside_mono m v x y col a b hab
  have hf : 0 ≤ ((i/(4*m+1) : Nat) : ℝ)*(((i/(4*m+1) : Nat) : ℝ)-1) := by
    rw [← falling_count_cast]
    positivity
  dsimp [wideLiteral]
  apply (add_le_add_iff_right _).mpr
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left (sub_le_sub_right (ht _ _) _) (by positivity)
        · exact mul_le_mul_of_nonneg_left (sub_le_sub_right (ht _ _) _) (by positivity)
      · apply mul_le_mul_of_nonneg_left (sub_le_sub_right (ht _ _) _)
        apply div_nonneg _ (by positivity)
        nlinarith only [hf]
    · exact mul_le_mul_of_nonneg_left (sub_le_sub_right (ht _ _) _) (by positivity)
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_right (ht _ _) _) (by positivity)

theorem wide_generator_mono_at (γ : ℝ) (hγ : 0 ≤ γ)
    (f g : WideFiniteState → ℝ) (s : WideFiniteState)
    (hfg : ∀ z, f z ≤ g z) (hs : f s=g s) :
    (wideFiniteModel γ hγ).generator f s ≤ (wideFiniteModel γ hγ).generator g s := by
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_left _ (wideRate_nonneg γ hγ s r)
  rw [hs]
  exact sub_le_sub_right (hfg _) _

theorem wideTimeWitness_le_value (data : Nat → Array Int)
    (hterminal : ∀ (x : Fin 801) (y : Fin 201),
      0 ≤ (value (data 50) (x.val*201+y.val) 2 : ℝ)) :
    ∀ s, wideTimeWitness data s ≤ wideValue data 2 s := by
  intro s
  cases s with
  | none => rfl
  | some s =>
    rcases s with ⟨j,x,y⟩
    by_cases hj : j.val=25
    · have h := hterminal ⟨x.val,by simpa [hj] using x.isLt⟩
        ⟨y.val,by simpa [hj] using y.isLt⟩
      simpa [wideTimeWitness,wideValue,hj] using
        div_nonneg h (show (0 : ℝ) ≤ (scale : ℝ) by norm_num [scale])
    · simp [wideTimeWitness,hj]

end CompositionalMemory
