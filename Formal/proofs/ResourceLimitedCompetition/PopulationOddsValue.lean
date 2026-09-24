import proofs.ResourceLimitedCompetition.PopulationOddsDrift
import proofs.ResourceLimitedCompetition.AncestralGenerator

namespace ResourceLimitedCompetition

noncomputable def oddsShape (N H L : ℝ) : ℝ :=
  Real.exp ((N/1000)*(-Real.log H+Real.log L+(3/5)*Real.log (H+L)))

noncomputable def oddsValue (N H0 L0 H L : ℕ) : ℝ :=
  if H=0 ∨ L=0 then 0 else oddsShape N H L/oddsShape N H0 L0

theorem oddsShape_pos (N H L : ℝ) : 0 < oddsShape N H L := Real.exp_pos _

theorem oddsValue_nonneg (N H0 L0 H L : ℕ) : 0 ≤ oddsValue N H0 L0 H L := by
  unfold oddsValue
  split_ifs
  · exact le_rfl
  · exact (div_pos (oddsShape_pos _ _ _) (oddsShape_pos _ _ _)).le

theorem log_increment_identity (B : ℝ) (hB : 0 < B) :
    Real.log (B+1)=Real.log B+Real.log (1+1/B) := by
  rw [← Real.log_mul (ne_of_gt hB) (ne_of_gt (by positivity : 0 < 1+1/B))]
  congr 1
  field_simp

theorem oddsShape_growth_high (N H L : ℝ) (hH : 0 < H) (hL : 0 < L) :
    oddsShape N (H+1) L=oddsShape N H L*Real.exp (oddsJumpH N H L) := by
  unfold oddsShape oddsJumpH
  rw [← Real.exp_add,log_increment_identity H hH]
  have hw : H+1+L=(H+L)+1 := by ring
  rw [hw,log_increment_identity (H+L) (add_pos hH hL)]
  congr 1
  ring

theorem oddsShape_growth_low (N H L : ℝ) (hH : 0 < H) (hL : 0 < L) :
    oddsShape N H (L+1)=oddsShape N H L*Real.exp (oddsJumpL N H L) := by
  unfold oddsShape oddsJumpL
  rw [← Real.exp_add,log_increment_identity L hL]
  have hw : H+(L+1)=(H+L)+1 := by ring
  rw [hw,log_increment_identity (H+L) (add_pos hH hL)]
  congr 1
  ring

theorem oddsValue_growth_high (N H0 L0 H L : ℕ) (hH : 0 < H) (hL : 0 < L) :
    oddsValue N H0 L0 (H+1) L=oddsValue N H0 L0 H L*Real.exp (oddsJumpH N H L) := by
  simp only [oddsValue,Nat.ne_of_gt hH,Nat.ne_of_gt hL,Nat.add_eq_zero_iff,
    one_ne_zero,and_false,or_self,if_false,Nat.cast_add,Nat.cast_one]
  rw [oddsShape_growth_high _ _ _ (by exact_mod_cast hH) (by exact_mod_cast hL)]
  ring

theorem oddsValue_growth_low (N H0 L0 H L : ℕ) (hH : 0 < H) (hL : 0 < L) :
    oddsValue N H0 L0 H (L+1)=oddsValue N H0 L0 H L*Real.exp (oddsJumpL N H L) := by
  simp only [oddsValue,Nat.ne_of_gt hH,Nat.ne_of_gt hL,Nat.add_eq_zero_iff,
    one_ne_zero,and_false,or_self,if_false,Nat.cast_add,Nat.cast_one]
  rw [oddsShape_growth_low _ _ _ (by exact_mod_cast hH) (by exact_mod_cast hL)]
  ring

end ResourceLimitedCompetition
