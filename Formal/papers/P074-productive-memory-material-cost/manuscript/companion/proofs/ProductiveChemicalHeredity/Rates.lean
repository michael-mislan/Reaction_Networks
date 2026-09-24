import proofs.ProductiveChemicalHeredity.Source

namespace ProductiveChemicalHeredity

/-- Falling-factorial mass action after cancellation of the factorial coefficients. -/
def forwardRate (x y : ℕ) : ℚ :=
  20*(x.choose 65 : ℚ)*(y.choose 8 : ℚ)*((414-x-y).choose 155 : ℚ)

def reverseRate (x y : ℕ) : ℚ :=
  (1/100000)*(((x+121).choose 186 : ℚ)/(Nat.choose 316 186 : ℚ))*
    (((y+30).choose 38 : ℚ)/(Nat.choose 94 38 : ℚ))

theorem forward_rate_lower (x y : ℕ) (h : corridor x y) : 20≤forwardRate x y := by
  rcases h with ⟨hx,hX,hy,hY⟩
  have hf : 155≤414-x-y := by omega
  have h1 : (1 : ℚ)≤x.choose 65 := by exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hx)
  have h2 : (1 : ℚ)≤y.choose 8 := by exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hy)
  have h3 : (1 : ℚ)≤(414-x-y).choose 155 := by exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hf)
  unfold forwardRate
  have h12 : (1 : ℚ)≤(x.choose 65 : ℚ)*(y.choose 8 : ℚ) := by nlinarith
  have h123 : (1 : ℚ)≤(x.choose 65 : ℚ)*(y.choose 8 : ℚ)*((414-x-y).choose 155 : ℚ) := by nlinarith
  nlinarith

theorem reverse_rate_upper (x y : ℕ) (h : corridor x y) :
    0≤reverseRate x y ∧ reverseRate x y≤1/100000 := by
  rcases h with ⟨hx,hX,hy,hY⟩
  have hxle : ((x+121).choose 186 : ℚ)≤(Nat.choose 316 186 : ℚ) := by
    exact_mod_cast Nat.choose_le_choose 186 (show x+121≤316 by omega)
  have hyle : ((y+30).choose 38 : ℚ)≤(Nat.choose 94 38 : ℚ) := by
    exact_mod_cast Nat.choose_le_choose 38 (show y+30≤94 by omega)
  have hxp : (0 : ℚ)<(Nat.choose 316 186 : ℚ) := by exact_mod_cast Nat.choose_pos (by omega : 186≤316)
  have hyp : (0 : ℚ)<(Nat.choose 94 38 : ℚ) := by exact_mod_cast Nat.choose_pos (by omega : 38≤94)
  have ha : (0 : ℚ)≤((x+121).choose 186 : ℚ)/(Nat.choose 316 186 : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hxp)
  have hb : (0 : ℚ)≤((y+30).choose 38 : ℚ)/(Nat.choose 94 38 : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hyp)
  have hc : ((x+121).choose 186 : ℚ)/(Nat.choose 316 186 : ℚ)≤1 := (div_le_one hxp).mpr hxle
  have hd : ((y+30).choose 38 : ℚ)/(Nat.choose 94 38 : ℚ)≤1 := (div_le_one hyp).mpr hyle
  unfold reverseRate
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) ha) hb
  · calc
      _ ≤ (1/100000 : ℚ)*1*1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hc (by norm_num)) hd hb (by norm_num)
      _ = _ := by norm_num

end ProductiveChemicalHeredity

