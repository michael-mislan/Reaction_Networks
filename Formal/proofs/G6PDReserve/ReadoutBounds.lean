import Mathlib.Tactic

namespace G6PDReserve.Population
noncomputable section

def Readout (p s f r : ℝ) : Prop :=
  9/10 ≤ s ∧ s ≤ 1 ∧ 0 ≤ f ∧ f ≤ 1/50 ∧
  17/25 ≤ r ∧ r ≤ 18/25 ∧ r = s*p+f*(1-p)

theorem readout_general (p s f r sl su fl fu rl ru : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hs : sl ≤ s) (hsu : s ≤ su) (hf : fl ≤ f) (hfu : f ≤ fu)
    (hr : rl ≤ r) (hru : r ≤ ru) (he : r = s*p+f*(1-p))
    (hd1 : 0 < su-fu) (hd2 : 0 < sl-fl) :
    (rl-fu)/(su-fu) ≤ p ∧ p ≤ (ru-fl)/(sl-fl) := by
  have hu := add_le_add (mul_le_mul_of_nonneg_right hsu hp)
    (mul_le_mul_of_nonneg_right hfu (by linarith : 0 ≤ 1-p))
  have hl := add_le_add (mul_le_mul_of_nonneg_right hs hp)
    (mul_le_mul_of_nonneg_right hf (by linarith : 0 ≤ 1-p))
  constructor
  · apply (div_le_iff₀ hd1).mpr
    nlinarith
  · apply (le_div_iff₀ hd2).mpr
    nlinarith

theorem readout_bounds {p s f r : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (h : Readout p s f r) : 33/49 ≤ p ∧ p ≤ 4/5 := by
  rcases h with ⟨hs,hsu,hf,hfu,hr,hru,he⟩
  have hh := readout_general p s f r (9/10) 1 0 (1/50) (17/25) (18/25)
    hp hp1 hs hsu hf hfu hr hru he (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

theorem readout_feasible (p : ℝ) (hl : 33/49 ≤ p) (hu : p ≤ 4/5) :
    ∃ s f r, Readout p s f r := by
  by_cases hlow : p ≤ 17/25
  · refine ⟨1,(17/25-p)/(1-p),17/25,?_⟩
    have hd : 0 < 1-p := by linarith
    have hf0 : 0 ≤ (17/25-p)/(1-p) := div_nonneg (by linarith) hd.le
    have hf1 : (17/25-p)/(1-p) ≤ 1/50 := by
      apply (div_le_iff₀ hd).mpr; linarith
    refine ⟨by norm_num,le_rfl,hf0,hf1,le_rfl,by norm_num,?_⟩
    rw [div_mul_cancel₀ _ (ne_of_gt hd)]
    ring
  · by_cases hhigh : 18/25 ≤ p
    · have hp : 0 < p := by linarith
      refine ⟨(18/25)/p,0,18/25,?_⟩
      refine ⟨?_,?_,le_rfl,by norm_num,by norm_num,le_rfl,?_⟩
      · apply (le_div_iff₀ hp).mpr; linarith
      · apply (div_le_iff₀ hp).mpr; linarith
      · rw [div_mul_cancel₀ _ (ne_of_gt hp)]; ring
    · exact ⟨1,0,p,by norm_num [Readout]; exact ⟨by linarith,by linarith⟩⟩

/-- A calibrated rate error and cutoff enclosure imply deterministic tail bounds. -/
theorem capacity_error_implications (V Z c cl cu e : ℝ)
    (herr : |Z-V| ≤ e) (hcl : cl ≤ c) (hcu : c ≤ cu) :
    (cu+e ≤ Z → c ≤ V) ∧ (c ≤ V → cl-e ≤ Z) := by
  rw [abs_le] at herr
  constructor <;> intro h <;> linarith [herr.1,herr.2]

theorem normalized_rate_error (A V ψ ε : ℝ) (hψ : 0 < ψ)
    (h : |A-V*ψ| ≤ ε) : |A/ψ-V| ≤ ε/ψ := by
  have he : A/ψ-V = (A-V*ψ)/ψ := by field_simp
  rw [he, abs_div, abs_of_pos hψ]
  exact div_le_div_of_nonneg_right h hψ.le

end
end G6PDReserve.Population
