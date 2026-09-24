import proofs.ProductiveMemory.ExtractionReadout

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
noncomputable section
set_option Elab.async false

theorem count_fraction_of_log_gain (H L g : ℝ) (hH : 0 < H) (hL : 0 < L)
    (h : g < Real.log H-Real.log L) : Real.exp g/(1+Real.exp g) < H/(H+L) := by
  have he := Real.exp_lt_exp.mpr h
  rw [Real.exp_sub,Real.exp_log hH,Real.exp_log hL] at he
  have hx := (lt_div_iff₀ hL).mp he
  apply (div_lt_div_iff₀ (by positivity : 0 < 1+Real.exp g) (by positivity : 0 < H+L)).mpr
  nlinarith only [hx]

theorem equilibrium_output_ratio (rho zL zH : ℝ) (hr : 0 < rho)
    (hL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hH : zH ∈ Icc (289014/100000:ℝ) (289017/100000)) :
    (294/100:ℝ) < (rho*zH)/(rho*zL) := by
  have hz : 0 < zL := by linarith only [hL.1]
  apply (lt_div_iff₀ (mul_pos hr hz)).mpr
  have hgap : (294/100:ℝ)*zL < zH := by linarith only [hL.2,hH.1]
  nlinarith only [mul_pos hr (sub_pos.mpr hgap)]

theorem robust_readout (tag : Bool) (z measured threshold margin : ℝ)
    (hrange : if tag then (288/100:ℝ) ≤ z ∧ z ≤ 3 else (97/100:ℝ) ≤ z ∧ z ≤ 1)
    (hlo : 1+margin ≤ threshold) (hhi : threshold+margin ≤ 288/100)
    (herr : |measured-z| < margin) : tag=true ↔ threshold ≤ measured := by
  have he := abs_lt.mp herr
  cases tag <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hrange ⊢
  · constructor
    · exact False.elim
    · intro hm; linarith only [hrange.2,he.2,hlo,hm]
  · constructor
    · intro _; linarith only [hrange.1,he.1,hhi]
    · intro _; trivial

theorem midpoint_readout (tag : Bool) (z measured : ℝ)
    (hrange : if tag then (288/100:ℝ) ≤ z ∧ z ≤ 3 else (97/100:ℝ) ≤ z ∧ z ≤ 1)
    (herr : |measured-z| < 94/100) : tag=true ↔ 194/100 ≤ measured :=
  robust_readout tag z measured (194/100) (94/100) hrange (by norm_num) (by norm_num) herr

theorem original_readout_margin (tag : Bool) (z measured : ℝ)
    (hrange : if tag then (288/100:ℝ) ≤ z ∧ z ≤ 3 else (97/100:ℝ) ≤ z ∧ z ≤ 1)
    (herr : |measured-z| < 88/100) : tag=true ↔ 2 ≤ measured :=
  robust_readout tag z measured 2 (88/100) hrange (by norm_num) (by norm_num) herr

theorem measured_fraction_gain (f initialMeasured finalMeasured e g : ℝ)
    (hf : Real.exp g/(1+Real.exp g) < f)
    (hi : |initialMeasured-1/2| ≤ e) (hfinal : |finalMeasured-f| ≤ e)
    (he : 2*e < Real.exp g/(1+Real.exp g)-1/2) : initialMeasured < finalMeasured := by
  have hi' := abs_le.mp hi
  have hf' := abs_le.mp hfinal
  linarith only [hf,hi'.2,hf'.1,he]

end
end ProductiveMemory
