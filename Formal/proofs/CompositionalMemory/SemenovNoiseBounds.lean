import proofs.CompositionalMemory.SemenovFieldTaylor
import proofs.CompositionalMemory.SemenovMetricConsequences

namespace CompositionalMemory.Semenov
open Matrix

theorem coordinate_deviation_bound {N : ℕ} (x : Fin N → ℝ) (radius : ℝ)
    (hr : 0 ≤ radius) (hx : vectorSquares x ≤ radius^2) (j : Fin N) : |x j| ≤ radius := by
  have hj : x j^2 ≤ vectorSquares x :=
    Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ j)
  exact (sq_le_sq₀ (abs_nonneg _) hr).mp (by simpa only [sq_abs] using hj.trans hx)

theorem tube_coordinate_upper (zc : Fin 8 → Fin 17 → ℚ) (radius : ℚ)
    (hr : 0 ≤ radius) (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (n : Fin 8 → ℝ)
    (hx : vectorSquares (fun j => n j-coefficientValue (zc j) t) ≤ (radius : ℝ)^2) (j : Fin 8) :
    n j ≤ (coordinateUpper zc radius j : ℝ) := by
  have hr' : (0 : ℝ) ≤ radius := by exact_mod_cast hr
  have hd := (le_abs_self _).trans (coordinate_deviation_bound _ (radius : ℝ) hr' hx j)
  have hz := (coefficientValue_bounds (zc j) t hl hu).2
  have hm : (coefficientUpper (zc j) : ℝ) ≤ (max 0 (coefficientUpper (zc j)) : ℚ) := by
    exact_mod_cast le_max_right (0 : ℚ) (coefficientUpper (zc j))
  simp only [coordinateUpper,Rat.cast_add]
  linarith only [hd,hz,hm]

theorem chemical_value_nonneg (n : Fin 8 → ℝ) (hn : ∀ j,0 ≤ n j) (r : Fin 11) :
    0 ≤ chemicalValue n r := by
  unfold chemicalValue
  have hk := nominalRate_nonneg r
  split_ifs
  · exact mul_nonneg hk (hn _)
  · exact mul_nonneg (mul_nonneg hk (hn _)) (hn _)

theorem tube_propensity_upper (zc : Fin 8 → Fin 17 → ℚ) (radius : ℚ)
    (n : Fin 8 → ℝ) (hn : ∀ j,0 ≤ n j)
    (hbound : ∀ j,n j ≤ (coordinateUpper zc radius j : ℝ)) (r : Fin 11) :
    chemicalValue n r ≤ (propensityUpper zc radius r : ℝ) := by
  have hupper (j : Fin 8) : (0 : ℝ) ≤ coordinateUpper zc radius j := (hn j).trans (hbound j)
  by_cases h7 : r.val=7
  · simp only [chemicalValue,propensityUpper,if_pos h7,Rat.cast_mul,kineticRational_cast]
    exact mul_le_mul_of_nonneg_left (hbound _) (nominalRate_nonneg r)
  · simp only [chemicalValue,propensityUpper,if_neg h7,Rat.cast_mul,kineticRational_cast]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hbound _) (nominalRate_nonneg r))
      (hbound _) (hn _) (mul_nonneg (nominalRate_nonneg r) (hupper _))

theorem jump_energy_value (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (r : Fin 11) (t : ℝ) :
    coefficientValue (jumpEnergyCoefficients pc r) t=
      matrixEnergy (coefficientMatrix pc t) (fun j => (stoich r j : ℝ)) := by
  change coefficientValue (fun k => ∑ i,(stoich r i : ℚ)*metricJumpCoefficients pc r i k) t = _
  rw [coefficientValue_linear]
  simp only [metric_jump_value,Rat.cast_intCast,matrixEnergy_dotProduct,dotProduct]

noncomputable def metricNoiseValue (pc : Fin 8 → Fin 8 → Fin 17 → ℚ) (t : ℝ) (n : Fin 8 → ℝ) : ℝ :=
  (∑ r,chemicalValue n r*matrixEnergy (coefficientMatrix pc t) (fun j => (stoich r j : ℝ)))+
    ∑ j,(1/500)*(nominalFeed j+n j)*coefficientValue (pc j j) t

/-- The rational noise checks bound all chemical, feed and outflow channels
at every nonnegative concentration in the checked tube. -/
theorem metric_noise_bound
    (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (eta radius margin L Q H : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr eta radius margin L Q H)
    (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1) (n : Fin 8 → ℝ) (hn : ∀ j,0 ≤ n j)
    (hx : vectorSquares (fun j => n j-coefficientValue (zc j) t) ≤ (radius : ℝ)^2) :
    metricNoiseValue pc t n ≤ (Q : ℝ) := by
  rcases hg with ⟨hpos,htri,hdiag,hmargin,hnr,hcurv,heta,hL,hH,hJ,hQ⟩
  have hb := tube_coordinate_upper zc radius hpos.2.1.le t hl hu n hx
  have hchem (r : Fin 11) :
      chemicalValue n r*matrixEnergy (coefficientMatrix pc t) (fun j => (stoich r j : ℝ)) ≤
        (propensityUpper zc radius r : ℝ)*(coefficientUpper (jumpEnergyCoefficients pc r) : ℝ) := by
    have he := (coefficientValue_bounds (jumpEnergyCoefficients pc r) t hl hu).2
    rw [jump_energy_value] at he
    have hp := tube_propensity_upper zc radius n hn hb r
    have hh : (0 : ℝ) ≤ coefficientUpper (jumpEnergyCoefficients pc r) := by exact_mod_cast (hH r).1
    exact (mul_le_mul_of_nonneg_left he (chemical_value_nonneg n hn r)).trans
      (mul_le_mul_of_nonneg_right hp hh)
  have hflow (j : Fin 8) :
      (1/500 : ℝ)*(nominalFeed j+n j)*coefficientValue (pc j j) t ≤
        (1/500 : ℝ)*(nominalFeed j+(coordinateUpper zc radius j : ℝ))*(coefficientUpper (pc j j) : ℝ) := by
    have he := (coefficientValue_bounds (pc j j) t hl hu).2
    have hh : (0 : ℝ) ≤ coefficientUpper (pc j j) := by exact_mod_cast (hJ j).1
    have ha : 0 ≤ (1/500 : ℝ)*(nominalFeed j+n j) := by
      have hf := nominalFeed_nonneg j
      exact mul_nonneg (by norm_num) (add_nonneg hf (hn j))
    exact (mul_le_mul_of_nonneg_left he ha).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hb j)) (by norm_num)) hh)
  have hs := add_le_add (Finset.sum_le_sum (s := Finset.univ) (fun r _ => hchem r))
    (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hflow j))
  have hcast : (noiseUpper zc pc radius : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  simp only [noiseUpper,Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,
    feedRational_cast] at hcast
  exact hs.trans hcast

end CompositionalMemory.Semenov
