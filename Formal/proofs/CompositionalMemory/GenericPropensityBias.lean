import proofs.CompositionalMemory.GenericProductBias

namespace CompositionalMemory

theorem clipped_density_factor (n ell : ℕ) (v : ℝ) (hv : 0 < v) :
    0 ≤ ((n-ell:ℕ):ℝ)/v ∧ ((n-ell:ℕ):ℝ)/v ≤ (n:ℝ)/v ∧
      (n:ℝ)/v-((n-ell:ℕ):ℝ)/v ≤ (ell:ℝ)/v := by
  have hsub : ((n-ell:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n ell
  have hcount : (n:ℝ) ≤ ((n-ell:ℕ):ℝ)+ell := by
    exact_mod_cast (show n ≤ n-ell+ell by omega)
  refine ⟨by positivity,div_le_div_of_nonneg_right hsub hv.le,?_⟩
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by linarith only [hcount]) hv.le

/-- Density propensity bias for a finite collection of reactant slots.
Natural subtraction enforces zero propensity for insufficient reactants. -/
theorem clipped_product_density_bias {ι : Type*} (s : Finset ι)
    (n offset : ι → ℕ) (v U : ℝ) (hv : 0 < v) (hU : 0 ≤ U)
    (hu : ∀ j ∈ s, (n j:ℝ)/v ≤ U) (hoff : ∀ j ∈ s, offset j ≤ s.card) :
    |(∏ j ∈ s, ((n j-offset j:ℕ):ℝ)/v)-(∏ j ∈ s, (n j:ℝ)/v)| ≤
      (s.card:ℝ)^2*(U+1)^s.card/v := by
  have hf (j) := clipped_density_factor (n j) (offset j) v hv
  have hprod : (∏ j ∈ s, ((n j-offset j:ℕ):ℝ)/v) ≤ ∏ j ∈ s, (n j:ℝ)/v :=
    Finset.prod_le_prod (fun j _ => (hf j).1) (fun j _ => (hf j).2.1)
  have hgap := ordered_product_gap s
    (fun j => ((n j-offset j:ℕ):ℝ)/v) (fun j => (n j:ℝ)/v)
    U ((s.card:ℝ)/v) hU (by positivity)
    (fun j _ => (hf j).1) (fun j _ => (hf j).2.1) hu
    (fun j hj => (hf j).2.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hoff j hj) hv.le))
  rw [abs_of_nonpos (sub_nonpos.mpr hprod)]
  convert hgap using 1 <;> ring

end CompositionalMemory
